// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! AVX2 SIMD implementation of `flat_square` for PACKED_LANES = 2.
//!
//! Processes both u128 lanes of a `PackedBlock128` in parallel inside a
//! single `__m256i`. The squaring is bit-spread + GCM reduction (no CLMUL),
//! so it executes on the shift/ALU ports and overlaps with CLMUL-based
//! `flat_mul` on port 5 in the Poseidon2b S-box.
//!
//! The module is only compiled when AVX2 is available and AVX-512 is not —
//! i.e. exactly the configuration where `PACKED_LANES == 2`.

#![cfg(target_arch = "x86_64")]

use super::PackedBlock128;
use core::arch::x86_64::*;

/// Left-shift each 128-bit lane of `$x` by `$n` bits (0 < $n < 64).
///
/// AVX2 has no native u128 shift; we do it by shifting each u64 and
/// carrying the bits that spill out of the low u64 into the high u64
/// of the same 128-bit lane.
macro_rules! shl_u128 {
    ($x:expr, $n:literal) => {{
        let x_ = $x;
        let hi = _mm256_slli_epi64(x_, $n);
        let carry = _mm256_srli_epi64(x_, 64 - $n);
        let carry_aligned = _mm256_slli_si256(carry, 8);
        _mm256_or_si256(hi, carry_aligned)
    }};
}

/// Bit-spread: each 128-bit lane holds a u64 in its low-u64 slot (hi-u64
/// is zero). Output: each bit `i` of the input u64 lands at position `2*i`
/// of the output u128 lane.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn bit_spread(x: __m256i) -> __m256i {
    let mask32 = _mm256_set1_epi64x(0x00000000FFFFFFFFu64 as i64);
    let mask16 = _mm256_set1_epi64x(0x0000FFFF0000FFFFu64 as i64);
    let mask8 = _mm256_set1_epi64x(0x00FF00FF00FF00FFu64 as i64);
    let mask4 = _mm256_set1_epi64x(0x0F0F0F0F0F0F0F0Fu64 as i64);
    let mask2 = _mm256_set1_epi64x(0x3333333333333333u64 as i64);
    let mask1 = _mm256_set1_epi64x(0x5555555555555555u64 as i64);

    let x = _mm256_and_si256(_mm256_or_si256(x, shl_u128!(x, 32)), mask32);
    let x = _mm256_and_si256(_mm256_or_si256(x, shl_u128!(x, 16)), mask16);
    let x = _mm256_and_si256(_mm256_or_si256(x, shl_u128!(x, 8)), mask8);
    let x = _mm256_and_si256(_mm256_or_si256(x, shl_u128!(x, 4)), mask4);
    let x = _mm256_and_si256(_mm256_or_si256(x, shl_u128!(x, 2)), mask2);
    _mm256_and_si256(_mm256_or_si256(x, shl_u128!(x, 1)), mask1)
}

/// Multiply each 128-bit lane by the GCM tail polynomial
/// P = x^7 + x^2 + x + 1 (= 0x87). Matches `clmul_u128_by_87` scalar.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn clmul_by_87(a: __m256i) -> __m256i {
    let s1 = shl_u128!(a, 1);
    let s2 = shl_u128!(a, 2);
    let s7 = shl_u128!(a, 7);
    _mm256_xor_si256(_mm256_xor_si256(a, s1), _mm256_xor_si256(s2, s7))
}

/// Per-lane 256-bit reduction modulo x^128 + x^7 + x^2 + x + 1, matching
/// `reduce_gcm_256` in `hardware.rs`. Each 128-bit lane is reduced
/// independently; the scalar algorithm splits `x_hi` into two u64 halves
/// to avoid overflow during the multiplication by P.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn reduce_gcm_256(x_hi: __m256i, x_lo: __m256i) -> __m256i {
    // `low_half_mask` per 128-bit lane: lo-u64 all-ones, hi-u64 zero.
    let low_half_mask = _mm256_set_epi64x(0, -1, 0, -1);

    // x1_lo = low u64 of x_hi, zero-extended into the 128-bit lane.
    let x1_lo = _mm256_and_si256(x_hi, low_half_mask);
    // x1_hi = high u64 of x_hi, moved to the lo-u64 slot (128-bit lane
    // shifted right by 8 bytes), hi-u64 zero.
    let x1_hi = _mm256_srli_si256(x_hi, 8);

    let v1 = clmul_by_87(x1_lo);
    let v2 = clmul_by_87(x1_hi);

    // v2_shift64 = v2 << 64 at u128 level  <=>  lane shifted left 8 bytes.
    let v2_shift64 = _mm256_slli_si256(v2, 8);
    // v2_overflow = v2 >> 64 at u128 level  <=>  lane shifted right 8 bytes.
    let v2_overflow = _mm256_srli_si256(v2, 8);

    let lo = _mm256_xor_si256(_mm256_xor_si256(x_lo, v1), v2_shift64);
    let v3 = clmul_by_87(v2_overflow);

    _mm256_xor_si256(lo, v3)
}

/// Per-lane flat-basis squaring directly on a `__m256i` (two u128 lanes) —
/// the register-domain core shared by [`packed_square_flat_avx2`] and the
/// vector permutation kernels. Bit-spread + shift-XOR reduction: no CLMUL,
/// so it runs on the shift/ALU ports and overlaps CLMUL-based multiplies.
///
/// # Safety
/// Requires AVX2; the module-level cfg gate guarantees it at compile time.
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn square_gcm_x2(val: __m256i) -> __m256i {
    let low_half_mask = _mm256_set_epi64x(0, -1, 0, -1);
    // Extract lo-u64 of each 128-bit lane (zero the hi-u64).
    let lo64s = _mm256_and_si256(val, low_half_mask);
    // Extract hi-u64 of each 128-bit lane into the lo-u64 slot.
    let hi64s = _mm256_srli_si256(val, 8);

    // Bit-spread each u64 into a full u128 (per lane).
    let s_lo = bit_spread(lo64s);
    let s_hi = bit_spread(hi64s);

    // Reduce the 256-bit per-lane value to 128 bits.
    reduce_gcm_256(s_hi, s_lo)
}

/// SIMD flat-basis squaring of a `PackedBlock128` (two u128 lanes).
///
/// # Safety
/// Requires runtime AVX2 support. The module-level cfg gate guarantees
/// this at compile time.
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn packed_square_flat_avx2(x: PackedBlock128) -> PackedBlock128 {
    // PackedBlock128 is repr(C) { lanes: [u128; 2] } = 32 bytes, layout-
    // compatible with __m256i. loadu/storeu handle arbitrary alignment.
    let lanes_ptr = &x as *const PackedBlock128 as *const __m256i;
    let val = _mm256_loadu_si256(lanes_ptr);

    let result = square_gcm_x2(val);

    let mut out = PackedBlock128::ZERO;
    let out_ptr = &mut out as *mut PackedBlock128 as *mut __m256i;
    _mm256_storeu_si256(out_ptr, result);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hardware::square_flat_u128;
    use crate::packed::PACKED_LANES;
    use crate::Block128;
    use rand::Rng;

    #[test]
    fn avx2_square_matches_scalar_random() {
        assert_eq!(PACKED_LANES, 2);
        let mut rng = rand::thread_rng();
        for _ in 0..10_000 {
            let a: [Block128; 2] = std::array::from_fn(|_| Block128::from(rng.gen::<u128>()));
            let pa = PackedBlock128::from_array(a);

            let expected = [
                square_flat_u128(a[0].to_u128()),
                square_flat_u128(a[1].to_u128()),
            ];
            let got = unsafe { packed_square_flat_avx2(pa) };
            assert_eq!(
                [got.get_lane(0).to_u128(), got.get_lane(1).to_u128()],
                expected,
                "mismatch on input {:x?}",
                a.map(|b| b.to_u128())
            );
        }
    }

    #[test]
    fn avx2_square_edge_cases() {
        let edge_values: [u128; 6] = [
            0,
            1,
            u128::MAX,
            1u128 << 127,
            0x0123456789ABCDEF_FEDCBA9876543210,
            0xAAAAAAAAAAAAAAAA_5555555555555555,
        ];
        for &v0 in &edge_values {
            for &v1 in &edge_values {
                let pa = PackedBlock128::from_array([Block128::from(v0), Block128::from(v1)]);
                let expected = [square_flat_u128(v0), square_flat_u128(v1)];
                let got = unsafe { packed_square_flat_avx2(pa) };
                assert_eq!(
                    [got.get_lane(0).to_u128(), got.get_lane(1).to_u128()],
                    expected,
                    "mismatch on ({:x}, {:x})",
                    v0,
                    v1
                );
            }
        }
    }
}
