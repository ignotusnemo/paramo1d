// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! Four-lane flat-basis GF(2^128) arithmetic for AVX-512.
//!
//! `PackedBlock128` deliberately remains two lanes on every x86-64 build.
//! These kernels consume two adjacent logical packs at a higher layer, so
//! enabling AVX-512 changes execution only — never proof or witness layout.

#![cfg(target_arch = "x86_64")]

use core::arch::x86_64::*;

/// Broadcast one flat-basis element into all four 128-bit lanes.
#[inline]
#[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
pub unsafe fn broadcast_u128(value: u128) -> __m512i {
    let lo = value as i64;
    let hi = (value >> 64) as i64;
    _mm512_set_epi64(hi, lo, hi, lo, hi, lo, hi, lo)
}

/// Reduce four independent 256-bit carry-less products modulo
/// x^128 + x^7 + x^2 + x + 1.
#[inline]
#[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
pub unsafe fn reduce_gcm_x4(hi: __m512i, lo: __m512i) -> __m512i {
    let p = _mm512_set1_epi64(0x87);
    let v1 = _mm512_clmulepi64_epi128::<0x00>(hi, p);
    let v2 = _mm512_clmulepi64_epi128::<0x01>(hi, p);
    let v2_shift = _mm512_bslli_epi128::<8>(v2);
    let v2_overflow = _mm512_bsrli_epi128::<8>(v2);
    let v3 = _mm512_clmulepi64_epi128::<0x00>(v2_overflow, p);
    _mm512_xor_si512(_mm512_xor_si512(lo, v1), _mm512_xor_si512(v2_shift, v3))
}

/// Four independent flat-basis products, one per 128-bit lane.
#[inline]
#[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
pub unsafe fn mul_gcm_x4(a: __m512i, b: __m512i) -> __m512i {
    let ll = _mm512_clmulepi64_epi128::<0x00>(a, b);
    let hh = _mm512_clmulepi64_epi128::<0x11>(a, b);
    let lh = _mm512_clmulepi64_epi128::<0x10>(a, b);
    let hl = _mm512_clmulepi64_epi128::<0x01>(a, b);
    let cross = _mm512_xor_si512(lh, hl);
    let lo = _mm512_xor_si512(ll, _mm512_bslli_epi128::<8>(cross));
    let hi = _mm512_xor_si512(hh, _mm512_bsrli_epi128::<8>(cross));
    reduce_gcm_x4(hi, lo)
}

/// Four independent flat-basis squares.
#[inline]
#[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
pub unsafe fn square_gcm_x4(a: __m512i) -> __m512i {
    let lo = _mm512_clmulepi64_epi128::<0x00>(a, a);
    let hi = _mm512_clmulepi64_epi128::<0x11>(a, a);
    reduce_gcm_x4(hi, lo)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hardware::clmul_gcm;

    fn supported() -> bool {
        std::arch::is_x86_feature_detected!("avx512f")
            && std::arch::is_x86_feature_detected!("avx512bw")
            && std::arch::is_x86_feature_detected!("vpclmulqdq")
    }

    fn next(seed: &mut u64) -> u128 {
        let mut word = || {
            *seed = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = *seed;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        ((word() as u128) << 64) | word() as u128
    }

    #[test]
    fn four_lane_mul_matches_scalar() {
        if !supported() {
            return;
        }
        let mut seed = 0xA5A5_5120_u64;
        for _ in 0..10_000 {
            let a: [u128; 4] = std::array::from_fn(|_| next(&mut seed));
            let b: [u128; 4] = std::array::from_fn(|_| next(&mut seed));
            let mut got = [0u128; 4];
            unsafe {
                let va = _mm512_loadu_si512(a.as_ptr().cast());
                let vb = _mm512_loadu_si512(b.as_ptr().cast());
                _mm512_storeu_si512(got.as_mut_ptr().cast(), mul_gcm_x4(va, vb));
            }
            for lane in 0..4 {
                assert_eq!(got[lane], clmul_gcm(a[lane], b[lane]));
            }
        }
    }
}
