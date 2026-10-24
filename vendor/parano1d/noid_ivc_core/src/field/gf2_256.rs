// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! GF(2^256) as a quadratic extension of the proof core's flat GF(2^128).
//!
//! `F256 { lo, hi }` denotes `lo + hi * X` modulo
//!
//! ```text
//! X^2 + X + tau,
//! ```
//!
//! where `tau` is the flat-basis image of `Block128::TAU`.  This makes the
//! coordinate-wise basis bridge to [`noid_core::Block256`] a field
//! isomorphism, which is load-bearing for native/recursive transcript replay.

use super::F128;
use core::ops::{Add, AddAssign, Mul, MulAssign};
use noid_core::{Block128, Block256};
use serde::{Deserialize, Serialize};

/// Flat-basis image of `Block128::TAU`.
///
/// `Block128::TAU` is tower basis bit 125.  The value below is row 125 of the
/// frozen tower-to-flat conversion matrix.  Tests pin it against the bridge
/// implementation and its absolute trace.
pub const F256_EXTENSION_TAU: F128 = F128 {
    lo: 0xFAAF_C414_3960_829A,
    hi: 0xB9E8_0FCC_7CA8_FE72,
};

/// Exact min-entropy of the C1 trace-one challenge support.
pub const C1_CHALLENGE_MIN_ENTROPY_BITS: u32 = 255;

/// One element of GF(2^256), in two flat GF(2^128) coordinates.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(C, align(16))]
pub struct F256 {
    pub lo: F128,
    pub hi: F128,
}

impl F256 {
    pub const ZERO: Self = Self {
        lo: F128::ZERO,
        hi: F128::ZERO,
    };
    pub const ONE: Self = Self {
        lo: F128::ONE,
        hi: F128::ZERO,
    };
    pub const EXTENSION_TAU: F128 = F256_EXTENSION_TAU;

    #[inline(always)]
    pub const fn new(lo: F128, hi: F128) -> Self {
        Self { lo, hi }
    }

    #[inline(always)]
    pub const fn from_base(value: F128) -> Self {
        Self {
            lo: value,
            hi: F128::ZERO,
        }
    }

    /// Multiply by an element of the embedded GF(2^128) subfield.  This is
    /// coordinate-wise and costs two base-field products instead of a full
    /// three-product extension multiplication.
    #[inline(always)]
    pub fn scale_base(self, scalar: F128) -> Self {
        Self {
            lo: self.lo * scalar,
            hi: self.hi * scalar,
        }
    }

    #[inline(always)]
    pub const fn is_zero(self) -> bool {
        self.lo.is_zero() && self.hi.is_zero()
    }

    #[inline(always)]
    pub const fn is_in_base_subfield(self) -> bool {
        self.hi.is_zero()
    }

    #[inline(always)]
    pub fn square(self) -> Self {
        let lo2 = self.lo * self.lo;
        let hi2 = self.hi * self.hi;
        Self {
            lo: lo2 + hi2 * Self::EXTENSION_TAU,
            hi: hi2,
        }
    }

    /// Multiplicative inverse, with `inv(0) = 0` matching the base field.
    #[inline]
    pub fn inv(self) -> Self {
        let lo2 = self.lo * self.lo;
        let hi2 = self.hi * self.hi;
        let hi_lo = self.hi * self.lo;
        let norm = hi2 * Self::EXTENSION_TAU + hi_lo + lo2;
        let norm_inv = norm.inv();
        Self {
            lo: (self.hi + self.lo) * norm_inv,
            hi: self.hi * norm_inv,
        }
    }

    /// C1 challenge map from two uniform transcript lanes.
    ///
    /// The high coordinate is `y^2 + y + tau`. Since `Tr(tau)=1`, it has
    /// absolute trace one and can never be zero. The linearized map
    /// `y -> y^2+y` has kernel `{0,1}`, so every output in the trace-one
    /// affine hyperplane has exactly two preimages. Together with the
    /// independent low lane, the result has exactly 255 bits of min-entropy
    /// and never lies in the distinguished GF(2^128) subfield.
    #[inline(always)]
    pub fn from_raw_challenge_lanes(lo: F128, raw_hi: F128) -> Self {
        Self {
            lo,
            hi: raw_hi * raw_hi + raw_hi + Self::EXTENSION_TAU,
        }
    }

    /// Canonical low-coordinate-then-high-coordinate little-endian encoding.
    pub fn to_le_bytes(self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        bytes[..8].copy_from_slice(&self.lo.lo.to_le_bytes());
        bytes[8..16].copy_from_slice(&self.lo.hi.to_le_bytes());
        bytes[16..24].copy_from_slice(&self.hi.lo.to_le_bytes());
        bytes[24..].copy_from_slice(&self.hi.hi.to_le_bytes());
        bytes
    }

    pub fn from_le_bytes(bytes: [u8; 32]) -> Self {
        Self {
            lo: F128 {
                lo: u64::from_le_bytes(bytes[..8].try_into().expect("eight-byte low limb")),
                hi: u64::from_le_bytes(bytes[8..16].try_into().expect("eight-byte high limb")),
            },
            hi: F128 {
                lo: u64::from_le_bytes(bytes[16..24].try_into().expect("eight-byte low limb")),
                hi: u64::from_le_bytes(bytes[24..].try_into().expect("eight-byte high limb")),
            },
        }
    }

    /// Coordinate-wise tower-to-flat basis bridge.
    pub fn from_tower(value: Block256) -> Self {
        Self {
            lo: flat_f128(value.lo),
            hi: flat_f128(value.hi),
        }
    }

    /// Coordinate-wise flat-to-tower inverse basis bridge.
    pub fn to_tower(self) -> Block256 {
        Block256::new(tower_f128(self.lo), tower_f128(self.hi))
    }
}

#[inline]
fn flat_f128(value: Block128) -> F128 {
    let flat = noid_core::hardware::tower_to_flat_u128(value.0);
    F128 {
        lo: flat as u64,
        hi: (flat >> 64) as u64,
    }
}

#[inline]
fn tower_f128(value: F128) -> Block128 {
    let flat = (value.lo as u128) | ((value.hi as u128) << 64);
    Block128(noid_core::hardware::flat_to_tower_u128(flat))
}

impl From<F128> for F256 {
    fn from(value: F128) -> Self {
        Self::from_base(value)
    }
}

impl Add for F256 {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self {
            lo: self.lo + rhs.lo,
            hi: self.hi + rhs.hi,
        }
    }
}

impl AddAssign for F256 {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Mul for F256 {
    type Output = Self;

    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        #[cfg(target_arch = "x86_64")]
        if noid_core::cpu::avx2_vpclmul_available() {
            // SAFETY: the runtime gate requires AVX2 and VPCLMULQDQ.
            return unsafe { mul_f256_avx2(self, rhs) };
        }
        mul_f256_portable(self, rhs)
    }
}

#[inline(always)]
fn mul_f256_portable(left: F256, right: F256) -> F256 {
    let v0 = left.lo * right.lo;
    let v1 = left.hi * right.hi;
    let v_sum = (left.lo + left.hi) * (right.lo + right.hi);
    F256 {
        lo: v0 + v1 * F256::EXTENSION_TAU,
        hi: v0 + v_sum,
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2,vpclmulqdq")]
unsafe fn mul_f256_avx2(left: F256, right: F256) -> F256 {
    use noid_core::packed::{PackedBlock128, clmul_avx2::packed_mul_flat_avx2};

    #[inline(always)]
    fn packed(low: F128, high: F128) -> PackedBlock128 {
        PackedBlock128::from_array([
            Block128((low.lo as u128) | ((low.hi as u128) << 64)),
            Block128((high.lo as u128) | ((high.hi as u128) << 64)),
        ])
    }

    #[inline(always)]
    fn unpack(value: PackedBlock128) -> [F128; 2] {
        value.to_array().map(|value| {
            let value = value.0;
            F128::new(value as u64, (value >> 64) as u64)
        })
    }

    // First vector lane computes lo*lo and the second computes hi*hi.
    let first =
        unsafe { packed_mul_flat_avx2(packed(left.lo, left.hi), packed(right.lo, right.hi)) };
    let [v0, v1] = unpack(first);
    // Compute the Karatsuba cross product and the fixed extension reduction
    // in parallel, retaining both GF(2^128) products in vector registers.
    let second = unsafe {
        packed_mul_flat_avx2(
            packed(left.lo + left.hi, v1),
            packed(right.lo + right.hi, F256::EXTENSION_TAU),
        )
    };
    let [v_sum, v1_tau] = unpack(second);
    F256 {
        lo: v0 + v1_tau,
        hi: v0 + v_sum,
    }
}

impl MulAssign for F256 {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy)]
    struct TestRng(u64);

    impl TestRng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        fn next_f128(&mut self) -> F128 {
            F128::new(self.next_u64(), self.next_u64())
        }

        fn next_f256(&mut self) -> F256 {
            F256::new(self.next_f128(), self.next_f128())
        }
    }

    fn absolute_trace(mut value: F128) -> F128 {
        let mut trace = value;
        for _ in 1..128 {
            value *= value;
            trace += value;
        }
        trace
    }

    #[test]
    fn tau_is_pinned_to_tower_bridge_and_has_trace_one() {
        let bridged = flat_f128(Block128::TAU);
        assert_eq!(F256::EXTENSION_TAU, bridged);
        assert_eq!(absolute_trace(F256::EXTENSION_TAU), F128::ONE);
    }

    #[test]
    fn tower_bridge_is_a_field_isomorphism() {
        let mut rng = TestRng(0xC1_256B);
        for _ in 0..256 {
            let a = rng.next_f256();
            let b = rng.next_f256();
            assert_eq!(F256::from_tower(a.to_tower()), a);
            assert_eq!(F256::from_tower(a.to_tower() + b.to_tower()), a + b);
            assert_eq!(F256::from_tower(a.to_tower() * b.to_tower()), a * b);
            assert_eq!(a.scale_base(b.lo), a * F256::from_base(b.lo));
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn avx2_vpclmul_matches_portable_multiplication() {
        if !noid_core::cpu::avx2_vpclmul_available() {
            return;
        }

        let mut rng = TestRng(0xC1_A72_256);
        for _ in 0..4096 {
            let left = rng.next_f256();
            let right = rng.next_f256();
            // SAFETY: the runtime gate above requires AVX2 and VPCLMULQDQ.
            let accelerated = unsafe { mul_f256_avx2(left, right) };
            assert_eq!(accelerated, mul_f256_portable(left, right));
        }
    }

    #[test]
    fn field_axioms_square_and_inverse() {
        let mut rng = TestRng(0xC1_F1E1D);
        for _ in 0..256 {
            let a = rng.next_f256();
            let b = rng.next_f256();
            let c = rng.next_f256();
            assert_eq!(a.square(), a * a);
            assert_eq!(a * (b + c), a * b + a * c);
            assert_eq!((a * b) * c, a * (b * c));
            if a.is_zero() {
                assert_eq!(a.inv(), F256::ZERO);
            } else {
                assert_eq!(a * a.inv(), F256::ONE);
            }
        }
    }

    #[test]
    fn c1_sampler_always_excludes_the_base_subfield() {
        let mut rng = TestRng(0xC1_5A4D);
        for _ in 0..4096 {
            let challenge = F256::from_raw_challenge_lanes(rng.next_f128(), rng.next_f128());
            assert!(!challenge.is_in_base_subfield());
            assert_eq!(absolute_trace(challenge.hi), F128::ONE);
        }
    }

    #[test]
    fn c1_sampler_is_exactly_two_to_one_in_its_high_lane() {
        let mut rng = TestRng(0xC1_2A1);
        for _ in 0..256 {
            let lo = rng.next_f128();
            let y = rng.next_f128();
            assert_eq!(
                F256::from_raw_challenge_lanes(lo, y),
                F256::from_raw_challenge_lanes(lo, y + F128::ONE)
            );
        }
    }

    #[test]
    fn canonical_encoding_roundtrips() {
        let mut rng = TestRng(0xC1_C0DE);
        for _ in 0..256 {
            let value = rng.next_f256();
            assert_eq!(F256::from_le_bytes(value.to_le_bytes()), value);
        }
    }
}
