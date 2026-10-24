// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! Packed arithmetic operations for PackedBlock128.

use super::PackedBlock128;
use crate::hardware::{
    clmul_gcm, flat_to_tower_u128, square_flat_u128, tower_to_flat_u128, Flat, HardwareField,
};
use crate::Block128;

/// Runtime gate for the two-lane AVX2 fast paths.
#[cfg(target_arch = "x86_64")]
#[inline]
fn avx2_vpclmul_runtime() -> bool {
    #[cfg(all(target_feature = "avx2", target_feature = "vpclmulqdq"))]
    return true;
    #[cfg(not(all(target_feature = "avx2", target_feature = "vpclmulqdq")))]
    crate::cpu::avx2_vpclmul_available()
}

#[cfg(target_arch = "x86_64")]
#[inline]
fn avx2_runtime() -> bool {
    #[cfg(target_feature = "avx2")]
    return true;
    #[cfg(not(target_feature = "avx2"))]
    crate::cpu::avx2_available()
}

impl PackedBlock128 {
    /// Packed multiplication using CLMUL hardware acceleration.
    ///
    /// Converts tower-basis lanes to flat-basis, performs CLMUL
    /// multiplication, and converts the result back to the tower basis.
    #[inline(always)]
    pub fn packed_mul(self, other: Self) -> Self {
        Self {
            lanes: std::array::from_fn(|i| {
                let a_tower = Block128::from(self.lanes[i]);
                let b_tower = Block128::from(other.lanes[i]);

                // Convert tower -> flat
                let a_flat = Flat(a_tower).to_flat();
                let b_flat = Flat(b_tower).to_flat();

                // Multiply in flat basis using CLMUL
                let c_flat = a_flat * b_flat;

                // Convert flat -> tower
                c_flat.to_tower().inner().0
            }),
        }
    }

    /// Packed squaring using linear Frobenius endomorphism.
    ///
    /// In GF(2^n), squaring is linear: (a+b)^2 = a^2 + b^2.
    /// Squaring remains in the tower basis because it is already extremely
    /// fast and does not require CLMUL.
    #[inline(always)]
    pub fn square(self) -> Self {
        Self {
            lanes: std::array::from_fn(|i| {
                super::square::square_block128(Block128::from(self.lanes[i])).to_u128()
            }),
        }
    }

    /// Multiply each lane by the same scalar Block128.
    ///
    /// Optimized to convert the scalar to flat-basis only once.
    #[inline(always)]
    pub fn scalar_mul(self, scalar: Block128) -> Self {
        // Convert the scalar to flat basis ONCE, instead of per-lane
        let scalar_flat = Flat(scalar).to_flat();

        Self {
            lanes: std::array::from_fn(|i| {
                let a_tower = Block128::from(self.lanes[i]);
                let a_flat = Flat(a_tower).to_flat();

                let c_flat = a_flat * scalar_flat;

                c_flat.to_tower().inner().0
            }),
        }
    }

    // ------------------------------------------------------------------
    // Flat-basis fast path
    //
    // For pipelines that perform several multiplications in a row (e.g.
    // Poseidon2b's S-box), converting to flat basis once, doing all work
    // in flat, then converting back amortises the expensive basis
    // transform over many arithmetic ops.
    // ------------------------------------------------------------------

    /// Convert every lane from tower basis to flat basis.
    #[inline(always)]
    pub fn to_flat(self) -> Self {
        Self {
            lanes: self.lanes.map(tower_to_flat_u128),
        }
    }

    /// Convert every lane from flat basis to tower basis.
    #[inline(always)]
    pub fn to_tower(self) -> Self {
        Self {
            lanes: self.lanes.map(flat_to_tower_u128),
        }
    }

    /// Multiply two flat-basis packed values (no basis conversion).
    #[inline(always)]
    pub fn flat_mul(self, other: Self) -> Self {
        #[cfg(target_arch = "x86_64")]
        if avx2_vpclmul_runtime() {
            // SAFETY: gated on runtime AVX2+VPCLMULQDQ detection.
            return unsafe { super::clmul_avx2::packed_mul_flat_avx2(self, other) };
        }
        #[allow(unreachable_code)]
        Self {
            lanes: std::array::from_fn(|i| clmul_gcm(self.lanes[i], other.lanes[i])),
        }
    }

    /// Square a flat-basis packed value (no basis conversion).
    #[inline(always)]
    pub fn flat_square(self) -> Self {
        #[cfg(target_arch = "x86_64")]
        if avx2_runtime() {
            // SAFETY: gated on runtime AVX2 detection.
            return unsafe { super::simd_square_avx2::packed_square_flat_avx2(self) };
        }
        #[allow(unreachable_code)]
        Self {
            lanes: self.lanes.map(square_flat_u128),
        }
    }

    /// Multiply every flat-basis lane by a single flat-basis scalar.
    #[inline(always)]
    pub fn flat_scalar_mul(self, scalar_flat: u128) -> Self {
        #[cfg(target_arch = "x86_64")]
        if avx2_vpclmul_runtime() {
            // SAFETY: gated on runtime AVX2+VPCLMULQDQ detection.
            return unsafe { super::clmul_avx2::packed_scalar_mul_flat_avx2(self, scalar_flat) };
        }
        #[allow(unreachable_code)]
        Self {
            lanes: std::array::from_fn(|i| clmul_gcm(self.lanes[i], scalar_flat)),
        }
    }

    /// Conditional select: for each lane, return `a[i]` if `mask[i]` is all-ones,
    /// else `b[i]`. Used in constant-time operations.
    #[inline(always)]
    pub fn select(mask: Self, a: Self, b: Self) -> Self {
        let and_a = Self {
            lanes: std::array::from_fn(|i| mask.lanes[i] & a.lanes[i]),
        };
        let not_mask = Self {
            lanes: std::array::from_fn(|i| !mask.lanes[i]),
        };
        let and_b = Self {
            lanes: std::array::from_fn(|i| not_mask.lanes[i] & b.lanes[i]),
        };
        and_a.xor(and_b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::packed::PACKED_LANES;
    use rand::Rng;

    #[test]
    fn packed_mul_matches_scalar() {
        let mut rng = rand::thread_rng();
        for _ in 0..1000 {
            let a: [Block128; PACKED_LANES] =
                std::array::from_fn(|_| Block128::from(rng.gen::<u128>()));
            let b: [Block128; PACKED_LANES] =
                std::array::from_fn(|_| Block128::from(rng.gen::<u128>()));

            let pa = PackedBlock128::from_array(a);
            let pb = PackedBlock128::from_array(b);
            let packed_result = pa.packed_mul(pb).to_array();

            for i in 0..PACKED_LANES {
                // This will assert that tower(tower_to_flat(a) * tower_to_flat(b)) == a * b
                assert_eq!(packed_result[i], a[i] * b[i]);
            }
        }
    }

    #[test]
    fn packed_square_matches_scalar() {
        let mut rng = rand::thread_rng();
        for _ in 0..1000 {
            let a: [Block128; PACKED_LANES] =
                std::array::from_fn(|_| Block128::from(rng.gen::<u128>()));

            let pa = PackedBlock128::from_array(a);
            let packed_result = pa.square().to_array();

            for i in 0..PACKED_LANES {
                assert_eq!(packed_result[i], a[i].square());
            }
        }
    }

    #[test]
    fn flat_roundtrip_matches_tower_mul() {
        let mut rng = rand::thread_rng();
        for _ in 0..200 {
            let a: [Block128; PACKED_LANES] =
                std::array::from_fn(|_| Block128::from(rng.gen::<u128>()));
            let b: [Block128; PACKED_LANES] =
                std::array::from_fn(|_| Block128::from(rng.gen::<u128>()));
            let pa = PackedBlock128::from_array(a);
            let pb = PackedBlock128::from_array(b);

            let mul_via_flat = pa.to_flat().flat_mul(pb.to_flat()).to_tower().to_array();
            let square_via_flat = pa.to_flat().flat_square().to_tower().to_array();

            for i in 0..PACKED_LANES {
                assert_eq!(mul_via_flat[i], a[i] * b[i]);
                assert_eq!(square_via_flat[i], a[i].square());
            }
        }
    }

    #[test]
    fn packed_scalar_mul_matches_scalar() {
        let mut rng = rand::thread_rng();
        let scalar = Block128::from(rng.gen::<u128>());
        for _ in 0..1000 {
            let a: [Block128; PACKED_LANES] =
                std::array::from_fn(|_| Block128::from(rng.gen::<u128>()));

            let pa = PackedBlock128::from_array(a);
            let packed_result = pa.scalar_mul(scalar).to_array();

            for i in 0..PACKED_LANES {
                assert_eq!(packed_result[i], a[i] * scalar);
            }
        }
    }
}
