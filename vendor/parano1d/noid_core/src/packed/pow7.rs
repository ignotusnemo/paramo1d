// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! Fast `x ↦ x^7` on `Block128` for the Poseidon2b S-box.
//!
//! In GF(2^128) squaring is the Frobenius endomorphism — a *linear*
//! operation `(a+b)^2 = a^2 + b^2`. So `x^7` decomposes as
//!
//! ```text
//!   s  = x
//!   s2 = s.square()           // free (linear)
//!   s3 = s2 * s                // 1 CLMUL
//!   s4 = s2.square()           // free (linear)
//!   s7 = s4 * s3               // 1 CLMUL
//! ```
//!
//! Total: **2 multiplications + 2 Frobenius squarings**. The previous
//! naive `x.pow(7)` performs 4 multiplications (or 6 in a generic
//! square-and-multiply), so this saves ~50% of the per-element work
//! inside the Spine Kill-Shot degree-7 sumcheck (≈ 9 evaluations × 15
//! rounds × 32 768 cells).

use super::PackedBlock128;
use crate::hardware::{clmul_gcm, square_flat_u128};
use crate::Block128;

/// Compute `x^7` via Frobenius squaring (tower basis).
#[inline(always)]
pub fn pow7_block128(x: Block128) -> Block128 {
    let s2 = x.square();
    let s3 = s2 * x;
    let s4 = s2.square();
    s4 * s3
}

/// Flat-basis `x^7` via Frobenius squaring + CLMUL.
///
/// Same algebraic structure as `pow7_block128` but every multiplication
/// is `clmul_gcm` and every squaring is `square_flat_u128`. The caller
/// owns the basis: `x` must already be in flat-basis, and the result
/// is in flat-basis.
#[inline(always)]
pub fn pow7_flat_block128(x: u128) -> u128 {
    let s2 = square_flat_u128(x);
    let s3 = clmul_gcm(s2, x);
    let s4 = square_flat_u128(s2);
    clmul_gcm(s4, s3)
}

/// Per-lane `x^7` over a packed value. Lane independence makes this a
/// straightforward unroll over `to_array` / `from_array`; the actual
/// SIMD win comes from the squaring helpers inside `Block128::square`
/// (see `simd_square_avx2.rs`).
#[inline(always)]
pub fn pow7_packed(x: PackedBlock128) -> PackedBlock128 {
    let arr = x.to_array();
    let out = arr.map(pow7_block128);
    PackedBlock128::from_array(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TowerField;
    use rand::Rng;

    fn naive_pow7(x: Block128) -> Block128 {
        // x · x · x · x · x · x · x
        let mut acc = Block128::ONE;
        for _ in 0..7 {
            acc *= x;
        }
        acc
    }

    #[test]
    fn pow7_matches_naive_random() {
        let mut rng = rand::thread_rng();
        for _ in 0..1000 {
            let x = Block128::from(rng.gen::<u128>());
            assert_eq!(pow7_block128(x), naive_pow7(x));
        }
    }

    #[test]
    fn pow7_zero_one_edge_cases() {
        assert_eq!(pow7_block128(Block128::ZERO), Block128::ZERO);
        assert_eq!(pow7_block128(Block128::ONE), Block128::ONE);
    }

    #[test]
    fn pow7_packed_matches_per_lane() {
        let mut rng = rand::thread_rng();
        let arr: [Block128; super::super::PACKED_LANES] =
            std::array::from_fn(|_| Block128::from(rng.gen::<u128>()));
        let p = PackedBlock128::from_array(arr);
        let got = pow7_packed(p).to_array();
        let want: [Block128; super::super::PACKED_LANES] = arr.map(pow7_block128);
        assert_eq!(got, want);
    }

    #[test]
    fn pow7_flat_matches_pow7_tower_via_basis_change() {
        use crate::hardware::{flat_to_tower_u128, tower_to_flat_u128};
        let mut rng = rand::thread_rng();
        for _ in 0..1000 {
            let x_tower = Block128::from(rng.gen::<u128>());
            let x_flat = tower_to_flat_u128(x_tower.to_u128());
            let y_flat = pow7_flat_block128(x_flat);
            let y_tower = Block128::from(flat_to_tower_u128(y_flat));
            assert_eq!(y_tower, pow7_block128(x_tower));
        }
    }

    #[test]
    fn pow7_is_multiplicative() {
        // (xy)^7 = x^7 · y^7
        let mut rng = rand::thread_rng();
        for _ in 0..100 {
            let x = Block128::from(rng.gen::<u128>());
            let y = Block128::from(rng.gen::<u128>());
            assert_eq!(pow7_block128(x * y), pow7_block128(x) * pow7_block128(y));
        }
    }
}
