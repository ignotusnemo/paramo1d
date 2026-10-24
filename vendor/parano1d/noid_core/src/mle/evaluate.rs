// SPDX-License-Identifier: Apache-2.0
// Adapted from binius64. Copyright (C) 2026 Paranoid Zero.

//! Multilinear polynomial evaluation over the boolean hypercube.

use super::fold::fold_highest_var_inplace;
use crate::packed::PACKED_LANES;
use crate::{Block128, TowerField};

/// Evaluate a multilinear polynomial at a point using in-place folding.
pub fn evaluate_inplace_scalars<F: TowerField>(mut evals: Vec<F>, point: &[F]) -> F {
    let n = point.len();
    assert_eq!(
        evals.len(),
        1 << n,
        "eval length {} must equal 2^{}",
        evals.len(),
        n
    );

    for &coord in point.iter().rev() {
        fold_highest_var_inplace(&mut evals, coord);
    }

    assert_eq!(evals.len(), 1);
    evals[0]
}

/// Convenience function: evaluate without consuming the input.
pub fn evaluate_slice<F: TowerField>(evals: &[F], point: &[F]) -> F {
    evaluate_inplace_scalars(evals.to_vec(), point)
}

/// Evaluate a multilinear polynomial using a caller-provided scratch buffer.
///
/// This avoids allocating a new `Vec` on every call by reusing the provided
/// scratch buffer. The buffer is cleared and resized as needed.
///
/// # Performance
///
/// When called in a hot loop (e.g., parallel evaluation of many columns),
/// this eliminates ~800 MB of peak allocations for 50 columns × 2^20 elements.
pub fn evaluate_slice_with_scratch<F: TowerField>(
    evals: &[F],
    point: &[F],
    scratch: &mut Vec<F>,
) -> F {
    // Reuse the caller's buffer: clear (keeps capacity) + refill.
    // IMPORTANT: must NOT use std::mem::take — that would move the Vec out
    // and destroy the reuse, allocating fresh on every call.
    scratch.clear();
    scratch.extend_from_slice(evals);
    // Fold in-place without consuming scratch, so the capacity is retained
    // for the next call on this thread.
    for &coord in point.iter().rev() {
        fold_highest_var_inplace(scratch, coord);
    }
    debug_assert_eq!(scratch.len(), 1, "fold must reduce to a single element");
    scratch[0]
}

/// Evaluate an MLE in flat (GCM) basis using a caller-supplied scratch buffer.
///
/// Same as [`evaluate_flat`] but reuses `scratch` to avoid per-call allocation.
/// Thread-local usage eliminates all allocations across millions of calls.
/// The fold uses `clmul_gcm` (flat basis) which is ~7-8x faster than the
/// tower-basis Karatsuba multiply used by [`evaluate_slice_with_scratch`].
pub fn evaluate_flat_with_scratch(
    poly: &[Block128],
    point: &[Block128],
    scratch: &mut Vec<u128>,
    point_flat_scratch: &mut Vec<u128>,
) -> Block128 {
    use crate::hardware::{clmul_gcm, flat_to_tower_u128, tower_to_flat_u128};
    let n = point.len();
    if n == 0 {
        return poly[0];
    }
    // Reuse scratch: convert tower → flat (fills scratch from poly).
    scratch.clear();
    scratch.extend(poly.iter().map(|v| tower_to_flat_u128(v.0)));
    // Pre-convert eval point to flat.
    point_flat_scratch.clear();
    point_flat_scratch.extend(point.iter().rev().map(|v| tower_to_flat_u128(v.0)));
    // Fold in flat basis using clmul_gcm (~4 ns/op vs ~30 ns for tower mul).
    for &r_flat in point_flat_scratch.iter() {
        let half = scratch.len() / 2;
        for j in 0..half {
            let lo = scratch[j];
            let hi = scratch[j + half];
            scratch[j] = lo ^ clmul_gcm(r_flat, hi ^ lo);
        }
        scratch.truncate(half);
    }
    Block128::from(flat_to_tower_u128(scratch[0]))
}

/// Evaluate an MLE in flat (GCM) basis for ~20x speedup over tower-basis mul.
///
/// Converts the table to flat basis, folds using `clmul_gcm`, and returns
/// the result converted back to tower. Ideal for verifier hot paths where
/// the table is large and the point is in tower basis.
pub fn evaluate_flat(poly: &[Block128], point: &[Block128]) -> Block128 {
    use crate::hardware::{clmul_gcm, flat_to_tower_u128, tower_to_flat_u128};

    let n = point.len();
    assert_eq!(poly.len(), 1 << n, "poly length must be 2^n");

    if n == 0 {
        return poly[0];
    }

    let mut buf: Vec<u128> = poly.iter().map(|v| tower_to_flat_u128(v.0)).collect();
    let point_flat: Vec<u128> = point
        .iter()
        .rev()
        .map(|v| tower_to_flat_u128(v.0))
        .collect();

    for &r_flat in &point_flat {
        let half = buf.len() / 2;
        for j in 0..half {
            let lo = buf[j];
            let hi = buf[j + half];
            buf[j] = lo ^ clmul_gcm(r_flat, hi ^ lo);
        }
        buf.truncate(half);
    }

    Block128::from(flat_to_tower_u128(buf[0]))
}

/// Evaluate an MLE whose table is already stored in flat (GCM) basis as `Vec<u128>`.
///
/// Skips the per-element `tower_to_flat_u128` conversion that `evaluate_flat` performs,
/// saving ~1 ns × table_size per call. The evaluation point is still in tower basis
/// and is converted internally. Result is returned in tower basis.
pub fn evaluate_preflat(poly_flat: &[u128], point: &[Block128]) -> Block128 {
    use crate::hardware::{clmul_gcm, flat_to_tower_u128, tower_to_flat_u128};

    let n = point.len();
    assert_eq!(poly_flat.len(), 1 << n, "poly length must be 2^n");

    if n == 0 {
        return Block128::from(flat_to_tower_u128(poly_flat[0]));
    }

    let mut buf: Vec<u128> = poly_flat.to_vec();
    let point_flat: Vec<u128> = point
        .iter()
        .rev()
        .map(|v| tower_to_flat_u128(v.0))
        .collect();

    for &r_flat in &point_flat {
        let half = buf.len() / 2;
        for j in 0..half {
            let lo = buf[j];
            let hi = buf[j + half];
            buf[j] = lo ^ clmul_gcm(r_flat, hi ^ lo);
        }
        buf.truncate(half);
    }

    Block128::from(flat_to_tower_u128(buf[0]))
}

/// Evaluate an MLE using packed fold operations.
pub fn evaluate_packed(poly: &[Block128], point: &[Block128]) -> Block128 {
    use crate::packed::{pack_slice, PackedBlock128};

    // Too small for packed path to be worthwhile — fall back to scalar.
    if poly.len() < PACKED_LANES * 2 || !poly.len().is_multiple_of(PACKED_LANES) {
        return evaluate_slice(poly, point);
    }

    let mut evals: Vec<PackedBlock128> = pack_slice(poly).to_vec();
    let mut point_iter = point.iter().rev();

    while evals.len() > 1 {
        let Some(&r) = point_iter.next() else {
            break;
        };
        let half = evals.len() / 2;
        for i in 0..half {
            let lo = evals[i];
            let hi = evals[i + half];
            let diff = hi.xor(lo);
            let scaled = diff.scalar_mul(r);
            evals[i] = lo.xor(scaled);
        }
        evals.truncate(half);
    }

    // Unpack final element and fold any remaining variables scalar-style.
    let mut scalars: Vec<Block128> = evals.into_iter().flat_map(|p| p.to_array()).collect();
    for &r in point_iter {
        fold_highest_var_inplace(&mut scalars, r);
    }

    scalars[0]
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::Block128;
    use rand::Rng;

    type F = Block128;

    #[test]
    fn test_evaluate_at_hypercube_vertex() {
        let n = 4;
        let mut rng = rand::thread_rng();
        let evals: Vec<F> = (0..(1 << n)).map(|_| F::from(rng.gen::<u128>())).collect();

        for i in 0..(1 << n) {
            let point: Vec<F> = (0..n)
                .map(|b| if (i >> b) & 1 == 1 { F::ONE } else { F::ZERO })
                .collect();
            let result = evaluate_slice(&evals, &point);
            assert_eq!(result, evals[i], "mismatch at vertex {i}");
        }
    }

    #[test]
    fn test_evaluate_linear() {
        let a = F::from(5u8);
        let b = F::from(2u8);
        let c = F::from(3u8);
        let d = F::from(7u8);

        let evals = vec![a, a + b, a + c, a + b + c + d];

        assert_eq!(evaluate_slice(&evals, &[F::ZERO, F::ZERO]), a);
        assert_eq!(evaluate_slice(&evals, &[F::ONE, F::ZERO]), a + b);
        assert_eq!(evaluate_slice(&evals, &[F::ZERO, F::ONE]), a + c);
        assert_eq!(evaluate_slice(&evals, &[F::ONE, F::ONE]), a + b + c + d);
    }
}
