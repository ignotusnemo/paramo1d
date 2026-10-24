// SPDX-License-Identifier: Apache-2.0
// Adapted from binius64. Copyright (C) 2026 Paranoid Zero.

//! Variable folding for multilinear polynomials.

use crate::{Block128, TowerField};

/// Fold the highest-index variable in a multilinear evaluation vector.
///
/// Given evaluations v[0..2^n] and a folding coordinate r, this computes
/// evaluations of the (n-1)-variate polynomial f(X_0, ..., X_{n-2}, r).
///
/// For each pair (`v[j]`, `v[j + half]`), the new value is:
/// ```text
/// v[j] += r * (v[j + half] - v[j])
/// ```
///
/// The vector is truncated to half its length. Runs in O(2^{n-1}) time.
pub fn fold_highest_var_inplace<F: TowerField>(evals: &mut Vec<F>, r: F) {
    let half = evals.len() / 2;
    assert!(half > 0, "evals must have at least 2 elements");

    for j in 0..half {
        let delta = evals[j + half] - evals[j];
        evals[j] += r * delta;
    }

    evals.truncate(half);
}

/// Parallel version of [`fold_highest_var_inplace`] for large tables.
///
/// Uses rayon when `half >= threshold` to saturate available cores.
/// Semantically identical to the scalar version.
pub fn fold_highest_var_par<F>(evals: &mut Vec<F>, r: F)
where
    F: TowerField + Send + Sync,
{
    use rayon::prelude::*;
    let half = evals.len() / 2;
    assert!(half > 0, "evals must have at least 2 elements");
    if half >= 1024 {
        let (lo, hi) = evals.split_at_mut(half);
        lo.par_iter_mut().zip(hi.par_iter()).for_each(|(l, h)| {
            *l += r * (*h - *l);
        });
    } else {
        for j in 0..half {
            let delta = evals[j + half] - evals[j];
            evals[j] += r * delta;
        }
    }
    evals.truncate(half);
}

/// Fold a specific variable index (not necessarily the highest).
///
/// `var_index` specifies which variable to fold (0 = lowest, n-1 = highest).
/// The vector length is 2^n. After folding, length becomes 2^{n-1}.
pub fn fold_variable_inplace<F: TowerField>(evals: &mut Vec<F>, r: F, var_index: usize) {
    let n = evals.len().trailing_zeros() as usize;
    assert!(
        var_index < n,
        "var_index {} out of range for n={}",
        var_index,
        n
    );

    let half = 1 << var_index;
    let stride = 1 << (var_index + 1);

    for block_start in (0..evals.len()).step_by(stride) {
        for j in 0..half {
            let lo_idx = block_start + j;
            let hi_idx = block_start + j + half;
            let delta = evals[hi_idx] - evals[lo_idx];
            evals[lo_idx] += r * delta;
        }
    }

    // Compress: remove every element at position j where (j >> var_index) & 1 == 1
    let mut write_idx = 0;
    for read_idx in 0..evals.len() {
        if (read_idx >> var_index) & 1 == 0 {
            evals[write_idx] = evals[read_idx];
            write_idx += 1;
        }
    }
    evals.truncate(evals.len() / 2);
}

// ---------------------------------------------------------------------------
// Packed variants for Block128
// ---------------------------------------------------------------------------

/// Fold MLE at the highest variable using packed operations.
pub fn fold_highest_packed(poly: &[Block128], r: Block128) -> Vec<Block128> {
    use crate::packed::{pack_slice, unpack_slice, PackedBlock128};

    let packed = pack_slice(poly);
    let half = packed.len() / 2;
    let _r_packed = PackedBlock128::broadcast(r);

    let result: Vec<PackedBlock128> = (0..half)
        .map(|i| {
            let lo = packed[i];
            let hi = packed[i + half];
            let diff = hi.xor(lo);
            let scaled = diff.scalar_mul(r);
            lo.xor(scaled)
        })
        .collect();

    unpack_slice(&result).to_vec()
}

/// Fold MLE at the lowest variable using packed operations.
pub fn fold_lowest_packed(poly: &[Block128], r: Block128) -> Vec<Block128> {
    use crate::packed::{pack_slice_mut, PackedBlock128};

    let mut data = poly.to_vec();
    let n = data.len();
    let stride = 1;

    let packed = pack_slice_mut(&mut data);
    let pairs = packed.len() / (2 * stride);

    let _r_packed = PackedBlock128::broadcast(r);

    for pair in 0..pairs {
        let lo_idx = 2 * pair * stride;
        let hi_idx = lo_idx + stride;

        for j in 0..stride {
            let lo = packed[lo_idx + j];
            let hi = packed[hi_idx + j];
            let diff = hi.xor(lo);
            let scaled = diff.scalar_mul(r);
            packed[lo_idx + j] = lo.xor(scaled);
        }
    }

    // Interleave: take lo elements
    let mut result = Vec::with_capacity(n / 2);
    for pair in 0..pairs {
        let lo_idx = 2 * pair * stride;
        for j in 0..stride {
            let arr = packed[lo_idx + j].to_array();
            result.extend_from_slice(&arr);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::super::evaluate::evaluate_inplace_scalars;
    use super::*;
    use crate::Block128;

    type F = Block128;

    #[test]
    fn test_fold_highest() {
        // f(x, y) = a + b*x + c*y + d*x*y
        let a = F::from(5u8);
        let b = F::from(2u8);
        let c = F::from(3u8);
        let d = F::from(7u8);

        let mut evals = vec![a, a + b, a + c, a + b + c + d];

        // Fold y=1: result should be f(x, 1) = a + c + (b + d)*x
        fold_highest_var_inplace(&mut evals, F::ONE);
        assert_eq!(evals.len(), 2);
        assert_eq!(evals[0], a + c); // f(0, 1)
        assert_eq!(evals[1], a + b + c + d); // f(1, 1)
    }

    #[test]
    fn test_fold_lowest_variable() {
        // f(x, y) = a + b*x + c*y + d*x*y
        let a = F::from(5u8);
        let b = F::from(2u8);
        let c = F::from(3u8);
        let d = F::from(7u8);

        let mut evals = vec![a, a + b, a + c, a + b + c + d];

        // Fold x=1 (var_index=0): result should be f(1, y) = a + b + (c + d)*y
        fold_variable_inplace(&mut evals, F::ONE, 0);
        assert_eq!(evals.len(), 2);
        assert_eq!(evals[0], a + b); // f(1, 0)
        assert_eq!(evals[1], a + b + c + d); // f(1, 1)
    }

    #[test]
    fn test_fold_consistency_with_evaluate() {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let n = 6;
        let evals_orig: Vec<F> = (0..(1 << n)).map(|_| F::from(rng.gen::<u128>())).collect();
        let point: Vec<F> = (0..n).map(|_| F::from(rng.gen::<u128>())).collect();

        let result_full = evaluate_inplace_scalars(evals_orig.clone(), &point);

        // Fold all but first variable using fold_highest, then evaluate last directly
        let mut partial = evals_orig.clone();
        for &coord in point.iter().skip(1).rev() {
            fold_highest_var_inplace(&mut partial, coord);
        }
        let result_partial = evaluate_inplace_scalars(partial, &[point[0]]);

        assert_eq!(result_full, result_partial);
    }
}
