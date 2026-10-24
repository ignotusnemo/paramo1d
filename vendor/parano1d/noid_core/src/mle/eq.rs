// SPDX-License-Identifier: Apache-2.0
// Adapted from binius64. Copyright (C) 2026 Paranoid Zero.

//! Equality indicator polynomial for multilinear extensions.
//! Computes tensor products of (1 - r_i, r_i) over the boolean hypercube.
use crate::{Block128, TowerField};

/// Evaluate the 2-variate equality indicator: eq(X, Y) = X*Y + (1-X)*(1-Y).
/// In GF(2): eq(X, Y) = X + Y + 1.
#[inline(always)]
pub fn eq_one_var<F: TowerField>(x: F, y: F) -> F {
    let one = F::ONE;
    x * y + (one - x) * (one - y)
}

/// Evaluate the full equality indicator polynomial at two length-n slices.
/// eq(x_0..x_{n-1}, y_0..y_{n-1}) = ∏_{i=0}^{n-1} eq_one_var(x_i, y_i)
pub fn eq_ind<F: TowerField>(x: &[F], y: &[F]) -> F {
    assert_eq!(x.len(), y.len());
    x.iter()
        .zip(y.iter())
        .map(|(xi, yi)| eq_one_var(*xi, *yi))
        .fold(F::ONE, |acc, val| acc * val)
}

/// Compute the partial evaluation of the equality indicator polynomial.
///
/// Returns the tensor product (1 - r_0, r_0) ⊗ ... ⊗ (1 - r_{n-1}, r_{n-1})
/// as a `Vec<F>` of length 2^n.
pub fn eq_ind_partial_eval<F: TowerField>(point: &[F]) -> Vec<F> {
    if point.is_empty() {
        return vec![F::ONE];
    }

    let mut result = vec![F::ONE];

    for &r_i in point {
        let len = result.len();
        result.reserve(len);
        for j in 0..len {
            // val * r_i computed once
            let prod = result[j] * r_i;
            // lo = val * (1 - r_i) = val - val*r_i
            result[j] -= prod;
            // hi = val * r_i
            result.push(prod);
        }
    }

    result
}

/// Compute the tensor product (1 - r_{k-1}, r_{k-1}) ⊗ ... ⊗ (1 - r_0, r_0) ⊗ v.
/// This is the left-tensor variant.
pub fn tensor_prod_eq_ind_prepend<F: TowerField>(values: &mut Vec<F>, extra_coords: &[F]) {
    for &r_i in extra_coords.iter().rev() {
        let len = values.len();
        values.reserve(len);
        for j in (0..len).rev() {
            let eval = values[j];
            // values[2*j] = eval * (1 - r_i)
            values[2 * j] = eval * (F::ONE - r_i);
            // values[2*j + 1] = eval * r_i
            values.push(eval * r_i);
        }
    }
}

/// Truncate the equality indicator expansion to fewer variables by summing halves.
pub fn eq_ind_truncate_low_inplace<F: TowerField>(values: &mut Vec<F>, truncated_log_len: usize) {
    let current_log_len = values.len().trailing_zeros() as usize;
    assert!(truncated_log_len <= current_log_len);

    for _log_len in (truncated_log_len..current_log_len).rev() {
        let half = values.len() / 2;
        for j in 0..half {
            values[j] = values[j] + values[j + half];
        }
        values.truncate(half);
    }
}

// ---------------------------------------------------------------------------
// Packed variant for Block128
// ---------------------------------------------------------------------------

/// Compute the equality indicator tensor using packed operations.
pub fn eq_ind_packed(point: &[Block128], num_vars: usize) -> Vec<Block128> {
    let size = 1usize << num_vars;
    let mut result = vec![Block128::ZERO; size];
    result[0] = Block128::ONE;

    let mut current_size = 1;

    for &r in point.iter() {
        let one_plus_r = Block128::ONE + r;

        for i in 0..current_size {
            result[i + current_size] = result[i] * r;
            result[i] *= one_plus_r;
        }
        current_size *= 2;
    }

    result
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::Block128;

    type F = Block128;

    #[test]
    fn test_eq_ind_empty() {
        let empty: &[F] = &[];
        assert_eq!(eq_ind(empty, empty), F::ONE);
    }
    #[test]
    fn test_eq_ind_identity() {
        let x = vec![F::ONE, F::ZERO];
        let y = vec![F::ONE, F::ZERO];
        assert_eq!(eq_ind(&x, &y), F::ONE);
    }
    #[test]
    fn test_eq_ind_partial_eval_empty() {
        let result = eq_ind_partial_eval::<F>(&[]);
        assert_eq!(result, vec![F::ONE]);
    }
    #[test]
    fn test_eq_ind_partial_eval_two_vars() {
        let r0 = F::from(2u8);
        let r1 = F::from(3u8);
        let result = eq_ind_partial_eval(&[r0, r1]);
        let expected = vec![
            (F::ONE - r0) * (F::ONE - r1),
            r0 * (F::ONE - r1),
            (F::ONE - r0) * r1,
            r0 * r1,
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_eq_ind_partial_eval_consistency() {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let n_vars = 6;
        let point: Vec<F> = (0..n_vars).map(|_| F::from(rng.gen::<u128>())).collect();
        let result = eq_ind_partial_eval(&point);

        for (i, &res_val) in result.iter().enumerate() {
            let mut bits = Vec::with_capacity(n_vars);
            for b in 0..n_vars {
                bits.push(if (i >> b) & 1 == 1 { F::ONE } else { F::ZERO });
            }
            // eq_ind(x, point) should match tensor product result
            let eq_val = eq_ind(&bits, &point);
            assert_eq!(res_val, eq_val, "mismatch at index {i}");
        }
    }
}
