// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! Additive NTT (Number Theoretic Transform) for binary tower fields.

use crate::TowerField;

/// Forward additive NTT.
///
/// Transforms a vector of polynomial coefficients into evaluations
/// over an additive subspace.
///
/// # Arguments
/// * `coeffs` - Polynomial coefficients (length must be power of 2)
/// * `basis` - Basis elements for the additive subspace
///
/// # Returns
/// Evaluations over the additive subspace.
#[allow(unused_variables)]
pub fn forward_ntt<F: TowerField>(coeffs: &[F], basis: &[F]) -> Vec<F> {
    let n = coeffs.len();
    assert!(n.is_power_of_two(), "length must be power of two");
    assert_eq!(
        basis.len(),
        n.trailing_zeros() as usize,
        "basis must have log2(n) elements"
    );

    let mut evals = coeffs.to_vec();
    let mut len = 1;

    for &b in basis.iter() {
        for start in (0..n).step_by(2 * len) {
            for i in start..start + len {
                let u = evals[i];
                let v = evals[i + len];
                // EVEN = u + v, ODD = (u + v) * b + v
                let sum = u + v;
                evals[i] = sum;
                evals[i + len] = sum * b + v;
            }
        }
        len *= 2;
    }

    evals
}

/// Inverse additive NTT.
///
/// Transforms evaluations back to polynomial coefficients.
#[allow(unused_variables)]
pub fn inverse_ntt<F: TowerField>(evals: &[F], basis: &[F]) -> Vec<F> {
    let n = evals.len();
    assert!(n.is_power_of_two(), "length must be power of two");

    let mut coeffs = evals.to_vec();
    let mut len = n / 2;

    for &b in basis.iter().rev() {
        for start in (0..n).step_by(2 * len) {
            for i in start..start + len {
                let even = coeffs[i];
                let odd = coeffs[i + len];
                // Invert the forward transform:
                // forward: evens = u+v, odds = (u+v)*b + v = evens*b + v
                // So: v = odds + evens*b, u = even + v
                let v = odd + even * b;
                coeffs[i] = even + v;
                coeffs[i + len] = v;
            }
        }
        len /= 2;
    }

    coeffs
}

// ---------------------------------------------------------------------------
// Parallel variants for Block128
// ---------------------------------------------------------------------------

use crate::hardware::{clmul_gcm, flat_to_tower_u128, tower_to_flat_u128};
use crate::packed::{PackedBlock128, PACKED_LANES};
use crate::Block128;
use rayon::prelude::*;

/// Minimum size to justify parallel NTT.
const NTT_PARALLEL_THRESHOLD: usize = 512;

/// Forward additive NTT with parallel, flat-basis SIMD butterflies.
///
/// Strategy: convert the whole buffer to flat basis once, run every level
/// using raw CLMUL butterflies (with packed SIMD when the butterfly stride
/// is at least `PACKED_LANES`), then convert back. This replaces one
/// tower-basis multiplication per butterfly (~95 ns) with a single CLMUL
/// (~5 ns) and amortises basis conversion over the whole transform.
pub fn forward_ntt_parallel(coeffs: &[Block128], basis: &[Block128]) -> Vec<Block128> {
    let mut out = coeffs.to_vec();
    forward_ntt_parallel_inplace(&mut out, basis);
    out
}

/// In-place variant of [`forward_ntt_parallel`]. Avoids the output `Vec`
/// allocation + copy so callers with a pre-sized destination buffer (e.g.
/// `Code::new_parallel`) can transform directly into it.
pub fn forward_ntt_parallel_inplace(data: &mut [Block128], basis: &[Block128]) {
    let n = data.len();
    assert!(n.is_power_of_two(), "length must be power of two");
    assert_eq!(basis.len(), n.trailing_zeros() as usize);

    // Work buffer in flat-basis u128. Butterflies run on this representation
    // because `clmul_gcm` / `flat_scalar_mul` need the flat basis; we convert
    // once on the way in and once on the way out.
    let mut evals_flat: Vec<u128> = if n >= NTT_PARALLEL_THRESHOLD {
        data.par_iter().map(|c| tower_to_flat_u128(c.0)).collect()
    } else {
        data.iter().map(|c| tower_to_flat_u128(c.0)).collect()
    };

    let mut len = 1usize;
    for &b in basis.iter() {
        let b_flat = tower_to_flat_u128(b.0);
        let block_size = 2 * len;

        if len >= PACKED_LANES {
            // SIMD-friendly: u and v are contiguous runs of length `len`,
            // so we can load PACKED_LANES consecutive lanes at a time.
            if n >= NTT_PARALLEL_THRESHOLD {
                evals_flat
                    .par_chunks_exact_mut(block_size)
                    .for_each(|chunk| ntt_butterfly_block_simd(chunk, len, b_flat));
            } else {
                for chunk in evals_flat.chunks_exact_mut(block_size) {
                    ntt_butterfly_block_simd(chunk, len, b_flat);
                }
            }
        } else if n >= NTT_PARALLEL_THRESHOLD {
            evals_flat
                .par_chunks_exact_mut(block_size)
                .for_each(|chunk| ntt_butterfly_block_scalar(chunk, len, b_flat));
        } else {
            for chunk in evals_flat.chunks_exact_mut(block_size) {
                ntt_butterfly_block_scalar(chunk, len, b_flat);
            }
        }
        len *= 2;
    }

    if n >= NTT_PARALLEL_THRESHOLD {
        data.par_iter_mut()
            .zip(evals_flat.par_iter())
            .for_each(|(slot, &v)| {
                *slot = Block128(flat_to_tower_u128(v));
            });
    } else {
        for (slot, v) in data.iter_mut().zip(evals_flat) {
            *slot = Block128(flat_to_tower_u128(v));
        }
    }
}

#[inline(always)]
fn ntt_butterfly_block_scalar(chunk: &mut [u128], len: usize, b_flat: u128) {
    for i in 0..len {
        let u = chunk[i];
        let v = chunk[i + len];
        let sum = u ^ v;
        chunk[i] = sum;
        chunk[i + len] = clmul_gcm(sum, b_flat) ^ v;
    }
}

#[inline(always)]
fn ntt_butterfly_block_simd(chunk: &mut [u128], len: usize, b_flat: u128) {
    debug_assert!(len.is_multiple_of(PACKED_LANES));
    let lanes = PACKED_LANES;
    let mut i = 0;
    while i + lanes <= len {
        let u = load_packed(&chunk[i..i + lanes]);
        let v = load_packed(&chunk[i + len..i + len + lanes]);
        let sum = u.xor(v);
        let prod = sum.flat_scalar_mul(b_flat);
        let new_v = prod.xor(v);
        store_packed(&mut chunk[i..i + lanes], sum);
        store_packed(&mut chunk[i + len..i + len + lanes], new_v);
        i += lanes;
    }
    // Tail (shouldn't happen when len is a power of 2 >= lanes, but be safe).
    while i < len {
        let u = chunk[i];
        let v = chunk[i + len];
        let sum = u ^ v;
        chunk[i] = sum;
        chunk[i + len] = clmul_gcm(sum, b_flat) ^ v;
        i += 1;
    }
}

#[inline(always)]
fn load_packed(src: &[u128]) -> PackedBlock128 {
    debug_assert_eq!(src.len(), PACKED_LANES);
    let mut arr = [Block128::ZERO; PACKED_LANES];
    for i in 0..PACKED_LANES {
        arr[i] = Block128(src[i]);
    }
    PackedBlock128::from_array(arr)
}

#[inline(always)]
fn store_packed(dst: &mut [u128], p: PackedBlock128) {
    debug_assert_eq!(dst.len(), PACKED_LANES);
    let arr = p.to_array();
    for i in 0..PACKED_LANES {
        dst[i] = arr[i].0;
    }
}

/// Inverse additive NTT with parallel, flat-basis SIMD butterflies.
pub fn inverse_ntt_parallel(evals: &[Block128], basis: &[Block128]) -> Vec<Block128> {
    let n = evals.len();
    assert!(n.is_power_of_two(), "length must be power of two");

    let mut coeffs_flat: Vec<u128> = evals.iter().map(|c| tower_to_flat_u128(c.0)).collect();
    let mut len = n / 2;

    for &b in basis.iter().rev() {
        let b_flat = tower_to_flat_u128(b.0);
        let block_size = 2 * len;

        if len >= PACKED_LANES {
            if n >= NTT_PARALLEL_THRESHOLD {
                coeffs_flat
                    .par_chunks_exact_mut(block_size)
                    .for_each(|chunk| inverse_butterfly_block_simd(chunk, len, b_flat));
            } else {
                for chunk in coeffs_flat.chunks_exact_mut(block_size) {
                    inverse_butterfly_block_simd(chunk, len, b_flat);
                }
            }
        } else if n >= NTT_PARALLEL_THRESHOLD {
            coeffs_flat
                .par_chunks_exact_mut(block_size)
                .for_each(|chunk| inverse_butterfly_block_scalar(chunk, len, b_flat));
        } else {
            for chunk in coeffs_flat.chunks_exact_mut(block_size) {
                inverse_butterfly_block_scalar(chunk, len, b_flat);
            }
        }
        len /= 2;
    }

    coeffs_flat
        .into_iter()
        .map(|v| Block128(flat_to_tower_u128(v)))
        .collect()
}

#[inline(always)]
fn inverse_butterfly_block_scalar(chunk: &mut [u128], len: usize, b_flat: u128) {
    for i in 0..len {
        let even = chunk[i];
        let odd = chunk[i + len];
        let v = odd ^ clmul_gcm(even, b_flat);
        chunk[i] = even ^ v;
        chunk[i + len] = v;
    }
}

#[inline(always)]
fn inverse_butterfly_block_simd(chunk: &mut [u128], len: usize, b_flat: u128) {
    let lanes = PACKED_LANES;
    let mut i = 0;
    while i + lanes <= len {
        let even = load_packed(&chunk[i..i + lanes]);
        let odd = load_packed(&chunk[i + len..i + len + lanes]);
        let prod = even.flat_scalar_mul(b_flat);
        let v = odd.xor(prod);
        let new_even = even.xor(v);
        store_packed(&mut chunk[i..i + lanes], new_even);
        store_packed(&mut chunk[i + len..i + len + lanes], v);
        i += lanes;
    }
    while i < len {
        let even = chunk[i];
        let odd = chunk[i + len];
        let v = odd ^ clmul_gcm(even, b_flat);
        chunk[i] = even ^ v;
        chunk[i + len] = v;
        i += 1;
    }
}

// ---------------------------------------------------------------------------
// AdditiveNTT — structured wrapper for FRI encoding / folding
// ---------------------------------------------------------------------------

/// Manages a canonical basis `1, 2, 4, 8, ...` for additive subspaces of
/// `GF(2^128)` and provides the twiddle lookup that FRI folding needs.
#[derive(Debug, Clone)]
pub struct AdditiveNTT<F: TowerField> {
    basis: Vec<F>,
}

impl<F: TowerField> AdditiveNTT<F> {
    /// Create an NTT object for vectors of length `2^log_size`.
    pub fn new(log_size: usize) -> Self {
        let basis: Vec<F> = (0..log_size).map(|i| F::from(1u128 << i)).collect();
        Self { basis }
    }

    /// Forward transform on `data` (length = power of two).
    /// `round` selects the starting offset inside the basis (coset).
    pub fn forward_transform(&self, data: &mut [F], round: u32, _subspace: u32) {
        let start = round as usize;
        let log_n = data.len().trailing_zeros() as usize;
        let end = start + log_n;
        let owned_basis;
        let sub_basis = if end <= self.basis.len() {
            &self.basis[start..end]
        } else {
            owned_basis = (start..end)
                .map(|i| F::from(1u128 << i))
                .collect::<Vec<_>>();
            &owned_basis
        };
        let transformed = forward_ntt(data, sub_basis);
        data.copy_from_slice(&transformed);
    }

    /// Evaluate the subspace polynomial at index `idx` for the given round.
    ///
    /// In additive NTT the twiddle for round `r` and pair index `idx` is the
    /// sum of `basis[j]` over all set bits `j < r` in `idx`.
    pub fn get_subspace_eval(&self, round: usize, idx: usize) -> F {
        let mut result = F::ZERO;
        for j in 0..round {
            if (idx >> j) & 1 == 1 {
                result += self.basis[j];
            }
        }
        result
    }

    /// Number of basis elements (log of max supported vector length).
    pub fn log_size(&self) -> usize {
        self.basis.len()
    }
}

// ---------------------------------------------------------------------------
// Block128-specialized parallel AdditiveNTT
// ---------------------------------------------------------------------------

impl AdditiveNTT<Block128> {
    /// Forward transform using parallel butterflies (Block128 only).
    ///
    /// Replaces the scalar `forward_transform` with `forward_ntt_parallel`
    /// for all sizes above the parallel threshold.
    pub fn forward_transform_parallel(&self, data: &mut [Block128], round: u32, _subspace: u32) {
        let start = round as usize;
        let log_n = data.len().trailing_zeros() as usize;
        let end = start + log_n;
        let owned_basis;
        let sub_basis = if end <= self.basis.len() {
            &self.basis[start..end]
        } else {
            owned_basis = (start..end)
                .map(|i| Block128::from(1u128 << i))
                .collect::<Vec<_>>();
            &owned_basis
        };
        forward_ntt_parallel_inplace(data, sub_basis);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Block128;

    type F = Block128;

    #[test]
    fn test_ntt_roundtrip() {
        use rand::Rng;
        let mut rng = rand::thread_rng();

        let n = 8;
        let coeffs: Vec<F> = (0..n).map(|_| F::from(rng.gen::<u128>())).collect();
        let basis: Vec<F> = (0..3).map(|i| F::from(1u128 << i)).collect();

        let evals = forward_ntt(&coeffs, &basis);
        let recovered = inverse_ntt(&evals, &basis);

        assert_eq!(coeffs, recovered);
    }

    #[test]
    fn test_additive_ntt_struct() {
        use rand::Rng;
        let mut rng = rand::thread_rng();

        let ntt = AdditiveNTT::<F>::new(4);
        let mut data: Vec<F> = (0..16).map(|_| F::from(rng.gen::<u128>())).collect();
        let original = data.clone();

        ntt.forward_transform(&mut data, 0, 0);
        // After forward + inverse we should recover original
        let basis: Vec<F> = (0..4).map(|i| F::from(1u128 << i)).collect();
        let recovered = inverse_ntt(&data, &basis);
        assert_eq!(original, recovered);
    }

    #[test]
    fn test_subspace_eval_consistency() {
        let ntt = AdditiveNTT::<F>::new(5);
        // For round 0, every idx must map to ZERO (empty sum).
        for idx in 0..8 {
            assert_eq!(ntt.get_subspace_eval(0, idx), F::ZERO);
        }
        // For round 1, only bit 0 matters.
        assert_eq!(ntt.get_subspace_eval(1, 0), F::ZERO);
        assert_eq!(ntt.get_subspace_eval(1, 1), ntt.basis[0]);
    }
}
