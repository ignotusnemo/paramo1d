// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! FRI Verifier.

use noid_core::{AdditiveNTT, Block128, TowerField};

use crate::channel::Channel;
use crate::code::{fold, LOG_RATE};
use crate::hasher::{CryptographicHasher, HashOutput};
use crate::prover::EvalProof;

/// Verify a FRI evaluation proof.
///
/// Returns `Ok(())` if the proof is valid, `Err` with a description otherwise.
///
/// The caller is responsible for having absorbed any commitment that binds
/// the polynomial being opened into the transcript **before** this call —
/// mirrors the contract of [`crate::prover::prove`]. For a standalone
/// (non-batched) opening, callers should absorb the single
/// `FriCommitment` via `channel.observe_fri_commitment(...)`. For the
/// RLC-batched path (§12b), per-column commitments upstream provide the
/// binding and no extra commitment is needed here.
pub fn verify(
    eval_point: &[Block128],
    eval: Block128,
    eval_proof: EvalProof,
    ntt: &AdditiveNTT<Block128>,
    channel: &mut Channel,
    hasher: &dyn CryptographicHasher,
) -> Result<(), String> {
    channel.observe_field_elems(eval_point);
    channel.observe_field_elem(eval);

    let tau = crate::channel::TAU.min(eval_point.len());
    let n = eval_point.len();
    let (right, left) = eval_point.split_at(n - tau);

    let expected_upper = 1usize
        .checked_shl(tau as u32)
        .ok_or_else(|| "tau overflow while sizing upper partial evals".to_string())?;
    if eval_proof.upper_partial_evals.len() != expected_upper {
        return Err(format!(
            "upper_partial_evals length mismatch: expected {}, got {}",
            expected_upper,
            eval_proof.upper_partial_evals.len()
        ));
    }

    // Reconstruct the eq table for the left (high) variables.
    let left_eq = compute_eq_table(left);
    if left_eq.len() != expected_upper {
        return Err("left eq table length mismatch".to_string());
    }

    // Check: Σ left_eq[i] * upper_partial_evals[i] == eval
    let mut derived_eval = Block128::ZERO;
    for (lhs, rhs) in left_eq.iter().zip(eval_proof.upper_partial_evals.iter()) {
        derived_eval += *lhs * *rhs;
    }
    if derived_eval != eval {
        return Err("derived eval does not match claimed eval".to_string());
    }

    // Draw tensor-batching challenge.
    let tensor_batching_point = channel.get_random_points(tau);
    let batching_eq = compute_eq_table(&tensor_batching_point);
    if batching_eq.len() != expected_upper {
        return Err("batching eq-table length mismatch".to_string());
    }

    // Recompute the sum-check claim from the upper partial evaluations.
    let mut sum_check_claim = compute_row_batch(&batching_eq, &eval_proof.upper_partial_evals);

    let rounds = right.len();
    if rounds != eval_proof.sum_check_oracles.len()
        || rounds != eval_proof.fri_oracles.len()
        || rounds != eval_proof.fri_queried_symbols.len()
        || rounds != eval_proof.fri_merkle_paths.len()
    {
        return Err(format!(
            "round count mismatch: expected {rounds}, got sumcheck={}, fri_oracles={}, queried_symbols={}, merkle_paths={}",
            eval_proof.sum_check_oracles.len(),
            eval_proof.fri_oracles.len(),
            eval_proof.fri_queried_symbols.len(),
            eval_proof.fri_merkle_paths.len()
        ));
    }

    let mut random_point = Vec::with_capacity(rounds);
    for (round, oracle) in eval_proof.sum_check_oracles.iter().enumerate().take(rounds) {
        // Core sum-check check: p(0) + p(1) == current claim.
        let sum_check = oracle.evaluate(Block128::ZERO) + oracle.evaluate(Block128::ONE);
        if sum_check != sum_check_claim {
            return Err(format!("Sum of oracle evaluations failed on round {round}"));
        }
        if oracle.coeffs.is_empty() {
            return Err(format!("empty sumcheck oracle at round {round}"));
        }

        // Transcript order (must match prover exactly):
        //   1. Absorb sumcheck oracle coefficients.
        //   2. Absorb the FRI oracle commitment for this round.
        //   3. Squeeze the folding challenge.
        channel.observe_field_elems(&oracle.coeffs);
        let fri_oracle = &eval_proof.fri_oracles[round];
        channel.observe_vector_commitment(fri_oracle);
        let r = channel.get_random_point();

        sum_check_claim = oracle.evaluate(r);
        random_point.push(r);
    }

    // Absorb the final codeword into the transcript.
    if eval_proof.final_codeword.is_empty() {
        return Err("empty final codeword".to_string());
    }
    channel.observe_field_elems(&eval_proof.final_codeword);
    let final_codeword_len = eval_proof.final_codeword.len();

    let query_indices = channel.gen_queries(rounds + LOG_RATE);
    let n_queries = query_indices.len();

    let mut folded_symbols: Vec<Option<Block128>> = vec![None; n_queries];

    // Scratch buffers reused across rounds.
    let mut leaf_pairs: Vec<Block128> = Vec::with_capacity(n_queries * 2);
    let mut leaf_hashes: Vec<HashOutput> = vec![[0u8; 32]; n_queries];
    let mut merkle_pairs: Vec<HashOutput> = Vec::with_capacity(n_queries * 2);
    let mut merkle_next: Vec<HashOutput> = vec![[0u8; 32]; n_queries];

    for (round, oracle) in eval_proof.fri_oracles.iter().enumerate().take(rounds) {
        let mut round_folded = Vec::with_capacity(n_queries);

        let queried_symbols = &eval_proof.fri_queried_symbols[round];
        let merkle_paths = &eval_proof.fri_merkle_paths[round];
        if queried_symbols.len() != n_queries || merkle_paths.len() != n_queries {
            return Err(format!(
                "query vector length mismatch at round {round}: symbols={}, paths={}, expected={n_queries}",
                queried_symbols.len(),
                merkle_paths.len()
            ));
        }

        // Fold-consistency check (round > 0) + collect (s0, s1) pairs for batched leaf hashing.
        leaf_pairs.clear();
        for i in 0..n_queries {
            let qi = query_indices[i];
            let scaled = qi >> round;
            let parity = scaled & 1;
            let (s0, s1) = queried_symbols[i];
            if round > 0 {
                let expected = if parity == 1 { s1 } else { s0 };
                if folded_symbols[i] != Some(expected) {
                    return Err(format!(
                        "Symbol not consistent at query {i} in round {round}"
                    ));
                }
            }
            leaf_pairs.push(s0);
            leaf_pairs.push(s1);
        }

        // Batch-hash all (s0, s1) leaves in one SIMD-packed pass.
        hasher.batch_hash_pair(&leaf_pairs, &mut leaf_hashes[..n_queries]);

        // Validate Merkle path lengths up-front.
        for (i, path) in merkle_paths.iter().enumerate().take(n_queries) {
            if path.len() != oracle.depth {
                return Err(format!("Merkle path failed at query {i} round {round}"));
            }
        }

        // Batch-verify Merkle paths one tree-layer at a time.
        // At each depth d, each query's running hash is combined with its
        // sibling at path[d] in the correct order (left/right).
        let mut running: Vec<HashOutput> = leaf_hashes[..n_queries].to_vec();
        let mut d = 0usize;
        while d < oracle.depth {
            merkle_pairs.clear();
            for i in 0..n_queries {
                let qi = query_indices[i];
                let pair_idx = (qi >> round) >> 1;
                let is_left_child = ((pair_idx >> d) & 1) == 0;
                let sibling = merkle_paths[i][d];
                if is_left_child {
                    merkle_pairs.push(running[i]);
                    merkle_pairs.push(sibling);
                } else {
                    merkle_pairs.push(sibling);
                    merkle_pairs.push(running[i]);
                }
            }
            hasher.batch_compress(&merkle_pairs, &mut merkle_next[..n_queries]);
            running.copy_from_slice(&merkle_next[..n_queries]);
            d += 1;
        }

        for (i, r) in running.iter().enumerate().take(n_queries) {
            if *r != oracle.root {
                return Err(format!("Merkle path failed at query {i} round {round}"));
            }
        }

        // Now compute the folds.
        for (i, &qi) in query_indices.iter().enumerate().take(n_queries) {
            let scaled = qi >> round;
            let pair_idx = scaled >> 1;
            let (s0, s1) = queried_symbols[i];
            round_folded.push(fold(random_point[round], round, pair_idx, s0, s1, ntt));
        }
        folded_symbols = round_folded.into_iter().map(Some).collect();
    }

    // The final fold result for query i should match the symbol at position
    // `qi >> rounds` in the final codeword.
    // After `rounds` halvings, query qi maps to symbol index `qi >> rounds`.
    for (i, sym) in folded_symbols.iter().enumerate() {
        if let Some(s) = sym {
            let qi = query_indices[i];
            let final_sym = qi >> rounds; // symbol index in final code
            let expected = eval_proof.final_codeword[final_sym % final_codeword_len];
            if *s != expected {
                return Err(format!(
                    "final folded value mismatch at query {i}: got {s:?} expected {expected:?}"
                ));
            }
        }
    }

    Ok(())
}

/// Compute the equality indicator table eq(r) for a point r.
pub fn compute_eq_table(r: &[Block128]) -> Vec<Block128> {
    let Some(size) = 1usize.checked_shl(r.len() as u32) else {
        return Vec::new();
    };
    let mut eq = vec![Block128::ZERO; size];
    eq[0] = Block128::ONE;
    let mut span = 1;

    for &r_i in r {
        let (eq_left, eq_right) = eq.split_at_mut(span);
        let (eq_right, _) = eq_right.split_at_mut(span);

        for j in 0..span {
            eq_right[j] = eq_left[j] * r_i;
            eq_left[j] += eq_right[j]; // eq_left[j] - eq_right[j] == same in char 2
        }
        span *= 2;
    }

    eq
}

/// Row-batch: inner product of `scalars` and `vals` (column view → row view).
fn compute_row_batch(scalars: &[Block128], vals: &[Block128]) -> Block128 {
    vals.iter()
        .zip(scalars.iter())
        .map(|(v, s)| *v * *s)
        .fold(Block128::ZERO, |acc, x| acc + x)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compute_eq_table() {
        let r = vec![Block128::from(1u8)];
        let eq = compute_eq_table(&r);
        assert_eq!(eq.len(), 2);
        // eq(0) = 1 - r = 1 + 1 = 0 in GF(2), eq(1) = r = 1
        assert_eq!(eq[0], Block128::ZERO);
        assert_eq!(eq[1], Block128::ONE);
    }

    #[test]
    fn test_compute_eq_table_two_vars() {
        let r0 = Block128::from(2u8);
        let r1 = Block128::from(3u8);
        let eq = compute_eq_table(&[r0, r1]);
        assert_eq!(eq.len(), 4);
        // eq[0] = (1-r0)*(1-r1)
        assert_eq!(eq[0], (Block128::ONE - r0) * (Block128::ONE - r1));
        // eq[1] = r0*(1-r1)
        assert_eq!(eq[1], r0 * (Block128::ONE - r1));
        // eq[2] = (1-r0)*r1
        assert_eq!(eq[2], (Block128::ONE - r0) * r1);
        // eq[3] = r0*r1
        assert_eq!(eq[3], r0 * r1);
    }
}
