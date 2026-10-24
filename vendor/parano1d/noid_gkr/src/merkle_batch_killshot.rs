// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Batched Merkle path Kill-Shot.
//!
//! This module proves many Poseidon2b Merkle paths with one dynamic
//! permutation-trace KillShot and one multi-column terminal batch proof. Public
//! path values are bound through a linear path-chain sumcheck over the shared
//! `state` column. Intermediate compression outputs stay inside the committed
//! trace and are not serialized as proof bytes.

use noid_core::transcript::FiatShamir;
use noid_core::{Block128, TowerField};
use noid_poseidon2b::native::domain::capacity_iv;
use noid_poseidon2b::native::permutation::{N_ROUNDS, STATE_SIZE};

use crate::batch_eval::{
    prove_linear_eval_prebound, prove_multi_batch_eval, verify_linear_eval_prebound,
    verify_multi_batch_eval, BatchEvalReduction, EvalClaim, LinearEvalClaim, LinearEvalProof,
    LinearEvalTerm, MultiBatchEvalProof,
};
use crate::block_spine::{
    block_spine_state_point, prove_block_spine_shift, prove_block_spine_unified,
    verify_block_spine_shift, verify_block_spine_unified, BlockSpineKillShotProof, BlockSpineMle,
    BlockSpineUnifiedReduction,
};
use crate::merkle_circuit::{MerkleCircuit, MerklePathInputs, MAX_MERKLE_DEPTH};
use crate::merkle_oracle::evaluate_merkle;
use noid_poseidon2b::native::permutation::MDS_FULL;

pub const MERKLE_CHAIN_LINEAR_RELATION_TAG: u128 = 0x4D45_524B_4C45_4348; // "MERKLECH"
pub const MERKLE_PIN_LANES: usize = 2;

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BatchedMerkleProofKillShot {
    pub kill_shot: BlockSpineKillShotProof,
    pub chain: LinearEvalProof,
    pub batch: MultiBatchEvalProof,
    pub n_paths: usize,
    pub num_vars: usize,
    pub live_slots: usize,
}

impl BatchedMerkleProofKillShot {
    pub fn byte_len(&self, _inputs: &[MerklePathInputs]) -> usize {
        let main_polys = self.kill_shot.main.round_polys.len() * 10 * 16;
        let shift_polys = self.kill_shot.shift.round_polys.len() * 3 * 16;
        let main_finals = 12 * 16;
        let shift_finals = 3 * 16;
        main_polys
            + shift_polys
            + main_finals
            + shift_finals
            + self.chain.byte_len()
            + self.batch.byte_len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchedMerkleKillShotReductions {
    pub state: BatchEvalReduction,
    pub sin: BatchEvalReduction,
    pub sout: BatchEvalReduction,
}

fn absorb_pair<T: FiatShamir<Block128>>(channel: &mut T, pair: &[Block128; 2]) {
    channel.absorb(pair[0]);
    channel.absorb(pair[1]);
}

fn absorb_public_path<T: FiatShamir<Block128>>(channel: &mut T, inputs: &MerklePathInputs) {
    // Prefix-decodable: the depth comes FIRST and bounds the sibling loop.
    // Levels past `active_depth` are canonical zeros (`inputs_are_canonical`)
    // — absorbing them bought nothing and cost `(MAX_MERKLE_DEPTH − depth)·3`
    // pure-padding lanes per path. Direction bits pack into ONE lane
    // (bit `level` of the last absorbed field) instead of a whole lane each.
    channel.absorb(Block128::from(inputs.active_depth as u128));
    absorb_pair(channel, &inputs.expected_root);
    absorb_pair(channel, &inputs.leaf);
    let mut directions = 0u128;
    for level in 0..inputs.active_depth {
        absorb_pair(channel, &inputs.siblings[level]);
        if inputs.directions[level] {
            directions |= 1 << level;
        }
    }
    channel.absorb(Block128::from(directions));
}

fn absorb_public_batch<T: FiatShamir<Block128>>(
    channel: &mut T,
    circuit: &MerkleCircuit,
    inputs: &[MerklePathInputs],
) {
    channel.absorb(Block128::from(inputs.len() as u128));
    channel.absorb(Block128::from(circuit.node_tag.as_u64() as u128));
    for input in inputs {
        absorb_public_path(channel, input);
    }
}

fn inputs_are_canonical(inputs: &MerklePathInputs) -> bool {
    if inputs.active_depth == 0 || inputs.active_depth > MAX_MERKLE_DEPTH {
        return false;
    }
    inputs.siblings[inputs.active_depth..]
        .iter()
        .all(|s| *s == [Block128::ZERO; 2])
        && inputs.directions[inputs.active_depth..]
            .iter()
            .all(|&direction| !direction)
}

fn state_claim(num_vars: usize, slot: usize, round: usize, lane: usize) -> LinearEvalTerm {
    LinearEvalTerm {
        point: block_spine_state_point(num_vars, slot, round, lane),
        coeff: Block128::ONE,
    }
}

fn weighted_state_claim(
    num_vars: usize,
    slot: usize,
    round: usize,
    lane: usize,
    coeff: Block128,
) -> LinearEvalTerm {
    LinearEvalTerm {
        point: block_spine_state_point(num_vars, slot, round, lane),
        coeff,
    }
}

#[inline]
fn term_vec_with_first(first: LinearEvalTerm, capacity: usize) -> Vec<LinearEvalTerm> {
    let mut terms = Vec::with_capacity(capacity);
    terms.push(first);
    terms
}

#[inline]
fn mds_coeff(row: usize, col: usize) -> Block128 {
    Block128::from(MDS_FULL[row][col])
}

fn mds_constant(row: usize, inputs: &[(usize, Block128)]) -> Block128 {
    inputs
        .iter()
        .map(|&(col, value)| mds_coeff(row, col) * value)
        .fold(Block128::ZERO, |a, b| a + b)
}

fn path_chain_claim_count(inputs: &[MerklePathInputs]) -> usize {
    inputs
        .iter()
        .map(|input| input.active_depth * 8 + MERKLE_PIN_LANES)
        .sum()
}

fn append_path_chain_claims_at_offset(
    circuit: &MerkleCircuit,
    inputs: &MerklePathInputs,
    slot_offset: usize,
    num_vars: usize,
    claims: &mut Vec<LinearEvalClaim>,
) -> Option<()> {
    if !inputs_are_canonical(inputs) {
        return None;
    }
    let depth = inputs.active_depth;

    // Direction-independent claim SHAPE: every claim carries the union of
    // both branches' terms, with per-term coefficients and values scaled by
    // `d` / `1 + d` (`d` = 1 iff the current digest is the right child;
    // char 2). A branch's absent term appears with a zero coefficient, so
    // the claim VALUES equal the branch form exactly, while the term list —
    // and therefore the verifying replay's structure — depends only on the
    // depth. An arithmetic replay of this verifier needs that.
    let [iv_hi, iv_lo] = capacity_iv(circuit.node_tag);
    for level in 0..depth {
        let perm_a_slot = slot_offset + level * 2;
        let perm_b_slot = perm_a_slot + 1;

        let d = if inputs.directions[level] {
            Block128::ONE
        } else {
            Block128::ZERO
        };
        let not_d = Block128::ONE + d;
        let sibling = inputs.siblings[level];

        // PermA row 0 must be the initial-MDS output for the left child:
        // the sibling when the current digest is the right child, else the
        // current digest (the leaf at level 0, the chained previous root
        // above it).
        for lane in 0..STATE_SIZE {
            let mut terms = term_vec_with_first(
                state_claim(num_vars, perm_a_slot, 0, lane),
                if level == 0 { 1 } else { 3 },
            );
            let mut value = mds_constant(
                lane,
                &[
                    (0, d * sibling[0]),
                    (1, d * sibling[1]),
                    (2, iv_hi),
                    (3, iv_lo),
                ],
            );
            if level == 0 {
                value += mds_constant(
                    lane,
                    &[(0, not_d * inputs.leaf[0]), (1, not_d * inputs.leaf[1])],
                );
            } else {
                let prev_perm_b = perm_a_slot - 1;
                terms.push(weighted_state_claim(
                    num_vars,
                    prev_perm_b,
                    N_ROUNDS,
                    0,
                    not_d * mds_coeff(lane, 0),
                ));
                terms.push(weighted_state_claim(
                    num_vars,
                    prev_perm_b,
                    N_ROUNDS,
                    1,
                    not_d * mds_coeff(lane, 1),
                ));
            }
            claims.push(LinearEvalClaim { terms, value });
        }

        // PermB row 0 must be the initial-MDS output after XOR-absorbing
        // the right child into the PermA output rate lanes: the current
        // digest when it is the right child, else the sibling.
        for lane in 0..STATE_SIZE {
            let mut terms = term_vec_with_first(
                state_claim(num_vars, perm_b_slot, 0, lane),
                if level == 0 { 5 } else { 7 },
            );
            for src_lane in 0..STATE_SIZE {
                terms.push(weighted_state_claim(
                    num_vars,
                    perm_a_slot,
                    N_ROUNDS,
                    src_lane,
                    mds_coeff(lane, src_lane),
                ));
            }
            let mut value = mds_constant(lane, &[(0, not_d * sibling[0]), (1, not_d * sibling[1])]);
            if level == 0 {
                value += mds_constant(lane, &[(0, d * inputs.leaf[0]), (1, d * inputs.leaf[1])]);
            } else {
                let prev_perm_b = perm_a_slot - 1;
                terms.push(weighted_state_claim(
                    num_vars,
                    prev_perm_b,
                    N_ROUNDS,
                    0,
                    d * mds_coeff(lane, 0),
                ));
                terms.push(weighted_state_claim(
                    num_vars,
                    prev_perm_b,
                    N_ROUNDS,
                    1,
                    d * mds_coeff(lane, 1),
                ));
            }
            claims.push(LinearEvalClaim { terms, value });
        }
    }

    let last_perm_b = slot_offset + (depth - 1) * 2 + 1;
    for lane in 0..MERKLE_PIN_LANES {
        claims.push(LinearEvalClaim {
            terms: vec![state_claim(num_vars, last_perm_b, N_ROUNDS, lane)],
            value: inputs.expected_root[lane],
        });
    }
    Some(())
}

fn live_slots_for(inputs: &[MerklePathInputs]) -> usize {
    inputs.iter().map(|input| input.active_depth * 2).sum()
}

/// Honest prover for a non-empty batch of Merkle paths.
pub fn prove_batched_merkle_killshot<T: FiatShamir<Block128>>(
    circuit: &MerkleCircuit,
    inputs: &[MerklePathInputs],
    channel: &mut T,
) -> (BatchedMerkleProofKillShot, BatchedMerkleKillShotReductions) {
    assert!(!inputs.is_empty());
    assert!(inputs.iter().all(inputs_are_canonical));

    let mut slot_state_ins = Vec::with_capacity(live_slots_for(inputs));
    for input in inputs {
        let witness = evaluate_merkle(circuit, input);
        assert_eq!(
            witness.derived_root, input.expected_root,
            "prover asked to prove a mismatching Merkle root"
        );
        let live_slots = MerkleCircuit::live_slots(input.active_depth);
        slot_state_ins.extend(witness.slots[..live_slots].iter().map(|slot| slot.state_in));
    }

    absorb_public_batch(channel, circuit, inputs);

    let mle = BlockSpineMle::build_from_slot_state_ins(&slot_state_ins);
    let (main, r_prime) = prove_block_spine_unified(&mle, channel);
    let main_red = BlockSpineUnifiedReduction {
        r_prime: r_prime.clone(),
        s_in_dec_at_r: main.s_in_dec_at_r,
        s_out_dec_at_r: main.s_out_dec_at_r,
        state_dec_at_r: main.state_dec_at_r,
        state_at_r: main.state_at_r,
        s_out_lane_dec_at_r: main.s_out_lane_dec_at_r,
        state_lane_dec_at_r: main.state_lane_dec_at_r,
        beta: Block128::ZERO,
        gamma: Block128::ZERO,
    };
    let (shift, r_double_prime) = prove_block_spine_shift(&mle, &r_prime, &main_red, channel);

    let mut chain_claims = Vec::with_capacity(path_chain_claim_count(inputs));
    let mut slot_offset = 0usize;
    for input in inputs {
        append_path_chain_claims_at_offset(
            circuit,
            input,
            slot_offset,
            mle.num_vars,
            &mut chain_claims,
        )
        .expect("honest prover constructed canonical chain claims");
        slot_offset += MerkleCircuit::live_slots(input.active_depth);
    }
    let (chain, chain_red) = prove_linear_eval_prebound(
        &mle.state,
        &chain_claims,
        MERKLE_CHAIN_LINEAR_RELATION_TAG,
        channel,
    );

    let state_claims = vec![
        EvalClaim {
            point: r_prime,
            value: main.state_at_r,
        },
        EvalClaim {
            point: r_double_prime.clone(),
            value: shift.state_at_r2,
        },
        EvalClaim {
            point: chain_red.point,
            value: chain_red.value,
        },
    ];

    let sin_claims = vec![EvalClaim {
        point: r_double_prime.clone(),
        value: shift.s_in_at_r2,
    }];
    let sout_claims = vec![EvalClaim {
        point: r_double_prime,
        value: shift.s_out_at_r2,
    }];
    let columns: [&[Block128]; 3] = [&mle.state, &mle.s_in, &mle.s_out];
    let claims_by_column: [&[EvalClaim]; 3] = [&state_claims, &sin_claims, &sout_claims];
    let (batch, reductions) = prove_multi_batch_eval(&columns, &claims_by_column, channel);
    let [state_red, sin_red, sout_red]: [BatchEvalReduction; 3] = reductions
        .try_into()
        .expect("multi-batch returns one reduction per column");

    let proof = BatchedMerkleProofKillShot {
        kill_shot: BlockSpineKillShotProof { main, shift },
        chain,
        batch,
        n_paths: inputs.len(),
        num_vars: mle.num_vars,
        live_slots: mle.live_slots,
    };
    let reductions = BatchedMerkleKillShotReductions {
        state: state_red,
        sin: sin_red,
        sout: sout_red,
    };
    (proof, reductions)
}

pub fn verify_batched_merkle_killshot<T: FiatShamir<Block128>>(
    circuit: &MerkleCircuit,
    proof: &BatchedMerkleProofKillShot,
    inputs: &[MerklePathInputs],
    channel: &mut T,
) -> Option<BatchedMerkleKillShotReductions> {
    if inputs.is_empty()
        || proof.n_paths != inputs.len()
        || !inputs.iter().all(inputs_are_canonical)
        || proof.live_slots != live_slots_for(inputs)
    {
        return None;
    }
    let expected_num_vars = crate::block_spine::num_vars_for(proof.live_slots);
    if proof.num_vars != expected_num_vars {
        return None;
    }

    absorb_public_batch(channel, circuit, inputs);

    let main_red = verify_block_spine_unified(
        &proof.kill_shot.main,
        proof.num_vars,
        proof.live_slots,
        channel,
    )?;
    let shift_red =
        verify_block_spine_shift(&proof.kill_shot.shift, &main_red, proof.num_vars, channel)?;

    let mut chain_claims = Vec::with_capacity(path_chain_claim_count(inputs));
    let mut slot_offset = 0usize;
    for input in inputs {
        append_path_chain_claims_at_offset(
            circuit,
            input,
            slot_offset,
            proof.num_vars,
            &mut chain_claims,
        )?;
        slot_offset += MerkleCircuit::live_slots(input.active_depth);
    }
    let chain_red = verify_linear_eval_prebound(
        &proof.chain,
        &chain_claims,
        proof.num_vars,
        MERKLE_CHAIN_LINEAR_RELATION_TAG,
        channel,
    )?;

    let state_claims = vec![
        EvalClaim {
            point: main_red.r_prime,
            value: main_red.state_at_r,
        },
        EvalClaim {
            point: shift_red.r_double_prime.clone(),
            value: shift_red.state_at_r2,
        },
        EvalClaim {
            point: chain_red.point,
            value: chain_red.value,
        },
    ];

    let sin_claims = vec![EvalClaim {
        point: shift_red.r_double_prime.clone(),
        value: shift_red.s_in_at_r2,
    }];
    let sout_claims = vec![EvalClaim {
        point: shift_red.r_double_prime,
        value: shift_red.s_out_at_r2,
    }];
    let claims_by_column: [&[EvalClaim]; 3] = [&state_claims, &sin_claims, &sout_claims];
    let reductions =
        verify_multi_batch_eval(&proof.batch, &claims_by_column, proof.num_vars, channel)?;
    let [state_red, sin_red, sout_red]: [BatchEvalReduction; 3] = reductions.try_into().ok()?;

    Some(BatchedMerkleKillShotReductions {
        state: state_red,
        sin: sin_red,
        sout: sout_red,
    })
}

pub fn discharge_batched_merkle_reductions_native(
    circuit: &MerkleCircuit,
    inputs: &[MerklePathInputs],
    reductions: &BatchedMerkleKillShotReductions,
) -> bool {
    if inputs.is_empty() || !inputs.iter().all(inputs_are_canonical) {
        return false;
    }
    let mut slot_state_ins = Vec::with_capacity(live_slots_for(inputs));
    for input in inputs {
        let witness = evaluate_merkle(circuit, input);
        if witness.derived_root != input.expected_root {
            return false;
        }
        let live_slots = MerkleCircuit::live_slots(input.active_depth);
        slot_state_ins.extend(witness.slots[..live_slots].iter().map(|slot| slot.state_in));
    }
    crate::block_spine::discharge_block_spine_batch_reductions_from_slot_state_ins_native(
        &slot_state_ins,
        &reductions.state,
        &reductions.sin,
        &reductions.sout,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::channel::Poseidon2bChannel;
    use noid_poseidon2b::native::compress;

    fn digest_to_fields(d: &[u8; 32]) -> [Block128; 2] {
        let mut a = [0u8; 16];
        let mut b = [0u8; 16];
        a.copy_from_slice(&d[..16]);
        b.copy_from_slice(&d[16..]);
        [
            Block128::from(u128::from_le_bytes(a)),
            Block128::from(u128::from_le_bytes(b)),
        ]
    }

    fn fixture(seed: u8, depth: usize) -> MerklePathInputs {
        let leaf = [seed; 32];
        let mut current = leaf;
        let mut siblings_raw = [[0u8; 32]; MAX_MERKLE_DEPTH];
        for (i, sibling) in siblings_raw.iter_mut().enumerate().take(depth) {
            *sibling = [seed.wrapping_add(i as u8).wrapping_add(17); 32];
            current = compress(&current, sibling);
        }
        let mut siblings = [[Block128::ZERO; 2]; MAX_MERKLE_DEPTH];
        for (i, sibling) in siblings_raw.iter().enumerate().take(depth) {
            siblings[i] = digest_to_fields(sibling);
        }
        MerklePathInputs {
            leaf: digest_to_fields(&leaf),
            siblings,
            directions: [false; MAX_MERKLE_DEPTH],
            expected_root: digest_to_fields(&current),
            active_depth: depth,
        }
    }

    #[test]
    fn batched_merkle_roundtrip_varied_depths() {
        let circuit = MerkleCircuit::build();
        let inputs = vec![fixture(1, 4), fixture(2, 8), fixture(3, 16), fixture(4, 1)];

        let mut ch_p = Poseidon2bChannel::new();
        let (proof, reductions) = prove_batched_merkle_killshot(&circuit, &inputs, &mut ch_p);

        let mut ch_v = Poseidon2bChannel::new();
        let verified = verify_batched_merkle_killshot(&circuit, &proof, &inputs, &mut ch_v)
            .expect("batched verifier accepts honest proof");

        assert_eq!(verified, reductions);
        assert_eq!(proof.n_paths, 4);
        assert_eq!(proof.live_slots, (4 + 8 + 16 + 1) * 2);
    }

    #[test]
    fn batched_merkle_rejects_boundary_tamper() {
        let circuit = MerkleCircuit::build();
        let inputs = vec![fixture(9, 8), fixture(10, 8)];

        let mut ch_p = Poseidon2bChannel::new();
        let (mut proof, _) = prove_batched_merkle_killshot(&circuit, &inputs, &mut ch_p);
        proof.chain.b_final += Block128::ONE;

        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_batched_merkle_killshot(&circuit, &proof, &inputs, &mut ch_v).is_none());
    }

    #[test]
    fn batched_merkle_rejects_wrong_domain_circuit() {
        use crate::merkle_oracle::compute_merkle_root;
        use noid_poseidon2b::native::domain::TAG_EXSTNOD;

        let generic = MerkleCircuit::build();
        let exact = MerkleCircuit::build_with_tag(TAG_EXSTNOD);
        let mut inputs = vec![fixture(21, 8)];
        inputs[0].expected_root = compute_merkle_root(
            &generic,
            inputs[0].leaf,
            &inputs[0].siblings[..inputs[0].active_depth],
            inputs[0].active_depth,
        );

        let mut ch_p = Poseidon2bChannel::new();
        let (proof, _) = prove_batched_merkle_killshot(&generic, &inputs, &mut ch_p);

        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_batched_merkle_killshot(&exact, &proof, &inputs, &mut ch_v).is_none());
    }
}
