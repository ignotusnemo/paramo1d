// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Batched exact-state slot leaf KillShot.
//!
//! Proves the fixed two-permutation `EXSTSLT_` leaf hash schedule:
//!
//! ```text
//! perm0_in = [packed_value, owner_hi, EXSTSLT_iv_hi, EXSTSLT_iv_lo]
//! perm1_in = [perm0_out[0] + owner_lo, perm0_out[1] + PAD, perm0_out[2], perm0_out[3]]
//! leaf     = perm1_out[0..2]
//! ```

use noid_core::transcript::FiatShamir;
use noid_core::{Block128, TowerField};
use noid_poseidon2b::native::domain::{capacity_iv, TAG_EXSTSLT};
use noid_poseidon2b::native::permutation::{Poseidon2bPermutation, MDS_FULL, N_ROUNDS, STATE_SIZE};

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

pub const SLOT_LEAF_LINEAR_RELATION_TAG: u128 = 0x4558_5354_534C_5401; // "EXSTSLT"+1
pub const SLOT_LEAF_PERMS: usize = 2;
pub const SLOT_LEAF_PIN_LANES: usize = 2;

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SlotLeafInputs {
    /// `(creation_id:u64 << 64) | amount:u64`.
    pub packed_value: Block128,
    pub owner_hi: Block128,
    pub owner_lo: Block128,
    pub expected_leaf: [Block128; 2],
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BatchedSlotLeafProofKillShot {
    pub kill_shot: BlockSpineKillShotProof,
    pub chain: LinearEvalProof,
    pub batch: MultiBatchEvalProof,
    pub n_leaves: usize,
    pub num_vars: usize,
    pub live_slots: usize,
}

impl BatchedSlotLeafProofKillShot {
    pub fn byte_len(&self) -> usize {
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
pub struct BatchedSlotLeafReductions {
    pub state: BatchEvalReduction,
    pub sin: BatchEvalReduction,
    pub sout: BatchEvalReduction,
}

#[derive(Debug, Clone, Copy)]
struct SlotLeafWitness {
    perm0_in: [Block128; STATE_SIZE],
    perm1_in: [Block128; STATE_SIZE],
    perm1_out: [Block128; STATE_SIZE],
}

fn absorb_public_leaf<T: FiatShamir<Block128>>(channel: &mut T, input: &SlotLeafInputs) {
    channel.absorb(input.packed_value);
    channel.absorb(input.owner_hi);
    channel.absorb(input.owner_lo);
    channel.absorb(input.expected_leaf[0]);
    channel.absorb(input.expected_leaf[1]);
}

fn absorb_public_batch<T: FiatShamir<Block128>>(channel: &mut T, inputs: &[SlotLeafInputs]) {
    channel.absorb(Block128::from(inputs.len() as u128));
    channel.absorb(Block128::from(TAG_EXSTSLT.as_u64() as u128));
    for input in inputs {
        absorb_public_leaf(channel, input);
    }
}

fn padding_after_one_field() -> Block128 {
    let mut bytes = [0u8; 16];
    bytes[0] = 0x80;
    bytes[15] = 0x01;
    Block128::from(u128::from_le_bytes(bytes))
}

fn evaluate_slot_leaf(input: &SlotLeafInputs) -> SlotLeafWitness {
    let [iv_hi, iv_lo] = capacity_iv(TAG_EXSTSLT);
    let perm = Poseidon2bPermutation;
    let mut perm0_out = [input.packed_value, input.owner_hi, iv_hi, iv_lo];
    let perm0_in = perm0_out;
    perm.permute_mut(&mut perm0_out);

    let mut perm1_out = [
        perm0_out[0] + input.owner_lo,
        perm0_out[1] + padding_after_one_field(),
        perm0_out[2],
        perm0_out[3],
    ];
    let perm1_in = perm1_out;
    perm.permute_mut(&mut perm1_out);

    SlotLeafWitness {
        perm0_in,
        perm1_in,
        perm1_out,
    }
}

fn live_slots_for(inputs: &[SlotLeafInputs]) -> usize {
    inputs.len() * SLOT_LEAF_PERMS
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
fn mds_coeff(row: usize, col: usize) -> Block128 {
    Block128::from(MDS_FULL[row][col])
}

fn mds_constant(row: usize, inputs: &[(usize, Block128)]) -> Block128 {
    inputs
        .iter()
        .map(|&(col, value)| mds_coeff(row, col) * value)
        .fold(Block128::ZERO, |a, b| a + b)
}

fn chain_claims_at_offset(
    input: &SlotLeafInputs,
    slot_offset: usize,
    num_vars: usize,
) -> Vec<LinearEvalClaim> {
    let [iv_hi, iv_lo] = capacity_iv(TAG_EXSTSLT);
    let mut claims = Vec::with_capacity(STATE_SIZE * 2 + SLOT_LEAF_PIN_LANES);

    for lane in 0..STATE_SIZE {
        claims.push(LinearEvalClaim {
            terms: vec![state_claim(num_vars, slot_offset, 0, lane)],
            value: mds_constant(
                lane,
                &[
                    (0, input.packed_value),
                    (1, input.owner_hi),
                    (2, iv_hi),
                    (3, iv_lo),
                ],
            ),
        });
    }

    for lane in 0..STATE_SIZE {
        let mut terms = vec![state_claim(num_vars, slot_offset + 1, 0, lane)];
        for src_lane in 0..STATE_SIZE {
            terms.push(weighted_state_claim(
                num_vars,
                slot_offset,
                N_ROUNDS,
                src_lane,
                mds_coeff(lane, src_lane),
            ));
        }
        let value = mds_constant(lane, &[(0, input.owner_lo), (1, padding_after_one_field())]);
        claims.push(LinearEvalClaim { terms, value });
    }

    for lane in 0..SLOT_LEAF_PIN_LANES {
        claims.push(LinearEvalClaim {
            terms: vec![state_claim(num_vars, slot_offset + 1, N_ROUNDS, lane)],
            value: input.expected_leaf[lane],
        });
    }

    claims
}

pub fn prove_batched_slot_leaf_killshot<T: FiatShamir<Block128>>(
    inputs: &[SlotLeafInputs],
    channel: &mut T,
) -> (BatchedSlotLeafProofKillShot, BatchedSlotLeafReductions) {
    assert!(!inputs.is_empty());

    let mut slot_state_ins = Vec::with_capacity(live_slots_for(inputs));
    for input in inputs {
        let witness = evaluate_slot_leaf(input);
        assert_eq!(
            [witness.perm1_out[0], witness.perm1_out[1]],
            input.expected_leaf,
            "prover asked to prove a mismatching slot leaf"
        );
        slot_state_ins.push(witness.perm0_in);
        slot_state_ins.push(witness.perm1_in);
    }

    absorb_public_batch(channel, inputs);

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

    let mut chain_claims = Vec::new();
    for (idx, input) in inputs.iter().enumerate() {
        chain_claims.extend(chain_claims_at_offset(
            input,
            idx * SLOT_LEAF_PERMS,
            mle.num_vars,
        ));
    }
    let (chain, chain_red) = prove_linear_eval_prebound(
        &mle.state,
        &chain_claims,
        SLOT_LEAF_LINEAR_RELATION_TAG,
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

    let proof = BatchedSlotLeafProofKillShot {
        kill_shot: BlockSpineKillShotProof { main, shift },
        chain,
        batch,
        n_leaves: inputs.len(),
        num_vars: mle.num_vars,
        live_slots: mle.live_slots,
    };
    let reductions = BatchedSlotLeafReductions {
        state: state_red,
        sin: sin_red,
        sout: sout_red,
    };
    (proof, reductions)
}

pub fn verify_batched_slot_leaf_killshot<T: FiatShamir<Block128>>(
    proof: &BatchedSlotLeafProofKillShot,
    inputs: &[SlotLeafInputs],
    channel: &mut T,
) -> Option<BatchedSlotLeafReductions> {
    if inputs.is_empty()
        || proof.n_leaves != inputs.len()
        || proof.live_slots != live_slots_for(inputs)
    {
        return None;
    }
    let expected_num_vars = crate::block_spine::num_vars_for(proof.live_slots);
    if proof.num_vars != expected_num_vars {
        return None;
    }

    absorb_public_batch(channel, inputs);

    let main_red = verify_block_spine_unified(
        &proof.kill_shot.main,
        proof.num_vars,
        proof.live_slots,
        channel,
    )?;
    let shift_red =
        verify_block_spine_shift(&proof.kill_shot.shift, &main_red, proof.num_vars, channel)?;

    let mut chain_claims = Vec::new();
    for (idx, input) in inputs.iter().enumerate() {
        chain_claims.extend(chain_claims_at_offset(
            input,
            idx * SLOT_LEAF_PERMS,
            proof.num_vars,
        ));
    }
    let chain_red = verify_linear_eval_prebound(
        &proof.chain,
        &chain_claims,
        proof.num_vars,
        SLOT_LEAF_LINEAR_RELATION_TAG,
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

    Some(BatchedSlotLeafReductions {
        state: state_red,
        sin: sin_red,
        sout: sout_red,
    })
}

pub fn discharge_batched_slot_leaf_reductions_native(
    inputs: &[SlotLeafInputs],
    reductions: &BatchedSlotLeafReductions,
) -> bool {
    if inputs.is_empty() {
        return false;
    }
    let mut slot_state_ins = Vec::with_capacity(live_slots_for(inputs));
    for input in inputs {
        let witness = evaluate_slot_leaf(input);
        if [witness.perm1_out[0], witness.perm1_out[1]] != input.expected_leaf {
            return false;
        }
        slot_state_ins.push(witness.perm0_in);
        slot_state_ins.push(witness.perm1_in);
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
    use noid_poseidon2b::native::compression::Poseidon2bSponge;

    fn fields_from_digest(hash: [u8; 32]) -> [Block128; 2] {
        let mut lo = [0u8; 16];
        let mut hi = [0u8; 16];
        lo.copy_from_slice(&hash[..16]);
        hi.copy_from_slice(&hash[16..]);
        [
            Block128::from(u128::from_le_bytes(lo)),
            Block128::from(u128::from_le_bytes(hi)),
        ]
    }

    fn native_leaf(
        packed_value: Block128,
        owner_hi: Block128,
        owner_lo: Block128,
    ) -> [Block128; 2] {
        let mut s = Poseidon2bSponge::with_iv(capacity_iv(TAG_EXSTSLT));
        s.absorb(packed_value);
        s.absorb_pair(owner_hi, owner_lo);
        fields_from_digest(s.finalize())
    }

    fn input(seed: u64) -> SlotLeafInputs {
        let amount = seed * 3 + 7;
        let packed_value = Block128::from(((seed as u128) << 64) | amount as u128);
        let owner_hi = Block128::from((seed as u128) << 32);
        let owner_lo = Block128::from((seed as u128).wrapping_mul(17));
        SlotLeafInputs {
            packed_value,
            owner_hi,
            owner_lo,
            expected_leaf: native_leaf(packed_value, owner_hi, owner_lo),
        }
    }

    #[test]
    fn batched_slot_leaf_roundtrip() {
        let inputs = vec![input(1), input(2), input(3), input(4)];
        let mut ch_p = Poseidon2bChannel::new();
        let (proof, reductions) = prove_batched_slot_leaf_killshot(&inputs, &mut ch_p);

        let mut ch_v = Poseidon2bChannel::new();
        let verified = verify_batched_slot_leaf_killshot(&proof, &inputs, &mut ch_v)
            .expect("slot leaf proof verifies");
        assert_eq!(verified, reductions);
        assert_eq!(proof.n_leaves, 4);
    }

    #[test]
    fn batched_slot_leaf_rejects_leaf_tamper() {
        let inputs = vec![input(9), input(10)];
        let mut ch_p = Poseidon2bChannel::new();
        let (proof, _) = prove_batched_slot_leaf_killshot(&inputs, &mut ch_p);

        let mut bad = inputs.clone();
        bad[1].expected_leaf[0] += Block128::ONE;
        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_batched_slot_leaf_killshot(&proof, &bad, &mut ch_v).is_none());
    }
}
