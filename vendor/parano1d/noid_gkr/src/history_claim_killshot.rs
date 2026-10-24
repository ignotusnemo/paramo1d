// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! History state-transition claim Poseidon2b KillShot.
//!
//! This component proves the fixed field-native history state-transition claim
//! schedule:
//!
//! ```text
//! history_claim = Poseidon2b(HISTCLM_, fields[0..32])
//! ```

use noid_core::transcript::FiatShamir;
use noid_core::{Block128, TowerField};
use noid_poseidon2b::native::domain::{capacity_iv, TAG_HISTCLM};
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

pub const HISTORY_CLAIM_FIELDS: usize = 32;
const HISTORY_CLAIM_BLOCKS: usize = HISTORY_CLAIM_FIELDS / 2;
const HISTORY_CLAIM_PIN_LANES: usize = 2;
const HISTORY_CLAIM_LINEAR_RELATION_TAG: u128 = 0x4849_5354_434C_4D01; // "HISTCLM"+1

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HistoryClaimHashInputs {
    pub fields: [Block128; HISTORY_CLAIM_FIELDS],
    pub expected_claim: [Block128; HISTORY_CLAIM_PIN_LANES],
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct HistoryClaimHashProofKillShot {
    pub kill_shot: BlockSpineKillShotProof,
    pub chain: LinearEvalProof,
    pub batch: MultiBatchEvalProof,
    pub n_claims: usize,
    pub num_vars: usize,
    pub live_slots: usize,
}

impl HistoryClaimHashProofKillShot {
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
pub struct HistoryClaimHashReductions {
    pub state: BatchEvalReduction,
    pub sin: BatchEvalReduction,
    pub sout: BatchEvalReduction,
}

fn claim_blocks(input: &HistoryClaimHashInputs) -> [[Block128; 2]; HISTORY_CLAIM_BLOCKS] {
    std::array::from_fn(|i| [input.fields[2 * i], input.fields[2 * i + 1]])
}

fn absorb_public_batch<T: FiatShamir<Block128>>(
    channel: &mut T,
    inputs: &[HistoryClaimHashInputs],
) {
    channel.absorb(Block128::from(inputs.len() as u128));
    channel.absorb(Block128::from(TAG_HISTCLM.as_u64() as u128));
    channel.absorb(Block128::from(HISTORY_CLAIM_FIELDS as u128));
    for input in inputs {
        for field in input.fields {
            channel.absorb(field);
        }
        for lane in input.expected_claim {
            channel.absorb(lane);
        }
    }
}

fn evaluate_claims(inputs: &[HistoryClaimHashInputs]) -> Option<Vec<[Block128; STATE_SIZE]>> {
    if inputs.is_empty() {
        return None;
    }
    let perm = Poseidon2bPermutation;
    let iv = capacity_iv(TAG_HISTCLM);
    let mut slot_state_ins = Vec::with_capacity(inputs.len() * HISTORY_CLAIM_BLOCKS);
    for input in inputs {
        let mut state = [Block128::ZERO, Block128::ZERO, iv[0], iv[1]];
        for block in claim_blocks(input) {
            state[0] += block[0];
            state[1] += block[1];
            slot_state_ins.push(state);
            perm.permute_mut(&mut state);
        }
        if state[..HISTORY_CLAIM_PIN_LANES] != input.expected_claim {
            return None;
        }
    }
    Some(slot_state_ins)
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

fn push_prev_terms(terms: &mut Vec<LinearEvalTerm>, num_vars: usize, prev_slot: usize, row: usize) {
    for src_lane in 0..STATE_SIZE {
        terms.push(weighted_state_claim(
            num_vars,
            prev_slot,
            N_ROUNDS,
            src_lane,
            mds_coeff(row, src_lane),
        ));
    }
}

fn claim_chain_claims(inputs: &[HistoryClaimHashInputs], num_vars: usize) -> Vec<LinearEvalClaim> {
    let iv = capacity_iv(TAG_HISTCLM);
    let mut claims = Vec::new();
    for (idx, input) in inputs.iter().enumerate() {
        let base = idx * HISTORY_CLAIM_BLOCKS;
        for (block_idx, block) in claim_blocks(input).iter().copied().enumerate() {
            let slot = base + block_idx;
            for lane in 0..STATE_SIZE {
                let mut terms = vec![state_claim(num_vars, slot, 0, lane)];
                let value = if block_idx == 0 {
                    mds_constant(
                        lane,
                        &[(0, block[0]), (1, block[1]), (2, iv[0]), (3, iv[1])],
                    )
                } else {
                    push_prev_terms(&mut terms, num_vars, slot - 1, lane);
                    mds_constant(lane, &[(0, block[0]), (1, block[1])])
                };
                claims.push(LinearEvalClaim { terms, value });
            }
        }
        let last_slot = base + HISTORY_CLAIM_BLOCKS - 1;
        for lane in 0..HISTORY_CLAIM_PIN_LANES {
            claims.push(LinearEvalClaim {
                terms: vec![state_claim(num_vars, last_slot, N_ROUNDS, lane)],
                value: input.expected_claim[lane],
            });
        }
    }
    claims
}

pub fn prove_history_claim_hash_killshot<T: FiatShamir<Block128>>(
    inputs: &[HistoryClaimHashInputs],
    channel: &mut T,
) -> (HistoryClaimHashProofKillShot, HistoryClaimHashReductions) {
    let slot_state_ins =
        evaluate_claims(inputs).expect("prover asked to prove wrong history-claim hash");

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

    let chain_claims = claim_chain_claims(inputs, mle.num_vars);
    let (chain, chain_red) = prove_linear_eval_prebound(
        &mle.state,
        &chain_claims,
        HISTORY_CLAIM_LINEAR_RELATION_TAG,
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

    let proof = HistoryClaimHashProofKillShot {
        kill_shot: BlockSpineKillShotProof { main, shift },
        chain,
        batch,
        n_claims: inputs.len(),
        num_vars: mle.num_vars,
        live_slots: mle.live_slots,
    };
    let reductions = HistoryClaimHashReductions {
        state: state_red,
        sin: sin_red,
        sout: sout_red,
    };
    (proof, reductions)
}

pub fn verify_history_claim_hash_killshot<T: FiatShamir<Block128>>(
    proof: &HistoryClaimHashProofKillShot,
    inputs: &[HistoryClaimHashInputs],
    channel: &mut T,
) -> Option<HistoryClaimHashReductions> {
    if inputs.is_empty()
        || proof.n_claims != inputs.len()
        || proof.live_slots != inputs.len() * HISTORY_CLAIM_BLOCKS
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

    let chain_claims = claim_chain_claims(inputs, proof.num_vars);
    let chain_red = verify_linear_eval_prebound(
        &proof.chain,
        &chain_claims,
        proof.num_vars,
        HISTORY_CLAIM_LINEAR_RELATION_TAG,
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

    Some(HistoryClaimHashReductions {
        state: state_red,
        sin: sin_red,
        sout: sout_red,
    })
}

pub fn discharge_history_claim_hash_reductions_native(
    inputs: &[HistoryClaimHashInputs],
    reductions: &HistoryClaimHashReductions,
) -> bool {
    let Some(slot_state_ins) = evaluate_claims(inputs) else {
        return false;
    };
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

    fn input(seed: u128) -> HistoryClaimHashInputs {
        let fields: [Block128; HISTORY_CLAIM_FIELDS] = std::array::from_fn(|i| {
            Block128::from(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) + i as u128)
        });
        let mut sponge = Poseidon2bSponge::with_iv(capacity_iv(TAG_HISTCLM));
        for pair in fields.chunks_exact(2) {
            sponge.absorb_pair(pair[0], pair[1]);
        }
        let digest = sponge.finalize_no_pad();
        let expected_claim = [
            Block128::from(u128::from_le_bytes(digest[..16].try_into().unwrap())),
            Block128::from(u128::from_le_bytes(digest[16..].try_into().unwrap())),
        ];
        HistoryClaimHashInputs {
            fields,
            expected_claim,
        }
    }

    #[test]
    fn history_claim_hash_roundtrip() {
        let inputs = vec![input(1), input(2)];
        let mut ch_p = Poseidon2bChannel::new();
        let (proof, reductions) = prove_history_claim_hash_killshot(&inputs, &mut ch_p);

        let mut ch_v = Poseidon2bChannel::new();
        let verified = verify_history_claim_hash_killshot(&proof, &inputs, &mut ch_v)
            .expect("history claim hash proof verifies");
        assert_eq!(verified, reductions);
    }

    #[test]
    fn history_claim_hash_rejects_tamper() {
        let inputs = vec![input(9)];
        let mut ch_p = Poseidon2bChannel::new();
        let (proof, _) = prove_history_claim_hash_killshot(&inputs, &mut ch_p);
        let mut bad = inputs.clone();
        bad[0].expected_claim[1] += Block128::ONE;
        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_history_claim_hash_killshot(&proof, &bad, &mut ch_v).is_none());
    }
}
