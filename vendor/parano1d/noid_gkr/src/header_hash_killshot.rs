// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Batched semantic-header and PoW-header Poseidon2b KillShot.
//!
//! For each header this component proves both fixed schedules from the same
//! public 16-field semantic header schedule:
//!
//! ```text
//! pow_digest = Poseidon2b(POWHDR__, fields[0..16]) no-pad squeeze
//! block_id   = Poseidon2b(BLOCKHDR, fields[0..16]) padded squeeze
//! ```

use noid_core::transcript::FiatShamir;
use noid_core::{Block128, TowerField};
use noid_poseidon2b::native::domain::{capacity_iv, TAG_BLOCKHDR, TAG_POWHDR};
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

pub const HEADER_HASH_FIELDS: usize = 16;
// Public: the in-circuit trace transliteration (`noid_recursive::acceptance::trace`)
// replays the chain relation from these same definitions; change both together.
pub const HEADER_HASH_BLOCK_PERMS: usize = 9;
pub const HEADER_HASH_POW_PERMS: usize = 8;
pub const HEADER_HASH_PERMS_PER_ITEM: usize = HEADER_HASH_BLOCK_PERMS + HEADER_HASH_POW_PERMS;
pub const HEADER_HASH_PIN_LANES: usize = 2;
pub const HEADER_HASH_LINEAR_RELATION_TAG: u128 = 0x4844_5248_4153_4801; // "HDRHASH"+1

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderHashInputs {
    pub fields: [Block128; HEADER_HASH_FIELDS],
    pub expected_pow_digest: [Block128; 2],
    pub expected_block_id: [Block128; 2],
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct HeaderHashProofKillShot {
    pub kill_shot: BlockSpineKillShotProof,
    pub chain: LinearEvalProof,
    pub batch: MultiBatchEvalProof,
    pub n_headers: usize,
    pub num_vars: usize,
    pub live_slots: usize,
}

impl HeaderHashProofKillShot {
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
pub struct HeaderHashReductions {
    pub state: BatchEvalReduction,
    pub sin: BatchEvalReduction,
    pub sout: BatchEvalReduction,
}

fn pad_pair() -> [Block128; 2] {
    let mut bytes = [0u8; 32];
    bytes[0] = 0x80;
    bytes[31] = 0x01;
    [
        Block128::from(u128::from_le_bytes(bytes[..16].try_into().unwrap())),
        Block128::from(u128::from_le_bytes(bytes[16..].try_into().unwrap())),
    ]
}

fn pow_blocks(input: &HeaderHashInputs) -> [[Block128; 2]; HEADER_HASH_POW_PERMS] {
    std::array::from_fn(|i| [input.fields[2 * i], input.fields[2 * i + 1]])
}

fn block_id_blocks(input: &HeaderHashInputs) -> [[Block128; 2]; HEADER_HASH_BLOCK_PERMS] {
    let pad = pad_pair();
    std::array::from_fn(|i| {
        if i < HEADER_HASH_POW_PERMS {
            [input.fields[2 * i], input.fields[2 * i + 1]]
        } else {
            pad
        }
    })
}

fn absorb_digest_fields<T: FiatShamir<Block128>>(channel: &mut T, fields: [Block128; 2]) {
    channel.absorb(fields[0]);
    channel.absorb(fields[1]);
}

fn absorb_public_header<T: FiatShamir<Block128>>(channel: &mut T, input: &HeaderHashInputs) {
    for field in input.fields {
        channel.absorb(field);
    }
    absorb_digest_fields(channel, input.expected_pow_digest);
    absorb_digest_fields(channel, input.expected_block_id);
}

fn absorb_public_batch<T: FiatShamir<Block128>>(channel: &mut T, inputs: &[HeaderHashInputs]) {
    channel.absorb(Block128::from(inputs.len() as u128));
    channel.absorb(Block128::from(TAG_POWHDR.as_u64() as u128));
    channel.absorb(Block128::from(TAG_BLOCKHDR.as_u64() as u128));
    for input in inputs {
        absorb_public_header(channel, input);
    }
}

fn zero_header_hash_input() -> HeaderHashInputs {
    HeaderHashInputs {
        fields: [Block128::ZERO; HEADER_HASH_FIELDS],
        expected_pow_digest: [Block128::ZERO; 2],
        expected_block_id: [Block128::ZERO; 2],
    }
}

fn absorb_public_batch_padded<T: FiatShamir<Block128>>(
    channel: &mut T,
    inputs: &[HeaderHashInputs],
    padded_headers: usize,
) {
    channel.absorb(Block128::from(inputs.len() as u128));
    channel.absorb(Block128::from(padded_headers as u128));
    channel.absorb(Block128::from(TAG_POWHDR.as_u64() as u128));
    channel.absorb(Block128::from(TAG_BLOCKHDR.as_u64() as u128));
    let zero = zero_header_hash_input();
    for idx in 0..padded_headers {
        absorb_public_header(channel, inputs.get(idx).unwrap_or(&zero));
    }
}

fn evaluate_sponge(
    blocks: &[[Block128; 2]],
    iv: [Block128; 2],
    expected: [Block128; 2],
    out: &mut Vec<[Block128; STATE_SIZE]>,
) -> Option<()> {
    let perm = Poseidon2bPermutation;
    let mut state = [Block128::ZERO, Block128::ZERO, iv[0], iv[1]];
    for block in blocks {
        state[0] += block[0];
        state[1] += block[1];
        out.push(state);
        perm.permute_mut(&mut state);
    }
    if [state[0], state[1]] != expected {
        return None;
    }
    Some(())
}

fn evaluate_header_hashes(inputs: &[HeaderHashInputs]) -> Option<Vec<[Block128; STATE_SIZE]>> {
    if inputs.is_empty() {
        return None;
    }
    let mut slot_state_ins = Vec::with_capacity(inputs.len() * HEADER_HASH_PERMS_PER_ITEM);
    for input in inputs {
        evaluate_sponge(
            &block_id_blocks(input),
            capacity_iv(TAG_BLOCKHDR),
            input.expected_block_id,
            &mut slot_state_ins,
        )?;
        evaluate_sponge(
            &pow_blocks(input),
            capacity_iv(TAG_POWHDR),
            input.expected_pow_digest,
            &mut slot_state_ins,
        )?;
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

fn sponge_chain_claims(
    blocks: &[[Block128; 2]],
    iv: [Block128; 2],
    expected: [Block128; 2],
    slot_offset: usize,
    num_vars: usize,
) -> Vec<LinearEvalClaim> {
    let mut claims = Vec::with_capacity(blocks.len() * STATE_SIZE + HEADER_HASH_PIN_LANES);
    for (block_idx, block) in blocks.iter().copied().enumerate() {
        let slot = slot_offset + block_idx;
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

    let last_slot = slot_offset + blocks.len() - 1;
    for lane in 0..HEADER_HASH_PIN_LANES {
        claims.push(LinearEvalClaim {
            terms: vec![state_claim(num_vars, last_slot, N_ROUNDS, lane)],
            value: expected[lane],
        });
    }
    claims
}

fn header_hash_claims(inputs: &[HeaderHashInputs], num_vars: usize) -> Vec<LinearEvalClaim> {
    let mut claims = Vec::new();
    for (idx, input) in inputs.iter().enumerate() {
        let base = idx * HEADER_HASH_PERMS_PER_ITEM;
        let block_blocks = block_id_blocks(input);
        claims.extend(sponge_chain_claims(
            &block_blocks,
            capacity_iv(TAG_BLOCKHDR),
            input.expected_block_id,
            base,
            num_vars,
        ));
        let pow_blocks = pow_blocks(input);
        claims.extend(sponge_chain_claims(
            &pow_blocks,
            capacity_iv(TAG_POWHDR),
            input.expected_pow_digest,
            base + HEADER_HASH_BLOCK_PERMS,
            num_vars,
        ));
    }
    claims
}

fn zero_linear_claims_like(mut claims: Vec<LinearEvalClaim>) -> Vec<LinearEvalClaim> {
    for claim in &mut claims {
        claim.value = Block128::ZERO;
        for term in &mut claim.terms {
            term.coeff = Block128::ZERO;
        }
    }
    claims
}

fn header_hash_claims_padded(
    inputs: &[HeaderHashInputs],
    padded_headers: usize,
    num_vars: usize,
) -> Vec<LinearEvalClaim> {
    let mut claims = header_hash_claims(inputs, num_vars);
    if inputs.len() < padded_headers {
        let zero = zero_header_hash_input();
        let template =
            zero_linear_claims_like(header_hash_claims(std::slice::from_ref(&zero), num_vars));
        claims.reserve(template.len() * (padded_headers - inputs.len()));
        for _ in inputs.len()..padded_headers {
            claims.extend(template.iter().cloned());
        }
    }
    claims
}

pub fn prove_header_hash_killshot<T: FiatShamir<Block128>>(
    inputs: &[HeaderHashInputs],
    channel: &mut T,
) -> (HeaderHashProofKillShot, HeaderHashReductions) {
    prove_header_hash_killshot_with_shape(inputs, inputs.len(), false, channel)
}

pub fn prove_header_hash_killshot_padded<T: FiatShamir<Block128>>(
    inputs: &[HeaderHashInputs],
    padded_headers: usize,
    channel: &mut T,
) -> (HeaderHashProofKillShot, HeaderHashReductions) {
    prove_header_hash_killshot_with_shape(inputs, padded_headers, true, channel)
}

fn prove_header_hash_killshot_with_shape<T: FiatShamir<Block128>>(
    inputs: &[HeaderHashInputs],
    padded_headers: usize,
    pad_public_transcript: bool,
    channel: &mut T,
) -> (HeaderHashProofKillShot, HeaderHashReductions) {
    let slot_state_ins =
        evaluate_header_hashes(inputs).expect("prover asked to prove wrong header hash");
    assert!(inputs.len() <= padded_headers);
    let padded_live_slots = padded_headers * HEADER_HASH_PERMS_PER_ITEM;

    if pad_public_transcript {
        absorb_public_batch_padded(channel, inputs, padded_headers);
    } else {
        absorb_public_batch(channel, inputs);
    }

    let mle = BlockSpineMle::build_from_slot_state_ins_padded(&slot_state_ins, padded_live_slots);
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

    let chain_claims = if pad_public_transcript {
        header_hash_claims_padded(inputs, padded_headers, mle.num_vars)
    } else {
        header_hash_claims(inputs, mle.num_vars)
    };
    let (chain, chain_red) = prove_linear_eval_prebound(
        &mle.state,
        &chain_claims,
        HEADER_HASH_LINEAR_RELATION_TAG,
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

    let proof = HeaderHashProofKillShot {
        kill_shot: BlockSpineKillShotProof { main, shift },
        chain,
        batch,
        n_headers: inputs.len(),
        num_vars: mle.num_vars,
        live_slots: mle.live_slots,
    };
    let reductions = HeaderHashReductions {
        state: state_red,
        sin: sin_red,
        sout: sout_red,
    };
    (proof, reductions)
}

pub fn verify_header_hash_killshot<T: FiatShamir<Block128>>(
    proof: &HeaderHashProofKillShot,
    inputs: &[HeaderHashInputs],
    channel: &mut T,
) -> Option<HeaderHashReductions> {
    verify_header_hash_killshot_with_shape(proof, inputs, inputs.len(), false, channel)
}

pub fn verify_header_hash_killshot_padded<T: FiatShamir<Block128>>(
    proof: &HeaderHashProofKillShot,
    inputs: &[HeaderHashInputs],
    padded_headers: usize,
    channel: &mut T,
) -> Option<HeaderHashReductions> {
    verify_header_hash_killshot_with_shape(proof, inputs, padded_headers, true, channel)
}

fn verify_header_hash_killshot_with_shape<T: FiatShamir<Block128>>(
    proof: &HeaderHashProofKillShot,
    inputs: &[HeaderHashInputs],
    padded_headers: usize,
    pad_public_transcript: bool,
    channel: &mut T,
) -> Option<HeaderHashReductions> {
    if inputs.is_empty()
        || proof.n_headers != inputs.len()
        || inputs.len() > padded_headers
        || proof.live_slots != padded_headers * HEADER_HASH_PERMS_PER_ITEM
    {
        return None;
    }
    let expected_num_vars = crate::block_spine::num_vars_for(proof.live_slots);
    if proof.num_vars != expected_num_vars {
        return None;
    }

    if pad_public_transcript {
        absorb_public_batch_padded(channel, inputs, padded_headers);
    } else {
        absorb_public_batch(channel, inputs);
    }

    let main_red = verify_block_spine_unified(
        &proof.kill_shot.main,
        proof.num_vars,
        proof.live_slots,
        channel,
    )?;
    let shift_red =
        verify_block_spine_shift(&proof.kill_shot.shift, &main_red, proof.num_vars, channel)?;

    let chain_claims = if pad_public_transcript {
        header_hash_claims_padded(inputs, padded_headers, proof.num_vars)
    } else {
        header_hash_claims(inputs, proof.num_vars)
    };
    let chain_red = verify_linear_eval_prebound(
        &proof.chain,
        &chain_claims,
        proof.num_vars,
        HEADER_HASH_LINEAR_RELATION_TAG,
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

    Some(HeaderHashReductions {
        state: state_red,
        sin: sin_red,
        sout: sout_red,
    })
}

pub fn discharge_header_hash_reductions_native(
    inputs: &[HeaderHashInputs],
    reductions: &HeaderHashReductions,
) -> bool {
    discharge_header_hash_reductions_native_padded(inputs, reductions, inputs.len())
}

pub fn discharge_header_hash_reductions_native_padded(
    inputs: &[HeaderHashInputs],
    reductions: &HeaderHashReductions,
    padded_headers: usize,
) -> bool {
    let Some(slot_state_ins) = evaluate_header_hashes(inputs) else {
        return false;
    };
    let padded_live_slots = padded_headers * HEADER_HASH_PERMS_PER_ITEM;
    if slot_state_ins.len() > padded_live_slots {
        return false;
    }
    let mut slot_state_ins = slot_state_ins;
    slot_state_ins.resize(padded_live_slots, [Block128::ZERO; STATE_SIZE]);
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
        [
            Block128::from(u128::from_le_bytes(hash[..16].try_into().unwrap())),
            Block128::from(u128::from_le_bytes(hash[16..].try_into().unwrap())),
        ]
    }

    fn digest_from_fields(fields: [Block128; 2]) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[..16].copy_from_slice(&fields[0].to_u128().to_le_bytes());
        out[16..].copy_from_slice(&fields[1].to_u128().to_le_bytes());
        out
    }

    fn input(seed: u128) -> HeaderHashInputs {
        let fields: [Block128; HEADER_HASH_FIELDS] = std::array::from_fn(|i| {
            Block128::from(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) + i as u128)
        });

        let mut pow = Poseidon2bSponge::with_iv(capacity_iv(TAG_POWHDR));
        for pair in fields.chunks_exact(2) {
            pow.absorb_pair(pair[0], pair[1]);
        }
        let expected_pow_digest = fields_from_digest(pow.finalize_no_pad());

        let mut block = Poseidon2bSponge::with_iv(capacity_iv(TAG_BLOCKHDR));
        for pair in fields.chunks_exact(2) {
            block.absorb_pair(pair[0], pair[1]);
        }
        let expected_block_id = fields_from_digest(block.finalize());

        HeaderHashInputs {
            fields,
            expected_pow_digest,
            expected_block_id,
        }
    }

    #[test]
    fn header_hash_roundtrip() {
        let inputs = vec![input(1), input(2), input(3)];
        let mut ch_p = Poseidon2bChannel::new();
        let (proof, reductions) = prove_header_hash_killshot(&inputs, &mut ch_p);

        let mut ch_v = Poseidon2bChannel::new();
        let verified = verify_header_hash_killshot(&proof, &inputs, &mut ch_v)
            .expect("header hash proof verifies");
        assert_eq!(verified, reductions);
    }

    #[test]
    fn header_hash_padded_roundtrip_size_constant_and_rejects_small_shape() {
        let all_inputs = vec![input(1), input(2), input(3), input(4)];
        let padded_headers = all_inputs.len();
        let mut expected_len = None;

        for n in [1usize, 3, padded_headers] {
            let inputs = &all_inputs[..n];
            let mut ch_p = Poseidon2bChannel::new();
            let (proof, reductions) =
                prove_header_hash_killshot_padded(inputs, padded_headers, &mut ch_p);
            assert_eq!(proof.n_headers, n);
            assert_eq!(
                proof.live_slots,
                padded_headers * HEADER_HASH_PERMS_PER_ITEM
            );

            let mut ch_v = Poseidon2bChannel::new();
            let verified =
                verify_header_hash_killshot_padded(&proof, inputs, padded_headers, &mut ch_v)
                    .expect("padded header hash proof verifies");
            assert_eq!(verified, reductions);
            assert!(discharge_header_hash_reductions_native_padded(
                inputs,
                &verified,
                padded_headers,
            ));

            if let Some(expected_len) = expected_len {
                assert_eq!(proof.byte_len(), expected_len);
            } else {
                expected_len = Some(proof.byte_len());
            }

            if n < padded_headers {
                let mut ch_small = Poseidon2bChannel::new();
                assert!(
                    verify_header_hash_killshot_padded(&proof, inputs, n, &mut ch_small).is_none()
                );
            }
        }

        let inputs = &all_inputs[..1];
        let mut ch_p = Poseidon2bChannel::new();
        let (small_shape_proof, _) = prove_header_hash_killshot(inputs, &mut ch_p);
        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_header_hash_killshot_padded(
            &small_shape_proof,
            inputs,
            padded_headers,
            &mut ch_v,
        )
        .is_none());
    }

    #[test]
    fn header_hash_rejects_tamper() {
        let inputs = vec![input(9)];
        let mut ch_p = Poseidon2bChannel::new();
        let (proof, _) = prove_header_hash_killshot(&inputs, &mut ch_p);
        let mut bad = inputs.clone();
        bad[0].expected_pow_digest[0] += Block128::ONE;
        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_header_hash_killshot(&proof, &bad, &mut ch_v).is_none());
    }

    #[test]
    fn test_input_matches_manual_digest() {
        let input = input(42);
        assert_ne!(
            digest_from_fields(input.expected_pow_digest),
            digest_from_fields(input.expected_block_id)
        );
    }
}
