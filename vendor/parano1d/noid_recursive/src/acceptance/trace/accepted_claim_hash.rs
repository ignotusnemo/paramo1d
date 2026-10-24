// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! The `accepted_claim_hash` killshot in the trace.
//!
//! Trace twins of `noid_gkr::accepted_claim_killshot`:
//! - [`verify_accepted_claim_hash_killshot_trace`] ←
//!   `verify_accepted_claim_hash_killshot` ([K] slot), and
//! - [`discharge_accepted_claim_hash_trace`] ←
//!   `discharge_accepted_claim_hash_reductions_native` ([D] slot).
//!
//! This is where the meaning of former slice S3 lands: the fixed 80-field
//! accepted-block claim schedule `accepted_claim = Poseidon2b(ACCBLK__,
//! fields[0..80])` is proven inside π by replaying the killshot VERIFIER
//! (unified + shift spine sumchecks, the prebound chain linear-eval and the
//! multi-batch closure) plus its discharge against the claim fields.
//!
//! The `fields` / `expected_claim` expressions are returned to the caller so
//! the binding slot of the acceptance proof can pin them to the receipt
//! digests.

use noid_gkr::accepted_claim_killshot::{
    AcceptedClaimHashInputs, AcceptedClaimHashProofKillShot, ACCEPTED_CLAIM_BLOCKS,
    ACCEPTED_CLAIM_FIELDS, ACCEPTED_CLAIM_LINEAR_RELATION_TAG, ACCEPTED_CLAIM_PIN_LANES,
};
use noid_gkr::block_spine::num_vars_for;
use noid_poseidon2b::native::domain::{capacity_iv, TAG_ACCBLK};
use noid_poseidon2b::native::permutation::STATE_SIZE;

use super::batch_eval::{
    verify_linear_eval_prebound_trace, verify_multi_batch_eval_trace, EvalClaimTrace,
    LinearEvalClaimTrace, LinearEvalProofTrace, MultiBatchEvalProofTrace,
};
use super::block_spine::{
    sponge_chain_claims_trace, verify_block_spine_shift_trace, verify_block_spine_unified_trace,
    BlockSpineShiftProofTrace, BlockSpineUnifiedProofTrace, ColumnAccumulator,
};
use super::{
    alloc_block, const_block, pin_zero, BatchEvalReductionTrace, FieldR1csBuilder, LinExpr,
    RawChannelTrace,
};

// ---------------------------------------------------------------------------
// Statement / proof wire types
// ---------------------------------------------------------------------------

/// Trace twin of `AcceptedClaimHashInputs`: 80 claim fields + the 2-lane
/// expected claim, as expressions (witness data; bound to the receipt in [B]).
pub struct AcceptedClaimHashInputsTrace {
    pub fields: Vec<LinExpr>,
    pub expected_claim: [LinExpr; ACCEPTED_CLAIM_PIN_LANES],
}

impl AcceptedClaimHashInputsTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &AcceptedClaimHashInputs) -> Self {
        Self {
            fields: native.fields.iter().map(|&f| alloc_block(b, f)).collect(),
            expected_claim: std::array::from_fn(|i| alloc_block(b, native.expected_claim[i])),
        }
    }
}

/// Trace twin of `AcceptedClaimHashProofKillShot`. `n_claims` / `num_vars` /
/// `live_slots` are trace-shape constants — `alloc` asserts the native proof
/// matches them (native's early shape rejects become unrepresentability).
pub struct AcceptedClaimHashProofTrace {
    pub main: BlockSpineUnifiedProofTrace,
    pub shift: BlockSpineShiftProofTrace,
    pub chain: LinearEvalProofTrace,
    pub batch: MultiBatchEvalProofTrace,
    pub n_claims: usize,
    pub num_vars: usize,
    pub live_slots: usize,
}

impl AcceptedClaimHashProofTrace {
    pub fn alloc(
        b: &mut FieldR1csBuilder,
        native: &AcceptedClaimHashProofKillShot,
        n_inputs: usize,
    ) -> Self {
        let live_slots = n_inputs * ACCEPTED_CLAIM_BLOCKS;
        let num_vars = num_vars_for(live_slots);
        assert_eq!(native.n_claims, n_inputs, "proof off the trace shape");
        assert_eq!(native.live_slots, live_slots, "proof off the trace shape");
        assert_eq!(native.num_vars, num_vars, "proof off the trace shape");
        Self {
            main: BlockSpineUnifiedProofTrace::alloc(b, &native.kill_shot.main, num_vars),
            shift: BlockSpineShiftProofTrace::alloc(b, &native.kill_shot.shift, num_vars),
            chain: LinearEvalProofTrace::alloc(b, &native.chain, num_vars),
            batch: MultiBatchEvalProofTrace::alloc(b, &native.batch, num_vars, 3),
            n_claims: n_inputs,
            num_vars,
            live_slots,
        }
    }
}

/// Trace twin of `AcceptedClaimHashReductions`.
pub struct AcceptedClaimHashReductionsTrace {
    pub state: BatchEvalReductionTrace,
    pub sin: BatchEvalReductionTrace,
    pub sout: BatchEvalReductionTrace,
}

// ---------------------------------------------------------------------------
// [K] — verifier replay
// ---------------------------------------------------------------------------

/// Trace twin of `absorb_public_batch`.
fn absorb_public_batch_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    inputs: &[AcceptedClaimHashInputsTrace],
) {
    ch.absorb_const_tower(b, inputs.len() as u128);
    ch.absorb_const_tower(b, TAG_ACCBLK.as_u64() as u128);
    ch.absorb_const_tower(b, ACCEPTED_CLAIM_FIELDS as u128);
    for input in inputs {
        for field in &input.fields {
            ch.absorb(b, field);
        }
        for lane in &input.expected_claim {
            ch.absorb(b, lane);
        }
    }
}

/// Trace twin of `claim_chain_claims`: one sponge chain per input over the
/// 40 claim blocks (same relation and order as the shared
/// `sponge_chain_claims` helper — the native killshot carries its own
/// identical copy).
fn claim_chain_claims_trace(
    inputs: &[AcceptedClaimHashInputsTrace],
    num_vars: usize,
) -> Vec<LinearEvalClaimTrace> {
    let iv = capacity_iv(TAG_ACCBLK);
    let mut claims = Vec::new();
    for (idx, input) in inputs.iter().enumerate() {
        let base = idx * ACCEPTED_CLAIM_BLOCKS;
        let blocks: Vec<[LinExpr; 2]> = (0..ACCEPTED_CLAIM_BLOCKS)
            .map(|i| [input.fields[2 * i].clone(), input.fields[2 * i + 1].clone()])
            .collect();
        claims.extend(sponge_chain_claims_trace(
            &blocks,
            iv,
            &input.expected_claim[..ACCEPTED_CLAIM_PIN_LANES],
            base,
            num_vars,
        ));
    }
    claims
}

/// Trace twin of `verify_accepted_claim_hash_killshot`. Native shape rejects
/// are `alloc`-time asserts; every value check is a pin.
pub fn verify_accepted_claim_hash_killshot_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    proof: &AcceptedClaimHashProofTrace,
    inputs: &[AcceptedClaimHashInputsTrace],
) -> AcceptedClaimHashReductionsTrace {
    assert!(!inputs.is_empty());
    assert_eq!(proof.n_claims, inputs.len());
    assert_eq!(proof.live_slots, inputs.len() * ACCEPTED_CLAIM_BLOCKS);
    assert_eq!(proof.num_vars, num_vars_for(proof.live_slots));

    absorb_public_batch_trace(b, ch, inputs);

    let main_red =
        verify_block_spine_unified_trace(b, ch, &proof.main, proof.num_vars, proof.live_slots);
    let shift_red = verify_block_spine_shift_trace(b, ch, &proof.shift, &main_red, proof.num_vars);

    let chain_claims = claim_chain_claims_trace(inputs, proof.num_vars);
    let chain_red = verify_linear_eval_prebound_trace(
        b,
        ch,
        &proof.chain,
        &chain_claims,
        proof.num_vars,
        ACCEPTED_CLAIM_LINEAR_RELATION_TAG,
    );

    let state_claims = vec![
        EvalClaimTrace {
            point: main_red.r_prime.clone(),
            value: main_red.state_at_r.clone(),
        },
        EvalClaimTrace {
            point: shift_red.r_double_prime.clone(),
            value: shift_red.state_at_r2.clone(),
        },
        EvalClaimTrace {
            point: chain_red.point.clone(),
            value: chain_red.value.clone(),
        },
    ];
    let sin_claims = vec![EvalClaimTrace {
        point: shift_red.r_double_prime.clone(),
        value: shift_red.s_in_at_r2.clone(),
    }];
    let sout_claims = vec![EvalClaimTrace {
        point: shift_red.r_double_prime.clone(),
        value: shift_red.s_out_at_r2.clone(),
    }];
    let claims_by_column: [&[EvalClaimTrace]; 3] = [&state_claims, &sin_claims, &sout_claims];
    let reductions =
        verify_multi_batch_eval_trace(b, ch, &proof.batch, &claims_by_column, proof.num_vars);
    let [state_red, sin_red, sout_red]: [BatchEvalReductionTrace; 3] = reductions
        .try_into()
        .map_err(|_| "multi-batch returns one reduction per column")
        .unwrap();

    AcceptedClaimHashReductionsTrace {
        state: state_red,
        sin: sin_red,
        sout: sout_red,
    }
}

// ---------------------------------------------------------------------------
// [D] — discharge replay
// ---------------------------------------------------------------------------

/// Trace twin of `discharge_accepted_claim_hash_reductions_native`:
/// `evaluate_claims` (the sponge chain over the 80 fields, with the
/// expected-claim check as pins) + the shared-point column evaluation. The
/// three reductions share one terminal point by construction of the
/// multi-batch trace (native's `state.point == sin.point == sout.point`
/// branch is compile-time here), and the chain reuses the accumulator's
/// permutation replay (see [`ColumnAccumulator`] docs).
pub fn discharge_accepted_claim_hash_trace(
    b: &mut FieldR1csBuilder,
    inputs: &[AcceptedClaimHashInputsTrace],
    reductions: &AcceptedClaimHashReductionsTrace,
) {
    assert!(!inputs.is_empty());
    let live_slots = inputs.len() * ACCEPTED_CLAIM_BLOCKS;
    let iv = capacity_iv(TAG_ACCBLK);

    let mut acc = ColumnAccumulator::new(b, &reductions.state.point, live_slots);

    for input in inputs {
        // evaluate_claims: state = [0, 0, iv0, iv1]; per block absorb the
        // two field lanes into the rate, record state_in, permute.
        let mut state: [LinExpr; STATE_SIZE] = [
            LinExpr::zero(),
            LinExpr::zero(),
            const_block(iv[0]),
            const_block(iv[1]),
        ];
        for block_idx in 0..ACCEPTED_CLAIM_BLOCKS {
            state[0] = state[0].add(&input.fields[2 * block_idx]);
            state[1] = state[1].add(&input.fields[2 * block_idx + 1]);
            state = acc.push_slot(b, &state);
        }
        // `if state[..2] != input.expected_claim { return None }` → pins.
        for lane in 0..ACCEPTED_CLAIM_PIN_LANES {
            pin_zero(b, &state[lane].add(&input.expected_claim[lane]));
        }
    }

    let (state_value, sin_value, sout_value) = acc.finish();
    pin_zero(b, &state_value.add(&reductions.state.value));
    pin_zero(b, &sin_value.add(&reductions.sin.value));
    pin_zero(b, &sout_value.add(&reductions.sout.value));
}

// ---------------------------------------------------------------------------
// Full slot assembly
// ---------------------------------------------------------------------------

/// Build the complete accepted_claim_hash [K]+[D] slot from native objects:
/// allocates the statement and proof as witness, replays the verifier on
/// `ch` and discharges the reductions. Returns the input expressions (for
/// the [B] receipt binding) and the reductions.
pub fn build_accepted_claim_hash_slot(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    proof: &AcceptedClaimHashProofKillShot,
    inputs: &[AcceptedClaimHashInputs],
) -> (
    Vec<AcceptedClaimHashInputsTrace>,
    AcceptedClaimHashReductionsTrace,
) {
    let inputs_t: Vec<AcceptedClaimHashInputsTrace> = inputs
        .iter()
        .map(|i| AcceptedClaimHashInputsTrace::alloc(b, i))
        .collect();
    let proof_t = AcceptedClaimHashProofTrace::alloc(b, proof, inputs.len());
    let reductions = verify_accepted_claim_hash_killshot_trace(b, ch, &proof_t, &inputs_t);
    discharge_accepted_claim_hash_trace(b, &inputs_t, &reductions);
    (inputs_t, reductions)
}

// ---------------------------------------------------------------------------
// Tests — positive fixture, lockstep, auto-mutator, native⇔trace cross-test
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::super::test_support::assert_expr_is;
    use super::*;
    use noid_core::{Block128, TowerField};
    use noid_gkr::accepted_claim_killshot::{
        discharge_accepted_claim_hash_reductions_native, prove_accepted_claim_hash_killshot,
        verify_accepted_claim_hash_killshot,
    };
    use noid_poseidon2b::channel::Poseidon2bChannel;
    use noid_poseidon2b::native::compression::Poseidon2bSponge;

    fn fixture_input(seed: u128) -> AcceptedClaimHashInputs {
        let fields: [Block128; ACCEPTED_CLAIM_FIELDS] = std::array::from_fn(|i| {
            Block128::from(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) + i as u128)
        });
        let mut sponge = Poseidon2bSponge::with_iv(capacity_iv(TAG_ACCBLK));
        for pair in fields.chunks_exact(2) {
            sponge.absorb_pair(pair[0], pair[1]);
        }
        let digest = sponge.finalize_no_pad();
        let expected_claim = [
            Block128::from(u128::from_le_bytes(digest[..16].try_into().unwrap())),
            Block128::from(u128::from_le_bytes(digest[16..].try_into().unwrap())),
        ];
        AcceptedClaimHashInputs {
            fields,
            expected_claim,
        }
    }

    fn prove_fixture(inputs: &[AcceptedClaimHashInputs]) -> AcceptedClaimHashProofKillShot {
        let mut ch_p = Poseidon2bChannel::new();
        let (proof, _) = prove_accepted_claim_hash_killshot(inputs, &mut ch_p);
        proof
    }

    /// Build the full [K]+[D] slot and return the built system.
    fn build_slot(
        proof: &AcceptedClaimHashProofKillShot,
        inputs: &[AcceptedClaimHashInputs],
    ) -> (
        noid_ivc_core::field_r1cs::FieldR1cs,
        Vec<noid_ivc_core::field::F128>,
        bool,
    ) {
        let mut b = FieldR1csBuilder::new();
        let mut ch = RawChannelTrace::new();
        let _ = build_accepted_claim_hash_slot(&mut b, &mut ch, proof, inputs);
        let (r1cs, z) = b.build();
        let sat = r1cs.satisfies(&z);
        (r1cs, z, sat)
    }

    /// Positive: the honest fixture's trace matches the native reductions
    /// value-for-value and is satisfiable.
    #[test]
    fn accepted_claim_hash_trace_positive_lockstep() {
        let inputs = vec![fixture_input(1)];
        let proof = prove_fixture(&inputs);

        let mut ch_n = Poseidon2bChannel::new();
        let red_native = verify_accepted_claim_hash_killshot(&proof, &inputs, &mut ch_n)
            .expect("native accepts the honest proof");
        assert!(discharge_accepted_claim_hash_reductions_native(
            &inputs,
            &red_native
        ));

        let mut b = FieldR1csBuilder::new();
        let mut ch = RawChannelTrace::new();
        let (_, red_t) = build_accepted_claim_hash_slot(&mut b, &mut ch, &proof, &inputs);
        for (e, v) in red_t.state.point.iter().zip(red_native.state.point.iter()) {
            assert_expr_is(&b, e, *v, "terminal point");
        }
        assert_expr_is(
            &b,
            &red_t.state.value,
            red_native.state.value,
            "state value",
        );
        assert_expr_is(&b, &red_t.sin.value, red_native.sin.value, "sin value");
        assert_expr_is(&b, &red_t.sout.value, red_native.sout.value, "sout value");

        let (r1cs, z) = b.build();
        assert!(
            r1cs.satisfies(&z),
            "honest accepted_claim_hash trace unsatisfiable"
        );
        eprintln!(
            "accepted_claim_hash slot: {} useful rows (k_log = {})",
            r1cs.useful_rows, r1cs.k_log
        );
    }

    /// Two-input batch positive (exercises slot chaining across inputs and
    /// the larger num_vars shape).
    #[test]
    fn accepted_claim_hash_trace_two_inputs() {
        let inputs = vec![fixture_input(3), fixture_input(4)];
        let proof = prove_fixture(&inputs);
        let (_, _, sat) = build_slot(&proof, &inputs);
        assert!(sat, "honest two-input trace unsatisfiable");
    }

    /// Enumerate every Block128 field of the proof.
    fn visit_proof_fields(
        p: &mut AcceptedClaimHashProofKillShot,
        f: &mut dyn FnMut(&mut Block128),
    ) {
        for rp in &mut p.kill_shot.main.round_polys {
            for c in &mut rp.coeffs_no_linear {
                f(c);
            }
        }
        f(&mut p.kill_shot.main.s_in_dec_at_r);
        f(&mut p.kill_shot.main.s_out_dec_at_r);
        f(&mut p.kill_shot.main.state_dec_at_r);
        f(&mut p.kill_shot.main.state_at_r);
        for v in &mut p.kill_shot.main.s_out_lane_dec_at_r {
            f(v);
        }
        for v in &mut p.kill_shot.main.state_lane_dec_at_r {
            f(v);
        }
        for rp in &mut p.kill_shot.shift.round_polys {
            for c in &mut rp.coeffs_no_linear {
                f(c);
            }
        }
        f(&mut p.kill_shot.shift.s_in_at_r2);
        f(&mut p.kill_shot.shift.s_out_at_r2);
        f(&mut p.kill_shot.shift.state_at_r2);
        for r in &mut p.chain.rounds {
            for e in &mut r.evals_at_1_2 {
                f(e);
            }
        }
        f(&mut p.chain.b_final);
        for r in &mut p.batch.rounds {
            for e in &mut r.evals_at_1_2 {
                f(e);
            }
        }
        for v in &mut p.batch.b_finals {
            f(v);
        }
    }

    fn count_proof_fields(p: &AcceptedClaimHashProofKillShot) -> usize {
        let mut n = 0usize;
        let mut c = p.clone();
        visit_proof_fields(&mut c, &mut |_| n += 1);
        n
    }

    fn mutate_proof_field(
        p: &AcceptedClaimHashProofKillShot,
        target: usize,
    ) -> AcceptedClaimHashProofKillShot {
        let mut m = p.clone();
        let mut i = 0usize;
        visit_proof_fields(&mut m, &mut |v| {
            if i == target {
                *v += Block128::ONE;
            }
            i += 1;
        });
        m
    }

    /// Replay-completeness auto-mutator (proof side): every field element of the proof,
    /// corrupted one at a time → native rejects AND the trace is
    /// unsatisfiable. 0 surviving mutants.
    ///
    /// Full sweep by default; `NOID_TRACE_MUTATE_STRIDE=k` samples every
    /// k-th field for quicker local iteration.
    #[test]
    fn accepted_claim_hash_proof_mutator_kills_all() {
        let inputs = vec![fixture_input(9)];
        let proof = prove_fixture(&inputs);
        let n_fields = count_proof_fields(&proof);
        let stride: usize = std::env::var("NOID_TRACE_MUTATE_STRIDE")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(1);

        let mut survivors = Vec::new();
        for target in (0..n_fields).step_by(stride) {
            let bad = mutate_proof_field(&proof, target);
            let mut ch_n = Poseidon2bChannel::new();
            let native_accepts =
                verify_accepted_claim_hash_killshot(&bad, &inputs, &mut ch_n).is_some();
            assert!(
                !native_accepts,
                "native accepted proof mutant {target} — fixture broken"
            );
            let (_, _, sat) = build_slot(&bad, &inputs);
            if sat {
                survivors.push(target);
            }
        }
        assert!(
            survivors.is_empty(),
            "surviving proof mutants (trace satisfiable, native rejects): {survivors:?} of {n_fields}"
        );
    }

    /// Statement/discharge auto-mutator: every claim
    /// field and expected-claim lane, corrupted one at a time → native
    /// rejects and the trace is unsatisfiable. Because the discharge shares
    /// the field wires with the verifier absorbs, this simultaneously covers
    /// the discharge-data binding.
    #[test]
    fn accepted_claim_hash_statement_mutator_kills_all() {
        let inputs = vec![fixture_input(17)];
        let proof = prove_fixture(&inputs);
        let stride: usize = std::env::var("NOID_TRACE_MUTATE_STRIDE")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(1);

        let mut survivors = Vec::new();
        for target in (0..ACCEPTED_CLAIM_FIELDS + ACCEPTED_CLAIM_PIN_LANES).step_by(stride) {
            let mut bad = inputs.clone();
            if target < ACCEPTED_CLAIM_FIELDS {
                bad[0].fields[target] += Block128::ONE;
            } else {
                bad[0].expected_claim[target - ACCEPTED_CLAIM_FIELDS] += Block128::ONE;
            }
            let mut ch_n = Poseidon2bChannel::new();
            let native_accepts = verify_accepted_claim_hash_killshot(&proof, &bad, &mut ch_n)
                .map(|red| discharge_accepted_claim_hash_reductions_native(&bad, &red))
                .unwrap_or(false);
            assert!(!native_accepts, "native accepted statement mutant {target}");
            let (_, _, sat) = build_slot(&proof, &bad);
            if sat {
                survivors.push(target);
            }
        }
        assert!(
            survivors.is_empty(),
            "surviving statement mutants: {survivors:?}"
        );
    }

    /// Cross-test "trace accepts ⇔ native accepts" on randomized cases:
    /// honest proofs (must both accept) and single-field random mutations
    /// (must both reject). Case count: 100 by default,
    /// `NOID_TRACE_CROSS_CASES=n` to override.
    #[test]
    fn accepted_claim_hash_native_trace_equivalence() {
        let cases: usize = std::env::var("NOID_TRACE_CROSS_CASES")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(100);
        let mut seed = 0xC0FF_EEu128;
        let mut next = |m: u128| {
            seed = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
            (seed >> 16) % m
        };

        for case in 0..cases {
            let inputs = vec![fixture_input(1000 + case as u128)];
            let proof = prove_fixture(&inputs);
            let n_fields = count_proof_fields(&proof);

            // Even cases: honest. Odd cases: one random corruption, split
            // between proof fields and statement fields.
            let (proof_c, inputs_c) = if case % 2 == 0 {
                (proof.clone(), inputs.clone())
            } else if next(2) == 0 {
                (
                    mutate_proof_field(&proof, next(n_fields as u128) as usize),
                    inputs.clone(),
                )
            } else {
                let mut bad = inputs.clone();
                let t = next((ACCEPTED_CLAIM_FIELDS + ACCEPTED_CLAIM_PIN_LANES) as u128) as usize;
                if t < ACCEPTED_CLAIM_FIELDS {
                    bad[0].fields[t] += Block128::ONE;
                } else {
                    bad[0].expected_claim[t - ACCEPTED_CLAIM_FIELDS] += Block128::ONE;
                }
                (proof.clone(), bad)
            };

            let mut ch_n = Poseidon2bChannel::new();
            let native_accepts =
                verify_accepted_claim_hash_killshot(&proof_c, &inputs_c, &mut ch_n)
                    .map(|red| discharge_accepted_claim_hash_reductions_native(&inputs_c, &red))
                    .unwrap_or(false);
            let (_, _, trace_accepts) = build_slot(&proof_c, &inputs_c);
            assert_eq!(
                native_accepts,
                trace_accepts,
                "native/trace divergence on case {case} (honest = {})",
                case % 2 == 0
            );
        }
    }
}
