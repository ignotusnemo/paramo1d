// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Trace twins of the dynamic block-spine verifiers
//! (`noid_gkr::block_spine`): `verify_block_spine_unified` and
//! `verify_block_spine_shift`, plus the discharge-side column evaluation
//! (`evaluate_block_spine_columns_from_slot_state_ins`). These are the shared
//! engine under `accepted_claim_hash`, the tx-body spines and the batched
//! Merkle/state killshots.

use noid_core::{Block128, TowerField};
use noid_gkr::block_spine::{
    BlockSpineShiftProof, BlockSpineUnifiedProof, BLOCK_SPINE_ROUND_DEGREE,
    BLOCK_SPINE_SHIFT_DEGREE,
};
use noid_gkr::spine_mle::{sigma_at, N_SPINE_ELEM_VARS, N_SPINE_ROUND_VARS};
use noid_poseidon2b::native::permutation::{
    F_ROUNDS, MDS_FULL, MDS_PARTIAL, N_ROUNDS, P_ROUNDS, ROUND_CONSTANTS, STATE_SIZE,
};

use super::{
    alloc_block, eq_ind_partial_eval_trace, eq_ind_trace, evaluate_slice_trace, flat_of, mul,
    pin_zero, FieldR1csBuilder, LinExpr, RawChannelTrace, RoundPolyTrace, F128,
};

const ELEM_BITS: usize = N_SPINE_ELEM_VARS; // 2
const ROUND_BITS: usize = N_SPINE_ROUND_VARS; // 7
const ROUND_LIMIT: usize = 1 << ROUND_BITS; // 128

/// Trace twin of `mds_coeff_dyn` (a public constant).
fn mds_coeff_dyn_const(round: usize, i: usize, j: usize) -> Block128 {
    let is_partial = (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&round);
    let raw = if is_partial {
        MDS_PARTIAL[i][j]
    } else {
        MDS_FULL[i][j]
    };
    Block128::from(raw)
}

// ---------------------------------------------------------------------------
// Proof wire types
// ---------------------------------------------------------------------------

/// Trace twin of `BlockSpineUnifiedProof`.
pub struct BlockSpineUnifiedProofTrace {
    pub round_polys: Vec<RoundPolyTrace>,
    pub s_in_dec_at_r: LinExpr,
    pub s_out_dec_at_r: LinExpr,
    pub state_dec_at_r: LinExpr,
    pub state_at_r: LinExpr,
    pub s_out_lane_dec_at_r: [LinExpr; STATE_SIZE],
    pub state_lane_dec_at_r: [LinExpr; STATE_SIZE],
}

impl BlockSpineUnifiedProofTrace {
    pub fn alloc(
        b: &mut FieldR1csBuilder,
        native: &BlockSpineUnifiedProof,
        num_vars: usize,
    ) -> Self {
        assert_eq!(
            native.round_polys.len(),
            num_vars,
            "unified proof off the trace shape"
        );
        Self {
            round_polys: native
                .round_polys
                .iter()
                .map(|p| RoundPolyTrace::alloc(b, p, BLOCK_SPINE_ROUND_DEGREE))
                .collect(),
            s_in_dec_at_r: alloc_block(b, native.s_in_dec_at_r),
            s_out_dec_at_r: alloc_block(b, native.s_out_dec_at_r),
            state_dec_at_r: alloc_block(b, native.state_dec_at_r),
            state_at_r: alloc_block(b, native.state_at_r),
            s_out_lane_dec_at_r: std::array::from_fn(|i| {
                alloc_block(b, native.s_out_lane_dec_at_r[i])
            }),
            state_lane_dec_at_r: std::array::from_fn(|i| {
                alloc_block(b, native.state_lane_dec_at_r[i])
            }),
        }
    }
}

/// Trace twin of `BlockSpineUnifiedReduction` (β/γ carried for the shift's
/// combined target, exactly as native).
pub struct BlockSpineUnifiedReductionTrace {
    pub r_prime: Vec<LinExpr>,
    pub s_in_dec_at_r: LinExpr,
    pub s_out_dec_at_r: LinExpr,
    pub state_dec_at_r: LinExpr,
    pub state_at_r: LinExpr,
    pub s_out_lane_dec_at_r: [LinExpr; STATE_SIZE],
    pub state_lane_dec_at_r: [LinExpr; STATE_SIZE],
}

/// Trace twin of `BlockSpineShiftProof`.
pub struct BlockSpineShiftProofTrace {
    pub round_polys: Vec<RoundPolyTrace>,
    pub s_in_at_r2: LinExpr,
    pub s_out_at_r2: LinExpr,
    pub state_at_r2: LinExpr,
}

impl BlockSpineShiftProofTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &BlockSpineShiftProof, num_vars: usize) -> Self {
        assert_eq!(
            native.round_polys.len(),
            num_vars,
            "shift proof off the trace shape"
        );
        Self {
            round_polys: native
                .round_polys
                .iter()
                .map(|p| RoundPolyTrace::alloc(b, p, BLOCK_SPINE_SHIFT_DEGREE))
                .collect(),
            s_in_at_r2: alloc_block(b, native.s_in_at_r2),
            s_out_at_r2: alloc_block(b, native.s_out_at_r2),
            state_at_r2: alloc_block(b, native.state_at_r2),
        }
    }
}

/// Trace twin of `BlockSpineShiftReduction`.
pub struct BlockSpineShiftReductionTrace {
    pub r_double_prime: Vec<LinExpr>,
    pub s_in_at_r2: LinExpr,
    pub s_out_at_r2: LinExpr,
    pub state_at_r2: LinExpr,
}

// ---------------------------------------------------------------------------
// fast_eval_block_schedules
// ---------------------------------------------------------------------------

struct SchedulesAtR {
    u_at_r: LinExpr,
    sigma_dec_at_r: LinExpr,
    rc_dec_at_r: LinExpr,
    mds_lane_at_r: [LinExpr; STATE_SIZE],
    sigma_lane_at_r: [LinExpr; STATE_SIZE],
}

/// Trace twin of `block_spine::fast_eval_block_schedules`. The σ/RC/MDS
/// schedule values are public constants, so every inner sum is affine in the
/// eq-tensor entries; multiplications are spent only on the tensors
/// themselves, the `eq_r × eq_elem` products and the final assembly.
fn fast_eval_block_schedules_trace(
    b: &mut FieldR1csBuilder,
    rho: &[LinExpr],
    r_prime: &[LinExpr],
    live_slots: usize,
) -> SchedulesAtR {
    let num_vars = r_prime.len();
    assert_eq!(rho.len(), num_vars);

    let r_elem = &r_prime[..ELEM_BITS];
    let r_round = &r_prime[ELEM_BITS..ELEM_BITS + ROUND_BITS];
    let r_slot = &r_prime[ELEM_BITS + ROUND_BITS..];
    let rho_elem = &rho[..ELEM_BITS];
    let rho_round = &rho[ELEM_BITS..ELEM_BITS + ROUND_BITS];
    let rho_slot = &rho[ELEM_BITS + ROUND_BITS..];

    let eq_elem = eq_ind_partial_eval_trace(b, r_elem);
    let eq_round_r = eq_ind_partial_eval_trace(b, r_round);
    let eq_r_slot = eq_ind_partial_eval_trace(b, r_slot);
    let eq_rho_elem = eq_ind_partial_eval_trace(b, rho_elem);
    let eq_rho_round = eq_ind_partial_eval_trace(b, rho_round);
    let eq_rho_slot = eq_ind_partial_eval_trace(b, rho_slot);

    // live_sum_r = Σ_{s < live_slots} eq(r'_slot, s) — affine, free.
    let mut live_sum_r = LinExpr::zero();
    for e in &eq_r_slot[..live_slots] {
        live_sum_r = live_sum_r.add(e);
    }

    // Inner sums over (round, elem): schedule values are constants ⇒ the
    // sums are affine in eq_re = eq_round_r[round] · eq_elem[elem].
    let mut sigma_dec_inner = LinExpr::zero();
    let mut rc_dec_inner = LinExpr::zero();
    let mut mds_inner: [LinExpr; STATE_SIZE] = std::array::from_fn(|_| LinExpr::zero());
    let mut sigma_round_sum: [LinExpr; STATE_SIZE] = std::array::from_fn(|_| LinExpr::zero());

    for round in 1..ROUND_LIMIT.min(N_ROUNDS + 1) {
        let eq_r = &eq_round_r[round];
        let prev = round - 1;

        for elem in 0..STATE_SIZE {
            let eq_re = mul(b, eq_r, &eq_elem[elem]);

            if sigma_at(prev, elem) == Block128::ONE {
                sigma_dec_inner = sigma_dec_inner.add(&eq_re);
            }

            let is_partial = (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&prev);
            if !is_partial || elem == 0 {
                rc_dec_inner = rc_dec_inner
                    .add(&eq_re.scale(flat_of(Block128::from(ROUND_CONSTANTS[elem][prev]))));
            }

            for (j, inner) in mds_inner.iter_mut().enumerate().take(STATE_SIZE) {
                *inner = inner.add(&eq_re.scale(flat_of(mds_coeff_dyn_const(prev, elem, j))));
            }
        }

        for (j, sum) in sigma_round_sum.iter_mut().enumerate().take(STATE_SIZE) {
            if sigma_at(prev, j) == Block128::ONE {
                *sum = sum.add(eq_r);
            }
        }
    }

    let sigma_dec_at_r = mul(b, &live_sum_r, &sigma_dec_inner);
    let rc_dec_at_r = mul(b, &live_sum_r, &rc_dec_inner);
    let mds_lane_at_r: [LinExpr; STATE_SIZE] =
        std::array::from_fn(|j| mul(b, &live_sum_r, &mds_inner[j]));
    let sigma_lane_at_r: [LinExpr; STATE_SIZE] =
        std::array::from_fn(|j| mul(b, &live_sum_r, &sigma_round_sum[j]));

    // u_MLE(r') = slot_factor × round_factor × elem_factor.
    let mut u_slot_factor = LinExpr::zero();
    for s in 0..live_slots {
        u_slot_factor = u_slot_factor.add(&mul(b, &eq_rho_slot[s], &eq_r_slot[s]));
    }
    let mut u_round_factor = LinExpr::zero();
    for r in 1..ROUND_LIMIT.min(N_ROUNDS + 1) {
        u_round_factor = u_round_factor.add(&mul(b, &eq_rho_round[r - 1], &eq_round_r[r]));
    }
    let mut u_elem_factor = LinExpr::zero();
    for e in 0..STATE_SIZE {
        u_elem_factor = u_elem_factor.add(&mul(b, &eq_rho_elem[e], &eq_elem[e]));
    }
    let u_sr = mul(b, &u_slot_factor, &u_round_factor);
    let u_at_r = mul(b, &u_sr, &u_elem_factor);

    SchedulesAtR {
        u_at_r,
        sigma_dec_at_r,
        rc_dec_at_r,
        mds_lane_at_r,
        sigma_lane_at_r,
    }
}

// ---------------------------------------------------------------------------
// verify_block_spine_unified
// ---------------------------------------------------------------------------

/// Trace twin of `block_spine::verify_block_spine_unified`.
pub fn verify_block_spine_unified_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    proof: &BlockSpineUnifiedProofTrace,
    num_vars: usize,
    live_slots: usize,
) -> BlockSpineUnifiedReductionTrace {
    assert_eq!(proof.round_polys.len(), num_vars);
    // Degree bound: structural (RoundPolyTrace::alloc pins the coeff count).

    let rho: Vec<LinExpr> = ch.squeeze_n(b, num_vars);
    let beta = ch.squeeze(b);
    let gamma = ch.squeeze(b);

    let mut expected = LinExpr::zero();
    let mut r_prime: Vec<Option<LinExpr>> = vec![None; num_vars];

    for (round, poly) in proof.round_polys.iter().enumerate() {
        // The linear coefficient comes from the running claim, so the
        // per-round sum check holds by construction (no pin).
        poly.absorb_coeffs(b, ch);
        let challenge = ch.squeeze(b);
        expected = poly.evaluate_reconstructed(b, &expected, &challenge);
        r_prime[num_vars - 1 - round] = Some(challenge);
    }
    let r_prime: Vec<LinExpr> = r_prime.into_iter().map(Option::unwrap).collect();

    let sched = fast_eval_block_schedules_trace(b, &rho, &r_prime, live_slots);

    // Reassemble constraint at r' (pow7 via the S-box gadget).
    let sin_pow7 = b.pow7(&proof.s_in_dec_at_r);
    let q_c1 = mul(b, &sched.sigma_dec_at_r, &sin_pow7)
        .add(&proof.s_out_dec_at_r)
        .add(&proof.s_in_dec_at_r)
        .add(&mul(b, &sched.sigma_dec_at_r, &proof.s_in_dec_at_r));
    let q_c1p_inner = proof
        .s_in_dec_at_r
        .add(&proof.state_dec_at_r)
        .add(&sched.rc_dec_at_r);
    let q_c1p = mul(b, &sched.sigma_dec_at_r, &q_c1p_inner);
    let mut c2_sum = proof.state_at_r.clone();
    for j in 0..STATE_SIZE {
        let pi_j = mul(b, &sched.sigma_lane_at_r[j], &proof.s_out_lane_dec_at_r[j]).add(&mul(
            b,
            &sched.sigma_lane_at_r[j].add_const(F128::ONE),
            &proof.state_lane_dec_at_r[j],
        ));
        c2_sum = c2_sum.add(&mul(b, &sched.mds_lane_at_r[j], &pi_j));
    }
    let q_at_r = q_c1
        .add(&mul(b, &beta, &q_c1p))
        .add(&mul(b, &gamma, &c2_sum));

    let rhs = mul(b, &sched.u_at_r, &q_at_r);
    pin_zero(b, &expected.add(&rhs));

    ch.absorb(b, &proof.s_in_dec_at_r);
    ch.absorb(b, &proof.s_out_dec_at_r);
    ch.absorb(b, &proof.state_dec_at_r);
    ch.absorb(b, &proof.state_at_r);
    for v in &proof.s_out_lane_dec_at_r {
        ch.absorb(b, v);
    }
    for v in &proof.state_lane_dec_at_r {
        ch.absorb(b, v);
    }

    BlockSpineUnifiedReductionTrace {
        r_prime,
        s_in_dec_at_r: proof.s_in_dec_at_r.clone(),
        s_out_dec_at_r: proof.s_out_dec_at_r.clone(),
        state_dec_at_r: proof.state_dec_at_r.clone(),
        state_at_r: proof.state_at_r.clone(),
        s_out_lane_dec_at_r: proof.s_out_lane_dec_at_r.clone(),
        state_lane_dec_at_r: proof.state_lane_dec_at_r.clone(),
    }
}

// ---------------------------------------------------------------------------
// verify_block_spine_shift
// ---------------------------------------------------------------------------

/// Trace twin of `block_spine::block_combined_target`.
fn block_combined_target_trace(
    b: &mut FieldR1csBuilder,
    red: &BlockSpineUnifiedReductionTrace,
    delta: &LinExpr,
) -> LinExpr {
    // Powers of δ: d1 = δ, d2 = δ², then 8 more for the lane weights.
    let d1 = delta.clone();
    let d2 = mul(b, &d1, delta);
    let mut acc = red
        .s_in_dec_at_r
        .add(&mul(b, &d1, &red.s_out_dec_at_r))
        .add(&mul(b, &d2, &red.state_dec_at_r));
    let mut p = mul(b, &d2, delta);
    for j in 0..STATE_SIZE {
        acc = acc.add(&mul(b, &p, &red.s_out_lane_dec_at_r[j]));
        p = mul(b, &p, delta);
    }
    for j in 0..STATE_SIZE {
        acc = acc.add(&mul(b, &p, &red.state_lane_dec_at_r[j]));
        p = mul(b, &p, delta);
    }
    acc
}

struct BlockWeightsAtPointTrace {
    w_sin: LinExpr,
    w_sout: LinExpr,
    w_state: LinExpr,
}

/// Trace twin of `block_spine::block_combined_weights_at_point`.
fn block_combined_weights_at_point_trace(
    b: &mut FieldR1csBuilder,
    r_prime: &[LinExpr],
    delta: &LinExpr,
    r2: &[LinExpr],
    num_vars: usize,
) -> BlockWeightsAtPointTrace {
    let rp_elem = &r_prime[0..ELEM_BITS];
    let rp_round = &r_prime[ELEM_BITS..ELEM_BITS + ROUND_BITS];
    let rp_slot = &r_prime[ELEM_BITS + ROUND_BITS..num_vars];
    let r2_elem = &r2[0..ELEM_BITS];
    let r2_round = &r2[ELEM_BITS..ELEM_BITS + ROUND_BITS];
    let r2_slot = &r2[ELEM_BITS + ROUND_BITS..num_vars];

    let eq_slot = eq_ind_trace(b, rp_slot, r2_slot);
    let eq_elem = eq_ind_trace(b, rp_elem, r2_elem);

    // g_round: the round-increment permutation of eq(rp_round, ·), evaluated
    // at r2_round. The permutation is a relabeling — free.
    let n_rounds = 1usize << ROUND_BITS;
    let eq_rp_round_tab = eq_ind_partial_eval_trace(b, rp_round);
    let mut tab: Vec<LinExpr> = vec![LinExpr::zero(); n_rounds];
    for (round_x, slot) in tab.iter_mut().enumerate().take(n_rounds) {
        let inc = (round_x + 1) & (n_rounds - 1);
        *slot = eq_rp_round_tab[inc].clone();
    }
    let g_round = evaluate_slice_trace(b, &tab, r2_round);

    // ind_j(r2_elem): the eq tensor over r2_elem IS the per-j product.
    let ind_j_at_r2 = eq_ind_partial_eval_trace(b, r2_elem);

    let lane_base = mul(b, &eq_slot, &g_round);
    let w_dec_r2 = mul(b, &lane_base, &eq_elem);

    // δ powers (same ladder as the combined target).
    let d1 = delta.clone();
    let d2 = mul(b, &d1, delta);
    let mut p = d2.clone();
    let mut lane_sout: Vec<LinExpr> = Vec::with_capacity(STATE_SIZE);
    for _ in 0..STATE_SIZE {
        p = mul(b, &p, delta);
        lane_sout.push(p.clone());
    }
    let mut lane_state: Vec<LinExpr> = Vec::with_capacity(STATE_SIZE);
    for _ in 0..STATE_SIZE {
        p = mul(b, &p, delta);
        lane_state.push(p.clone());
    }

    let w_sin = w_dec_r2.clone();
    let mut w_sout = mul(b, &d1, &w_dec_r2);
    let mut w_state = mul(b, &d2, &w_dec_r2);
    for j in 0..STATE_SIZE {
        let lane_w = mul(b, &lane_base, &ind_j_at_r2[j]);
        w_sout = w_sout.add(&mul(b, &lane_sout[j], &lane_w));
        w_state = w_state.add(&mul(b, &lane_state[j], &lane_w));
    }

    BlockWeightsAtPointTrace {
        w_sin,
        w_sout,
        w_state,
    }
}

/// Trace twin of `block_spine::verify_block_spine_shift`.
pub fn verify_block_spine_shift_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    proof: &BlockSpineShiftProofTrace,
    main_reduction: &BlockSpineUnifiedReductionTrace,
    num_vars: usize,
) -> BlockSpineShiftReductionTrace {
    assert_eq!(proof.round_polys.len(), num_vars);

    let delta = ch.squeeze(b);
    let expected_target = block_combined_target_trace(b, main_reduction, &delta);

    let mut expected = expected_target;
    let mut r_double_prime: Vec<Option<LinExpr>> = vec![None; num_vars];

    for (round, poly) in proof.round_polys.iter().enumerate() {
        // Same reconstruction as the unified loop — sum check by
        // construction.
        poly.absorb_coeffs(b, ch);
        let challenge = ch.squeeze(b);
        expected = poly.evaluate_reconstructed(b, &expected, &challenge);
        r_double_prime[num_vars - 1 - round] = Some(challenge);
    }
    let r_double_prime: Vec<LinExpr> = r_double_prime.into_iter().map(Option::unwrap).collect();

    let w = block_combined_weights_at_point_trace(
        b,
        &main_reduction.r_prime,
        &delta,
        &r_double_prime,
        num_vars,
    );
    let claimed = mul(b, &w.w_sin, &proof.s_in_at_r2)
        .add(&mul(b, &w.w_sout, &proof.s_out_at_r2))
        .add(&mul(b, &w.w_state, &proof.state_at_r2));
    pin_zero(b, &expected.add(&claimed));

    ch.absorb(b, &proof.s_in_at_r2);
    ch.absorb(b, &proof.s_out_at_r2);
    ch.absorb(b, &proof.state_at_r2);

    BlockSpineShiftReductionTrace {
        r_double_prime,
        s_in_at_r2: proof.s_in_at_r2.clone(),
        s_out_at_r2: proof.s_out_at_r2.clone(),
        state_at_r2: proof.state_at_r2.clone(),
    }
}

// ---------------------------------------------------------------------------
// Spine-family shared pieces
// ---------------------------------------------------------------------------

/// Trace twin of the multi-batch closure every spine-family killshot ends
/// with (`accepted_claim_hash`, `header_hash`, direct accumulator, …): the
/// three column claim sets `(state ← r', r'', chain point; s_in/s_out ← r'')`
/// fed into `verify_multi_batch_eval`. Returns `[state, sin, sout]`.
pub fn close_spine_family_batch(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    main_red: &BlockSpineUnifiedReductionTrace,
    shift_red: &BlockSpineShiftReductionTrace,
    chain_red: &super::BatchEvalReductionTrace,
    batch: &super::batch_eval::MultiBatchEvalProofTrace,
    num_vars: usize,
) -> [super::BatchEvalReductionTrace; 3] {
    use super::batch_eval::{verify_multi_batch_eval_trace, EvalClaimTrace};
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
    let reductions = verify_multi_batch_eval_trace(b, ch, batch, &claims_by_column, num_vars);
    reductions
        .try_into()
        .map_err(|_| "multi-batch returns one reduction per column")
        .unwrap()
}

/// Pack a boolean spine point back into its index (the native
/// `block_spine_state_point` packing is the single source of truth).
pub fn spine_point_index(num_vars: usize, slot: usize, round: usize, lane: usize) -> usize {
    let point = noid_gkr::block_spine::block_spine_state_point(num_vars, slot, round, lane);
    let mut index = 0usize;
    for (bit, v) in point.iter().enumerate() {
        if *v == Block128::ONE {
            index |= 1 << bit;
        } else {
            debug_assert_eq!(*v, Block128::ZERO);
        }
    }
    index
}

/// Trace twin of the shared `sponge_chain_claims` helper
/// (`header_hash_killshot::sponge_chain_claims`; `accepted_claim_killshot`'s
/// `claim_chain_claims` is the same relation per input): the public linear
/// relations binding a rate-2 sponge chain's round-0 states to the absorbed
/// blocks and the final state to the expected digest. Same claim and term
/// order as native.
pub fn sponge_chain_claims_trace(
    blocks: &[[LinExpr; 2]],
    iv: [Block128; 2],
    expected: &[LinExpr],
    slot_offset: usize,
    num_vars: usize,
) -> Vec<super::batch_eval::LinearEvalClaimTrace> {
    use super::batch_eval::{LinearEvalClaimTrace, LinearEvalTermTrace};
    let mds = |row: usize, col: usize| Block128::from(MDS_FULL[row][col]);
    let mut claims = Vec::with_capacity(blocks.len() * STATE_SIZE + expected.len());
    for (block_idx, block) in blocks.iter().enumerate() {
        let slot = slot_offset + block_idx;
        for lane in 0..STATE_SIZE {
            let mut terms = vec![LinearEvalTermTrace {
                index: spine_point_index(num_vars, slot, 0, lane),
                coeff: LinExpr::constant(F128::ONE),
            }];
            let value = if block_idx == 0 {
                block[0]
                    .scale(super::flat_of(mds(lane, 0)))
                    .add(&block[1].scale(super::flat_of(mds(lane, 1))))
                    .add_const(super::flat_of(mds(lane, 2) * iv[0] + mds(lane, 3) * iv[1]))
            } else {
                for src_lane in 0..STATE_SIZE {
                    terms.push(LinearEvalTermTrace {
                        index: spine_point_index(num_vars, slot - 1, N_ROUNDS, src_lane),
                        coeff: LinExpr::constant(super::flat_of(mds(lane, src_lane))),
                    });
                }
                block[0]
                    .scale(super::flat_of(mds(lane, 0)))
                    .add(&block[1].scale(super::flat_of(mds(lane, 1))))
            };
            claims.push(LinearEvalClaimTrace { terms, value });
        }
    }
    let last_slot = slot_offset + blocks.len() - 1;
    for (lane, exp) in expected.iter().enumerate() {
        claims.push(LinearEvalClaimTrace {
            terms: vec![LinearEvalTermTrace {
                index: spine_point_index(num_vars, last_slot, N_ROUNDS, lane),
                coeff: LinExpr::constant(F128::ONE),
            }],
            value: exp.clone(),
        });
    }
    claims
}

// ---------------------------------------------------------------------------
// Discharge-side column evaluation ([D])
// ---------------------------------------------------------------------------

/// Incremental trace twin of `evaluate_block_spine_columns_from_slot_state_ins`
/// + `accumulate_permutation_columns_at_point` ([D]): replays the Poseidon2b
/// chain per slot from witness `state_in` expressions (the S-box gadget IS
/// the native `pow7_block128`) and accumulates the three column evaluations
/// at one shared point. [`Self::push_slot`] also returns the permutation
/// output state, so chained callers (`accepted_claim_hash`'s
/// `evaluate_claims`) reuse ONE in-trace replay where native replays the
/// permutation twice — the values are identical (the permutation is
/// deterministic); only the shared-subexpression structure differs.
///
/// The zero-weight skip in native `accumulate_row` is a fast path over zero
/// padding slots; the trace has no padding slots (the caller pushes exactly
/// the live inputs), so every row is accumulated.
pub struct ColumnAccumulator {
    eq_elem: Vec<LinExpr>,
    eq_round: Vec<LinExpr>,
    eq_slot: Vec<LinExpr>,
    state_acc: LinExpr,
    sin_acc: LinExpr,
    sout_acc: LinExpr,
    next_slot: usize,
    n_slots: usize,
}

impl ColumnAccumulator {
    /// `point` must have `num_vars_for(n_slots)` coordinates.
    pub fn new(b: &mut FieldR1csBuilder, point: &[LinExpr], n_slots: usize) -> Self {
        assert!(n_slots > 0);
        let num_vars = noid_gkr::block_spine::num_vars_for(n_slots);
        assert_eq!(point.len(), num_vars);
        let r_elem = &point[..ELEM_BITS];
        let r_round = &point[ELEM_BITS..ELEM_BITS + ROUND_BITS];
        let r_slot = &point[ELEM_BITS + ROUND_BITS..];
        Self {
            eq_elem: eq_ind_partial_eval_trace(b, r_elem),
            eq_round: eq_ind_partial_eval_trace(b, r_round),
            eq_slot: eq_ind_partial_eval_trace(b, r_slot),
            state_acc: LinExpr::zero(),
            sin_acc: LinExpr::zero(),
            sout_acc: LinExpr::zero(),
            next_slot: 0,
            n_slots,
        }
    }

    /// Replay one slot's permutation, fold its rows into the accumulators,
    /// and return the permutation output state (state row `N_ROUNDS`).
    ///
    /// Rows are weighted by `eq_round` alone inside the slot and the slot
    /// weight multiplies each per-slot column sum ONCE at the end —
    /// `Σ_r (w_slot·eq_r)·inner_r = w_slot·Σ_r eq_r·inner_r` exactly
    /// (associativity), replacing one `w_slot·eq_r` product per row with
    /// three products per slot.
    pub fn push_slot(
        &mut self,
        b: &mut FieldR1csBuilder,
        state_in: &[LinExpr; STATE_SIZE],
    ) -> [LinExpr; STATE_SIZE] {
        assert!(self.next_slot < self.n_slots, "more slots than declared");
        let slot_weight = self.eq_slot[self.next_slot].clone();
        self.next_slot += 1;

        let t = poseidon_flat_tables_ref();
        let mut current: [LinExpr; STATE_SIZE] = state_in.clone();
        apply_mds_symbolic_local(&mut current, &t.mds_full);

        let mut slot_state = LinExpr::zero();
        let mut slot_sin = LinExpr::zero();
        let mut slot_sout = LinExpr::zero();

        for round in 0..N_ROUNDS {
            let row_weight = &self.eq_round[round];
            let state_row = current.clone();
            accumulate_row_trace(b, &mut slot_state, &state_row, row_weight, &self.eq_elem);

            let is_partial = (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&round);
            if !is_partial {
                let mut sin: [LinExpr; STATE_SIZE] = std::array::from_fn(|_| LinExpr::zero());
                let mut sout: [LinExpr; STATE_SIZE] = std::array::from_fn(|_| LinExpr::zero());
                for lane in 0..STATE_SIZE {
                    sin[lane] = current[lane].add_const(t.rc[lane][round]);
                    sout[lane] = b.pow7(&sin[lane]);
                }
                accumulate_row_trace(b, &mut slot_sin, &sin, row_weight, &self.eq_elem);
                accumulate_row_trace(b, &mut slot_sout, &sout, row_weight, &self.eq_elem);
                current = sout;
                apply_mds_symbolic_local(&mut current, &t.mds_full);
            } else {
                let mut sin: [LinExpr; STATE_SIZE] = std::array::from_fn(|_| LinExpr::zero());
                let mut sout: [LinExpr; STATE_SIZE] = std::array::from_fn(|_| LinExpr::zero());
                sin[0] = current[0].add_const(t.rc[0][round]);
                sout[0] = b.pow7(&sin[0]);
                accumulate_row_trace(b, &mut slot_sin, &sin, row_weight, &self.eq_elem);
                accumulate_row_trace(b, &mut slot_sout, &sout, row_weight, &self.eq_elem);
                current = [
                    sout[0].clone(),
                    current[1].clone(),
                    current[2].clone(),
                    current[3].clone(),
                ];
                apply_mds_symbolic_local(&mut current, &t.mds_partial);
            }
        }

        let final_row_weight = &self.eq_round[N_ROUNDS];
        accumulate_row_trace(
            b,
            &mut slot_state,
            &current,
            final_row_weight,
            &self.eq_elem,
        );

        self.state_acc = self.state_acc.add(&mul(b, &slot_weight, &slot_state));
        self.sin_acc = self.sin_acc.add(&mul(b, &slot_weight, &slot_sin));
        self.sout_acc = self.sout_acc.add(&mul(b, &slot_weight, &slot_sout));
        current
    }

    /// `(state, s_in, s_out)` evaluations after all `n_slots` were pushed.
    pub fn finish(self) -> (LinExpr, LinExpr, LinExpr) {
        assert_eq!(self.next_slot, self.n_slots, "missing slots");
        (self.state_acc, self.sin_acc, self.sout_acc)
    }
}

/// One-shot wrapper over [`ColumnAccumulator`] — the direct twin of
/// `evaluate_block_spine_columns_from_slot_state_ins`.
pub fn evaluate_block_spine_columns_trace(
    b: &mut FieldR1csBuilder,
    slot_state_ins: &[[LinExpr; STATE_SIZE]],
    point: &[LinExpr],
) -> (LinExpr, LinExpr, LinExpr) {
    let mut acc = ColumnAccumulator::new(b, point, slot_state_ins.len());
    for state_in in slot_state_ins {
        acc.push_slot(b, state_in);
    }
    acc.finish()
}

/// Trace twin of `accumulate_row`: `acc += row_weight · Σ_lane
/// eq_elem[lane] · row[lane]` (same value, inner sum shared — 5 muls/row
/// instead of native's 8 tower muls).
fn accumulate_row_trace(
    b: &mut FieldR1csBuilder,
    acc: &mut LinExpr,
    row: &[LinExpr; STATE_SIZE],
    row_weight: &LinExpr,
    eq_elem: &[LinExpr],
) {
    let mut inner = LinExpr::zero();
    for lane in 0..STATE_SIZE {
        inner = inner.add(&mul(b, &eq_elem[lane], &row[lane]));
    }
    *acc = acc.add(&mul(b, row_weight, &inner));
}

/// φ-mapped Poseidon2b constants (same tables the permutation gadget uses;
/// duplicated read-only here because `field_circuit`'s copy is private).
struct PoseidonFlatTablesLocal {
    rc: [[F128; N_ROUNDS]; STATE_SIZE],
    mds_full: [[F128; STATE_SIZE]; STATE_SIZE],
    mds_partial: [[F128; STATE_SIZE]; STATE_SIZE],
}

fn poseidon_flat_tables_ref() -> &'static PoseidonFlatTablesLocal {
    static TABLES: std::sync::OnceLock<PoseidonFlatTablesLocal> = std::sync::OnceLock::new();
    TABLES.get_or_init(|| {
        let mut rc = [[F128::ZERO; N_ROUNDS]; STATE_SIZE];
        for (i, row) in rc.iter_mut().enumerate() {
            for (r, slot) in row.iter_mut().enumerate() {
                *slot = super::flat_const(ROUND_CONSTANTS[i][r]);
            }
        }
        let mut mds_full = [[F128::ZERO; STATE_SIZE]; STATE_SIZE];
        let mut mds_partial = [[F128::ZERO; STATE_SIZE]; STATE_SIZE];
        for i in 0..STATE_SIZE {
            for j in 0..STATE_SIZE {
                mds_full[i][j] = super::flat_const(MDS_FULL[i][j]);
                mds_partial[i][j] = super::flat_const(MDS_PARTIAL[i][j]);
            }
        }
        PoseidonFlatTablesLocal {
            rc,
            mds_full,
            mds_partial,
        }
    })
}

fn apply_mds_symbolic_local(
    state: &mut [LinExpr; STATE_SIZE],
    mds: &[[F128; STATE_SIZE]; STATE_SIZE],
) {
    let old = state.clone();
    for (i, slot) in state.iter_mut().enumerate() {
        let mut acc = LinExpr::zero();
        for (j, o) in old.iter().enumerate() {
            acc = acc.add(&o.scale(mds[i][j]));
        }
        *slot = acc;
    }
}

/// One rate-2 sponge chain for the shared discharge replay: absorb the
/// blocks in order from the IV, pin the final rate lanes to `expected`.
pub struct SpongeChainTrace {
    pub blocks: Vec<[LinExpr; 2]>,
    pub iv: [Block128; 2],
    pub expected: [LinExpr; 2],
}

/// Shared discharge skeleton for the sponge-chain killshots
/// (`accepted_claim_hash`, `header_hash`, `slot_leaf`): replay every chain
/// through one [`ColumnAccumulator`] (the
/// slot order is the concatenation order of `chains`) and pin the three
/// column evaluations against the reductions.
pub fn discharge_sponge_chains_trace(
    b: &mut FieldR1csBuilder,
    chains: &[SpongeChainTrace],
    reductions: &[super::BatchEvalReductionTrace; 3],
) {
    let live_slots: usize = chains.iter().map(|c| c.blocks.len()).sum();
    assert!(live_slots > 0);
    let mut acc = ColumnAccumulator::new(b, &reductions[0].point, live_slots);
    for chain in chains {
        let mut state: [LinExpr; STATE_SIZE] = [
            LinExpr::zero(),
            LinExpr::zero(),
            LinExpr::constant(flat_of(chain.iv[0])),
            LinExpr::constant(flat_of(chain.iv[1])),
        ];
        for block in &chain.blocks {
            state[0] = state[0].add(&block[0]);
            state[1] = state[1].add(&block[1]);
            state = acc.push_slot(b, &state);
        }
        super::pin_zero(b, &state[0].add(&chain.expected[0]));
        super::pin_zero(b, &state[1].add(&chain.expected[1]));
    }
    let (state_value, sin_value, sout_value) = acc.finish();
    super::pin_zero(b, &state_value.add(&reductions[0].value));
    super::pin_zero(b, &sin_value.add(&reductions[1].value));
    super::pin_zero(b, &sout_value.add(&reductions[2].value));
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::super::test_support::assert_expr_is;
    use super::super::{alloc_blocks, RawChannelTrace};
    use super::*;
    use noid_core::transcript::FiatShamir;
    use noid_gkr::block_spine::{
        block_spine_state_point, discharge_block_spine_batch_reductions_from_slot_state_ins_native,
        evaluate_block_spine_columns_from_slot_state_ins, num_vars_for, prove_block_spine_shift,
        prove_block_spine_unified, verify_block_spine_shift, verify_block_spine_unified,
        BlockSpineMle, BlockSpineUnifiedReduction,
    };
    use noid_poseidon2b::channel::Poseidon2bChannel;

    fn rand_states(seed: u64, n: usize) -> Vec<[Block128; STATE_SIZE]> {
        let mut s = seed as u128 | 1;
        (0..n)
            .map(|_| {
                std::array::from_fn(|_| {
                    s = s
                        .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                        .wrapping_add(0xDEAD_BEEF);
                    Block128::from(s)
                })
            })
            .collect()
    }

    /// Unified + shift traces in lockstep with native on a real proof over a
    /// small live-slot set; honest trace satisfiable, tampered final claim
    /// unsat while native also rejects.
    #[test]
    fn unified_and_shift_trace_lockstep() {
        let slot_state_ins = rand_states(5, 3);
        let mle = BlockSpineMle::build_from_slot_state_ins(&slot_state_ins);
        let num_vars = mle.num_vars;
        let live_slots = mle.live_slots;

        let mut ch_p = Poseidon2bChannel::new();
        ch_p.absorb(Block128::from(9u128));
        let (main, r_prime) = prove_block_spine_unified(&mle, &mut ch_p);
        let main_red_native = BlockSpineUnifiedReduction {
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
        let (shift, _r2) = prove_block_spine_shift(&mle, &r_prime, &main_red_native, &mut ch_p);

        // Native verify (reference challenges + reductions).
        let mut ch_n = Poseidon2bChannel::new();
        ch_n.absorb(Block128::from(9u128));
        let main_red = verify_block_spine_unified(&main, num_vars, live_slots, &mut ch_n)
            .expect("native unified accepts");
        let shift_red = verify_block_spine_shift(&shift, &main_red, num_vars, &mut ch_n)
            .expect("native shift accepts");

        // Trace replay.
        let mut b = FieldR1csBuilder::new();
        let mut ch = RawChannelTrace::new();
        ch.absorb_const_tower(&mut b, 9);
        let main_t = BlockSpineUnifiedProofTrace::alloc(&mut b, &main, num_vars);
        let main_red_t =
            verify_block_spine_unified_trace(&mut b, &mut ch, &main_t, num_vars, live_slots);
        for (e, v) in main_red_t.r_prime.iter().zip(main_red.r_prime.iter()) {
            assert_expr_is(&b, e, *v, "unified r'");
        }
        let shift_t = BlockSpineShiftProofTrace::alloc(&mut b, &shift, num_vars);
        let shift_red_t =
            verify_block_spine_shift_trace(&mut b, &mut ch, &shift_t, &main_red_t, num_vars);
        for (e, v) in shift_red_t
            .r_double_prime
            .iter()
            .zip(shift_red.r_double_prime.iter())
        {
            assert_expr_is(&b, e, *v, "shift r''");
        }
        let (r1cs, z) = b.build();
        assert!(r1cs.satisfies(&z), "honest spine trace unsatisfiable");

        // Tamper the unified terminal claim: native rejects, trace unsat.
        let mut bad = main.clone();
        bad.state_at_r += Block128::ONE;
        let mut ch_bad = Poseidon2bChannel::new();
        ch_bad.absorb(Block128::from(9u128));
        assert!(verify_block_spine_unified(&bad, num_vars, live_slots, &mut ch_bad).is_none());

        let mut b2 = FieldR1csBuilder::new();
        let mut ch2 = RawChannelTrace::new();
        ch2.absorb_const_tower(&mut b2, 9);
        let bad_t = BlockSpineUnifiedProofTrace::alloc(&mut b2, &bad, num_vars);
        let _ = verify_block_spine_unified_trace(&mut b2, &mut ch2, &bad_t, num_vars, live_slots);
        let (r1cs2, z2) = b2.build();
        assert!(!r1cs2.satisfies(&z2), "tampered unified trace satisfiable");
    }

    /// The discharge column evaluation matches native at a random point and
    /// at a boolean spine point.
    #[test]
    fn column_evaluation_trace_matches_native() {
        let slot_state_ins = rand_states(31, 2);
        let num_vars = num_vars_for(slot_state_ins.len());

        let mut points: Vec<Vec<Block128>> = Vec::new();
        // Random dense point.
        let mut s = 0xABCDu128;
        points.push(
            (0..num_vars)
                .map(|_| {
                    s = s.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(7);
                    Block128::from(s)
                })
                .collect(),
        );
        // Structural boolean point.
        points.push(block_spine_state_point(num_vars, 1, 3, 2));

        for point in points {
            let (state_n, sin_n, sout_n) =
                evaluate_block_spine_columns_from_slot_state_ins(&slot_state_ins, &point)
                    .expect("native evaluation");

            let mut b = FieldR1csBuilder::new();
            let state_in_exprs: Vec<[LinExpr; STATE_SIZE]> = slot_state_ins
                .iter()
                .map(|st| {
                    let v = alloc_blocks(&mut b, st);
                    [v[0].clone(), v[1].clone(), v[2].clone(), v[3].clone()]
                })
                .collect();
            let point_exprs = alloc_blocks(&mut b, &point);
            let (state_e, sin_e, sout_e) =
                evaluate_block_spine_columns_trace(&mut b, &state_in_exprs, &point_exprs);
            assert_expr_is(&b, &state_e, state_n, "state column");
            assert_expr_is(&b, &sin_e, sin_n, "sin column");
            assert_expr_is(&b, &sout_e, sout_n, "sout column");
            let (r1cs, z) = b.build();
            assert!(r1cs.satisfies(&z));
        }

        // Link the native discharge path to the same evaluator (sanity).
        let point = block_spine_state_point(num_vars, 0, 0, 0);
        let (sv, iv, ov) =
            evaluate_block_spine_columns_from_slot_state_ins(&slot_state_ins, &point).unwrap();
        use noid_gkr::batch_eval::BatchEvalReduction;
        assert!(
            discharge_block_spine_batch_reductions_from_slot_state_ins_native(
                &slot_state_ins,
                &BatchEvalReduction {
                    point: point.clone(),
                    value: sv
                },
                &BatchEvalReduction {
                    point: point.clone(),
                    value: iv
                },
                &BatchEvalReduction { point, value: ov },
            )
        );
    }
}
