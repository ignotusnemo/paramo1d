// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

#![allow(clippy::needless_range_loop)]

//! Unified Kill-Shot sumcheck — main half.
//!
//! Discharges the full Spine algebraic surface (C1 + β·C1' + γ·C2)
//! in a single degree-9 sumcheck of length `N_SPINE_UNIFIED_VARS = 14`.
//!
//! Variant I (immutable tables + later shift gadget): the change of
//! variable `y = inc_round(x)` is realised by materialising one
//! permuted helper table per "indexed at dec(y)" factor. All factors
//! then become standard multilinear MLEs in `y`, the round polynomial
//! is degree 9, and the sumcheck folds high-to-low like every other
//! sumcheck in this codebase.
//!
//! After the 15 main rounds, the prover holds 12 witness-derived
//! claims at the final point `r' ∈ F^14`:
//!
//! * `s_in_dec(r')`, `s_out_dec(r')`, `state_dec(r')`,
//! * `state(r')` — direct opening of the un-permuted state column,
//! * four lane projections `s_out_lane_dec[j](r')` for `j = 0..3`,
//! * four lane projections `state_lane_dec[j](r')`.
//!
//! Eleven of these (everything except `state(r')`) live on permuted
//! columns and are reduced to claims on the original committed
//! columns by the shift gadget in `spine_shift`. `state(r')` is
//! already a direct opening and goes straight to `batch_eval`.
//!
//! The verifier recomputes the four public schedules `U`, `σ_dec`,
//! `RC_dec`, `M_lane_dec[j]`, and `σ_lane_dec[j]` natively at `r'`
//! using `evaluate_slice` — `O(2^14)` per evaluation (precomputed
//! tables, no FFT). With six public inner products this is ~200K
//! Block128 muls total in the verifier per spine.

use noid_core::hardware::{clmul_gcm, flat_to_tower_u128, square_flat_u128, tower_to_flat_u128};
use noid_core::mle::eq::eq_ind;
use noid_core::mle::evaluate::{evaluate_flat, evaluate_preflat, evaluate_slice};
use noid_core::mle::fold::fold_highest_var_inplace;
use noid_core::packed::pow7::{pow7_block128, pow7_flat_block128};
use noid_core::sumcheck::RoundPolynomial;
use noid_core::transcript::FiatShamir;
use noid_core::{Block128, TowerField};
use noid_poseidon2b::native::permutation::STATE_SIZE;

use crate::spine_mle::N_SPINE_SLOTS;
use crate::spine_mle::{
    SpineUnifiedMle, N_SPINE_ELEM_VARS, N_SPINE_ROUND_VARS, N_SPINE_SLOT_VARS,
    N_SPINE_UNIFIED_CELLS, N_SPINE_UNIFIED_VARS,
};
use crate::spine_shift::{
    build_mds_lane_table_for_live_slots, build_rc_table_for_live_slots,
    build_sigma_table_for_live_slots, build_u_table_for_live_slots, permute_by_dec, project_lane,
    spine_mds_lane_tables_flat, spine_rc_dec_table_flat, spine_sigma_dec_lane_tables_flat,
    spine_sigma_dec_table_flat,
};

// Bit layout: `elem:2 | round:7 | slot:5` (low → high). Slices over
// `r_prime[bit_idx]` follow the same convention as `evaluate_slice`.
const ELEM_LO: usize = 0;
const ELEM_HI: usize = ELEM_LO + N_SPINE_ELEM_VARS;
const ROUND_LO: usize = ELEM_HI;
const ROUND_HI: usize = ROUND_LO + N_SPINE_ROUND_VARS;
const SLOT_LO: usize = ROUND_HI;
const SLOT_HI: usize = SLOT_LO + N_SPINE_SLOT_VARS;

/// Per-variable degree of the round polynomial. C1 contributes
/// `eq:1 · σ:1 · sin^7:7 = 9`; C1' and C2 contribute degree 3 and 4
/// respectively. The cap is therefore 9.
pub const SPINE_UNIFIED_ROUND_DEGREE: usize = 9;

/// Number of witness-derived claims emitted by the main sumcheck.
/// See module docstring for the catalog.
pub const N_UNIFIED_WITNESS_CLAIMS: usize = 12;

/// Output of the main unified sumcheck prover.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpineUnifiedProof {
    /// `N_SPINE_UNIFIED_VARS` round polynomials, each of degree at
    /// most `SPINE_UNIFIED_ROUND_DEGREE`.
    pub round_polys: Vec<RoundPolynomial<Block128>>,
    pub s_in_dec_at_r: Block128,
    pub s_out_dec_at_r: Block128,
    pub state_dec_at_r: Block128,
    pub state_at_r: Block128,
    pub s_out_lane_dec_at_r: [Block128; STATE_SIZE],
    pub state_lane_dec_at_r: [Block128; STATE_SIZE],
}

/// Output of the verifier on a successful run: the verified final
/// point plus the cross-checked witness claims (downstream stages
/// must batch-open against committed columns).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpineUnifiedReduction {
    pub r_prime: Vec<Block128>,
    pub s_in_dec_at_r: Block128,
    pub s_out_dec_at_r: Block128,
    pub state_dec_at_r: Block128,
    pub state_at_r: Block128,
    pub s_out_lane_dec_at_r: [Block128; STATE_SIZE],
    pub state_lane_dec_at_r: [Block128; STATE_SIZE],
    /// Constraint-batching coefficients squeezed by the channel.
    pub beta: Block128,
    pub gamma: Block128,
}

/// Run the unified main sumcheck on a populated `SpineUnifiedMle`.
///
/// Channel side effects:
///   - squeezes `ρ` (length 15) for the eq mask in `U`,
///   - squeezes `β` and `γ` (constraint RLC),
///   - per round absorbs the round-poly evaluations and squeezes one
///     challenge,
///   - absorbs the 12 final witness evaluations.
pub fn prove_spine_unified<T: FiatShamir<Block128>>(
    mle: &SpineUnifiedMle,
    channel: &mut T,
) -> (SpineUnifiedProof, Vec<Block128>) {
    prove_spine_unified_for_live_slots(mle, N_SPINE_SLOTS, channel)
}

/// Live-slot-parameterised variant for AuthGKR (`live_slots = 20`)
/// and any other topology that reuses the unified hypercube.
pub fn prove_spine_unified_for_live_slots<T: FiatShamir<Block128>>(
    mle: &SpineUnifiedMle,
    live_slots: usize,
    channel: &mut T,
) -> (SpineUnifiedProof, Vec<Block128>) {
    assert_eq!(mle.s_in.len(), N_SPINE_UNIFIED_CELLS);
    assert_eq!(mle.s_out.len(), N_SPINE_UNIFIED_CELLS);
    assert_eq!(mle.sigma.len(), N_SPINE_UNIFIED_CELLS);
    assert_eq!(mle.state.len(), N_SPINE_UNIFIED_CELLS);

    let rho: Vec<Block128> = (0..N_SPINE_UNIFIED_VARS)
        .map(|_| channel.squeeze())
        .collect();
    let beta = channel.squeeze();
    let gamma = channel.squeeze();

    // Flat-basis prover hot path.
    //
    // The 23-table bundle is materialised once in tower basis (so the
    // public-schedule constructors stay reusable elsewhere), then
    // hoisted into flat basis for the entire 15-round sumcheck. Each
    // `compute_round_polynomial_flat` call uses `clmul_gcm` and
    // `square_flat_u128` directly; folds run in flat too. Only the
    // round-poly coefficients (absorbed into the channel) and the
    // final witness claims are converted back to tower.
    let tabs = build_unified_tables(mle, &rho, live_slots);
    let mut tabs = UnifiedFlatTables::from_tower(tabs);
    let beta_flat = tower_to_flat_u128(beta.to_u128());
    let gamma_flat = tower_to_flat_u128(gamma.to_u128());

    let mut round_polys = Vec::with_capacity(N_SPINE_UNIFIED_VARS);
    let mut r_prime = vec![Block128::ZERO; N_SPINE_UNIFIED_VARS];

    for round in 0..N_SPINE_UNIFIED_VARS {
        let poly = compute_round_polynomial_flat(&tabs, beta_flat, gamma_flat);
        for &c in &poly.coeffs {
            channel.absorb(c);
        }
        let challenge = channel.squeeze();
        let challenge_flat = tower_to_flat_u128(challenge.to_u128());
        tabs.fold_flat(challenge_flat);
        r_prime[N_SPINE_UNIFIED_VARS - 1 - round] = challenge;
        round_polys.push(poly);
    }

    let final_claims = tabs.final_claims_tower();
    channel.absorb(final_claims.s_in_dec);
    channel.absorb(final_claims.s_out_dec);
    channel.absorb(final_claims.state_dec);
    channel.absorb(final_claims.state);
    for v in &final_claims.s_out_lane_dec {
        channel.absorb(*v);
    }
    for v in &final_claims.state_lane_dec {
        channel.absorb(*v);
    }

    let proof = SpineUnifiedProof {
        round_polys,
        s_in_dec_at_r: final_claims.s_in_dec,
        s_out_dec_at_r: final_claims.s_out_dec,
        state_dec_at_r: final_claims.state_dec,
        state_at_r: final_claims.state,
        s_out_lane_dec_at_r: final_claims.s_out_lane_dec,
        state_lane_dec_at_r: final_claims.state_lane_dec,
    };
    (proof, r_prime)
}

/// Verify a unified main sumcheck proof. Returns the reduction
/// context on success, `None` on rejection.
pub fn verify_spine_unified<T: FiatShamir<Block128>>(
    proof: &SpineUnifiedProof,
    channel: &mut T,
) -> Option<SpineUnifiedReduction> {
    verify_spine_unified_for_live_slots(proof, N_SPINE_SLOTS, channel)
}

/// Live-slot-parameterised variant of `verify_spine_unified`. Must be
/// called with the same `live_slots` value the prover used.
pub fn verify_spine_unified_for_live_slots<T: FiatShamir<Block128>>(
    proof: &SpineUnifiedProof,
    live_slots: usize,
    channel: &mut T,
) -> Option<SpineUnifiedReduction> {
    if proof.round_polys.len() != N_SPINE_UNIFIED_VARS {
        return None;
    }
    for p in &proof.round_polys {
        if p.degree() > SPINE_UNIFIED_ROUND_DEGREE {
            return None;
        }
    }

    let rho: Vec<Block128> = (0..N_SPINE_UNIFIED_VARS)
        .map(|_| channel.squeeze())
        .collect();
    let beta = channel.squeeze();
    let gamma = channel.squeeze();

    // The unified relation must vanish on the cube, so the initial
    // sumcheck claim is zero.
    let mut expected = Block128::ZERO;
    let mut r_prime = vec![Block128::ZERO; N_SPINE_UNIFIED_VARS];

    for (round, poly) in proof.round_polys.iter().enumerate() {
        let s = poly.evaluate(Block128::ZERO) + poly.evaluate(Block128::ONE);
        if s != expected {
            return None;
        }
        for &c in &poly.coeffs {
            channel.absorb(c);
        }
        let challenge = channel.squeeze();
        expected = poly.evaluate(challenge);
        // Sumcheck folds highest-bit-first, so round k pins variable
        // index `(N_VARS - 1 - k)` in the canonical low-bit-first
        // representation.
        r_prime[N_SPINE_UNIFIED_VARS - 1 - round] = challenge;
    }

    // Recompute public schedules at r' natively. Use cached static tables for
    // sigma, RC, and MDS lanes — these are deterministic functions of
    // live_slots only, so they never change across calls in the same process.
    // Only the U mask depends on ρ (a per-proof challenge) and cannot be cached.
    //
    // When live_slots == N_SPINE_SLOTS (production path), we use the `OnceLock`
    // getters from spine_shift. For other values we fall back to building
    // the tables on demand (test / non-standard topologies only).
    let u_at_r = evaluate_flat(&build_u_table_for_live_slots(&rho, live_slots), &r_prime);

    let (sigma_dec_at_r, rc_dec_at_r, mds_lane_dec_at_r, sigma_lane_dec_at_r) =
        if live_slots == N_SPINE_SLOTS {
            // Hot path: use pre-flat tables to skip per-element tower_to_flat conversion.
            let sigma_dec_at_r = evaluate_preflat(spine_sigma_dec_table_flat(), &r_prime);
            let rc_dec_at_r = evaluate_preflat(spine_rc_dec_table_flat(), &r_prime);
            let mut mds_lane = [Block128::ZERO; STATE_SIZE];
            let mut sigma_lane = [Block128::ZERO; STATE_SIZE];
            let mds_tables = spine_mds_lane_tables_flat();
            let sigma_lane_tables = spine_sigma_dec_lane_tables_flat();
            for j in 0..STATE_SIZE {
                mds_lane[j] = evaluate_preflat(&mds_tables[j], &r_prime);
                sigma_lane[j] = evaluate_preflat(&sigma_lane_tables[j], &r_prime);
            }
            (sigma_dec_at_r, rc_dec_at_r, mds_lane, sigma_lane)
        } else {
            // Non-production path: build on demand.
            let sigma_dec_full = permute_by_dec(&build_sigma_table_for_live_slots(live_slots));
            let sigma_dec_at_r = evaluate_flat(&sigma_dec_full, &r_prime);
            let rc_dec_at_r = evaluate_flat(
                &permute_by_dec(&build_rc_table_for_live_slots(live_slots)),
                &r_prime,
            );
            let mut mds_lane = [Block128::ZERO; STATE_SIZE];
            let mut sigma_lane = [Block128::ZERO; STATE_SIZE];
            for j in 0..STATE_SIZE {
                mds_lane[j] = evaluate_flat(
                    &build_mds_lane_table_for_live_slots(j, live_slots),
                    &r_prime,
                );
                sigma_lane[j] = evaluate_flat(&project_lane(&sigma_dec_full, j), &r_prime);
            }
            (sigma_dec_at_r, rc_dec_at_r, mds_lane, sigma_lane)
        };

    // Reassemble the constraint at r' from the prover's claims.
    let q_c1 = sigma_dec_at_r * pow7_block128(proof.s_in_dec_at_r)
        + proof.s_out_dec_at_r
        + proof.s_in_dec_at_r
        + sigma_dec_at_r * proof.s_in_dec_at_r;
    let q_c1p = sigma_dec_at_r * (proof.s_in_dec_at_r + proof.state_dec_at_r + rc_dec_at_r);
    let mut c2_sum = proof.state_at_r;
    for j in 0..STATE_SIZE {
        let pi_j = sigma_lane_dec_at_r[j] * proof.s_out_lane_dec_at_r[j]
            + (Block128::ONE + sigma_lane_dec_at_r[j]) * proof.state_lane_dec_at_r[j];
        c2_sum += mds_lane_dec_at_r[j] * pi_j;
    }
    let q_at_r = q_c1 + beta * q_c1p + gamma * c2_sum;

    if expected != u_at_r * q_at_r {
        return None;
    }

    channel.absorb(proof.s_in_dec_at_r);
    channel.absorb(proof.s_out_dec_at_r);
    channel.absorb(proof.state_dec_at_r);
    channel.absorb(proof.state_at_r);
    for v in &proof.s_out_lane_dec_at_r {
        channel.absorb(*v);
    }
    for v in &proof.state_lane_dec_at_r {
        channel.absorb(*v);
    }

    Some(SpineUnifiedReduction {
        r_prime,
        s_in_dec_at_r: proof.s_in_dec_at_r,
        s_out_dec_at_r: proof.s_out_dec_at_r,
        state_dec_at_r: proof.state_dec_at_r,
        state_at_r: proof.state_at_r,
        s_out_lane_dec_at_r: proof.s_out_lane_dec_at_r,
        state_lane_dec_at_r: proof.state_lane_dec_at_r,
        beta,
        gamma,
    })
}

// ---------------------------------------------------------------------------
// Internal helper-table bundle.
//
// Stores all 23 tables that participate in the round-poly computation,
// owns the high-to-low fold across them in lockstep, and exposes the
// final-claim accessors after the last fold.
// ---------------------------------------------------------------------------

#[derive(Debug)]
struct UnifiedTables {
    // Public schedules (verifier-recomputable).
    u: Vec<Block128>,
    sigma_dec: Vec<Block128>,
    rc_dec: Vec<Block128>,
    mds_lane_dec: [Vec<Block128>; STATE_SIZE],
    sigma_lane_dec: [Vec<Block128>; STATE_SIZE],
    // Witness-derived MLEs (must be opened after the sumcheck).
    s_in_dec: Vec<Block128>,
    s_out_dec: Vec<Block128>,
    state_dec: Vec<Block128>,
    state: Vec<Block128>,
    s_out_lane_dec: [Vec<Block128>; STATE_SIZE],
    state_lane_dec: [Vec<Block128>; STATE_SIZE],
}

struct UnifiedFinalClaims {
    s_in_dec: Block128,
    s_out_dec: Block128,
    state_dec: Block128,
    state: Block128,
    s_out_lane_dec: [Block128; STATE_SIZE],
    state_lane_dec: [Block128; STATE_SIZE],
}

fn build_unified_tables(
    mle: &SpineUnifiedMle,
    rho: &[Block128],
    live_slots: usize,
) -> UnifiedTables {
    let sigma_full = build_sigma_table_for_live_slots(live_slots);
    let sigma_dec = permute_by_dec(&sigma_full);
    let rc_dec = permute_by_dec(&build_rc_table_for_live_slots(live_slots));
    let s_in_dec = permute_by_dec(&mle.s_in);
    let s_out_dec = permute_by_dec(&mle.s_out);
    let state_dec = permute_by_dec(&mle.state);

    let mds_lane_dec: [Vec<Block128>; STATE_SIZE] =
        std::array::from_fn(|j| build_mds_lane_table_for_live_slots(j, live_slots));
    let sigma_lane_dec: [Vec<Block128>; STATE_SIZE] =
        std::array::from_fn(|j| project_lane(&sigma_dec, j));
    let s_out_lane_dec: [Vec<Block128>; STATE_SIZE] =
        std::array::from_fn(|j| project_lane(&s_out_dec, j));
    let state_lane_dec: [Vec<Block128>; STATE_SIZE] =
        std::array::from_fn(|j| project_lane(&state_dec, j));

    UnifiedTables {
        u: build_u_table_for_live_slots(rho, live_slots),
        sigma_dec,
        rc_dec,
        mds_lane_dec,
        sigma_lane_dec,
        s_in_dec,
        s_out_dec,
        state_dec,
        state: mle.state.clone(),
        s_out_lane_dec,
        state_lane_dec,
    }
}

impl UnifiedTables {
    #[allow(dead_code)]
    fn fold(&mut self, r: Block128) {
        fold_highest_var_inplace(&mut self.u, r);
        fold_highest_var_inplace(&mut self.sigma_dec, r);
        fold_highest_var_inplace(&mut self.rc_dec, r);
        fold_highest_var_inplace(&mut self.s_in_dec, r);
        fold_highest_var_inplace(&mut self.s_out_dec, r);
        fold_highest_var_inplace(&mut self.state_dec, r);
        fold_highest_var_inplace(&mut self.state, r);
        for j in 0..STATE_SIZE {
            fold_highest_var_inplace(&mut self.mds_lane_dec[j], r);
            fold_highest_var_inplace(&mut self.sigma_lane_dec[j], r);
            fold_highest_var_inplace(&mut self.s_out_lane_dec[j], r);
            fold_highest_var_inplace(&mut self.state_lane_dec[j], r);
        }
    }

    #[allow(dead_code)]
    fn final_claims(&self) -> UnifiedFinalClaims {
        debug_assert_eq!(self.u.len(), 1);
        UnifiedFinalClaims {
            s_in_dec: self.s_in_dec[0],
            s_out_dec: self.s_out_dec[0],
            state_dec: self.state_dec[0],
            state: self.state[0],
            s_out_lane_dec: std::array::from_fn(|j| self.s_out_lane_dec[j][0]),
            state_lane_dec: std::array::from_fn(|j| self.state_lane_dec[j][0]),
        }
    }
}

// ---------------------------------------------------------------------------
// Round-polynomial evaluator.
//
// The constraint is
//   F(y) = U(y) · [ Q1(y) + β · Q1'(y) + γ · Q2(y) ]
// where
//   Q1  = σ_dec·s_in_dec^7 + s_out_dec + s_in_dec + σ_dec·s_in_dec
//   Q1' = σ_dec · (s_in_dec + state_dec + RC_dec)
//   Q2  = state(y) + Σ_j  M_lane_dec[j]·π_lane_dec[j]
//   π_lane_dec[j] = σ_lane_dec[j]·s_out_lane_dec[j]
//                 + (1+σ_lane_dec[j])·state_lane_dec[j]
//
// Per-variable degree caps: 1+1+7 = 9 (Q1), 1+1+1 = 3 (Q1'), 1+1+1+1 = 4
// (Q2 with the lane-π subterm). With the leading `U` factor (deg 1)
// the round poly is degree ≤ 9 with 10 evaluation points.
// ---------------------------------------------------------------------------

/// Tower-basis parity implementation of the round polynomial. The
/// prover hot path now goes through `compute_round_polynomial_flat`
/// (flat-basis hot path); this version is kept only as a parity oracle for the
/// `flat_round_poly_matches_tower_round_poly` unit test below.
#[allow(dead_code)]
fn compute_round_polynomial(
    tabs: &UnifiedTables,
    beta: Block128,
    gamma: Block128,
) -> RoundPolynomial<Block128> {
    let half = tabs.u.len() / 2;
    let mut evals = [Block128::ZERO; SPINE_UNIFIED_ROUND_DEGREE + 1];

    for i in 0..half {
        // Capture (lo, hi) pairs for every folded table.
        let (u0, u1) = (tabs.u[i], tabs.u[i + half]);
        let (sg0, sg1) = (tabs.sigma_dec[i], tabs.sigma_dec[i + half]);
        let (rc0, rc1) = (tabs.rc_dec[i], tabs.rc_dec[i + half]);
        let (si0, si1) = (tabs.s_in_dec[i], tabs.s_in_dec[i + half]);
        let (so0, so1) = (tabs.s_out_dec[i], tabs.s_out_dec[i + half]);
        let (st0, st1) = (tabs.state_dec[i], tabs.state_dec[i + half]);
        let (stmain0, stmain1) = (tabs.state[i], tabs.state[i + half]);
        let mut mds0 = [Block128::ZERO; STATE_SIZE];
        let mut mds1 = [Block128::ZERO; STATE_SIZE];
        let mut sgl0 = [Block128::ZERO; STATE_SIZE];
        let mut sgl1 = [Block128::ZERO; STATE_SIZE];
        let mut sol0 = [Block128::ZERO; STATE_SIZE];
        let mut sol1 = [Block128::ZERO; STATE_SIZE];
        let mut stl0 = [Block128::ZERO; STATE_SIZE];
        let mut stl1 = [Block128::ZERO; STATE_SIZE];
        for j in 0..STATE_SIZE {
            mds0[j] = tabs.mds_lane_dec[j][i];
            mds1[j] = tabs.mds_lane_dec[j][i + half];
            sgl0[j] = tabs.sigma_lane_dec[j][i];
            sgl1[j] = tabs.sigma_lane_dec[j][i + half];
            sol0[j] = tabs.s_out_lane_dec[j][i];
            sol1[j] = tabs.s_out_lane_dec[j][i + half];
            stl0[j] = tabs.state_lane_dec[j][i];
            stl1[j] = tabs.state_lane_dec[j][i + half];
        }

        // Linear interpolants in the round variable t.
        let ud = u0 + u1;
        let sgd = sg0 + sg1;
        let rcd = rc0 + rc1;
        let sid = si0 + si1;
        let sod = so0 + so1;
        let std = st0 + st1;
        let stmd = stmain0 + stmain1;

        for (k, slot) in evals.iter_mut().enumerate() {
            let t = Block128::from(k as u8);
            let u = u0 + t * ud;
            let sg = sg0 + t * sgd;
            let rc = rc0 + t * rcd;
            let si = si0 + t * sid;
            let so = so0 + t * sod;
            let st_dec = st0 + t * std;
            let st_main = stmain0 + t * stmd;

            // Q1
            let q1 = sg * pow7_block128(si) + so + si + sg * si;
            // Q1'
            let q1p = sg * (si + st_dec + rc);
            // Q2
            let mut q2 = st_main;
            for j in 0..STATE_SIZE {
                let m = mds0[j] + t * (mds0[j] + mds1[j]);
                let sgl = sgl0[j] + t * (sgl0[j] + sgl1[j]);
                let sol = sol0[j] + t * (sol0[j] + sol1[j]);
                let stl = stl0[j] + t * (stl0[j] + stl1[j]);
                let pi_j = sgl * sol + (Block128::ONE + sgl) * stl;
                q2 += m * pi_j;
            }
            let q = q1 + beta * q1p + gamma * q2;
            *slot += u * q;
        }
    }

    RoundPolynomial::from_evals(&evals)
}

// ---------------------------------------------------------------------------
// Flat-basis prover hot path.
//
// The 23-table bundle is materialised once in tower basis (so the
// public-schedule constructors keep reusable elsewhere), then hoisted
// into flat basis for the entire 15-round sumcheck. Multiplications
// inside `compute_round_polynomial_flat` go through `clmul_gcm`, the
// `pow7` factor through `pow7_flat_block128`, squarings through
// `square_flat_u128`. Folding stays flat too: the challenge is
// converted to flat once per round and then `r * delta` uses
// `clmul_gcm`. Only the round-poly coefficients (absorbed by the
// channel) and the 12 final witness claims are converted back to
// tower at the boundary.
// ---------------------------------------------------------------------------

#[derive(Debug)]
struct UnifiedFlatTables {
    u: Vec<u128>,
    sigma_dec: Vec<u128>,
    rc_dec: Vec<u128>,
    mds_lane_dec: [Vec<u128>; STATE_SIZE],
    sigma_lane_dec: [Vec<u128>; STATE_SIZE],
    s_in_dec: Vec<u128>,
    s_out_dec: Vec<u128>,
    state_dec: Vec<u128>,
    state: Vec<u128>,
    s_out_lane_dec: [Vec<u128>; STATE_SIZE],
    state_lane_dec: [Vec<u128>; STATE_SIZE],
}

#[inline]
fn vec_tower_to_flat(v: Vec<Block128>) -> Vec<u128> {
    v.into_iter()
        .map(|b| tower_to_flat_u128(b.to_u128()))
        .collect()
}

impl UnifiedFlatTables {
    fn from_tower(t: UnifiedTables) -> Self {
        UnifiedFlatTables {
            u: vec_tower_to_flat(t.u),
            sigma_dec: vec_tower_to_flat(t.sigma_dec),
            rc_dec: vec_tower_to_flat(t.rc_dec),
            mds_lane_dec: t.mds_lane_dec.map(vec_tower_to_flat),
            sigma_lane_dec: t.sigma_lane_dec.map(vec_tower_to_flat),
            s_in_dec: vec_tower_to_flat(t.s_in_dec),
            s_out_dec: vec_tower_to_flat(t.s_out_dec),
            state_dec: vec_tower_to_flat(t.state_dec),
            state: vec_tower_to_flat(t.state),
            s_out_lane_dec: t.s_out_lane_dec.map(vec_tower_to_flat),
            state_lane_dec: t.state_lane_dec.map(vec_tower_to_flat),
        }
    }

    fn fold_flat(&mut self, r_flat: u128) {
        fold_highest_var_inplace_flat(&mut self.u, r_flat);
        fold_highest_var_inplace_flat(&mut self.sigma_dec, r_flat);
        fold_highest_var_inplace_flat(&mut self.rc_dec, r_flat);
        fold_highest_var_inplace_flat(&mut self.s_in_dec, r_flat);
        fold_highest_var_inplace_flat(&mut self.s_out_dec, r_flat);
        fold_highest_var_inplace_flat(&mut self.state_dec, r_flat);
        fold_highest_var_inplace_flat(&mut self.state, r_flat);
        for j in 0..STATE_SIZE {
            fold_highest_var_inplace_flat(&mut self.mds_lane_dec[j], r_flat);
            fold_highest_var_inplace_flat(&mut self.sigma_lane_dec[j], r_flat);
            fold_highest_var_inplace_flat(&mut self.s_out_lane_dec[j], r_flat);
            fold_highest_var_inplace_flat(&mut self.state_lane_dec[j], r_flat);
        }
    }

    fn final_claims_tower(&self) -> UnifiedFinalClaims {
        debug_assert_eq!(self.u.len(), 1);
        let f = |x: u128| Block128::from(flat_to_tower_u128(x));
        UnifiedFinalClaims {
            s_in_dec: f(self.s_in_dec[0]),
            s_out_dec: f(self.s_out_dec[0]),
            state_dec: f(self.state_dec[0]),
            state: f(self.state[0]),
            s_out_lane_dec: std::array::from_fn(|j| f(self.s_out_lane_dec[j][0])),
            state_lane_dec: std::array::from_fn(|j| f(self.state_lane_dec[j][0])),
        }
    }
}

#[inline(always)]
fn fold_highest_var_inplace_flat(evals: &mut Vec<u128>, r_flat: u128) {
    let half = evals.len() / 2;
    debug_assert!(half > 0);
    for j in 0..half {
        let delta = evals[j] ^ evals[j + half];
        evals[j] ^= clmul_gcm(r_flat, delta);
    }
    evals.truncate(half);
}

/// Flat-basis representation of the field elements `0,1,2,...,9`. The
/// sumcheck round polynomial is interpolated through these 10 points
/// (as **tower-basis** Block128 in `RoundPolynomial::from_evals` /
/// `evaluate`), so the prover must evaluate at the same field
/// elements expressed in flat basis. Because basis change is linear,
/// `T_FLAT[k] = tower_to_flat_u128(k as u128)`.
fn t_flat_table() -> [u128; SPINE_UNIFIED_ROUND_DEGREE + 1] {
    std::array::from_fn(|k| tower_to_flat_u128(k as u128))
}

/// Per-evaluation-point flat-basis prover (baseline).
///
/// Kept as a parity oracle for the monomial-form prover
/// `compute_round_polynomial_flat` (monomial form). Production callers
/// go through the monomial form.
#[allow(dead_code)]
fn compute_round_polynomial_flat_per_eval(
    tabs: &UnifiedFlatTables,
    beta_flat: u128,
    gamma_flat: u128,
) -> RoundPolynomial<Block128> {
    let half = tabs.u.len() / 2;
    let mut evals = [0u128; SPINE_UNIFIED_ROUND_DEGREE + 1];
    let t_flat = t_flat_table();
    // Field "1" has the same u128 encoding (1) in both bases. XOR is
    // basis-invariant.
    const ONE_FLAT: u128 = 1u128;

    for i in 0..half {
        let (u0, u1) = (tabs.u[i], tabs.u[i + half]);
        let (sg0, sg1) = (tabs.sigma_dec[i], tabs.sigma_dec[i + half]);
        let (rc0, rc1) = (tabs.rc_dec[i], tabs.rc_dec[i + half]);
        let (si0, si1) = (tabs.s_in_dec[i], tabs.s_in_dec[i + half]);
        let (so0, so1) = (tabs.s_out_dec[i], tabs.s_out_dec[i + half]);
        let (st0, st1) = (tabs.state_dec[i], tabs.state_dec[i + half]);
        let (stmain0, stmain1) = (tabs.state[i], tabs.state[i + half]);

        let mut mds0 = [0u128; STATE_SIZE];
        let mut mds1 = [0u128; STATE_SIZE];
        let mut sgl0 = [0u128; STATE_SIZE];
        let mut sgl1 = [0u128; STATE_SIZE];
        let mut sol0 = [0u128; STATE_SIZE];
        let mut sol1 = [0u128; STATE_SIZE];
        let mut stl0 = [0u128; STATE_SIZE];
        let mut stl1 = [0u128; STATE_SIZE];
        for j in 0..STATE_SIZE {
            mds0[j] = tabs.mds_lane_dec[j][i];
            mds1[j] = tabs.mds_lane_dec[j][i + half];
            sgl0[j] = tabs.sigma_lane_dec[j][i];
            sgl1[j] = tabs.sigma_lane_dec[j][i + half];
            sol0[j] = tabs.s_out_lane_dec[j][i];
            sol1[j] = tabs.s_out_lane_dec[j][i + half];
            stl0[j] = tabs.state_lane_dec[j][i];
            stl1[j] = tabs.state_lane_dec[j][i + half];
        }

        // XOR-deltas (basis-invariant).
        let ud = u0 ^ u1;
        let sgd = sg0 ^ sg1;
        let rcd = rc0 ^ rc1;
        let sid = si0 ^ si1;
        let sod = so0 ^ so1;
        let std = st0 ^ st1;
        let stmd = stmain0 ^ stmain1;
        let mut mdsd = [0u128; STATE_SIZE];
        let mut sgld = [0u128; STATE_SIZE];
        let mut sold = [0u128; STATE_SIZE];
        let mut stld = [0u128; STATE_SIZE];
        for j in 0..STATE_SIZE {
            mdsd[j] = mds0[j] ^ mds1[j];
            sgld[j] = sgl0[j] ^ sgl1[j];
            sold[j] = sol0[j] ^ sol1[j];
            stld[j] = stl0[j] ^ stl1[j];
        }

        for k in 0..=SPINE_UNIFIED_ROUND_DEGREE {
            let t = t_flat[k];
            let u = u0 ^ clmul_gcm(t, ud);
            let sg = sg0 ^ clmul_gcm(t, sgd);
            let rc = rc0 ^ clmul_gcm(t, rcd);
            let si = si0 ^ clmul_gcm(t, sid);
            let so = so0 ^ clmul_gcm(t, sod);
            let st_dec = st0 ^ clmul_gcm(t, std);
            let st_main = stmain0 ^ clmul_gcm(t, stmd);

            // Q1 = σ·s_in^7 + s_out + s_in + σ·s_in
            let si7 = pow7_flat_block128(si);
            let sg_si = clmul_gcm(sg, si);
            let q1 = clmul_gcm(sg, si7) ^ so ^ si ^ sg_si;
            // Q1' = σ · (s_in + state_dec + RC)
            let q1p = clmul_gcm(sg, si ^ st_dec ^ rc);
            // Q2 = state + Σ_j M_j · π_j ; π_j = σ_j·s_out_j + (1+σ_j)·state_j
            let mut q2 = st_main;
            for j in 0..STATE_SIZE {
                let m = mds0[j] ^ clmul_gcm(t, mdsd[j]);
                let sgl = sgl0[j] ^ clmul_gcm(t, sgld[j]);
                let sol = sol0[j] ^ clmul_gcm(t, sold[j]);
                let stl = stl0[j] ^ clmul_gcm(t, stld[j]);
                let pi_j = clmul_gcm(sgl, sol) ^ clmul_gcm(ONE_FLAT ^ sgl, stl);
                q2 ^= clmul_gcm(m, pi_j);
            }
            let q = q1 ^ clmul_gcm(beta_flat, q1p) ^ clmul_gcm(gamma_flat, q2);
            evals[k] ^= clmul_gcm(u, q);
        }
    }

    let evals_tower: [Block128; SPINE_UNIFIED_ROUND_DEGREE + 1] =
        std::array::from_fn(|k| Block128::from(flat_to_tower_u128(evals[k])));
    RoundPolynomial::from_evals(&evals_tower)
}

// ---------------------------------------------------------------------------
// Monomial-form prover (Lagrange/DP amortisation).
//
// Reformulation. Inside one cell, every witness factor is affine in
// the round variable `t`: `x(t) = x0 + t · dx`. So the round-poly
// integrand
//
//     F_i(t) = u(t) · ( Q1(t) + β · Q1'(t) + γ · Q2(t) )
//
// is a polynomial in `t` of degree ≤ 9 with 10 monomial coefficients.
// We build those coefficients **once per cell** (using flat-basis
// `clmul_gcm` for the polynomial-in-t convolutions) and accumulate
// them XOR-wise into a global degree-9 vector. The final
// `RoundPolynomial::from_coeffs` is a no-op constructor — no Lagrange
// interpolation is needed.
//
// Cost per cell. The dominant work is the 32-lane `Q2` build: each
// lane contributes a deg-3 polynomial (`m_j · π_j` where `π_j` is
// itself deg-2), so ≈ 14 muls per lane × 32 lanes = 448 muls. Plus
// ≈ 70 muls for `Q1` (including the deg-7 build of `(s_in)^7` via
// the binomial-2 expansion `(a+tb)^7 = Σ a^j b^{7-j} · t^j`, valid
// because `binomial(7,j) ≡ 1 (mod 2)` for all `j ∈ [0,7]`). Plus 18
// muls for the final deg-1 × deg-8 multiplication by `u(t)`.
//
// Comparison vs. 1.5.8.A baseline (`_per_eval`): the per-cell budget
// drops from ~850 → ~520 GF(2^128) muls, plus a much smaller working
// set (no 10× re-walk of `mds0/sgl0/sol0/stl0` arrays per cell), so
// cache traffic improves substantially.
// ---------------------------------------------------------------------------

/// Polynomial multiply over GF(2^128) on a *formal* indeterminate `t`,
/// using `clmul_gcm` for the field coefficient products. Result has
/// length `a.len() + b.len() - 1` polynomial coefficients in `t`.
#[inline(always)]
fn poly_mul_t<const NA: usize, const NB: usize, const NR: usize>(
    a: &[u128; NA],
    b: &[u128; NB],
) -> [u128; NR] {
    debug_assert_eq!(NR, NA + NB - 1);
    let mut out = [0u128; NR];
    for i in 0..NA {
        for j in 0..NB {
            out[i + j] ^= clmul_gcm(a[i], b[j]);
        }
    }
    out
}

/// Scalar-multiply every `t`-coefficient by `s` (flat-basis).
#[inline(always)]
fn poly_scalar_mul_t<const N: usize>(p: &[u128; N], s: u128) -> [u128; N] {
    let mut out = [0u128; N];
    for k in 0..N {
        out[k] = clmul_gcm(s, p[k]);
    }
    out
}

/// Build the eight monomial coefficients of `(a + t·b)^7` over
/// GF(2^128). Valid in characteristic-2 because `binomial(7, j) mod
/// 2 = 1` for every `j ∈ [0,7]` (7 = 0b111, all bits set, so
/// Lucas' theorem gives 1).
#[inline(always)]
fn pow7_poly_t(a: u128, b: u128) -> [u128; 8] {
    // Powers of a: a^1..a^7. Powers of b: b^1..b^7.
    let a2 = square_flat_u128(a);
    let a3 = clmul_gcm(a2, a);
    let a4 = square_flat_u128(a2);
    let a5 = clmul_gcm(a4, a);
    let a6 = clmul_gcm(a4, a2);
    let a7 = clmul_gcm(a4, a3);

    let b2 = square_flat_u128(b);
    let b3 = clmul_gcm(b2, b);
    let b4 = square_flat_u128(b2);
    let b5 = clmul_gcm(b4, b);
    let b6 = clmul_gcm(b4, b2);
    let b7 = clmul_gcm(b4, b3);

    [
        a7,                // t^0
        clmul_gcm(a6, b),  // t^1
        clmul_gcm(a5, b2), // t^2
        clmul_gcm(a4, b3), // t^3
        clmul_gcm(a3, b4), // t^4
        clmul_gcm(a2, b5), // t^5
        clmul_gcm(a, b6),  // t^6
        b7,                // t^7
    ]
}

fn compute_round_polynomial_flat(
    tabs: &UnifiedFlatTables,
    beta_flat: u128,
    gamma_flat: u128,
) -> RoundPolynomial<Block128> {
    let half = tabs.u.len() / 2;
    let mut acc = [0u128; SPINE_UNIFIED_ROUND_DEGREE + 1]; // 10 coeffs in t
    const ONE_FLAT: u128 = 1u128;

    for i in 0..half {
        // Pull (lo, hi) → (c0, c1=delta) per affine factor.
        let u_p: [u128; 2] = [tabs.u[i], tabs.u[i] ^ tabs.u[i + half]];
        let sg_p: [u128; 2] = [
            tabs.sigma_dec[i],
            tabs.sigma_dec[i] ^ tabs.sigma_dec[i + half],
        ];
        let rc_p: [u128; 2] = [tabs.rc_dec[i], tabs.rc_dec[i] ^ tabs.rc_dec[i + half]];
        let si_p: [u128; 2] = [tabs.s_in_dec[i], tabs.s_in_dec[i] ^ tabs.s_in_dec[i + half]];
        let so_p: [u128; 2] = [
            tabs.s_out_dec[i],
            tabs.s_out_dec[i] ^ tabs.s_out_dec[i + half],
        ];
        let st_p: [u128; 2] = [
            tabs.state_dec[i],
            tabs.state_dec[i] ^ tabs.state_dec[i + half],
        ];
        let stmain_p: [u128; 2] = [tabs.state[i], tabs.state[i] ^ tabs.state[i + half]];

        // === Q1(t) = sg(t) · si(t)^7  +  so(t) + si(t) + sg(t) · si(t) ===
        // si(t)^7 as deg-7 poly in t (8 coeffs).
        let si7_p: [u128; 8] = pow7_poly_t(si_p[0], si_p[1]);
        // sg · si^7 → deg-8, 9 coeffs.
        let sg_si7_p: [u128; 9] = poly_mul_t::<2, 8, 9>(&sg_p, &si7_p);
        // sg · si → deg-2, 3 coeffs.
        let sg_si_p: [u128; 3] = poly_mul_t::<2, 2, 3>(&sg_p, &si_p);
        // Q1: 9 coeffs (deg-8).
        let mut q1_p = [0u128; 9];
        q1_p.copy_from_slice(&sg_si7_p);
        // Add (so + si) at degrees 0..1, sg·si at degrees 0..2 (XOR).
        q1_p[0] ^= so_p[0] ^ si_p[0] ^ sg_si_p[0];
        q1_p[1] ^= so_p[1] ^ si_p[1] ^ sg_si_p[1];
        q1_p[2] ^= sg_si_p[2];

        // === Q1'(t) = sg(t) · ( si(t) + st_dec(t) + rc(t) ) → deg-2 ===
        let inner_p: [u128; 2] = [si_p[0] ^ st_p[0] ^ rc_p[0], si_p[1] ^ st_p[1] ^ rc_p[1]];
        let q1p_p: [u128; 3] = poly_mul_t::<2, 2, 3>(&sg_p, &inner_p);

        // === Q2(t) = st_main(t) + Σ_j m_j(t) · π_j(t)  → deg-3 ===
        //
        // Per lane: π_j(t) = sgl_j(t)·sol_j(t) + (1 + sgl_j(t))·stl_j(t)
        //   both summands deg-2, result deg-2.
        // Then m_j(t) · π_j(t) is deg-1 × deg-2 = deg-3.
        let mut q2_p = [0u128; 4];
        // st_main contributes at degrees 0..1.
        q2_p[0] ^= stmain_p[0];
        q2_p[1] ^= stmain_p[1];
        for j in 0..STATE_SIZE {
            let m_p: [u128; 2] = [
                tabs.mds_lane_dec[j][i],
                tabs.mds_lane_dec[j][i] ^ tabs.mds_lane_dec[j][i + half],
            ];
            let sgl_p: [u128; 2] = [
                tabs.sigma_lane_dec[j][i],
                tabs.sigma_lane_dec[j][i] ^ tabs.sigma_lane_dec[j][i + half],
            ];
            let sol_p: [u128; 2] = [
                tabs.s_out_lane_dec[j][i],
                tabs.s_out_lane_dec[j][i] ^ tabs.s_out_lane_dec[j][i + half],
            ];
            let stl_p: [u128; 2] = [
                tabs.state_lane_dec[j][i],
                tabs.state_lane_dec[j][i] ^ tabs.state_lane_dec[j][i + half],
            ];
            // 1 + sgl_j(t): only the constant-in-t coefficient flips by 1.
            let one_plus_sgl_p: [u128; 2] = [ONE_FLAT ^ sgl_p[0], sgl_p[1]];

            let sgl_sol_p: [u128; 3] = poly_mul_t::<2, 2, 3>(&sgl_p, &sol_p);
            let onep_stl_p: [u128; 3] = poly_mul_t::<2, 2, 3>(&one_plus_sgl_p, &stl_p);
            let pi_p: [u128; 3] = [
                sgl_sol_p[0] ^ onep_stl_p[0],
                sgl_sol_p[1] ^ onep_stl_p[1],
                sgl_sol_p[2] ^ onep_stl_p[2],
            ];
            let m_pi_p: [u128; 4] = poly_mul_t::<2, 3, 4>(&m_p, &pi_p);
            for k in 0..4 {
                q2_p[k] ^= m_pi_p[k];
            }
        }

        // === q(t) = Q1(t) + β · Q1'(t) + γ · Q2(t)  → deg-8, 9 coeffs ===
        let beta_q1p_p: [u128; 3] = poly_scalar_mul_t::<3>(&q1p_p, beta_flat);
        let gamma_q2_p: [u128; 4] = poly_scalar_mul_t::<4>(&q2_p, gamma_flat);
        let mut q_p = [0u128; 9];
        q_p.copy_from_slice(&q1_p);
        for k in 0..3 {
            q_p[k] ^= beta_q1p_p[k];
        }
        for k in 0..4 {
            q_p[k] ^= gamma_q2_p[k];
        }

        // === F_i(t) = u(t) · q(t)  → deg-9, 10 coeffs ===
        let f_p: [u128; 10] = poly_mul_t::<2, 9, 10>(&u_p, &q_p);
        for k in 0..=SPINE_UNIFIED_ROUND_DEGREE {
            acc[k] ^= f_p[k];
        }
    }

    // Lift the 10 monomial coefficients back to tower basis.
    let coeffs_tower: Vec<Block128> = acc
        .iter()
        .map(|&c| Block128::from(flat_to_tower_u128(c)))
        .collect();
    RoundPolynomial::from_coeffs(coeffs_tower)
}

// ===========================================================================
// Shift Gadget.
//
// Reduces the eleven `_dec` / `_lane_dec` claims emitted by the main
// sumcheck to three claims on the *original* committed columns
// `s_in`, `s_out`, `state` at one common point `r''`. The twelfth
// claim (`state(r')`) is already a direct opening of `state` and is
// passed through.
//
// The gadget is a single batched product-sumcheck of degree 2 over
// `N_SPINE_UNIFIED_VARS = 14` rounds. Eleven witness claims share the
// shape `Σ_x w_k(r', x) · T_k(x) = c_k` with public weights `w_k`:
//
//   k=0: T = s_in,         w(x) = eq(r', inc(x))                          (s_in_dec)
//   k=1: T = s_out,        w(x) = eq(r', inc(x))                          (s_out_dec)
//   k=2: T = state,        w(x) = eq(r', inc(x))                          (state_dec)
//   k=3..6:  T = s_out,    w(x) = eq_slot · eq_round_inc · 1[elem(x)==j]  (s_out_lane_dec[j])
//   k=7..10: T = state,    w(x) = eq_slot · eq_round_inc · 1[elem(x)==j]  (state_lane_dec[j])
//
// where `eq_slot   = eq(r'_slot,  slot(x))`, `eq_round_inc = eq(r'_round, round_inc(x))`.
// (`round_inc` here is `round(inc(x)) = (round(x) + 1) mod 128`.)
//
// The verifier randomises with `δ = channel.squeeze()` and the prover
// runs one product-sumcheck of degree 2 over the polynomial
//   F(x) = W_sin(x)·s_in(x) + W_sout(x)·s_out(x) + W_state(x)·state(x)
// with combined weights
//   W_sin   = δ⁰ · w_dec
//   W_sout  = δ¹ · w_dec + Σ_{j} δ^{3+j} · w_lane[j]
//   W_state = δ² · w_dec + Σ_{j} δ^{7+j} · w_lane[j]
// targeting the combined sum
//   C = δ⁰·c_s_in_dec + δ¹·c_s_out_dec + δ²·c_state_dec
//     + Σ_{j} δ^{3+j}·c_s_out_lane[j] + Σ_{j} δ^{7+j}·c_state_lane[j].
//
// After 14 rounds the verifier learns one final point `r'' ∈ F^14`
// and three claimed evaluations `s_in(r'')`, `s_out(r'')`,
// `state(r'')`. It checks the final-round-poly value matches
//   W_sin(r'')·v_sin + W_sout(r'')·v_sout + W_state(r'')·v_state
// where `W_*(r'')` is recomputed natively in O(N_VARS) muls (no
// 32K-table inner products needed): the weights factorise as products
// of `eq` along the variable axes.
// ===========================================================================

/// Per-variable degree of the shift-gadget round polynomial.
pub const SPINE_SHIFT_ROUND_DEGREE: usize = 2;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpineShiftProof {
    pub round_polys: Vec<RoundPolynomial<Block128>>,
    pub s_in_at_r2: Block128,
    pub s_out_at_r2: Block128,
    pub state_at_r2: Block128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpineShiftReduction {
    pub r_double_prime: Vec<Block128>,
    pub s_in_at_r2: Block128,
    pub s_out_at_r2: Block128,
    pub state_at_r2: Block128,
}

/// Combined output of `prove_spine_unified` + shift gadget. The
/// `state(r')` claim is carried verbatim — it is a direct opening of
/// the un-permuted state column at the main sumcheck's challenge
/// point and will be batch-opened alongside the three `_at_r2`
/// claims.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpineKillShotProof {
    pub main: SpineUnifiedProof,
    pub shift: SpineShiftProof,
}

/// Run the shift gadget on the eleven `_dec` claims of an already
/// constructed `SpineUnifiedProof`. The MLE is required because the
/// gadget folds the original `s_in`, `s_out`, `state` columns.
///
/// Channel: squeezes `δ`, then absorbs round polys and squeezes
/// challenges per round, finally absorbs the three `_at_r2` claims.
pub fn prove_spine_shift<T: FiatShamir<Block128>>(
    mle: &SpineUnifiedMle,
    main_red_r_prime: &[Block128],
    channel: &mut T,
) -> (SpineShiftProof, Vec<Block128>) {
    assert_eq!(main_red_r_prime.len(), N_SPINE_UNIFIED_VARS);
    let delta = channel.squeeze();

    let weights = build_combined_weights(main_red_r_prime, delta);

    // Eleven `_dec*` claims (the verifier-side combined target value
    // is checked by the sumcheck against the round-poly sums).
    // The prover does NOT need to assert it explicitly — the
    // sumcheck protocol will reject if the prover lies about C.

    // Flat-basis prover hot path for the shift gadget.
    // Same shape as the main sumcheck — convert the six tables to flat
    // basis once, run all 15 folds + round-poly computes in flat, lift
    // back to tower at the boundary.
    let mut s_in = vec_tower_to_flat(mle.s_in.clone());
    let mut s_out = vec_tower_to_flat(mle.s_out.clone());
    let mut state = vec_tower_to_flat(mle.state.clone());
    let mut w_sin = vec_tower_to_flat(weights.w_sin);
    let mut w_sout = vec_tower_to_flat(weights.w_sout);
    let mut w_state = vec_tower_to_flat(weights.w_state);

    let mut round_polys = Vec::with_capacity(N_SPINE_UNIFIED_VARS);
    let mut r_double_prime = vec![Block128::ZERO; N_SPINE_UNIFIED_VARS];
    for round in 0..N_SPINE_UNIFIED_VARS {
        let poly =
            compute_shift_round_polynomial_flat(&s_in, &s_out, &state, &w_sin, &w_sout, &w_state);
        for &c in &poly.coeffs {
            channel.absorb(c);
        }
        let r = channel.squeeze();
        let r_flat = tower_to_flat_u128(r.to_u128());
        fold_highest_var_inplace_flat(&mut s_in, r_flat);
        fold_highest_var_inplace_flat(&mut s_out, r_flat);
        fold_highest_var_inplace_flat(&mut state, r_flat);
        fold_highest_var_inplace_flat(&mut w_sin, r_flat);
        fold_highest_var_inplace_flat(&mut w_sout, r_flat);
        fold_highest_var_inplace_flat(&mut w_state, r_flat);
        r_double_prime[N_SPINE_UNIFIED_VARS - 1 - round] = r;
        round_polys.push(poly);
    }

    let s_in_at_r2 = Block128::from(flat_to_tower_u128(s_in[0]));
    let s_out_at_r2 = Block128::from(flat_to_tower_u128(s_out[0]));
    let state_at_r2 = Block128::from(flat_to_tower_u128(state[0]));
    channel.absorb(s_in_at_r2);
    channel.absorb(s_out_at_r2);
    channel.absorb(state_at_r2);

    (
        SpineShiftProof {
            round_polys,
            s_in_at_r2,
            s_out_at_r2,
            state_at_r2,
        },
        r_double_prime,
    )
}

/// Verify the shift gadget against the main reduction. Returns the
/// reduction context on success.
pub fn verify_spine_shift<T: FiatShamir<Block128>>(
    proof: &SpineShiftProof,
    main_red: &SpineUnifiedReduction,
    channel: &mut T,
) -> Option<SpineShiftReduction> {
    if proof.round_polys.len() != N_SPINE_UNIFIED_VARS {
        return None;
    }
    for p in &proof.round_polys {
        if p.degree() > SPINE_SHIFT_ROUND_DEGREE {
            return None;
        }
    }
    let delta = channel.squeeze();
    let target = combined_target(main_red, delta);

    let mut expected = target;
    let mut r_double_prime = vec![Block128::ZERO; N_SPINE_UNIFIED_VARS];
    for (round, poly) in proof.round_polys.iter().enumerate() {
        let s = poly.evaluate(Block128::ZERO) + poly.evaluate(Block128::ONE);
        if s != expected {
            return None;
        }
        for &c in &poly.coeffs {
            channel.absorb(c);
        }
        let r = channel.squeeze();
        expected = poly.evaluate(r);
        r_double_prime[N_SPINE_UNIFIED_VARS - 1 - round] = r;
    }

    // Recompute the combined weights at r'' natively. No 32K-cell
    // inner products: each weight factorises along (slot, round, elem)
    // axes via `eq`.
    let w = combined_weights_at_point(&main_red.r_prime, delta, &r_double_prime);
    let claimed =
        w.w_sin * proof.s_in_at_r2 + w.w_sout * proof.s_out_at_r2 + w.w_state * proof.state_at_r2;
    if expected != claimed {
        return None;
    }

    channel.absorb(proof.s_in_at_r2);
    channel.absorb(proof.s_out_at_r2);
    channel.absorb(proof.state_at_r2);

    Some(SpineShiftReduction {
        r_double_prime,
        s_in_at_r2: proof.s_in_at_r2,
        s_out_at_r2: proof.s_out_at_r2,
        state_at_r2: proof.state_at_r2,
    })
}

// ---------------------------------------------------------------------------
// Combined weight construction (prover side).
// ---------------------------------------------------------------------------

struct CombinedWeights {
    w_sin: Vec<Block128>,
    w_sout: Vec<Block128>,
    w_state: Vec<Block128>,
}

struct WeightsAtPoint {
    w_sin: Block128,
    w_sout: Block128,
    w_state: Block128,
}

/// Build the per-cell combined weight tables for the shift gadget.
/// Returns three length-`2^14` tables aligned with the natural
/// low-bit-first cell index.
fn build_combined_weights(r_prime: &[Block128], delta: Block128) -> CombinedWeights {
    let r_slot = &r_prime[SLOT_LO..SLOT_HI];
    let r_round = &r_prime[ROUND_LO..ROUND_HI];
    let r_elem = &r_prime[ELEM_LO..ELEM_HI];

    // w_dec[x] = eq(r', inc(x)). Since `inc_round_index` only touches
    // round bits, we factorise as eq_slot · eq_round_at_inc(round) · eq_elem.
    let mut w_dec = vec![Block128::ZERO; N_SPINE_UNIFIED_CELLS];
    // w_lane[j][x] = eq_slot · eq_round_at_inc(round) · 1[elem==j].
    let mut w_lane: [Vec<Block128>; STATE_SIZE] =
        std::array::from_fn(|_| vec![Block128::ZERO; N_SPINE_UNIFIED_CELLS]);

    let n_slots = 1usize << N_SPINE_SLOT_VARS;
    let n_rounds = 1usize << N_SPINE_ROUND_VARS;
    let n_elems = 1usize << N_SPINE_ELEM_VARS;

    // Precompute eq_slot[s], eq_elem[e].
    let eq_slot_tab = boolean_tensor(r_slot);
    let eq_elem_tab = boolean_tensor(r_elem);

    // Precompute eq_round_at_inc[round_x] = eq(r_round, (round_x + 1) mod 128).
    let mut eq_round_at_inc = vec![Block128::ZERO; n_rounds];
    let eq_round_tab = boolean_tensor(r_round);
    for round_x in 0..n_rounds {
        let inc = (round_x + 1) & (n_rounds - 1);
        eq_round_at_inc[round_x] = eq_round_tab[inc];
    }

    for slot in 0..n_slots {
        let es = eq_slot_tab[slot];
        for round_x in 0..n_rounds {
            let er = eq_round_at_inc[round_x];
            let es_er = es * er;
            for elem in 0..n_elems {
                let idx = (slot << SLOT_LO) | (round_x << ROUND_LO) | (elem << ELEM_LO);
                let ee = eq_elem_tab[elem];
                w_dec[idx] = es_er * ee;
                // 1[elem(x)==j] is non-zero only at j==elem(x);
                // populate that single lane column.
                w_lane[elem][idx] = es_er;
            }
        }
    }

    // Combined weights: linear combinations with δ-powers.
    let d0 = Block128::ONE;
    let d1 = delta;
    let d2 = d1 * delta;
    let d3 = d2 * delta;
    let d4 = d3 * delta;
    let d5 = d4 * delta;
    let d6 = d5 * delta;
    let d7 = d6 * delta;
    let d8 = d7 * delta;
    let d9 = d8 * delta;
    let d10 = d9 * delta;

    let lane_sout = [d3, d4, d5, d6];
    let lane_state = [d7, d8, d9, d10];

    let mut w_sin = vec![Block128::ZERO; N_SPINE_UNIFIED_CELLS];
    let mut w_sout = vec![Block128::ZERO; N_SPINE_UNIFIED_CELLS];
    let mut w_state = vec![Block128::ZERO; N_SPINE_UNIFIED_CELLS];

    for x in 0..N_SPINE_UNIFIED_CELLS {
        let dec = w_dec[x];
        w_sin[x] = d0 * dec;
        w_sout[x] = d1 * dec;
        w_state[x] = d2 * dec;
        let elem = x & ((1 << N_SPINE_ELEM_VARS) - 1);
        // For each x, only the lane==elem(x) contributions are non-zero.
        w_sout[x] += lane_sout[elem] * w_lane[elem][x];
        w_state[x] += lane_state[elem] * w_lane[elem][x];
    }

    CombinedWeights {
        w_sin,
        w_sout,
        w_state,
    }
}

/// Combined target value the verifier checks against the first
/// round-poly sum: `Σ_k δ^k · c_k`.
fn combined_target(red: &SpineUnifiedReduction, delta: Block128) -> Block128 {
    let d0 = Block128::ONE;
    let d1 = delta;
    let d2 = d1 * delta;
    let mut acc = d0 * red.s_in_dec_at_r + d1 * red.s_out_dec_at_r + d2 * red.state_dec_at_r;
    let mut p = d2 * delta; // δ^3
    for j in 0..STATE_SIZE {
        acc += p * red.s_out_lane_dec_at_r[j];
        p *= delta;
    }
    for j in 0..STATE_SIZE {
        acc += p * red.state_lane_dec_at_r[j];
        p *= delta;
    }
    acc
}

/// Recompute `(W_sin, W_sout, W_state)` at `r''` natively in O(N_VARS)
/// muls via the eq factorisation.
///
/// Each combined weight is the multilinear extension (in x) of a
/// public function evaluated at the verifier's point r''. The base
/// pieces factorise along the (slot, round, elem) axes:
///
/// * `w_dec(x) = eq(r'_slot, slot(x)) · eq(r'_round, round_inc(x)) · eq(r'_elem, elem(x))`
///   so its MLE at r'' is `eq_slot · g(r''_round) · eq_elem`,
///   with `g(t) = MLE-in-round_x of eq(r'_round, round_inc(round_x))`.
///
/// * `w_lane[j](x) = eq(r'_slot, slot(x)) · eq(r'_round, round_inc(x)) · 1[elem(x)==j]`
///   has MLE at r'' equal to `eq_slot · g(r''_round) · ind_j(r''_elem)`,
///   where `ind_j(r''_elem) = Π_b f_b(r''_elem_b)` with
///   `f_b(t) = t` if bit b of j is 1 else `1+t`.
fn combined_weights_at_point(
    r_prime: &[Block128],
    delta: Block128,
    r2: &[Block128],
) -> WeightsAtPoint {
    let rp_slot = &r_prime[SLOT_LO..SLOT_HI];
    let rp_round = &r_prime[ROUND_LO..ROUND_HI];
    let rp_elem = &r_prime[ELEM_LO..ELEM_HI];
    let r2_slot = &r2[SLOT_LO..SLOT_HI];
    let r2_round = &r2[ROUND_LO..ROUND_HI];
    let r2_elem = &r2[ELEM_LO..ELEM_HI];

    let eq_slot = eq_ind(rp_slot, r2_slot);
    let eq_elem = eq_ind(rp_elem, r2_elem);

    // g(r''_round) = MLE-in-round_x of eq(rp_round, round_inc(round_x))
    // at t = r''_round. Build the 128-cell table once.
    let n_rounds = 1usize << N_SPINE_ROUND_VARS;
    let eq_rp_round_tab = boolean_tensor(rp_round);
    let mut tab = vec![Block128::ZERO; n_rounds];
    for round_x in 0..n_rounds {
        let inc = (round_x + 1) & (n_rounds - 1);
        tab[round_x] = eq_rp_round_tab[inc];
    }
    let g_round = evaluate_slice(&tab, r2_round);

    // Indicator MLEs `1[elem == j]` at r''_elem.
    let mut ind_j_at_r2 = [Block128::ZERO; STATE_SIZE];
    for (j, slot) in ind_j_at_r2.iter_mut().enumerate() {
        let mut acc = Block128::ONE;
        for (b, &r) in r2_elem.iter().enumerate() {
            if (j >> b) & 1 == 1 {
                acc *= r;
            } else {
                acc *= Block128::ONE + r;
            }
        }
        *slot = acc;
    }

    let w_dec_r2 = eq_slot * g_round * eq_elem;
    let lane_base = eq_slot * g_round;

    let d0 = Block128::ONE;
    let d1 = delta;
    let d2 = d1 * delta;
    let mut p = d2;
    let mut lane_sout = [Block128::ZERO; STATE_SIZE];
    for slot in lane_sout.iter_mut() {
        p *= delta;
        *slot = p;
    }
    let mut lane_state = [Block128::ZERO; STATE_SIZE];
    for slot in lane_state.iter_mut() {
        p *= delta;
        *slot = p;
    }

    let w_sin = d0 * w_dec_r2;
    let mut w_sout = d1 * w_dec_r2;
    let mut w_state = d2 * w_dec_r2;
    for j in 0..STATE_SIZE {
        let lane_w = lane_base * ind_j_at_r2[j];
        w_sout += lane_sout[j] * lane_w;
        w_state += lane_state[j] * lane_w;
    }

    WeightsAtPoint {
        w_sin,
        w_sout,
        w_state,
    }
}

fn boolean_tensor(point: &[Block128]) -> Vec<Block128> {
    use noid_core::mle::eq::eq_ind_partial_eval;
    eq_ind_partial_eval::<Block128>(point)
}

/// Tower-basis parity implementation of the shift-gadget round
/// polynomial. Kept as a parity oracle for
/// `flat_shift_round_poly_matches_tower`. Production
/// callers go through `compute_shift_round_polynomial_flat`.
#[allow(dead_code)]
fn compute_shift_round_polynomial(
    s_in: &[Block128],
    s_out: &[Block128],
    state: &[Block128],
    w_sin: &[Block128],
    w_sout: &[Block128],
    w_state: &[Block128],
) -> RoundPolynomial<Block128> {
    let half = s_in.len() / 2;
    let mut evals = [Block128::ZERO; SPINE_SHIFT_ROUND_DEGREE + 1];
    for i in 0..half {
        let (sin0, sin1) = (s_in[i], s_in[i + half]);
        let (sout0, sout1) = (s_out[i], s_out[i + half]);
        let (st0, st1) = (state[i], state[i + half]);
        let (wsin0, wsin1) = (w_sin[i], w_sin[i + half]);
        let (wsout0, wsout1) = (w_sout[i], w_sout[i + half]);
        let (wst0, wst1) = (w_state[i], w_state[i + half]);

        let dsin = sin0 + sin1;
        let dsout = sout0 + sout1;
        let dst = st0 + st1;
        let dwsin = wsin0 + wsin1;
        let dwsout = wsout0 + wsout1;
        let dwst = wst0 + wst1;

        for (k, slot) in evals.iter_mut().enumerate() {
            let t = Block128::from(k as u8);
            let sin = sin0 + t * dsin;
            let sout = sout0 + t * dsout;
            let st = st0 + t * dst;
            let wsin = wsin0 + t * dwsin;
            let wsout = wsout0 + t * dwsout;
            let wst = wst0 + t * dwst;
            *slot += wsin * sin + wsout * sout + wst * st;
        }
    }
    RoundPolynomial::from_evals(&evals)
}

/// Flat-basis fast path for the shift gadget round polynomial.
///
/// All six inputs must already be in flat basis. Returns a tower-basis
/// `RoundPolynomial` because that is what the channel and the verifier
/// consume.
fn compute_shift_round_polynomial_flat(
    s_in: &[u128],
    s_out: &[u128],
    state: &[u128],
    w_sin: &[u128],
    w_sout: &[u128],
    w_state: &[u128],
) -> RoundPolynomial<Block128> {
    let half = s_in.len() / 2;
    let mut evals = [0u128; SPINE_SHIFT_ROUND_DEGREE + 1];
    let t_flat: [u128; SPINE_SHIFT_ROUND_DEGREE + 1] =
        std::array::from_fn(|k| tower_to_flat_u128(k as u128));

    for i in 0..half {
        let (sin0, sin1) = (s_in[i], s_in[i + half]);
        let (sout0, sout1) = (s_out[i], s_out[i + half]);
        let (st0, st1) = (state[i], state[i + half]);
        let (wsin0, wsin1) = (w_sin[i], w_sin[i + half]);
        let (wsout0, wsout1) = (w_sout[i], w_sout[i + half]);
        let (wst0, wst1) = (w_state[i], w_state[i + half]);

        let dsin = sin0 ^ sin1;
        let dsout = sout0 ^ sout1;
        let dst = st0 ^ st1;
        let dwsin = wsin0 ^ wsin1;
        let dwsout = wsout0 ^ wsout1;
        let dwst = wst0 ^ wst1;

        for k in 0..=SPINE_SHIFT_ROUND_DEGREE {
            let t = t_flat[k];
            let sin = sin0 ^ clmul_gcm(t, dsin);
            let sout = sout0 ^ clmul_gcm(t, dsout);
            let st = st0 ^ clmul_gcm(t, dst);
            let wsin = wsin0 ^ clmul_gcm(t, dwsin);
            let wsout = wsout0 ^ clmul_gcm(t, dwsout);
            let wst = wst0 ^ clmul_gcm(t, dwst);
            evals[k] ^= clmul_gcm(wsin, sin) ^ clmul_gcm(wsout, sout) ^ clmul_gcm(wst, st);
        }
    }

    let evals_tower: [Block128; SPINE_SHIFT_ROUND_DEGREE + 1] =
        std::array::from_fn(|k| Block128::from(flat_to_tower_u128(evals[k])));
    RoundPolynomial::from_evals(&evals_tower)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spine_mle::{build_unified_mle, N_SPINE_SLOTS};
    use noid_poseidon2b::channel::Poseidon2bChannel;

    fn random_state(seed: u128) -> [Block128; STATE_SIZE] {
        let mut s = seed.wrapping_add(0xC0FFEE);
        std::array::from_fn(|_| {
            s = s.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0xDEAD_BEEF);
            Block128::from(s)
        })
    }

    fn random_mle(seed: u128) -> SpineUnifiedMle {
        let state_ins: Vec<_> = (0..N_SPINE_SLOTS)
            .map(|i| random_state(i as u128 + seed))
            .collect();
        let (mle, _) = build_unified_mle(&state_ins);
        mle.debug_check_identity();
        mle
    }

    #[test]
    fn round_degree_constant_matches() {
        assert_eq!(SPINE_UNIFIED_ROUND_DEGREE, 9);
    }

    #[test]
    fn pow7_poly_t_matches_naive() {
        // Monomial-form parity check: the 8-coefficient build of (a + t·b)^7 must
        // agree with `pow7_flat_block128(a ^ clmul_gcm(t, b))` for
        // every flat-basis t, evaluated as a degree-7 polynomial in t.
        use rand::Rng;
        let mut rng = rand::thread_rng();
        for _ in 0..1000 {
            let a = rng.gen::<u128>();
            let b = rng.gen::<u128>();
            let coeffs = pow7_poly_t(a, b);
            for k in 0..=9u128 {
                let t = tower_to_flat_u128(k);
                // Horner over `coeffs` (lowest degree first).
                let mut horner = 0u128;
                for &c in coeffs.iter().rev() {
                    horner = clmul_gcm(horner, t) ^ c;
                }
                let direct = pow7_flat_block128(a ^ clmul_gcm(t, b));
                assert_eq!(
                    horner, direct,
                    "pow7_poly_t mismatch at t-index {} (a={:x}, b={:x})",
                    k, a, b
                );
            }
        }
    }

    #[test]
    fn flat_round_poly_matches_tower_round_poly() {
        // Parity test: the flat-basis prover hot path (monomial form)
        // must compute the bit-identical round polynomial as both the
        // tower-basis parity path and the per-evaluation flat-basis
        // baseline, in every round.
        let mle = random_mle(424242);
        let rho: Vec<Block128> = (0..N_SPINE_UNIFIED_VARS)
            .map(|k| Block128::from(0xA5A5_DEAD_BEEFu128.wrapping_mul((k as u128) + 1)))
            .collect();
        let beta = Block128::from(0x00C0_FFEE_BAAD_u128);
        let gamma = Block128::from(0xFEEDFACE_CAFEBABEu128);

        let mut tow = build_unified_tables(&mle, &rho, N_SPINE_SLOTS);
        let mut flt =
            UnifiedFlatTables::from_tower(build_unified_tables(&mle, &rho, N_SPINE_SLOTS));
        let beta_flat = tower_to_flat_u128(beta.to_u128());
        let gamma_flat = tower_to_flat_u128(gamma.to_u128());

        for round in 0..N_SPINE_UNIFIED_VARS {
            let p_tow = compute_round_polynomial(&tow, beta, gamma);
            let p_flt = compute_round_polynomial_flat(&flt, beta_flat, gamma_flat);
            let p_flt_eval = compute_round_polynomial_flat_per_eval(&flt, beta_flat, gamma_flat);
            assert_eq!(
                p_tow.coeffs, p_flt.coeffs,
                "round {} monomial-form flat poly diverged from tower",
                round
            );
            assert_eq!(
                p_flt_eval.coeffs, p_flt.coeffs,
                "round {} monomial-form flat poly diverged from per-eval flat",
                round
            );
            // Use a deterministic round challenge for both bookkeeping.
            let r = Block128::from(0xDEAD_BEEFu128.wrapping_mul((round as u128) + 7));
            tow.fold(r);
            flt.fold_flat(tower_to_flat_u128(r.to_u128()));
        }

        // Final claims must match too (the prover absorbs them into
        // the channel — bit-equality there is what guarantees the
        // end-to-end proof bit-equals the tower-basis prover would
        // have produced on the same fixture).
        let tow_claims = tow.final_claims();
        let flt_claims = flt.final_claims_tower();
        assert_eq!(tow_claims.s_in_dec, flt_claims.s_in_dec);
        assert_eq!(tow_claims.s_out_dec, flt_claims.s_out_dec);
        assert_eq!(tow_claims.state_dec, flt_claims.state_dec);
        assert_eq!(tow_claims.state, flt_claims.state);
        assert_eq!(tow_claims.s_out_lane_dec, flt_claims.s_out_lane_dec);
        assert_eq!(tow_claims.state_lane_dec, flt_claims.state_lane_dec);
    }

    #[test]
    fn honest_prover_verifies() {
        let mle = random_mle(17);

        let mut ch_p = Poseidon2bChannel::new();
        let (proof, _r_prime) = prove_spine_unified(&mle, &mut ch_p);
        assert_eq!(proof.round_polys.len(), N_SPINE_UNIFIED_VARS);

        let mut ch_v = Poseidon2bChannel::new();
        let red = verify_spine_unified(&proof, &mut ch_v).expect("verify must accept");
        assert_eq!(red.r_prime.len(), N_SPINE_UNIFIED_VARS);
        // Channels stay in sync.
        assert_eq!(ch_p.squeeze(), ch_v.squeeze());
    }

    #[test]
    fn final_claims_match_native_mle_evaluations() {
        let mle = random_mle(91);

        let mut ch_p = Poseidon2bChannel::new();
        let (proof, _r_prime) = prove_spine_unified(&mle, &mut ch_p);

        let mut ch_v = Poseidon2bChannel::new();
        let red = verify_spine_unified(&proof, &mut ch_v).unwrap();

        // Direct openings: state(r').
        assert_eq!(evaluate_slice(&mle.state, &red.r_prime), red.state_at_r);

        // Permuted openings: each `_dec` claim must equal the native
        // evaluation of the round-shifted column at r'.
        assert_eq!(
            evaluate_slice(&permute_by_dec(&mle.s_in), &red.r_prime),
            red.s_in_dec_at_r
        );
        assert_eq!(
            evaluate_slice(&permute_by_dec(&mle.s_out), &red.r_prime),
            red.s_out_dec_at_r
        );
        assert_eq!(
            evaluate_slice(&permute_by_dec(&mle.state), &red.r_prime),
            red.state_dec_at_r
        );

        let s_out_dec_full = permute_by_dec(&mle.s_out);
        let state_dec_full = permute_by_dec(&mle.state);
        for j in 0..STATE_SIZE {
            assert_eq!(
                evaluate_slice(&project_lane(&s_out_dec_full, j), &red.r_prime),
                red.s_out_lane_dec_at_r[j],
                "s_out lane {j}"
            );
            assert_eq!(
                evaluate_slice(&project_lane(&state_dec_full, j), &red.r_prime),
                red.state_lane_dec_at_r[j],
                "state lane {j}"
            );
        }
    }

    #[test]
    fn tampered_state_claim_is_rejected() {
        let mle = random_mle(5);

        let mut ch_p = Poseidon2bChannel::new();
        let (mut proof, _r_prime) = prove_spine_unified(&mle, &mut ch_p);
        proof.state_at_r += Block128::ONE;

        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_spine_unified(&proof, &mut ch_v).is_none());
    }

    #[test]
    fn tampered_s_in_dec_claim_is_rejected() {
        let mle = random_mle(13);

        let mut ch_p = Poseidon2bChannel::new();
        let (mut proof, _r_prime) = prove_spine_unified(&mle, &mut ch_p);
        proof.s_in_dec_at_r += Block128::from(0xBADu32);

        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_spine_unified(&proof, &mut ch_v).is_none());
    }

    #[test]
    fn tampered_lane_claim_is_rejected() {
        let mle = random_mle(23);

        let mut ch_p = Poseidon2bChannel::new();
        let (mut proof, _r_prime) = prove_spine_unified(&mle, &mut ch_p);
        proof.s_out_lane_dec_at_r[2] += Block128::ONE;

        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_spine_unified(&proof, &mut ch_v).is_none());
    }

    #[test]
    fn tampered_round_poly_is_rejected() {
        let mle = random_mle(31);

        let mut ch_p = Poseidon2bChannel::new();
        let (mut proof, _r_prime) = prove_spine_unified(&mle, &mut ch_p);
        proof.round_polys[7].coeffs[0] += Block128::ONE;

        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_spine_unified(&proof, &mut ch_v).is_none());
    }

    #[test]
    fn malformed_proof_rejected_on_round_count() {
        let mle = random_mle(41);

        let mut ch_p = Poseidon2bChannel::new();
        let (mut proof, _r_prime) = prove_spine_unified(&mle, &mut ch_p);
        proof.round_polys.pop();

        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_spine_unified(&proof, &mut ch_v).is_none());
    }

    // -----------------------------------------------------------------------
    // Shift gadget tests.
    // -----------------------------------------------------------------------

    fn run_full_pipeline(seed: u128) -> (SpineUnifiedMle, SpineKillShotProof) {
        let mle = random_mle(seed);
        let mut ch = Poseidon2bChannel::new();
        let (main, r_prime) = prove_spine_unified(&mle, &mut ch);
        let (shift, _r2) = prove_spine_shift(&mle, &r_prime, &mut ch);
        (mle, SpineKillShotProof { main, shift })
    }

    #[test]
    fn flat_shift_round_poly_matches_tower() {
        // Flat-basis shift gadget parity: the round
        // polynomial is bit-identical to the tower-basis parity path.
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let n: usize = 1 << N_SPINE_UNIFIED_VARS;
        let mut make =
            || -> Vec<Block128> { (0..n).map(|_| Block128::from(rng.gen::<u128>())).collect() };
        let s_in = make();
        let s_out = make();
        let state = make();
        let w_sin = make();
        let w_sout = make();
        let w_state = make();

        let p_tow =
            compute_shift_round_polynomial(&s_in, &s_out, &state, &w_sin, &w_sout, &w_state);
        let s_in_f = vec_tower_to_flat(s_in);
        let s_out_f = vec_tower_to_flat(s_out);
        let state_f = vec_tower_to_flat(state);
        let w_sin_f = vec_tower_to_flat(w_sin);
        let w_sout_f = vec_tower_to_flat(w_sout);
        let w_state_f = vec_tower_to_flat(w_state);
        let p_flt = compute_shift_round_polynomial_flat(
            &s_in_f, &s_out_f, &state_f, &w_sin_f, &w_sout_f, &w_state_f,
        );
        assert_eq!(p_tow.coeffs, p_flt.coeffs);
    }

    #[test]
    fn shift_gadget_round_count_and_degree() {
        let (_, proof) = run_full_pipeline(101);
        assert_eq!(proof.shift.round_polys.len(), N_SPINE_UNIFIED_VARS);
        for p in &proof.shift.round_polys {
            assert!(p.degree() <= SPINE_SHIFT_ROUND_DEGREE);
        }
    }

    #[test]
    fn shift_gadget_verifies_end_to_end() {
        let (_, proof) = run_full_pipeline(102);

        let mut ch = Poseidon2bChannel::new();
        let main_red = verify_spine_unified(&proof.main, &mut ch).expect("main verify");
        let shift_red = verify_spine_shift(&proof.shift, &main_red, &mut ch).expect("shift verify");
        assert_eq!(shift_red.r_double_prime.len(), N_SPINE_UNIFIED_VARS);
    }

    #[test]
    fn shift_final_claims_match_native_evaluations() {
        let (mle, proof) = run_full_pipeline(103);

        let mut ch = Poseidon2bChannel::new();
        let main_red = verify_spine_unified(&proof.main, &mut ch).unwrap();
        let shift_red = verify_spine_shift(&proof.shift, &main_red, &mut ch).unwrap();

        assert_eq!(
            evaluate_slice(&mle.s_in, &shift_red.r_double_prime),
            shift_red.s_in_at_r2
        );
        assert_eq!(
            evaluate_slice(&mle.s_out, &shift_red.r_double_prime),
            shift_red.s_out_at_r2
        );
        assert_eq!(
            evaluate_slice(&mle.state, &shift_red.r_double_prime),
            shift_red.state_at_r2
        );
    }

    #[test]
    fn shift_tampered_final_claim_is_rejected() {
        let (_, mut proof) = run_full_pipeline(104);
        proof.shift.s_in_at_r2 += Block128::ONE;

        let mut ch = Poseidon2bChannel::new();
        let main_red = verify_spine_unified(&proof.main, &mut ch).unwrap();
        assert!(verify_spine_shift(&proof.shift, &main_red, &mut ch).is_none());
    }

    #[test]
    fn shift_tampered_round_poly_is_rejected() {
        let (_, mut proof) = run_full_pipeline(105);
        proof.shift.round_polys[3].coeffs[0] += Block128::ONE;

        let mut ch = Poseidon2bChannel::new();
        let main_red = verify_spine_unified(&proof.main, &mut ch).unwrap();
        assert!(verify_spine_shift(&proof.shift, &main_red, &mut ch).is_none());
    }

    #[test]
    fn shift_combined_target_matches_first_round_sum() {
        // The very first sumcheck round-poly must sum to the
        // verifier's combined target; this pins the prover/verifier
        // RLC convention.
        let (mle, _) = run_full_pipeline(106);

        let mut ch = Poseidon2bChannel::new();
        let (main, r_prime) = prove_spine_unified(&mle, &mut ch);
        let (shift, _r2) = prove_spine_shift(&mle, &r_prime, &mut ch);

        let mut ch_v = Poseidon2bChannel::new();
        let main_red = verify_spine_unified(&main, &mut ch_v).unwrap();
        let delta = ch_v.squeeze();
        let target = combined_target(&main_red, delta);
        let first = &shift.round_polys[0];
        assert_eq!(
            first.evaluate(Block128::ZERO) + first.evaluate(Block128::ONE),
            target
        );
    }
}
