// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Unified Block SpineGKR — single Kill-Shot over N*31 slots.
//!
//! Instead of N independent per-tx SpineGKR proofs (each 5 KB, each
//! requiring a separate sumcheck replay at verification), this module
//! packs all N transactions' 31-slot spines into a single dynamically-
//! sized MLE and runs one unified Kill-Shot.
//!
//! Proof size and verification cost grow logarithmically rather than
//! linearly in the number of transaction bodies.
//!
//! # Layout
//!
//! The bit layout mirrors the per-tx `SpineUnifiedMle` but with more
//! slot bits:
//!
//! ```text
//!   elem:2 | round:7 | slot:S
//! ```
//!
//! where `S = ceil(log2(N * 31))` (padded to next power of two).
//!
//! The constraints (C1, C1', C2) are identical per-slot — the same
//! Poseidon2b round structure applies regardless of which transaction
//! owns the slot.

use noid_core::hardware::{clmul_gcm, flat_to_tower_u128, square_flat_u128, tower_to_flat_u128};
use noid_core::mle::eq::{eq_ind, eq_ind_partial_eval};
use noid_core::mle::evaluate::evaluate_slice;
use noid_core::packed::pow7::pow7_block128;
use noid_core::transcript::FiatShamir;
use noid_core::{Block128, TowerField};
use noid_poseidon2b::native::permutation::{
    F_ROUNDS, MDS_FULL, MDS_PARTIAL, N_ROUNDS, P_ROUNDS, ROUND_CONSTANTS, STATE_SIZE,
};

use crate::batch_eval::{
    prove_linear_eval_prebound, prove_multi_batch_eval, verify_linear_eval_prebound,
    verify_multi_batch_eval, BatchEvalReduction, EvalClaim, LinearEvalClaim, LinearEvalProof,
    LinearEvalTerm, MultiBatchEvalProof,
};
use crate::layers::{
    apply_mds_full, apply_mds_partial, evaluate_permutation, round_kind, RoundKind,
};
use crate::spine_mle::{sigma_at, N_SPINE_ELEM_VARS, N_SPINE_ROUND_VARS};
use crate::spine_sumcheck::N_SPINE_SLOTS;
use noid_core::sumcheck::{CompressedRoundPolynomial, RoundPolynomial};
use std::time::{Duration, Instant};

const ELEM_BITS: usize = N_SPINE_ELEM_VARS; // 2
const ROUND_BITS: usize = N_SPINE_ROUND_VARS; // 7
const ROUND_LIMIT: usize = 1 << ROUND_BITS; // 128
                                            // Public: the in-circuit trace transliteration replays the tx-hash pin relation
                                            // from this same definition; change both together.
pub const BLOCK_SPINE_TX_HASH_PIN_TAG: u128 = 0x4253_5049_4E54_5801; // "BSPINTX"+1

/// Per-variable degree of the unified block sumcheck (same as per-tx).
pub const BLOCK_SPINE_ROUND_DEGREE: usize = 9;

#[derive(Debug)]
struct BlockSpinePhaseTiming {
    name: &'static str,
    elapsed: Duration,
}

#[derive(Debug)]
struct BlockSpineProfiler {
    enabled: bool,
    scope: &'static str,
    n_instances: usize,
    live_slots: usize,
    num_vars: usize,
    started: Instant,
    last: Instant,
    phases: Vec<BlockSpinePhaseTiming>,
}

impl BlockSpineProfiler {
    fn new(scope: &'static str, n_instances: usize, live_slots: usize, num_vars: usize) -> Self {
        let now = Instant::now();
        Self {
            enabled: block_spine_profile_enabled(),
            scope,
            n_instances,
            live_slots,
            num_vars,
            started: now,
            last: now,
            phases: Vec::with_capacity(12),
        }
    }

    fn enabled(&self) -> bool {
        self.enabled
    }

    fn phase(&mut self, name: &'static str) {
        if !self.enabled {
            return;
        }
        let now = Instant::now();
        self.phases.push(BlockSpinePhaseTiming {
            name,
            elapsed: now.duration_since(self.last),
        });
        self.last = now;
    }

    fn record(&mut self, name: &'static str, elapsed: Duration) {
        if !self.enabled {
            return;
        }
        self.phases.push(BlockSpinePhaseTiming { name, elapsed });
    }

    fn finish(self) {
        if !self.enabled {
            return;
        }

        let total = self.started.elapsed();
        let summary = self
            .phases
            .iter()
            .map(|p| format!("{}={:.3}ms", p.name, duration_ms(p.elapsed)))
            .collect::<Vec<_>>()
            .join(", ");

        for phase in &self.phases {
            eprintln!(
                "prove_block_profile block_spine scope={} phase={} n_instances={} live_slots={} num_vars={} elapsed_ms={:.3}",
                self.scope,
                phase.name,
                self.n_instances,
                self.live_slots,
                self.num_vars,
                duration_ms(phase.elapsed)
            );
        }
        eprintln!(
            "prove_block_profile block_spine summary scope={} n_instances={} live_slots={} num_vars={} total_ms={:.3} phases={}",
            self.scope,
            self.n_instances,
            self.live_slots,
            self.num_vars,
            duration_ms(total),
            summary
        );
    }
}

fn block_spine_profile_enabled() -> bool {
    std::env::var("NOID_PROVE_BLOCK_PROFILE")
        .map(|v| {
            matches!(
                v.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        })
        .unwrap_or(false)
}

fn duration_ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1_000.0
}

/// Compute the number of slot variables needed for `total_live_slots`.
fn slot_vars_for(total_live_slots: usize) -> usize {
    assert!(total_live_slots > 0);
    let bits = (usize::BITS - (total_live_slots - 1).leading_zeros()) as usize;
    bits.max(1)
}

/// Total number of MLE variables for a given number of live slots.
pub fn num_vars_for(total_live_slots: usize) -> usize {
    slot_vars_for(total_live_slots) + ROUND_BITS + ELEM_BITS
}

/// Pack (slot, round, elem) into the dynamic-width index.
#[inline]
fn pack_index_dyn(slot: usize, round: usize, elem: usize) -> usize {
    (slot << (ROUND_BITS + ELEM_BITS)) | (round << ELEM_BITS) | elem
}

/// Hypercube point for the dynamic block-spine `state(slot, round, elem)`.
pub fn block_spine_state_point(
    num_vars: usize,
    slot: usize,
    round: usize,
    elem: usize,
) -> Vec<Block128> {
    let cell = pack_index_dyn(slot, round, elem);
    (0..num_vars)
        .map(|b| {
            if (cell >> b) & 1 == 1 {
                Block128::ONE
            } else {
                Block128::ZERO
            }
        })
        .collect()
}

/// Extract round from a dynamic-width index.
#[inline]
fn round_of_dyn(idx: usize) -> usize {
    (idx >> ELEM_BITS) & ((1 << ROUND_BITS) - 1)
}

/// Extract slot from a dynamic-width index given slot_vars.
#[inline]
fn slot_of_dyn(idx: usize) -> usize {
    idx >> (ROUND_BITS + ELEM_BITS)
}

/// Extract elem from a dynamic-width index.
#[inline]
fn elem_of_dyn(idx: usize) -> usize {
    idx & ((1 << ELEM_BITS) - 1)
}

/// Decrement the round component by 1 (mod 128) in a dynamic-width index.
#[inline]
fn dec_round_dyn(idx: usize) -> usize {
    let round = round_of_dyn(idx);
    let prev = (round + ROUND_LIMIT - 1) & (ROUND_LIMIT - 1);
    let round_mask = ((1 << ROUND_BITS) - 1) << ELEM_BITS;
    (idx & !round_mask) | (prev << ELEM_BITS)
}

/// Dynamically-sized unified MLE for the block spine.
#[derive(Debug, Clone)]
pub struct BlockSpineMle {
    pub s_in: Vec<Block128>,
    pub s_out: Vec<Block128>,
    pub state: Vec<Block128>,
    pub num_vars: usize,
    pub live_slots: usize,
}

impl BlockSpineMle {
    /// Build a dynamic Poseidon2b permutation-trace MLE from arbitrary live
    /// slot inputs. This is the shared production helper for block spines and
    /// batched Merkle paths.
    pub fn build_from_slot_state_ins(slot_state_ins: &[[Block128; STATE_SIZE]]) -> Self {
        let total_live = slot_state_ins.len();
        Self::build_from_slot_state_ins_padded(slot_state_ins, total_live)
    }

    /// Build a dynamic Poseidon2b permutation-trace MLE with a fixed active
    /// slot count. Slots beyond `slot_state_ins.len()` are independent zero
    /// permutation witnesses; they fix the proof shape without changing the
    /// caller's logical claims over the supplied slots.
    pub fn build_from_slot_state_ins_padded(
        slot_state_ins: &[[Block128; STATE_SIZE]],
        padded_live_slots: usize,
    ) -> Self {
        let total_live = slot_state_ins.len();
        assert!(total_live > 0);
        assert!(total_live <= padded_live_slots);
        let num_vars = num_vars_for(padded_live_slots);
        let n_cells = 1usize << num_vars;

        let mut mle = BlockSpineMle {
            s_in: vec![Block128::ZERO; n_cells],
            s_out: vec![Block128::ZERO; n_cells],
            state: vec![Block128::ZERO; n_cells],
            num_vars,
            live_slots: padded_live_slots,
        };

        use rayon::prelude::*;
        let witnesses: Vec<crate::layers::PermLayerWitness> = (0..padded_live_slots)
            .into_par_iter()
            .map(|slot| {
                let state_in = slot_state_ins
                    .get(slot)
                    .copied()
                    .unwrap_or([Block128::ZERO; STATE_SIZE]);
                evaluate_permutation(state_in)
            })
            .collect();

        for (slot, witness) in witnesses.iter().enumerate() {
            mle.populate_slot(slot, witness);
        }
        mle
    }

    /// Build the unified block MLE from N transactions' slot state_in vectors.
    /// Each transaction contributes exactly `N_SPINE_SLOTS` (31) slots.
    pub fn build(n_instances: usize, slot_state_ins: &[[Block128; STATE_SIZE]]) -> Self {
        let total_live = n_instances * N_SPINE_SLOTS;
        assert_eq!(slot_state_ins.len(), total_live);
        let num_vars = num_vars_for(total_live);
        let n_cells = 1usize << num_vars;
        let mut profiler =
            BlockSpineProfiler::new("block_spine_mle_build", n_instances, total_live, num_vars);

        let mut mle = BlockSpineMle {
            s_in: vec![Block128::ZERO; n_cells],
            s_out: vec![Block128::ZERO; n_cells],
            state: vec![Block128::ZERO; n_cells],
            num_vars,
            live_slots: total_live,
        };
        profiler.phase("allocate_columns");

        // Parallel: evaluate_permutation (Poseidon2b chain) is the expensive part.
        // Each slot's computation is fully independent.
        use rayon::prelude::*;
        let witnesses: Vec<crate::layers::PermLayerWitness> = slot_state_ins
            .par_iter()
            .map(|&state_in| evaluate_permutation(state_in))
            .collect();
        profiler.phase("evaluate_permutation_witnesses");

        // Sequential fill: populate_slot takes &mut self but writes to disjoint
        // indices; this pass is cheap compared to the permutation evaluations.
        for (slot, witness) in witnesses.iter().enumerate() {
            mle.populate_slot(slot, witness);
        }
        profiler.phase("populate_columns");
        profiler.finish();
        mle
    }

    fn populate_slot(&mut self, slot: usize, witness: &crate::layers::PermLayerWitness) {
        for r in 0..N_ROUNDS {
            for elem in 0..STATE_SIZE {
                let idx = pack_index_dyn(slot, r, elem);
                self.s_in[idx] = witness.sin[r][elem];
                self.s_out[idx] = witness.sout[r][elem];
            }
        }
        debug_assert_eq!(witness.state.len(), N_ROUNDS + 1);
        for r in 0..=N_ROUNDS {
            for elem in 0..STATE_SIZE {
                let idx = pack_index_dyn(slot, r, elem);
                self.state[idx] = witness.state[r][elem];
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Public schedule tables (dynamic size)
// ---------------------------------------------------------------------------

fn mds_coeff_dyn(round: usize, i: usize, j: usize) -> Block128 {
    let is_partial = (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&round);
    let raw = if is_partial {
        MDS_PARTIAL[i][j]
    } else {
        MDS_FULL[i][j]
    };
    Block128::from(raw)
}

fn sigma_dec_value(live_slots: usize, y: usize) -> Block128 {
    let slot = slot_of_dyn(y);
    if slot >= live_slots {
        return Block128::ZERO;
    }
    let dec_round = round_of_dyn(dec_round_dyn(y));
    if dec_round >= N_ROUNDS {
        return Block128::ZERO;
    }
    sigma_at(dec_round, elem_of_dyn(y))
}

#[cfg(test)]
fn build_sigma_dec_table_flat_dyn(live_slots: usize, n_cells: usize) -> Vec<u128> {
    use rayon::prelude::*;
    (0..n_cells)
        .into_par_iter()
        .map(|y| tower_to_flat_u128(sigma_dec_value(live_slots, y).to_u128()))
        .collect()
}

#[cfg(test)]
fn build_sigma_lane_dec_table_flat_dyn(
    lane: usize,
    live_slots: usize,
    n_cells: usize,
) -> Vec<u128> {
    use rayon::prelude::*;
    let elem_mask = (1 << ELEM_BITS) - 1;
    (0..n_cells)
        .into_par_iter()
        .map(|y| {
            let row_base = y & !elem_mask;
            tower_to_flat_u128(sigma_dec_value(live_slots, row_base | lane).to_u128())
        })
        .collect()
}

#[cfg(test)]
fn build_rc_dec_table_flat_dyn(live_slots: usize, n_cells: usize) -> Vec<u128> {
    use rayon::prelude::*;
    (0..n_cells)
        .into_par_iter()
        .map(|y| {
            let slot = slot_of_dyn(y);
            if slot >= live_slots {
                return 0;
            }
            let dec_round = round_of_dyn(dec_round_dyn(y));
            if dec_round >= N_ROUNDS {
                return 0;
            }
            let elem = elem_of_dyn(y);
            let is_partial = (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&dec_round);
            if is_partial && elem != 0 {
                0
            } else {
                tower_to_flat_u128(ROUND_CONSTANTS[elem][dec_round])
            }
        })
        .collect()
}

#[cfg(test)]
fn build_mds_lane_table_flat_dyn(lane: usize, live_slots: usize, n_cells: usize) -> Vec<u128> {
    use rayon::prelude::*;
    (0..n_cells)
        .into_par_iter()
        .map(|y| {
            let slot = slot_of_dyn(y);
            if slot >= live_slots {
                return 0;
            }
            let dec_round = round_of_dyn(dec_round_dyn(y));
            if dec_round >= N_ROUNDS {
                return 0;
            }
            let elem = elem_of_dyn(y);
            tower_to_flat_u128(mds_coeff_dyn(dec_round, elem, lane).to_u128())
        })
        .collect()
}

#[cfg(test)]
fn build_u_table_flat_dyn(rho: &[Block128], live_slots: usize, n_cells: usize) -> Vec<u128> {
    use rayon::prelude::*;
    let eq_tab = eq_ind_partial_eval::<Block128>(rho);
    (0..n_cells)
        .into_par_iter()
        .map(|y| {
            let x = dec_round_dyn(y);
            let slot = slot_of_dyn(x);
            if slot >= live_slots || round_of_dyn(x) >= N_ROUNDS {
                0
            } else {
                tower_to_flat_u128(eq_tab[x].to_u128())
            }
        })
        .collect()
}

fn permute_by_dec_flat_dyn(src: &[Block128]) -> Vec<u128> {
    use rayon::prelude::*;
    let n = src.len();
    (0..n)
        .into_par_iter()
        .map(|y| tower_to_flat_u128(src[dec_round_dyn(y)].to_u128()))
        .collect()
}

// ---------------------------------------------------------------------------
// Fast direct MLE evaluation at a point — O(live_slots + N_ROUNDS) per table
// ---------------------------------------------------------------------------
//
// All block-spine public-schedule tables (sigma, rc, mds, sigma_lane) share
// the same slot-independent structure.  The prover keeps this factorization
// throughout sumcheck; the verifier evaluates the factors directly at its
// terminal point:
//
//   table(slot, round, elem) = f(prev_round, elem)   for slot < live_slots
//                             = 0                      otherwise
//
// Their MLE at any point r' factors as:
//
//   table_MLE(r') = live_sum(r'_slot)  ×  inner(r'_round, r'_elem)
//
// where:
//   live_sum = Σ_{s < live_slots} eq(r'_slot, s)   — O(live_slots)
//   inner    = Σ_{round=1}^{N_ROUNDS} Σ_elem f(round-1, elem) × eq_round[round] × eq_elem[elem]
//              — O(N_ROUNDS × STATE_SIZE) = O(264) — O(1)
//
// u_table additionally depends on rho (the Fiat-Shamir sumcheck challenge)
// and factors into three independent terms (slot, round, elem).
//
// This replaces O(24 × 2^num_vars) table builds + evaluations with
// O(live_slots + N_ROUNDS × STATE_SIZE), roughly a 512× speedup.

/// Direct evaluation of all public-schedule MLEs at a single point `r_prime`.
///
/// Returns `(u_at_r, sigma_dec_at_r, rc_dec_at_r, mds_lane_at_r, sigma_lane_at_r)`.
/// Correctness invariant: each returned value equals the terminal evaluation
/// of the corresponding separable prover schedule.
fn fast_eval_block_schedules(
    rho: &[Block128],
    r_prime: &[Block128],
    live_slots: usize,
) -> (
    Block128,
    Block128,
    Block128,
    [Block128; STATE_SIZE],
    [Block128; STATE_SIZE],
) {
    let num_vars = r_prime.len();
    debug_assert_eq!(rho.len(), num_vars);

    // Split r' / rho into (elem, round, slot) sub-vectors.
    // Bit layout: elem:ELEM_BITS | round:ROUND_BITS | slot:slot_vars
    let r_elem = &r_prime[..ELEM_BITS];
    let r_round = &r_prime[ELEM_BITS..ELEM_BITS + ROUND_BITS];
    let r_slot = &r_prime[ELEM_BITS + ROUND_BITS..];
    let rho_elem = &rho[..ELEM_BITS];
    let rho_round = &rho[ELEM_BITS..ELEM_BITS + ROUND_BITS];
    let rho_slot = &rho[ELEM_BITS + ROUND_BITS..];

    // ---- Precompute small eq tensors (sizes: 4, 128, 2^slot_vars ≤ 2×live_slots) ----
    let eq_elem: Vec<Block128> = eq_ind_partial_eval(r_elem); // size 2^ELEM_BITS = 4
    let eq_round_r: Vec<Block128> = eq_ind_partial_eval(r_round); // size 2^ROUND_BITS = 128
    let eq_r_slot: Vec<Block128> = eq_ind_partial_eval(r_slot); // size 2^slot_vars
    let eq_rho_elem: Vec<Block128> = eq_ind_partial_eval(rho_elem); // size 4
    let eq_rho_round: Vec<Block128> = eq_ind_partial_eval(rho_round); // size 128
    let eq_rho_slot: Vec<Block128> = eq_ind_partial_eval(rho_slot); // size 2^slot_vars

    // ---- live_sum_r = Σ_{s < live_slots} eq(r'_slot, s) ----
    let live_sum_r: Block128 = eq_r_slot[..live_slots]
        .iter()
        .copied()
        .fold(Block128::ZERO, |a, b| a + b);

    // ---- Inner sums over (round, elem) for slot-independent tables ----
    //
    // dec_round(pack(slot, round, elem)) = pack(slot, round-1, elem) for round ≥ 1.
    // For round = 0: prev_round = ROUND_LIMIT-1 ≥ N_ROUNDS → table = 0. Skip.
    let mut sigma_dec_inner = Block128::ZERO;
    let mut rc_dec_inner = Block128::ZERO;
    let mut mds_inner = [Block128::ZERO; STATE_SIZE];
    let mut sigma_round_sum = [Block128::ZERO; STATE_SIZE];

    for (round, eq_r) in eq_round_r
        .iter()
        .copied()
        .enumerate()
        .take(ROUND_LIMIT.min(N_ROUNDS + 1))
        .skip(1)
    {
        let prev = round - 1; // prev_round(round) — always < N_ROUNDS

        for elem in 0..STATE_SIZE {
            let eq_re = eq_r * eq_elem[elem];

            // sigma_dec: σ(prev, elem)
            sigma_dec_inner += eq_re * sigma_at(prev, elem);

            // rc_dec: RC[elem][prev] (zero on partial rounds, elem > 0)
            let is_partial = (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&prev);
            if !is_partial || elem == 0 {
                rc_dec_inner += eq_re * Block128::from(ROUND_CONSTANTS[elem][prev]);
            }

            // mds_lane_dec[j]: mds_coeff(prev, elem, j) for each output lane j
            for (j, inner) in mds_inner.iter_mut().enumerate().take(STATE_SIZE) {
                *inner += eq_re * mds_coeff_dyn(prev, elem, j);
            }
        }

        // sigma_lane_dec[j]: σ(prev, j) × eq_round[round] × Σ_e eq_elem[e]
        // Σ_e eq_elem[e] = 1 (sum over all 2^ELEM_BITS Boolean vertices = 1)
        for (j, sum) in sigma_round_sum.iter_mut().enumerate().take(STATE_SIZE) {
            *sum += eq_r * sigma_at(prev, j);
        }
    }

    let sigma_dec_at_r = live_sum_r * sigma_dec_inner;
    let rc_dec_at_r = live_sum_r * rc_dec_inner;
    let mds_lane_at_r = mds_inner.map(|v| live_sum_r * v);
    let sigma_lane_at_r = sigma_round_sum.map(|v| live_sum_r * v);

    // ---- u_MLE: factors into (slot) × (round) × (elem) ----
    //
    // u(y) = eq(rho, dec_round(y)) × 1[slot<live ∧ round≥1]
    //       = eq_slot(rho_s, s) × eq_round(rho_r, round-1) × eq_elem(rho_e, elem)
    //         × 1[slot<live ∧ round≥1]
    //
    // u_MLE(r') = slot_factor × round_factor × elem_factor
    //
    // slot_factor  = Σ_{s<live} eq(rho_slot, s) × eq(r'_slot, s)  — O(live_slots)
    // round_factor = Σ_{r=1}^{N_ROUNDS} eq(rho_round, r-1) × eq(r'_round, r)  — O(N_ROUNDS)
    // elem_factor  = Σ_{e<STATE_SIZE} eq(rho_elem, e) × eq(r'_elem, e)  — O(4)

    let u_slot_factor: Block128 = (0..live_slots)
        .map(|s| eq_rho_slot[s] * eq_r_slot[s])
        .fold(Block128::ZERO, |a, b| a + b);

    let u_round_factor: Block128 = (1..ROUND_LIMIT.min(N_ROUNDS + 1))
        .map(|r| eq_rho_round[r - 1] * eq_round_r[r])
        .fold(Block128::ZERO, |a, b| a + b);

    let u_elem_factor: Block128 = (0..STATE_SIZE)
        .map(|e| eq_rho_elem[e] * eq_elem[e])
        .fold(Block128::ZERO, |a, b| a + b);

    let u_at_r = u_slot_factor * u_round_factor * u_elem_factor;

    (
        u_at_r,
        sigma_dec_at_r,
        rc_dec_at_r,
        mds_lane_at_r,
        sigma_lane_at_r,
    )
}

#[cfg(test)]
fn project_lane_dec_flat_dyn(src: &[Block128], lane: usize) -> Vec<u128> {
    use rayon::prelude::*;
    let n = src.len();
    let elem_mask = (1 << ELEM_BITS) - 1;
    (0..n)
        .into_par_iter()
        .map(|y| {
            let row_base = y & !elem_mask;
            tower_to_flat_u128(src[dec_round_dyn(row_base | lane)].to_u128())
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Unified sumcheck (dynamic-size variant)
// ---------------------------------------------------------------------------

/// Output of the block-level unified spine sumcheck.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BlockSpineUnifiedProof {
    pub round_polys: Vec<CompressedRoundPolynomial<Block128>>,
    pub s_in_dec_at_r: Block128,
    pub s_out_dec_at_r: Block128,
    pub state_dec_at_r: Block128,
    pub state_at_r: Block128,
    pub s_out_lane_dec_at_r: [Block128; STATE_SIZE],
    pub state_lane_dec_at_r: [Block128; STATE_SIZE],
}

/// Verifier reduction from the block spine unified sumcheck.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockSpineUnifiedReduction {
    pub r_prime: Vec<Block128>,
    pub s_in_dec_at_r: Block128,
    pub s_out_dec_at_r: Block128,
    pub state_dec_at_r: Block128,
    pub state_at_r: Block128,
    pub s_out_lane_dec_at_r: [Block128; STATE_SIZE],
    pub state_lane_dec_at_r: [Block128; STATE_SIZE],
    pub beta: Block128,
    pub gamma: Block128,
}

/// Public schedules factor over `(slot, round || elem)`.  Keeping the two
/// factors instead of their tensor product is important at the production
/// m22 shape: the largest factor has one entry per slot rather than one entry
/// per cell.
struct BlockPublicFlatSchedules {
    live_slot: Vec<u128>,
    u_slot: Vec<u128>,
    u_inner: Vec<u128>,
    sigma_dec_inner: Vec<u128>,
    rc_dec_inner: Vec<u128>,
    mds_lane_dec_inner: [Vec<u128>; STATE_SIZE],
    sigma_lane_dec_inner: [Vec<u128>; STATE_SIZE],
}

/// Internal table bundle for the block-level sumcheck (flat basis for hw
/// acceleration).  Only the four actual witness columns are materialized.
/// Public schedules are separable, while lane projections are views over the
/// two corresponding witness columns.
struct BlockUnifiedFlatTables {
    public: BlockPublicFlatSchedules,
    s_in_dec: Vec<u128>,
    s_out_dec: Vec<u128>,
    state_dec: Vec<u128>,
    state: Vec<u128>,
    // Once the slot and round variables have been fixed, these are the four
    // lane values.  The lane MLEs are constant in the remaining y.elem vars.
    s_out_lane_claims: Option<[u128; STATE_SIZE]>,
    state_lane_claims: Option<[u128; STATE_SIZE]>,
}

#[inline]
fn vec_to_flat(v: &[Block128]) -> Vec<u128> {
    // Parallel conversion for large tables (dominant for 100-tx blocks: 4M elements).
    use rayon::prelude::*;
    if v.len() >= 4096 {
        v.par_iter()
            .map(|b| tower_to_flat_u128(b.to_u128()))
            .collect()
    } else {
        v.iter().map(|b| tower_to_flat_u128(b.to_u128())).collect()
    }
}

impl BlockPublicFlatSchedules {
    fn new(rho: &[Block128], live_slots: usize, num_vars: usize) -> Self {
        const INNER_BITS: usize = ROUND_BITS + ELEM_BITS;
        const INNER_CELLS: usize = 1 << INNER_BITS;

        debug_assert_eq!(rho.len(), num_vars);
        let slot_cells = 1usize << (num_vars - INNER_BITS);
        let rho_elem = &rho[..ELEM_BITS];
        let rho_round = &rho[ELEM_BITS..INNER_BITS];
        let rho_slot = &rho[INNER_BITS..];
        let eq_rho_elem = eq_ind_partial_eval::<Block128>(rho_elem);
        let eq_rho_round = eq_ind_partial_eval::<Block128>(rho_round);
        let eq_rho_slot = eq_ind_partial_eval::<Block128>(rho_slot);

        let live_slot: Vec<u128> = (0..slot_cells)
            .map(|slot| u128::from(slot < live_slots))
            .collect();
        let u_slot: Vec<u128> = (0..slot_cells)
            .map(|slot| {
                if slot < live_slots {
                    tower_to_flat_u128(eq_rho_slot[slot].to_u128())
                } else {
                    0
                }
            })
            .collect();

        let u_inner = (0..INNER_CELLS)
            .map(|y| {
                let dec_round = round_of_dyn(dec_round_dyn(y));
                if dec_round >= N_ROUNDS {
                    return 0;
                }
                let elem = elem_of_dyn(y);
                tower_to_flat_u128((eq_rho_round[dec_round] * eq_rho_elem[elem]).to_u128())
            })
            .collect();
        let sigma_dec_inner = (0..INNER_CELLS)
            .map(|y| tower_to_flat_u128(sigma_dec_value(1, y).to_u128()))
            .collect();
        let rc_dec_inner = (0..INNER_CELLS)
            .map(|y| {
                let dec_round = round_of_dyn(dec_round_dyn(y));
                if dec_round >= N_ROUNDS {
                    return 0;
                }
                let elem = elem_of_dyn(y);
                let is_partial = (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&dec_round);
                if is_partial && elem != 0 {
                    0
                } else {
                    tower_to_flat_u128(ROUND_CONSTANTS[elem][dec_round])
                }
            })
            .collect();
        let mds_lane_dec_inner = std::array::from_fn(|lane| {
            (0..INNER_CELLS)
                .map(|y| {
                    let dec_round = round_of_dyn(dec_round_dyn(y));
                    if dec_round >= N_ROUNDS {
                        return 0;
                    }
                    let elem = elem_of_dyn(y);
                    tower_to_flat_u128(mds_coeff_dyn(dec_round, elem, lane).to_u128())
                })
                .collect()
        });
        let sigma_lane_dec_inner = std::array::from_fn(|lane| {
            (0..INNER_CELLS)
                .map(|y| {
                    let row_base = y & !(STATE_SIZE - 1);
                    tower_to_flat_u128(sigma_dec_value(1, row_base | lane).to_u128())
                })
                .collect()
        });

        Self {
            live_slot,
            u_slot,
            u_inner,
            sigma_dec_inner,
            rc_dec_inner,
            mds_lane_dec_inner,
            sigma_lane_dec_inner,
        }
    }

    fn fold(&mut self, r_flat: u128) {
        if self.live_slot.len() > 1 {
            fold_flat_inplace(&mut self.live_slot, r_flat);
            fold_flat_inplace(&mut self.u_slot, r_flat);
        } else {
            fold_flat_inplace(&mut self.u_inner, r_flat);
            fold_flat_inplace(&mut self.sigma_dec_inner, r_flat);
            fold_flat_inplace(&mut self.rc_dec_inner, r_flat);
            for lane in 0..STATE_SIZE {
                fold_flat_inplace(&mut self.mds_lane_dec_inner[lane], r_flat);
                fold_flat_inplace(&mut self.sigma_lane_dec_inner[lane], r_flat);
            }
        }
    }

    #[inline(always)]
    fn factored_pair(outer: &[u128], inner: &[u128], i: usize, half: usize) -> [u128; 2] {
        if outer.len() > 1 {
            debug_assert_eq!(outer.len() * inner.len(), half * 2);
            let inner_i = i % inner.len();
            let outer_i = i / inner.len();
            let outer_hi = (i + half) / inner.len();
            let inner_v = inner[inner_i];
            [
                clmul_gcm(outer[outer_i], inner_v),
                clmul_gcm(outer[outer_i] ^ outer[outer_hi], inner_v),
            ]
        } else {
            debug_assert_eq!(inner.len(), half * 2);
            [
                clmul_gcm(outer[0], inner[i]),
                clmul_gcm(outer[0], inner[i] ^ inner[i + half]),
            ]
        }
    }

    #[inline(always)]
    fn round_pairs(&self, i: usize, half: usize) -> BlockPublicRoundPairs {
        BlockPublicRoundPairs {
            u: Self::factored_pair(&self.u_slot, &self.u_inner, i, half),
            sigma_dec: Self::factored_pair(&self.live_slot, &self.sigma_dec_inner, i, half),
            rc_dec: Self::factored_pair(&self.live_slot, &self.rc_dec_inner, i, half),
            mds_lane_dec: std::array::from_fn(|lane| {
                Self::factored_pair(&self.live_slot, &self.mds_lane_dec_inner[lane], i, half)
            }),
            sigma_lane_dec: std::array::from_fn(|lane| {
                Self::factored_pair(&self.live_slot, &self.sigma_lane_dec_inner[lane], i, half)
            }),
        }
    }
}

struct BlockPublicRoundPairs {
    u: [u128; 2],
    sigma_dec: [u128; 2],
    rc_dec: [u128; 2],
    mds_lane_dec: [[u128; 2]; STATE_SIZE],
    sigma_lane_dec: [[u128; 2]; STATE_SIZE],
}

struct BlockRoundPairs {
    public: BlockPublicRoundPairs,
    s_in_dec: [u128; 2],
    s_out_dec: [u128; 2],
    state_dec: [u128; 2],
    state: [u128; 2],
    s_out_lane_dec: [[u128; 2]; STATE_SIZE],
    state_lane_dec: [[u128; 2]; STATE_SIZE],
}

fn build_block_unified_flat_tables(
    mle: &BlockSpineMle,
    rho: &[Block128],
) -> BlockUnifiedFlatTables {
    let public = BlockPublicFlatSchedules::new(rho, mle.live_slots, mle.num_vars);

    // The four full-size tables are independent.  Build them in parallel, but
    // do not overlap this allocation with any full-size public schedule.
    let ((s_in_dec_flat, s_out_dec_flat), (state_dec_flat, state_flat)) = rayon::join(
        || {
            rayon::join(
                || permute_by_dec_flat_dyn(&mle.s_in),
                || permute_by_dec_flat_dyn(&mle.s_out),
            )
        },
        || {
            rayon::join(
                || permute_by_dec_flat_dyn(&mle.state),
                || vec_to_flat(&mle.state),
            )
        },
    );

    BlockUnifiedFlatTables {
        public,
        s_in_dec: s_in_dec_flat,
        s_out_dec: s_out_dec_flat,
        state_dec: state_dec_flat,
        state: state_flat,
        s_out_lane_claims: None,
        state_lane_claims: None,
    }
}

#[inline]
fn fold_flat_inplace(evals: &mut Vec<u128>, r_flat: u128) {
    let half = evals.len() / 2;
    // Parallelize fold for large tables (dominant in later rounds for big blocks).
    if half >= 1024 {
        use rayon::prelude::*;
        let (lo, hi) = evals.split_at_mut(half);
        lo.par_iter_mut().zip(hi.par_iter()).for_each(|(l, &h)| {
            *l ^= clmul_gcm(r_flat, *l ^ h);
        });
    } else {
        for j in 0..half {
            let delta = evals[j] ^ evals[j + half];
            evals[j] ^= clmul_gcm(r_flat, delta);
        }
    }
    evals.truncate(half);
    // `truncate` alone retains the original m22 allocation through the whole
    // proof.  The allocator can normally release the tail in place; even when
    // it must move, the next round operates on half as many elements.
    evals.shrink_to_fit();
}

impl BlockUnifiedFlatTables {
    #[inline]
    fn len(&self) -> usize {
        self.state.len()
    }

    #[inline(always)]
    fn table_pair(table: &[u128], i: usize, half: usize) -> [u128; 2] {
        [table[i], table[i] ^ table[i + half]]
    }

    #[inline(always)]
    fn lane_pair(
        table: &[u128],
        captured: Option<&[u128; STATE_SIZE]>,
        lane: usize,
        i: usize,
        half: usize,
    ) -> [u128; 2] {
        if table.len() > STATE_SIZE {
            let row_mask = !(STATE_SIZE - 1);
            let lo = table[(i & row_mask) | lane];
            let hi = table[((i + half) & row_mask) | lane];
            [lo, lo ^ hi]
        } else if table.len() == STATE_SIZE {
            // The lane projection fixes source.elem=lane and is therefore
            // constant in both remaining y.elem variables.
            [table[lane], 0]
        } else {
            [captured.expect("lane claims captured")[lane], 0]
        }
    }

    #[inline(always)]
    fn round_pairs(&self, i: usize, half: usize) -> BlockRoundPairs {
        BlockRoundPairs {
            public: self.public.round_pairs(i, half),
            s_in_dec: Self::table_pair(&self.s_in_dec, i, half),
            s_out_dec: Self::table_pair(&self.s_out_dec, i, half),
            state_dec: Self::table_pair(&self.state_dec, i, half),
            state: Self::table_pair(&self.state, i, half),
            s_out_lane_dec: std::array::from_fn(|lane| {
                Self::lane_pair(
                    &self.s_out_dec,
                    self.s_out_lane_claims.as_ref(),
                    lane,
                    i,
                    half,
                )
            }),
            state_lane_dec: std::array::from_fn(|lane| {
                Self::lane_pair(
                    &self.state_dec,
                    self.state_lane_claims.as_ref(),
                    lane,
                    i,
                    half,
                )
            }),
        }
    }

    fn fold(&mut self, r_flat: u128) {
        if self.len() == STATE_SIZE && self.s_out_lane_claims.is_none() {
            self.s_out_lane_claims = Some(std::array::from_fn(|j| self.s_out_dec[j]));
            self.state_lane_claims = Some(std::array::from_fn(|j| self.state_dec[j]));
        }
        self.public.fold(r_flat);
        fold_flat_inplace(&mut self.s_in_dec, r_flat);
        fold_flat_inplace(&mut self.s_out_dec, r_flat);
        fold_flat_inplace(&mut self.state_dec, r_flat);
        fold_flat_inplace(&mut self.state, r_flat);
    }

    fn final_claims_tower(&self) -> BlockFinalClaims {
        debug_assert_eq!(self.len(), 1);
        let f = |x: u128| Block128::from(flat_to_tower_u128(x));
        BlockFinalClaims {
            s_in_dec: f(self.s_in_dec[0]),
            s_out_dec: f(self.s_out_dec[0]),
            state_dec: f(self.state_dec[0]),
            state: f(self.state[0]),
            s_out_lane_dec: self
                .s_out_lane_claims
                .expect("lane claims captured before elem folding")
                .map(f),
            state_lane_dec: self
                .state_lane_claims
                .expect("lane claims captured before elem folding")
                .map(f),
        }
    }
}

struct BlockFinalClaims {
    s_in_dec: Block128,
    s_out_dec: Block128,
    state_dec: Block128,
    state: Block128,
    s_out_lane_dec: [Block128; STATE_SIZE],
    state_lane_dec: [Block128; STATE_SIZE],
}

// ---------------------------------------------------------------------------
// Flat-basis monomial helpers (same as spine_unified.rs)
// ---------------------------------------------------------------------------

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

#[inline(always)]
fn poly_scalar_mul_t<const N: usize>(p: &[u128; N], s: u128) -> [u128; N] {
    let mut out = [0u128; N];
    for k in 0..N {
        out[k] = clmul_gcm(s, p[k]);
    }
    out
}

#[inline(always)]
fn pow7_poly_t(a: u128, b: u128) -> [u128; 8] {
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
        a7,
        clmul_gcm(a6, b),
        clmul_gcm(a5, b2),
        clmul_gcm(a4, b3),
        clmul_gcm(a3, b4),
        clmul_gcm(a2, b5),
        clmul_gcm(a, b6),
        b7,
    ]
}

/// Flat-basis monomial-form round polynomial for the block spine.
///
/// Parallelized over the `half` positions via rayon for large tables
/// (dominant cost when num_vars is high for many-tx blocks).
fn compute_block_round_polynomial_flat(
    tabs: &BlockUnifiedFlatTables,
    beta_flat: u128,
    gamma_flat: u128,
) -> RoundPolynomial<Block128> {
    use rayon::prelude::*;
    let half = tabs.len() / 2;
    const ONE_FLAT: u128 = 1u128;

    // Parallel reduce: each position i contributes independently to acc via XOR.
    let acc: [u128; BLOCK_SPINE_ROUND_DEGREE + 1] = if half >= 256 {
        (0..half)
            .into_par_iter()
            .fold(
                || [0u128; BLOCK_SPINE_ROUND_DEGREE + 1],
                |mut local_acc, i| {
                    let pairs = tabs.round_pairs(i, half);
                    let u_p = pairs.public.u;
                    let sg_p = pairs.public.sigma_dec;
                    let rc_p = pairs.public.rc_dec;
                    let si_p = pairs.s_in_dec;
                    let so_p = pairs.s_out_dec;
                    let st_p = pairs.state_dec;
                    let stmain_p = pairs.state;

                    // Q1(t) = sg(t) * si(t)^7 + so(t) + si(t) + sg(t) * si(t)
                    let si7_p: [u128; 8] = pow7_poly_t(si_p[0], si_p[1]);
                    let sg_si7_p: [u128; 9] = poly_mul_t::<2, 8, 9>(&sg_p, &si7_p);
                    let sg_si_p: [u128; 3] = poly_mul_t::<2, 2, 3>(&sg_p, &si_p);
                    let mut q1_p = [0u128; 9];
                    q1_p.copy_from_slice(&sg_si7_p);
                    q1_p[0] ^= so_p[0] ^ si_p[0] ^ sg_si_p[0];
                    q1_p[1] ^= so_p[1] ^ si_p[1] ^ sg_si_p[1];
                    q1_p[2] ^= sg_si_p[2];

                    // Q1'(t) = sg(t) * (si(t) + st_dec(t) + rc(t))
                    let inner_p: [u128; 2] =
                        [si_p[0] ^ st_p[0] ^ rc_p[0], si_p[1] ^ st_p[1] ^ rc_p[1]];
                    let q1p_p: [u128; 3] = poly_mul_t::<2, 2, 3>(&sg_p, &inner_p);

                    // Q2(t) = st_main(t) + sum_j m_j(t) * pi_j(t)
                    let mut q2_p = [0u128; 4];
                    q2_p[0] ^= stmain_p[0];
                    q2_p[1] ^= stmain_p[1];
                    for j in 0..STATE_SIZE {
                        let m_p = pairs.public.mds_lane_dec[j];
                        let sgl_p = pairs.public.sigma_lane_dec[j];
                        let sol_p = pairs.s_out_lane_dec[j];
                        let stl_p = pairs.state_lane_dec[j];
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

                    // q(t) = Q1(t) + beta * Q1'(t) + gamma * Q2(t)
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

                    // F_i(t) = u(t) * q(t) -> deg-9
                    let f_p: [u128; 10] = poly_mul_t::<2, 9, 10>(&u_p, &q_p);
                    for k in 0..=BLOCK_SPINE_ROUND_DEGREE {
                        local_acc[k] ^= f_p[k];
                    }
                    local_acc
                },
            )
            .reduce(
                || [0u128; BLOCK_SPINE_ROUND_DEGREE + 1],
                |mut a, b| {
                    for k in 0..=BLOCK_SPINE_ROUND_DEGREE {
                        a[k] ^= b[k];
                    }
                    a
                },
            )
    } else {
        // Small table: serial loop (no rayon overhead for tiny blocks).
        let mut acc = [0u128; BLOCK_SPINE_ROUND_DEGREE + 1];
        for i in 0..half {
            let pairs = tabs.round_pairs(i, half);
            let u_p = pairs.public.u;
            let sg_p = pairs.public.sigma_dec;
            let rc_p = pairs.public.rc_dec;
            let si_p = pairs.s_in_dec;
            let so_p = pairs.s_out_dec;
            let st_p = pairs.state_dec;
            let stmain_p = pairs.state;
            let si7_p: [u128; 8] = pow7_poly_t(si_p[0], si_p[1]);
            let sg_si7_p: [u128; 9] = poly_mul_t::<2, 8, 9>(&sg_p, &si7_p);
            let sg_si_p: [u128; 3] = poly_mul_t::<2, 2, 3>(&sg_p, &si_p);
            let mut q1_p = [0u128; 9];
            q1_p.copy_from_slice(&sg_si7_p);
            q1_p[0] ^= so_p[0] ^ si_p[0] ^ sg_si_p[0];
            q1_p[1] ^= so_p[1] ^ si_p[1] ^ sg_si_p[1];
            q1_p[2] ^= sg_si_p[2];
            let inner_p: [u128; 2] = [si_p[0] ^ st_p[0] ^ rc_p[0], si_p[1] ^ st_p[1] ^ rc_p[1]];
            let q1p_p: [u128; 3] = poly_mul_t::<2, 2, 3>(&sg_p, &inner_p);
            let mut q2_p = [0u128; 4];
            q2_p[0] ^= stmain_p[0];
            q2_p[1] ^= stmain_p[1];
            for j in 0..STATE_SIZE {
                let m_p = pairs.public.mds_lane_dec[j];
                let sgl_p = pairs.public.sigma_lane_dec[j];
                let sol_p = pairs.s_out_lane_dec[j];
                let stl_p = pairs.state_lane_dec[j];
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
            let f_p: [u128; 10] = poly_mul_t::<2, 9, 10>(&u_p, &q_p);
            for k in 0..=BLOCK_SPINE_ROUND_DEGREE {
                acc[k] ^= f_p[k];
            }
        }
        acc
    };

    let coeffs_tower: Vec<Block128> = acc
        .iter()
        .map(|&c| Block128::from(flat_to_tower_u128(c)))
        .collect();
    RoundPolynomial::from_coeffs(coeffs_tower)
}

/// Prove the unified block spine sumcheck (flat-basis hot path).
pub fn prove_block_spine_unified<T: FiatShamir<Block128>>(
    mle: &BlockSpineMle,
    channel: &mut T,
) -> (BlockSpineUnifiedProof, Vec<Block128>) {
    let num_vars = mle.num_vars;
    let n_instances = mle.live_slots / N_SPINE_SLOTS;
    let mut profiler =
        BlockSpineProfiler::new("block_spine_unified", n_instances, mle.live_slots, num_vars);

    let rho: Vec<Block128> = (0..num_vars).map(|_| channel.squeeze()).collect();
    let beta = channel.squeeze();
    let gamma = channel.squeeze();
    profiler.phase("challenge_squeeze");

    let mut tabs = build_block_unified_flat_tables(mle, &rho);
    let beta_flat = tower_to_flat_u128(beta.to_u128());
    let gamma_flat = tower_to_flat_u128(gamma.to_u128());
    profiler.phase("build_flat_tables");

    let mut round_polys = Vec::with_capacity(num_vars);
    let mut r_prime = vec![Block128::ZERO; num_vars];
    let mut round_poly_total = Duration::ZERO;
    let mut transcript_total = Duration::ZERO;
    let mut fold_total = Duration::ZERO;

    for round in 0..num_vars {
        let t0 = profiler.enabled().then(Instant::now);
        let poly = compute_block_round_polynomial_flat(&tabs, beta_flat, gamma_flat);
        if let Some(t0) = t0 {
            round_poly_total += t0.elapsed();
        }

        let t0 = profiler.enabled().then(Instant::now);
        let wire = CompressedRoundPolynomial::compress(&poly);
        for &c in &wire.coeffs_no_linear {
            channel.absorb(c);
        }
        let challenge = channel.squeeze();
        let challenge_flat = tower_to_flat_u128(challenge.to_u128());
        if let Some(t0) = t0 {
            transcript_total += t0.elapsed();
        }

        let t0 = profiler.enabled().then(Instant::now);
        tabs.fold(challenge_flat);
        if let Some(t0) = t0 {
            fold_total += t0.elapsed();
        }

        r_prime[num_vars - 1 - round] = challenge;
        round_polys.push(wire);
    }
    profiler.record("round_polynomials_total", round_poly_total);
    profiler.record("round_transcript_total", transcript_total);
    profiler.record("round_folds_total", fold_total);
    profiler.phase("sumcheck_rounds_wall");

    let claims = tabs.final_claims_tower();

    channel.absorb(claims.s_in_dec);
    channel.absorb(claims.s_out_dec);
    channel.absorb(claims.state_dec);
    channel.absorb(claims.state);
    for v in &claims.s_out_lane_dec {
        channel.absorb(*v);
    }
    for v in &claims.state_lane_dec {
        channel.absorb(*v);
    }
    profiler.phase("final_claim_absorb");

    let proof = BlockSpineUnifiedProof {
        round_polys,
        s_in_dec_at_r: claims.s_in_dec,
        s_out_dec_at_r: claims.s_out_dec,
        state_dec_at_r: claims.state_dec,
        state_at_r: claims.state,
        s_out_lane_dec_at_r: claims.s_out_lane_dec,
        state_lane_dec_at_r: claims.state_lane_dec,
    };
    profiler.phase("proof_assembly");
    profiler.finish();
    (proof, r_prime)
}

/// Verify the unified block spine sumcheck.
pub fn verify_block_spine_unified<T: FiatShamir<Block128>>(
    proof: &BlockSpineUnifiedProof,
    num_vars: usize,
    live_slots: usize,
    channel: &mut T,
) -> Option<BlockSpineUnifiedReduction> {
    if proof.round_polys.len() != num_vars {
        return None;
    }
    for p in &proof.round_polys {
        if p.degree() != BLOCK_SPINE_ROUND_DEGREE {
            return None;
        }
    }

    let rho: Vec<Block128> = (0..num_vars).map(|_| channel.squeeze()).collect();
    let beta = channel.squeeze();
    let gamma = channel.squeeze();

    let mut expected = Block128::ZERO;
    let mut r_prime = vec![Block128::ZERO; num_vars];

    for (round, wire) in proof.round_polys.iter().enumerate() {
        // The reconstruction seeds the linear coefficient from the
        // running claim, so `p(0) + p(1) = expected` holds by
        // construction — no explicit sum check.
        let poly = wire.reconstruct(expected);
        for &c in &wire.coeffs_no_linear {
            channel.absorb(c);
        }
        let challenge = channel.squeeze();
        expected = poly.evaluate(challenge);
        r_prime[num_vars - 1 - round] = challenge;
    }

    // Recompute public schedules at r' using direct point evaluation.
    // O(live_slots + N_ROUNDS × STATE_SIZE) instead of O(24 × 2^num_vars).
    let (u_at_r, sigma_dec_at_r, rc_dec_at_r, mds_lane_at_r, sigma_lane_at_r) =
        fast_eval_block_schedules(&rho, &r_prime, live_slots);

    // Reassemble constraint at r'.
    let q_c1 = sigma_dec_at_r * pow7_block128(proof.s_in_dec_at_r)
        + proof.s_out_dec_at_r
        + proof.s_in_dec_at_r
        + sigma_dec_at_r * proof.s_in_dec_at_r;
    let q_c1p = sigma_dec_at_r * (proof.s_in_dec_at_r + proof.state_dec_at_r + rc_dec_at_r);
    let mut c2_sum = proof.state_at_r;
    for j in 0..STATE_SIZE {
        let pi_j = sigma_lane_at_r[j] * proof.s_out_lane_dec_at_r[j]
            + (Block128::ONE + sigma_lane_at_r[j]) * proof.state_lane_dec_at_r[j];
        c2_sum += mds_lane_at_r[j] * pi_j;
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

    Some(BlockSpineUnifiedReduction {
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
// Shift gadget (dynamic-size variant)
// ---------------------------------------------------------------------------

/// Shift gadget degree.
pub const BLOCK_SPINE_SHIFT_DEGREE: usize = 2;

/// Shift proof for the block spine.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BlockSpineShiftProof {
    pub round_polys: Vec<CompressedRoundPolynomial<Block128>>,
    pub s_in_at_r2: Block128,
    pub s_out_at_r2: Block128,
    pub state_at_r2: Block128,
}

/// Shift reduction output.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockSpineShiftReduction {
    pub r_double_prime: Vec<Block128>,
    pub s_in_at_r2: Block128,
    pub s_out_at_r2: Block128,
    pub state_at_r2: Block128,
}

/// Combined Kill-Shot proof for block spine.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BlockSpineKillShotProof {
    pub main: BlockSpineUnifiedProof,
    pub shift: BlockSpineShiftProof,
}

struct BlockCombinedWeights {
    w_sin: Vec<u128>,
    w_sout: Vec<u128>,
    w_state: Vec<u128>,
}

struct BlockWeightsAtPoint {
    w_sin: Block128,
    w_sout: Block128,
    w_state: Block128,
}

fn build_block_combined_weights(
    r_prime: &[Block128],
    delta: Block128,
    num_vars: usize,
) -> BlockCombinedWeights {
    let n_cells = 1usize << num_vars;

    let rp_elem = &r_prime[0..ELEM_BITS];
    let rp_round = &r_prime[ELEM_BITS..ELEM_BITS + ROUND_BITS];
    let rp_slot = &r_prime[ELEM_BITS + ROUND_BITS..num_vars];

    let eq_slot_tab = vec_to_flat(&eq_ind_partial_eval::<Block128>(rp_slot));
    let eq_elem_tab = vec_to_flat(&eq_ind_partial_eval::<Block128>(rp_elem));

    let n_rounds = 1usize << ROUND_BITS;

    let eq_round_tab = vec_to_flat(&eq_ind_partial_eval::<Block128>(rp_round));
    let mut eq_round_at_inc = vec![0u128; n_rounds];
    for (round_x, slot) in eq_round_at_inc.iter_mut().enumerate().take(n_rounds) {
        let inc = (round_x + 1) & (n_rounds - 1);
        *slot = eq_round_tab[inc];
    }

    use rayon::prelude::*;

    let d1 = tower_to_flat_u128(delta.to_u128());
    let d2 = clmul_gcm(d1, d1);
    let d3 = clmul_gcm(d2, d1);
    let d4 = clmul_gcm(d3, d1);
    let d5 = clmul_gcm(d4, d1);
    let d6 = clmul_gcm(d5, d1);
    let d7 = clmul_gcm(d6, d1);
    let d8 = clmul_gcm(d7, d1);
    let d9 = clmul_gcm(d8, d1);
    let d10 = clmul_gcm(d9, d1);

    let lane_sout = [d3, d4, d5, d6];
    let lane_state = [d7, d8, d9, d10];

    // Directly fill the final combined weight tables. This is algebraically
    // identical to materializing w_dec plus four lane tables, but avoids the
    // scatter_data allocation and four full-size temporary lane vectors.
    let mut w_sin = vec![0u128; n_cells];
    let mut w_sout = vec![0u128; n_cells];
    let mut w_state = vec![0u128; n_cells];
    w_sin
        .par_iter_mut()
        .zip(w_sout.par_iter_mut())
        .zip(w_state.par_iter_mut())
        .enumerate()
        .for_each(|(x, ((sin, sout), state))| {
            let slot = slot_of_dyn(x);
            let round = round_of_dyn(x);
            let elem = elem_of_dyn(x);
            let es_er = clmul_gcm(eq_slot_tab[slot], eq_round_at_inc[round]);
            let w_dec = clmul_gcm(es_er, eq_elem_tab[elem]);
            *sin = w_dec;
            *sout = clmul_gcm(d1, w_dec) ^ clmul_gcm(lane_sout[elem], es_er);
            *state = clmul_gcm(d2, w_dec) ^ clmul_gcm(lane_state[elem], es_er);
        });

    BlockCombinedWeights {
        w_sin,
        w_sout,
        w_state,
    }
}

fn block_combined_target(red: &BlockSpineUnifiedReduction, delta: Block128) -> Block128 {
    let d0 = Block128::ONE;
    let d1 = delta;
    let d2 = d1 * delta;
    let mut acc = d0 * red.s_in_dec_at_r + d1 * red.s_out_dec_at_r + d2 * red.state_dec_at_r;
    let mut p = d2 * delta;
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

fn block_combined_weights_at_point(
    r_prime: &[Block128],
    delta: Block128,
    r2: &[Block128],
    num_vars: usize,
) -> BlockWeightsAtPoint {
    let rp_elem = &r_prime[0..ELEM_BITS];
    let rp_round = &r_prime[ELEM_BITS..ELEM_BITS + ROUND_BITS];
    let rp_slot = &r_prime[ELEM_BITS + ROUND_BITS..num_vars];
    let r2_elem = &r2[0..ELEM_BITS];
    let r2_round = &r2[ELEM_BITS..ELEM_BITS + ROUND_BITS];
    let r2_slot = &r2[ELEM_BITS + ROUND_BITS..num_vars];

    let eq_slot = eq_ind(rp_slot, r2_slot);
    let eq_elem = eq_ind(rp_elem, r2_elem);

    let n_rounds = 1usize << ROUND_BITS;
    let eq_rp_round_tab = eq_ind_partial_eval::<Block128>(rp_round);
    let mut tab = vec![Block128::ZERO; n_rounds];
    for (round_x, slot) in tab.iter_mut().enumerate().take(n_rounds) {
        let inc = (round_x + 1) & (n_rounds - 1);
        *slot = eq_rp_round_tab[inc];
    }
    let g_round = evaluate_slice(&tab, r2_round);

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

    BlockWeightsAtPoint {
        w_sin,
        w_sout,
        w_state,
    }
}

/// Prove the shift gadget: reduces 11 dec-permuted claims to 3 direct
/// claims on the original columns using combined weight tables.
pub fn prove_block_spine_shift<T: FiatShamir<Block128>>(
    mle: &BlockSpineMle,
    r_prime: &[Block128],
    _main_reduction: &BlockSpineUnifiedReduction,
    channel: &mut T,
) -> (BlockSpineShiftProof, Vec<Block128>) {
    let num_vars = mle.num_vars;
    debug_assert_eq!(r_prime.len(), num_vars);
    let n_instances = mle.live_slots / N_SPINE_SLOTS;
    let mut profiler =
        BlockSpineProfiler::new("block_spine_shift", n_instances, mle.live_slots, num_vars);

    let delta = channel.squeeze();
    profiler.phase("delta_squeeze");
    let weights = build_block_combined_weights(r_prime, delta, num_vars);
    profiler.phase("build_combined_weights");

    // Degree-2 sumcheck in flat basis for hw acceleration.
    // Witness tables still need conversion; combined weights are built directly
    // in flat basis by `build_block_combined_weights`.
    let ((mut f_sin, mut f_sout), mut f_state) = rayon::join(
        || rayon::join(|| vec_to_flat(&mle.s_in), || vec_to_flat(&mle.s_out)),
        || vec_to_flat(&mle.state),
    );
    let mut f_wsin = weights.w_sin;
    let mut f_wsout = weights.w_sout;
    let mut f_wstate = weights.w_state;
    profiler.phase("convert_tables_to_flat");

    let mut round_polys = Vec::with_capacity(num_vars);
    let mut r_double_prime = vec![Block128::ZERO; num_vars];
    let mut round_poly_total = Duration::ZERO;
    let mut transcript_total = Duration::ZERO;
    let mut fold_total = Duration::ZERO;

    for round in 0..num_vars {
        let half = f_sin.len() / 2;
        let t0 = profiler.enabled().then(Instant::now);
        // Parallel reduction over positions (same pattern as compute_block_round_polynomial_flat).
        let acc: [u128; BLOCK_SPINE_SHIFT_DEGREE + 1] = if half >= 256 {
            use rayon::prelude::*;
            (0..half)
                .into_par_iter()
                .fold(
                    || [0u128; BLOCK_SPINE_SHIFT_DEGREE + 1],
                    |mut local, i| {
                        let sin_p: [u128; 2] = [f_sin[i], f_sin[i] ^ f_sin[i + half]];
                        let sout_p: [u128; 2] = [f_sout[i], f_sout[i] ^ f_sout[i + half]];
                        let st_p: [u128; 2] = [f_state[i], f_state[i] ^ f_state[i + half]];
                        let wsin_p: [u128; 2] = [f_wsin[i], f_wsin[i] ^ f_wsin[i + half]];
                        let wsout_p: [u128; 2] = [f_wsout[i], f_wsout[i] ^ f_wsout[i + half]];
                        let wst_p: [u128; 2] = [f_wstate[i], f_wstate[i] ^ f_wstate[i + half]];
                        let t1: [u128; 3] = poly_mul_t::<2, 2, 3>(&wsin_p, &sin_p);
                        let t2: [u128; 3] = poly_mul_t::<2, 2, 3>(&wsout_p, &sout_p);
                        let t3: [u128; 3] = poly_mul_t::<2, 2, 3>(&wst_p, &st_p);
                        local[0] ^= t1[0] ^ t2[0] ^ t3[0];
                        local[1] ^= t1[1] ^ t2[1] ^ t3[1];
                        local[2] ^= t1[2] ^ t2[2] ^ t3[2];
                        local
                    },
                )
                .reduce(
                    || [0u128; BLOCK_SPINE_SHIFT_DEGREE + 1],
                    |mut a, b| {
                        for k in 0..=BLOCK_SPINE_SHIFT_DEGREE {
                            a[k] ^= b[k];
                        }
                        a
                    },
                )
        } else {
            let mut acc = [0u128; BLOCK_SPINE_SHIFT_DEGREE + 1];
            for i in 0..half {
                let sin_p: [u128; 2] = [f_sin[i], f_sin[i] ^ f_sin[i + half]];
                let sout_p: [u128; 2] = [f_sout[i], f_sout[i] ^ f_sout[i + half]];
                let st_p: [u128; 2] = [f_state[i], f_state[i] ^ f_state[i + half]];
                let wsin_p: [u128; 2] = [f_wsin[i], f_wsin[i] ^ f_wsin[i + half]];
                let wsout_p: [u128; 2] = [f_wsout[i], f_wsout[i] ^ f_wsout[i + half]];
                let wst_p: [u128; 2] = [f_wstate[i], f_wstate[i] ^ f_wstate[i + half]];
                let t1: [u128; 3] = poly_mul_t::<2, 2, 3>(&wsin_p, &sin_p);
                let t2: [u128; 3] = poly_mul_t::<2, 2, 3>(&wsout_p, &sout_p);
                let t3: [u128; 3] = poly_mul_t::<2, 2, 3>(&wst_p, &st_p);
                acc[0] ^= t1[0] ^ t2[0] ^ t3[0];
                acc[1] ^= t1[1] ^ t2[1] ^ t3[1];
                acc[2] ^= t1[2] ^ t2[2] ^ t3[2];
            }
            acc
        };
        if let Some(t0) = t0 {
            round_poly_total += t0.elapsed();
        }

        let coeffs_tower: Vec<Block128> = acc
            .iter()
            .map(|&c| Block128::from(flat_to_tower_u128(c)))
            .collect();
        let wire = CompressedRoundPolynomial::compress(&RoundPolynomial::from_coeffs(coeffs_tower));
        let t0 = profiler.enabled().then(Instant::now);
        for &c in &wire.coeffs_no_linear {
            channel.absorb(c);
        }
        let challenge = channel.squeeze();
        let challenge_flat = tower_to_flat_u128(challenge.to_u128());
        if let Some(t0) = t0 {
            transcript_total += t0.elapsed();
        }

        let t0 = profiler.enabled().then(Instant::now);
        fold_flat_inplace(&mut f_sin, challenge_flat);
        fold_flat_inplace(&mut f_sout, challenge_flat);
        fold_flat_inplace(&mut f_state, challenge_flat);
        fold_flat_inplace(&mut f_wsin, challenge_flat);
        fold_flat_inplace(&mut f_wsout, challenge_flat);
        fold_flat_inplace(&mut f_wstate, challenge_flat);
        if let Some(t0) = t0 {
            fold_total += t0.elapsed();
        }
        r_double_prime[num_vars - 1 - round] = challenge;
        round_polys.push(wire);
    }
    profiler.record("round_polynomials_total", round_poly_total);
    profiler.record("round_transcript_total", transcript_total);
    profiler.record("round_folds_total", fold_total);
    profiler.phase("sumcheck_rounds_wall");

    debug_assert_eq!(f_sin.len(), 1);
    let s_in_at_r2 = Block128::from(flat_to_tower_u128(f_sin[0]));
    let s_out_at_r2 = Block128::from(flat_to_tower_u128(f_sout[0]));
    let state_at_r2 = Block128::from(flat_to_tower_u128(f_state[0]));

    channel.absorb(s_in_at_r2);
    channel.absorb(s_out_at_r2);
    channel.absorb(state_at_r2);
    profiler.phase("final_claim_absorb");

    let proof = BlockSpineShiftProof {
        round_polys,
        s_in_at_r2,
        s_out_at_r2,
        state_at_r2,
    };
    profiler.phase("proof_assembly");
    profiler.finish();
    (proof, r_double_prime)
}

/// Verify the shift gadget for block spine.
pub fn verify_block_spine_shift<T: FiatShamir<Block128>>(
    proof: &BlockSpineShiftProof,
    main_reduction: &BlockSpineUnifiedReduction,
    num_vars: usize,
    channel: &mut T,
) -> Option<BlockSpineShiftReduction> {
    if proof.round_polys.len() != num_vars {
        return None;
    }
    for p in &proof.round_polys {
        if p.degree() != BLOCK_SPINE_SHIFT_DEGREE {
            return None;
        }
    }

    let delta = channel.squeeze();
    let expected_target = block_combined_target(main_reduction, delta);

    let mut expected = expected_target;
    let mut r_double_prime = vec![Block128::ZERO; num_vars];

    for (round, wire) in proof.round_polys.iter().enumerate() {
        // Linear coefficient reconstructed from the running claim — the
        // per-round sum check holds by construction.
        let poly = wire.reconstruct(expected);
        for &c in &wire.coeffs_no_linear {
            channel.absorb(c);
        }
        let challenge = channel.squeeze();
        expected = poly.evaluate(challenge);
        r_double_prime[num_vars - 1 - round] = challenge;
    }

    let w =
        block_combined_weights_at_point(&main_reduction.r_prime, delta, &r_double_prime, num_vars);
    let claimed =
        w.w_sin * proof.s_in_at_r2 + w.w_sout * proof.s_out_at_r2 + w.w_state * proof.state_at_r2;
    if expected != claimed {
        return None;
    }

    channel.absorb(proof.s_in_at_r2);
    channel.absorb(proof.s_out_at_r2);
    channel.absorb(proof.state_at_r2);

    Some(BlockSpineShiftReduction {
        r_double_prime,
        s_in_at_r2: proof.s_in_at_r2,
        s_out_at_r2: proof.s_out_at_r2,
        state_at_r2: proof.state_at_r2,
    })
}

// ---------------------------------------------------------------------------
// Full block spine Kill-Shot orchestration
// ---------------------------------------------------------------------------

/// Complete proof for the unified block spine.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BlockSpineProof {
    pub kill_shot: BlockSpineKillShotProof,
    pub tx_hash_pins: LinearEvalProof,
    pub batch: MultiBatchEvalProof,
    pub num_vars: usize,
    pub live_slots: usize,
}

impl BlockSpineProof {
    pub fn byte_len(&self) -> usize {
        let main_polys = self.kill_shot.main.round_polys.len() * BLOCK_SPINE_ROUND_DEGREE * 16;
        let shift_polys = self.kill_shot.shift.round_polys.len() * BLOCK_SPINE_SHIFT_DEGREE * 16;
        let main_finals = 12 * 16;
        let shift_finals = 3 * 16;
        main_polys
            + shift_polys
            + main_finals
            + shift_finals
            + self.tx_hash_pins.byte_len()
            + self.batch.byte_len()
    }
}

/// Reductions delivered to the composed batch relation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockSpineReductions {
    pub state: BatchEvalReduction,
    pub sin: BatchEvalReduction,
    pub sout: BatchEvalReduction,
}

fn tx_hash_pin_claims(
    n_instances: usize,
    tx_body_hashes: &[[Block128; 2]],
    num_vars: usize,
) -> Vec<LinearEvalClaim> {
    let mut claims = Vec::with_capacity(n_instances * 2);
    for (tx_idx, tx_hash) in tx_body_hashes.iter().enumerate().take(n_instances) {
        let wrap_slot = tx_idx * N_SPINE_SLOTS + (N_SPINE_SLOTS - 1);
        for lane in 0..2 {
            claims.push(LinearEvalClaim {
                terms: vec![LinearEvalTerm {
                    point: block_spine_state_point(num_vars, wrap_slot, N_ROUNDS, lane),
                    coeff: Block128::ONE,
                }],
                value: tx_hash[lane],
            });
        }
    }
    claims
}

/// Prove the unified block spine Kill-Shot over N*31 slots.
///
/// The caller provides the already-built `BlockSpineMle`. This keeps the block
/// prover honest-by-construction: the GKR proof is derived from the same spine
/// MLE whose `state` column is committed into the production PCS opening.
pub fn prove_block_spine_killshot<T: FiatShamir<Block128>>(
    n_instances: usize,
    mle: &BlockSpineMle,
    all_tx_body_hashes: &[[Block128; 2]],
    channel: &mut T,
) -> (BlockSpineProof, BlockSpineReductions) {
    assert_eq!(all_tx_body_hashes.len(), n_instances);
    let live_slots = n_instances * N_SPINE_SLOTS;
    let num_vars = num_vars_for(live_slots);
    assert_eq!(mle.live_slots, live_slots);
    assert_eq!(mle.num_vars, num_vars);
    let mut profiler =
        BlockSpineProfiler::new("block_spine_killshot", n_instances, live_slots, num_vars);

    // Absorb all tx_body_hashes into the channel (binds block contents).
    for hash in all_tx_body_hashes {
        channel.absorb(hash[0]);
        channel.absorb(hash[1]);
    }
    profiler.phase("absorb_tx_body_hashes");

    // (1) Main unified sumcheck.
    let (main, r_prime) = prove_block_spine_unified(mle, channel);
    profiler.phase("unified_sumcheck");

    let main_red = BlockSpineUnifiedReduction {
        r_prime: r_prime.clone(),
        s_in_dec_at_r: main.s_in_dec_at_r,
        s_out_dec_at_r: main.s_out_dec_at_r,
        state_dec_at_r: main.state_dec_at_r,
        state_at_r: main.state_at_r,
        s_out_lane_dec_at_r: main.s_out_lane_dec_at_r,
        state_lane_dec_at_r: main.state_lane_dec_at_r,
        beta: Block128::ZERO, // filled by verifier
        gamma: Block128::ZERO,
    };
    profiler.phase("main_reduction_assembly");

    // (2) Shift gadget.
    let (shift, r_double_prime) = prove_block_spine_shift(mle, &r_prime, &main_red, channel);
    profiler.phase("shift_gadget");

    let tx_hash_pin_claims = tx_hash_pin_claims(n_instances, all_tx_body_hashes, mle.num_vars);
    let (tx_hash_pins, tx_hash_pin_red) = prove_linear_eval_prebound(
        &mle.state,
        &tx_hash_pin_claims,
        BLOCK_SPINE_TX_HASH_PIN_TAG,
        channel,
    );
    profiler.phase("tx_hash_pins");

    let state_claims = vec![
        EvalClaim {
            point: r_prime.clone(),
            value: main.state_at_r,
        },
        EvalClaim {
            point: r_double_prime.clone(),
            value: shift.state_at_r2,
        },
        EvalClaim {
            point: tx_hash_pin_red.point,
            value: tx_hash_pin_red.value,
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
    profiler.phase("multi_batch_eval");

    let proof = BlockSpineProof {
        kill_shot: BlockSpineKillShotProof { main, shift },
        tx_hash_pins,
        batch,
        num_vars: mle.num_vars,
        live_slots: mle.live_slots,
    };
    let reductions = BlockSpineReductions {
        state: state_red,
        sin: sin_red,
        sout: sout_red,
    };
    profiler.phase("proof_and_reduction_assembly");
    profiler.finish();
    (proof, reductions)
}

/// Verify the unified block spine Kill-Shot.
pub fn verify_block_spine_killshot<T: FiatShamir<Block128>>(
    proof: &BlockSpineProof,
    n_instances: usize,
    all_tx_body_hashes: &[[Block128; 2]],
    channel: &mut T,
) -> Option<BlockSpineReductions> {
    let expected_live = n_instances * N_SPINE_SLOTS;
    if proof.live_slots != expected_live {
        return None;
    }
    let expected_num_vars = num_vars_for(expected_live);
    if proof.num_vars != expected_num_vars {
        return None;
    }
    if all_tx_body_hashes.len() != n_instances {
        return None;
    }

    // Absorb all tx_body_hashes.
    for hash in all_tx_body_hashes {
        channel.absorb(hash[0]);
        channel.absorb(hash[1]);
    }

    // (1) Verify main unified sumcheck.
    let main_red = verify_block_spine_unified(
        &proof.kill_shot.main,
        proof.num_vars,
        proof.live_slots,
        channel,
    )?;

    // (2) Verify shift gadget.
    let shift_red =
        verify_block_spine_shift(&proof.kill_shot.shift, &main_red, proof.num_vars, channel)?;

    let tx_hash_pin_claims = tx_hash_pin_claims(n_instances, all_tx_body_hashes, proof.num_vars);
    let tx_hash_pin_red = verify_linear_eval_prebound(
        &proof.tx_hash_pins,
        &tx_hash_pin_claims,
        proof.num_vars,
        BLOCK_SPINE_TX_HASH_PIN_TAG,
        channel,
    )?;

    let state_claims = vec![
        EvalClaim {
            point: main_red.r_prime.clone(),
            value: main_red.state_at_r,
        },
        EvalClaim {
            point: shift_red.r_double_prime.clone(),
            value: shift_red.state_at_r2,
        },
        EvalClaim {
            point: tx_hash_pin_red.point,
            value: tx_hash_pin_red.value,
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

    Some(BlockSpineReductions {
        state: state_red,
        sin: sin_red,
        sout: sout_red,
    })
}

/// Discharge all reductions against natively-reconstructed MLE. Test helper.
pub fn discharge_block_spine_reductions_native(
    n_instances: usize,
    all_slot_state_ins: &[[Block128; STATE_SIZE]],
    reductions: &BlockSpineReductions,
) -> bool {
    if all_slot_state_ins.len() != n_instances * N_SPINE_SLOTS {
        return false;
    }
    discharge_block_spine_batch_reductions_from_slot_state_ins_native(
        all_slot_state_ins,
        &reductions.state,
        &reductions.sin,
        &reductions.sout,
    )
}

pub fn discharge_block_spine_batch_reductions_from_slot_state_ins_native(
    slot_state_ins: &[[Block128; STATE_SIZE]],
    state: &BatchEvalReduction,
    sin: &BatchEvalReduction,
    sout: &BatchEvalReduction,
) -> bool {
    if state.point == sin.point && sin.point == sout.point {
        let Some((state_value, sin_value, sout_value)) =
            evaluate_block_spine_columns_from_slot_state_ins(slot_state_ins, &state.point)
        else {
            return false;
        };
        state_value == state.value && sin_value == sin.value && sout_value == sout.value
    } else {
        let Some((state_value, _, _)) =
            evaluate_block_spine_columns_from_slot_state_ins(slot_state_ins, &state.point)
        else {
            return false;
        };
        let Some((_, sin_value, _)) =
            evaluate_block_spine_columns_from_slot_state_ins(slot_state_ins, &sin.point)
        else {
            return false;
        };
        let Some((_, _, sout_value)) =
            evaluate_block_spine_columns_from_slot_state_ins(slot_state_ins, &sout.point)
        else {
            return false;
        };
        state_value == state.value && sin_value == sin.value && sout_value == sout.value
    }
}

pub fn evaluate_block_spine_columns_from_slot_state_ins(
    slot_state_ins: &[[Block128; STATE_SIZE]],
    point: &[Block128],
) -> Option<(Block128, Block128, Block128)> {
    if slot_state_ins.is_empty() {
        return None;
    }
    let num_vars = num_vars_for(slot_state_ins.len());
    if point.len() != num_vars {
        return None;
    }

    let r_elem = &point[..ELEM_BITS];
    let r_round = &point[ELEM_BITS..ELEM_BITS + ROUND_BITS];
    let r_slot = &point[ELEM_BITS + ROUND_BITS..];
    let eq_elem = eq_ind_partial_eval(r_elem);
    let eq_round = eq_ind_partial_eval(r_round);
    let eq_slot = eq_ind_partial_eval(r_slot);

    use rayon::prelude::*;
    let (state, sin, sout) = slot_state_ins
        .par_iter()
        .enumerate()
        .map(|(slot, &state_in)| {
            let slot_weight = eq_slot[slot];
            if slot_weight == Block128::ZERO {
                return (Block128::ZERO, Block128::ZERO, Block128::ZERO);
            }
            accumulate_permutation_columns_at_point(state_in, slot_weight, &eq_round, &eq_elem)
        })
        .reduce(
            || (Block128::ZERO, Block128::ZERO, Block128::ZERO),
            |a, b| (a.0 + b.0, a.1 + b.1, a.2 + b.2),
        );

    Some((state, sin, sout))
}

fn accumulate_permutation_columns_at_point(
    state_in: [Block128; STATE_SIZE],
    slot_weight: Block128,
    eq_round: &[Block128],
    eq_elem: &[Block128],
) -> (Block128, Block128, Block128) {
    let mut state_acc = Block128::ZERO;
    let mut sin_acc = Block128::ZERO;
    let mut sout_acc = Block128::ZERO;
    let mut current = state_in;
    apply_mds_full(&mut current);

    for round in 0..N_ROUNDS {
        let row_weight = slot_weight * eq_round[round];
        accumulate_row(&mut state_acc, current, row_weight, eq_elem);

        match round_kind(round) {
            RoundKind::Full => {
                let mut sin = [Block128::ZERO; STATE_SIZE];
                let mut sout = [Block128::ZERO; STATE_SIZE];
                for lane in 0..STATE_SIZE {
                    sin[lane] = current[lane] + Block128::from(ROUND_CONSTANTS[lane][round]);
                    sout[lane] = pow7_block128(sin[lane]);
                }
                accumulate_row(&mut sin_acc, sin, row_weight, eq_elem);
                accumulate_row(&mut sout_acc, sout, row_weight, eq_elem);
                current = sout;
                apply_mds_full(&mut current);
            }
            RoundKind::Partial => {
                let mut sin = [Block128::ZERO; STATE_SIZE];
                let mut sout = [Block128::ZERO; STATE_SIZE];
                sin[0] = current[0] + Block128::from(ROUND_CONSTANTS[0][round]);
                sout[0] = pow7_block128(sin[0]);
                accumulate_row(&mut sin_acc, sin, row_weight, eq_elem);
                accumulate_row(&mut sout_acc, sout, row_weight, eq_elem);
                current = apply_mds_partial([sout[0], current[1], current[2], current[3]]);
            }
        }
    }

    accumulate_row(
        &mut state_acc,
        current,
        slot_weight * eq_round[N_ROUNDS],
        eq_elem,
    );
    (state_acc, sin_acc, sout_acc)
}

#[inline]
fn accumulate_row(
    acc: &mut Block128,
    row: [Block128; STATE_SIZE],
    row_weight: Block128,
    eq_elem: &[Block128],
) {
    if row_weight == Block128::ZERO {
        return;
    }
    for lane in 0..STATE_SIZE {
        *acc += row_weight * eq_elem[lane] * row[lane];
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{SpineCircuit, SpineInputs};
    use crate::spine_sumcheck::reconstruct_slot_states;
    use noid_poseidon2b::channel::Poseidon2bChannel;

    fn fixture_inputs(seed: u128) -> SpineInputs {
        SpineInputs {
            leaves: std::array::from_fn(|leaf| {
                [
                    Block128::from(seed + (2 * leaf + 1) as u128),
                    Block128::from(seed + (2 * leaf + 2) as u128),
                ]
            }),
        }
    }

    fn collect_slot_state_ins(
        circuit: &SpineCircuit,
        inputs_list: &[SpineInputs],
    ) -> Vec<[Block128; STATE_SIZE]> {
        let mut all = Vec::new();
        for inputs in inputs_list {
            let states = reconstruct_slot_states(circuit, inputs);
            for (s_in, _) in &states {
                all.push(*s_in);
            }
        }
        all
    }

    struct LegacyVirtualTables {
        u: Vec<u128>,
        sigma_dec: Vec<u128>,
        rc_dec: Vec<u128>,
        mds_lane_dec: [Vec<u128>; STATE_SIZE],
        sigma_lane_dec: [Vec<u128>; STATE_SIZE],
        s_out_lane_dec: [Vec<u128>; STATE_SIZE],
        state_lane_dec: [Vec<u128>; STATE_SIZE],
    }

    impl LegacyVirtualTables {
        fn build(mle: &BlockSpineMle, rho: &[Block128]) -> Self {
            let n_cells = 1usize << mle.num_vars;
            Self {
                u: build_u_table_flat_dyn(rho, mle.live_slots, n_cells),
                sigma_dec: build_sigma_dec_table_flat_dyn(mle.live_slots, n_cells),
                rc_dec: build_rc_dec_table_flat_dyn(mle.live_slots, n_cells),
                mds_lane_dec: std::array::from_fn(|lane| {
                    build_mds_lane_table_flat_dyn(lane, mle.live_slots, n_cells)
                }),
                sigma_lane_dec: std::array::from_fn(|lane| {
                    build_sigma_lane_dec_table_flat_dyn(lane, mle.live_slots, n_cells)
                }),
                s_out_lane_dec: std::array::from_fn(|lane| {
                    project_lane_dec_flat_dyn(&mle.s_out, lane)
                }),
                state_lane_dec: std::array::from_fn(|lane| {
                    project_lane_dec_flat_dyn(&mle.state, lane)
                }),
            }
        }

        fn fold(&mut self, challenge: u128) {
            fold_flat_inplace(&mut self.u, challenge);
            fold_flat_inplace(&mut self.sigma_dec, challenge);
            fold_flat_inplace(&mut self.rc_dec, challenge);
            for lane in 0..STATE_SIZE {
                fold_flat_inplace(&mut self.mds_lane_dec[lane], challenge);
                fold_flat_inplace(&mut self.sigma_lane_dec[lane], challenge);
                fold_flat_inplace(&mut self.s_out_lane_dec[lane], challenge);
                fold_flat_inplace(&mut self.state_lane_dec[lane], challenge);
            }
        }
    }

    #[inline]
    fn legacy_pair(table: &[u128], i: usize, half: usize) -> [u128; 2] {
        [table[i], table[i] ^ table[i + half]]
    }

    #[test]
    fn slot_vars_computation() {
        assert_eq!(slot_vars_for(31), 5); // 1 tx
        assert_eq!(slot_vars_for(62), 6); // 2 txs
        assert_eq!(slot_vars_for(4 * 31), 7); // 4 txs: 124 slots
        assert_eq!(slot_vars_for(1024 * 31), 15); // 1024 txs: 31744 slots
    }

    #[test]
    fn num_vars_computation() {
        assert_eq!(num_vars_for(31), 5 + 7 + 2); // 14 (same as per-tx)
        assert_eq!(num_vars_for(62), 6 + 7 + 2); // 15
        assert_eq!(num_vars_for(4 * 31), 7 + 7 + 2); // 16
    }

    #[test]
    fn exact_block_class_geometry_includes_coinbase_body() {
        for (bodies, live_slots, slot_domain, num_vars) in [
            (9, 279, 512, 18),
            (33, 1_023, 1_024, 19),
            (65, 2_015, 2_048, 20),
            (256, 7_936, 8_192, 22),
        ] {
            let actual_live = bodies * N_SPINE_SLOTS;
            assert_eq!(actual_live, live_slots);
            assert_eq!(actual_live.next_power_of_two(), slot_domain);
            assert_eq!(num_vars_for(actual_live), num_vars);
        }
    }

    #[test]
    fn separable_and_virtual_tables_match_materialized_tables_every_round() {
        let circuit = SpineCircuit::build();
        let inputs = fixture_inputs(17);
        let all_state_ins = collect_slot_state_ins(&circuit, &[inputs]);
        let mle = BlockSpineMle::build(1, &all_state_ins);
        let rho: Vec<Block128> = (0..mle.num_vars)
            .map(|i| Block128::from(0x100 + i as u128 * 17))
            .collect();
        let mut compact = build_block_unified_flat_tables(&mle, &rho);
        let mut legacy = LegacyVirtualTables::build(&mle, &rho);

        for round in 0..mle.num_vars {
            let half = compact.len() / 2;
            assert_eq!(legacy.u.len(), compact.len());
            for i in 0..half {
                let pairs = compact.round_pairs(i, half);
                assert_eq!(pairs.public.u, legacy_pair(&legacy.u, i, half));
                assert_eq!(
                    pairs.public.sigma_dec,
                    legacy_pair(&legacy.sigma_dec, i, half)
                );
                assert_eq!(pairs.public.rc_dec, legacy_pair(&legacy.rc_dec, i, half));
                for lane in 0..STATE_SIZE {
                    assert_eq!(
                        pairs.public.mds_lane_dec[lane],
                        legacy_pair(&legacy.mds_lane_dec[lane], i, half)
                    );
                    assert_eq!(
                        pairs.public.sigma_lane_dec[lane],
                        legacy_pair(&legacy.sigma_lane_dec[lane], i, half)
                    );
                    assert_eq!(
                        pairs.s_out_lane_dec[lane],
                        legacy_pair(&legacy.s_out_lane_dec[lane], i, half)
                    );
                    assert_eq!(
                        pairs.state_lane_dec[lane],
                        legacy_pair(&legacy.state_lane_dec[lane], i, half)
                    );
                }
            }

            let challenge =
                tower_to_flat_u128(Block128::from(0x400 + round as u128 * 29).to_u128());
            compact.fold(challenge);
            legacy.fold(challenge);
        }

        let claims = compact.final_claims_tower();
        assert_eq!(
            claims.s_out_lane_dec,
            std::array::from_fn(|lane| Block128::from(flat_to_tower_u128(
                legacy.s_out_lane_dec[lane][0]
            )))
        );
        assert_eq!(
            claims.state_lane_dec,
            std::array::from_fn(|lane| Block128::from(flat_to_tower_u128(
                legacy.state_lane_dec[lane][0]
            )))
        );
    }

    #[test]
    fn production_shape_keeps_public_schedule_storage_sublinear_in_cells() {
        let live_slots = 256 * N_SPINE_SLOTS;
        let num_vars = num_vars_for(live_slots);
        assert_eq!(num_vars, 22);
        let schedules =
            BlockPublicFlatSchedules::new(&vec![Block128::ZERO; num_vars], live_slots, num_vars);
        let resident_entries = schedules.live_slot.len()
            + schedules.u_slot.len()
            + schedules.u_inner.len()
            + schedules.sigma_dec_inner.len()
            + schedules.rc_dec_inner.len()
            + schedules
                .mds_lane_dec_inner
                .iter()
                .map(Vec::len)
                .sum::<usize>()
            + schedules
                .sigma_lane_dec_inner
                .iter()
                .map(Vec::len)
                .sum::<usize>();
        assert_eq!(schedules.live_slot.len(), 8_192);
        assert_eq!(schedules.u_inner.len(), 512);
        assert_eq!(resident_entries, 2 * 8_192 + 11 * 512);
        assert!(resident_entries < (1usize << num_vars) / 100);
    }

    #[test]
    fn flat_fold_releases_truncated_capacity() {
        let mut table = vec![0u128; 1 << 16];
        let original_capacity = table.capacity();
        fold_flat_inplace(&mut table, 7);
        assert_eq!(table.len(), 1 << 15);
        assert!(table.capacity() < original_capacity);
    }

    #[test]
    fn block_spine_killshot_1tx_roundtrip() {
        let circuit = SpineCircuit::build();
        let inputs = fixture_inputs(42);
        let inputs_list = vec![inputs];
        let all_state_ins = collect_slot_state_ins(&circuit, &inputs_list);

        let states = reconstruct_slot_states(&circuit, &inputs_list[0]);
        let wrap = states.last().unwrap();
        let tx_body_hash = [wrap.1[0], wrap.1[1]];

        let mle = BlockSpineMle::build(1, &all_state_ins);
        let mut ch_p = Poseidon2bChannel::new();
        let (proof, reductions) = prove_block_spine_killshot(1, &mle, &[tx_body_hash], &mut ch_p);

        let mut ch_v = Poseidon2bChannel::new();
        let v_red = verify_block_spine_killshot(&proof, 1, &[tx_body_hash], &mut ch_v)
            .expect("verifier accepts honest proof");

        assert_eq!(v_red, reductions);
        assert!(discharge_block_spine_reductions_native(
            1,
            &all_state_ins,
            &v_red
        ));
    }

    #[test]
    fn block_spine_killshot_4tx_roundtrip() {
        let circuit = SpineCircuit::build();
        let inputs_list: Vec<SpineInputs> =
            (0..4).map(|i| fixture_inputs(i as u128 * 100)).collect();
        let all_state_ins = collect_slot_state_ins(&circuit, &inputs_list);

        let tx_body_hashes: Vec<[Block128; 2]> = inputs_list
            .iter()
            .map(|inp| {
                let states = reconstruct_slot_states(&circuit, inp);
                let wrap = states.last().unwrap();
                [wrap.1[0], wrap.1[1]]
            })
            .collect();

        let mle = BlockSpineMle::build(4, &all_state_ins);
        let mut ch_p = Poseidon2bChannel::new();
        let (proof, reductions) = prove_block_spine_killshot(4, &mle, &tx_body_hashes, &mut ch_p);

        assert_eq!(proof.num_vars, 7 + 7 + 2); // 16 vars for 124 slots
        assert_eq!(proof.live_slots, 4 * 31);

        let mut ch_v = Poseidon2bChannel::new();
        let v_red = verify_block_spine_killshot(&proof, 4, &tx_body_hashes, &mut ch_v)
            .expect("verifier accepts 4-tx block");

        assert_eq!(v_red, reductions);
        assert!(discharge_block_spine_reductions_native(
            4,
            &all_state_ins,
            &v_red
        ));
    }

    #[test]
    fn block_spine_rejects_tampered_main_claim() {
        let circuit = SpineCircuit::build();
        let inputs_list: Vec<SpineInputs> =
            (0..2).map(|i| fixture_inputs(i as u128 * 50)).collect();
        let all_state_ins = collect_slot_state_ins(&circuit, &inputs_list);

        let tx_body_hashes: Vec<[Block128; 2]> = inputs_list
            .iter()
            .map(|inp| {
                let states = reconstruct_slot_states(&circuit, inp);
                let wrap = states.last().unwrap();
                [wrap.1[0], wrap.1[1]]
            })
            .collect();

        let mle = BlockSpineMle::build(2, &all_state_ins);
        let mut ch_p = Poseidon2bChannel::new();
        let (mut proof, _) = prove_block_spine_killshot(2, &mle, &tx_body_hashes, &mut ch_p);
        proof.kill_shot.main.state_at_r += Block128::ONE;

        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_block_spine_killshot(&proof, 2, &tx_body_hashes, &mut ch_v).is_none());
    }

    fn one_tx_proof() -> (BlockSpineProof, Vec<[Block128; 2]>) {
        let circuit = SpineCircuit::build();
        let inputs = fixture_inputs(7);
        let inputs_list = vec![inputs];
        let all_state_ins = collect_slot_state_ins(&circuit, &inputs_list);
        let states = reconstruct_slot_states(&circuit, &inputs_list[0]);
        let wrap = states.last().unwrap();
        let tx_body_hashes = vec![[wrap.1[0], wrap.1[1]]];
        let mle = BlockSpineMle::build(1, &all_state_ins);
        let mut ch_p = Poseidon2bChannel::new();
        let (proof, _) = prove_block_spine_killshot(1, &mle, &tx_body_hashes, &mut ch_p);
        (proof, tx_body_hashes)
    }

    #[test]
    fn block_spine_rejects_tampered_round_coefficients() {
        // Compressed rounds have no per-round sum check; rejection must
        // come from the final constraint / claim chain instead. Flip the
        // constant term and one high-degree term separately.
        for (poly_idx, coeff_idx) in [(0usize, 0usize), (3, 5)] {
            let (mut proof, hashes) = one_tx_proof();
            proof.kill_shot.main.round_polys[poly_idx].coeffs_no_linear[coeff_idx] += Block128::ONE;
            let mut ch_v = Poseidon2bChannel::new();
            assert!(verify_block_spine_killshot(&proof, 1, &hashes, &mut ch_v).is_none());
        }
        let (mut proof, hashes) = one_tx_proof();
        proof.kill_shot.shift.round_polys[2].coeffs_no_linear[1] += Block128::ONE;
        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_block_spine_killshot(&proof, 1, &hashes, &mut ch_v).is_none());
    }

    #[test]
    fn block_spine_rejects_off_shape_round_polys() {
        // Wire length is an exact shape check: shorter AND longer rounds
        // must both be rejected before any transcript interaction.
        let (mut proof, hashes) = one_tx_proof();
        proof.kill_shot.main.round_polys[1].coeffs_no_linear.pop();
        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_block_spine_killshot(&proof, 1, &hashes, &mut ch_v).is_none());

        let (mut proof, hashes) = one_tx_proof();
        proof.kill_shot.main.round_polys[1]
            .coeffs_no_linear
            .push(Block128::ZERO);
        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_block_spine_killshot(&proof, 1, &hashes, &mut ch_v).is_none());

        let (mut proof, hashes) = one_tx_proof();
        proof.kill_shot.shift.round_polys[0].coeffs_no_linear.pop();
        let mut ch_v = Poseidon2bChannel::new();
        assert!(verify_block_spine_killshot(&proof, 1, &hashes, &mut ch_v).is_none());
    }
}
