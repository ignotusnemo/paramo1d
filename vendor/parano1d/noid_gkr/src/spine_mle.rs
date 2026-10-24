// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

#![allow(clippy::needless_range_loop, clippy::doc_overindented_list_items)]

//! Unified 14-variable MLE layout for the Spine Kill-Shot.
//!
//! Architecture
//! ------------
//!
//! The kill-shot prover represents the full 31-permutation spine as
//! four side-by-side 14-variable MLEs on a single hypercube of
//! `2^14 = 16 384` cells:
//!
//! | MLE       | Meaning per cell `(slot, round, elem)`                       |
//! |-----------|---------------------------------------------------------------|
//! | `s_in`    | S-box input  = `sin[round][elem]` from the witness            |
//! | `s_out`   | S-box output = `sout[round][elem]` from the witness           |
//! | `sigma`   | 1 if the S-box is active on this cell, else 0                 |
//! | `state`   | Round-entry state = `state[round][elem]` from the witness     |
//!
//! Bit layout (14 bits, low → high): `elem:2 | round:7 | slot:5`.
//! `(slot, round, elem)` lives at index
//! `(slot << (N_SPINE_ROUND_VARS + N_SPINE_ELEM_VARS))
//!  | (round << N_SPINE_ELEM_VARS)
//!  | elem`.
//!
//! Topology (matches `noid_poseidon2b` natively):
//!   - Rounds 0..3 and 62..65 are **full** — every elem is active in `σ`.
//!   - Rounds 4..61 are **partial** — only `elem == 0` is active in `σ`.
//!   - `state[round]` exists for `round ∈ 0..=N_ROUNDS` (67 rows). Row
//!     `0` is the post-initial-MDS state; row `N_ROUNDS = 66` is the
//!     permutation output. The 7-bit round axis covers indices 0..127;
//!     rounds 67..127 are zero-padded.
//!   - `s_in` / `s_out` exist for `round ∈ 0..N_ROUNDS`; row `N_ROUNDS`
//!     and rounds 67..127 are zero by convention.
//!   - Slot 31 is zero-padded.
//!
//! Identities discharged by the unified Kill-Shot sumcheck (degree 9
//! after the change of variable `y = inc_round(x)`):
//!
//! ```text
//!   C1 (deg 7 in s_in):
//!       σ(x)·(s_out(x) + s_in(x)^7) + (1+σ(x))·(s_out(x) + s_in(x)) = 0
//!
//!   C1' (deg 2, "RC tie"): for every active cell, the witness obeys
//!       σ(x)·(s_in(x) + state(x) + RC(x)) = 0
//!     where RC(x) is the round-constant table indexed at `x` itself.
//!
//!   C2 (deg 2, "MDS shift"): the next-round state is the MDS image
//!     of the previous row's S-box output (full rounds) or of a mixed
//!     row (partial rounds, lanes 1..3 pass `state` through):
//!         state(y)_e + Σ_j  M_{kind(dec(y))}[e][j] · π(dec(y) | e=j) = 0
//!     where π is the multilinear lookup
//!         π(x | e=j) = s_out(x | e=j) + (1 - σ(x | e=j)) · state(x | e=j).
//!     On full rounds σ ≡ 1 so π = s_out; on partial rounds σ(j=0)=1
//!     so π = s_out at lane 0 and π = state at lanes 1..3 (the witness
//!     pins `s_out=0` there).
//! ```
//!
//! Inactive cells (`σ = 0`) trivialise C1 (both branches collapse to
//! `s_out + s_in = 0` with both pinned to zero) and C1' (`σ = 0`
//! kills the constraint). Padded cells (slot ≥ N_SPINE_SLOTS or
//! round ≥ N_ROUNDS) have every MLE zero so all three identities hold
//! trivially. C2 is masked at the sumcheck level by the public mask
//! `μ(dec(y)) = 1[slot(dec(y)) < N_SPINE_SLOTS ∧ round(dec(y)) < N_ROUNDS]`.

use noid_core::{Block128, TowerField};
use noid_poseidon2b::native::permutation::{F_ROUNDS, N_ROUNDS, P_ROUNDS, STATE_SIZE};

use crate::layers::{evaluate_permutation, PermLayerWitness, RoundKind};
pub use crate::tx_body_layout::N_SPINE_SLOTS;
use crate::tx_body_layout::N_SPINE_SLOTS_PADDED;

/// `log2(32) = 5` slot variables.
pub const N_SPINE_SLOT_VARS: usize = N_SPINE_SLOTS_PADDED.trailing_zeros() as usize;
/// `log2(128) = 7` round variables (covers `N_ROUNDS = 66` with padding).
pub const N_SPINE_ROUND_VARS: usize = 7;
/// `log2(4) = 2` element-within-state variables.
pub const N_SPINE_ELEM_VARS: usize = 2;
/// Total variable count of the unified MLE.
pub const N_SPINE_UNIFIED_VARS: usize = N_SPINE_SLOT_VARS + N_SPINE_ROUND_VARS + N_SPINE_ELEM_VARS;
/// `2^14 = 16 384` cells.
pub const N_SPINE_UNIFIED_CELLS: usize = 1 << N_SPINE_UNIFIED_VARS;

/// Padding helpers — compile-time assertions on topology.
const _: () = assert!(N_ROUNDS == 66);
const _: () = assert!(STATE_SIZE == 4);
const _: () = assert!(N_SPINE_SLOT_VARS == 5);
const _: () = assert!(N_SPINE_UNIFIED_VARS == 14);
const _: () = assert!(N_SPINE_SLOTS <= (1 << N_SPINE_SLOT_VARS));
const _: () = assert!(N_ROUNDS <= (1 << N_SPINE_ROUND_VARS));
const _: () = assert!(STATE_SIZE <= (1 << N_SPINE_ELEM_VARS));

/// The four columns of the unified MLE. Each is a length-`2^14`
/// vector of `Block128`. The verifier opens all of them at points
/// derived from the unified sumcheck's final challenge.
#[derive(Debug, Clone)]
pub struct SpineUnifiedMle {
    pub s_in: Vec<Block128>,
    pub s_out: Vec<Block128>,
    pub sigma: Vec<Block128>,
    /// Round-entry state. `state[(slot, 0, elem)]` is the
    /// post-initial-MDS state lane; `state[(slot, N_ROUNDS, elem)]`
    /// is the permutation output lane. Rounds `> N_ROUNDS` and
    /// padded slots are zero.
    pub state: Vec<Block128>,
}

impl SpineUnifiedMle {
    /// Empty (all-zero) MLE — useful as a starting buffer before
    /// `populate_slot`.
    pub fn zero() -> Self {
        Self {
            s_in: vec![Block128::ZERO; N_SPINE_UNIFIED_CELLS],
            s_out: vec![Block128::ZERO; N_SPINE_UNIFIED_CELLS],
            sigma: vec![Block128::ZERO; N_SPINE_UNIFIED_CELLS],
            state: vec![Block128::ZERO; N_SPINE_UNIFIED_CELLS],
        }
    }

    /// Index into the unified MLE for `(slot, round, elem)`.
    #[inline]
    pub fn index(slot: usize, round: usize, elem: usize) -> usize {
        debug_assert!(slot < 1 << N_SPINE_SLOT_VARS);
        debug_assert!(round < 1 << N_SPINE_ROUND_VARS);
        debug_assert!(elem < 1 << N_SPINE_ELEM_VARS);
        (slot << (N_SPINE_ROUND_VARS + N_SPINE_ELEM_VARS)) | (round << N_SPINE_ELEM_VARS) | elem
    }

    /// Fill in one slot's cells from an instrumented `PermLayerWitness`.
    /// `slot` must satisfy `slot < N_SPINE_SLOTS`.
    pub fn populate_slot(&mut self, slot: usize, witness: &PermLayerWitness) {
        assert!(slot < N_SPINE_SLOTS, "slot out of range");
        // `s_in`, `s_out`, `σ` live for `r ∈ 0..N_ROUNDS`.
        for r in 0..N_ROUNDS {
            let active_mask = match witness.kind[r] {
                RoundKind::Full => [true; STATE_SIZE],
                RoundKind::Partial => {
                    let mut m = [false; STATE_SIZE];
                    m[0] = true;
                    m
                }
            };
            for elem in 0..STATE_SIZE {
                let idx = Self::index(slot, r, elem);
                // `sin`/`sout` already obey the partial-round zeroing
                // convention (lanes 1..3 are pinned to zero by
                // `evaluate_permutation`). Copy them straight in.
                self.s_in[idx] = witness.sin[r][elem];
                self.s_out[idx] = witness.sout[r][elem];
                self.sigma[idx] = if active_mask[elem] {
                    Block128::ONE
                } else {
                    Block128::ZERO
                };
            }
        }
        // `state` lives for `r ∈ 0..=N_ROUNDS` (rows 0..67 inclusive
        // of the witness). Row 0 is the post-initial-MDS state,
        // row N_ROUNDS is the permutation output.
        debug_assert_eq!(witness.state.len(), N_ROUNDS + 1);
        for r in 0..=N_ROUNDS {
            for elem in 0..STATE_SIZE {
                let idx = Self::index(slot, r, elem);
                self.state[idx] = witness.state[r][elem];
            }
        }
    }

    /// Local consistency check: every cell satisfies all three
    /// kill-shot identities (`C1`, `C1'`, `C2`). Used by debug paths
    /// and the integration differential test in `spine_killshot_vs_native`.
    pub fn debug_check_identity(&self) {
        use crate::spine_shift::{
            build_mu_table, build_rc_table, dec_round_index, mds_coeff, round_of,
        };
        use noid_core::packed::pow7::pow7_block128;

        let rc = build_rc_table();
        let mu = build_mu_table();

        for idx in 0..N_SPINE_UNIFIED_CELLS {
            let sin = self.s_in[idx];
            let sout = self.s_out[idx];
            let sigma = self.sigma[idx];
            let state = self.state[idx];
            let rcv = rc[idx];

            // C1: σ·(sout + sin^7) + (1+σ)·(sout + sin) == 0.
            let active = sout + pow7_block128(sin);
            let identity = sout + sin;
            let c1 = sigma * active + (Block128::ONE + sigma) * identity;
            assert_eq!(c1, Block128::ZERO, "C1 violated at idx {idx}");

            // C1': σ · (sin + state + RC) == 0.
            let c1p = sigma * (sin + state + rcv);
            assert_eq!(c1p, Block128::ZERO, "C1' violated at idx {idx}");
        }

        // C2 (MDS shift): for every y where μ(dec(y)) == 1, we must
        // have state(y) + Σ_j M_{kind(dec(y))}[e][j] · π(dec(y) | e=j) = 0,
        // where π = s_out + (1-σ)·state.
        for idx_y in 0..N_SPINE_UNIFIED_CELLS {
            let dec = dec_round_index(idx_y as u16) as usize;
            if mu[dec] == Block128::ZERO {
                continue;
            }
            let r = round_of(dec as u16);
            // Build π lookups for all four lanes at `dec` with that
            // lane substituted in.
            let pi: [Block128; STATE_SIZE] = std::array::from_fn(|j| {
                let dec_with_j = (dec & !0b11) | j;
                let sout_j = self.s_out[dec_with_j];
                let state_j = self.state[dec_with_j];
                let sigma_j = self.sigma[dec_with_j];
                // π = σ·s_out + (1+σ)·state — matches the symbolic
                // form the unified sumcheck will fold over.
                sigma_j * sout_j + (Block128::ONE + sigma_j) * state_j
            });
            let e = idx_y & 0b11;
            let mut acc = Block128::ZERO;
            for j in 0..STATE_SIZE {
                acc += mds_coeff(r, e, j) * pi[j];
            }
            let c2 = self.state[idx_y] + acc;
            assert_eq!(
                c2,
                Block128::ZERO,
                "C2 violated at idx_y {idx_y} (dec={dec})"
            );
        }
    }
}

/// Build the unified MLE from `N_SPINE_SLOTS` `state_in` vectors. The
/// returned object also carries the witness slice for the boundary
/// boundary pin step (the Kill-Shot orchestrator reads `state_in` from `s_in[..,0,..]`).
pub fn build_unified_mle(
    slot_state_ins: &[[Block128; STATE_SIZE]],
) -> (SpineUnifiedMle, Vec<PermLayerWitness>) {
    assert_eq!(
        slot_state_ins.len(),
        N_SPINE_SLOTS,
        "expected exactly N_SPINE_SLOTS slot inputs"
    );
    let mut mle = SpineUnifiedMle::zero();
    let mut witnesses = Vec::with_capacity(N_SPINE_SLOTS);
    for (slot, state_in) in slot_state_ins.iter().enumerate() {
        let w = evaluate_permutation(*state_in);
        mle.populate_slot(slot, &w);
        witnesses.push(w);
    }
    (mle, witnesses)
}

/// Compile-time sigma schedule: `sigma_template()[r][elem]` is the same
/// for every slot, so callers that want to verify the selector value at
/// a specific `(round, elem)` can do so without rebuilding the MLE.
pub fn sigma_at(round: usize, elem: usize) -> Block128 {
    if round >= N_ROUNDS || elem >= STATE_SIZE {
        return Block128::ZERO;
    }
    let is_partial = (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&round);
    if !is_partial || elem == 0 {
        Block128::ONE
    } else {
        Block128::ZERO
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_core::TowerField;
    use noid_poseidon2b::native::permutation::Poseidon2bPermutation;

    fn random_state(seed: u128) -> [Block128; STATE_SIZE] {
        // Deterministic helper — not crypto-grade, just spreads bits.
        let mut s = seed;
        std::array::from_fn(|_| {
            s = s.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0xDEAD_BEEF);
            Block128::from(s)
        })
    }

    #[test]
    fn topology_constants_consistent() {
        assert_eq!(N_SPINE_UNIFIED_VARS, 14);
        assert_eq!(N_SPINE_UNIFIED_CELLS, 16_384);
    }

    #[test]
    fn index_round_trip() {
        // Each (slot, round, elem) must produce a unique index inside
        // the 14-bit space, and we should be able to decode it back.
        for slot in 0..N_SPINE_SLOTS {
            for round in 0..N_ROUNDS {
                for elem in 0..STATE_SIZE {
                    let idx = SpineUnifiedMle::index(slot, round, elem);
                    assert!(idx < N_SPINE_UNIFIED_CELLS);
                    let recovered_elem = idx & 0b11;
                    let recovered_round = (idx >> 2) & 0b111_1111;
                    let recovered_slot = idx >> 9;
                    assert_eq!(recovered_elem, elem);
                    assert_eq!(recovered_round, round);
                    assert_eq!(recovered_slot, slot);
                }
            }
        }
    }

    #[test]
    fn sigma_schedule_matches_native_round_kinds() {
        // Match `layers::round_kind` for every (round, elem).
        use crate::layers::round_kind;
        for round in 0..N_ROUNDS {
            let kind = round_kind(round);
            for elem in 0..STATE_SIZE {
                let expected = match kind {
                    RoundKind::Full => Block128::ONE,
                    RoundKind::Partial => {
                        if elem == 0 {
                            Block128::ONE
                        } else {
                            Block128::ZERO
                        }
                    }
                };
                assert_eq!(sigma_at(round, elem), expected, "round {round} elem {elem}");
            }
        }
    }

    #[test]
    fn sigma_zero_outside_topology() {
        assert_eq!(sigma_at(N_ROUNDS, 0), Block128::ZERO);
        assert_eq!(sigma_at(N_ROUNDS + 1, 0), Block128::ZERO);
        assert_eq!(sigma_at(0, STATE_SIZE), Block128::ZERO);
    }

    #[test]
    fn populate_slot_matches_native_permutation() {
        // For a non-trivial state, the populated MLE's `s_in[0,*,*]`
        // and `s_out[N_ROUNDS-1,*,*]` must agree with the native
        // permutation trace.
        let state = random_state(42);
        let mut mle = SpineUnifiedMle::zero();
        let witness = evaluate_permutation(state);
        mle.populate_slot(7, &witness);

        let perm = Poseidon2bPermutation;
        let mut native = state;
        perm.permute_mut(&mut native);
        assert_eq!(witness.final_state(), native);

        // Sigma is independent of slot — spot-check.
        for round in 0..N_ROUNDS {
            for elem in 0..STATE_SIZE {
                let idx = SpineUnifiedMle::index(7, round, elem);
                assert_eq!(mle.sigma[idx], sigma_at(round, elem));
            }
        }
    }

    #[test]
    fn unified_mle_satisfies_sbox_identity() {
        let state_ins: Vec<_> = (0..N_SPINE_SLOTS)
            .map(|i| random_state(i as u128 + 1))
            .collect();
        let (mle, _) = build_unified_mle(&state_ins);
        mle.debug_check_identity();
    }

    #[test]
    fn padded_cells_are_zero() {
        let state_ins: Vec<_> = (0..N_SPINE_SLOTS)
            .map(|i| random_state(i as u128 + 1))
            .collect();
        let (mle, _) = build_unified_mle(&state_ins);
        // Slot 31 must be fully zero.
        for slot in N_SPINE_SLOTS..(1 << N_SPINE_SLOT_VARS) {
            for round in 0..(1 << N_SPINE_ROUND_VARS) {
                for elem in 0..(1 << N_SPINE_ELEM_VARS) {
                    let idx = SpineUnifiedMle::index(slot, round, elem);
                    assert_eq!(mle.s_in[idx], Block128::ZERO);
                    assert_eq!(mle.s_out[idx], Block128::ZERO);
                    assert_eq!(mle.sigma[idx], Block128::ZERO);
                }
            }
        }
        // Rounds N_ROUNDS..128 inside every active slot must also be
        // zero (the witness only writes 0..N_ROUNDS).
        for slot in 0..N_SPINE_SLOTS {
            for round in N_ROUNDS..(1 << N_SPINE_ROUND_VARS) {
                for elem in 0..STATE_SIZE {
                    let idx = SpineUnifiedMle::index(slot, round, elem);
                    assert_eq!(mle.s_in[idx], Block128::ZERO);
                    assert_eq!(mle.s_out[idx], Block128::ZERO);
                    assert_eq!(mle.sigma[idx], Block128::ZERO);
                }
            }
        }
    }
}
