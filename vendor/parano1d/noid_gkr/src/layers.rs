// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

#![allow(clippy::needless_range_loop)]

//! Poseidon2b permutation as a layered arithmetic witness.
//!
//! One `permute_mut` call is re-expressed as:
//!
//! - a **row programme** over `0..=N_ROUNDS` rows (N_ROUNDS + 1 = 67),
//!   with row 0 holding the post-initial-MDS state and row 66 holding
//!   the final output,
//! - a **per-row decomposition** of the x^7 S-box into four degree-2
//!   sub-lanes `x2 = sin*sin`, `x4 = x2*x2`, `x3 = x2*sin`,
//!   `sout = x4*x3`,
//! - a deterministic **round-kind selector** `is_full[r]` and
//!   a deterministic **round-constant programme** `rc[i][r]` sourced
//!   from `noid_poseidon2b::native::permutation`.
//!
//! The layout follows the native permutation semantics: partial-round rows
//! zero out lanes 1..3 of `sin`, `x2`,
//! `x4`, `x3`, `sout`, and the MDS_PARTIAL step reads `[sout[0],
//! state[1], state[2], state[3]]` (lanes 1..3 come from the raw state,
//! not from the zeroed S-box outputs). This is critical for the
//! batch-eval sumcheck to line up with the committed MLE columns.
//!
//! This module produces *no* proof. Its sole contract is:
//! `evaluate_permutation(state_in).final_state()` must byte-equal
//! `Poseidon2bPermutation::permute_mut(state_in)`. `mle_layout` builds
//! the MLE representation on top.

use noid_core::Block128;
use noid_poseidon2b::native::permutation::{
    F_ROUNDS, MDS_FULL, MDS_PARTIAL, N_ROUNDS, P_ROUNDS, ROUND_CONSTANTS, STATE_SIZE,
};
use zeroize::{Zeroize, Zeroizing};

#[cfg(test)]
use noid_poseidon2b::native::permutation::sbox_x7;

/// Full-vs-partial classification of a round. Deterministic: head +
/// tail `F_ROUNDS/2` rounds are full, middle `P_ROUNDS` are partial.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoundKind {
    Full,
    Partial,
}

/// `true` iff round `r` is full. Byte-identical to the native
/// `permute_mut` branch.
#[inline]
pub fn round_kind(r: usize) -> RoundKind {
    if !(F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&r) {
        RoundKind::Full
    } else {
        RoundKind::Partial
    }
}

/// Per-row witness of one Poseidon permutation. Every cell the later
/// sumcheck will reference lives here.
///
/// Indexing convention for each field below: `[row][lane]`, with
/// `row ∈ 0..=N_ROUNDS` and `lane ∈ 0..STATE_SIZE`.
pub struct PermLayerWitness {
    /// Round-entry state. `state[0]` is the post-initial-MDS state;
    /// `state[N_ROUNDS]` is the permutation output.
    pub state: Vec<[Block128; STATE_SIZE]>,
    /// S-box input per lane per row: `sin[r][i] = state[r][i] +
    /// rc[i][r]` on full rounds; on partial rounds lane 0 follows the
    /// same rule and lanes 1..3 are zero.
    pub sin: Vec<[Block128; STATE_SIZE]>,
    /// `x2[r][i] = sin[r][i]²` (zero on partial rows for lanes 1..3).
    pub x2: Vec<[Block128; STATE_SIZE]>,
    /// `x4[r][i] = x2[r][i]²`.
    pub x4: Vec<[Block128; STATE_SIZE]>,
    /// `x3[r][i] = x2[r][i] · sin[r][i]`.
    pub x3: Vec<[Block128; STATE_SIZE]>,
    /// `sout[r][i] = x4[r][i] · x3[r][i]` (= `sin[r][i]^7`).
    pub sout: Vec<[Block128; STATE_SIZE]>,
    /// Per-row round kind. Index `N_ROUNDS` is the output row and
    /// carries `Full` purely for column-typing convenience — its
    /// `sin/x2/...` rows are zero and carry no S-box meaning.
    pub kind: Vec<RoundKind>,
}

impl Drop for PermLayerWitness {
    fn drop(&mut self) {
        self.state.zeroize();
        self.sin.zeroize();
        self.x2.zeroize();
        self.x4.zeroize();
        self.x3.zeroize();
        self.sout.zeroize();
    }
}

impl PermLayerWitness {
    /// Number of rows = `N_ROUNDS + 1` = 67.
    #[inline]
    pub fn n_rows(&self) -> usize {
        self.state.len()
    }

    /// Final permutation output = `state[N_ROUNDS]`.
    #[inline]
    pub fn final_state(&self) -> [Block128; STATE_SIZE] {
        self.state[N_ROUNDS]
    }
}

/// Run the entire permutation and record the full layered witness.
/// The function is a native re-implementation of
/// `Poseidon2bPermutation::permute_mut` instrumented to keep every
/// intermediate value. It must never diverge from native.
pub fn evaluate_permutation(mut current: [Block128; STATE_SIZE]) -> PermLayerWitness {
    // Row 0's state is the post-initial-MDS state (native applies
    // MDS_FULL before the round loop).
    apply_mds_full(&mut current);

    let n_rows = N_ROUNDS + 1;
    let mut state = Vec::with_capacity(n_rows);
    let mut sin = Vec::with_capacity(n_rows);
    let mut x2 = Vec::with_capacity(n_rows);
    let mut x4 = Vec::with_capacity(n_rows);
    let mut x3 = Vec::with_capacity(n_rows);
    let mut sout = Vec::with_capacity(n_rows);
    let mut kind = Vec::with_capacity(n_rows);

    for r in 0..N_ROUNDS {
        state.push(current);
        let k = round_kind(r);
        kind.push(k);

        let (row_sin, row_x2, row_x4, row_x3, row_sout) = match k {
            RoundKind::Full => {
                let mut sn = Zeroizing::new([Block128::from(0u128); STATE_SIZE]);
                let mut x2r = Zeroizing::new([Block128::from(0u128); STATE_SIZE]);
                let mut x4r = Zeroizing::new([Block128::from(0u128); STATE_SIZE]);
                let mut x3r = Zeroizing::new([Block128::from(0u128); STATE_SIZE]);
                let mut so = Zeroizing::new([Block128::from(0u128); STATE_SIZE]);
                for i in 0..STATE_SIZE {
                    sn[i] = current[i] + Block128::from(ROUND_CONSTANTS[i][r]);
                    x2r[i] = sn[i] * sn[i];
                    x4r[i] = x2r[i] * x2r[i];
                    x3r[i] = x2r[i] * sn[i];
                    so[i] = x4r[i] * x3r[i];
                }
                let mut next = *so;
                apply_mds_full(&mut next);
                current = next;
                next.zeroize();
                (sn, x2r, x4r, x3r, so)
            }
            RoundKind::Partial => {
                let mut sn = Zeroizing::new([Block128::from(0u128); STATE_SIZE]);
                let mut x2r = Zeroizing::new([Block128::from(0u128); STATE_SIZE]);
                let mut x4r = Zeroizing::new([Block128::from(0u128); STATE_SIZE]);
                let mut x3r = Zeroizing::new([Block128::from(0u128); STATE_SIZE]);
                let mut so = Zeroizing::new([Block128::from(0u128); STATE_SIZE]);
                sn[0] = current[0] + Block128::from(ROUND_CONSTANTS[0][r]);
                x2r[0] = sn[0] * sn[0];
                x4r[0] = x2r[0] * x2r[0];
                x3r[0] = x2r[0] * sn[0];
                so[0] = x4r[0] * x3r[0];
                // Build the partial-MDS input: lane 0 uses the S-box
                // output, lanes 1..3 use the raw state (the AIR pins
                // sin/x2/x3/x4/sout to zero on those lanes).
                let mut partial_input =
                    Zeroizing::new([current[0], current[1], current[2], current[3]]);
                partial_input[0] = so[0];
                let mut next = apply_mds_partial(*partial_input);
                current = next;
                next.zeroize();
                (sn, x2r, x4r, x3r, so)
            }
        };

        sin.push(*row_sin);
        x2.push(*row_x2);
        x4.push(*row_x4);
        x3.push(*row_x3);
        sout.push(*row_sout);
    }

    // Output row (index = N_ROUNDS): state only, all S-box cells zero.
    state.push(current);
    sin.push([Block128::from(0u128); STATE_SIZE]);
    x2.push([Block128::from(0u128); STATE_SIZE]);
    x4.push([Block128::from(0u128); STATE_SIZE]);
    x3.push([Block128::from(0u128); STATE_SIZE]);
    sout.push([Block128::from(0u128); STATE_SIZE]);
    kind.push(RoundKind::Full); // typing convenience; see doc

    PermLayerWitness {
        state,
        sin,
        x2,
        x4,
        x3,
        sout,
        kind,
    }
}

/// Apply `MDS_FULL` in place. Mirrors the native helper of the same
/// name but avoids reaching into the private module — we re-derive it
/// here from the public `MDS_FULL` constant.
#[inline]
pub fn apply_mds_full(state: &mut [Block128; STATE_SIZE]) {
    let mut input = *state;
    for i in 0..STATE_SIZE {
        let mut out = Block128::from(0u128);
        for j in 0..STATE_SIZE {
            if MDS_FULL[i][j] == 1 {
                out += input[j];
            } else {
                out += Block128::from(MDS_FULL[i][j]) * input[j];
            }
        }
        state[i] = out;
    }
    input.zeroize();
}

/// Apply `MDS_PARTIAL` and return the result. Operates on a passed-in
/// vector rather than in-place to highlight that the caller chooses
/// which rule builds the input (for partial rounds: `[sout[0],
/// state[1..3]]`).
#[inline]
pub fn apply_mds_partial(mut input: [Block128; STATE_SIZE]) -> [Block128; STATE_SIZE] {
    let mut out = [Block128::from(0u128); STATE_SIZE];
    for i in 0..STATE_SIZE {
        let mut acc = Block128::from(0u128);
        for j in 0..STATE_SIZE {
            if MDS_PARTIAL[i][j] == 1 {
                acc += input[j];
            } else {
                acc += Block128::from(MDS_PARTIAL[i][j]) * input[j];
            }
        }
        out[i] = acc;
    }
    input.zeroize();
    out
}

/// Compile-time checks on the round schedule.
#[cfg(test)]
mod schedule_tests {
    use super::*;

    #[test]
    fn first_and_last_four_rounds_are_full() {
        for r in 0..F_ROUNDS / 2 {
            assert_eq!(round_kind(r), RoundKind::Full);
        }
        for r in (F_ROUNDS / 2 + P_ROUNDS)..N_ROUNDS {
            assert_eq!(round_kind(r), RoundKind::Full);
        }
    }

    #[test]
    fn middle_58_rounds_are_partial() {
        for r in (F_ROUNDS / 2)..(F_ROUNDS / 2 + P_ROUNDS) {
            assert_eq!(round_kind(r), RoundKind::Partial);
        }
    }

    #[test]
    fn sbox_x7_equals_native() {
        for x in [0u128, 1, 2, 3, 0xDEADBEEFu128, u128::MAX] {
            let v = Block128::from(x);
            let via_layers = {
                let x2 = v * v;
                let x4 = x2 * x2;
                let x3 = x2 * v;
                x4 * x3
            };
            assert_eq!(via_layers, sbox_x7(v));
        }
    }
}
