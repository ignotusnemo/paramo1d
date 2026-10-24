// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Spine utility functions: boundary MLE construction, state reconstruction,
//! and tx-body hash computation.
//!
//! Kill-Shot proves the full tx-body Poseidon2b spine from these canonical
//! witness and hash helpers.

use noid_core::{Block128, TowerField};
use noid_poseidon2b::native::permutation::STATE_SIZE;

use crate::circuit::{SpineCircuit, SpineInputs};
use crate::layers::evaluate_permutation;
use crate::mle_layout::{PermMle, N_PERM_CELLS, N_PERM_VARS};
pub use crate::tx_body_layout::{N_SPINE_SLOTS, N_SPINE_SLOTS_PADDED};

/// Extra variable count to index the 32-slot padded body domain.
pub const N_SLOT_VARS: usize = N_SPINE_SLOTS_PADDED.trailing_zeros() as usize;

/// Total variables in the concatenated boundary MLE:
/// `log2(N_SPINE_SLOTS_PADDED) + N_PERM_VARS = 5 + 9 = 14`.
pub const N_BOUNDARY_VARS: usize = N_SLOT_VARS + N_PERM_VARS;

/// `2^N_BOUNDARY_VARS` cells — the padded size of the boundary MLE.
pub const N_BOUNDARY_CELLS: usize = 1 << N_BOUNDARY_VARS;

const _: () = assert!(N_SLOT_VARS == 5);
const _: () = assert!(N_BOUNDARY_VARS == 14);

/// Build the concatenated boundary MLE `B` of length
/// `N_BOUNDARY_CELLS = 2^14`. Slot `s ∈ 0..N_SPINE_SLOTS` occupies
/// indices `(s << N_PERM_VARS) .. ((s+1) << N_PERM_VARS)`; padded
/// slots are zero.
pub fn build_boundary_mle(
    slot_states: &[([Block128; STATE_SIZE], [Block128; STATE_SIZE])],
) -> Vec<Block128> {
    debug_assert_eq!(slot_states.len(), N_SPINE_SLOTS);
    let mut b = vec![Block128::ZERO; N_BOUNDARY_CELLS];
    for (s, (state_in, _)) in slot_states.iter().enumerate() {
        let witness = evaluate_permutation(*state_in);
        let state_mle = PermMle::from_witness(&witness).state;
        debug_assert_eq!(state_mle.len(), N_PERM_CELLS);
        let offset = s << N_PERM_VARS;
        b[offset..offset + N_PERM_CELLS].copy_from_slice(&state_mle);
    }
    b
}

/// Rebuild every slot's `(state_in, state_out)` natively. Matches
/// `oracle::evaluate_spine` but returns the intermediate witness
/// directly so both prover and verifier can drive their sumchecks off
/// it.
pub fn reconstruct_slot_states(
    circuit: &SpineCircuit,
    inputs: &SpineInputs,
) -> Vec<([Block128; STATE_SIZE], [Block128; STATE_SIZE])> {
    use crate::oracle::evaluate_spine;
    let w = evaluate_spine(circuit, inputs);
    w.slots
        .into_iter()
        .map(|s| (s.state_in, s.state_out))
        .collect()
}

/// Discharge a `BatchEvalReduction` against the natively-reconstructed
/// boundary MLE. Used by test harnesses.
pub fn discharge_boundary_native(
    circuit: &SpineCircuit,
    inputs: &SpineInputs,
    reduction: &crate::batch_eval::BatchEvalReduction,
) -> bool {
    let states = reconstruct_slot_states(circuit, inputs);
    let boundary_mle = build_boundary_mle(&states);
    noid_core::mle::evaluate::evaluate_slice(&boundary_mle, &reduction.point) == reduction.value
}

/// Convenience: reconstruct the wrap digest from `SpineInputs` without
/// building any proof. Useful for callers that need to compute the
/// claimed hash before opening a transcript.
pub fn compute_tx_body_hash(circuit: &SpineCircuit, inputs: &SpineInputs) -> [Block128; 2] {
    let states = reconstruct_slot_states(circuit, inputs);
    let wrap = states.last().expect("spine must have at least one slot");
    [wrap.1[0], wrap.1[1]]
}

#[cfg(test)]
mod unit {
    use super::*;
    use noid_poseidon2b::native::permutation::Poseidon2bPermutation;

    #[test]
    fn compute_tx_body_hash_matches_oracle() {
        use crate::oracle::evaluate_spine;
        let circuit = SpineCircuit::build();
        let inputs = SpineInputs {
            leaves: std::array::from_fn(|leaf| {
                [
                    Block128::from((2 * leaf + 1) as u128),
                    Block128::from((2 * leaf + 2) as u128),
                ]
            }),
        };
        let from_spine = compute_tx_body_hash(&circuit, &inputs);
        let from_oracle = evaluate_spine(&circuit, &inputs).tx_body_hash;
        assert_eq!(from_spine, from_oracle);

        // And the final lane we'd permute natively is consistent.
        let wrap = reconstruct_slot_states(&circuit, &inputs).pop().unwrap();
        let mut s = wrap.0;
        Poseidon2bPermutation.permute_mut(&mut s);
        assert_eq!([s[0], s[1]], from_spine);
    }
}
