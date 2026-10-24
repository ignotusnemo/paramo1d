// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Native Merkle path circuit execution (32 slots).
//!
//! Drives `N_MERKLE_SLOTS` Poseidon2b permutations in chain order,
//! producing a full witness suitable for the unified Kill-Shot sumcheck.
//! The result must agree byte-for-byte with
//! `noid_poseidon2b::native::compress` applied sequentially.

use noid_core::{Block128, TowerField};
use noid_poseidon2b::native::permutation::Poseidon2bPermutation;

use crate::merkle_circuit::{
    MerkleCircuit, MerklePathInputs, MerkleSlotDescriptor, MerkleSlotRole, MAX_MERKLE_DEPTH,
    N_MERKLE_SLOTS,
};

/// Per-slot state snapshot (same shape as `AuthSlotState`).
#[derive(Debug, Clone, Copy)]
pub struct MerkleSlotState {
    pub state_in: [Block128; 4],
    pub state_out: [Block128; 4],
}

impl MerkleSlotState {
    #[inline]
    pub fn digest(&self) -> [Block128; 2] {
        [self.state_out[0], self.state_out[1]]
    }
}

/// Full Merkle path witness.
#[derive(Debug, Clone)]
pub struct MerkleWitness {
    pub slots: Vec<MerkleSlotState>,
    /// The root derived by chaining all compressions.
    pub derived_root: [Block128; 2],
}

/// Execute the Merkle path circuit natively, returning the full witness.
pub fn evaluate_merkle(circuit: &MerkleCircuit, inputs: &MerklePathInputs) -> MerkleWitness {
    let perm = Poseidon2bPermutation;
    let mut slots: Vec<MerkleSlotState> = Vec::with_capacity(N_MERKLE_SLOTS);

    for slot in &circuit.slots {
        let state_in = build_state_in(slot, inputs, &slots);
        let mut state_out = state_in;
        perm.permute_mut(&mut state_out);
        slots.push(MerkleSlotState {
            state_in,
            state_out,
        });
    }

    // The derived root is the output of the last active PermB.
    let root_slot = if inputs.active_depth > 0 {
        MerkleCircuit::output_slot(inputs.active_depth - 1)
    } else {
        0
    };
    let derived_root = slots[root_slot].digest();

    MerkleWitness {
        slots,
        derived_root,
    }
}

fn build_state_in(
    slot: &MerkleSlotDescriptor,
    inputs: &MerklePathInputs,
    prev: &[MerkleSlotState],
) -> [Block128; 4] {
    let [iv_hi, iv_lo] = slot.capacity_iv;

    match slot.role {
        MerkleSlotRole::PermA { level } => {
            let level = level as usize;
            let current = if level == 0 {
                inputs.leaf
            } else {
                let src_id = slot
                    .prev_output_src
                    .expect("PermA at level > 0 must chain from prev PermB");
                prev[src_id].digest()
            };
            let sibling = inputs.siblings[level];
            let left = if inputs.directions[level] {
                sibling
            } else {
                current
            };
            [left[0], left[1], iv_hi, iv_lo]
        }
        MerkleSlotRole::PermB { level } => {
            // Chains from PermA of same level: XOR sibling into rate.
            let src_id = slot.prev_output_src.expect("PermB must chain from PermA");
            let s = prev[src_id].state_out;
            let level = level as usize;
            let current = if level == 0 {
                inputs.leaf
            } else {
                let current_src = slot
                    .id
                    .checked_sub(2)
                    .expect("level > 0 PermB must have previous PermB");
                prev[current_src].digest()
            };
            let sibling = inputs.siblings[level];
            let right = if inputs.directions[level] {
                current
            } else {
                sibling
            };
            [s[0] + right[0], s[1] + right[1], s[2], s[3]]
        }
    }
}

/// Compute the honest root by chaining compressions natively.
pub fn compute_merkle_root(
    circuit: &MerkleCircuit,
    leaf: [Block128; 2],
    siblings: &[[Block128; 2]],
    active_depth: usize,
) -> [Block128; 2] {
    compute_merkle_root_with_directions(
        circuit,
        leaf,
        siblings,
        &[false; MAX_MERKLE_DEPTH],
        active_depth,
    )
}

/// Compute the honest directed root by chaining compressions natively.
pub fn compute_merkle_root_with_directions(
    circuit: &MerkleCircuit,
    leaf: [Block128; 2],
    siblings: &[[Block128; 2]],
    directions: &[bool; MAX_MERKLE_DEPTH],
    active_depth: usize,
) -> [Block128; 2] {
    let mut full_siblings = [[Block128::ZERO; 2]; MAX_MERKLE_DEPTH];
    for (i, s) in siblings.iter().enumerate().take(active_depth) {
        full_siblings[i] = *s;
    }
    let inputs = MerklePathInputs {
        leaf,
        siblings: full_siblings,
        directions: *directions,
        expected_root: [Block128::ZERO; 2],
        active_depth,
    };
    let w = evaluate_merkle(circuit, &inputs);
    w.derived_root
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_core::CanonicalSerialize;
    use noid_poseidon2b::native::compress;

    fn fields_to_digest(f: [Block128; 2]) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[..16].copy_from_slice(&f[0].to_bytes());
        out[16..].copy_from_slice(&f[1].to_bytes());
        out
    }

    fn digest_to_fields(d: &[u8; 32]) -> [Block128; 2] {
        let mut a = [0u8; 16];
        let mut b = [0u8; 16];
        a.copy_from_slice(&d[..16]);
        b.copy_from_slice(&d[16..]);
        [
            Block128::from(u128::from_le_bytes(a)),
            Block128::from(u128::from_le_bytes(b)),
        ]
    }

    #[test]
    fn single_compression_matches_native() {
        let circuit = MerkleCircuit::build();
        let left = [0x11u8; 32];
        let right = [0x22u8; 32];
        let native_out = compress(&left, &right);

        let inputs = MerklePathInputs {
            leaf: digest_to_fields(&left),
            siblings: {
                let mut s = [[Block128::ZERO; 2]; MAX_MERKLE_DEPTH];
                s[0] = digest_to_fields(&right);
                s
            },
            directions: [false; MAX_MERKLE_DEPTH],
            expected_root: digest_to_fields(&native_out),
            active_depth: 1,
        };
        let w = evaluate_merkle(&circuit, &inputs);
        assert_eq!(fields_to_digest(w.derived_root), native_out);
    }

    #[test]
    fn three_level_path_matches_native() {
        let circuit = MerkleCircuit::build();
        let leaf = [0xAAu8; 32];
        let s0 = [0xBBu8; 32];
        let s1 = [0xCCu8; 32];
        let s2 = [0xDDu8; 32];

        let h0 = compress(&leaf, &s0);
        let h1 = compress(&h0, &s1);
        let h2 = compress(&h1, &s2);

        let inputs = MerklePathInputs {
            leaf: digest_to_fields(&leaf),
            siblings: {
                let mut s = [[Block128::ZERO; 2]; MAX_MERKLE_DEPTH];
                s[0] = digest_to_fields(&s0);
                s[1] = digest_to_fields(&s1);
                s[2] = digest_to_fields(&s2);
                s
            },
            directions: [false; MAX_MERKLE_DEPTH],
            expected_root: digest_to_fields(&h2),
            active_depth: 3,
        };
        let w = evaluate_merkle(&circuit, &inputs);
        assert_eq!(fields_to_digest(w.derived_root), h2);
    }

    #[test]
    fn full_depth_16_path() {
        let circuit = MerkleCircuit::build();
        let mut current = [0x42u8; 32];
        let mut siblings_raw = [[0u8; 32]; MAX_MERKLE_DEPTH];
        for (i, sibling) in siblings_raw.iter_mut().enumerate().take(MAX_MERKLE_DEPTH) {
            *sibling = [(i as u8).wrapping_add(1); 32];
            current = compress(&current, sibling);
        }

        let leaf_fields = digest_to_fields(&[0x42u8; 32]);
        let mut siblings = [[Block128::ZERO; 2]; MAX_MERKLE_DEPTH];
        for (i, sibling) in siblings_raw.iter().enumerate().take(MAX_MERKLE_DEPTH) {
            siblings[i] = digest_to_fields(sibling);
        }
        let inputs = MerklePathInputs {
            leaf: leaf_fields,
            siblings,
            directions: [false; MAX_MERKLE_DEPTH],
            expected_root: digest_to_fields(&current),
            active_depth: MAX_MERKLE_DEPTH,
        };
        let w = evaluate_merkle(&circuit, &inputs);
        assert_eq!(fields_to_digest(w.derived_root), current);
    }

    #[test]
    fn directed_path_matches_native_left_right_order() {
        use noid_poseidon2b::native::compress;

        let circuit = MerkleCircuit::build();
        let leaf = [0x11u8; 32];
        let s0 = [0x22u8; 32];
        let s1 = [0x33u8; 32];
        let s2 = [0x44u8; 32];

        let h0 = compress(&s0, &leaf);
        let h1 = compress(&h0, &s1);
        let h2 = compress(&s2, &h1);

        let mut siblings = [[Block128::ZERO; 2]; MAX_MERKLE_DEPTH];
        siblings[0] = digest_to_fields(&s0);
        siblings[1] = digest_to_fields(&s1);
        siblings[2] = digest_to_fields(&s2);
        let mut directions = [false; MAX_MERKLE_DEPTH];
        directions[0] = true;
        directions[2] = true;
        let inputs = MerklePathInputs {
            leaf: digest_to_fields(&leaf),
            siblings,
            directions,
            expected_root: digest_to_fields(&h2),
            active_depth: 3,
        };

        let w = evaluate_merkle(&circuit, &inputs);
        assert_eq!(fields_to_digest(w.derived_root), h2);
    }
}
