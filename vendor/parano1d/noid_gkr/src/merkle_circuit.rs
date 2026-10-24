// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Typed topology for the Merkle path Kill-Shot circuit.
//!
//! A Merkle path through a consensus Poseidon2b tree consists of
//! `N_MERKLE_COMPRESSIONS` chained Poseidon2b compressions. Each
//! compression is 2 permutations (PermA absorbs the left digest,
//! PermB absorbs the right/sibling digest), totalling
//! `N_MERKLE_SLOTS` permutation slots in a single linear chain.
//!
//! The circuit is parameterised by a maximum path depth of 32 so it can
//! cover the exact UTXO sparse tree at maximum state size. Shorter paths
//! zero-pad unused slots via the
//! active cell mask `mu(x)` — same mechanism as spine/auth.
//!
//! ## What the circuit proves
//!
//! Given a leaf digest `L`, a list of sibling digests `S[0..depth]`,
//! and the expected root `R`, the circuit verifies:
//!
//! ```text
//!   h_0 = compress(L, S[0])    — or compress(S[0], L) depending on path bit
//!   h_1 = compress(h_0, S[1])
//!   ...
//!   h_{depth-1} = compress(h_{depth-2}, S[depth-1])
//!   h_{depth-1} == R
//! ```
//!
//! The path direction (left vs right) is encoded by swapping operands
//! before building the witness — the circuit itself always chains
//! PermA(left) → PermB(right).

use noid_core::{Block128, TowerField};
use noid_poseidon2b::native::domain::{capacity_iv, DomainTag, TAG_COMPRESS};

/// Maximum supported Merkle path depth for the exact UTXO sparse tree.
pub const MAX_MERKLE_DEPTH: usize = 32;

/// Permutation slots per compression: absorb left (PermA) + absorb
/// right (PermB).
pub const N_PERMS_PER_COMPRESS: usize = 2;

/// Total permutation slots in the circuit (fixed at compile time).
pub const N_MERKLE_SLOTS: usize = N_PERMS_PER_COMPRESS * MAX_MERKLE_DEPTH;

/// Per-slot role in the Merkle path circuit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MerkleSlotRole {
    /// Head of compression `level`. Absorbs the left digest into
    /// `[left_hi, left_lo, iv_hi, iv_lo]`.
    PermA { level: u8 },
    /// Chains from PermA of the same level. XOR-absorbs the right
    /// (sibling) digest into `state_out[0..1]` of PermA. Output
    /// `state_out[0..1]` is the compression result.
    PermB { level: u8 },
}

impl MerkleSlotRole {
    #[inline]
    pub fn level(&self) -> usize {
        match self {
            MerkleSlotRole::PermA { level } | MerkleSlotRole::PermB { level } => *level as usize,
        }
    }
}

/// Descriptor for one permutation slot in the Merkle path circuit.
#[derive(Debug, Clone, Copy)]
pub struct MerkleSlotDescriptor {
    pub id: usize,
    pub role: MerkleSlotRole,
    pub capacity_iv: [Block128; 2],
    pub is_head: bool,
    /// For PermB: chains from the PermA of the same level.
    /// For PermA at level > 0: chains from PermB of level-1 (output
    /// feeds as left input to next compression).
    pub prev_output_src: Option<usize>,
}

/// Public inputs to the Merkle path GKR.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MerklePathInputs {
    /// Leaf digest `[hi, lo]` — the segment root being opened.
    pub leaf: [Block128; 2],
    /// Sibling digests at each level. Unused levels (beyond
    /// `active_depth`) must be `[ZERO, ZERO]`.
    pub siblings: [[Block128; 2]; MAX_MERKLE_DEPTH],
    /// `false`: current digest is left child and sibling is right child.
    /// `true`: sibling is left child and current digest is right child.
    /// Unused levels must be `false`.
    pub directions: [bool; MAX_MERKLE_DEPTH],
    /// Expected root — `state_root`.
    pub expected_root: [Block128; 2],
    /// Number of active compression levels (8..=16). Determines which
    /// slots are live via the `mu` mask.
    pub active_depth: usize,
}

impl MerklePathInputs {
    pub fn zero() -> Self {
        Self {
            leaf: [Block128::ZERO; 2],
            siblings: [[Block128::ZERO; 2]; MAX_MERKLE_DEPTH],
            directions: [false; MAX_MERKLE_DEPTH],
            expected_root: [Block128::ZERO; 2],
            active_depth: 0,
        }
    }
}

/// Static topology of the 32-slot Merkle path circuit.
#[derive(Debug, Clone)]
pub struct MerkleCircuit {
    pub node_tag: DomainTag,
    pub slots: Vec<MerkleSlotDescriptor>,
}

impl MerkleCircuit {
    pub fn build() -> Self {
        Self::build_with_tag(TAG_COMPRESS)
    }

    pub fn build_with_tag(node_tag: DomainTag) -> Self {
        let iv = capacity_iv(node_tag);
        let mut slots = Vec::with_capacity(N_MERKLE_SLOTS);

        for level in 0..MAX_MERKLE_DEPTH {
            let base = slots.len();

            // PermA — head of compression at this level.
            // At level 0: absorbs the leaf directly.
            // At level > 0: chains from PermB of level-1 (the previous
            // compression's output feeds as the "left" operand).
            let prev_for_perm_a = if level == 0 {
                None
            } else {
                Some(base - 1) // PermB of previous level
            };

            slots.push(MerkleSlotDescriptor {
                id: base,
                role: MerkleSlotRole::PermA { level: level as u8 },
                capacity_iv: iv,
                is_head: level == 0,
                prev_output_src: prev_for_perm_a,
            });

            // PermB — chains from PermA of same level.
            slots.push(MerkleSlotDescriptor {
                id: base + 1,
                role: MerkleSlotRole::PermB { level: level as u8 },
                capacity_iv: iv,
                is_head: false,
                prev_output_src: Some(base),
            });
        }

        debug_assert_eq!(slots.len(), N_MERKLE_SLOTS);
        Self { node_tag, slots }
    }

    /// Slot id of the PermB at the given level — its `state_out[0..1]`
    /// is the compression result for that level.
    #[inline]
    pub fn output_slot(level: usize) -> usize {
        debug_assert!(level < MAX_MERKLE_DEPTH);
        level * N_PERMS_PER_COMPRESS + 1
    }

    /// Number of live slots for a given active depth.
    #[inline]
    pub fn live_slots(active_depth: usize) -> usize {
        N_PERMS_PER_COMPRESS * active_depth
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_has_expected_slot_count() {
        let c = MerkleCircuit::build();
        assert_eq!(c.slots.len(), N_MERKLE_SLOTS);
        assert_eq!(N_MERKLE_SLOTS, 64);
        assert_eq!(c.node_tag, TAG_COMPRESS);
    }

    #[test]
    fn topology_chain_structure() {
        let c = MerkleCircuit::build();
        // Level 0 PermA is head (no prev)
        assert!(c.slots[0].is_head);
        assert!(c.slots[0].prev_output_src.is_none());
        // Level 0 PermB chains from PermA
        assert!(!c.slots[1].is_head);
        assert_eq!(c.slots[1].prev_output_src, Some(0));
        // Level 1 PermA chains from Level 0 PermB
        assert!(!c.slots[2].is_head);
        assert_eq!(c.slots[2].prev_output_src, Some(1));
        // Level 1 PermB chains from Level 1 PermA
        assert!(!c.slots[3].is_head);
        assert_eq!(c.slots[3].prev_output_src, Some(2));
    }

    #[test]
    fn all_ivs_are_compress() {
        let c = MerkleCircuit::build();
        let iv = capacity_iv(TAG_COMPRESS);
        for s in &c.slots {
            assert_eq!(s.capacity_iv, iv);
        }
    }

    #[test]
    fn explicit_domain_changes_ivs() {
        use noid_poseidon2b::native::domain::TAG_EXSTNOD;

        let generic = MerkleCircuit::build();
        let exact = MerkleCircuit::build_with_tag(TAG_EXSTNOD);
        assert_eq!(exact.node_tag, TAG_EXSTNOD);
        assert_ne!(generic.slots[0].capacity_iv, exact.slots[0].capacity_iv);
        for s in &exact.slots {
            assert_eq!(s.capacity_iv, capacity_iv(TAG_EXSTNOD));
        }
    }

    #[test]
    fn output_slot_lands_on_perm_b() {
        let c = MerkleCircuit::build();
        for level in 0..MAX_MERKLE_DEPTH {
            let slot = &c.slots[MerkleCircuit::output_slot(level)];
            assert!(matches!(slot.role, MerkleSlotRole::PermB { level: l } if l as usize == level));
        }
    }
}
