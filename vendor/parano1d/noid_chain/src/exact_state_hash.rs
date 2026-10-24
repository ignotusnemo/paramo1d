// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Domain-separated exact-state commitment hashes.
//!
//! These helpers are intentionally independent from the raw segment storage
//! commitment path. They are pure building blocks for the exact Merkle state
//! transition proof.

#[cfg(test)]
use noid_core::Block128;
use noid_poseidon2b::native::compression::{compress_with_tag, Poseidon2bSponge};
use noid_poseidon2b::native::domain::{capacity_iv, TAG_EXSTNOD, TAG_EXSTSLT};

use crate::fri_state::SlotValue;

/// 32-byte exact-state hash.
pub type StateHash = [u8; 32];

/// Hash one exact-state slot leaf.
///
/// The full packed `(amount, creation_id)` lane is absorbed. Every 128-bit
/// lane is a canonical pair of `u64`s, so hashing is infallible.
pub fn slot_leaf_hash(slot: SlotValue) -> StateHash {
    let mut s = Poseidon2bSponge::with_iv(capacity_iv(TAG_EXSTSLT));
    s.absorb(slot.value);
    s.absorb_pair(slot.owner_hi, slot.owner_lo);
    s.finalize()
}

/// Hash one exact-state binary Merkle node.
pub fn state_node_hash(left: StateHash, right: StateHash) -> StateHash {
    compress_with_tag(TAG_EXSTNOD, &left, &right)
}

/// Precompute `Z_0..=Z_max_depth` for the exact sparse UTXO tree.
pub fn zero_slot_roots(max_depth: usize) -> Vec<StateHash> {
    let mut roots = Vec::with_capacity(max_depth.saturating_add(1));
    roots.push(slot_leaf_hash(SlotValue::EMPTY));
    for depth in 0..max_depth {
        let z = roots[depth];
        roots.push(state_node_hash(z, z));
    }
    roots
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_core::TowerField;

    fn slot(value: u128, hi: u128, lo: u128) -> SlotValue {
        SlotValue {
            value: Block128::from(value),
            owner_hi: Block128::from(hi),
            owner_lo: Block128::from(lo),
        }
    }

    #[test]
    fn slot_hash_binds_full_packed_value_and_zero_id_uses_low_lane() {
        let s = slot(42, 7, 9);
        assert_eq!(slot_leaf_hash(s), slot_leaf_hash(s));
        let incarnation = slot((1u128 << 64) | 42, 7, 9);
        assert_ne!(slot_leaf_hash(s), slot_leaf_hash(incarnation));

        let mut zero_id = Poseidon2bSponge::with_iv(capacity_iv(TAG_EXSTSLT));
        zero_id.absorb(Block128::from(42u64));
        zero_id.absorb_pair(Block128::from(7u64), Block128::from(9u64));
        assert_eq!(slot_leaf_hash(s), zero_id.finalize());
    }

    #[test]
    fn node_order_and_domains_matter() {
        let a = slot_leaf_hash(slot(1, 2, 3));
        let b = slot_leaf_hash(slot(4, 5, 6));
        assert_ne!(state_node_hash(a, b), state_node_hash(b, a));
        assert_ne!(slot_leaf_hash(SlotValue::EMPTY), state_node_hash(a, b));
    }

    #[test]
    fn zero_roots_match_explicit_empty_trees() {
        let roots = zero_slot_roots(5);
        assert_eq!(roots.len(), 6);
        let mut root = slot_leaf_hash(SlotValue::EMPTY);
        assert_eq!(root, roots[0]);
        for &expected in roots.iter().take(6).skip(1) {
            root = state_node_hash(root, root);
            assert_eq!(root, expected);
        }
    }

    #[test]
    fn zero_root_golden_vectors_are_stable() {
        let roots = zero_slot_roots(32);
        let vectors = [
            (
                0usize,
                [
                    129, 102, 210, 70, 24, 117, 164, 73, 150, 82, 163, 157, 56, 215, 196, 144, 152,
                    52, 131, 97, 217, 58, 221, 252, 173, 30, 138, 210, 158, 138, 112, 66,
                ],
            ),
            (
                1usize,
                [
                    6, 197, 99, 94, 29, 133, 197, 229, 174, 5, 238, 221, 187, 30, 247, 147, 65,
                    157, 47, 74, 14, 197, 144, 45, 189, 81, 132, 99, 44, 230, 81, 177,
                ],
            ),
            (
                4usize,
                [
                    170, 248, 23, 183, 124, 240, 4, 165, 25, 234, 105, 246, 1, 26, 145, 66, 37,
                    100, 219, 76, 136, 251, 74, 103, 231, 72, 51, 39, 246, 32, 50, 67,
                ],
            ),
            (
                16usize,
                [
                    83, 188, 60, 195, 138, 167, 135, 135, 217, 179, 116, 131, 126, 82, 131, 158, 8,
                    219, 2, 75, 184, 7, 169, 218, 53, 192, 1, 239, 60, 225, 155, 165,
                ],
            ),
            (
                24usize,
                [
                    92, 127, 55, 18, 97, 28, 131, 106, 44, 106, 176, 68, 141, 50, 194, 113, 240,
                    78, 50, 19, 86, 14, 138, 83, 33, 51, 28, 214, 165, 201, 132, 146,
                ],
            ),
            (
                32usize,
                [
                    198, 166, 100, 191, 38, 11, 167, 36, 137, 171, 94, 54, 102, 98, 128, 161, 43,
                    65, 20, 230, 75, 130, 35, 253, 184, 60, 150, 192, 56, 211, 164, 188,
                ],
            ),
        ];
        for (depth, expected) in vectors {
            assert_eq!(roots[depth], expected, "depth {depth}");
        }
    }

    #[test]
    fn endian_tamper_changes_hash() {
        let s = slot(0x0102, 0x0304, 0x0506);
        let mut tampered = s;
        tampered.value = Block128::from(0x0201u128);
        assert_ne!(slot_leaf_hash(s), slot_leaf_hash(tampered));
        assert_ne!(Block128::ZERO, Block128::ONE);
    }
}
