// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical block shape classes for the sole Tx8x2 transaction form.
//!
//! Performance measurements live in `bench_prover` and are never protocol
//! constants. This module contains only current proof-shape identity.

use noid_poseidon2b::native::poseidon2b_hash_byte_slices;

/// One block shape class: a canonical physical-page tier.
///
/// Every proof-facing per-block structure is padded to this tier. The fixed
/// one-owner authorization statement has one geometry in every class; the
/// tier selects transaction, spend, universal-tree, and touched-slot capacity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ShapeClass {
    pub tier: usize,
}

impl ShapeClass {
    /// The class holding `page_count`, or `None` above the consensus maximum.
    pub fn for_page_count(page_count: usize) -> Option<Self> {
        Some(Self {
            tier: noid_chain::consensus::params::block_page_class_tier(page_count)?,
        })
    }

    /// Class live-input capacity used by spend-facing structures.
    pub fn spend_capacity(self) -> usize {
        noid_chain::consensus::params::block_class_spend_capacity(self.tier)
    }

    /// Authorization slots are padded to the next power of two.
    pub fn authorization_capacity(self) -> usize {
        self.tier.next_power_of_two()
    }

    /// Exact-state touched capacity. On payout heights the two development
    /// creations replace one physical user-page position, so the existing
    /// class maximum remains unchanged.
    pub fn touched_capacity(self) -> usize {
        self.spend_capacity() + self.tier * noid_tx::TX_OUTPUTS + 1
    }

    /// Maximum number of distinct 2^16-slot segments touched by the class.
    /// Consensus caps the attack tier at 256; smaller classes cannot touch
    /// more segments than they have actions.
    pub fn segment_capacity(self) -> usize {
        self.touched_capacity()
            .min(noid_chain::consensus::params::BLOCK_MAX_DISTINCT_SEGMENTS)
    }

    /// Physical bitmap-selected rows scanned by the stable compactor: ten
    /// positions per user body, the primary coinbase mint, and two
    /// fixed-position development-payout candidates gated by the schedule.
    /// Dyadic authorization PAD slots are deliberately not action slots.
    pub fn action_candidate_capacity(self) -> usize {
        self.tier * noid_tx::TX_ACTIONS + 3
    }

    /// Power-of-two Beneš routing width for the action candidates.
    pub fn action_sort_capacity(self) -> usize {
        self.action_candidate_capacity().next_power_of_two()
    }

    /// Maximum digest-only structural-frontier witness rows at depth 32 under
    /// the consensus 256-segment cap.
    pub fn frontier_sibling_capacity(self) -> usize {
        noid_chain::sparse_merkle::maximum_sibling_count_with_segment_cap(
            self.touched_capacity(),
            noid_gkr::MAX_MERKLE_DEPTH as u32,
            noid_chain::consensus::params::LOG_SEGMENT_SIZE,
            noid_chain::consensus::params::BLOCK_MAX_DISTINCT_SEGMENTS,
        )
    }

    /// Binary hash-combine rows required to reconstruct one root from the
    /// class's maximum touched leaves and frontier siblings.
    pub fn frontier_combine_capacity(self) -> usize {
        self.touched_capacity() + self.frontier_sibling_capacity() - 1
    }

    /// Domain-separated identity of the class key and current structural
    /// parameters. This is not an R1CS statement digest.
    pub fn shape_digest(self) -> [u8; 32] {
        let fields = [
            self.tier,
            self.spend_capacity(),
            self.authorization_capacity(),
            self.touched_capacity(),
            self.segment_capacity(),
            self.action_candidate_capacity(),
            self.action_sort_capacity(),
            self.frontier_sibling_capacity(),
            self.frontier_combine_capacity(),
            noid_tx::TX_INPUTS,
            noid_tx::TX_OUTPUTS,
            noid_tx::body_hash::BODY_HASH_LEAVES,
            noid_gkr::N_SPINE_SLOTS,
            noid_chain::tx_tree::TX_TREE_DEPTH,
        ];
        let mut encoded = Vec::with_capacity(fields.len() * 8);
        for field in fields {
            encoded.extend_from_slice(&(field as u64).to_le_bytes());
        }
        poseidon2b_hash_byte_slices(SHAPE_CLASS_DOMAIN, &[&encoded])
    }
}

/// Every current class in canonical ladder order: B25, B255.
pub fn enumerate_shape_classes() -> impl Iterator<Item = ShapeClass> {
    noid_chain::consensus::params::BLOCK_PAGE_CLASS_TIERS
        .into_iter()
        .map(|tier| ShapeClass { tier })
}

const SHAPE_CLASS_DOMAIN: &[u8] = b"NOID-TX8X2-SHAPE-CLASS-V4";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn class_table_is_finite_and_injective() {
        let classes: Vec<_> = enumerate_shape_classes().collect();
        assert_eq!(
            classes.iter().map(|class| class.tier).collect::<Vec<_>>(),
            [25, 255]
        );
        let digests: std::collections::HashSet<_> = classes
            .iter()
            .copied()
            .map(ShapeClass::shape_digest)
            .collect();
        assert_eq!(digests.len(), classes.len());

        assert_eq!(ShapeClass::for_page_count(0).unwrap().tier, 25);
        assert_eq!(ShapeClass::for_page_count(26).unwrap().tier, 255);
        assert!(ShapeClass::for_page_count(256).is_none());
        assert_eq!(
            ShapeClass::for_page_count(255).unwrap().spend_capacity(),
            noid_chain::consensus::params::BLOCK_MAX_LIVE_INPUTS
        );
        assert_eq!(
            ShapeClass::for_page_count(255)
                .unwrap()
                .authorization_capacity(),
            256
        );
        assert_eq!(
            ShapeClass::for_page_count(255).unwrap().touched_capacity(),
            1_531
        );
        assert_eq!(
            ShapeClass::for_page_count(255)
                .unwrap()
                .action_candidate_capacity(),
            2_553
        );
        assert_eq!(
            ShapeClass::for_page_count(255)
                .unwrap()
                .action_sort_capacity(),
            4_096
        );
        assert_eq!(noid_tx::body_hash::BODY_HASH_LEAVES, 16);
        assert_eq!(noid_gkr::N_SPINE_SLOTS, 31);
    }

    #[test]
    fn analytical_frontier_table_matches_live_class_caps() {
        let table: Vec<_> = enumerate_shape_classes()
            .map(|class| {
                (
                    class.tier,
                    class.touched_capacity(),
                    class.frontier_sibling_capacity(),
                    class.frontier_combine_capacity(),
                )
            })
            .collect();
        assert_eq!(
            table,
            [(25, 251, 6_029, 6_279), (255, 1_531, 22_468, 23_998)]
        );
    }

    #[test]
    fn action_compactor_table_excludes_the_b255_auth_pad() {
        let table: Vec<_> = enumerate_shape_classes()
            .map(|class| {
                (
                    class.tier,
                    class.action_candidate_capacity(),
                    class.action_sort_capacity(),
                    class.touched_capacity(),
                )
            })
            .collect();
        assert_eq!(table, [(25, 253, 256, 251), (255, 2_553, 4_096, 1_531)]);
    }

    #[test]
    fn paired_segment_capacity_table_is_exact() {
        let table: Vec<_> = enumerate_shape_classes()
            .map(|class| {
                (
                    class.tier,
                    class.touched_capacity(),
                    class.segment_capacity(),
                )
            })
            .collect();
        assert_eq!(table, [(25, 251, 251), (255, 1_531, 256)]);
    }
}
