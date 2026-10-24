// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Fork choice rule: heaviest chain wins.
//!
//! Paranoid uses **cumulative PoW work** as the canonical chain selector,
//! identical to Bitcoin's "most work" rule. Since PoW provides ordering
//! only (not security), the rule keeps the chain deterministic.
//!
//! Tie-break: if two chains have equal work, the lexicographically smaller
//! block hash (byte 0 first) wins. This is deterministic and prevents
//! accidental forks from timestamp ties.
//!
//! Reference: Bitcoin Core `src/chain.h::CChainWork`, Grin `chain/src/chain.rs`.

use crate::consensus::difficulty::work_gt;
use crate::consensus::params::CONSENSUS_FINALITY_DEPTH;
use crate::storage::FinalizedCheckpoint;

/// Compare two chain tips by cumulative PoW work.
///
/// Work for a block = 2^256 / difficulty_target (more work = smaller target).
/// We approximate work by comparing difficulty targets inversely: the chain
/// whose tip required MORE work (smaller target) wins.
///
/// Returns `Ordering::Greater` if chain A has more work than chain B.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChainChoice {
    /// Chain A is heavier (should be canonical).
    A,
    /// Chain B is heavier (should be canonical).
    B,
    /// Equal work: tie-broken by block hash.
    Equal,
}

/// Full fork choice using cumulative chainwork (production API).
///
/// # Arguments
/// - `chainwork_a`: cumulative work for chain A (sum of block_work() for all blocks)
/// - `chainwork_b`: cumulative work for chain B
/// - `hash_a`, `hash_b`: tip hashes for tie-breaking
pub fn choose_chain_by_work(
    chainwork_a: &[u8; 32],
    hash_a: &[u8; 32],
    chainwork_b: &[u8; 32],
    hash_b: &[u8; 32],
) -> ChainChoice {
    if work_gt(chainwork_a, chainwork_b) {
        return ChainChoice::A;
    }
    if work_gt(chainwork_b, chainwork_a) {
        return ChainChoice::B;
    }

    if hash_a < hash_b {
        ChainChoice::A
    } else if hash_b < hash_a {
        ChainChoice::B
    } else {
        ChainChoice::Equal
    }
}

/// Return true when a candidate chain preserves the local finalized prefix.
///
/// Fork choice must choose maximum cumulative work only among candidates for
/// which the block hash at `finalized.height` equals `finalized.hash`.
pub fn preserves_finalized_prefix(
    candidate_hash_at_finalized_height: Option<[u8; 32]>,
    finalized: FinalizedCheckpoint,
) -> bool {
    candidate_hash_at_finalized_height == Some(finalized.hash)
}

/// Check whether a reorg is allowed by depth alone.
///
/// Callers must also enforce `preserves_finalized_prefix`; this helper only
/// answers whether the depth is inside the configured consensus finality window.
pub fn reorg_allowed(n_confirmations_to_undo: u64) -> bool {
    n_confirmations_to_undo <= CONSENSUS_FINALITY_DEPTH
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consensus::difficulty::{add_work, block_work};

    #[test]
    fn hash_tiebreak() {
        let work = [7u8; 32];
        let hash_a = [0u8; 32]; // lexicographically smaller
        let hash_b = [1u8; 32];
        assert_eq!(
            choose_chain_by_work(&work, &hash_a, &work, &hash_b),
            ChainChoice::A
        );
        assert_eq!(
            choose_chain_by_work(&work, &hash_b, &work, &hash_a),
            ChainChoice::B
        );
    }

    #[test]
    fn same_block_is_equal() {
        let work = [7u8; 32];
        let h = [0u8; 32];
        assert_eq!(
            choose_chain_by_work(&work, &h, &work, &h),
            ChainChoice::Equal
        );
    }

    #[test]
    fn reorg_within_finality_allowed() {
        assert!(reorg_allowed(0));
        assert!(reorg_allowed(17));
        assert!(reorg_allowed(18)); // preserve the finalized ancestor, replace 18 descendants
        assert!(!reorg_allowed(19));
        assert!(!reorg_allowed(100));
    }

    #[test]
    fn finalized_prefix_must_match() {
        let finalized = FinalizedCheckpoint {
            height: 7,
            hash: [0xAA; 32],
        };
        assert!(preserves_finalized_prefix(Some([0xAA; 32]), finalized));
        assert!(!preserves_finalized_prefix(Some([0xBB; 32]), finalized));
        assert!(!preserves_finalized_prefix(None, finalized));
    }

    #[test]
    fn more_work_wins_over_longer_chain() {
        // hard = 2^224, easy = 2^252 (old genesis); work_a(10 blocks) >> work_b(100 blocks)
        let hard_target = {
            let mut t = [0u8; 32];
            t[28] = 0x01;
            t
        };
        let easy_target = {
            let mut t = [0u8; 32];
            t[31] = 0x10;
            t
        };

        let mut work_a = [0u8; 32];
        for _ in 0..10 {
            work_a = add_work(&work_a, &block_work(&hard_target));
        }
        let mut work_b = [0u8; 32];
        for _ in 0..100 {
            work_b = add_work(&work_b, &block_work(&easy_target));
        }

        let h = [0u8; 32];
        // With cumulative work, chain A should win even though it's shorter.
        let result = choose_chain_by_work(&work_a, &h, &work_b, &h);
        assert_eq!(
            result,
            ChainChoice::A,
            "more work chain should win regardless of height"
        );
    }
}
