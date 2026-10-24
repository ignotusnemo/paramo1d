// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Deterministic transaction epoch-anchor transition.
//!
//! This schedule is intentionally independent from ASERT's difficulty epochs.
//! Every user transaction in a child block binds the anchor that was current at
//! the start of that block. Coinbase instead binds the immediate parent id.

use noid_poseidon2b::primitives::Digest;

use crate::block::Block;
use crate::consensus::{params::TX_EPOCH_BLOCKS, pow::block_id, ConsensusError};

/// Canonical integer decomposition of a block height by the transaction epoch.
///
/// `is_boundary` is deliberately derived from the remainder rather than stored
/// as an independent bit. Height zero is mathematically divisible by the epoch
/// length; genesis is initialized separately and is never passed through the
/// accepted-child accumulator transition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TxEpochHeightDecomposition {
    pub quotient: u64,
    pub remainder: u8,
}

impl TxEpochHeightDecomposition {
    #[inline]
    pub const fn is_boundary(self) -> bool {
        self.remainder == 0
    }
}

/// Decompose `height = TX_EPOCH_BLOCKS * quotient + remainder`, checking the
/// reconstruction with overflow-detecting integer operations.
///
/// For the fixed 144-block epoch and every `u64` height this returns `Some`.
/// Keeping the checked contract makes this the native specification twin of
/// the recursive quotient/remainder gadget instead of relying on that fact
/// implicitly.
#[inline]
pub fn checked_tx_epoch_height_decomposition(height: u64) -> Option<TxEpochHeightDecomposition> {
    let quotient = height.checked_div(TX_EPOCH_BLOCKS)?;
    let remainder_u64 = height.checked_rem(TX_EPOCH_BLOCKS)?;
    let recomposed = quotient
        .checked_mul(TX_EPOCH_BLOCKS)?
        .checked_add(remainder_u64)?;
    if recomposed != height || remainder_u64 >= TX_EPOCH_BLOCKS {
        return None;
    }
    Some(TxEpochHeightDecomposition {
        quotient,
        remainder: remainder_u64.try_into().ok()?,
    })
}

/// Height of the canonical header that supplies a child block's user anchor.
///
/// Boundary block `k * TX_EPOCH_BLOCKS` still consumes the preceding anchor;
/// its own id becomes active only after that block is accepted.
#[inline]
pub const fn tx_epoch_anchor_height_for_child(child_height: u64) -> u64 {
    if child_height == 0 {
        0
    } else {
        ((child_height - 1) / TX_EPOCH_BLOCKS) * TX_EPOCH_BLOCKS
    }
}

/// Validate the exact start-of-block anchors for every serialized body.
pub fn validate_block_epoch_anchors(
    block: &Block,
    user_epoch_anchor_id: Digest,
    parent_id: Digest,
) -> Result<(), ConsensusError> {
    for tx in &block.transactions {
        let expected = if tx.body.is_coinbase {
            parent_id
        } else {
            user_epoch_anchor_id
        };
        if tx.body.epoch_anchor != expected {
            return Err(if tx.body.is_coinbase {
                ConsensusError::BadCoinbaseAnchor
            } else {
                ConsensusError::BadEpochAnchor
            });
        }
    }
    Ok(())
}

/// Deterministic accumulator transition for the epoch-anchor lane.
#[inline]
pub fn next_tx_epoch_anchor_id(
    start_anchor_id: Digest,
    accepted_child_height: u64,
    accepted_child_id: Digest,
) -> Digest {
    let boundary = checked_tx_epoch_height_decomposition(accepted_child_height)
        .expect("every u64 height has a checked transaction-epoch decomposition")
        .is_boundary();
    if accepted_child_height != 0 && boundary {
        accepted_child_id
    } else {
        start_anchor_id
    }
}

/// Resolve the expected user anchor from a canonical header lookup.
pub fn resolve_user_epoch_anchor_id(
    child_height: u64,
    mut header_at: impl FnMut(u64) -> Option<crate::block_header::BlockHeader>,
) -> Option<Digest> {
    let height = tx_epoch_anchor_height_for_child(child_height);
    header_at(height).map(|header| block_id(&header))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_height_decomposition_marks_exact_boundaries() {
        for (height, quotient, remainder, boundary) in [
            (0, 0, 0, true),
            (1, 0, 1, false),
            (143, 0, 143, false),
            (144, 1, 0, true),
            (145, 1, 1, false),
            (287, 1, 143, false),
            (288, 2, 0, true),
            (289, 2, 1, false),
        ] {
            let decomposition =
                checked_tx_epoch_height_decomposition(height).expect("test height decomposes");
            assert_eq!(decomposition.quotient, quotient, "height {height}");
            assert_eq!(decomposition.remainder, remainder, "height {height}");
            assert_eq!(decomposition.is_boundary(), boundary, "height {height}");
            assert_eq!(
                decomposition.quotient * TX_EPOCH_BLOCKS + u64::from(decomposition.remainder),
                height
            );
        }
    }

    #[test]
    fn boundary_block_consumes_old_anchor_then_advances() {
        assert_eq!(tx_epoch_anchor_height_for_child(1), 0);
        assert_eq!(tx_epoch_anchor_height_for_child(143), 0);
        assert_eq!(tx_epoch_anchor_height_for_child(144), 0);
        assert_eq!(tx_epoch_anchor_height_for_child(145), 144);
        assert_eq!(tx_epoch_anchor_height_for_child(288), 144);
        assert_eq!(tx_epoch_anchor_height_for_child(289), 288);

        let old = [1u8; 32];
        let boundary = [2u8; 32];
        assert_eq!(next_tx_epoch_anchor_id(old, 143, boundary), old);
        assert_eq!(next_tx_epoch_anchor_id(old, 144, boundary), boundary);
    }
}
