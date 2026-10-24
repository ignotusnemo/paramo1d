// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Exact local header-tip anchor for public history proofs.
//!
//! Nodes validate and retain the canonical header chain itself. A block id
//! commits to the complete header and recursively to its ancestry through
//! `prev_block_hash`, so history proofs bind directly to the locally selected
//! tip instead of maintaining a parallel rolling projection hash.

use noid_poseidon2b::primitives::{Address, Digest};

use crate::block_header::{hash_block_header, BlockHeader};

/// Exact tip of a locally verified canonical header prefix.
///
/// `cumulative_chainwork` is the exact chainwork recorded by native header
/// validation for this tip. `block_id` commits to the full ancestry.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct HeaderChainAnchor {
    pub height: u64,
    pub block_id: Digest,
    pub state_root: Digest,
    pub tx_root: Digest,
    pub miner_address: Address,
    pub log_slots: u32,
    pub active_slot_count: u64,
    pub alloc_counter: u64,
    pub cumulative_chainwork: Digest,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HeaderChainAnchorError {
    Empty,
    StartsAfterGenesis { first_height: u64 },
    NonContiguous { expected: u64, actual: u64 },
    BadParentLink { height: u64 },
}

impl std::fmt::Display for HeaderChainAnchorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "empty header prefix"),
            Self::StartsAfterGenesis { first_height } => {
                write!(f, "header prefix starts at h={first_height}, expected h=0")
            }
            Self::NonContiguous { expected, actual } => {
                write!(
                    f,
                    "non-contiguous header prefix: expected h={expected}, got h={actual}"
                )
            }
            Self::BadParentLink { height } => {
                write!(f, "bad parent link at h={height}")
            }
        }
    }
}

impl std::error::Error for HeaderChainAnchorError {}

/// Extend a verified header-chain anchor by one canonical child header.
///
/// This carries the exact child tip and cumulative chainwork already validated
/// by the native header path; it does not build a second history commitment.
pub fn extend_header_chain_anchor(
    previous: &HeaderChainAnchor,
    header: &BlockHeader,
    cumulative_chainwork: Digest,
) -> Result<HeaderChainAnchor, HeaderChainAnchorError> {
    extend_header_chain_anchor_prehashed(
        previous,
        header,
        hash_block_header(header),
        cumulative_chainwork,
    )
}

/// Extend an anchor with the block id produced by the authoritative native
/// header pass. This avoids re-running the same hash while streaming a sealed
/// snapshot header archive into durable storage.
pub(crate) fn extend_header_chain_anchor_prehashed(
    previous: &HeaderChainAnchor,
    header: &BlockHeader,
    block_id: Digest,
    cumulative_chainwork: Digest,
) -> Result<HeaderChainAnchor, HeaderChainAnchorError> {
    let expected = previous.height.saturating_add(1);
    if header.height != expected {
        return Err(HeaderChainAnchorError::NonContiguous {
            expected,
            actual: header.height,
        });
    }
    if header.prev_block_hash != previous.block_id {
        return Err(HeaderChainAnchorError::BadParentLink {
            height: header.height,
        });
    }

    Ok(HeaderChainAnchor {
        height: header.height,
        block_id,
        state_root: header.state_root,
        tx_root: header.tx_root,
        miner_address: header.miner_address,
        log_slots: header.log_slots,
        active_slot_count: header.active_slot_count,
        alloc_counter: header.alloc_counter,
        cumulative_chainwork,
    })
}

/// Build an anchor for a contiguous header prefix from genesis through tip.
pub fn compute_header_chain_anchor<'a, I>(
    headers: I,
    cumulative_chainwork: Digest,
) -> Result<HeaderChainAnchor, HeaderChainAnchorError>
where
    I: IntoIterator<Item = &'a BlockHeader>,
{
    let mut iter = headers.into_iter();
    let first = iter.next().ok_or(HeaderChainAnchorError::Empty)?;
    if first.height != 0 {
        return Err(HeaderChainAnchorError::StartsAfterGenesis {
            first_height: first.height,
        });
    }

    let mut expected_height = 0u64;
    let mut previous_block_id = [0u8; 32];
    let mut tip = None;

    for header in std::iter::once(first).chain(iter) {
        if header.height != expected_height {
            return Err(HeaderChainAnchorError::NonContiguous {
                expected: expected_height,
                actual: header.height,
            });
        }
        if header.height > 0 && header.prev_block_hash != previous_block_id {
            return Err(HeaderChainAnchorError::BadParentLink {
                height: header.height,
            });
        }

        let block_id = hash_block_header(header);
        previous_block_id = block_id;
        tip = Some((*header, block_id));
        expected_height = expected_height.saturating_add(1);
    }

    let (tip_header, block_id) = tip.expect("non-empty iterator handled above");
    Ok(HeaderChainAnchor {
        height: tip_header.height,
        block_id,
        state_root: tip_header.state_root,
        tx_root: tip_header.tx_root,
        miner_address: tip_header.miner_address,
        log_slots: tip_header.log_slots,
        active_slot_count: tip_header.active_slot_count,
        alloc_counter: tip_header.alloc_counter,
        cumulative_chainwork,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::primitives::Address;

    fn header(height: u64, prev: Digest, state_seed: u8) -> BlockHeader {
        BlockHeader {
            prev_block_hash: prev,
            state_root: [state_seed; 32],
            tx_root: [state_seed ^ 0x55; 32],
            timestamp: 1_700_000_000 + height,
            height,
            miner_address: Address([0x44; 32]),
            nonce: height as u128,
            difficulty_target: [0x7f; 32],
            log_slots: 24,
            active_slot_count: height,
            alloc_counter: height * 2,
        }
    }

    fn three_headers() -> Vec<BlockHeader> {
        let h0 = header(0, [0u8; 32], 1);
        let h0_hash = hash_block_header(&h0);
        let h1 = header(1, h0_hash, 2);
        let h1_hash = hash_block_header(&h1);
        let h2 = header(2, h1_hash, 3);
        vec![h0, h1, h2]
    }

    #[test]
    fn anchor_binds_exact_tip_and_chainwork() {
        let headers = three_headers();
        let work = [0xAA; 32];
        let anchor = compute_header_chain_anchor(headers.iter(), work).unwrap();

        assert_eq!(anchor.height, 2);
        assert_eq!(anchor.block_id, hash_block_header(&headers[2]));
        assert_eq!(anchor.state_root, headers[2].state_root);
        assert_eq!(anchor.tx_root, headers[2].tx_root);
        assert_eq!(anchor.miner_address, headers[2].miner_address);
        assert_eq!(anchor.log_slots, headers[2].log_slots);
        assert_eq!(anchor.active_slot_count, headers[2].active_slot_count);
        assert_eq!(anchor.alloc_counter, headers[2].alloc_counter);
        assert_eq!(anchor.cumulative_chainwork, work);
    }

    #[test]
    fn tip_block_id_commits_changed_ancestor_after_relink() {
        let headers = three_headers();
        let mut changed = headers.clone();
        changed[1].active_slot_count += 1;
        changed[2].prev_block_hash = hash_block_header(&changed[1]);
        let original = compute_header_chain_anchor(headers.iter(), [1u8; 32]).unwrap();
        let changed = compute_header_chain_anchor(changed.iter(), [1u8; 32]).unwrap();

        assert_ne!(original.block_id, changed.block_id);
        assert_eq!(original.height, changed.height);
        assert_eq!(original.state_root, changed.state_root);
        assert_eq!(original.tx_root, changed.tx_root);
    }

    #[test]
    fn rejects_non_contiguous_prefix() {
        let mut headers = three_headers();
        headers[2].height = 3;
        assert_eq!(
            compute_header_chain_anchor(headers.iter(), [0u8; 32]),
            Err(HeaderChainAnchorError::NonContiguous {
                expected: 2,
                actual: 3
            })
        );
    }

    #[test]
    fn rejects_bad_parent_link() {
        let mut headers = three_headers();
        headers[2].prev_block_hash[0] ^= 1;
        assert_eq!(
            compute_header_chain_anchor(headers.iter(), [0u8; 32]),
            Err(HeaderChainAnchorError::BadParentLink { height: 2 })
        );
    }

    #[test]
    fn incremental_anchor_matches_full_prefix() {
        let headers = three_headers();
        let a0 = compute_header_chain_anchor(headers[..1].iter(), [1u8; 32]).unwrap();
        let a1 = extend_header_chain_anchor(&a0, &headers[1], [2u8; 32]).unwrap();
        let a2 = extend_header_chain_anchor(&a1, &headers[2], [3u8; 32]).unwrap();
        let full = compute_header_chain_anchor(headers.iter(), [3u8; 32]).unwrap();

        assert_eq!(a2, full);
    }
}
