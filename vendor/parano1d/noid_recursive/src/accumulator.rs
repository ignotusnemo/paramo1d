// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Direct recursive-chain continuity boundary.

use noid_chain::block_header::{semantic_header_id, BlockHeader};
use noid_chain::consensus::{
    checked_tx_epoch_height_decomposition, genesis_header, tx_epoch_anchor_height_for_child,
};
use noid_chain::fri_state::StateRoot;
use noid_chain::hash_block_header;
use noid_core::Block128;
use noid_poseidon2b::primitives::Digest;

/// Canonical number of `Block128` lanes in [`ChainAccumulator`].
pub const CHAIN_ACCUMULATOR_LANES: usize = 10;

/// Direct recursive continuity state.
///
/// The tip lanes carry the nonce-free semantic header projection, so the
/// complete boundary is known at template-freeze time. The chain-link glue
/// `semantic tip == projection(parent header)` and
/// `child.prev_block_hash == H_BLOCKHDR(parent header)` is checked natively
/// at every acceptance for the tip and sealed in-circuit by the child step's
/// parent-seal replay for history.
///
/// The lane order is consensus-significant and is centralized in
/// [`ChainAccumulator::to_lanes`] and [`ChainAccumulator::from_lanes`]:
///
/// ```text
/// height
/// tip_semantic_id[2]
/// state_root[2]
/// log_slots
/// active_slot_count
/// alloc_counter
/// epoch_anchor_id[2]
/// ```
///
/// `epoch_anchor_id` is the block id consumed by the boundary block's own
/// transactions (`tx_epoch_anchor_height_for_child`); it is written from the
/// derived parent block id exactly when the parent height is a 144-boundary.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ChainAccumulator {
    pub height: u64,
    pub tip_semantic_id: Digest,
    pub state_root: StateRoot,
    pub log_slots: u32,
    pub active_slot_count: u64,
    pub alloc_counter: u64,
    pub epoch_anchor_id: Digest,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChainAccumulatorLaneError {
    HeightOutOfRange,
    LogSlotsOutOfRange,
    ActiveSlotCountOutOfRange,
    AllocCounterOutOfRange,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChainAccumulatorAdvanceError {
    HeightOverflow,
    BadHeight {
        expected: u64,
        actual: u64,
    },
    /// The supplied parent header's semantic projection does not match the
    /// accumulator tip.
    BadParentTip,
    /// The parent header's height does not match the accumulator height.
    BadParentHeight {
        expected: u64,
        actual: u64,
    },
    /// The child header does not chain-link to the supplied parent header.
    BadParentLink,
}

/// Mismatch between a recovered recursive boundary and the node's locally
/// selected canonical header chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChainAccumulatorLocalBoundaryError {
    Height,
    TipBlockId,
    StateRoot,
    LogSlots,
    ActiveSlotCount,
    AllocCounter,
    EpochAnchorHeight { expected: u64, actual: u64 },
    EpochAnchorId,
}

impl core::fmt::Display for ChainAccumulatorLocalBoundaryError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Height => write!(f, "accumulator height does not match local tip"),
            Self::TipBlockId => write!(f, "accumulator tip id does not match local tip header"),
            Self::StateRoot => write!(f, "accumulator state root does not match local tip"),
            Self::LogSlots => write!(f, "accumulator log_slots does not match local tip"),
            Self::ActiveSlotCount => {
                write!(f, "accumulator active count does not match local tip")
            }
            Self::AllocCounter => {
                write!(f, "accumulator allocation counter does not match local tip")
            }
            Self::EpochAnchorHeight { expected, actual } => write!(
                f,
                "local epoch-anchor header has height {actual}, expected {expected}"
            ),
            Self::EpochAnchorId => write!(
                f,
                "accumulator epoch anchor does not match the local canonical epoch header"
            ),
        }
    }
}

impl std::error::Error for ChainAccumulatorLocalBoundaryError {}

impl ChainAccumulator {
    /// Encode the canonical ten-lane recursive boundary.
    pub fn to_lanes(&self) -> [Block128; CHAIN_ACCUMULATOR_LANES] {
        let tip = digest_to_lanes(self.tip_semantic_id);
        let state = digest_to_lanes(self.state_root);
        let epoch = digest_to_lanes(self.epoch_anchor_id);
        [
            Block128::from(self.height),
            tip[0],
            tip[1],
            state[0],
            state[1],
            Block128::from(self.log_slots),
            Block128::from(self.active_slot_count),
            Block128::from(self.alloc_counter),
            epoch[0],
            epoch[1],
        ]
    }

    /// Decode the canonical ten-lane recursive boundary.
    ///
    /// Scalar lanes are range-checked before conversion. In particular, this
    /// API never truncates a field lane with `as u64`/`as u32`.
    pub fn from_lanes(
        lanes: [Block128; CHAIN_ACCUMULATOR_LANES],
    ) -> Result<Self, ChainAccumulatorLaneError> {
        Ok(Self {
            height: u64::try_from(lanes[0].to_u128())
                .map_err(|_| ChainAccumulatorLaneError::HeightOutOfRange)?,
            tip_semantic_id: digest_from_lanes([lanes[1], lanes[2]]),
            state_root: digest_from_lanes([lanes[3], lanes[4]]),
            log_slots: u32::try_from(lanes[5].to_u128())
                .map_err(|_| ChainAccumulatorLaneError::LogSlotsOutOfRange)?,
            active_slot_count: u64::try_from(lanes[6].to_u128())
                .map_err(|_| ChainAccumulatorLaneError::ActiveSlotCountOutOfRange)?,
            alloc_counter: u64::try_from(lanes[7].to_u128())
                .map_err(|_| ChainAccumulatorLaneError::AllocCounterOutOfRange)?,
            epoch_anchor_id: digest_from_lanes([lanes[8], lanes[9]]),
        })
    }

    /// Advance by one canonical child header, glued through the exact parent
    /// header — the same witness the child step's in-circuit parent-seal
    /// replays.
    ///
    /// The parent header must project to the current semantic tip at the
    /// current height; the child must chain-link to `H_BLOCKHDR(parent)` and
    /// increment height exactly. The child's semantic projection becomes the
    /// new tip; the transaction epoch switches to the derived parent block id
    /// exactly when the parent height is a 144-boundary (the anchor consumed
    /// by the child's own transactions).
    pub fn advance(
        &self,
        parent_header: &BlockHeader,
        child_header: &BlockHeader,
    ) -> Result<Self, ChainAccumulatorAdvanceError> {
        if parent_header.height != self.height {
            return Err(ChainAccumulatorAdvanceError::BadParentHeight {
                expected: self.height,
                actual: parent_header.height,
            });
        }
        if semantic_header_id(parent_header) != self.tip_semantic_id {
            return Err(ChainAccumulatorAdvanceError::BadParentTip);
        }
        let parent_block_id = hash_block_header(parent_header);
        if child_header.prev_block_hash != parent_block_id {
            return Err(ChainAccumulatorAdvanceError::BadParentLink);
        }
        let expected_height = self
            .height
            .checked_add(1)
            .ok_or(ChainAccumulatorAdvanceError::HeightOverflow)?;
        if child_header.height != expected_height {
            return Err(ChainAccumulatorAdvanceError::BadHeight {
                expected: expected_height,
                actual: child_header.height,
            });
        }
        Ok(Self {
            height: child_header.height,
            tip_semantic_id: semantic_header_id(child_header),
            state_root: child_header.state_root,
            log_slots: child_header.log_slots,
            active_slot_count: child_header.active_slot_count,
            alloc_counter: child_header.alloc_counter,
            epoch_anchor_id: if checked_tx_epoch_height_decomposition(self.height)
                .expect("every u64 height has a checked transaction-epoch decomposition")
                .is_boundary()
            {
                parent_block_id
            } else {
                self.epoch_anchor_id
            },
        })
    }

    /// Bind all ten recursive lanes to the locally selected canonical chain.
    ///
    /// `tip_header` and `epoch_anchor_header` must come from the node's native
    /// header store on the selected fork. The latter is the header at
    /// `tx_epoch_anchor_height_for_child(tip_height)` — the anchor the tip's
    /// own transactions bind. Recomputing the semantic projection and the
    /// anchor block id makes the direct boundary sufficient; no rolling
    /// header projection is needed.
    pub fn validate_local_header_boundary(
        &self,
        tip_header: &BlockHeader,
        epoch_anchor_header: &BlockHeader,
    ) -> Result<(), ChainAccumulatorLocalBoundaryError> {
        if self.height != tip_header.height {
            return Err(ChainAccumulatorLocalBoundaryError::Height);
        }
        if self.tip_semantic_id != semantic_header_id(tip_header) {
            return Err(ChainAccumulatorLocalBoundaryError::TipBlockId);
        }
        if self.state_root != tip_header.state_root {
            return Err(ChainAccumulatorLocalBoundaryError::StateRoot);
        }
        if self.log_slots != tip_header.log_slots {
            return Err(ChainAccumulatorLocalBoundaryError::LogSlots);
        }
        if self.active_slot_count != tip_header.active_slot_count {
            return Err(ChainAccumulatorLocalBoundaryError::ActiveSlotCount);
        }
        if self.alloc_counter != tip_header.alloc_counter {
            return Err(ChainAccumulatorLocalBoundaryError::AllocCounter);
        }
        let expected_epoch_height = tx_epoch_anchor_height_for_child(tip_header.height);
        if epoch_anchor_header.height != expected_epoch_height {
            return Err(ChainAccumulatorLocalBoundaryError::EpochAnchorHeight {
                expected: expected_epoch_height,
                actual: epoch_anchor_header.height,
            });
        }
        if self.epoch_anchor_id != hash_block_header(epoch_anchor_header) {
            return Err(ChainAccumulatorLocalBoundaryError::EpochAnchorId);
        }
        Ok(())
    }
}

/// Canonical blockless bootstrap boundary.
///
/// The tip carries the genesis semantic projection; the epoch anchor is the
/// genesis block id — the anchor every transaction in blocks 1..=144 binds.
pub fn genesis_accumulator() -> ChainAccumulator {
    let header = genesis_header();
    ChainAccumulator {
        height: header.height,
        tip_semantic_id: semantic_header_id(&header),
        state_root: header.state_root,
        log_slots: header.log_slots,
        active_slot_count: header.active_slot_count,
        alloc_counter: header.alloc_counter,
        epoch_anchor_id: hash_block_header(&header),
    }
}

fn digest_to_lanes(digest: Digest) -> [Block128; 2] {
    [
        Block128::from(u128::from_le_bytes(digest[..16].try_into().unwrap())),
        Block128::from(u128::from_le_bytes(digest[16..].try_into().unwrap())),
    ]
}

fn digest_from_lanes(lanes: [Block128; 2]) -> Digest {
    let mut digest = [0u8; 32];
    digest[..16].copy_from_slice(&lanes[0].to_u128().to_le_bytes());
    digest[16..].copy_from_slice(&lanes[1].to_u128().to_le_bytes());
    digest
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_chain::consensus::params::GENESIS_TARGET;
    use noid_poseidon2b::primitives::Address;

    fn child_of(parent_header: &BlockHeader, height: u64) -> BlockHeader {
        BlockHeader {
            prev_block_hash: hash_block_header(parent_header),
            state_root: [height as u8; 32],
            tx_root: [0x33; 32],
            timestamp: height,
            height,
            miner_address: Address([0x44; 32]),
            nonce: height as u128,
            difficulty_target: GENESIS_TARGET,
            log_slots: 24 + u32::from(height >= 145),
            active_slot_count: height * 2,
            alloc_counter: height * 3,
        }
    }

    #[test]
    fn genesis_is_the_canonical_header_boundary() {
        let header = genesis_header();
        assert_eq!(
            genesis_accumulator(),
            ChainAccumulator {
                height: 0,
                tip_semantic_id: semantic_header_id(&header),
                state_root: header.state_root,
                log_slots: header.log_slots,
                active_slot_count: 0,
                alloc_counter: 0,
                epoch_anchor_id: hash_block_header(&header),
            }
        );
    }

    #[test]
    fn lanes_roundtrip_without_truncation() {
        let accumulator = ChainAccumulator {
            height: u64::MAX,
            tip_semantic_id: [0x11; 32],
            state_root: [0x22; 32],
            log_slots: u32::MAX,
            active_slot_count: u64::MAX - 1,
            alloc_counter: u64::MAX - 2,
            epoch_anchor_id: [0x33; 32],
        };
        assert_eq!(
            ChainAccumulator::from_lanes(accumulator.to_lanes()),
            Ok(accumulator)
        );
    }

    #[test]
    fn lane_decoder_rejects_every_oversized_scalar() {
        let base = genesis_accumulator().to_lanes();
        for (lane, expected) in [
            (0, ChainAccumulatorLaneError::HeightOutOfRange),
            (5, ChainAccumulatorLaneError::LogSlotsOutOfRange),
            (6, ChainAccumulatorLaneError::ActiveSlotCountOutOfRange),
            (7, ChainAccumulatorLaneError::AllocCounterOutOfRange),
        ] {
            let mut lanes = base;
            lanes[lane] = if lane == 5 {
                Block128::from(u32::MAX as u128 + 1)
            } else {
                Block128::from(u64::MAX as u128 + 1)
            };
            assert_eq!(ChainAccumulator::from_lanes(lanes), Err(expected));
        }
    }

    #[test]
    fn advance_checks_parent_glue_link_and_exact_height() {
        let start = genesis_accumulator();
        let genesis = genesis_header();
        let valid = child_of(&genesis, 1);
        let end = start.advance(&genesis, &valid).unwrap();
        assert_eq!(end.height, 1);
        assert_eq!(end.tip_semantic_id, semantic_header_id(&valid));
        assert_eq!(end.state_root, valid.state_root);
        assert_eq!(end.log_slots, valid.log_slots);
        assert_eq!(end.active_slot_count, valid.active_slot_count);
        assert_eq!(end.alloc_counter, valid.alloc_counter);
        // Genesis (height 0) is a boundary parent: the epoch anchor is the
        // derived genesis block id — idempotent with the bootstrap value.
        assert_eq!(end.epoch_anchor_id, start.epoch_anchor_id);

        // A different nonce on the same parent template keeps the semantic
        // glue but breaks the chain link.
        let mut renonced_parent = genesis;
        renonced_parent.nonce = renonced_parent.nonce.wrapping_add(1);
        assert_eq!(
            start.advance(&renonced_parent, &valid),
            Err(ChainAccumulatorAdvanceError::BadParentLink)
        );

        let mut wrong_parent = genesis;
        wrong_parent.state_root = [0x99; 32];
        assert_eq!(
            start.advance(&wrong_parent, &valid),
            Err(ChainAccumulatorAdvanceError::BadParentTip)
        );

        let mut unlinked = valid;
        unlinked.prev_block_hash = [0x99; 32];
        assert_eq!(
            start.advance(&genesis, &unlinked),
            Err(ChainAccumulatorAdvanceError::BadParentLink)
        );

        let bad_height = child_of(&genesis, 2);
        assert_eq!(
            start.advance(&genesis, &bad_height),
            Err(ChainAccumulatorAdvanceError::BadHeight {
                expected: 1,
                actual: 2,
            })
        );

        assert_eq!(
            start.advance(&valid, &child_of(&valid, 2)),
            Err(ChainAccumulatorAdvanceError::BadParentHeight {
                expected: 0,
                actual: 1,
            })
        );
    }

    #[test]
    fn epoch_switches_to_the_derived_parent_id_after_the_boundary() {
        let mut accumulator = genesis_accumulator();
        let genesis_epoch = accumulator.epoch_anchor_id;
        let mut parent = genesis_header();
        let mut boundary_id = None;
        for height in 1..=146 {
            let header = child_of(&parent, height);
            accumulator = accumulator.advance(&parent, &header).unwrap();
            match height {
                // The boundary block 144 itself still consumes the previous
                // anchor; its own id becomes the anchor for 145..=288.
                1..=144 => assert_eq!(accumulator.epoch_anchor_id, genesis_epoch),
                145 => {
                    boundary_id = Some(hash_block_header(&parent));
                    assert_eq!(accumulator.epoch_anchor_id, boundary_id.unwrap());
                }
                146 => assert_eq!(accumulator.epoch_anchor_id, boundary_id.unwrap()),
                _ => unreachable!(),
            }
            parent = header;
        }
    }

    #[test]
    fn local_header_boundary_covers_epoch_edges_and_every_lane() {
        let genesis = genesis_header();
        let mut headers = vec![genesis];
        let mut accumulator = genesis_accumulator();
        let mut edge_boundaries = Vec::new();
        for height in 1..=145 {
            let parent = headers[height as usize - 1];
            let header = child_of(&parent, height);
            accumulator = accumulator.advance(&parent, &header).unwrap();
            headers.push(header);
            if matches!(height, 143..=145) {
                edge_boundaries.push(accumulator.clone());
            }
        }

        // The anchor a tip's own transactions bind: 143 -> 0, 144 -> 0
        // (boundary block still consumes the old anchor), 145 -> 144.
        for (boundary, epoch_height) in edge_boundaries.iter().zip([0usize, 0, 144]) {
            boundary
                .validate_local_header_boundary(
                    &headers[boundary.height as usize],
                    &headers[epoch_height],
                )
                .unwrap();
        }

        let honest = &edge_boundaries[2];
        let tip = &headers[145];
        let epoch = &headers[144];
        for lane in 0..CHAIN_ACCUMULATOR_LANES {
            let mut lanes = honest.to_lanes();
            lanes[lane] = Block128::from(lanes[lane].to_u128() ^ 1);
            let bad = ChainAccumulator::from_lanes(lanes).unwrap();
            assert!(
                bad.validate_local_header_boundary(tip, epoch).is_err(),
                "mutated accumulator lane {lane} accepted"
            );
        }

        // Semantic-field mutation is rejected; a renonced tip keeps its
        // semantic projection and is deliberately accepted — the chain link
        // and PoW over the exact nonce remain native header authority.
        let mut competing_tip = *tip;
        competing_tip.state_root = [0x77; 32];
        assert_eq!(
            honest.validate_local_header_boundary(&competing_tip, epoch),
            Err(ChainAccumulatorLocalBoundaryError::TipBlockId)
        );
        let mut renonced_tip = *tip;
        renonced_tip.nonce = renonced_tip.nonce.wrapping_add(1);
        assert_eq!(
            honest.validate_local_header_boundary(&renonced_tip, epoch),
            Ok(())
        );

        assert_eq!(
            honest.validate_local_header_boundary(tip, &headers[143]),
            Err(ChainAccumulatorLocalBoundaryError::EpochAnchorHeight {
                expected: 144,
                actual: 143,
            })
        );
        let mut competing_epoch = *epoch;
        competing_epoch.nonce = competing_epoch.nonce.wrapping_add(1);
        assert_eq!(
            honest.validate_local_header_boundary(tip, &competing_epoch),
            Err(ChainAccumulatorLocalBoundaryError::EpochAnchorId)
        );
    }
}
