// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical byte serialization for MDBX-persisted chain data.
//!
//! All formats are little-endian, fixed-width where possible.
//! These are NOT network formats — they are storage-internal and may evolve
//! across software versions (the MDBX file is not portable between major versions).

use noid_core::field::{CanonicalDeserialize, CanonicalSerialize, TowerField};
use noid_core::Block128;

use crate::block_header::BlockHeader;
use crate::consensus::da_prune::BlockUndoLog;
use crate::consensus::params::{BLOCK_MAX_ACTIONS, BLOCK_MAX_TXS};
use crate::fri_state::SlotValue;
use crate::header_anchor::HeaderChainAnchor;
use crate::segmented_state::SegmentColumns;
use crate::storage::meta::{ConsensusMeta, FinalizedCheckpoint};
use crate::wire::BLOCK_HEADER_WIRE_SIZE;
use noid_poseidon2b::primitives::TxBodyHash;

// ---------------------------------------------------------------------------
// u64 / u32 key helpers
// ---------------------------------------------------------------------------

pub fn u64_key(v: u64) -> [u8; 8] {
    v.to_le_bytes()
}

pub fn u64_from_key(b: &[u8]) -> Option<u64> {
    b.get(..8)?.try_into().ok().map(u64::from_le_bytes)
}

pub fn u32_key(v: u32) -> [u8; 4] {
    v.to_le_bytes()
}

// ---------------------------------------------------------------------------
// BlockHeader
// ---------------------------------------------------------------------------

/// Serialize a `BlockHeader` to exactly `BLOCK_HEADER_WIRE_SIZE` bytes.
pub fn encode_header(h: &BlockHeader) -> Vec<u8> {
    let mut buf = Vec::with_capacity(BLOCK_HEADER_WIRE_SIZE);
    h.encode(&mut buf);
    debug_assert_eq!(buf.len(), BLOCK_HEADER_WIRE_SIZE);
    buf
}

/// Deserialize a `BlockHeader` from bytes.
pub fn decode_header(bytes: &[u8]) -> Option<BlockHeader> {
    BlockHeader::from_bytes(bytes).ok()
}

// ---------------------------------------------------------------------------
// HeaderChainAnchor
// ---------------------------------------------------------------------------

pub const ENCODED_HEADER_CHAIN_ANCHOR_BYTES: usize = 188;

pub fn encode_header_chain_anchor(
    anchor: &HeaderChainAnchor,
) -> [u8; ENCODED_HEADER_CHAIN_ANCHOR_BYTES] {
    let mut out = [0u8; ENCODED_HEADER_CHAIN_ANCHOR_BYTES];
    let mut pos = 0usize;
    out[pos..pos + 8].copy_from_slice(&anchor.height.to_le_bytes());
    pos += 8;
    out[pos..pos + 32].copy_from_slice(&anchor.block_id);
    pos += 32;
    out[pos..pos + 32].copy_from_slice(&anchor.state_root);
    pos += 32;
    out[pos..pos + 32].copy_from_slice(&anchor.tx_root);
    pos += 32;
    out[pos..pos + 32].copy_from_slice(anchor.miner_address.as_bytes());
    pos += 32;
    out[pos..pos + 4].copy_from_slice(&anchor.log_slots.to_le_bytes());
    pos += 4;
    out[pos..pos + 8].copy_from_slice(&anchor.active_slot_count.to_le_bytes());
    pos += 8;
    out[pos..pos + 8].copy_from_slice(&anchor.alloc_counter.to_le_bytes());
    pos += 8;
    out[pos..pos + 32].copy_from_slice(&anchor.cumulative_chainwork);
    pos += 32;
    debug_assert_eq!(pos, ENCODED_HEADER_CHAIN_ANCHOR_BYTES);
    out
}

pub fn decode_header_chain_anchor(bytes: &[u8]) -> Option<HeaderChainAnchor> {
    if bytes.len() != ENCODED_HEADER_CHAIN_ANCHOR_BYTES {
        return None;
    }
    let mut pos = 0usize;
    let height = u64::from_le_bytes(bytes[pos..pos + 8].try_into().ok()?);
    pos += 8;
    let block_id = bytes[pos..pos + 32].try_into().ok()?;
    pos += 32;
    let state_root = bytes[pos..pos + 32].try_into().ok()?;
    pos += 32;
    let tx_root = bytes[pos..pos + 32].try_into().ok()?;
    pos += 32;
    let miner_address = noid_poseidon2b::primitives::Address(bytes[pos..pos + 32].try_into().ok()?);
    pos += 32;
    let log_slots = u32::from_le_bytes(bytes[pos..pos + 4].try_into().ok()?);
    pos += 4;
    let active_slot_count = u64::from_le_bytes(bytes[pos..pos + 8].try_into().ok()?);
    pos += 8;
    let alloc_counter = u64::from_le_bytes(bytes[pos..pos + 8].try_into().ok()?);
    pos += 8;
    let cumulative_chainwork = bytes[pos..pos + 32].try_into().ok()?;
    pos += 32;
    debug_assert_eq!(pos, ENCODED_HEADER_CHAIN_ANCHOR_BYTES);
    Some(HeaderChainAnchor {
        height,
        block_id,
        state_root,
        tx_root,
        miner_address,
        log_slots,
        active_slot_count,
        alloc_counter,
        cumulative_chainwork,
    })
}

// ---------------------------------------------------------------------------
// Block128
// ---------------------------------------------------------------------------

fn encode_b128(b: &Block128) -> [u8; 16] {
    let v = b.to_bytes();
    debug_assert_eq!(v.len(), 16);
    v.try_into().unwrap_or([0u8; 16])
}

fn decode_b128(bytes: &[u8; 16]) -> Block128 {
    Block128::deserialize(bytes).unwrap_or(Block128::ZERO)
}

// ---------------------------------------------------------------------------
// SlotValue  (48 bytes)
// ---------------------------------------------------------------------------

pub fn encode_slot_value(sv: &SlotValue) -> [u8; 48] {
    let mut out = [0u8; 48];
    out[0..16].copy_from_slice(&encode_b128(&sv.value));
    out[16..32].copy_from_slice(&encode_b128(&sv.owner_hi));
    out[32..48].copy_from_slice(&encode_b128(&sv.owner_lo));
    out
}

pub fn decode_slot_value(bytes: &[u8]) -> Option<SlotValue> {
    if bytes.len() < 48 {
        return None;
    }
    Some(SlotValue {
        value: decode_b128(bytes[0..16].try_into().ok()?),
        owner_hi: decode_b128(bytes[16..32].try_into().ok()?),
        owner_lo: decode_b128(bytes[32..48].try_into().ok()?),
    })
}

// ---------------------------------------------------------------------------
// BlockUndoLog
// ---------------------------------------------------------------------------
//
// Wire format:
//   block_height             : u64 LE  (8 bytes)
//   log_slots_before          : u32 LE  (4 bytes)
//   active_slot_count_before : u64 LE  (8 bytes)
//   alloc_counter_before     : u64 LE  (8 bytes)
//   n_changes                : u32 LE  (4 bytes)
//   n_hashes                 : u32 LE  (4 bytes)
//   [slot_index  : u32 LE  (4 bytes)
//    slot_value  : 48 bytes          ] × n_changes
//   tx_hash      : 32 bytes × n_hashes

pub fn encode_undo_log(u: &BlockUndoLog) -> Vec<u8> {
    let mut buf = Vec::with_capacity(36 + u.slot_changes.len() * 52 + u.tx_hashes.len() * 32);
    buf.extend_from_slice(&u.block_height.to_le_bytes());
    buf.extend_from_slice(&u.log_slots_before.to_le_bytes());
    buf.extend_from_slice(&u.active_slot_count_before.to_le_bytes());
    buf.extend_from_slice(&u.alloc_counter_before.to_le_bytes());
    buf.extend_from_slice(&(u.slot_changes.len() as u32).to_le_bytes());
    buf.extend_from_slice(&(u.tx_hashes.len() as u32).to_le_bytes());
    for (idx, sv) in &u.slot_changes {
        buf.extend_from_slice(&idx.to_le_bytes());
        buf.extend_from_slice(&encode_slot_value(sv));
    }
    for h in &u.tx_hashes {
        buf.extend_from_slice(&h.0);
    }
    buf
}

pub fn decode_undo_log(bytes: &[u8]) -> Option<BlockUndoLog> {
    if bytes.len() < 36 {
        return None;
    }
    let block_height = u64::from_le_bytes(bytes[0..8].try_into().ok()?);
    let log_slots_before = u32::from_le_bytes(bytes[8..12].try_into().ok()?);
    let active_slot_count_before = u64::from_le_bytes(bytes[12..20].try_into().ok()?);
    let alloc_counter_before = u64::from_le_bytes(bytes[20..28].try_into().ok()?);
    let n = u32::from_le_bytes(bytes[28..32].try_into().ok()?) as usize;
    let n_hashes = u32::from_le_bytes(bytes[32..36].try_into().ok()?) as usize;
    // These lengths originate in a consensus-bounded block.  Reject corrupt
    // storage before either the size arithmetic or the Vec reservations so a
    // malformed MDBX value cannot turn restart/reorg into an allocation DoS.
    if n > BLOCK_MAX_ACTIONS || n_hashes > BLOCK_MAX_TXS {
        return None;
    }
    let payload_min = 36usize
        .checked_add(n.checked_mul(52)?)?
        .checked_add(n_hashes.checked_mul(32)?)?;
    if bytes.len() != payload_min {
        return None;
    }
    let mut slot_changes = Vec::with_capacity(n);
    let mut pos = 36;
    for _ in 0..n {
        if bytes.len() < pos + 52 {
            return None;
        }
        let idx = u32::from_le_bytes(bytes[pos..pos + 4].try_into().ok()?);
        let sv = decode_slot_value(&bytes[pos + 4..pos + 52])?;
        slot_changes.push((idx, sv));
        pos += 52;
    }
    let mut tx_hashes = Vec::with_capacity(n_hashes);
    for _ in 0..n_hashes {
        if bytes.len() < pos + 32 {
            return None;
        }
        let h: [u8; 32] = bytes[pos..pos + 32].try_into().ok()?;
        tx_hashes.push(TxBodyHash(h));
        pos += 32;
    }
    debug_assert_eq!(pos, bytes.len());
    Some(BlockUndoLog {
        block_height,
        log_slots_before,
        active_slot_count_before,
        alloc_counter_before,
        slot_changes,
        tx_hashes,
    })
}

// ---------------------------------------------------------------------------
// SegmentColumns
// ---------------------------------------------------------------------------
//
// Sparse V1 format:
//   magic             : "SGS1"       (4 bytes)
//   effective_log_seg : u8            (1 byte)
//   live_count        : u32 LE        (4 bytes)
//   [local_index      : u16 LE        (2 bytes)
//    slot_value       : 3 × 16 bytes (48 bytes)] × live_count
//
// Entries are strictly increasing and never encode an empty slot. A segment
// with one live UTXO is therefore 59 bytes instead of 3 MiB. Even a completely
// full 2^16-slot segment stays below 3.13 MiB, only ~4% above raw columns.

pub const SEGMENT_ENCODING_MAGIC: [u8; 4] = *b"SGS1";
pub const ENCODED_SEGMENT_HEADER_BYTES: usize = 9;
pub const ENCODED_SEGMENT_INDEX_BYTES: usize = 2;
pub const SEGMENT_LANE_COUNT: usize = 3;
pub const SEGMENT_FIELD_BYTES: usize = 16;
pub const ENCODED_SEGMENT_SLOT_VALUE_BYTES: usize = SEGMENT_LANE_COUNT * SEGMENT_FIELD_BYTES;
pub const ENCODED_SEGMENT_ENTRY_BYTES: usize =
    ENCODED_SEGMENT_INDEX_BYTES + ENCODED_SEGMENT_SLOT_VALUE_BYTES;

/// One borrowed canonical sparse segment payload.
///
/// Construction validates the complete frame once. Iteration then decodes
/// only live entries and never allocates the dense `2^16` column image.
#[derive(Clone, Copy, Debug)]
pub struct SparseSegmentView<'a> {
    effective_log_seg: u8,
    live_count: u32,
    entries: &'a [u8],
}

impl<'a> SparseSegmentView<'a> {
    #[inline]
    pub fn effective_log_segment(self) -> u8 {
        self.effective_log_seg
    }

    #[inline]
    pub fn live_count(self) -> u32 {
        self.live_count
    }

    #[inline]
    pub fn entries(self) -> impl ExactSizeIterator<Item = (u16, SlotValue)> + 'a {
        self.entries
            .chunks_exact(ENCODED_SEGMENT_ENTRY_BYTES)
            .map(|entry| {
                let local_index =
                    u16::from_le_bytes(entry[..2].try_into().expect("validated sparse index"));
                let slot = decode_slot_value(&entry[2..]).expect("validated sparse slot");
                (local_index, slot)
            })
    }
}

#[inline]
pub fn encoded_segment_len_for_live_count(effective_log_seg: u8, live_count: u32) -> Option<usize> {
    if effective_log_seg > 16 || effective_log_seg as u32 >= usize::BITS {
        return None;
    }
    let capacity = 1usize.checked_shl(effective_log_seg as u32)?;
    let live_count = usize::try_from(live_count).ok()?;
    if live_count > capacity {
        return None;
    }
    ENCODED_SEGMENT_HEADER_BYTES.checked_add(live_count.checked_mul(ENCODED_SEGMENT_ENTRY_BYTES)?)
}

/// Recover the live-entry count from a canonical sparse segment length.
///
/// This validates only the public framing geometry. `decode_segment` also
/// validates the embedded count, entry ordering and non-empty slot values.
#[inline]
pub fn encoded_segment_live_count_from_len(
    effective_log_seg: u8,
    encoded_len: usize,
) -> Option<u32> {
    let payload_len = encoded_len.checked_sub(ENCODED_SEGMENT_HEADER_BYTES)?;
    if payload_len % ENCODED_SEGMENT_ENTRY_BYTES != 0 {
        return None;
    }
    let live_count = u32::try_from(payload_len / ENCODED_SEGMENT_ENTRY_BYTES).ok()?;
    (encoded_segment_len_for_live_count(effective_log_seg, live_count)? == encoded_len)
        .then_some(live_count)
}

#[inline]
pub fn max_encoded_segment_len_for_eff_log(effective_log_seg: u8) -> Option<usize> {
    let capacity = 1usize.checked_shl(effective_log_seg as u32)?;
    encoded_segment_len_for_live_count(effective_log_seg, u32::try_from(capacity).ok()?)
}

#[inline]
pub fn max_encoded_segments_total_len(
    segment_count: usize,
    effective_log_seg: u8,
) -> Option<usize> {
    segment_count.checked_mul(max_encoded_segment_len_for_eff_log(effective_log_seg)?)
}

/// Validate and borrow one canonical sparse segment without expanding it.
pub fn decode_sparse_segment(bytes: &[u8]) -> Option<SparseSegmentView<'_>> {
    if bytes.len() < ENCODED_SEGMENT_HEADER_BYTES || bytes[..4] != SEGMENT_ENCODING_MAGIC {
        return None;
    }
    let effective_log_seg = bytes[4];
    if effective_log_seg > 16 || effective_log_seg as u32 >= usize::BITS {
        return None;
    }
    let live_count = u32::from_le_bytes(bytes[5..9].try_into().ok()?);
    let expected_len = encoded_segment_len_for_live_count(effective_log_seg, live_count)?;
    if bytes.len() != expected_len {
        return None;
    }
    let capacity = 1usize << effective_log_seg;
    let entries = &bytes[ENCODED_SEGMENT_HEADER_BYTES..];
    let mut previous = None;
    for entry in entries.chunks_exact(ENCODED_SEGMENT_ENTRY_BYTES) {
        let local_index = u16::from_le_bytes(entry[..2].try_into().ok()?);
        if usize::from(local_index) >= capacity
            || previous.is_some_and(|previous| local_index <= previous)
        {
            return None;
        }
        let slot = decode_slot_value(&entry[2..])?;
        if slot.is_empty() {
            return None;
        }
        previous = Some(local_index);
    }
    Some(SparseSegmentView {
        effective_log_seg,
        live_count,
        entries,
    })
}

/// Encode an already-sparse, strictly ordered live-entry sequence.
pub fn encode_sparse_segment_entries(
    effective_log_seg: u8,
    entries: &[(u16, SlotValue)],
) -> Option<Vec<u8>> {
    let live_count = u32::try_from(entries.len()).ok()?;
    let encoded_len = encoded_segment_len_for_live_count(effective_log_seg, live_count)?;
    let capacity = 1usize.checked_shl(u32::from(effective_log_seg))?;
    let mut previous = None;
    let mut encoded = Vec::with_capacity(encoded_len);
    encoded.extend_from_slice(&SEGMENT_ENCODING_MAGIC);
    encoded.push(effective_log_seg);
    encoded.extend_from_slice(&live_count.to_le_bytes());
    for &(local_index, slot) in entries {
        if slot.is_empty()
            || usize::from(local_index) >= capacity
            || previous.is_some_and(|previous| local_index <= previous)
        {
            return None;
        }
        encoded.extend_from_slice(&local_index.to_le_bytes());
        encoded.extend_from_slice(&encode_slot_value(&slot));
        previous = Some(local_index);
    }
    debug_assert_eq!(encoded.len(), encoded_len);
    Some(encoded)
}

pub fn encode_segment(seg: &SegmentColumns, effective_log_seg: u8) -> Vec<u8> {
    let n = seg.values.len();
    debug_assert_eq!(n, seg.owners_hi.len());
    debug_assert_eq!(n, seg.owners_lo.len());
    debug_assert_eq!(n, 1usize << effective_log_seg);
    let live_count = (0..n)
        .filter(|&index| {
            !(SlotValue {
                value: seg.values[index],
                owner_hi: seg.owners_hi[index],
                owner_lo: seg.owners_lo[index],
            })
            .is_empty()
        })
        .count();
    let live_count = u32::try_from(live_count).expect("segment live count fits u32");
    let mut buf = Vec::with_capacity(
        encoded_segment_len_for_live_count(effective_log_seg, live_count).unwrap_or(0),
    );
    buf.extend_from_slice(&SEGMENT_ENCODING_MAGIC);
    buf.push(effective_log_seg);
    buf.extend_from_slice(&live_count.to_le_bytes());
    for index in 0..n {
        let slot = SlotValue {
            value: seg.values[index],
            owner_hi: seg.owners_hi[index],
            owner_lo: seg.owners_lo[index],
        };
        if slot.is_empty() {
            continue;
        }
        buf.extend_from_slice(&(index as u16).to_le_bytes());
        buf.extend_from_slice(&encode_slot_value(&slot));
    }
    debug_assert_eq!(
        buf.len(),
        encoded_segment_len_for_live_count(effective_log_seg, live_count).unwrap_or(0)
    );
    buf
}

/// Returns `(effective_log_seg, SegmentColumns)`.
pub fn decode_segment(bytes: &[u8]) -> Option<(u8, SegmentColumns)> {
    let sparse = decode_sparse_segment(bytes)?;
    let effective_log_seg = sparse.effective_log_segment();
    let capacity = 1usize << effective_log_seg;
    let mut columns = SegmentColumns::new_zero(capacity);
    for (local_index, slot) in sparse.entries() {
        let local = usize::from(local_index);
        columns.values[local] = slot.value;
        columns.owners_hi[local] = slot.owner_hi;
        columns.owners_lo[local] = slot.owner_lo;
    }
    Some((effective_log_seg, columns))
}

// ---------------------------------------------------------------------------
// TxIndex  (height + position within block)
// ---------------------------------------------------------------------------
//
// Value format:
//   height  : u64 LE  (8 bytes)
//   tx_pos  : u32 LE  (4 bytes)

pub fn encode_tx_index_value(height: u64, tx_pos: u32) -> [u8; 12] {
    let mut out = [0u8; 12];
    out[0..8].copy_from_slice(&height.to_le_bytes());
    out[8..12].copy_from_slice(&tx_pos.to_le_bytes());
    out
}

pub fn decode_tx_index_value(bytes: &[u8]) -> Option<(u64, u32)> {
    if bytes.len() < 12 {
        return None;
    }
    let height = u64::from_le_bytes(bytes[0..8].try_into().ok()?);
    let pos = u32::from_le_bytes(bytes[8..12].try_into().ok()?);
    Some((height, pos))
}

// ---------------------------------------------------------------------------
// Chain meta (tip + state counters)
// ---------------------------------------------------------------------------
//
// chain_tip value: height(u64) + hash([u8;32]) = 40 bytes

pub fn encode_chain_tip(height: u64, hash: &[u8; 32]) -> [u8; 40] {
    let mut out = [0u8; 40];
    out[0..8].copy_from_slice(&height.to_le_bytes());
    out[8..40].copy_from_slice(hash);
    out
}

pub fn decode_chain_tip(bytes: &[u8]) -> Option<(u64, [u8; 32])> {
    if bytes.len() < 40 {
        return None;
    }
    let height = u64::from_le_bytes(bytes[0..8].try_into().ok()?);
    let hash: [u8; 32] = bytes[8..40].try_into().ok()?;
    Some((height, hash))
}

// state_meta v1:
//   log_slots(u32) + active_slot_count(u64) + alloc_counter(u64) = 20 bytes
// state_meta v2 appends:
//   circulating_supply_micronoid(u128) = 16 bytes
//
// The first 20 bytes remain unchanged so pre-v2 databases can be upgraded by
// one dense verification pass instead of being discarded.
pub const ENCODED_STATE_META_V1_BYTES: usize = 20;
pub const ENCODED_STATE_META_BYTES: usize = 36;

pub fn encode_state_meta(
    log_slots: u32,
    active: u64,
    alloc: u64,
    circulating_supply_micronoid: u128,
) -> [u8; ENCODED_STATE_META_BYTES] {
    let mut out = [0u8; ENCODED_STATE_META_BYTES];
    out[0..4].copy_from_slice(&log_slots.to_le_bytes());
    out[4..12].copy_from_slice(&active.to_le_bytes());
    out[12..20].copy_from_slice(&alloc.to_le_bytes());
    out[20..36].copy_from_slice(&circulating_supply_micronoid.to_le_bytes());
    out
}

pub fn decode_state_meta(bytes: &[u8]) -> Option<(u32, u64, u64)> {
    if bytes.len() < ENCODED_STATE_META_V1_BYTES {
        return None;
    }
    let log_slots = u32::from_le_bytes(bytes[0..4].try_into().ok()?);
    let active = u64::from_le_bytes(bytes[4..12].try_into().ok()?);
    let alloc = u64::from_le_bytes(bytes[12..20].try_into().ok()?);
    Some((log_slots, active, alloc))
}

pub fn decode_circulating_supply(bytes: &[u8]) -> Option<u128> {
    if bytes.len() < ENCODED_STATE_META_BYTES {
        return None;
    }
    Some(u128::from_le_bytes(bytes[20..36].try_into().ok()?))
}

// Compact restart accelerator for one non-empty durable segment:
// live_count(u32) + exact sparse-Merkle segment root([u8; 32]) = 36 bytes.
//
// The exact roots are collectively authenticated by the canonical tip's
// state_root. Raw columns remain authoritative and are checked against this
// summary when the segment is first faulted into RAM.
pub const ENCODED_SEGMENT_SUMMARY_BYTES: usize = 36;

pub fn encode_segment_summary(
    live_count: u32,
    exact_root: &[u8; 32],
) -> [u8; ENCODED_SEGMENT_SUMMARY_BYTES] {
    let mut out = [0u8; ENCODED_SEGMENT_SUMMARY_BYTES];
    out[0..4].copy_from_slice(&live_count.to_le_bytes());
    out[4..36].copy_from_slice(exact_root);
    out
}

pub fn decode_segment_summary(bytes: &[u8]) -> Option<(u32, [u8; 32])> {
    if bytes.len() != ENCODED_SEGMENT_SUMMARY_BYTES {
        return None;
    }
    let live_count = u32::from_le_bytes(bytes[0..4].try_into().ok()?);
    let exact_root = bytes[4..36].try_into().ok()?;
    Some((live_count, exact_root))
}

// consensus_meta value:
//   tip_height(u64) + tip_hash([u8;32]) + cumulative_chainwork([u8;32])
//   + finalized_height(u64) + finalized_hash([u8;32]) = 112 bytes
pub const ENCODED_CONSENSUS_META_BYTES: usize = 112;

pub fn encode_consensus_meta(meta: &ConsensusMeta) -> [u8; ENCODED_CONSENSUS_META_BYTES] {
    let mut out = [0u8; ENCODED_CONSENSUS_META_BYTES];
    out[0..8].copy_from_slice(&meta.tip_height.to_le_bytes());
    out[8..40].copy_from_slice(&meta.tip_hash);
    out[40..72].copy_from_slice(&meta.cumulative_chainwork);
    out[72..80].copy_from_slice(&meta.finalized.height.to_le_bytes());
    out[80..112].copy_from_slice(&meta.finalized.hash);
    out
}

pub fn decode_consensus_meta(bytes: &[u8]) -> Option<ConsensusMeta> {
    if bytes.len() != ENCODED_CONSENSUS_META_BYTES {
        return None;
    }
    let tip_height = u64::from_le_bytes(bytes[0..8].try_into().ok()?);
    let tip_hash: [u8; 32] = bytes[8..40].try_into().ok()?;
    let cumulative_chainwork: [u8; 32] = bytes[40..72].try_into().ok()?;
    let finalized_height = u64::from_le_bytes(bytes[72..80].try_into().ok()?);
    let finalized_hash: [u8; 32] = bytes[80..112].try_into().ok()?;
    Some(ConsensusMeta {
        tip_height,
        tip_hash,
        cumulative_chainwork,
        finalized: FinalizedCheckpoint {
            height: finalized_height,
            hash: finalized_hash,
        },
    })
}

pub fn encode_chain_work(work: &[u8; 32]) -> [u8; 32] {
    *work
}

pub fn decode_chain_work(bytes: &[u8]) -> Option<[u8; 32]> {
    bytes.try_into().ok()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use noid_core::Block128;
    use noid_core::TowerField;

    #[test]
    fn u64_key_roundtrip() {
        let v = 12345678u64;
        assert_eq!(u64_from_key(&u64_key(v)), Some(v));
        assert_eq!(u64_from_key(&[]), None);
    }

    #[test]
    fn header_roundtrip() {
        use crate::block_header::BlockHeader;
        use noid_poseidon2b::primitives::Address;
        let h = BlockHeader {
            prev_block_hash: [1u8; 32],
            state_root: [2u8; 32],
            tx_root: [3u8; 32],
            timestamp: 9999,
            height: 42,
            miner_address: Address([4u8; 32]),
            nonce: 12345u128,
            difficulty_target: [5u8; 32],
            log_slots: 24,
            active_slot_count: 100,
            alloc_counter: 200,
        };
        let bytes = encode_header(&h);
        assert_eq!(bytes.len(), BLOCK_HEADER_WIRE_SIZE);
        let h2 = decode_header(&bytes).expect("decode");
        assert_eq!(h, h2);
    }

    #[test]
    fn header_chain_anchor_roundtrip_uses_only_direct_tip_fields() {
        let anchor = HeaderChainAnchor {
            height: 42,
            block_id: [1u8; 32],
            state_root: [2u8; 32],
            tx_root: [3u8; 32],
            miner_address: noid_poseidon2b::primitives::Address([4u8; 32]),
            log_slots: 24,
            active_slot_count: 100,
            alloc_counter: 200,
            cumulative_chainwork: [5u8; 32],
        };
        let bytes = encode_header_chain_anchor(&anchor);
        assert_eq!(bytes.len(), 188);
        assert_eq!(decode_header_chain_anchor(&bytes), Some(anchor));

        let mut obsolete_rolling_layout = bytes.to_vec();
        obsolete_rolling_layout.extend_from_slice(&[0xAA; 32]);
        assert_eq!(obsolete_rolling_layout.len(), 220);
        assert_eq!(decode_header_chain_anchor(&obsolete_rolling_layout), None);
    }

    #[test]
    fn slot_value_roundtrip() {
        let sv = SlotValue {
            value: Block128::from(12345u128),
            owner_hi: Block128::from(0xABCDEFu128),
            owner_lo: Block128::from(0x123456u128),
        };
        let bytes = encode_slot_value(&sv);
        let sv2 = decode_slot_value(&bytes).expect("decode");
        assert_eq!(sv.value, sv2.value);
        assert_eq!(sv.owner_hi, sv2.owner_hi);
        assert_eq!(sv.owner_lo, sv2.owner_lo);
    }

    #[test]
    fn undo_log_roundtrip() {
        use noid_poseidon2b::primitives::TxBodyHash;
        let sv = SlotValue {
            value: Block128::from(1u128),
            owner_hi: Block128::ZERO,
            owner_lo: Block128::ZERO,
        };
        let undo = BlockUndoLog {
            block_height: 7,
            log_slots_before: 24,
            active_slot_count_before: 19,
            alloc_counter_before: 41,
            slot_changes: vec![(3u32, sv), (9u32, SlotValue::EMPTY)],
            tx_hashes: vec![TxBodyHash([0xABu8; 32])],
        };
        let bytes = encode_undo_log(&undo);
        let undo2 = decode_undo_log(&bytes).expect("decode");
        assert_eq!(undo2, undo);
    }

    #[test]
    fn undo_log_empty_roundtrip() {
        let undo = BlockUndoLog::empty(42, 24);
        let bytes = encode_undo_log(&undo);
        let undo2 = decode_undo_log(&bytes).expect("decode");
        assert_eq!(undo2.block_height, 42);
        assert_eq!(undo2.active_slot_count_before, 0);
        assert_eq!(undo2.alloc_counter_before, 0);
        assert!(undo2.slot_changes.is_empty());
        assert!(undo2.tx_hashes.is_empty());
    }

    #[test]
    fn undo_log_rejects_truncated_counter_header_and_impossible_lengths() {
        let undo = BlockUndoLog::empty(42, 24);
        let bytes = encode_undo_log(&undo);
        assert!(decode_undo_log(&bytes[..23]).is_none());

        let mut malformed = bytes;
        malformed[28..32].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(decode_undo_log(&malformed).is_none());

        let mut too_many_hashes = encode_undo_log(&BlockUndoLog::empty(42, 24));
        too_many_hashes[32..36].copy_from_slice(&((BLOCK_MAX_TXS as u32) + 1).to_le_bytes());
        assert!(decode_undo_log(&too_many_hashes).is_none());
    }

    #[test]
    fn chain_tip_roundtrip() {
        let hash = [0xABu8; 32];
        let bytes = encode_chain_tip(999, &hash);
        let (h, hh) = decode_chain_tip(&bytes).expect("decode");
        assert_eq!(h, 999);
        assert_eq!(hh, hash);
    }

    #[test]
    fn state_meta_roundtrip() {
        let supply = 123_456_789_012_345u128;
        let bytes = encode_state_meta(25, 1234567, 999999, supply);
        let (ls, active, alloc) = decode_state_meta(&bytes).expect("decode");
        assert_eq!(ls, 25);
        assert_eq!(active, 1234567);
        assert_eq!(alloc, 999999);
        assert_eq!(decode_circulating_supply(&bytes), Some(supply));

        let legacy = &bytes[..ENCODED_STATE_META_V1_BYTES];
        assert_eq!(decode_state_meta(legacy), Some((25, 1234567, 999999)));
        assert_eq!(decode_circulating_supply(legacy), None);
    }

    #[test]
    fn segment_summary_roundtrip_is_exact_length() {
        let root = [0xA5; 32];
        let bytes = encode_segment_summary(65_535, &root);
        assert_eq!(bytes.len(), ENCODED_SEGMENT_SUMMARY_BYTES);
        assert_eq!(decode_segment_summary(&bytes), Some((65_535, root)));
        assert_eq!(decode_segment_summary(&bytes[..35]), None);
        let mut extended = bytes.to_vec();
        extended.push(0);
        assert_eq!(decode_segment_summary(&extended), None);
    }

    #[test]
    fn consensus_meta_roundtrip() {
        let meta = ConsensusMeta {
            tip_height: 42,
            tip_hash: [0xAA; 32],
            cumulative_chainwork: [0xBB; 32],
            finalized: FinalizedCheckpoint {
                height: 24,
                hash: [0xCC; 32],
            },
        };
        let bytes = encode_consensus_meta(&meta);
        assert_eq!(bytes.len(), ENCODED_CONSENSUS_META_BYTES);
        assert_eq!(decode_consensus_meta(&bytes), Some(meta));
        assert_eq!(decode_consensus_meta(&bytes[..111]), None);
    }

    #[test]
    fn sparse_encoded_segment_size_matches_snapshot_caps() {
        use crate::consensus::wire_limits::{MAX_SEGMENT_BYTES, MAX_SNAPSHOT_MANIFEST_SEGMENTS};

        assert_eq!(encoded_segment_len_for_live_count(16, 0), Some(9));
        assert_eq!(encoded_segment_len_for_live_count(16, 1), Some(59));
        assert_eq!(encoded_segment_live_count_from_len(16, 9), Some(0));
        assert_eq!(encoded_segment_live_count_from_len(16, 59), Some(1));
        assert_eq!(encoded_segment_live_count_from_len(16, 60), None);
        assert_eq!(max_encoded_segment_len_for_eff_log(16), Some(3_276_809));
        assert!(max_encoded_segment_len_for_eff_log(16).unwrap() <= MAX_SEGMENT_BYTES);
        assert_eq!(MAX_SNAPSHOT_MANIFEST_SEGMENTS, u16::MAX as usize + 1);
        assert_eq!(
            max_encoded_segments_total_len(MAX_SNAPSHOT_MANIFEST_SEGMENTS, 16),
            Some(214_748_954_624)
        );
    }

    #[test]
    fn encoded_segment_size_rejects_impossible_logs() {
        assert_eq!(max_encoded_segment_len_for_eff_log(17), None);
        assert_eq!(encoded_segment_len_for_live_count(16, 65_537), None);
        assert_eq!(max_encoded_segments_total_len(usize::MAX, 16), None);
    }

    #[test]
    fn segment_roundtrip_small() {
        // 4 elements per column (effective_log_seg=2)
        let seg = SegmentColumns {
            values: vec![
                Block128::from(1u128),
                Block128::from(2u128),
                Block128::from(3u128),
                Block128::ZERO,
            ],
            owners_hi: vec![Block128::ZERO; 4],
            owners_lo: vec![Block128::ZERO; 4],
        };
        let bytes = encode_segment(&seg, 2);
        assert_eq!(
            bytes.len(),
            3 * ENCODED_SEGMENT_ENTRY_BYTES + ENCODED_SEGMENT_HEADER_BYTES
        );
        let (els, seg2) = decode_segment(&bytes).expect("decode");
        assert_eq!(els, 2);
        assert_eq!(seg2.values.len(), 4);
        assert_eq!(seg2.values[0], Block128::from(1u128));
        assert_eq!(seg2.owners_lo[0], Block128::ZERO);
        assert_eq!(seg2.values, seg.values);
        assert_eq!(seg2.owners_hi, seg.owners_hi);
        assert_eq!(seg2.owners_lo, seg.owners_lo);
    }

    #[test]
    fn sparse_segment_rejects_noncanonical_entries() {
        let mut seg = SegmentColumns::new_zero(4);
        seg.values[1] = Block128::ONE;
        seg.values[3] = Block128::from(2u128);
        let canonical = encode_segment(&seg, 2);
        let sparse = decode_sparse_segment(&canonical).unwrap();
        assert_eq!(sparse.effective_log_segment(), 2);
        assert_eq!(sparse.live_count(), 2);
        let entries = sparse.entries().collect::<Vec<_>>();
        assert_eq!(entries[0].0, 1);
        assert_eq!(entries[1].0, 3);
        assert_eq!(
            encode_sparse_segment_entries(2, &entries),
            Some(canonical.clone())
        );

        let mut duplicate = canonical.clone();
        let second_index = ENCODED_SEGMENT_HEADER_BYTES + ENCODED_SEGMENT_ENTRY_BYTES;
        duplicate[second_index..second_index + 2].copy_from_slice(&1u16.to_le_bytes());
        assert!(decode_segment(&duplicate).is_none());

        let mut empty_entry = canonical.clone();
        let first_value = ENCODED_SEGMENT_HEADER_BYTES + ENCODED_SEGMENT_INDEX_BYTES;
        empty_entry[first_value..first_value + ENCODED_SEGMENT_SLOT_VALUE_BYTES].fill(0);
        assert!(decode_segment(&empty_entry).is_none());

        let mut trailing = canonical;
        trailing.push(0);
        assert!(decode_segment(&trailing).is_none());
    }
}
