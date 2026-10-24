// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical wire encoding for chain-level types.
//!
//! Same rules as `noid_tx::wire`: fixed-width little-endian, no hidden
//! padding, errors on truncation / trailing bytes / unknown version.

use noid_poseidon2b::primitives::Address;
use noid_tx::wire::WireError;

use crate::block_header::BlockHeader;

#[inline]
fn put_digest(buf: &mut Vec<u8>, d: &[u8; 32]) {
    buf.extend_from_slice(d);
}

#[inline]
fn put_u32(buf: &mut Vec<u8>, v: u32) {
    buf.extend_from_slice(&v.to_le_bytes());
}

#[inline]
fn put_u64(buf: &mut Vec<u8>, v: u64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

#[inline]
fn put_u128(buf: &mut Vec<u8>, v: u128) {
    buf.extend_from_slice(&v.to_le_bytes());
}

#[inline]
fn take<'a>(src: &mut &'a [u8], n: usize) -> Result<&'a [u8], WireError> {
    if src.len() < n {
        return Err(WireError::Truncated);
    }
    let (head, tail) = src.split_at(n);
    *src = tail;
    Ok(head)
}

#[inline]
fn take_digest(src: &mut &[u8]) -> Result<[u8; 32], WireError> {
    let bytes = take(src, 32)?;
    let mut out = [0u8; 32];
    out.copy_from_slice(bytes);
    Ok(out)
}

#[inline]
fn take_u32(src: &mut &[u8]) -> Result<u32, WireError> {
    let bytes = take(src, 4)?;
    Ok(u32::from_le_bytes(bytes.try_into().unwrap()))
}

#[inline]
fn take_u64(src: &mut &[u8]) -> Result<u64, WireError> {
    let bytes = take(src, 8)?;
    Ok(u64::from_le_bytes(bytes.try_into().unwrap()))
}

#[inline]
fn take_u128(src: &mut &[u8]) -> Result<u128, WireError> {
    let bytes = take(src, 16)?;
    Ok(u128::from_le_bytes(bytes.try_into().unwrap()))
}

/// Wire size of a [`BlockHeader`] in bytes.
///
/// Field breakdown (all LE):
/// ```text
///   prev_block_hash       32B
///   state_root            32B
///   tx_root               32B
///   timestamp              8B
///   height                 8B
///   miner_address         32B
///   nonce                 16B
///   difficulty_target     32B
///   log_slots              4B
///   active_slot_count      8B
///   alloc_counter          8B
///   ─────────────────────────
///   Total                212B
/// ```
pub const BLOCK_HEADER_WIRE_SIZE: usize =
    32   // prev_block_hash
    + 32 // state_root
    + 32 // tx_root
    + 8  // timestamp
    + 8  // height
    + 32 // miner_address
    + 16 // nonce
    + 32 // difficulty_target
    + 4  // log_slots
    + 8  // active_slot_count
    + 8  // alloc_counter
    ; // = 212

/// Byte offset of `BlockHeader::nonce` inside the canonical block-header wire.
pub const BLOCK_HEADER_NONCE_OFFSET: usize = 32 + 32 + 32 + 8 + 8 + 32;

impl BlockHeader {
    pub fn encode(&self, buf: &mut Vec<u8>) {
        put_digest(buf, &self.prev_block_hash);
        put_digest(buf, &self.state_root);
        put_digest(buf, &self.tx_root);
        put_u64(buf, self.timestamp);
        put_u64(buf, self.height);
        put_digest(buf, self.miner_address.as_bytes());
        put_u128(buf, self.nonce);
        put_digest(buf, &self.difficulty_target);
        put_u32(buf, self.log_slots);
        put_u64(buf, self.active_slot_count);
        put_u64(buf, self.alloc_counter);
    }

    pub fn to_bytes(&self) -> [u8; BLOCK_HEADER_WIRE_SIZE] {
        let mut buf = Vec::with_capacity(BLOCK_HEADER_WIRE_SIZE);
        self.encode(&mut buf);
        debug_assert_eq!(buf.len(), BLOCK_HEADER_WIRE_SIZE);
        let mut out = [0u8; BLOCK_HEADER_WIRE_SIZE];
        out.copy_from_slice(&buf);
        out
    }

    pub fn decode(src: &mut &[u8]) -> Result<Self, WireError> {
        let prev_block_hash = take_digest(src)?;
        let state_root = take_digest(src)?;
        let tx_root = take_digest(src)?;
        let timestamp = take_u64(src)?;
        let height = take_u64(src)?;
        let miner_address = Address(take_digest(src)?);
        let nonce = take_u128(src)?;
        let difficulty_target = take_digest(src)?;
        let log_slots = take_u32(src)?;
        let active_slot_count = take_u64(src)?;
        let alloc_counter = take_u64(src)?;
        Ok(Self {
            prev_block_hash,
            state_root,
            tx_root,
            timestamp,
            height,
            miner_address,
            nonce,
            difficulty_target,
            log_slots,
            active_slot_count,
            alloc_counter,
        })
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, WireError> {
        let mut src = bytes;
        let out = Self::decode(&mut src)?;
        if !src.is_empty() {
            return Err(WireError::TrailingBytes);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hdr() -> BlockHeader {
        BlockHeader {
            prev_block_hash: [0x11u8; 32],
            state_root: [0x22u8; 32],
            tx_root: [0x33u8; 32],
            timestamp: 1_700_000_000,
            height: 42,
            miner_address: Address([0x44u8; 32]),
            nonce: 0xDEAD_BEEF_CAFE_BABEu128,
            difficulty_target: [0x77u8; 32],
            log_slots: 24,
            active_slot_count: 7_777,
            alloc_counter: 8_888,
        }
    }

    #[test]
    fn wire_size_constant_is_correct() {
        assert_eq!(BLOCK_HEADER_WIRE_SIZE, 212);
        let h = hdr();
        assert_eq!(h.to_bytes().len(), BLOCK_HEADER_WIRE_SIZE);
    }

    #[test]
    fn block_header_roundtrip() {
        let h = hdr();
        let bytes = h.to_bytes();
        assert_eq!(bytes.len(), BLOCK_HEADER_WIRE_SIZE);
        let back = BlockHeader::from_bytes(&bytes).unwrap();
        assert_eq!(back, h);
    }

    #[test]
    fn header_truncation_errors_cleanly() {
        let h = hdr();
        let bytes = h.to_bytes();
        for cut in 0..bytes.len() {
            assert!(
                BlockHeader::from_bytes(&bytes[..cut]).is_err(),
                "truncation at {cut} should error"
            );
        }
    }

    #[test]
    fn header_rejects_trailing_bytes() {
        let h = hdr();
        let mut v = h.to_bytes().to_vec();
        v.push(0);
        assert_eq!(BlockHeader::from_bytes(&v), Err(WireError::TrailingBytes));
    }

    #[test]
    fn state_boundary_fields_survive_roundtrip() {
        let mut h = hdr();
        h.log_slots = 27;
        h.active_slot_count = u64::MAX;
        h.alloc_counter = 123_456_789;
        let back = BlockHeader::from_bytes(&h.to_bytes()).unwrap();
        assert_eq!(back.log_slots, 27);
        assert_eq!(back.active_slot_count, u64::MAX);
        assert_eq!(back.alloc_counter, 123_456_789);
    }
}
