// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Poseidon2b proof-of-work validation.
//!
//! The mining digest is a fixed-field Poseidon2b sponge over the semantic
//! header fields, under the dedicated `POWHDR__` capacity IV.
//!
//! The absorbed field schedule is fixed at 16 `Block128` elements:
//!
//! ```text
//! prev_block_hash       2 fields
//! state_root            2 fields
//! tx_root               2 fields
//! timestamp             1 field   zero-extended LE u64
//! height                1 field   zero-extended LE u64
//! miner_address         2 fields
//! nonce                 1 field   LE u128
//! difficulty_target     2 fields
//! log_slots             1 field   zero-extended LE u32
//! active_slot_count     1 field   zero-extended LE u64
//! alloc_counter         1 field   zero-extended LE u64
//! ```
//!
//! With Poseidon2b `rate = 2`, this is exactly eight rate blocks and uses
//! `finalize_no_pad()`. Domain separation comes from `POWHDR__`; the semantic
//! chain-link id uses the distinct `BLOCKHDR` domain.

use crate::block_header::BlockHeader;
use crate::consensus::{difficulty::le256_lt, ConsensusError};
use noid_core::{Block128, TowerField};
use noid_poseidon2b::batch::FixedFieldNonceBatch;
use noid_poseidon2b::native::compression::Poseidon2bSponge;
use noid_poseidon2b::native::domain::{capacity_iv, TAG_POWHDR};

/// Consensus semantic block id.
pub type BlockHash = [u8; 32];

/// Number of `Block128` field elements absorbed by `poseidon_pow_digest`.
pub const POW_HEADER_FIELD_COUNT: usize = 16;

/// Index of the nonce field in the fixed PoW field schedule.
pub const POW_NONCE_FIELD_INDEX: usize = 10;

pub type PowHeaderFields = [Block128; POW_HEADER_FIELD_COUNT];

/// Prepared production PoW hasher. One value should be retained by each mining
/// worker so the fixed flat-basis header and scratch allocation are reused
/// across nonce batches.
pub struct PowNonceBatchHasher {
    inner: FixedFieldNonceBatch,
}

impl PowNonceBatchHasher {
    pub fn new(fields: &PowHeaderFields) -> Self {
        Self {
            inner: FixedFieldNonceBatch::new(TAG_POWHDR, fields, POW_NONCE_FIELD_INDEX),
        }
    }

    #[inline]
    pub fn hash_into(&mut self, start_nonce: u128, out: &mut [[u8; 32]]) {
        self.inner.hash_into(start_nonce, out);
    }
}

/// Compute the semantic block id (used as `prev_block_hash` in the next block).
#[inline]
pub fn block_id(h: &BlockHeader) -> BlockHash {
    crate::block_header::block_id(h)
}

/// Fill the fixed Poseidon2b PoW field schedule for a header.
pub fn pow_header_fields_into(h: &BlockHeader, out: &mut PowHeaderFields) {
    let mut i = 0usize;
    put_digest(out, &mut i, &h.prev_block_hash);
    put_digest(out, &mut i, &h.state_root);
    put_digest(out, &mut i, &h.tx_root);
    out[i] = Block128::from(h.timestamp as u128);
    i += 1;
    out[i] = Block128::from(h.height as u128);
    i += 1;
    put_digest(out, &mut i, h.miner_address.as_bytes());
    debug_assert_eq!(i, POW_NONCE_FIELD_INDEX);
    out[i] = Block128::from(h.nonce);
    i += 1;
    put_digest(out, &mut i, &h.difficulty_target);
    out[i] = Block128::from(h.log_slots as u128);
    i += 1;
    out[i] = Block128::from(h.active_slot_count as u128);
    i += 1;
    out[i] = Block128::from(h.alloc_counter as u128);
    i += 1;
    debug_assert_eq!(i, POW_HEADER_FIELD_COUNT);
}

/// Return the fixed Poseidon2b PoW field schedule for a header.
pub fn pow_header_fields(h: &BlockHeader) -> PowHeaderFields {
    let mut fields = [Block128::ZERO; POW_HEADER_FIELD_COUNT];
    pow_header_fields_into(h, &mut fields);
    fields
}

/// Compute `H_POSEIDON_POW(header)`.
#[inline]
pub fn poseidon_pow_digest(header: &BlockHeader) -> BlockHash {
    poseidon_pow_digest_from_fields(&pow_header_fields(header))
}

/// Compute `H_POSEIDON_POW(fields)` from an already materialized field schedule.
pub fn poseidon_pow_digest_from_fields(fields: &PowHeaderFields) -> BlockHash {
    let mut sponge = Poseidon2bSponge::with_iv(capacity_iv(TAG_POWHDR));
    for chunk in fields.chunks_exact(2) {
        sponge.absorb_pair(chunk[0], chunk[1]);
    }
    sponge.finalize_no_pad()
}

/// Compute `H_POSEIDON_POW` for consecutive nonce values.
///
/// `out[i]` is the digest for `fields` with nonce `start_nonce + i`.
/// The packed path is consensus-equivalent to [`poseidon_pow_digest_from_fields`]
/// and only changes how many independent permutations are evaluated together.
pub fn poseidon_pow_digest_nonce_batch(
    fields: &PowHeaderFields,
    start_nonce: u128,
    out: &mut [[u8; 32]],
) {
    PowNonceBatchHasher::new(fields).hash_into(start_nonce, out);
}

/// Validate that the block satisfies the declared PoW target.
///
/// Computes `pow_digest = H_POSEIDON_POW(header)` and checks
/// `pow_digest < header.difficulty_target` as little-endian 256-bit integers.
/// Equality is rejected.
pub fn validate_pow(header: &BlockHeader) -> Result<BlockHash, ConsensusError> {
    let digest = poseidon_pow_digest(header);
    if le256_lt(&digest, &header.difficulty_target) {
        Ok(digest)
    } else {
        Err(ConsensusError::InvalidPoW)
    }
}

/// Search for a valid PoW nonce in `[start, start + range)`.
pub fn search_pow(header_template: &BlockHeader, start_nonce: u128, range: u128) -> Option<u128> {
    let fields = pow_header_fields(header_template);
    let mut hasher = PowNonceBatchHasher::new(&fields);
    let target = &header_template.difficulty_target;
    let mut digests = [[0u8; 32]; 64];
    let mut done = 0u128;
    while done < range {
        let batch_len = ((range - done).min(digests.len() as u128)) as usize;
        let nonce_base = start_nonce.saturating_add(done);
        hasher.hash_into(nonce_base, &mut digests[..batch_len]);
        for (i, digest) in digests[..batch_len].iter().enumerate() {
            if le256_lt(digest, target) {
                return Some(nonce_base.saturating_add(i as u128));
            }
        }
        done += batch_len as u128;
    }
    None
}

#[inline]
fn put_digest(out: &mut PowHeaderFields, index: &mut usize, digest: &[u8; 32]) {
    out[*index] = Block128::from(u128::from_le_bytes(digest[..16].try_into().unwrap()));
    *index += 1;
    out[*index] = Block128::from(u128::from_le_bytes(digest[16..].try_into().unwrap()));
    *index += 1;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_header::BlockHeader;
    use noid_core::packed::PACKED_LANES;
    use noid_poseidon2b::native::domain::{capacity_iv, TAG_BLOCKHDR};
    use noid_poseidon2b::primitives::Address;

    const TEST_TARGET: [u8; 32] = [0xFF; 32];

    fn dummy_header() -> BlockHeader {
        BlockHeader {
            prev_block_hash: [0u8; 32],
            state_root: [1u8; 32],
            tx_root: [2u8; 32],
            timestamp: 1_700_000_000,
            height: 1,
            miner_address: Address([3u8; 32]),
            nonce: 0,
            difficulty_target: TEST_TARGET,
            log_slots: 24,
            active_slot_count: 0,
            alloc_counter: 0,
        }
    }

    #[test]
    fn pow_field_schedule_is_fixed_and_canonical() {
        let mut h = dummy_header();
        h.prev_block_hash = [0x10; 32];
        h.state_root = [0x20; 32];
        h.tx_root = [0x30; 32];
        h.timestamp = 0x0102_0304_0506_0708;
        h.height = 0x1112_1314_1516_1718;
        h.miner_address = Address([0x40; 32]);
        h.nonce = 0x2122_2324_2526_2728_3132_3334_3536_3738;
        h.difficulty_target = [0x50; 32];
        h.log_slots = 0x6162_6364;
        h.active_slot_count = 0x7172_7374_7576_7778;
        h.alloc_counter = 0x8182_8384_8586_8788;

        let fields = pow_header_fields(&h);
        assert_eq!(fields.len(), POW_HEADER_FIELD_COUNT);
        assert_eq!(POW_NONCE_FIELD_INDEX, 10);
        assert_eq!(fields[0], digest_half(&h.prev_block_hash, 0));
        assert_eq!(fields[1], digest_half(&h.prev_block_hash, 1));
        assert_eq!(fields[2], digest_half(&h.state_root, 0));
        assert_eq!(fields[3], digest_half(&h.state_root, 1));
        assert_eq!(fields[4], digest_half(&h.tx_root, 0));
        assert_eq!(fields[5], digest_half(&h.tx_root, 1));
        assert_eq!(fields[6], Block128::from(h.timestamp as u128));
        assert_eq!(fields[7], Block128::from(h.height as u128));
        assert_eq!(fields[8], digest_half(h.miner_address.as_bytes(), 0));
        assert_eq!(fields[9], digest_half(h.miner_address.as_bytes(), 1));
        assert_eq!(fields[10], Block128::from(h.nonce));
        assert_eq!(fields[11], digest_half(&h.difficulty_target, 0));
        assert_eq!(fields[12], digest_half(&h.difficulty_target, 1));
        assert_eq!(fields[13], Block128::from(h.log_slots as u128));
        assert_eq!(fields[14], Block128::from(h.active_slot_count as u128));
        assert_eq!(fields[15], Block128::from(h.alloc_counter as u128));
    }

    #[test]
    fn pow_digest_uses_distinct_domain_from_block_id() {
        let h = dummy_header();
        assert_ne!(capacity_iv(TAG_POWHDR), capacity_iv(TAG_BLOCKHDR));
        assert_ne!(poseidon_pow_digest(&h), block_id(&h));
    }

    #[test]
    fn nonce_change_changes_pow_digest() {
        let mut h = dummy_header();
        let digest1 = poseidon_pow_digest(&h);
        h.nonce = 42;
        let digest2 = poseidon_pow_digest(&h);
        assert_ne!(digest1, digest2);
    }

    #[test]
    fn pow_nonce_batch_matches_scalar_for_partial_and_full_chunks() {
        let h = dummy_header();
        let fields = pow_header_fields(&h);
        let start = 123_456u128;
        let n = PACKED_LANES * 3 + 1;
        let mut batch = vec![[0u8; 32]; n];

        poseidon_pow_digest_nonce_batch(&fields, start, &mut batch);

        for (i, digest) in batch.iter().enumerate() {
            let mut scalar_fields = fields;
            scalar_fields[POW_NONCE_FIELD_INDEX] = Block128::from(start + i as u128);
            assert_eq!(*digest, poseidon_pow_digest_from_fields(&scalar_fields));
        }
    }

    #[test]
    fn search_pow_returns_nonce_that_validates() {
        let mut h = dummy_header();
        let nonce = search_pow(&h, 0, 16).expect("max target should accept quickly");
        h.nonce = nonce;
        assert!(validate_pow(&h).is_ok());
    }

    #[test]
    fn validate_pow_rejects_zero_target() {
        let mut h = dummy_header();
        h.difficulty_target = [0u8; 32];
        assert_eq!(validate_pow(&h), Err(ConsensusError::InvalidPoW));
    }

    #[test]
    fn validate_pow_accepts_easy_target() {
        let mut h = dummy_header();
        h.nonce = 0;
        assert!(validate_pow(&h).is_ok());
    }

    #[test]
    fn le256_lt_correctness() {
        let zero = [0u8; 32];
        let mut one = [0u8; 32];
        one[0] = 1;
        let mut big = [0u8; 32];
        big[31] = 1;

        assert!(le256_lt(&zero, &one));
        assert!(le256_lt(&one, &big));
        assert!(!le256_lt(&big, &zero));
        assert!(!le256_lt(&one, &one));
    }

    #[inline]
    fn digest_half(digest: &[u8; 32], half: usize) -> Block128 {
        let offset = half * 16;
        Block128::from(u128::from_le_bytes(
            digest[offset..offset + 16].try_into().unwrap(),
        ))
    }
}
