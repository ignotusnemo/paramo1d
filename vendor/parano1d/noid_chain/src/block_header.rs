// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Block-header hash.
//!
//! `H_BLOCK` absorbs all consensus-significant header fields in the order
//! declared below, using capacity IV = `BLOCKHDR`. Each 32-byte digest is
//! absorbed as two `Block128` halves (hi then lo, little-endian). Scalar
//! integers are absorbed as a single `Block128` word (zero-extended).
//!
//! **Field order is locked. Future fields MUST be appended at the end**,
//! never reordered. Consensus nodes reject any header whose byte count
//! does not equal `BLOCK_HEADER_WIRE_SIZE`.

use noid_core::Block128;
use noid_poseidon2b::native::compression::Poseidon2bSponge;
use noid_poseidon2b::native::domain::{capacity_iv, TAG_BLOCKHDR, TAG_SEMHDR};
use noid_poseidon2b::primitives::{Address, Digest};

/// Canonical block header.
///
/// Byte layout (see `BLOCK_HEADER_WIRE_SIZE` in `wire.rs`):
///
/// ```text
///   prev_block_hash       [32B]  hash of previous header
///   state_root            [32B]  exact sparse-Merkle UTXO root
///   tx_root               [32B]  count-bound universal transaction root
///   timestamp             [8B]   seconds since Unix epoch (LE u64)
///   height                [8B]   block height (LE u64)
///   miner_address         [32B]  coinbase recipient address
///   nonce                 [16B]  128-bit Poseidon2b PoW nonce (LE u128)
///   difficulty_target     [32B]  256-bit ASERT target
///   log_slots             [4B]   current slot-space depth (LE u32)
///   active_slot_count     [8B]   live UTXO count after this block (LE u64)
///   alloc_counter         [8B]   monotonic PRNG seed after this block (LE u64)
/// ```
///
/// Total: 212 bytes (see `BLOCK_HEADER_WIRE_SIZE`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BlockHeader {
    pub prev_block_hash: Digest,
    /// Exact sparse-Merkle root over the UTXO slot vector.
    pub state_root: Digest,
    /// Count-bound `TAG_TXROOT` wrap of the universal 256-leaf transaction tree.
    pub tx_root: Digest,
    pub timestamp: u64,
    pub height: u64,
    pub miner_address: Address,
    /// 128-bit Poseidon2b PoW nonce.
    pub nonce: u128,
    /// 256-bit ASERT difficulty target (LE). Block valid iff
    /// `H_POSEIDON_POW(header) < difficulty_target`.
    pub difficulty_target: [u8; 32],
    /// Slot-space depth: `log₂(num_slots)`. Production values are in
    /// `[LOG_SLOTS_GENESIS, LOG_SLOTS_MAX]`; small in-memory fixtures may use
    /// reduced domains. Replicated in every Fiat-Shamir
    pub log_slots: u32,
    /// Number of live (non-empty) slots after all transactions in this block
    /// are applied. Each hard-finalized value is an input to the state-depth
    /// expansion rule. MUST equal `ChainState::active_slot_count` after
    /// `apply_block`.
    pub active_slot_count: u64,
    /// Monotonic PRNG seed: incremented on every successful mint.
    /// MUST equal `ChainState::alloc_counter` after `apply_block`.
    pub alloc_counter: u64,
}

/// Compute the semantic `block_id` — the Poseidon2b hash of the canonical
/// semantic header.
///
/// Header identity is also used by the separate 144-block transaction epoch.
/// and for chain linking (`prev_block_hash`).
pub fn hash_block_header(hdr: &BlockHeader) -> Digest {
    let mut s = Poseidon2bSponge::with_iv(capacity_iv(TAG_BLOCKHDR));

    absorb_digest(&mut s, &hdr.prev_block_hash);
    absorb_digest(&mut s, &hdr.state_root);
    absorb_digest(&mut s, &hdr.tx_root);
    s.absorb(Block128::from(hdr.timestamp as u128));
    s.absorb(Block128::from(hdr.height as u128));
    absorb_digest(&mut s, hdr.miner_address.as_bytes());
    s.absorb(Block128::from(hdr.nonce));
    absorb_digest(&mut s, &hdr.difficulty_target);
    s.absorb(Block128::from(hdr.log_slots as u128));
    s.absorb(Block128::from(hdr.active_slot_count as u128));
    s.absorb(Block128::from(hdr.alloc_counter as u128));

    s.finalize()
}

/// Explicit alias for the consensus semantic chain-link id.
#[inline]
pub fn block_id(hdr: &BlockHeader) -> Digest {
    hash_block_header(hdr)
}

/// Compute the nonce-free semantic header projection `C` under `SEMHDR__`.
///
/// Absorbs every consensus-significant field in exactly the
/// `hash_block_header` order with the nonce skipped, so one template has one
/// projection across every nonce. A HistoryStep terminal binds this value;
/// the chain-link identity stays `block_id` (`BLOCKHDR`, nonce included) and
/// every accepting node natively requires the two to agree on one header.
pub fn semantic_header_id(hdr: &BlockHeader) -> Digest {
    let mut s = Poseidon2bSponge::with_iv(capacity_iv(TAG_SEMHDR));

    absorb_digest(&mut s, &hdr.prev_block_hash);
    absorb_digest(&mut s, &hdr.state_root);
    absorb_digest(&mut s, &hdr.tx_root);
    s.absorb(Block128::from(hdr.timestamp as u128));
    s.absorb(Block128::from(hdr.height as u128));
    absorb_digest(&mut s, hdr.miner_address.as_bytes());
    absorb_digest(&mut s, &hdr.difficulty_target);
    s.absorb(Block128::from(hdr.log_slots as u128));
    s.absorb(Block128::from(hdr.active_slot_count as u128));
    s.absorb(Block128::from(hdr.alloc_counter as u128));

    s.finalize()
}

#[inline]
fn absorb_digest(s: &mut Poseidon2bSponge, d: &Digest) {
    let hi = Block128::from(u128::from_le_bytes(d[..16].try_into().unwrap()));
    let lo = Block128::from(u128::from_le_bytes(d[16..].try_into().unwrap()));
    s.absorb_pair(hi, lo);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn header_fixture() -> BlockHeader {
        BlockHeader {
            prev_block_hash: [0x11u8; 32],
            state_root: [0x22u8; 32],
            tx_root: [0x33u8; 32],
            timestamp: 1_700_000_000,
            height: 100,
            miner_address: Address([0x44u8; 32]),
            nonce: 0xDEAD_BEEF_CAFE_BABEu128,
            difficulty_target: [0x77u8; 32],
            log_slots: 24,
            active_slot_count: 12_345,
            alloc_counter: 99_999,
        }
    }

    #[test]
    fn determinism() {
        let h = header_fixture();
        assert_eq!(hash_block_header(&h), hash_block_header(&h));
    }

    #[test]
    fn each_field_affects_hash() {
        let base = header_fixture();
        let baseline = hash_block_header(&base);

        macro_rules! check {
            ($field:ident, $val:expr) => {{
                let mut h = base;
                h.$field = $val;
                assert_ne!(
                    hash_block_header(&h),
                    baseline,
                    "field {} did not affect hash",
                    stringify!($field)
                );
            }};
        }

        check!(prev_block_hash, [0xAAu8; 32]);
        check!(state_root, [0xAAu8; 32]);
        check!(tx_root, [0xAAu8; 32]);
        check!(timestamp, base.timestamp + 1);
        check!(height, base.height + 1);
        check!(miner_address, Address([0xAAu8; 32]));
        check!(nonce, base.nonce ^ 1);
        check!(difficulty_target, [0xAAu8; 32]);
        check!(log_slots, base.log_slots + 1);
        check!(active_slot_count, base.active_slot_count + 1);
        check!(alloc_counter, base.alloc_counter + 1);
    }

    #[test]
    fn domain_disjoint_from_tx8x2() {
        use noid_poseidon2b::native::domain::{capacity_iv, TAG_TX8X2};

        let h = header_fixture();
        let block_digest = hash_block_header(&h);

        // Build the same absorb schedule under a different IV.
        let mut s = Poseidon2bSponge::with_iv(capacity_iv(TAG_TX8X2));
        absorb_digest(&mut s, &h.prev_block_hash);
        absorb_digest(&mut s, &h.state_root);
        absorb_digest(&mut s, &h.tx_root);
        s.absorb(Block128::from(h.timestamp as u128));
        s.absorb(Block128::from(h.height as u128));
        absorb_digest(&mut s, h.miner_address.as_bytes());
        s.absorb(Block128::from(h.nonce));
        absorb_digest(&mut s, &h.difficulty_target);
        s.absorb(Block128::from(h.log_slots as u128));
        s.absorb(Block128::from(h.active_slot_count as u128));
        s.absorb(Block128::from(h.alloc_counter as u128));
        let tx8x2_flavor = s.finalize();

        assert_ne!(block_digest, tx8x2_flavor);
    }

    #[test]
    fn semantic_projection_ignores_only_the_nonce() {
        let base = header_fixture();
        let baseline = semantic_header_id(&base);

        let mut renonced = base;
        renonced.nonce = base.nonce ^ 0xFFFF;
        assert_eq!(semantic_header_id(&renonced), baseline);
        assert_ne!(hash_block_header(&renonced), hash_block_header(&base));

        macro_rules! check {
            ($field:ident, $val:expr) => {{
                let mut h = base;
                h.$field = $val;
                assert_ne!(
                    semantic_header_id(&h),
                    baseline,
                    "semantic field {} did not affect the projection",
                    stringify!($field)
                );
            }};
        }

        check!(prev_block_hash, [0xAAu8; 32]);
        check!(state_root, [0xAAu8; 32]);
        check!(tx_root, [0xAAu8; 32]);
        check!(timestamp, base.timestamp + 1);
        check!(height, base.height + 1);
        check!(miner_address, Address([0xAAu8; 32]));
        check!(difficulty_target, [0xAAu8; 32]);
        check!(log_slots, base.log_slots + 1);
        check!(active_slot_count, base.active_slot_count + 1);
        check!(alloc_counter, base.alloc_counter + 1);
    }

    #[test]
    fn semantic_domain_disjoint_from_chain_link() {
        let h = header_fixture();

        // The same nonce-free absorb schedule under the chain-link IV must
        // not collide with the semantic projection domain.
        let mut s = Poseidon2bSponge::with_iv(capacity_iv(TAG_BLOCKHDR));
        absorb_digest(&mut s, &h.prev_block_hash);
        absorb_digest(&mut s, &h.state_root);
        absorb_digest(&mut s, &h.tx_root);
        s.absorb(Block128::from(h.timestamp as u128));
        s.absorb(Block128::from(h.height as u128));
        absorb_digest(&mut s, h.miner_address.as_bytes());
        absorb_digest(&mut s, &h.difficulty_target);
        s.absorb(Block128::from(h.log_slots as u128));
        s.absorb(Block128::from(h.active_slot_count as u128));
        s.absorb(Block128::from(h.alloc_counter as u128));
        let chain_link_flavor = s.finalize();

        assert_ne!(semantic_header_id(&h), chain_link_flavor);
        assert_ne!(semantic_header_id(&h), hash_block_header(&h));
    }
}
