// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Capacity-IV domain separation tags for Poseidon2b constructions.
//!
//! See `CRYPTO.md` §3 and §11. Every sponge-mode construction initializes
//! `state[2]`, `state[3]` from an 8-byte ASCII label: the high capacity
//! word holds `LABEL_u64 << 64`, the low holds `LABEL_u64`. Distinct
//! halves prevent trivial cancellation.

use noid_core::Block128;

/// An 8-byte ASCII domain-separation label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DomainTag(pub [u8; 8]);

impl DomainTag {
    pub const fn new(label: &[u8; 8]) -> Self {
        let mut i = 0;
        while i < 8 {
            assert!(label[i] < 128, "domain tag must be ASCII");
            i += 1;
        }
        Self(*label)
    }

    #[inline]
    pub const fn as_u64(&self) -> u64 {
        u64::from_be_bytes(self.0)
    }
}

/// Derive the two capacity-IV words `(state[2], state[3])` from a tag.
#[inline]
pub fn capacity_iv(tag: DomainTag) -> [Block128; 2] {
    let label = tag.as_u64() as u128;
    let high = Block128::from(label << 64);
    let low = Block128::from(label);
    [high, low]
}

/// [`capacity_iv`] mapped into the **flat (GCM) basis** — IV words for
/// constructions whose state lives in the flat basis end to end
/// (`compress_flat_feed_forward_with_tag`, `Poseidon2bFlatSponge`).
#[inline]
pub fn capacity_iv_flat(tag: DomainTag) -> [u128; 2] {
    let [high, low] = capacity_iv(tag);
    [
        noid_core::hardware::tower_to_flat_u128(high.0),
        noid_core::hardware::tower_to_flat_u128(low.0),
    ]
}

pub const TAG_LEAF: DomainTag = DomainTag::new(b"LEAF____");
pub const TAG_COMMIT: DomainTag = DomainTag::new(b"COMMIT__");
pub const TAG_ADDRFIX: DomainTag = DomainTag::new(b"ADDRFIX_");
/// Canonical flattened Tx8x2 body: raw 16-leaf tree plus one wrap permutation.
pub const TAG_TX8X2: DomainTag = DomainTag::new(b"TX8X2___");
/// Count-bound universal 256-leaf block transaction root.
pub const TAG_TXROOT: DomainTag = DomainTag::new(b"TXROOT__");
pub const TAG_BLOCKHDR: DomainTag = DomainTag::new(b"BLOCKHDR");
/// Proof-of-work header digest. Distinct from `BLOCKHDR`: the same semantic
/// header has separate chain-link and mining-difficulty hash domains.
pub const TAG_POWHDR: DomainTag = DomainTag::new(b"POWHDR__");
/// Nonce-free semantic header projection. Distinct from `BLOCKHDR` (chain
/// link, nonce included) and `POWHDR__` (mining digest): one template has
/// exactly one projection across every nonce, so a HistoryStep terminal
/// minted before PoW binds any winning encoding of the same template.
pub const TAG_SEMHDR: DomainTag = DomainTag::new(b"SEMHDR__");
/// Byte-oriented Fiat-Shamir challenger (`FsChallenger`: op headers +
/// length-prefixed byte absorbs).
pub const TAG_FSCHALNG: DomainTag = DomainTag::new(b"FSCHALNG");
/// C1 byte-oriented Fiat-Shamir challenger with 255-bit extension-field
/// challenges. Its framing is intentionally disjoint from `FSCHALNG`.
pub const TAG_FSCH256: DomainTag = DomainTag::new(b"FSCH256_");
/// Lane-oriented Fiat-Shamir challenger for the proof-core transcripts
/// (`FsLaneChallenger` and its in-trace twin). Distinct from the other
/// Fiat-Shamir families so no transcript state can be replayed across
/// challenger constructions that absorb different framings.
pub const TAG_LANECHAL: DomainTag = DomainTag::new(b"LANECHAL");
/// C1 lane-oriented Fiat-Shamir challenger with 255-bit extension-field
/// challenges and a two-coordinate absorb schedule.
pub const TAG_LANE256: DomainTag = DomainTag::new(b"LANE256_");
/// Killshot Fiat-Shamir channel (`Poseidon2bChannel`, the bare rate-2
/// duplex every GKR verifier runs on) and its replays.
pub const TAG_KSCHANNL: DomainTag = DomainTag::new(b"KSCHANNL");
/// C1 GKR/Wallet channel. Every algebraic message occupies one complete
/// two-lane rate block and every squeeze returns one GF(2^256) challenge.
pub const TAG_KSCH256: DomainTag = DomainTag::new(b"KSCH256_");
/// Wallet-capsule FRI transcript (`noid_fri::Channel`) and its replays.
pub const TAG_FRICHANL: DomainTag = DomainTag::new(b"FRICHANL");
pub const TAG_COMPRESS: DomainTag = DomainTag::new(b"COMPRESS");
pub const TAG_DAWTNSS: DomainTag = DomainTag::new(b"DAWTNSS_");
pub const TAG_FRISTATE: DomainTag = DomainTag::new(b"FRISTATE");
/// Segment-level Merkle tree: Poseidon2b binary tree over per-segment
/// FRI roots. The root is the global `state_root` when `num_segments > 1`.
pub const TAG_SEGMENTTREE: DomainTag = DomainTag::new(b"SEGTREE_");
/// Claims commitment: Poseidon2b sponge over all claimed slot data
/// (inputs + outputs). Bridges WalletAuthorizationBundle to exact state proof.
pub const TAG_CLAIMS: DomainTag = DomainTag::new(b"CLAIMS__");
/// Exact UTXO state slot leaf: `PARANOID/EXACT-STATE-SLOT/256/v1`.
pub const TAG_EXSTSLT: DomainTag = DomainTag::new(b"EXSTSLT_");
/// Exact UTXO state binary Merkle node: `PARANOID/EXACT-STATE-NODE/256/v1`.
pub const TAG_EXSTNOD: DomainTag = DomainTag::new(b"EXSTNOD_");
/// Accepted-block claim field transcript for recursive chain accumulation.
pub const TAG_ACCBLK: DomainTag = DomainTag::new(b"ACCBLK__");
/// Accepted history/state transition digest for O(1) state sync.
pub const TAG_HISTTRN: DomainTag = DomainTag::new(b"HISTTRN_");
/// Accepted history/state claim digest for O(1) state sync.
pub const TAG_HISTCLM: DomainTag = DomainTag::new(b"HISTCLM_");
/// Constant public history proof envelope digest for O(1) state sync.
pub const TAG_HISTPRF: DomainTag = DomainTag::new(b"HISTPRF_");
/// Variable-length byte hashing with an explicit absorbed domain string.
pub const TAG_BYTEHASH: DomainTag = DomainTag::new(b"BYTEHASH");
/// Wallet-capsule PCS tree leaf (flat sponge over one 16-symbol fold coset).
pub const TAG_CAPSLEAF: DomainTag = DomainTag::new(b"CAPSLEAF");
/// C1 Wallet-capsule PCS leaf containing sixteen GF(2^256) symbols.
pub const TAG_CAPS256: DomainTag = DomainTag::new(b"CAPS256_");
/// C1 Wallet source leaf containing eight GF(2^128) bank symbols and eight
/// GF(2^256) companion symbols in a canonical packed representation.
pub const TAG_CAPSMIX: DomainTag = DomainTag::new(b"CAPSMIX_");
/// Wallet-capsule PCS tree inner node (1-permutation flat feed-forward
/// compress — the same node shape as the proof-core PCS Merkle).
pub const TAG_CAPSNODE: DomainTag = DomainTag::new(b"CAPSNODE");

#[cfg(test)]
mod tests {
    use super::*;
    use noid_core::TowerField;

    #[test]
    fn all_tags_distinct() {
        let tags = [
            TAG_LEAF,
            TAG_COMMIT,
            TAG_ADDRFIX,
            TAG_TX8X2,
            TAG_TXROOT,
            TAG_BLOCKHDR,
            TAG_POWHDR,
            TAG_SEMHDR,
            TAG_FSCHALNG,
            TAG_FSCH256,
            TAG_LANECHAL,
            TAG_LANE256,
            TAG_KSCHANNL,
            TAG_KSCH256,
            TAG_FRICHANL,
            TAG_COMPRESS,
            TAG_DAWTNSS,
            TAG_FRISTATE,
            TAG_SEGMENTTREE,
            TAG_CLAIMS,
            TAG_EXSTSLT,
            TAG_EXSTNOD,
            TAG_ACCBLK,
            TAG_HISTTRN,
            TAG_HISTCLM,
            TAG_HISTPRF,
            TAG_BYTEHASH,
            TAG_CAPSLEAF,
            TAG_CAPS256,
            TAG_CAPSMIX,
            TAG_CAPSNODE,
        ];
        for i in 0..tags.len() {
            for j in (i + 1)..tags.len() {
                assert_ne!(tags[i], tags[j]);
            }
        }
    }

    #[test]
    fn iv_nonzero_and_split() {
        let [hi, lo] = capacity_iv(TAG_LEAF);
        assert_ne!(hi, Block128::ZERO);
        assert_ne!(lo, Block128::ZERO);
        assert_ne!(hi, lo);
    }

    #[test]
    fn tx8x2_tag_bytes_are_frozen() {
        assert_eq!(TAG_TX8X2.0, *b"TX8X2___");
        assert_eq!(TAG_TX8X2.as_u64(), 0x5458_3858_325f_5f5f);
    }
}
