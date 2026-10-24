// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Genesis block construction.
//!
//! The genesis block is hardcoded: same bytes on every node.
//! It has:
//! - Zero state (all slots empty)
//! - Fixed Poseidon2b PoW target
//! - Coinbase to burn address (initial coins bootstrapping)
//! - no transported HistoryStep terminal; genesis is the built-in recursion boundary
//!
//! The genesis state_root is the direct exact sparse-Merkle root of an empty UTXO tree.

use crate::block_header::BlockHeader;
use crate::consensus::{
    params::{GENESIS_TARGET, LOG_SLOTS_GENESIS},
    pow::search_pow,
};
use noid_poseidon2b::primitives::Address;

/// Fixed mainnet genesis timestamp (2026-08-21 16:00:00 UTC).
pub const GENESIS_TIMESTAMP: u64 = 1_787_328_000;

/// The genesis burn address — coinbase recipient at height 0.
/// Uses a zero address; no private key is known.
pub const GENESIS_BURN_ADDRESS: Address = Address([0u8; 32]);

/// Build the canonical genesis block header.
///
/// The header's PoW is pre-computed and hardcoded. The `state_root` is the
/// canonical empty-state root and `tx_root` is all-zeros (coinbase-only,
/// computed by the full node layer).
///
/// Every node must produce byte-identical output from this function.
pub fn genesis_header() -> BlockHeader {
    BlockHeader {
        prev_block_hash: [0u8; 32],
        state_root: genesis_state_root(),
        tx_root: [0u8; 32],
        timestamp: GENESIS_TIMESTAMP,
        height: 0,
        miner_address: GENESIS_BURN_ADDRESS,
        nonce: GENESIS_NONCE,
        difficulty_target: GENESIS_TARGET,
        // Genesis is built in and has no attached HistoryStep terminal.
        log_slots: LOG_SLOTS_GENESIS,
        active_slot_count: 0,
        alloc_counter: 0,
    }
}

/// The canonical genesis state root of the all-zero exact UTXO tree at
/// `LOG_SLOTS_GENESIS`.
///
/// Computed from `zero_slot_roots(LOG_SLOTS_GENESIS)` and hardcoded.
/// Verified by the test `genesis_state_root_matches_computed` below.
pub fn genesis_state_root() -> [u8; 32] {
    GENESIS_STATE_ROOT
}

/// Pre-computed genesis state root. All 2^24 slots are zero.
const GENESIS_STATE_ROOT: [u8; 32] = [
    0x5c, 0x7f, 0x37, 0x12, 0x61, 0x1c, 0x83, 0x6a, 0x2c, 0x6a, 0xb0, 0x44, 0x8d, 0x32, 0xc2, 0x71,
    0xf0, 0x4e, 0x32, 0x13, 0x56, 0x0e, 0x8a, 0x53, 0x21, 0x33, 0x1c, 0xd6, 0xa5, 0xc9, 0x84, 0x92,
];

/// Pre-mined genesis nonce.
/// Satisfies: `H_POSEIDON_POW(genesis_header()) < GENESIS_TARGET`.
/// Mined for the canonical 16-field PoW schedule.
const GENESIS_NONCE: u128 = 28_170;

/// Find and return a valid genesis nonce at runtime.
/// Used for verification only — not for production (nonce is hardcoded as `GENESIS_NONCE`).
pub fn find_genesis_nonce() -> u128 {
    let mut h = genesis_header();
    h.nonce = 0;
    search_pow(&h, 0, 100_000_000).expect("genesis target is trivially satisfiable")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn genesis_header_is_deterministic() {
        let a = genesis_header();
        let b = genesis_header();
        assert_eq!(a.height, b.height);
        assert_eq!(a.timestamp, b.timestamp);
        assert_eq!(a.difficulty_target, b.difficulty_target);
        assert_eq!(a.prev_block_hash, b.prev_block_hash);
    }

    #[test]
    fn genesis_header_fields() {
        let h = genesis_header();
        assert_eq!(h.height, 0);
        assert_eq!(h.prev_block_hash, [0u8; 32]);
        assert_eq!(h.difficulty_target, GENESIS_TARGET);
        assert_eq!(h.log_slots, LOG_SLOTS_GENESIS);
        assert_eq!(h.active_slot_count, 0);
        assert_eq!(h.alloc_counter, 0);
    }

    #[test]
    fn genesis_state_root_matches_computed() {
        let mut state = crate::state::ChainState::with_log_slots(24);
        assert_eq!(state.state_root(), genesis_state_root());
    }

    /// Print the new genesis state root and a valid nonce for it.
    /// Run with: cargo test -p noid_chain --lib -- consensus::genesis::tests::print_new_genesis --nocapture
    #[test]
    #[ignore]
    fn print_new_genesis() {
        let mut state = crate::state::ChainState::with_log_slots(24);
        let new_root = state.state_root();
        println!("\nNew GENESIS_STATE_ROOT:");
        print!("const GENESIS_STATE_ROOT: [u8; 32] = [");
        for (i, b) in new_root.iter().enumerate() {
            if i % 16 == 0 {
                print!("\n    ");
            }
            print!("0x{:02x}, ", b);
        }
        println!("\n];");
        let new_nonce = find_genesis_nonce_for(&new_root);
        println!("New GENESIS_NONCE: {}", new_nonce);
        print!("New GENESIS_BLOCK_ID: ");
        for byte in crate::block_header::block_id(&genesis_header()) {
            print!("{byte:02x}");
        }
        println!();
    }

    fn find_genesis_nonce_for(state_root: &[u8; 32]) -> u128 {
        use crate::block_header::BlockHeader;
        use crate::consensus::params::{GENESIS_TARGET, LOG_SLOTS_GENESIS};
        use crate::consensus::pow::search_pow;
        let h = BlockHeader {
            prev_block_hash: [0u8; 32],
            state_root: *state_root,
            tx_root: [0u8; 32],
            timestamp: GENESIS_TIMESTAMP,
            height: 0,
            miner_address: GENESIS_BURN_ADDRESS,
            nonce: 0,
            difficulty_target: GENESIS_TARGET,
            log_slots: LOG_SLOTS_GENESIS,
            active_slot_count: 0,
            alloc_counter: 0,
        };
        search_pow(&h, 0, 2_000_000_000).expect("genesis target is trivially satisfiable")
    }

    #[test]
    fn genesis_nonce_satisfies_pow() {
        let h = genesis_header();
        use crate::consensus::pow::validate_pow;
        assert!(
            validate_pow(&h).is_ok(),
            "GENESIS_NONCE={} must satisfy PoW",
            GENESIS_NONCE
        );
    }

    #[test]
    fn genesis_block_id_is_canonical() {
        assert_eq!(
            crate::block_header::block_id(&genesis_header()),
            [
                0x86, 0x0e, 0x70, 0x45, 0x33, 0x90, 0xbf, 0x81, 0x57, 0x18, 0xe9, 0x33, 0xaa, 0x49,
                0x27, 0x16, 0x7a, 0x13, 0xd0, 0x98, 0xb0, 0x15, 0x13, 0x91, 0xee, 0xfd, 0x72, 0x2e,
                0xe1, 0xad, 0xd6, 0x10,
            ]
        );
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn genesis_timestamp_is_reasonable() {
        assert_eq!(GENESIS_TIMESTAMP, 1_787_328_000);
    }
}
