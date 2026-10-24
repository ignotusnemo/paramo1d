// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Consensus logic — pure, I/O-free validation functions.
//!
//! This module contains every consensus rule for Paranoid. All functions
//! are deterministic and produce identical results on any architecture.
//! No networking, no disk I/O, no mutable global state.
//!
//! # Modules
//!
//! - [`params`]         — All consensus constants (single source of truth).
//! - [`emission`]       — Block reward schedule (halves per state expansion).
//! - [`fees`]           — Consensus fee model and burned state-growth fee.
//! - [`difficulty`]     — ASERT difficulty adjustment (no floats).
//! - [`pow`]            — Poseidon2b PoW over semantic header fields.
//! - [`timestamps`]     — Median-time-past and future-drift rules.
//! - [`receipt`]        — ParanoidReceipt generation and verification.
//! - [`header`]         — Per-block header validation rules.
//! - [`checks`]         — Slot-conflict and tx-consensus validation.
//! - [`allocator`]      — Slot hint generation (splitmix64, zone-based).
//! - [`fork_choice`]    — Cumulative-chainwork fork choice rule.
//! - [`reorg`]          — Chain reorganisation within finality window.
//! - [`template`]       — Block template assembly for the miner.
//! - [`validation`]     — Full block consensus + state application.
//! - [`ordering`]       — Canonical tx ordering policy for block assembly.
//! - [`conflict`]       — Slot-conflict resolution between competing txs.
//! - [`da_prune`]       — Undo-log build/prune for chain reorg support.
//! - [`genesis`]        — Genesis block / state root derivation.
//! - [`network`]        — Network-kind parameters and per-network constants.
//! - [`wire_limits`]    — Shared wire/memory/decode DoS caps.

pub mod checks;
pub mod conflict;
pub mod da_prune;
pub mod network;
pub mod ordering;
pub mod paged_spend;
pub mod reorg;
pub mod template;
pub mod validation;
pub mod wire_limits;

pub mod allocator;
pub mod development_allocation;
pub mod difficulty;
pub mod emission;
pub mod epoch_anchor;
pub mod fees;
pub mod fork_choice;
pub mod forks;
pub mod genesis;
pub mod header;
pub mod params;
pub mod pow;
pub mod receipt;
pub mod slot_expansion;
pub mod timestamps;

// Convenient re-exports.
pub use allocator::{
    deduplicate_hints, generate_slot_hints, generate_zone_segment_hints, splitmix64,
};
pub use checks::{validate_block_slot_conflicts, validate_tx_consensus};
pub use conflict::resolve_slot_conflicts;
pub use da_prune::{build_undo_log, prune_undo_logs, revert_block, BlockUndoLog};
pub use development_allocation::{
    development_allocation, development_allocation_active, development_payout_due,
    development_share_each, miner_subsidy, DevelopmentAllocation, DevelopmentAllocationError,
    DEVELOPMENT_ALLOCATION_END_HEIGHT, DEVELOPMENT_ALLOCATION_PAYOUTS,
    DEVELOPMENT_SHARE_DENOMINATOR, O1_NETWORK_FUND_ADDRESS, PARANO1D_LAB_ADDRESS,
    TARGET_BLOCKS_PER_DAY,
};
pub use difficulty::{
    add_work, block_work, le256_lt, next_target, target_leading_zero_bits, work_gt,
};
pub use emission::{
    block_reward, format_noid, max_coinbase_value, max_coinbase_value_from_claimable_fee_sum,
    total_fees,
};
pub use epoch_anchor::{
    checked_tx_epoch_height_decomposition, next_tx_epoch_anchor_id, resolve_user_epoch_anchor_id,
    tx_epoch_anchor_height_for_child, validate_block_epoch_anchors, TxEpochHeightDecomposition,
};
pub use fees::{
    burned_fee_for_tx_body, claimable_fee_for_tx_body, fee_breakdown, fee_breakdown_for_tx_body,
    occupancy_bps, pressure_multiplier, required_fee_for_tx_body, state_growth_fee_per_slot,
    tx_live_counts, FeeBreakdown,
};
pub use fork_choice::{choose_chain_by_work, reorg_allowed, ChainChoice};
pub use genesis::{find_genesis_nonce, genesis_header, genesis_state_root, GENESIS_TIMESTAMP};
pub use header::{asert_anchor_height, is_final, validate_header};
pub use network::{NetworkConfig, NetworkKind};
pub use ordering::order_block_txs;
pub use paged_spend::{
    validate_paged_spend_transaction_stream, validate_paged_spend_transaction_stream_for_class,
    validate_paged_spend_tx_page_stream, validate_paged_spend_tx_page_stream_for_class,
    BlockProofClass, PagedSpendGroupFacts, PagedSpendStreamError, PagedSpendStreamFacts,
    BLOCK_PROOF_CLASS_TIERS,
};
pub use params::*;
pub use pow::{
    block_id, poseidon_pow_digest, pow_header_fields, search_pow, validate_pow, BlockHash,
};
pub use receipt::{
    generate_receipt, tx_root, verify_against_header, verify_merkle_inclusion, ParanoidReceipt,
    ReceiptVerifyResult, TxSummary,
};
pub use reorg::ReorgResult;
pub use slot_expansion::{expected_child_log_slots, finalized_expansion_window};
pub use template::{build_block_template, BlockTemplate, TemplateBuildError};
pub use timestamps::{
    median_time_past, median_u64, validate_future_drift, validate_median_time_past,
    validate_timestamp,
};
pub use validation::{
    validate_block_checks, validate_block_checks_timeless, validate_block_consensus,
    validate_block_resource_preflight, validate_mandatory_coinbase, AnchorInfo,
    BlockResourcePreflight,
};

/// Consensus validation errors — one variant per block invariant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConsensusError {
    /// §16.1 — PoW hash ≥ difficulty target.
    InvalidPoW,
    /// §16.2 — `prev_block_hash` does not match canonical parent.
    BadParentHash,
    /// §16.3 — `height != parent.height + 1`.
    BadHeight,
    /// §16.4 — `difficulty_target` differs from ASERT expectation.
    BadDifficultyTarget,
    /// §16.5 — Timestamp violates MTP or future-drift rules.
    BadTimestamp,
    /// §16.8 — Block contains more than `BLOCK_MAX_TXS` decoded transactions.
    TooManyTxs,
    /// §16.8b — Block exceeds a canonical shape or availability resource bound.
    BlockResourceLimitExceeded {
        limit: &'static str,
        actual: usize,
        max: usize,
    },
    /// §16.9 — `tx_root` does not match the computed Merkle root.
    BadTxRoot,
    /// §16.10 — Two transactions claim the same input or output slot.
    SlotConflict,
    /// User records do not form canonical complete PagedSpend groups.
    InvalidPagedSpend(String),
    /// §16.11 — user `epoch_anchor` differs from the one current epoch id.
    BadEpochAnchor,
    /// §16.14 — LogicProof verification failed.
    InvalidLogicProof { tx_index: usize },
    /// Every non-genesis block must carry its canonical coinbase at index zero.
    MissingCoinbase,
    /// A block carries more than one transaction marked as coinbase.
    MultipleCoinbase,
    /// The unique coinbase is present but is not transaction zero.
    CoinbaseNotFirst,
    /// The unique live coinbase output must pay `header.miner_address`.
    BadCoinbaseOwner,
    /// §16.15 — Coinbase value exceeds `block_reward + sum(fees)`.
    InflatedCoinbase,
    /// Coinbase `epoch_anchor` must equal the parent block hash.
    BadCoinbaseAnchor,
    /// A scheduled development payout record is missing.
    MissingDevelopmentPayout,
    /// A development payout record appears outside its scheduled height.
    UnexpectedDevelopmentPayout,
    /// The mandatory development payout has a wrong anchor, owner, or amount.
    BadDevelopmentPayout,
    /// The block's mandatory current-height history terminal is missing, does
    /// not natively verify, or does not bind the exact candidate header.
    /// Nodes without the pinned verifier artifacts fail closed here.
    BadHistoryStepTerminal(String),
    /// P.16 — transaction fee is below the deterministic minimum fee.
    BelowMinFee { required: u64, actual: u64 },
    /// §15.3.6 — `log_slots` must expand exactly when occupancy ≥ 75 %,
    /// and must not expand when occupancy < 75 %.
    BadLogSlotsExpansion,
    /// §16.16 — `state_root` does not match post-block state.
    BadStateRoot,
    /// Generic shape / length mismatch.
    ShapeMismatch(String),
}

impl std::fmt::Display for ConsensusError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidLogicProof { tx_index } => {
                write!(f, "InvalidLogicProof at tx_index={tx_index}")
            }
            Self::BadLogSlotsExpansion => write!(f, "BadLogSlotsExpansion"),
            Self::ShapeMismatch(msg) => write!(f, "ShapeMismatch: {msg}"),
            Self::InvalidPagedSpend(msg) => write!(f, "InvalidPagedSpend: {msg}"),
            Self::BelowMinFee { required, actual } => {
                write!(f, "BelowMinFee: required={required} actual={actual}")
            }
            other => write!(f, "{other:?}"),
        }
    }
}

impl std::error::Error for ConsensusError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn consensus_error_display() {
        let e = ConsensusError::InvalidLogicProof { tx_index: 3 };
        assert!(e.to_string().contains("3"));
        let e2 = ConsensusError::InvalidPoW;
        assert!(e2.to_string().contains("InvalidPoW"));
    }
}
