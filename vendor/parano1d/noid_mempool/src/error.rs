// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Error types for the async mempool.

use noid_chain::consensus::ConsensusError;
use noid_poseidon2b::primitives::TxBodyHash;
use thiserror::Error;

/// Error returned by [`AsyncMempool::submit`].
#[derive(Debug, Error)]
pub enum SubmitError {
    /// Transaction already in the pool (idempotent — not a hard error).
    #[error("already admitted: {0:?}")]
    AlreadyAdmitted(TxBodyHash),

    /// Native consensus check failed (fee, anchor, slot).
    #[error("consensus: {0}")]
    Consensus(#[from] ConsensusError),

    /// Pool is at capacity.
    #[error("mempool full (capacity {capacity})")]
    Full { capacity: usize },

    /// Pool serialized PagedSpendIntent byte cap would be exceeded.
    #[error("mempool byte cap exceeded: {actual} bytes (max {max})")]
    BytesFull { actual: usize, max: usize },

    /// Malformed PagedSpendIntent wire format.
    #[error("malformed intent: {0}")]
    MalformedIntent(String),

    /// Serialized PagedSpendIntent bytes exceed the wire/admission cap.
    #[error("tx intent too large: {actual} bytes (max {max})")]
    IntentTooLarge { actual: usize, max: usize },

    /// The node must know the authenticated bank before admitting v2 traffic.
    #[error("v2 transaction limits are unavailable")]
    V2LimitsUnavailable,

    /// The spend exceeds every class compatible with its other resources.
    #[error("transaction has {actual} inputs; the active block limit is {max_inputs}")]
    InputLimitExceeded { actual: usize, max_inputs: usize },

    /// No one class can accommodate the complete indivisible spend.
    #[error(
        "no active proof class fits {pages} pages, {inputs} inputs and {calls} contract calls"
    )]
    NoProofClass {
        pages: usize,
        inputs: usize,
        calls: usize,
    },

    /// Non-coinbase transactions must carry a wallet authorization.
    #[error("missing auth authorization for non-coinbase transaction")]
    MissingProof,

    /// Logic proof bytes exceed the mempool wire/admission cap.
    #[error("auth authorization too large: {actual} bytes (max {max})")]
    ProofTooLarge { actual: usize, max: usize },

    /// Selected-ZK authorization verification failed.
    #[error("invalid auth authorization: {0}")]
    InvalidProof(String),

    /// Internal error (lock poisoned, channel closed, etc).
    #[error("internal: {0}")]
    Internal(String),
}

impl SubmitError {
    /// Returns `true` if this error is a soft rejection (no evidence of malice).
    /// Soft rejections can be retried after the on-chain state changes.
    pub fn is_soft(&self) -> bool {
        matches!(
            self,
            SubmitError::AlreadyAdmitted(_)
                | SubmitError::Full { .. }
                | SubmitError::BytesFull { .. }
                | SubmitError::V2LimitsUnavailable
                | SubmitError::InputLimitExceeded { .. }
                | SubmitError::NoProofClass { .. }
                | SubmitError::Consensus(ConsensusError::SlotConflict)
        )
    }
}
