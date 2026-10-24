// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Consensus metadata persisted atomically with canonical chain commits.

/// Hard-finalized canonical checkpoint.
///
/// This is intentionally non-optional: a valid database always has at least the
/// genesis checkpoint finalized.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FinalizedCheckpoint {
    pub height: u64,
    pub hash: [u8; 32],
}

/// Canonical consensus metadata for the current durable tip.
///
/// Must be written in the same MDBX transaction as the canonical header/state
/// update that it describes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConsensusMeta {
    pub tip_height: u64,
    pub tip_hash: [u8; 32],
    pub cumulative_chainwork: [u8; 32],
    pub finalized: FinalizedCheckpoint,
}
