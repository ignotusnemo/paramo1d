// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Types and deterministic state helpers shared by the atomic MDBX reorg path.

use crate::consensus::da_prune::BlockUndoLog;
use crate::state::ChainState;
use noid_poseidon2b::primitives::TxBodyHash;

/// Result of a successful atomic accepted-bundle reorg.
#[derive(Debug, Clone)]
pub struct ReorgResult {
    /// Heights removed from the old canonical suffix.
    pub reverted_heights: Vec<u64>,
    /// Heights installed from fully verified replacement bundles.
    pub applied_heights: Vec<u64>,
    /// Transactions from removed blocks that may be reconsidered by mempool admission.
    pub reclaimed_tx_hashes: Vec<TxBodyHash>,
}

/// Restore counters captured before a reverted block.
///
/// Counter deltas cannot be inferred from final slot pre-images because a slot
/// may be minted and spent within the same block.
pub(crate) fn restore_state_counters(state: &mut ChainState, undo: &BlockUndoLog) {
    state.active_slot_count = undo.active_slot_count_before;
    state.alloc_counter = undo.alloc_counter_before;
}
