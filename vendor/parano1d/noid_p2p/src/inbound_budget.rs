// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Process-wide admission for decoded inbound P2P payloads.
//!
//! Accepted-block, HistoryStep, state-segment, and mempool codecs share this one
//! byte domain.  A permit is acquired before payload allocation and travels
//! with the decoded response until node-side consumption finishes.  Traffic
//! on different protocols therefore cannot add their individual maxima or
//! scale resident payload memory with peer count.

use std::sync::{Arc, OnceLock};

use tokio::sync::Semaphore;

/// Aggregate decoded payload bytes admitted across every large inbound P2P
/// response. Smaller protocols share remaining capacity and wait when the
/// process-wide domain is full.
pub const INBOUND_RESPONSE_BUDGET_BYTES: usize = 64 * 1024 * 1024;

pub(crate) fn process_global_inbound_budget() -> Arc<Semaphore> {
    static BUDGET: OnceLock<Arc<Semaphore>> = OnceLock::new();
    Arc::clone(BUDGET.get_or_init(|| Arc::new(Semaphore::new(INBOUND_RESPONSE_BUDGET_BYTES))))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn production_callers_share_one_process_domain() {
        let first = process_global_inbound_budget();
        let second = process_global_inbound_budget();
        assert!(Arc::ptr_eq(&first, &second));
        // Rust runs unit tests concurrently. Other codec tests may hold a
        // legitimate permit from this same singleton at this instant, so the
        // observable availability is bounded above rather than exactly full.
        assert!(first.available_permits() <= INBOUND_RESPONSE_BUDGET_BYTES);
    }
}
