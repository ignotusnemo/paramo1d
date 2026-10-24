// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! RAM state backend .
//!
//! `RamBackend` is a thin `StateBackend` wrapper around `SegmentedFriState`.
//! Recommended for `log_slots ≤ 26` (≤ 3 GB peak usage). When
//! `log_slots > 26` the node must switch to the MDBX disk backend.

use crate::fri_state::{SlotValue, StateRoot};
use crate::segmented_state::{SegmentColumns, SegmentedFriState};
use crate::storage::StateBackend;

/// In-memory state backend backed by `SegmentedFriState`.
pub struct RamBackend {
    inner: SegmentedFriState,
}

impl RamBackend {
    pub fn new(log_slots: usize) -> Self {
        Self {
            inner: SegmentedFriState::new_empty(log_slots),
        }
    }

    /// Direct access to the underlying `SegmentedFriState`.
    pub fn inner(&self) -> &SegmentedFriState {
        &self.inner
    }

    /// Mutable access to the underlying `SegmentedFriState`.
    pub fn inner_mut(&mut self) -> &mut SegmentedFriState {
        &mut self.inner
    }
}

impl StateBackend for RamBackend {
    fn get_slot(&self, seg_id: u16, local_idx: u16) -> SlotValue {
        let eff = self.inner.effective_log_segment_size();
        let global_idx = ((seg_id as u32) << eff) | (local_idx as u32);
        self.inner.slot(global_idx)
    }

    fn set_slot(&mut self, seg_id: u16, local_idx: u16, v: SlotValue) {
        let eff = self.inner.effective_log_segment_size();
        let global_idx = ((seg_id as u32) << eff) | (local_idx as u32);
        self.inner
            .set_slot(global_idx, v)
            .expect("slot out of range in RamBackend::set_slot");
    }

    fn load_segment_columns(&mut self, seg_id: u16) -> &SegmentColumns {
        self.inner.segment_columns(seg_id)
    }

    fn flush(&mut self) {
        // No-op: RAM backend is always in sync.
    }

    fn state_root(&mut self) -> StateRoot {
        self.inner.root()
    }
}
