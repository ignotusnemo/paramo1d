// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Rebuildable, bounded hot-segment Merkle trees. These are local acceleration
//! data only: their hashes use the unchanged exact-state commitment functions.

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::exact_state_hash::{slot_leaf_hash, state_node_hash, zero_slot_roots, StateHash};
use crate::fri_state::SlotValue;
use crate::segmented_state::SegmentColumns;

/// Payload budget per state view, INCLUDING the raw columns retained with each
/// tree. At production geometry this holds nine 3 MiB column / 4 MiB tree pairs,
/// independently of the slot-domain size. Active block scratch is separate.
const DEFAULT_CACHE_BYTES: usize = 64 * 1024 * 1024;

#[derive(Debug, Clone)]
pub(crate) struct ExactSegmentTree {
    log_slots: usize,
    nodes: Vec<StateHash>,
    zeros: Vec<StateHash>,
    column_bytes: usize,
}

impl ExactSegmentTree {
    pub(crate) fn from_columns(log_slots: usize, columns: &SegmentColumns) -> Self {
        let size = 1usize << log_slots;
        assert_eq!(columns.values.len(), size);
        assert_eq!(columns.owners_hi.len(), size);
        assert_eq!(columns.owners_lo.len(), size);
        let zeros = zero_slot_roots(log_slots);
        let mut nodes = vec![zeros[0]; 2 * size];
        for local in 0..size {
            let slot = SlotValue {
                value: columns.values[local],
                owner_hi: columns.owners_hi[local],
                owner_lo: columns.owners_lo[local],
            };
            if !slot.is_empty() {
                nodes[size + local] = slot_leaf_hash(slot);
            }
        }
        for level in 1..=log_slots {
            let start = size >> level;
            for node in start..2 * start {
                let left = nodes[2 * node];
                let right = nodes[2 * node + 1];
                nodes[node] = if left == zeros[level - 1] && right == zeros[level - 1] {
                    zeros[level]
                } else {
                    state_node_hash(left, right)
                };
            }
        }
        Self {
            log_slots,
            nodes,
            zeros,
            column_bytes: (columns.values.capacity()
                + columns.owners_hi.capacity()
                + columns.owners_lo.capacity())
                * std::mem::size_of::<noid_core::Block128>(),
        }
    }

    pub(crate) fn root(&self) -> StateHash {
        self.nodes[1]
    }

    pub(crate) fn log_slots(&self) -> usize {
        self.log_slots
    }

    pub(crate) fn subtree_root(&self, level: u32, index: u64) -> Option<StateHash> {
        if level as usize > self.log_slots {
            return None;
        }
        let width = 1usize << (self.log_slots - level as usize);
        if index >= width as u64 {
            return None;
        }
        Some(self.nodes[width + index as usize])
    }

    fn set_slot(&mut self, local: usize, value: SlotValue) {
        let mut node = (1usize << self.log_slots) + local;
        let hash = if value.is_empty() {
            self.zeros[0]
        } else {
            slot_leaf_hash(value)
        };
        if self.nodes[node] == hash {
            return;
        }
        self.nodes[node] = hash;
        let mut level = 0;
        while node > 1 {
            node /= 2;
            let left = self.nodes[2 * node];
            let right = self.nodes[2 * node + 1];
            let hash = if left == self.zeros[level] && right == self.zeros[level] {
                self.zeros[level + 1]
            } else {
                state_node_hash(left, right)
            };
            if self.nodes[node] == hash {
                break;
            }
            self.nodes[node] = hash;
            level += 1;
        }
    }

    /// Read-only overlay: hash the union of changed paths without cloning the
    /// entire tree or altering the authenticated parent cache.
    pub(crate) fn root_with_updates(&self, updates: &BTreeMap<u32, SlotValue>) -> StateHash {
        let leaves: Vec<_> = updates
            .iter()
            .map(|(&local, &value)| {
                assert!((local as usize) < (1usize << self.log_slots));
                (
                    local as usize,
                    if value.is_empty() {
                        self.zeros[0]
                    } else {
                        slot_leaf_hash(value)
                    },
                )
            })
            .collect();
        self.overlay_root(1, 0, 1usize << self.log_slots, &leaves)
    }

    fn overlay_root(
        &self,
        node: usize,
        start: usize,
        width: usize,
        updates: &[(usize, StateHash)],
    ) -> StateHash {
        if updates.is_empty() {
            return self.nodes[node];
        }
        if width == 1 {
            return updates[0].1;
        }
        let half = width / 2;
        let split = updates.partition_point(|&(local, _)| local < start + half);
        let left = self.overlay_root(2 * node, start, half, &updates[..split]);
        let right = self.overlay_root(2 * node + 1, start + half, half, &updates[split..]);
        state_node_hash(left, right)
    }

    fn resident_bytes(&self) -> usize {
        (self.nodes.capacity() + self.zeros.capacity()) * std::mem::size_of::<StateHash>()
            + self.column_bytes
    }
}

/// A small LRU; production has at most nine entries, so a linear lookup avoids
/// a domain-sized map. Clones share immutable trees until a slot is written.
#[derive(Debug, Clone)]
pub(crate) struct ExactSegmentCache {
    entries: Vec<(u16, Arc<ExactSegmentTree>)>,
    bytes: usize,
    budget: usize,
}

impl Default for ExactSegmentCache {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
            bytes: 0,
            budget: DEFAULT_CACHE_BYTES,
        }
    }
}

impl ExactSegmentCache {
    pub(crate) fn get(&self, id: u16) -> Option<&ExactSegmentTree> {
        self.entries
            .iter()
            .find(|(key, _)| *key == id)
            .map(|(_, tree)| tree.as_ref())
    }

    pub(crate) fn remove(&mut self, id: u16) {
        if let Some(index) = self.entries.iter().position(|(key, _)| *key == id) {
            let (_, tree) = self.entries.remove(index);
            self.bytes -= tree.resident_bytes();
        }
    }

    pub(crate) fn insert(&mut self, id: u16, tree: ExactSegmentTree) {
        self.remove(id);
        let bytes = tree.resident_bytes();
        if bytes > self.budget {
            return;
        }
        while self.bytes + bytes > self.budget {
            let (_, oldest) = self.entries.remove(0);
            self.bytes -= oldest.resident_bytes();
        }
        self.entries.push((id, Arc::new(tree)));
        self.bytes += bytes;
    }

    pub(crate) fn update_slot(&mut self, id: u16, local: usize, value: SlotValue) {
        if let Some(index) = self.entries.iter().position(|(key, _)| *key == id) {
            let mut entry = self.entries.remove(index);
            Arc::make_mut(&mut entry.1).set_slot(local, value);
            self.entries.push(entry);
        }
    }

    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.bytes = 0;
    }

    pub(crate) fn truncate_segments(&mut self, count: usize) {
        self.entries.retain(|(id, _)| (*id as usize) < count);
        self.bytes = self
            .entries
            .iter()
            .map(|(_, tree)| tree.resident_bytes())
            .sum();
    }

    #[cfg(test)]
    pub(crate) fn with_budget(budget: usize) -> Self {
        Self {
            budget,
            ..Self::default()
        }
    }

    #[cfg(test)]
    pub(crate) fn bytes(&self) -> usize {
        self.bytes
    }
}
