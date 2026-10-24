// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Typed topology of the canonical 31-slot Tx8x2 body spine.

use crate::tx_body_layout::{
    build_instance_layout, InstanceMeta, InstanceRole, N_SPINE_SLOTS, TXBODY_N_TREE_LEAVES,
};
use noid_core::Block128;
use noid_poseidon2b::native::domain::{capacity_iv, TAG_COMPRESS, TAG_TX8X2};

#[derive(Debug, Clone, Copy)]
pub struct SlotDescriptor {
    pub id: usize,
    pub role: InstanceRole,
    pub capacity_iv: [Block128; 2],
    pub is_head: bool,
    /// Present only on a compress-B slot; points to that node's compress-A.
    pub prev_output_src: Option<usize>,
    /// `None` at level one means the raw left leaf is statement-provided.
    pub left_child: Option<usize>,
    /// `None` at level one means the raw right leaf is statement-provided.
    pub right_child: Option<usize>,
}

/// The exact raw L0..L15 body-hash statement.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SpineInputs {
    pub leaves: [[Block128; 2]; TXBODY_N_TREE_LEAVES],
}

#[derive(Debug, Clone)]
pub struct SpineCircuit {
    pub slots: Vec<SlotDescriptor>,
    pub layout: Vec<InstanceMeta>,
}

impl SpineCircuit {
    pub fn build() -> Self {
        let layout = build_instance_layout();
        debug_assert_eq!(layout.len(), N_SPINE_SLOTS);
        let iv_compress = capacity_iv(TAG_COMPRESS);
        let iv_tx8x2 = capacity_iv(TAG_TX8X2);
        let slots = layout
            .iter()
            .enumerate()
            .map(|(id, meta)| {
                let capacity_iv = match meta.role {
                    InstanceRole::CompressPermA { .. } | InstanceRole::CompressPermB { .. } => {
                        iv_compress
                    }
                    InstanceRole::WrapPerm => iv_tx8x2,
                };
                let [left_child, right_child] = meta.children.unwrap_or([None, None]);
                SlotDescriptor {
                    id,
                    role: meta.role,
                    capacity_iv,
                    is_head: meta.is_head,
                    prev_output_src: (!meta.is_head).then(|| id - 1),
                    left_child,
                    right_child,
                }
            })
            .collect();
        Self { slots, layout }
    }

    #[inline]
    pub fn wrap_id(&self) -> usize {
        N_SPINE_SLOTS - 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_has_exact_31_slot_geometry() {
        let circuit = SpineCircuit::build();
        assert_eq!(circuit.slots.len(), 31);
        assert_eq!(circuit.wrap_id(), 30);
        assert!(matches!(circuit.slots[30].role, InstanceRole::WrapPerm));
        assert_eq!(circuit.slots[30].capacity_iv, capacity_iv(TAG_TX8X2));
    }

    #[test]
    fn only_compress_b_chains_from_previous_slot() {
        let circuit = SpineCircuit::build();
        for slot in &circuit.slots {
            match slot.role {
                InstanceRole::CompressPermB { .. } => {
                    assert_eq!(slot.prev_output_src, Some(slot.id - 1));
                }
                _ => assert!(slot.prev_output_src.is_none()),
            }
        }
    }
}
