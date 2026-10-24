// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Native reference oracle for the 31-permutation flattened Tx8x2 spine.

use noid_core::{Block128, CanonicalSerialize};
use noid_poseidon2b::native::permutation::Poseidon2bPermutation;

use crate::circuit::{SlotDescriptor, SpineCircuit, SpineInputs};
use crate::tx_body_layout::InstanceRole;

#[derive(Debug, Clone, Copy)]
pub struct SlotState {
    pub state_in: [Block128; 4],
    pub state_out: [Block128; 4],
}

impl SlotState {
    #[inline]
    pub fn digest(&self) -> [Block128; 2] {
        [self.state_out[0], self.state_out[1]]
    }
}

#[derive(Debug, Clone)]
pub struct SpineWitness {
    pub slots: Vec<SlotState>,
    pub tx_body_hash: [Block128; 2],
}

impl SpineWitness {
    pub fn tx_body_hash_bytes(&self) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[..16].copy_from_slice(&self.tx_body_hash[0].to_bytes());
        out[16..].copy_from_slice(&self.tx_body_hash[1].to_bytes());
        out
    }
}

pub fn evaluate_spine(circuit: &SpineCircuit, inputs: &SpineInputs) -> SpineWitness {
    let permutation = Poseidon2bPermutation;
    let mut slots = Vec::with_capacity(circuit.slots.len());
    for slot in &circuit.slots {
        let state_in = build_state_in(slot, inputs, &slots);
        let mut state_out = state_in;
        permutation.permute_mut(&mut state_out);
        slots.push(SlotState {
            state_in,
            state_out,
        });
    }
    let tx_body_hash = slots.last().expect("spine wrap exists").digest();
    SpineWitness {
        slots,
        tx_body_hash,
    }
}

fn build_state_in(
    slot: &SlotDescriptor,
    inputs: &SpineInputs,
    previous: &[SlotState],
) -> [Block128; 4] {
    let [iv_hi, iv_lo] = slot.capacity_iv;
    match slot.role {
        InstanceRole::CompressPermA { level, pos } => {
            let left = resolve_child(slot.left_child, previous, inputs, level, pos, false);
            [left[0], left[1], iv_hi, iv_lo]
        }
        InstanceRole::CompressPermB { level, pos } => {
            let right = resolve_child(slot.right_child, previous, inputs, level, pos, true);
            chain_absorb_pair(previous, slot, right)
        }
        InstanceRole::WrapPerm => {
            let root = previous[slot.left_child.expect("wrap references root")].digest();
            [root[0], root[1], iv_hi, iv_lo]
        }
    }
}

#[inline]
fn chain_absorb_pair(
    previous: &[SlotState],
    slot: &SlotDescriptor,
    absorb: [Block128; 2],
) -> [Block128; 4] {
    let state = previous[slot
        .prev_output_src
        .expect("compress-B chains from compress-A")]
    .state_out;
    [
        state[0] + absorb[0],
        state[1] + absorb[1],
        state[2],
        state[3],
    ]
}

fn resolve_child(
    child: Option<usize>,
    previous: &[SlotState],
    inputs: &SpineInputs,
    level: u8,
    pos: u8,
    right: bool,
) -> [Block128; 2] {
    if let Some(child) = child {
        return previous[child].digest();
    }
    assert_eq!(level, 1, "only level-one children are raw leaves");
    inputs.leaves[2 * pos as usize + usize::from(right)]
}

pub fn digest_to_fields(digest: &[u8; 32]) -> [Block128; 2] {
    [
        Block128::from(u128::from_le_bytes(digest[..16].try_into().unwrap())),
        Block128::from(u128::from_le_bytes(digest[16..].try_into().unwrap())),
    ]
}
