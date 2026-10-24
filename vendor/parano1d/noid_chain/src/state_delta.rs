// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical native model for the exact block state-transition surface.
//!
//! This module formalizes the ordered touched-slot relation used to build the
//! exact authenticated state transition proof:
//!
//! ```text
//! read(slot) = pre_state(slot)
//!
//! spend: require read(slot) == claimed input; write(slot) = EMPTY
//! mint:  require read(slot) == EMPTY;         write(slot) = claimed output
//! ```
//!
//! A block-wide guarded set requires every live action to name a distinct slot;
//! there is no same-block spend/mint chaining in either direction. The returned
//! witness is a compact ordered delta surface, not full segment columns.

use std::collections::{BTreeMap, HashMap, HashSet};

use noid_poseidon2b::primitives::Digest;
use noid_tx::{Transaction, TxBody, TxInput, TxOutput};

use crate::fri_state::{SlotValue, StateRoot};
use crate::segmented_state::SegmentedFriState;

/// Direction of one touched-slot update in the ordered state-delta surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StateDeltaActionKind {
    /// A valid input consumes an existing UTXO: `pre != EMPTY`, `post = EMPTY`.
    Spend,
    /// A valid output creates a UTXO in an empty slot: `pre = EMPTY`, `post != EMPTY`.
    Mint,
}

/// One ordered touched-slot transition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StateDeltaAction {
    /// Transaction index in the block-order body slice.
    pub tx_index: u32,
    /// Input/output index inside the transaction body.
    pub op_index: u8,
    /// Global state slot index.
    pub slot_index: u32,
    /// Prefix-read value before this action.
    pub pre: SlotValue,
    /// Value written by this action.
    pub post: SlotValue,
    pub kind: StateDeltaActionKind,
}

/// Ordered touched-slot action surface without root recomputation.
///
/// This is the canonical lightweight surface used by proof adapters.  It checks
/// the same prefix-overlay semantics as [`StateDeltaWitness`] but does not
/// mutate state and does not compute the post root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateDeltaActionSurface {
    /// Ordered touched-slot updates: inputs first, then outputs for each tx.
    pub actions: Vec<StateDeltaAction>,
    /// Number of spend actions. Future header-counter checks can derive
    /// `active_slot_count' = active_slot_count - spends + mints` from these.
    pub spends: u32,
    /// Number of mint actions. Future header-counter checks can derive
    /// `alloc_counter' = alloc_counter + mints` from this.
    pub mints: u32,
}

impl StateDeltaActionSurface {
    /// Net change in live UTXO count induced by this delta.
    #[inline]
    pub fn active_slot_delta(&self) -> i64 {
        self.mints as i64 - self.spends as i64
    }
}

/// Canonical exact-state action surface derived from the ordered prefix overlay.
///
/// `touched_indices`, `old_slots` and `new_slots` are index-aligned and sorted
/// by slot index. `actions` remains in canonical tx/op order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactActionSurface {
    pub actions: Vec<StateDeltaAction>,
    pub touched_indices: Vec<u32>,
    pub old_slots: Vec<SlotValue>,
    pub new_slots: Vec<SlotValue>,
    pub spends: u32,
    pub mints: u32,
}

/// Native state-delta witness for a block body sequence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateDeltaWitness {
    /// Root before applying any action in this witness.
    pub prev_state_root: StateRoot,
    /// Root after applying all actions in order.
    pub post_state_root: StateRoot,
    /// Ordered touched-slot updates: inputs first, then outputs for each tx.
    pub actions: Vec<StateDeltaAction>,
    /// Number of spend actions. Future header-counter checks can derive
    /// `active_slot_count' = active_slot_count - spends + mints` from these.
    pub spends: u32,
    /// Number of mint actions. Future header-counter checks can derive
    /// `alloc_counter' = alloc_counter + mints` from this.
    pub mints: u32,
}

impl StateDeltaWitness {
    /// Net change in live UTXO count induced by this delta.
    #[inline]
    pub fn active_slot_delta(&self) -> i64 {
        self.mints as i64 - self.spends as i64
    }
}

/// Errors during native state-delta witness construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StateDeltaError {
    /// A valid input slot does not match the tx body's claimed `(value, owner)`.
    InputMismatch { tx_index: usize, input_index: usize },
    /// A valid output slot is not empty in the prefix state.
    OutputSlotOccupied {
        tx_index: usize,
        output_index: usize,
    },
    /// The tx body's slot claims do not match the expected public commitment.
    ClaimsCommitmentMismatch { tx_index: usize },
    /// One tx tries to spend the same slot more than once.
    DuplicateInputSlot { tx_index: usize },
    /// One tx tries to mint two outputs into the same slot.
    DuplicateOutputSlot { tx_index: usize },
    /// One tx tries to spend and mint the same slot in the same body.
    InputOutputSlotOverlap { tx_index: usize },
    /// A physical slot appears in more than one live action anywhere in the
    /// block. This includes spend-to-mint reuse across transaction boundaries.
    BlockSlotConflict { tx_index: usize, op_index: usize },
    /// A valid input/output references a slot outside the current state domain.
    SlotOutOfRange { tx_index: usize },
    /// The requested exact surface domain is neither the parent depth nor its
    /// single permitted expansion.
    InvalidSlotDomain,
    /// Assigning the next live output's creation ID would overflow the
    /// consensus allocation counter.
    AllocationCounterOverflow {
        tx_index: usize,
        output_index: usize,
    },
    /// The compact action counters cannot represent the supplied body list.
    ActionCountOverflow,
}

/// Build the canonical ordered state-delta action surface without mutating state
/// or recomputing roots.
///
/// This is the cheap verifier/proof-adapter view. It enforces the same
/// prefix-overlay relation as [`build_state_delta_witness`]: earlier writes in
/// the block are visible to later transactions, future writes are not, and
/// inputs are processed before outputs inside one transaction.
pub fn build_state_delta_action_surface(
    state: &SegmentedFriState,
    bodies: &[TxBody],
    expected_commitments: &[Digest],
    parent_alloc_counter: u64,
    block_height: u64,
) -> Result<StateDeltaActionSurface, StateDeltaError> {
    assert_eq!(
        bodies.len(),
        expected_commitments.len(),
        "one claims commitment per tx body required"
    );
    build_state_delta_action_surface_in_domain(
        state,
        state.num_slots(),
        bodies.len(),
        |tx_index| &bodies[tx_index],
        |tx_index| Some(expected_commitments[tx_index]),
        parent_alloc_counter,
        block_height,
    )
}

fn build_state_delta_action_surface_in_domain<'a>(
    state: &SegmentedFriState,
    slot_domain: u64,
    body_count: usize,
    mut body_at: impl FnMut(usize) -> &'a TxBody,
    mut expected_commitment_at: impl FnMut(usize) -> Option<Digest>,
    parent_alloc_counter: u64,
    block_height: u64,
) -> Result<StateDeltaActionSurface, StateDeltaError> {
    let parent_slot_domain = state.num_slots();
    if slot_domain < parent_slot_domain {
        return Err(StateDeltaError::InvalidSlotDomain);
    }
    let mut overlay: HashMap<u32, SlotValue> = HashMap::new();
    let mut actions = Vec::new();
    let mut spends = 0u32;
    let mut mints = 0u32;
    let mut alloc_counter = parent_alloc_counter;
    let mut block_touched = HashSet::new();

    for tx_idx in 0..body_count {
        let body = body_at(tx_idx);
        check_tx_slot_shape(body, tx_idx)?;

        if let Some(expected_commitment) = expected_commitment_at(tx_idx) {
            if body.claims_commitment() != expected_commitment {
                return Err(StateDeltaError::ClaimsCommitmentMismatch { tx_index: tx_idx });
            }
        }

        for (i, input) in body.live_inputs() {
            if (input.slot_index as u64) >= slot_domain {
                return Err(StateDeltaError::SlotOutOfRange { tx_index: tx_idx });
            }
            if !block_touched.insert(input.slot_index) {
                return Err(StateDeltaError::BlockSlotConflict {
                    tx_index: tx_idx,
                    op_index: i,
                });
            }

            let pre = overlay.get(&input.slot_index).copied().unwrap_or_else(|| {
                if u64::from(input.slot_index) < parent_slot_domain {
                    state.slot(input.slot_index)
                } else {
                    SlotValue::EMPTY
                }
            });
            let post = SlotValue::EMPTY;
            if pre != slot_value_from_input(input, &body.input_owner) {
                return Err(StateDeltaError::InputMismatch {
                    tx_index: tx_idx,
                    input_index: i,
                });
            }

            actions.push(StateDeltaAction {
                tx_index: tx_idx as u32,
                op_index: i as u8,
                slot_index: input.slot_index,
                pre,
                post,
                kind: StateDeltaActionKind::Spend,
            });
            overlay.insert(input.slot_index, post);
            spends = spends
                .checked_add(1)
                .ok_or(StateDeltaError::ActionCountOverflow)?;
        }

        for (j, output) in body.live_outputs() {
            if (output.slot_index as u64) >= slot_domain {
                return Err(StateDeltaError::SlotOutOfRange { tx_index: tx_idx });
            }
            if !block_touched.insert(output.slot_index) {
                return Err(StateDeltaError::BlockSlotConflict {
                    tx_index: tx_idx,
                    op_index: j,
                });
            }

            let pre = overlay.get(&output.slot_index).copied().unwrap_or_else(|| {
                if u64::from(output.slot_index) < parent_slot_domain {
                    state.slot(output.slot_index)
                } else {
                    SlotValue::EMPTY
                }
            });
            if pre != SlotValue::EMPTY {
                return Err(StateDeltaError::OutputSlotOccupied {
                    tx_index: tx_idx,
                    output_index: j,
                });
            }
            // Every mint consumes one allocator increment; the coinbase's
            // unique live output stores the tagged height id instead of the
            // allocator id (height-tagged coinbase identity).
            let next_alloc =
                alloc_counter
                    .checked_add(1)
                    .ok_or(StateDeltaError::AllocationCounterOverflow {
                        tx_index: tx_idx,
                        output_index: j,
                    })?;
            // Normal mints must never enter the tagged coinbase namespace.
            if crate::consensus::params::is_coinbase_creation_id(next_alloc) {
                return Err(StateDeltaError::AllocationCounterOverflow {
                    tx_index: tx_idx,
                    output_index: j,
                });
            }
            let creation_id = if body.is_primary_coinbase_shape() {
                crate::consensus::params::coinbase_creation_id(block_height)
            } else {
                next_alloc
            };
            let post = slot_value_from_output(output, creation_id);

            actions.push(StateDeltaAction {
                tx_index: tx_idx as u32,
                op_index: j as u8,
                slot_index: output.slot_index,
                pre,
                post,
                kind: StateDeltaActionKind::Mint,
            });
            overlay.insert(output.slot_index, post);
            mints = mints
                .checked_add(1)
                .ok_or(StateDeltaError::ActionCountOverflow)?;
            alloc_counter = next_alloc;
        }
    }

    Ok(StateDeltaActionSurface {
        actions,
        spends,
        mints,
    })
}

/// Build the exact-state surface that a Merkle frontier verifier consumes.
pub fn build_exact_action_surface(
    state: &SegmentedFriState,
    bodies: &[TxBody],
    expected_commitments: &[Digest],
    parent_alloc_counter: u64,
    block_height: u64,
) -> Result<ExactActionSurface, StateDeltaError> {
    let surface = build_state_delta_action_surface(
        state,
        bodies,
        expected_commitments,
        parent_alloc_counter,
        block_height,
    )?;
    Ok(exact_action_surface_from_surface(surface))
}

/// Build the exact surface at the current depth or its one-level expansion
/// without cloning or expanding the resident segment payloads.
///
/// Slots in the newly introduced upper half are canonical virtual zero. They
/// may therefore receive outputs, while an input there deterministically fails
/// its claimed pre-image check. This is the native exact-state expansion seam;
/// it creates no FRI matrix/tree authority.
pub fn build_exact_action_surface_at_log_slots(
    state: &SegmentedFriState,
    target_log_slots: u32,
    bodies: &[TxBody],
    expected_commitments: &[Digest],
    parent_alloc_counter: u64,
    block_height: u64,
) -> Result<ExactActionSurface, StateDeltaError> {
    assert_eq!(
        bodies.len(),
        expected_commitments.len(),
        "one claims commitment per tx body required"
    );
    build_exact_action_surface_at_log_slots_from_source(
        state,
        target_log_slots,
        bodies.len(),
        |tx_index| &bodies[tx_index],
        |tx_index| Some(expected_commitments[tx_index]),
        parent_alloc_counter,
        block_height,
    )
}

/// Build the exact block surface directly from the resident transaction
/// vector. Bodies and their commitments are borrowed/derived in place, so the
/// verifier does not allocate a second block-sized `Vec<TxBody>`.
pub fn build_exact_action_surface_for_transactions_at_log_slots(
    state: &SegmentedFriState,
    target_log_slots: u32,
    transactions: &[Transaction],
    parent_alloc_counter: u64,
    block_height: u64,
) -> Result<ExactActionSurface, StateDeltaError> {
    build_exact_action_surface_at_log_slots_from_source(
        state,
        target_log_slots,
        transactions.len(),
        |tx_index| &transactions[tx_index].body,
        |_| None,
        parent_alloc_counter,
        block_height,
    )
}

fn build_exact_action_surface_at_log_slots_from_source<'a>(
    state: &SegmentedFriState,
    target_log_slots: u32,
    body_count: usize,
    body_at: impl FnMut(usize) -> &'a TxBody,
    expected_commitment_at: impl FnMut(usize) -> Option<Digest>,
    parent_alloc_counter: u64,
    block_height: u64,
) -> Result<ExactActionSurface, StateDeltaError> {
    let current = state.log_slots();
    let target =
        usize::try_from(target_log_slots).map_err(|_| StateDeltaError::InvalidSlotDomain)?;
    if target != current && target != current.saturating_add(1) {
        return Err(StateDeltaError::InvalidSlotDomain);
    }
    let slot_domain = 1u64
        .checked_shl(target_log_slots)
        .ok_or(StateDeltaError::InvalidSlotDomain)?;
    let surface = build_state_delta_action_surface_in_domain(
        state,
        slot_domain,
        body_count,
        body_at,
        expected_commitment_at,
        parent_alloc_counter,
        block_height,
    )?;
    Ok(exact_action_surface_from_surface(surface))
}

/// Convert the ordered action surface into sorted old/new leaves.
pub fn exact_action_surface_from_surface(surface: StateDeltaActionSurface) -> ExactActionSurface {
    let mut touched: BTreeMap<u32, (SlotValue, SlotValue)> = BTreeMap::new();

    for action in &surface.actions {
        touched
            .entry(action.slot_index)
            .and_modify(|(_, new_slot)| *new_slot = action.post)
            .or_insert((action.pre, action.post));
    }

    let mut touched_indices = Vec::with_capacity(touched.len());
    let mut old_slots = Vec::with_capacity(touched.len());
    let mut new_slots = Vec::with_capacity(touched.len());
    for (idx, (old, new)) in touched {
        touched_indices.push(idx);
        old_slots.push(old);
        new_slots.push(new);
    }

    ExactActionSurface {
        actions: surface.actions,
        touched_indices,
        old_slots,
        new_slots,
        spends: surface.spends,
        mints: surface.mints,
    }
}

/// Build a compact ordered state-delta witness and apply it to `state` on success.
///
/// On `Err`, the input state is left untouched. This mirrors the atomic behavior
/// required from consensus validation and gives the proof system a single
/// canonical native relation.
pub fn build_state_delta_witness(
    state: &mut SegmentedFriState,
    bodies: &[TxBody],
    expected_commitments: &[Digest],
    parent_alloc_counter: u64,
    block_height: u64,
) -> Result<StateDeltaWitness, StateDeltaError> {
    let mut snap = state.clone();
    let prev_state_root = snap.root();
    let surface = build_state_delta_action_surface(
        &snap,
        bodies,
        expected_commitments,
        parent_alloc_counter,
        block_height,
    )?;

    let deltas: Vec<_> = surface
        .actions
        .iter()
        .map(|action| (action.slot_index, action.post))
        .collect();
    snap.apply_delta(&deltas)
        .expect("state-delta action surface bounds checked every slot");
    let post_state_root = snap.root();
    *state = snap;

    Ok(StateDeltaWitness {
        prev_state_root,
        post_state_root,
        actions: surface.actions,
        spends: surface.spends,
        mints: surface.mints,
    })
}

fn check_tx_slot_shape(body: &TxBody, tx_idx: usize) -> Result<(), StateDeltaError> {
    let mut seen_inputs = HashSet::new();
    let mut seen_outputs = HashSet::new();

    for (_, input) in body.live_inputs() {
        if !seen_inputs.insert(input.slot_index) {
            return Err(StateDeltaError::DuplicateInputSlot { tx_index: tx_idx });
        }
    }

    for (_, output) in body.live_outputs() {
        if !seen_outputs.insert(output.slot_index) {
            return Err(StateDeltaError::DuplicateOutputSlot { tx_index: tx_idx });
        }
        if seen_inputs.contains(&output.slot_index) {
            return Err(StateDeltaError::InputOutputSlotOverlap { tx_index: tx_idx });
        }
    }

    Ok(())
}

#[inline]
fn slot_value_from_input(
    input: &TxInput,
    owner: &noid_poseidon2b::primitives::Address,
) -> SlotValue {
    SlotValue::with_owner_fields(input.amount, input.creation_id, owner.as_fields())
}

#[inline]
fn slot_value_from_output(output: &TxOutput, creation_id: u64) -> SlotValue {
    SlotValue::with_owner_fields(output.amount, creation_id, output.owner.as_fields())
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::primitives::Address;
    use noid_tx::{output_bitmap_bit, TxBody, TxInput, TxOutput, TX_INPUTS, TX_OUTPUTS};

    fn body(input_slot: u32, output_slot: u32, owner: Address) -> TxBody {
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        inputs[0] = TxInput {
            slot_index: input_slot,
            amount: 11,
            creation_id: 1,
        };
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: output_slot,
            amount: 10,
            owner: Address([2u8; 32]),
        };
        TxBody {
            epoch_anchor: [3u8; 32],
            fee: 1,
            input_owner: owner,
            inputs,
            outputs,
            validity_bitmap: 1 | output_bitmap_bit(0),
            is_coinbase: false,
        }
    }

    fn coinbase_body(output_slot: u32) -> TxBody {
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: output_slot,
            amount: 10,
            owner: Address([7u8; 32]),
        };
        TxBody {
            epoch_anchor: [0u8; 32],
            fee: 0,
            input_owner: Address([0u8; 32]),
            inputs: [TxInput::dummy(); TX_INPUTS],
            outputs,
            validity_bitmap: output_bitmap_bit(0),
            is_coinbase: true,
        }
    }

    fn state() -> SegmentedFriState {
        let mut state = SegmentedFriState::new_empty(8);
        for slot in [1u32, 3, 5] {
            state
                .set_slot(
                    slot,
                    SlotValue::with_owner_fields(11, 1, Address([1u8; 32]).as_fields()),
                )
                .unwrap();
        }
        state
    }

    #[test]
    fn action_surface_uses_body_input_owner_and_exact_counts() {
        let body = body(1, 2, Address([1u8; 32]));
        let surface = build_state_delta_action_surface(
            &state(),
            std::slice::from_ref(&body),
            &[body.claims_commitment()],
            1,
            7,
        )
        .unwrap();
        assert_eq!(surface.spends, 1);
        assert_eq!(surface.mints, 1);
        assert_eq!(surface.actions.len(), 2);
        assert_eq!(surface.actions[0].slot_index, 1);
        assert_eq!(surface.actions[1].slot_index, 2);
    }

    #[test]
    fn every_cross_transaction_slot_reuse_rejects() {
        let first = body(1, 2, Address([1u8; 32]));
        for second in [
            body(1, 4, Address([1u8; 32])),
            body(3, 2, Address([1u8; 32])),
            body(2, 4, Address([1u8; 32])),
            body(3, 1, Address([1u8; 32])),
        ] {
            let commitments = [first.claims_commitment(), second.claims_commitment()];
            assert!(matches!(
                build_state_delta_action_surface(
                    &state(),
                    &[first.clone(), second],
                    &commitments,
                    1,
                    7,
                ),
                Err(StateDeltaError::BlockSlotConflict { .. })
            ));
        }
    }

    #[test]
    fn claims_and_owner_mismatch_fail_closed() {
        let body = body(1, 2, Address([9u8; 32]));
        assert!(matches!(
            build_state_delta_action_surface(
                &state(),
                std::slice::from_ref(&body),
                &[body.claims_commitment()],
                1,
                7,
            ),
            Err(StateDeltaError::InputMismatch { .. })
        ));
        assert!(matches!(
            build_state_delta_action_surface(&state(), &[body], &[[0u8; 32]], 1, 7),
            Err(StateDeltaError::ClaimsCommitmentMismatch { .. })
        ));
    }

    #[test]
    fn exact_expansion_reads_new_upper_half_as_virtual_zero_without_state_clone() {
        let state = state();
        let mint = coinbase_body(300);
        let surface = build_exact_action_surface_at_log_slots(
            &state,
            9,
            std::slice::from_ref(&mint),
            &[mint.claims_commitment()],
            3,
            7,
        )
        .unwrap();
        assert_eq!(surface.touched_indices, vec![300]);
        assert_eq!(surface.old_slots, vec![SlotValue::EMPTY]);
        assert_eq!(surface.mints, 1);

        let impossible_spend = body(300, 2, Address([1u8; 32]));
        assert!(matches!(
            build_exact_action_surface_at_log_slots(
                &state,
                9,
                std::slice::from_ref(&impossible_spend),
                &[impossible_spend.claims_commitment()],
                3,
                7,
            ),
            Err(StateDeltaError::InputMismatch { .. })
        ));
        assert!(matches!(
            build_exact_action_surface_at_log_slots(
                &state,
                10,
                std::slice::from_ref(&mint),
                &[mint.claims_commitment()],
                3,
                7,
            ),
            Err(StateDeltaError::InvalidSlotDomain)
        ));
    }
}
