// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Exact-state slot-leaf and EXSTNOD verification in the recursive trace.
//!
//! Root/depth binding is derived from the canonical sibling-only structural
//! frontier. C' still owns the compacted-action/slot-sort recombination
//! relation binding the canonical body actions to these packed leaves.

use noid_chain::exact_state_hash::{slot_leaf_hash, state_node_hash, zero_slot_roots, StateHash};
use noid_chain::sparse_merkle::{
    derive_structural_frontier_plan, evaluate_structural_frontier,
    expand_multiproof_segmented_updates, SegmentedSequentialMerkleUpdates,
    SequentialMerkleUpdatePath, SparseMerkleError, StructuralFrontierEvaluation,
    StructuralFrontierPlan, StructuralNodeRef, STRUCTURAL_FRONTIER_PAD,
};
use noid_chain::SlotValue;
use noid_core::Block128;
use noid_gkr::state_leaf_killshot::SlotLeafInputs;
use noid_ivc_core::deep_chain::leaf_hash::flat_sponge_leaf_hash;
use noid_ivc_core::field_circuit::Wire;
use noid_poseidon2b::native::domain::{capacity_iv, TAG_EXSTNOD};

use crate::acceptance::history_step::ExactStateStructuralFrontierInputs;

use super::action_surface::ActionRowTrace;
use super::paired_merkle_update::{
    PairedMerkleUpdateWitness, PAIRED_UPDATE_DEPTH, PAIRED_UPDATE_STRIDE,
};
use super::{
    alloc_block, const_block, flat_const, flat_of, mul, pin_eq, pin_zero, poseidon2b_permute,
    range_check_bits, FieldR1csBuilder, LinExpr, F128,
};

/// Verifier-owned topology and hashes materialized from the sibling-only
/// structural frontier carried by one HistoryStep block input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedExactStateStructuralFrontier {
    pub plan: StructuralFrontierPlan,
    pub old_evaluation: StructuralFrontierEvaluation,
    pub new_evaluation: StructuralFrontierEvaluation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExactStateStructuralFrontierError {
    SlotLeafCountMismatch {
        touched: usize,
        old: usize,
        new: usize,
    },
    OldSlotLeafMismatch {
        index: usize,
    },
    NewSlotLeafMismatch {
        index: usize,
    },
    CombineDigestCountMismatch {
        expected: usize,
        old: usize,
        new: usize,
    },
    OldCombineDigestMismatch {
        index: usize,
    },
    NewCombineDigestMismatch {
        index: usize,
    },
    OldRootMismatch,
    NewRootMismatch,
    SparseMerkle(SparseMerkleError),
}

impl From<SparseMerkleError> for ExactStateStructuralFrontierError {
    fn from(source: SparseMerkleError) -> Self {
        Self::SparseMerkle(source)
    }
}

fn fields_to_digest(fields: [Block128; 2]) -> StateHash {
    let mut digest = [0u8; 32];
    digest[..16].copy_from_slice(&fields[0].0.to_le_bytes());
    digest[16..].copy_from_slice(&fields[1].0.to_le_bytes());
    digest
}

fn validated_slot_leaf_hashes(
    inputs: &[SlotLeafInputs],
    mismatch: impl Fn(usize) -> ExactStateStructuralFrontierError,
) -> Result<Vec<StateHash>, ExactStateStructuralFrontierError> {
    inputs
        .iter()
        .enumerate()
        .map(|(index, input)| {
            let digest = slot_leaf_hash(SlotValue {
                value: input.packed_value,
                owner_hi: input.owner_hi,
                owner_lo: input.owner_lo,
            });
            if fields_to_digest(input.expected_leaf) != digest {
                return Err(mismatch(index));
            }
            Ok(digest)
        })
        .collect()
}

fn first_digest_mismatch(left: &[StateHash], right: &[StateHash]) -> Option<usize> {
    left.iter()
        .zip(right.iter())
        .position(|(left, right)| left != right)
}

/// Validate the exact sibling-only carrier and derive all Merkle topology on
/// the verifier side. No path direction or node coordinate is accepted from
/// the prover.
pub fn verify_exact_state_structural_frontier(
    inputs: &ExactStateStructuralFrontierInputs,
) -> Result<VerifiedExactStateStructuralFrontier, ExactStateStructuralFrontierError> {
    let touched = inputs.touched_indices.len();
    if inputs.old_slot_leaves.len() != touched || inputs.new_slot_leaves.len() != touched {
        return Err(ExactStateStructuralFrontierError::SlotLeafCountMismatch {
            touched,
            old: inputs.old_slot_leaves.len(),
            new: inputs.new_slot_leaves.len(),
        });
    }
    let plan = derive_structural_frontier_plan(&inputs.touched_indices, inputs.active_depth)?;
    let combines = plan.combines().len();
    if inputs.old_combine_digests.len() != combines || inputs.new_combine_digests.len() != combines
    {
        return Err(
            ExactStateStructuralFrontierError::CombineDigestCountMismatch {
                expected: combines,
                old: inputs.old_combine_digests.len(),
                new: inputs.new_combine_digests.len(),
            },
        );
    }
    let old_leaves = validated_slot_leaf_hashes(&inputs.old_slot_leaves, |index| {
        ExactStateStructuralFrontierError::OldSlotLeafMismatch { index }
    })?;
    let new_leaves = validated_slot_leaf_hashes(&inputs.new_slot_leaves, |index| {
        ExactStateStructuralFrontierError::NewSlotLeafMismatch { index }
    })?;
    let old_evaluation =
        evaluate_structural_frontier(&plan, &old_leaves, &inputs.live_sibling_digests)?;
    if let Some(index) =
        first_digest_mismatch(&inputs.old_combine_digests, &old_evaluation.combines)
    {
        return Err(ExactStateStructuralFrontierError::OldCombineDigestMismatch { index });
    }
    if old_evaluation.root != inputs.old_root {
        return Err(ExactStateStructuralFrontierError::OldRootMismatch);
    }
    let new_evaluation =
        evaluate_structural_frontier(&plan, &new_leaves, &inputs.live_sibling_digests)?;
    if let Some(index) =
        first_digest_mismatch(&inputs.new_combine_digests, &new_evaluation.combines)
    {
        return Err(ExactStateStructuralFrontierError::NewCombineDigestMismatch { index });
    }
    if new_evaluation.root != inputs.new_root {
        return Err(ExactStateStructuralFrontierError::NewRootMismatch);
    }
    Ok(VerifiedExactStateStructuralFrontier {
        plan,
        old_evaluation,
        new_evaluation,
    })
}

/// Deterministically project the same authenticated frontier into the local
/// and segment update paths consumed by the fixed-shape trace.
pub fn derive_exact_state_segmented_updates(
    inputs: &ExactStateStructuralFrontierInputs,
    log_segment_size: u32,
) -> Result<SegmentedSequentialMerkleUpdates, ExactStateStructuralFrontierError> {
    verify_exact_state_structural_frontier(inputs)?;
    let old_leaves = inputs
        .old_slot_leaves
        .iter()
        .map(|leaf| fields_to_digest(leaf.expected_leaf))
        .collect::<Vec<_>>();
    let new_leaves = inputs
        .new_slot_leaves
        .iter()
        .map(|leaf| fields_to_digest(leaf.expected_leaf))
        .collect::<Vec<_>>();
    Ok(expand_multiproof_segmented_updates(
        &inputs.touched_indices,
        &old_leaves,
        &new_leaves,
        &inputs.live_sibling_digests,
        inputs.active_depth,
        log_segment_size,
    )?)
}

pub struct SlotLeafInputsTrace {
    pub packed_value: LinExpr,
    pub owner_hi: LinExpr,
    pub owner_lo: LinExpr,
    pub expected_leaf: [LinExpr; 2],
}

impl SlotLeafInputsTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &SlotLeafInputs) -> Self {
        Self {
            packed_value: alloc_block(b, native.packed_value),
            owner_hi: alloc_block(b, native.owner_hi),
            owner_lo: alloc_block(b, native.owner_lo),
            expected_leaf: std::array::from_fn(|i| alloc_block(b, native.expected_leaf[i])),
        }
    }
}

/// Bind slot-sorted actions to the old/new exact-state leaf statements.
///
/// A spend authenticates the body's packed `(amount, creation_id)` and owner
/// in the old leaf and writes the canonical empty slot. A mint authenticates
/// an empty old leaf and writes the allocator-packed action value and owner.
/// The creation-id high half was built from the allocator's constrained bits
/// in body order before the shared action permutation, so slot sorting cannot
/// change allocator order. Mint amounts must already be proven u64 at their
/// body source (user public arithmetic, or the coinbase surface).
pub fn bind_actions_to_exact_state_leaves(
    b: &mut FieldR1csBuilder,
    actions: &[ActionRowTrace],
    old_leaves: &[SlotLeafInputsTrace],
    new_leaves: &[SlotLeafInputsTrace],
) {
    assert_eq!(actions.len(), old_leaves.len());
    assert_eq!(actions.len(), new_leaves.len());

    for ((action, old), new) in actions.iter().zip(old_leaves).zip(new_leaves) {
        // `is_mint <= live` and both are boolean from the action compactor.
        // In characteristic two this is the exact Spend selector.
        let is_spend = action.live.add(&action.is_mint);

        let old_value = mul(b, &is_spend, &action.value);
        pin_eq(b, &old.packed_value, &old_value);
        for lane in 0..2 {
            let old_owner = mul(b, &is_spend, &action.owner[lane]);
            pin_eq(
                b,
                if lane == 0 {
                    &old.owner_hi
                } else {
                    &old.owner_lo
                },
                &old_owner,
            );
        }

        // `action.value` is already the exact packed state value. Selecting
        // by role leaves spends unrestricted in the old leaf and mints in the
        // new leaf without re-decomposing either half after the permutation.
        let new_value = mul(b, &action.is_mint, &action.value);
        pin_eq(b, &new.packed_value, &new_value);
        for lane in 0..2 {
            let new_owner = mul(b, &action.is_mint, &action.owner[lane]);
            pin_eq(
                b,
                if lane == 0 {
                    &new.owner_hi
                } else {
                    &new.owner_lo
                },
                &new_owner,
            );
        }
    }
}

/// One index-aligned old/new leaf pair prepared for the future structural
/// region binding.
pub struct StructuralTouchedLeafPreparation {
    pub slot_index: LinExpr,
    pub old: SlotLeafInputsTrace,
    pub new: SlotLeafInputsTrace,
}

/// One ordered EXSTNOD statement prepared for a structural combine row.
///
/// These are independent witness wires for now. The future region cut must
/// bind `left`/`right` to the verifier-plan sources and `parent` to both the
/// hash output and every downstream reference.
pub struct StructuralCombineTuplePreparation {
    pub left: [LinExpr; 2],
    pub right: [LinExpr; 2],
    pub parent: [LinExpr; 2],
    pub is_live: bool,
}

/// Preparation-only structural exact-state carrier.
///
/// Native validation derives `plan`; allocation then materializes aligned
/// leaves, one shared live sibling frontier, and fixed-capacity old/new
/// combine tuples. This object is **not** a proved topology relation yet.
/// Callers must not treat it as sound exact-state verification until region
/// constraints bind every plan edge, the common sibling rows, roots, and PAD.
pub struct ExactStateStructuralRegionPreparation {
    pub plan: StructuralFrontierPlan,
    pub touched_leaves: Vec<StructuralTouchedLeafPreparation>,
    /// Fixed preparation width. `[..live_sibling_count]` is the real shared
    /// frontier; the suffix is canonical all-zero PAD.
    pub shared_sibling_frontier: Vec<[LinExpr; 2]>,
    pub live_sibling_count: usize,
    pub old_combines: Vec<StructuralCombineTuplePreparation>,
    pub new_combines: Vec<StructuralCombineTuplePreparation>,
    pub live_combine_count: usize,
    pub combine_capacity_per_root: usize,
    pub roots: ExactStateRootWires,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExactStateStructuralPreparationError {
    Structural(ExactStateStructuralFrontierError),
    CombineCapacityExceeded { required: usize, capacity: usize },
}

impl From<ExactStateStructuralFrontierError> for ExactStateStructuralPreparationError {
    fn from(source: ExactStateStructuralFrontierError) -> Self {
        Self::Structural(source)
    }
}

/// Validate and allocate a structural carrier without yet proving its
/// topology. Live combine tuples preserve `StructuralFrontierPlan::combines`
/// order; every suffix row is the canonical `(PAD, PAD, H(PAD, PAD))` ghost.
pub fn prepare_exact_state_structural_region(
    b: &mut FieldR1csBuilder,
    inputs: &ExactStateStructuralFrontierInputs,
    combine_capacity_per_root: usize,
) -> Result<ExactStateStructuralRegionPreparation, ExactStateStructuralPreparationError> {
    let verified = verify_exact_state_structural_frontier(inputs)?;
    let live_combine_count = verified.plan.combines().len();
    if live_combine_count > combine_capacity_per_root {
        return Err(
            ExactStateStructuralPreparationError::CombineCapacityExceeded {
                required: live_combine_count,
                capacity: combine_capacity_per_root,
            },
        );
    }

    let old_leaf_digests = inputs
        .old_slot_leaves
        .iter()
        .map(|leaf| fields_to_state_hash(leaf.expected_leaf))
        .collect::<Vec<_>>();
    let new_leaf_digests = inputs
        .new_slot_leaves
        .iter()
        .map(|leaf| fields_to_state_hash(leaf.expected_leaf))
        .collect::<Vec<_>>();
    let old_live = structural_combine_values(
        &verified.plan,
        &old_leaf_digests,
        &inputs.live_sibling_digests,
        &verified.old_evaluation,
    );
    let new_live = structural_combine_values(
        &verified.plan,
        &new_leaf_digests,
        &inputs.live_sibling_digests,
        &verified.new_evaluation,
    );

    let touched_leaves = inputs
        .touched_indices
        .iter()
        .zip(
            inputs
                .old_slot_leaves
                .iter()
                .zip(inputs.new_slot_leaves.iter()),
        )
        .map(
            |(&slot_index, (old, new))| StructuralTouchedLeafPreparation {
                slot_index: alloc_block(b, Block128::from(slot_index as u128)),
                old: SlotLeafInputsTrace::alloc(b, old),
                new: SlotLeafInputsTrace::alloc(b, new),
            },
        )
        .collect();
    let live_sibling_count = inputs.live_sibling_digests.len();
    debug_assert!(live_sibling_count <= combine_capacity_per_root);
    let shared_sibling_frontier = (0..combine_capacity_per_root)
        .map(|ordinal| {
            alloc_state_hash(
                b,
                inputs
                    .live_sibling_digests
                    .get(ordinal)
                    .copied()
                    .unwrap_or(STRUCTURAL_FRONTIER_PAD),
            )
        })
        .collect();
    let old_combines = allocate_structural_combine_half(
        b,
        &old_live,
        live_combine_count,
        combine_capacity_per_root,
    );
    let new_combines = allocate_structural_combine_half(
        b,
        &new_live,
        live_combine_count,
        combine_capacity_per_root,
    );
    let roots = ExactStateRootWires {
        old_root: alloc_state_hash(b, inputs.old_root),
        new_root: alloc_state_hash(b, inputs.new_root),
        active_depth: inputs.active_depth as usize,
    };

    Ok(ExactStateStructuralRegionPreparation {
        plan: verified.plan,
        touched_leaves,
        shared_sibling_frontier,
        live_sibling_count,
        old_combines,
        new_combines,
        live_combine_count,
        combine_capacity_per_root,
        roots,
    })
}

fn structural_combine_values(
    plan: &StructuralFrontierPlan,
    leaves: &[StateHash],
    siblings: &[StateHash],
    evaluation: &StructuralFrontierEvaluation,
) -> Vec<(StateHash, StateHash, StateHash)> {
    plan.combines()
        .iter()
        .enumerate()
        .map(|(ordinal, combine)| {
            (
                structural_node_value(combine.left, leaves, siblings, &evaluation.combines),
                structural_node_value(combine.right, leaves, siblings, &evaluation.combines),
                evaluation.combines[ordinal],
            )
        })
        .collect()
}

fn structural_node_value(
    node: StructuralNodeRef,
    leaves: &[StateHash],
    siblings: &[StateHash],
    combines: &[StateHash],
) -> StateHash {
    match node {
        StructuralNodeRef::TouchedLeaf(ordinal) => leaves[ordinal],
        StructuralNodeRef::FrontierSibling(ordinal) => siblings[ordinal],
        StructuralNodeRef::Combine(ordinal) => combines[ordinal],
    }
}

fn allocate_structural_combine_half(
    b: &mut FieldR1csBuilder,
    live: &[(StateHash, StateHash, StateHash)],
    live_combine_count: usize,
    capacity: usize,
) -> Vec<StructuralCombineTuplePreparation> {
    debug_assert_eq!(live.len(), live_combine_count);
    let ghost_parent = state_node_hash(STRUCTURAL_FRONTIER_PAD, STRUCTURAL_FRONTIER_PAD);
    (0..capacity)
        .map(|ordinal| {
            let (left, right, parent, is_live) = live.get(ordinal).map_or(
                (
                    STRUCTURAL_FRONTIER_PAD,
                    STRUCTURAL_FRONTIER_PAD,
                    ghost_parent,
                    false,
                ),
                |&(left, right, parent)| (left, right, parent, true),
            );
            StructuralCombineTuplePreparation {
                left: alloc_state_hash(b, left),
                right: alloc_state_hash(b, right),
                parent: alloc_state_hash(b, parent),
                is_live,
            }
        })
        .collect()
}

fn alloc_state_hash(b: &mut FieldR1csBuilder, digest: StateHash) -> [LinExpr; 2] {
    let fields = digest_to_fields(digest);
    std::array::from_fn(|lane| alloc_block(b, fields[lane]))
}

fn fields_to_state_hash(fields: [Block128; 2]) -> StateHash {
    let mut digest = [0u8; 32];
    digest[..16].copy_from_slice(&fields[0].0.to_le_bytes());
    digest[16..].copy_from_slice(&fields[1].0.to_le_bytes());
    digest
}

pub const MIN_EXACT_STATE_DEPTH: usize = 24;
pub const MAX_EXACT_STATE_DEPTH: usize = 32;
const EXACT_STATE_DEPTH_CHOICES: usize = MAX_EXACT_STATE_DEPTH - MIN_EXACT_STATE_DEPTH + 1;
const MIN_PAIRED_EXACT_STATE_DEPTH: u32 = MIN_EXACT_STATE_DEPTH as u32;
const MAX_PAIRED_EXACT_STATE_DEPTH: u32 = MAX_EXACT_STATE_DEPTH as u32;

/// Header-bound exact-state depth represented by one fixed nine-way selector.
///
/// The selectors are boolean, mutually exclusive, and sum to one.  The
/// original expression is reconstructed from them, so neither a native path
/// depth nor a trace-class constant is proof authority for the selected
/// depth.  Every value in `24..=32` uses the same constraint matrix.
#[derive(Clone, Debug)]
pub struct StateDepthTrace {
    pub value: LinExpr,
    /// Index zero selects depth 24; index eight selects depth 32.
    pub one_hot: [LinExpr; EXACT_STATE_DEPTH_CHOICES],
}

impl StateDepthTrace {
    pub fn bind(b: &mut FieldR1csBuilder, value: &LinExpr) -> Self {
        let native = value.eval(b.values());
        let one_hot = std::array::from_fn(|index| {
            let depth = MIN_EXACT_STATE_DEPTH + index;
            LinExpr::from_wire(b.alloc_bool(native == flat_of(Block128::from(depth as u128))))
        });

        // In characteristic two, `sum(selectors) = 1` alone would also admit
        // any odd number of live selectors.  The running overlap pins make
        // the representation genuinely one-hot.
        let mut seen = LinExpr::zero();
        for selector in &one_hot {
            let overlap = mul(b, selector, &seen);
            pin_zero(b, &overlap);
            seen = seen.add(selector);
        }
        pin_eq(b, &seen, &LinExpr::constant(F128::ONE));

        let selected =
            one_hot
                .iter()
                .enumerate()
                .fold(LinExpr::zero(), |sum, (index, selector)| {
                    let depth = MIN_EXACT_STATE_DEPTH + index;
                    sum.add(&selector.scale(flat_of(Block128::from(depth as u128))))
                });
        pin_eq(b, value, &selected);

        Self {
            value: value.clone(),
            one_hot,
        }
    }

    fn selected_unsigned_bits(&self, addend: usize) -> Vec<LinExpr> {
        let max = MAX_EXACT_STATE_DEPTH + addend;
        let width = usize::BITS as usize - max.leading_zeros() as usize;
        (0..width.max(1))
            .map(|bit| {
                self.one_hot
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| {
                        ((MIN_EXACT_STATE_DEPTH + *index + addend) >> bit) & 1 == 1
                    })
                    .fold(LinExpr::zero(), |sum, (_, selector)| sum.add(selector))
            })
            .collect()
    }
}

/// Authoritatively derived old/new update witnesses for the future paired
/// exact-state region.
///
/// The two vectors contain only real updates. Fixed-capacity ghosts are added
/// by [`Self::packed_updates`] so consumers cannot accidentally confuse class
/// capacity with the number of touched slots or segments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactStatePairedRegionData {
    pub local_updates: Vec<PairedMerkleUpdateWitness>,
    pub upper_updates: Vec<PairedMerkleUpdateWitness>,
    pub local_update_count: usize,
    pub upper_update_count: usize,
    pub touched_capacity: usize,
    pub segment_capacity: usize,
    /// The authenticated prefix of every fixed-depth upper update. Endpoints
    /// must be read after this many levels, not after the padded depth 16.
    pub active_upper_depth: usize,
}

/// One class-shaped paired-update handoff and its dyadic walk geometry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedExactStatePairedUpdates {
    /// `local live || local ghosts || upper live || upper ghosts`.
    /// The paired column builder supplies any remaining dyadic-domain ghosts.
    pub updates: Vec<PairedMerkleUpdateWitness>,
    /// Slots occupied by `updates` before dyadic rounding.
    pub active_slots: usize,
    /// Full walk width, equal to `1 << w_log`.
    pub slots: usize,
    pub w_log: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactStatePairedRegionError {
    Structural(ExactStateStructuralFrontierError),
    ActiveDepthOutOfRange {
        active_depth: u32,
        min: u32,
        max: u32,
    },
    LocalDepthMismatch {
        expected: usize,
        actual: usize,
    },
    UpperDepthOutOfRange {
        actual: usize,
        min: usize,
        max: usize,
    },
    LocalPathDepthMismatch {
        update: usize,
        expected: usize,
        siblings: usize,
        directions: usize,
    },
    UpperPathDepthMismatch {
        update: usize,
        expected: usize,
        siblings: usize,
        directions: usize,
    },
    TouchedCapacityExceeded {
        required: usize,
        capacity: usize,
    },
    SegmentCapacityExceeded {
        required: usize,
        capacity: usize,
    },
    PackedGeometryOverflow {
        total_updates: usize,
    },
}

impl From<ExactStateStructuralFrontierError> for ExactStatePairedRegionError {
    fn from(source: ExactStateStructuralFrontierError) -> Self {
        Self::Structural(source)
    }
}

impl ExactStatePairedRegionData {
    /// Audit the sibling-only carrier, derive its sequential segmented update
    /// projection, and convert it into the fixed depth-16 paired-walk basis.
    pub fn new(
        inputs: &ExactStateStructuralFrontierInputs,
        touched_capacity: usize,
        segment_capacity: usize,
    ) -> Result<Self, ExactStatePairedRegionError> {
        // This helper first runs the authoritative native structural audit;
        // none of the data below is accepted directly from the witness.
        let segmented = derive_exact_state_segmented_updates(inputs, PAIRED_UPDATE_DEPTH as u32)?;

        if !(MIN_PAIRED_EXACT_STATE_DEPTH..=MAX_PAIRED_EXACT_STATE_DEPTH)
            .contains(&inputs.active_depth)
        {
            return Err(ExactStatePairedRegionError::ActiveDepthOutOfRange {
                active_depth: inputs.active_depth,
                min: MIN_PAIRED_EXACT_STATE_DEPTH,
                max: MAX_PAIRED_EXACT_STATE_DEPTH,
            });
        }
        let local_depth = segmented.local_depth as usize;
        if local_depth != PAIRED_UPDATE_DEPTH {
            return Err(ExactStatePairedRegionError::LocalDepthMismatch {
                expected: PAIRED_UPDATE_DEPTH,
                actual: local_depth,
            });
        }
        let active_upper_depth = segmented.upper_depth as usize;
        let min_upper_depth = MIN_PAIRED_EXACT_STATE_DEPTH as usize - PAIRED_UPDATE_DEPTH;
        if !(min_upper_depth..=PAIRED_UPDATE_DEPTH).contains(&active_upper_depth) {
            return Err(ExactStatePairedRegionError::UpperDepthOutOfRange {
                actual: active_upper_depth,
                min: min_upper_depth,
                max: PAIRED_UPDATE_DEPTH,
            });
        }

        let local_update_count = segmented.local_updates.len();
        let upper_update_count = segmented.segment_updates.len();
        if local_update_count > touched_capacity {
            return Err(ExactStatePairedRegionError::TouchedCapacityExceeded {
                required: local_update_count,
                capacity: touched_capacity,
            });
        }
        if upper_update_count > segment_capacity {
            return Err(ExactStatePairedRegionError::SegmentCapacityExceeded {
                required: upper_update_count,
                capacity: segment_capacity,
            });
        }
        validate_paired_path_depths(&segmented.local_updates, local_depth, true)?;
        validate_paired_path_depths(&segmented.segment_updates, active_upper_depth, false)?;
        let total_updates = touched_capacity.checked_add(segment_capacity).ok_or(
            ExactStatePairedRegionError::PackedGeometryOverflow {
                total_updates: usize::MAX,
            },
        )?;
        let active_slots = total_updates
            .checked_mul(PAIRED_UPDATE_STRIDE)
            .ok_or(ExactStatePairedRegionError::PackedGeometryOverflow { total_updates })?;
        if active_slots == 0 || active_slots.checked_next_power_of_two().is_none() {
            return Err(ExactStatePairedRegionError::PackedGeometryOverflow { total_updates });
        }

        let local_updates = segmented
            .local_updates
            .iter()
            .map(paired_local_witness)
            .collect();
        let zero_roots = zero_slot_roots((MAX_PAIRED_EXACT_STATE_DEPTH - 1) as usize);
        let upper_updates = segmented
            .segment_updates
            .iter()
            .map(|update| paired_upper_witness(update, active_upper_depth, &zero_roots))
            .collect();

        Ok(Self {
            local_updates,
            upper_updates,
            local_update_count,
            upper_update_count,
            touched_capacity,
            segment_capacity,
            active_upper_depth,
        })
    }

    /// Pack live updates into their class partitions and report the dyadic
    /// column domain consumed by the fixed 64-slot update primitive.
    pub fn packed_updates(&self) -> PackedExactStatePairedUpdates {
        assert_eq!(self.local_updates.len(), self.local_update_count);
        assert_eq!(self.upper_updates.len(), self.upper_update_count);
        assert!(self.local_update_count <= self.touched_capacity);
        assert!(self.upper_update_count <= self.segment_capacity);
        assert!((8..=PAIRED_UPDATE_DEPTH).contains(&self.active_upper_depth));

        let total_updates = self
            .touched_capacity
            .checked_add(self.segment_capacity)
            .expect("paired region geometry was validated by its constructor");
        let mut updates = Vec::with_capacity(total_updates);
        updates.extend(self.local_updates.iter().cloned());
        updates.resize_with(self.touched_capacity, local_empty_ghost);
        updates.extend(self.upper_updates.iter().cloned());
        updates.resize_with(total_updates, PairedMerkleUpdateWitness::canonical_ghost);

        let active_slots = total_updates
            .checked_mul(PAIRED_UPDATE_STRIDE)
            .expect("paired region geometry was validated by its constructor");
        let slots = active_slots
            .checked_next_power_of_two()
            .expect("paired region geometry was validated by its constructor");
        let w_log = slots.trailing_zeros() as usize;
        PackedExactStatePairedUpdates {
            updates,
            active_slots,
            slots,
            w_log,
        }
    }
}

fn validate_paired_path_depths(
    updates: &[SequentialMerkleUpdatePath],
    expected: usize,
    local: bool,
) -> Result<(), ExactStatePairedRegionError> {
    for (update, path) in updates.iter().enumerate() {
        if path.siblings.len() != expected || path.directions.len() != expected {
            return Err(if local {
                ExactStatePairedRegionError::LocalPathDepthMismatch {
                    update,
                    expected,
                    siblings: path.siblings.len(),
                    directions: path.directions.len(),
                }
            } else {
                ExactStatePairedRegionError::UpperPathDepthMismatch {
                    update,
                    expected,
                    siblings: path.siblings.len(),
                    directions: path.directions.len(),
                }
            });
        }
    }
    Ok(())
}

fn paired_local_witness(update: &SequentialMerkleUpdatePath) -> PairedMerkleUpdateWitness {
    debug_assert_eq!(update.siblings.len(), PAIRED_UPDATE_DEPTH);
    debug_assert_eq!(update.directions.len(), PAIRED_UPDATE_DEPTH);
    PairedMerkleUpdateWitness {
        old_entry: flat_state_hash(update.old_leaf),
        new_entry: flat_state_hash(update.new_leaf),
        siblings: std::array::from_fn(|level| flat_state_hash(update.siblings[level])),
        directions: std::array::from_fn(|level| update.directions[level]),
    }
}

fn paired_upper_witness(
    update: &SequentialMerkleUpdatePath,
    active_upper_depth: usize,
    zero_roots: &[StateHash],
) -> PairedMerkleUpdateWitness {
    debug_assert_eq!(update.siblings.len(), active_upper_depth);
    debug_assert_eq!(update.directions.len(), active_upper_depth);
    PairedMerkleUpdateWitness {
        old_entry: flat_state_hash(update.old_leaf),
        new_entry: flat_state_hash(update.new_leaf),
        siblings: std::array::from_fn(|level| {
            if level < active_upper_depth {
                flat_state_hash(update.siblings[level])
            } else {
                // Upper level zero is global level 16. At and above the real
                // root, the fixed walk continues as canonical left growth.
                flat_state_hash(zero_roots[PAIRED_UPDATE_DEPTH + level])
            }
        }),
        directions: std::array::from_fn(|level| {
            level < active_upper_depth && update.directions[level]
        }),
    }
}

fn flat_state_hash(digest: StateHash) -> [F128; 2] {
    flat2(digest_to_fields(digest))
}

/// Local padding is bridged to padded exact-state leaf rows, whose canonical
/// value is the hash of `SlotValue::EMPTY`, not the all-zero field pair.
fn local_empty_ghost() -> PairedMerkleUpdateWitness {
    let empty_leaf = flat_state_hash(slot_leaf_hash(SlotValue::EMPTY));
    PairedMerkleUpdateWitness {
        old_entry: empty_leaf,
        new_entry: empty_leaf,
        siblings: [[F128::ZERO; 2]; PAIRED_UPDATE_DEPTH],
        directions: [false; PAIRED_UPDATE_DEPTH],
    }
}

/// Bind the accepted-claim frontier-node count to the same sorted action
/// prefix that drives exact-state updates.
///
/// For sorted distinct depth-`d` indices `x_0 < ... < x_{T-1}`, the canonical
/// binary multiproof has
///
/// `F + T = d + 1 + sum(msb(x_i XOR x_{i-1}))`.
///
/// The exposed action slot bits let this relation avoid a second range check.
/// All binary additions below operate on bit vectors, so they are integer
/// additions rather than characteristic-two field XOR. `active_depth` is the
/// current trace-class depth constant; a future variable-depth class must mux
/// this same relation from a header-bound depth wire rather than accepting a
/// native count.
pub fn bind_structural_frontier_count_from_actions(
    b: &mut FieldR1csBuilder,
    actions: &[ActionRowTrace],
    slot_bits: &[Vec<Wire>],
    adjacent_msb_one_hot: &[Vec<LinExpr>],
    active_depth: usize,
    claimed_frontier_count: &LinExpr,
) {
    const SLOT_BITS: usize = 32;
    const COUNT_BITS: usize = 16;
    assert!(
        !actions.is_empty(),
        "coinbase makes the touched set non-empty"
    );
    assert_eq!(actions.len(), slot_bits.len());
    assert_eq!(adjacent_msb_one_hot.len(), actions.len().saturating_sub(1));
    assert!(active_depth <= SLOT_BITS);
    assert!(slot_bits.iter().all(|bits| bits.len() == SLOT_BITS));
    assert!(adjacent_msb_one_hot
        .iter()
        .all(|one_hot| one_hot.len() == SLOT_BITS));

    // Dynamic action values cannot alias modulo the active tree depth. One
    // linear pin per row suffices because the tower power basis is linearly
    // independent; dead suffix rows are already canonical zero actions.
    for bits in slot_bits {
        let high =
            bits[active_depth..]
                .iter()
                .enumerate()
                .fold(LinExpr::zero(), |sum, (offset, &bit)| {
                    sum.add(
                        &LinExpr::from_wire(bit)
                            .scale(flat_const(1u128 << (active_depth + offset))),
                    )
                });
        pin_zero(b, &high);
    }

    // One five-bit `msb(x_i XOR x_{i-1})` term per possible live adjacency.
    // The strict-order comparator already built each one-hot highest set bit;
    // only the live gate and integer accumulation remain here.
    let mut msb_terms = Vec::with_capacity(actions.len().saturating_sub(1));
    for (index, highest) in adjacent_msb_one_hot.iter().enumerate() {
        let current_live = &actions[index + 1].live;
        let term_bits = (0..5)
            .map(|out_bit| {
                let raw = highest
                    .iter()
                    .enumerate()
                    .filter(|(position, _)| position >> out_bit & 1 == 1)
                    .fold(LinExpr::zero(), |sum, (_, bit)| sum.add(bit));
                mul(b, current_live, &raw)
            })
            .collect::<Vec<_>>();
        msb_terms.push(term_bits);
    }

    let msb_sum = sum_unsigned_bit_vectors(b, msb_terms);
    let touched_sum = sum_unsigned_bit_vectors(
        b,
        actions
            .iter()
            .map(|action| vec![action.live.clone()])
            .collect(),
    );
    let rhs = add_unsigned_bits(b, &msb_sum, &constant_unsigned_bits(active_depth + 1));
    let frontier_bits: Vec<LinExpr> = range_check_bits(b, claimed_frontier_count, COUNT_BITS)
        .into_iter()
        .map(LinExpr::from_wire)
        .collect();
    let lhs = add_unsigned_bits(b, &frontier_bits, &touched_sum);
    let width = lhs.len().max(rhs.len());
    for bit in 0..width {
        pin_eq(
            b,
            lhs.get(bit).unwrap_or(&LinExpr::zero()),
            rhs.get(bit).unwrap_or(&LinExpr::zero()),
        );
    }
}

/// Dynamic-depth form of [`bind_structural_frontier_count_from_actions`].
///
/// The header-bound [`StateDepthTrace`] selects both the integer `d + 1`
/// term and the admissible slot-index width.  All eight potentially forbidden
/// high bits are gated algebraically, so depth 24 and depth 32 have identical
/// matrices even though one forbids every high bit and the other forbids none.
pub fn bind_structural_frontier_count_from_actions_dynamic(
    b: &mut FieldR1csBuilder,
    actions: &[ActionRowTrace],
    slot_bits: &[Vec<Wire>],
    adjacent_msb_one_hot: &[Vec<LinExpr>],
    depth: &StateDepthTrace,
    claimed_frontier_count: &LinExpr,
) {
    const SLOT_BITS: usize = 32;
    const COUNT_BITS: usize = 16;
    assert!(
        !actions.is_empty(),
        "coinbase makes the touched set non-empty"
    );
    assert_eq!(actions.len(), slot_bits.len());
    assert_eq!(adjacent_msb_one_hot.len(), actions.len().saturating_sub(1));
    assert!(slot_bits.iter().all(|bits| bits.len() == SLOT_BITS));
    assert!(adjacent_msb_one_hot
        .iter()
        .all(|one_hot| one_hot.len() == SLOT_BITS));

    // At bit position `p`, exactly the selectors for depths `d <= p` make
    // that position illegal.  The loop bounds and coefficients are protocol
    // constants; only the one-hot witness changes across depth classes.
    for bits in slot_bits {
        let mut packed_violations = LinExpr::zero();
        for (position, &bit) in bits.iter().enumerate().skip(MIN_EXACT_STATE_DEPTH) {
            let forbidden = depth
                .one_hot
                .iter()
                .enumerate()
                .take(position - MIN_EXACT_STATE_DEPTH + 1)
                .fold(LinExpr::zero(), |sum, (_, selector)| sum.add(selector));
            let violation = mul(b, &LinExpr::from_wire(bit), &forbidden);
            packed_violations =
                packed_violations.add(&violation.scale(flat_const(1u128 << position)));
        }
        // Every violation is boolean and the eight coefficients are distinct
        // power-basis elements, so one linear pin is equivalent to eight
        // separate zero pins.
        pin_zero(b, &packed_violations);
    }

    let mut msb_terms = Vec::with_capacity(actions.len().saturating_sub(1));
    for (index, highest) in adjacent_msb_one_hot.iter().enumerate() {
        let current_live = &actions[index + 1].live;
        let term_bits = (0..5)
            .map(|out_bit| {
                let raw = highest
                    .iter()
                    .enumerate()
                    .filter(|(position, _)| position >> out_bit & 1 == 1)
                    .fold(LinExpr::zero(), |sum, (_, bit)| sum.add(bit));
                mul(b, current_live, &raw)
            })
            .collect::<Vec<_>>();
        msb_terms.push(term_bits);
    }

    let msb_sum = sum_unsigned_bit_vectors(b, msb_terms);
    let touched_sum = sum_unsigned_bit_vectors(
        b,
        actions
            .iter()
            .map(|action| vec![action.live.clone()])
            .collect(),
    );
    let rhs = add_unsigned_bits(b, &msb_sum, &depth.selected_unsigned_bits(1));
    let frontier_bits: Vec<LinExpr> = range_check_bits(b, claimed_frontier_count, COUNT_BITS)
        .into_iter()
        .map(LinExpr::from_wire)
        .collect();
    let lhs = add_unsigned_bits(b, &frontier_bits, &touched_sum);
    let width = lhs.len().max(rhs.len());
    let zero = LinExpr::zero();
    for bit in 0..width {
        pin_eq(
            b,
            lhs.get(bit).unwrap_or(&zero),
            rhs.get(bit).unwrap_or(&zero),
        );
    }
}

/// Add two little-endian boolean bit vectors, retaining the final carry.
fn add_unsigned_bits(
    b: &mut FieldR1csBuilder,
    left: &[LinExpr],
    right: &[LinExpr],
) -> Vec<LinExpr> {
    let width = left.len().max(right.len());
    let zero = LinExpr::zero();
    let mut carry = LinExpr::zero();
    let mut out = Vec::with_capacity(width + 1);
    for bit in 0..width {
        let a = left.get(bit).unwrap_or(&zero);
        let c = right.get(bit).unwrap_or(&zero);
        out.push(a.add(c).add(&carry));
        let both = mul(b, a, c);
        let carry_one = mul(b, &carry, &a.add(c));
        carry = both.add(&carry_one);
    }
    out.push(carry);
    out
}

/// Balanced sum of fixed-shape little-endian unsigned values.
fn sum_unsigned_bit_vectors(
    b: &mut FieldR1csBuilder,
    mut values: Vec<Vec<LinExpr>>,
) -> Vec<LinExpr> {
    if values.is_empty() {
        return vec![LinExpr::zero()];
    }
    while values.len() > 1 {
        let mut next = Vec::with_capacity(values.len().div_ceil(2));
        let mut pairs = values.chunks_exact(2);
        for pair in &mut pairs {
            next.push(add_unsigned_bits(b, &pair[0], &pair[1]));
        }
        if let [last] = pairs.remainder() {
            next.push(last.clone());
        }
        values = next;
    }
    values.pop().unwrap()
}

fn constant_unsigned_bits(value: usize) -> Vec<LinExpr> {
    let width = usize::BITS as usize - value.leading_zeros() as usize;
    (0..width.max(1))
        .map(|bit| {
            LinExpr::constant(if value >> bit & 1 == 1 {
                F128::ONE
            } else {
                F128::ZERO
            })
        })
        .collect()
}

pub struct ExactStateRootWires {
    pub old_root: [LinExpr; 2],
    pub new_root: [LinExpr; 2],
    pub active_depth: usize,
}

pub struct ExactStateSlotWires {
    pub slot_leaves: Vec<SlotLeafInputsTrace>,
    pub roots: ExactStateRootWires,
}

pub struct ExactStateLeafRegion {
    pub packed_value_w: LinExpr,
    pub owner_hi_w: LinExpr,
    pub owner_lo_w: LinExpr,
    pub expected_leaf_w: [LinExpr; 2],
    pub packed_value_flat: F128,
    pub owner_hi_flat: F128,
    pub owner_lo_flat: F128,
    pub expected_leaf_flat: [F128; 2],
}

pub struct ExactStateRegionData {
    pub leaves: Vec<ExactStateLeafRegion>,
    /// Production sequential old/new update schedule derived from the
    /// authoritative structural frontier.
    pub paired: ExactStatePairedRegionData,
    pub old_root_w: [LinExpr; 2],
    pub old_root_flat: [F128; 2],
    pub new_root_w: [LinExpr; 2],
    pub new_root_flat: [F128; 2],
}

fn flat2(fields: [Block128; 2]) -> [F128; 2] {
    [flat_of(fields[0]), flat_of(fields[1])]
}

fn assemble_exact_state_leaf_region(
    natives: &[SlotLeafInputs],
    wires: &[SlotLeafInputsTrace],
) -> Vec<ExactStateLeafRegion> {
    assert_eq!(natives.len(), wires.len());
    natives
        .iter()
        .zip(wires)
        .map(|(native, wires)| {
            let leaf = ExactStateLeafRegion {
                packed_value_w: wires.packed_value.clone(),
                owner_hi_w: wires.owner_hi.clone(),
                owner_lo_w: wires.owner_lo.clone(),
                expected_leaf_w: wires.expected_leaf.clone(),
                packed_value_flat: flat_of(native.packed_value),
                owner_hi_flat: flat_of(native.owner_hi),
                owner_lo_flat: flat_of(native.owner_lo),
                expected_leaf_flat: flat2(native.expected_leaf),
            };
            assert_eq!(
                flat_sponge_leaf_hash(
                    leaf.packed_value_flat,
                    leaf.owner_hi_flat,
                    leaf.owner_lo_flat,
                ),
                leaf.expected_leaf_flat,
                "slot-leaf statement digest != flat sponge replay"
            );
            leaf
        })
        .collect()
}

fn empty_slot_leaf_input() -> SlotLeafInputs {
    let empty = noid_chain::SlotValue::EMPTY;
    SlotLeafInputs {
        packed_value: empty.value,
        owner_hi: empty.owner_hi,
        owner_lo: empty.owner_lo,
        expected_leaf: digest_to_fields(noid_chain::exact_state_hash::slot_leaf_hash(empty)),
    }
}

/// Build the production exact-state region handoff directly from the
/// authoritative sibling-only carrier. No expanded path is allocated or
/// accepted here: local/upper paired witnesses are derived by
/// [`ExactStatePairedRegionData::new`].
pub fn build_exact_state_structural_region_slot(
    b: &mut FieldR1csBuilder,
    inputs: &ExactStateStructuralFrontierInputs,
    touched_capacity: usize,
    segment_capacity: usize,
) -> Result<(ExactStateSlotWires, ExactStateRegionData), ExactStatePairedRegionError> {
    let paired = ExactStatePairedRegionData::new(inputs, touched_capacity, segment_capacity)?;
    let empty = empty_slot_leaf_input();
    let mut old_natives = inputs.old_slot_leaves.clone();
    let mut new_natives = inputs.new_slot_leaves.clone();
    old_natives.resize(touched_capacity, empty.clone());
    new_natives.resize(touched_capacity, empty);
    let mut natives = old_natives;
    natives.extend(new_natives);
    let slot_leaves = natives
        .iter()
        .map(|native| SlotLeafInputsTrace::alloc(b, native))
        .collect::<Vec<_>>();
    let roots = ExactStateRootWires {
        old_root: alloc_state_hash(b, inputs.old_root),
        new_root: alloc_state_hash(b, inputs.new_root),
        active_depth: inputs.active_depth as usize,
    };
    let region = ExactStateRegionData {
        leaves: assemble_exact_state_leaf_region(&natives, &slot_leaves),
        paired,
        old_root_w: roots.old_root.clone(),
        old_root_flat: flat_state_hash(inputs.old_root),
        new_root_w: roots.new_root.clone(),
        new_root_flat: flat_state_hash(inputs.new_root),
    };
    Ok((ExactStateSlotWires { slot_leaves, roots }, region))
}

fn pin_pair(b: &mut FieldR1csBuilder, a: &[LinExpr; 2], c: &[LinExpr; 2]) {
    pin_eq(b, &a[0], &c[0]);
    pin_eq(b, &a[1], &c[1]);
}

/// Header-bound exact-state depth transition reused by exact-state routing,
/// fee pressure (parent depth), and emission (child depth).
#[derive(Clone, Debug)]
pub struct StateDepthTransitionTrace {
    pub parent: StateDepthTrace,
    pub child: StateDepthTrace,
    pub grow: LinExpr,
}

/// Bind exact-state roots and both header depths without a native depth
/// coefficient.
///
/// `parent_log` and `child_log` each receive a fixed nine-way range proof.
/// The child selector is constrained to equal the parent selector or its
/// one-position shift.  The grow candidate is always evaluated as
/// `H(parent_root, Z_parent_depth)` and then algebraically selected, so equal
/// and grow transitions share one matrix.
pub fn bind_exact_state_header_roots_dynamic(
    b: &mut FieldR1csBuilder,
    roots: &ExactStateRootWires,
    parent_root: &[LinExpr; 2],
    parent_log: &LinExpr,
    child_root: &[LinExpr; 2],
    child_log: &LinExpr,
) -> StateDepthTransitionTrace {
    let parent_depth = StateDepthTrace::bind(b, parent_log);
    let child_depth = StateDepthTrace::bind(b, child_log);
    let grows = (1..EXACT_STATE_DEPTH_CHOICES).any(|index| {
        parent_depth.one_hot[index - 1].eval(b.values()) == F128::ONE
            && child_depth.one_hot[index].eval(b.values()) == F128::ONE
    });
    let grow = LinExpr::from_wire(b.alloc_bool(grows));

    // grow=0 copies the selector; grow=1 shifts it one place upward.  At
    // parent depth 32 the shifted vector is all zero and therefore conflicts
    // with the child's exact-one constraint, forbidding growth past 32.
    let zero = LinExpr::zero();
    for index in 0..EXACT_STATE_DEPTH_CHOICES {
        let previous = if index == 0 {
            &zero
        } else {
            &parent_depth.one_hot[index - 1]
        };
        let delta = parent_depth.one_hot[index].add(previous);
        let selected = parent_depth.one_hot[index].add(&mul(b, &grow, &delta));
        pin_eq(b, &child_depth.one_hot[index], &selected);
    }

    let zero_roots = zero_slot_roots(MAX_EXACT_STATE_DEPTH);
    let selected_zero: [LinExpr; 2] = std::array::from_fn(|lane| {
        parent_depth
            .one_hot
            .iter()
            .enumerate()
            .fold(LinExpr::zero(), |sum, (index, selector)| {
                let native_depth = MIN_EXACT_STATE_DEPTH + index;
                let zero = digest_to_fields(zero_roots[native_depth]);
                sum.add(&selector.scale(flat_of(zero[lane])))
            })
    });
    let iv = capacity_iv(TAG_EXSTNOD);
    let state = poseidon2b_permute(
        b,
        [
            parent_root[0].clone(),
            parent_root[1].clone(),
            const_block(iv[0]),
            const_block(iv[1]),
        ],
    );
    let grow_root = poseidon2b_permute(
        b,
        [
            state[0].add(&selected_zero[0]),
            state[1].add(&selected_zero[1]),
            state[2].clone(),
            state[3].clone(),
        ],
    );
    for lane in 0..2 {
        let delta = grow_root[lane].add(&parent_root[lane]);
        let selected = parent_root[lane].add(&mul(b, &grow, &delta));
        pin_eq(b, &roots.old_root[lane], &selected);
    }
    pin_pair(b, &roots.new_root, child_root);

    StateDepthTransitionTrace {
        parent: parent_depth,
        child: child_depth,
        grow,
    }
}

/// Before/after root cells for one fixed paired-update depth.
pub type PairedRootCellPair = [[LinExpr; 2]; 2];

/// Select the upper paired-update endpoint at depth `child_depth - 16`.
///
/// `roots_by_depth[0]` is the depth-one pair and index 15 is the depth-16
/// pair.  All sixteen pairs are supplied even though exact-state depths only
/// select upper depths 8 through 16.  This keeps the handoff shape independent
/// of the header value.
pub fn select_upper_paired_roots(
    b: &mut FieldR1csBuilder,
    child_depth: &StateDepthTrace,
    roots_by_depth: &[PairedRootCellPair; PAIRED_UPDATE_DEPTH],
) -> PairedRootCellPair {
    std::array::from_fn(|side| {
        std::array::from_fn(|lane| {
            child_depth.one_hot.iter().enumerate().fold(
                LinExpr::zero(),
                |sum, (index, selector)| {
                    let state_depth = MIN_EXACT_STATE_DEPTH + index;
                    let upper_depth = state_depth - PAIRED_UPDATE_DEPTH;
                    let cell = &roots_by_depth[upper_depth - 1][side][lane];
                    sum.add(&mul(b, selector, cell))
                },
            )
        })
    })
}

/// Bind exact-state path roots/depth directly to the parent and child header
/// statement wires. `parent_log_slots` is class/native metadata already bound
/// to `parent_log`; `roots.active_depth` is the child path class.
pub fn bind_exact_state_header_roots(
    b: &mut FieldR1csBuilder,
    roots: &ExactStateRootWires,
    parent_root: &[LinExpr; 2],
    parent_log: &LinExpr,
    parent_log_slots: u32,
    child_root: &[LinExpr; 2],
    child_log: &LinExpr,
) -> LinExpr {
    let child_log_slots = roots.active_depth as u32;
    assert!(
        child_log_slots == parent_log_slots || child_log_slots == parent_log_slots + 1,
        "exact-state depth must stay equal or grow by one"
    );
    assert!(child_log_slots > 0, "exact-state paths have non-zero depth");
    let grows = child_log_slots == parent_log_slots + 1;
    let grow = LinExpr::from_wire(b.alloc_bool(grows));
    // Fixed child-depth matrix: parent depth is selected between d and d-1.
    // Integer encodings are tower constants; selection in characteristic two
    // uses `d + grow * (d XOR (d-1))`.
    let parent_same = Block128::from(child_log_slots as u128);
    let parent_grow = Block128::from((child_log_slots - 1) as u128);
    let parent_selected =
        const_block(parent_same).add(&grow.scale(flat_of(parent_same + parent_grow)));
    pin_eq(b, parent_log, &parent_selected);
    pin_eq(
        b,
        child_log,
        &const_block(Block128::from(child_log_slots as u128)),
    );
    pin_pair(b, &roots.new_root, child_root);
    // Always compute the grow candidate at d-1 so equal/grow share one matrix.
    let grow_parent_depth = child_log_slots as usize - 1;
    let zeros = zero_slot_roots(grow_parent_depth);
    let zero = digest_to_fields(zeros[grow_parent_depth]);
    let iv = capacity_iv(TAG_EXSTNOD);
    let state = poseidon2b_permute(
        b,
        [
            parent_root[0].clone(),
            parent_root[1].clone(),
            const_block(iv[0]),
            const_block(iv[1]),
        ],
    );
    let state = poseidon2b_permute(
        b,
        [
            state[0].add(&const_block(zero[0])),
            state[1].add(&const_block(zero[1])),
            state[2].clone(),
            state[3].clone(),
        ],
    );
    for lane in 0..2 {
        let delta = state[lane].add(&parent_root[lane]);
        let selected = parent_root[lane].add(&mul(b, &grow, &delta));
        pin_eq(b, &roots.old_root[lane], &selected);
    }
    grow
}

fn digest_to_fields(hash: [u8; 32]) -> [Block128; 2] {
    [
        Block128::from(u128::from_le_bytes(hash[..16].try_into().unwrap())),
        Block128::from(u128::from_le_bytes(hash[16..].try_into().unwrap())),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::trace::action_compaction::{
        bind_mint_packed_values_body_order, compact_action_rows,
    };
    use noid_chain::exact_state_hash::{slot_leaf_hash, state_node_hash};
    use noid_chain::sparse_merkle::{
        derive_structural_frontier_plan, evaluate_structural_frontier, expected_sibling_count,
        SparseMerkleError,
    };
    use noid_chain::SlotValue;
    use noid_ivc_core::field::F128 as Field;
    use noid_ivc_core::field_r1cs::FieldR1cs;

    const TEST_BLOCK_HEIGHT: u128 = 6;
    const COINBASE_TEST_ID: u64 = (1u64 << 63) | (TEST_BLOCK_HEIGHT as u64);

    fn exact_leaf_input(value: Block128, owner: [Block128; 2]) -> SlotLeafInputs {
        let slot = SlotValue {
            value,
            owner_hi: owner[0],
            owner_lo: owner[1],
        };
        SlotLeafInputs {
            packed_value: value,
            owner_hi: owner[0],
            owner_lo: owner[1],
            expected_leaf: digest_to_fields(slot_leaf_hash(slot)),
        }
    }

    fn action_leaf_case(
        old_spend_value: Block128,
        old_mint_value: Block128,
        new_mint_value: Block128,
        mint_body_value: Block128,
        new_mint_owner: [Block128; 2],
    ) -> (FieldR1cs, Vec<F128>) {
        let spend_owner = [Block128::from(21u128), Block128::from(22u128)];
        let mint_owner = [Block128::from(31u128), Block128::from(32u128)];
        let mut b = FieldR1csBuilder::new();
        let live_mint = LinExpr::from_wire(b.alloc_bool(true));
        let live_spend = LinExpr::from_wire(b.alloc_bool(true));
        // Body order deliberately differs from slot order.
        let mut actions = vec![
            ActionRowTrace {
                live: live_mint.clone(),
                slot_index: alloc_block(&mut b, Block128::from(9u128)),
                value: alloc_block(&mut b, mint_body_value),
                owner: std::array::from_fn(|lane| alloc_block(&mut b, mint_owner[lane])),
                is_mint: live_mint,
            },
            ActionRowTrace {
                live: live_spend,
                slot_index: alloc_block(&mut b, Block128::from(5u128)),
                value: alloc_block(&mut b, noid_tx::pack_amount_creation_id(11, 7)),
                owner: std::array::from_fn(|lane| alloc_block(&mut b, spend_owner[lane])),
                is_mint: LinExpr::zero(),
            },
        ];
        let parent = alloc_block(&mut b, Block128::from(7u128));
        let child = alloc_block(&mut b, Block128::from(8u128));
        // Body index 0 is the mandatory coinbase mint: its packed id is the
        // tagged height while the allocator still advances 7 -> 8.
        let height = alloc_block(&mut b, Block128::from(TEST_BLOCK_HEIGHT));
        // Production proves this at the body source through public_arithmetic.
        let _ = range_check_bits(&mut b, &actions[0].value, 64);
        bind_mint_packed_values_body_order(&mut b, &mut actions, &parent, &child, &height);
        let compacted = compact_action_rows(&mut b, &actions, actions.len());

        let empty = exact_leaf_input(Block128::from(0u128), [Block128::from(0u128); 2]);
        let old_native = [
            exact_leaf_input(old_spend_value, spend_owner),
            exact_leaf_input(old_mint_value, [Block128::from(0u128); 2]),
        ];
        let new_native = [empty, exact_leaf_input(new_mint_value, new_mint_owner)];
        let old = old_native
            .iter()
            .map(|leaf| SlotLeafInputsTrace::alloc(&mut b, leaf))
            .collect::<Vec<_>>();
        let new = new_native
            .iter()
            .map(|leaf| SlotLeafInputsTrace::alloc(&mut b, leaf))
            .collect::<Vec<_>>();
        bind_actions_to_exact_state_leaves(&mut b, &compacted.rows, &old, &new);
        b.build()
    }

    fn structural_slot_leaf(seed: u128) -> SlotLeafInputs {
        let slot = SlotValue {
            value: Block128::from(seed),
            owner_hi: Block128::from(seed.wrapping_mul(17)),
            owner_lo: Block128::from(seed.wrapping_mul(29)),
        };
        SlotLeafInputs {
            packed_value: slot.value,
            owner_hi: slot.owner_hi,
            owner_lo: slot.owner_lo,
            expected_leaf: digest_to_fields(slot_leaf_hash(slot)),
        }
    }

    #[test]
    fn spend_and_mint_leaf_semantics_follow_the_sorted_action_tuple() {
        let mint_owner = [Block128::from(31u128), Block128::from(32u128)];
        let (r1cs, witness) = action_leaf_case(
            noid_tx::pack_amount_creation_id(11, 7),
            Block128::from(0u128),
            noid_tx::pack_amount_creation_id(13, COINBASE_TEST_ID),
            Block128::from(13u128),
            mint_owner,
        );
        assert!(r1cs.satisfies(&witness));
    }

    #[test]
    fn action_leaf_recombination_rejects_component_mixing() {
        let mint_owner = [Block128::from(31u128), Block128::from(32u128)];
        let cases = [
            action_leaf_case(
                noid_tx::pack_amount_creation_id(12, 7),
                Block128::from(0u128),
                noid_tx::pack_amount_creation_id(13, COINBASE_TEST_ID),
                Block128::from(13u128),
                mint_owner,
            ),
            action_leaf_case(
                noid_tx::pack_amount_creation_id(11, 7),
                Block128::from(1u128),
                noid_tx::pack_amount_creation_id(13, COINBASE_TEST_ID),
                Block128::from(13u128),
                mint_owner,
            ),
            action_leaf_case(
                noid_tx::pack_amount_creation_id(11, 7),
                Block128::from(0u128),
                noid_tx::pack_amount_creation_id(13, COINBASE_TEST_ID + 1),
                Block128::from(13u128),
                mint_owner,
            ),
            action_leaf_case(
                noid_tx::pack_amount_creation_id(11, 7),
                Block128::from(0u128),
                noid_tx::pack_amount_creation_id(13, COINBASE_TEST_ID),
                Block128::from(1u128 << 64),
                mint_owner,
            ),
            action_leaf_case(
                noid_tx::pack_amount_creation_id(11, 7),
                Block128::from(0u128),
                noid_tx::pack_amount_creation_id(13, COINBASE_TEST_ID),
                Block128::from(13u128),
                [Block128::from(99u128), mint_owner[1]],
            ),
        ];
        for (case, (r1cs, witness)) in cases.into_iter().enumerate() {
            assert!(
                !r1cs.satisfies(&witness),
                "mixed exact-state component case {case} must reject"
            );
        }
    }

    fn structural_fixture(seed: u128) -> ExactStateStructuralFrontierInputs {
        structural_fixture_for_indices(seed, vec![1, 2, 11], 4)
    }

    fn structural_fixture_for_indices(
        seed: u128,
        touched_indices: Vec<u32>,
        active_depth: u32,
    ) -> ExactStateStructuralFrontierInputs {
        let old_slot_leaves = (0..touched_indices.len())
            .map(|ordinal| structural_slot_leaf(seed + ordinal as u128))
            .collect::<Vec<_>>();
        let new_slot_leaves = (0..touched_indices.len())
            .map(|ordinal| structural_slot_leaf(seed + 100 + ordinal as u128))
            .collect::<Vec<_>>();
        let plan = derive_structural_frontier_plan(&touched_indices, active_depth).unwrap();
        let live_sibling_digests = (0..plan.frontier_positions().len())
            .map(|ordinal| {
                slot_leaf_hash(SlotValue {
                    value: Block128::from(seed + 1_000 + ordinal as u128),
                    owner_hi: Block128::from(seed + 2_000 + ordinal as u128),
                    owner_lo: Block128::from(seed + 3_000 + ordinal as u128),
                })
            })
            .collect::<Vec<_>>();
        let old_hashes = old_slot_leaves
            .iter()
            .map(|leaf| fields_to_state_hash(leaf.expected_leaf))
            .collect::<Vec<_>>();
        let new_hashes = new_slot_leaves
            .iter()
            .map(|leaf| fields_to_state_hash(leaf.expected_leaf))
            .collect::<Vec<_>>();
        let old_evaluation =
            evaluate_structural_frontier(&plan, &old_hashes, &live_sibling_digests).unwrap();
        let new_evaluation =
            evaluate_structural_frontier(&plan, &new_hashes, &live_sibling_digests).unwrap();
        ExactStateStructuralFrontierInputs {
            touched_indices,
            active_depth,
            old_slot_leaves,
            new_slot_leaves,
            live_sibling_digests,
            old_combine_digests: old_evaluation.combines,
            new_combine_digests: new_evaluation.combines,
            old_root: old_evaluation.root,
            new_root: new_evaluation.root,
        }
    }

    fn paired_iv_flat() -> [F128; 2] {
        let iv = capacity_iv(TAG_EXSTNOD);
        [flat_of(iv[0]), flat_of(iv[1])]
    }

    fn assert_paired_endpoints(
        data: &ExactStatePairedRegionData,
        inputs: &ExactStateStructuralFrontierInputs,
    ) {
        let segmented =
            derive_exact_state_segmented_updates(inputs, PAIRED_UPDATE_DEPTH as u32).unwrap();
        let packed = data.packed_updates();
        let columns = super::super::paired_merkle_update::build_paired_merkle_update_columns(
            &packed.updates,
            paired_iv_flat(),
            packed.w_log,
        );

        for (index, update) in segmented.local_updates.iter().enumerate() {
            assert_eq!(
                columns.update_roots_at_depth(index, PAIRED_UPDATE_DEPTH),
                (
                    flat_state_hash(update.root_before),
                    flat_state_hash(update.root_after),
                )
            );
        }
        for (index, update) in segmented.segment_updates.iter().enumerate() {
            assert_eq!(
                columns
                    .update_roots_at_depth(data.touched_capacity + index, data.active_upper_depth,),
                (
                    flat_state_hash(update.root_before),
                    flat_state_hash(update.root_after),
                )
            );
        }
    }

    #[test]
    fn paired_region_preserves_chains_counts_and_capacity_partition_padding() {
        let inputs = structural_fixture_for_indices(201, vec![1, 2, (1 << 16) + 3], 24);
        let segmented =
            derive_exact_state_segmented_updates(&inputs, PAIRED_UPDATE_DEPTH as u32).unwrap();
        let data = ExactStatePairedRegionData::new(&inputs, 5, 4).unwrap();

        assert_eq!(data.local_update_count, 3);
        assert_eq!(data.upper_update_count, 2);
        assert_eq!(data.local_updates.len(), data.local_update_count);
        assert_eq!(data.upper_updates.len(), data.upper_update_count);
        assert_eq!(data.active_upper_depth, 8);
        assert_eq!(
            segmented.local_updates[0].root_after,
            segmented.local_updates[1].root_before
        );
        assert_eq!(
            segmented.segment_updates[0].root_after,
            segmented.segment_updates[1].root_before
        );

        let packed = data.packed_updates();
        assert_eq!(packed.updates.len(), 9);
        assert_eq!(packed.active_slots, 9 * PAIRED_UPDATE_STRIDE);
        assert_eq!(packed.slots, 1 << 10);
        assert_eq!(packed.w_log, 10);
        assert_eq!(&packed.updates[..3], data.local_updates.as_slice());
        assert!(packed.updates[3..5]
            .iter()
            .all(|update| *update == local_empty_ghost()));
        assert_eq!(&packed.updates[5..7], data.upper_updates.as_slice());
        assert!(packed.updates[7..]
            .iter()
            .all(|update| *update == PairedMerkleUpdateWitness::canonical_ghost()));
        assert_paired_endpoints(&data, &inputs);
    }

    #[test]
    fn paired_local_padding_uses_empty_leaf_digest_but_upper_padding_uses_zero_entry() {
        let inputs = structural_fixture_for_indices(251, vec![7], 24);
        let data = ExactStatePairedRegionData::new(&inputs, 2, 2).unwrap();
        let packed = data.packed_updates();
        let empty_leaf = flat_state_hash(slot_leaf_hash(SlotValue::EMPTY));
        let local_ghost = &packed.updates[1];
        let upper_ghost = &packed.updates[3];

        assert_eq!(local_ghost, &local_empty_ghost());
        assert_eq!(local_ghost.old_entry, empty_leaf);
        assert_eq!(local_ghost.new_entry, empty_leaf);
        assert_ne!(empty_leaf, [F128::ZERO; 2]);
        assert!(local_ghost
            .siblings
            .iter()
            .all(|sibling| *sibling == [F128::ZERO; 2]));
        assert!(local_ghost.directions.iter().all(|&direction| !direction));

        assert_eq!(upper_ghost, &PairedMerkleUpdateWitness::canonical_ghost());
        assert_eq!(upper_ghost.old_entry, [F128::ZERO; 2]);
        assert_ne!(local_ghost, upper_ghost);
    }

    fn structural_region_slot_case(
        inputs: &ExactStateStructuralFrontierInputs,
        touched_capacity: usize,
        segment_capacity: usize,
    ) -> (FieldR1cs, Vec<F128>, [F128; 2], [F128; 2]) {
        let mut b = FieldR1csBuilder::new();
        let (slot, region) = build_exact_state_structural_region_slot(
            &mut b,
            inputs,
            touched_capacity,
            segment_capacity,
        )
        .unwrap();
        assert_eq!(
            region.paired.local_update_count,
            inputs.touched_indices.len()
        );
        assert_eq!(slot.slot_leaves.len(), 2 * touched_capacity);
        let old_pad = slot.slot_leaves[touched_capacity - 1].expected_leaf.clone();
        let new_pad = slot.slot_leaves[2 * touched_capacity - 1]
            .expected_leaf
            .clone();
        let old_pad = [old_pad[0].eval(b.values()), old_pad[1].eval(b.values())];
        let new_pad = [new_pad[0].eval(b.values()), new_pad[1].eval(b.values())];
        let (r1cs, witness) = b.build();
        (r1cs, witness, old_pad, new_pad)
    }

    #[test]
    fn structural_region_slot_has_no_paths_and_empty_fixed_padding() {
        let inputs = structural_fixture_for_indices(281, vec![1, 2, (1 << 16) + 3], 24);
        let (r1cs, witness, old_pad, new_pad) = structural_region_slot_case(&inputs, 5, 4);
        assert!(r1cs.satisfies(&witness));
        let empty = flat_state_hash(slot_leaf_hash(SlotValue::EMPTY));
        assert_eq!(old_pad, empty);
        assert_eq!(new_pad, empty);
    }

    #[test]
    fn structural_region_slot_matrix_is_count_topology_and_depth_invariant() {
        let sparse = structural_fixture_for_indices(301, vec![7], 24);
        let dispersed =
            structural_fixture_for_indices(401, vec![1, (1 << 16) + 3, (3 << 16) + 5], 32);
        let (left, left_witness, _, _) = structural_region_slot_case(&sparse, 5, 4);
        let (right, right_witness, _, _) = structural_region_slot_case(&dispersed, 5, 4);
        assert!(left.satisfies(&left_witness));
        assert!(right.satisfies(&right_witness));
        assert_eq!(left.useful_rows, right.useful_rows);
        assert_eq!(left.statement_digest(), right.statement_digest());
    }

    #[test]
    fn paired_depth24_selects_upper_endpoint_at_depth8_and_pads_canonical_growth() {
        let inputs = structural_fixture_for_indices(301, vec![7, (3 << 16) + 9], 24);
        let data = ExactStatePairedRegionData::new(&inputs, 2, 2).unwrap();
        assert_eq!(data.active_upper_depth, 8);

        let zero_roots = zero_slot_roots(31);
        for update in &data.upper_updates {
            for level in data.active_upper_depth..PAIRED_UPDATE_DEPTH {
                assert_eq!(
                    update.siblings[level],
                    flat_state_hash(zero_roots[PAIRED_UPDATE_DEPTH + level])
                );
                assert!(!update.directions[level]);
            }
        }
        assert_paired_endpoints(&data, &inputs);
    }

    #[test]
    fn paired_depth32_selects_upper_endpoint_at_depth16_without_padding() {
        let inputs = structural_fixture_for_indices(401, vec![11, (7 << 16) + 13], 32);
        let data = ExactStatePairedRegionData::new(&inputs, 2, 2).unwrap();
        assert_eq!(data.active_upper_depth, 16);

        let segmented =
            derive_exact_state_segmented_updates(&inputs, PAIRED_UPDATE_DEPTH as u32).unwrap();
        for (witness, update) in data.upper_updates.iter().zip(&segmented.segment_updates) {
            for level in 0..PAIRED_UPDATE_DEPTH {
                assert_eq!(
                    witness.siblings[level],
                    flat_state_hash(update.siblings[level])
                );
                assert_eq!(witness.directions[level], update.directions[level]);
            }
        }
        assert_paired_endpoints(&data, &inputs);
    }

    #[test]
    fn paired_region_rejects_undersized_fixed_capacities() {
        let inputs = structural_fixture_for_indices(501, vec![1, 2, (1 << 16) + 3], 24);
        assert_eq!(
            ExactStatePairedRegionData::new(&inputs, 2, 2).unwrap_err(),
            ExactStatePairedRegionError::TouchedCapacityExceeded {
                required: 3,
                capacity: 2,
            }
        );
        assert_eq!(
            ExactStatePairedRegionData::new(&inputs, 3, 1).unwrap_err(),
            ExactStatePairedRegionError::SegmentCapacityExceeded {
                required: 2,
                capacity: 1,
            }
        );
    }

    #[test]
    fn paired_b255_capacities_fit_one_depth17_walk() {
        const TOUCHED_CAPACITY: usize = 1_531;
        const SEGMENT_CAPACITY: usize = 256;
        let ghost = PairedMerkleUpdateWitness::canonical_ghost();
        let data = ExactStatePairedRegionData {
            local_updates: vec![ghost.clone(); TOUCHED_CAPACITY],
            upper_updates: vec![ghost; SEGMENT_CAPACITY],
            local_update_count: TOUCHED_CAPACITY,
            upper_update_count: SEGMENT_CAPACITY,
            touched_capacity: TOUCHED_CAPACITY,
            segment_capacity: SEGMENT_CAPACITY,
            active_upper_depth: PAIRED_UPDATE_DEPTH,
        };
        let packed = data.packed_updates();
        assert_eq!(packed.updates.len(), TOUCHED_CAPACITY + SEGMENT_CAPACITY);
        assert_eq!(
            packed.active_slots,
            (TOUCHED_CAPACITY + SEGMENT_CAPACITY) * PAIRED_UPDATE_STRIDE
        );
        assert_eq!(packed.slots, 1 << 17);
        assert_eq!(packed.w_log, 17);
    }

    fn eval_pair(b: &FieldR1csBuilder, pair: &[LinExpr; 2]) -> [F128; 2] {
        [pair[0].eval(b.values()), pair[1].eval(b.values())]
    }

    fn frontier_count_circuit(
        indices: &[u32],
        capacity: usize,
        depth: usize,
        claimed: usize,
    ) -> (FieldR1cs, Vec<F128>, usize, usize) {
        assert!(indices.len() <= capacity);
        let mut b = FieldR1csBuilder::new();
        let mut actions = Vec::with_capacity(capacity);
        for row in 0..capacity {
            let live = LinExpr::from_wire(b.alloc_bool(row < indices.len()));
            let slot = alloc_block(
                &mut b,
                Block128::from(indices.get(row).copied().unwrap_or(0) as u128),
            );
            actions.push(ActionRowTrace {
                live,
                slot_index: slot,
                value: LinExpr::zero(),
                owner: [LinExpr::zero(), LinExpr::zero()],
                is_mint: LinExpr::zero(),
            });
        }
        let compacted = compact_action_rows(&mut b, &actions, capacity);
        let count = alloc_block(&mut b, Block128::from(claimed as u128));
        let binding_start = b.num_wires();
        bind_structural_frontier_count_from_actions(
            &mut b,
            &compacted.rows,
            &compacted.slot_bits,
            &compacted.adjacent_msb_one_hot,
            depth,
            &count,
        );
        let rows = b.num_wires();
        let binding_rows = rows - binding_start;
        let (r1cs, witness) = b.build();
        (r1cs, witness, rows, binding_rows)
    }

    #[test]
    fn frontier_count_is_derived_from_sorted_action_bits() {
        for indices in [
            vec![0],
            vec![0, 1],
            vec![0, 3, 7],
            vec![1, 2, 8, 14],
            vec![0, 2, 4, 6, 8, 10, 12, 14],
        ] {
            let expected = expected_sibling_count(&indices, 4).unwrap();
            let (r1cs, witness, _, _) = frontier_count_circuit(&indices, 8, 4, expected);
            assert!(r1cs.satisfies(&witness), "indices={indices:?}");
        }
    }

    #[test]
    fn frontier_count_rejects_tampering_and_out_of_range_slots() {
        let indices = [0, 3, 7];
        let expected = expected_sibling_count(&indices, 4).unwrap();
        let (bad_count, bad_count_witness, _, _) =
            frontier_count_circuit(&indices, 8, 4, expected + 1);
        assert!(!bad_count.satisfies(&bad_count_witness));

        let (out_of_range, out_of_range_witness, _, _) = frontier_count_circuit(&[0, 16], 8, 4, 0);
        assert!(!out_of_range.satisfies(&out_of_range_witness));
    }

    #[test]
    fn frontier_count_matrix_is_topology_and_occupancy_invariant() {
        let clustered = [0, 1, 2];
        let dispersed = [0, 5, 10, 15];
        let clustered_count = expected_sibling_count(&clustered, 4).unwrap();
        let dispersed_count = expected_sibling_count(&dispersed, 4).unwrap();
        let (clustered_r1cs, clustered_witness, clustered_rows, clustered_binding) =
            frontier_count_circuit(&clustered, 8, 4, clustered_count);
        let (dispersed_r1cs, dispersed_witness, dispersed_rows, dispersed_binding) =
            frontier_count_circuit(&dispersed, 8, 4, dispersed_count);

        assert!(clustered_r1cs.satisfies(&clustered_witness));
        assert!(dispersed_r1cs.satisfies(&dispersed_witness));
        assert_eq!(clustered_rows, dispersed_rows);
        assert_eq!(clustered_binding, dispersed_binding);
        assert_eq!(
            clustered_r1cs.statement_digest(),
            dispersed_r1cs.statement_digest()
        );
    }

    fn dynamic_frontier_count_circuit(
        indices: &[u32],
        capacity: usize,
        depth: usize,
        claimed: usize,
    ) -> (FieldR1cs, Vec<F128>) {
        assert!(indices.len() <= capacity);
        let mut b = FieldR1csBuilder::new();
        let mut actions = Vec::with_capacity(capacity);
        for row in 0..capacity {
            let live = LinExpr::from_wire(b.alloc_bool(row < indices.len()));
            let slot = alloc_block(
                &mut b,
                Block128::from(indices.get(row).copied().unwrap_or(0) as u128),
            );
            actions.push(ActionRowTrace {
                live,
                slot_index: slot,
                value: LinExpr::zero(),
                owner: [LinExpr::zero(), LinExpr::zero()],
                is_mint: LinExpr::zero(),
            });
        }
        let compacted = compact_action_rows(&mut b, &actions, capacity);
        let depth_value = alloc_block(&mut b, Block128::from(depth as u128));
        let depth = StateDepthTrace::bind(&mut b, &depth_value);
        let count = alloc_block(&mut b, Block128::from(claimed as u128));
        bind_structural_frontier_count_from_actions_dynamic(
            &mut b,
            &compacted.rows,
            &compacted.slot_bits,
            &compacted.adjacent_msb_one_hot,
            &depth,
            &count,
        );
        b.build()
    }

    #[test]
    fn dynamic_frontier_count_has_one_matrix_for_depth24_and_depth32() {
        let indices = [1, 3, 7, 15];
        let count24 = expected_sibling_count(&indices, 24).unwrap();
        let count32 = expected_sibling_count(&indices, 32).unwrap();
        let (depth24, witness24) = dynamic_frontier_count_circuit(&indices, 8, 24, count24);
        let (depth32, witness32) = dynamic_frontier_count_circuit(&indices, 8, 32, count32);

        assert!(depth24.satisfies(&witness24));
        assert!(depth32.satisfies(&witness32));
        assert_eq!(depth24.useful_rows, depth32.useful_rows);
        assert_eq!(depth24.statement_digest(), depth32.statement_digest());
    }

    #[test]
    fn dynamic_frontier_count_rejects_a_slot_above_selected_depth() {
        let (r1cs, witness) = dynamic_frontier_count_circuit(&[0, 1 << 24], 4, 24, 0);
        assert!(!r1cs.satisfies(&witness));
    }

    #[test]
    fn b255_frontier_count_binding_stays_below_one_hundred_thousand_rows() {
        const TOUCHED: usize = 1_531;
        let mut indices = Vec::with_capacity(TOUCHED);
        for segment_rank in 0..256usize {
            let segment = (segment_rank as u32).reverse_bits() >> 16;
            let local_count = if segment_rank < 251 { 6 } else { 5 };
            for local_rank in 0..local_count {
                let local = (local_rank as u32).reverse_bits() >> 16;
                indices.push((segment << 16) | local);
            }
        }
        indices.sort_unstable();
        let expected = expected_sibling_count(&indices, 32).unwrap();
        assert_eq!(expected, 22_468);
        let (r1cs, witness, _, binding_rows) =
            frontier_count_circuit(&indices, TOUCHED, 32, expected);
        assert!(r1cs.satisfies(&witness));
        assert_eq!(binding_rows, 30_628);
    }

    #[test]
    fn structural_preparation_is_content_invariant_at_one_shape() {
        let first = structural_fixture(7);
        let second = structural_fixture(70_000);
        let live = derive_structural_frontier_plan(&first.touched_indices, first.active_depth)
            .unwrap()
            .combines()
            .len();
        let capacity = live + 3;

        let mut b_first = FieldR1csBuilder::new();
        let prepared_first =
            prepare_exact_state_structural_region(&mut b_first, &first, capacity).unwrap();
        let rows_first = b_first.num_wires();
        let (r1cs_first, witness_first) = b_first.build();

        let mut b_second = FieldR1csBuilder::new();
        let prepared_second =
            prepare_exact_state_structural_region(&mut b_second, &second, capacity).unwrap();
        let rows_second = b_second.num_wires();
        let (r1cs_second, witness_second) = b_second.build();

        assert_eq!(rows_first, rows_second);
        assert_eq!(
            r1cs_first.statement_digest(),
            r1cs_second.statement_digest(),
            "digest content must not change preparation shape"
        );
        assert!(r1cs_first.satisfies(&witness_first));
        assert!(r1cs_second.satisfies(&witness_second));
        assert_eq!(prepared_first.live_combine_count, live);
        assert_eq!(prepared_second.live_combine_count, live);
        assert_eq!(prepared_first.old_combines.len(), capacity);
        assert_eq!(prepared_second.new_combines.len(), capacity);
    }

    #[test]
    fn structural_preparation_shape_is_invariant_across_frontier_topology() {
        let clustered = structural_fixture_for_indices(81, vec![0, 1, 2], 4);
        let dispersed = structural_fixture_for_indices(91, vec![0, 5, 10], 4);
        let clustered_live =
            derive_structural_frontier_plan(&clustered.touched_indices, clustered.active_depth)
                .unwrap()
                .combines()
                .len();
        let dispersed_live =
            derive_structural_frontier_plan(&dispersed.touched_indices, dispersed.active_depth)
                .unwrap()
                .combines()
                .len();
        assert_ne!(clustered_live, dispersed_live);
        let capacity = clustered_live.max(dispersed_live) + 2;

        let mut b_clustered = FieldR1csBuilder::new();
        let clustered_prepared =
            prepare_exact_state_structural_region(&mut b_clustered, &clustered, capacity).unwrap();
        let clustered_rows = b_clustered.num_wires();
        let (clustered_r1cs, clustered_witness) = b_clustered.build();

        let mut b_dispersed = FieldR1csBuilder::new();
        let dispersed_prepared =
            prepare_exact_state_structural_region(&mut b_dispersed, &dispersed, capacity).unwrap();
        let dispersed_rows = b_dispersed.num_wires();
        let (dispersed_r1cs, dispersed_witness) = b_dispersed.build();

        assert_eq!(clustered_rows, dispersed_rows);
        assert_eq!(
            clustered_r1cs.statement_digest(),
            dispersed_r1cs.statement_digest()
        );
        assert!(clustered_r1cs.satisfies(&clustered_witness));
        assert!(dispersed_r1cs.satisfies(&dispersed_witness));
        assert_ne!(
            clustered_prepared.live_sibling_count,
            dispersed_prepared.live_sibling_count
        );
        assert_eq!(
            clustered_prepared.shared_sibling_frontier.len(),
            dispersed_prepared.shared_sibling_frontier.len()
        );
    }

    #[test]
    fn structural_preparation_allocates_aligned_leaves_shared_frontier_and_ghost_pad() {
        let inputs = structural_fixture(11);
        let plan =
            derive_structural_frontier_plan(&inputs.touched_indices, inputs.active_depth).unwrap();
        let live = plan.combines().len();
        let capacity = live + 2;
        let mut b = FieldR1csBuilder::new();
        let prepared = prepare_exact_state_structural_region(&mut b, &inputs, capacity).unwrap();

        assert_eq!(prepared.touched_leaves.len(), inputs.touched_indices.len());
        for (row, &slot_index) in prepared
            .touched_leaves
            .iter()
            .zip(inputs.touched_indices.iter())
        {
            assert_eq!(
                row.slot_index.eval(b.values()),
                flat_of(Block128::from(slot_index as u128))
            );
        }
        assert_eq!(prepared.shared_sibling_frontier.len(), capacity);
        assert_eq!(
            prepared.live_sibling_count,
            inputs.live_sibling_digests.len()
        );
        for (wires, &digest) in prepared
            .shared_sibling_frontier
            .iter()
            .zip(inputs.live_sibling_digests.iter())
        {
            let fields = digest_to_fields(digest);
            assert_eq!(
                eval_pair(&b, wires),
                [flat_of(fields[0]), flat_of(fields[1])]
            );
        }
        for wires in &prepared.shared_sibling_frontier[prepared.live_sibling_count..] {
            assert_eq!(eval_pair(&b, wires), [F128::ZERO; 2]);
        }

        let verified = verify_exact_state_structural_frontier(&inputs).unwrap();
        let old_hashes = inputs
            .old_slot_leaves
            .iter()
            .map(|leaf| fields_to_state_hash(leaf.expected_leaf))
            .collect::<Vec<_>>();
        let old_expected = structural_combine_values(
            &verified.plan,
            &old_hashes,
            &inputs.live_sibling_digests,
            &verified.old_evaluation,
        );
        for (tuple, &(left, right, parent)) in prepared.old_combines[..live]
            .iter()
            .zip(old_expected.iter())
        {
            let left = digest_to_fields(left);
            let right = digest_to_fields(right);
            let parent = digest_to_fields(parent);
            assert_eq!(
                eval_pair(&b, &tuple.left),
                [flat_of(left[0]), flat_of(left[1])]
            );
            assert_eq!(
                eval_pair(&b, &tuple.right),
                [flat_of(right[0]), flat_of(right[1])]
            );
            assert_eq!(
                eval_pair(&b, &tuple.parent),
                [flat_of(parent[0]), flat_of(parent[1])]
            );
        }

        let ghost_parent = digest_to_fields(state_node_hash(
            STRUCTURAL_FRONTIER_PAD,
            STRUCTURAL_FRONTIER_PAD,
        ));
        let ghost_parent = [flat_of(ghost_parent[0]), flat_of(ghost_parent[1])];
        for half in [&prepared.old_combines, &prepared.new_combines] {
            assert!(half[..live].iter().all(|tuple| tuple.is_live));
            for tuple in &half[live..] {
                assert!(!tuple.is_live);
                assert_eq!(eval_pair(&b, &tuple.left), [F128::ZERO; 2]);
                assert_eq!(eval_pair(&b, &tuple.right), [F128::ZERO; 2]);
                assert_eq!(eval_pair(&b, &tuple.parent), ghost_parent);
            }
        }
    }

    #[test]
    fn structural_preparation_rejects_tamper_and_undersized_capacity_before_allocating() {
        let inputs = structural_fixture(19);
        let live = derive_structural_frontier_plan(&inputs.touched_indices, inputs.active_depth)
            .unwrap()
            .combines()
            .len();

        let mut bad_root = inputs.clone();
        bad_root.new_root[0] ^= 1;
        let mut b = FieldR1csBuilder::new();
        let before = b.num_wires();
        assert!(matches!(
            prepare_exact_state_structural_region(&mut b, &bad_root, live),
            Err(ExactStateStructuralPreparationError::Structural(
                ExactStateStructuralFrontierError::NewRootMismatch
            ))
        ));
        assert_eq!(b.num_wires(), before);

        let mut short_frontier = inputs.clone();
        short_frontier.live_sibling_digests.pop();
        let mut b = FieldR1csBuilder::new();
        let before = b.num_wires();
        assert!(matches!(
            prepare_exact_state_structural_region(&mut b, &short_frontier, live),
            Err(ExactStateStructuralPreparationError::Structural(
                ExactStateStructuralFrontierError::SparseMerkle(
                    SparseMerkleError::ProofLengthMismatch { .. }
                )
            ))
        ));
        assert_eq!(b.num_wires(), before);

        let mut b = FieldR1csBuilder::new();
        let before = b.num_wires();
        assert_eq!(
            prepare_exact_state_structural_region(&mut b, &inputs, live - 1).err(),
            Some(
                ExactStateStructuralPreparationError::CombineCapacityExceeded {
                    required: live,
                    capacity: live - 1,
                }
            )
        );
        assert_eq!(b.num_wires(), before);
    }

    #[test]
    fn live_zero_sibling_is_not_confused_with_ghost_suffix() {
        let touched_indices = vec![0];
        let active_depth = 1;
        let old_slot_leaves = vec![structural_slot_leaf(31)];
        let new_slot_leaves = vec![structural_slot_leaf(32)];
        let live_sibling_digests = vec![STRUCTURAL_FRONTIER_PAD];
        let plan = derive_structural_frontier_plan(&touched_indices, active_depth).unwrap();
        let old_hash = fields_to_state_hash(old_slot_leaves[0].expected_leaf);
        let new_hash = fields_to_state_hash(new_slot_leaves[0].expected_leaf);
        let old_evaluation =
            evaluate_structural_frontier(&plan, &[old_hash], &[STRUCTURAL_FRONTIER_PAD]).unwrap();
        let new_evaluation =
            evaluate_structural_frontier(&plan, &[new_hash], &[STRUCTURAL_FRONTIER_PAD]).unwrap();
        let inputs = ExactStateStructuralFrontierInputs {
            touched_indices,
            active_depth,
            old_slot_leaves,
            new_slot_leaves,
            live_sibling_digests,
            old_combine_digests: old_evaluation.combines,
            new_combine_digests: new_evaluation.combines,
            old_root: old_evaluation.root,
            new_root: new_evaluation.root,
        };
        let mut b = FieldR1csBuilder::new();
        let prepared = prepare_exact_state_structural_region(&mut b, &inputs, 2).unwrap();
        assert_eq!(prepared.live_combine_count, 1);
        assert_eq!(prepared.live_sibling_count, 1);
        assert_eq!(prepared.shared_sibling_frontier.len(), 2);
        assert_eq!(
            eval_pair(&b, &prepared.shared_sibling_frontier[0]),
            [F128::ZERO; 2]
        );
        assert!(prepared.old_combines[0].is_live);
        assert!(!prepared.old_combines[1].is_live);
    }

    fn root_wires(
        b: &mut FieldR1csBuilder,
        old: [Block128; 2],
        new: [Block128; 2],
        depth: usize,
    ) -> ExactStateRootWires {
        ExactStateRootWires {
            old_root: std::array::from_fn(|i| alloc_block(b, old[i])),
            new_root: std::array::from_fn(|i| alloc_block(b, new[i])),
            active_depth: depth,
        }
    }

    struct BindingCase {
        r1cs: FieldR1cs,
        z: Vec<Field>,
        parent_root: [usize; 2],
        old_root: [usize; 2],
        new_root: [usize; 2],
        child_root: [usize; 2],
        parent_log: usize,
        child_log: usize,
        grow: usize,
    }

    fn wire(expr: &LinExpr) -> usize {
        expr.terms[0].0 as usize
    }

    fn binding_case(grows: bool) -> BindingCase {
        const CHILD_DEPTH: usize = 5;
        let parent_digest = [7u8; 32];
        let parent = digest_to_fields(parent_digest);
        let zeros = zero_slot_roots(CHILD_DEPTH - 1);
        let old = if grows {
            digest_to_fields(state_node_hash(parent_digest, zeros[CHILD_DEPTH - 1]))
        } else {
            parent
        };
        let child = [Block128::from(31u128), Block128::from(32u128)];
        let mut b = FieldR1csBuilder::new();
        let roots = root_wires(&mut b, old, child, CHILD_DEPTH);
        let parent_w = std::array::from_fn(|i| alloc_block(&mut b, parent[i]));
        let child_w = std::array::from_fn(|i| alloc_block(&mut b, child[i]));
        let parent_depth = CHILD_DEPTH - usize::from(grows);
        let parent_log = alloc_block(&mut b, Block128::from(parent_depth as u128));
        let child_log = alloc_block(&mut b, Block128::from(CHILD_DEPTH as u128));
        let grow = bind_exact_state_header_roots(
            &mut b,
            &roots,
            &parent_w,
            &parent_log,
            parent_depth as u32,
            &child_w,
            &child_log,
        );
        let parent_root = std::array::from_fn(|lane| wire(&parent_w[lane]));
        let old_root = std::array::from_fn(|lane| wire(&roots.old_root[lane]));
        let new_root = std::array::from_fn(|lane| wire(&roots.new_root[lane]));
        let child_root = std::array::from_fn(|lane| wire(&child_w[lane]));
        let parent_log = wire(&parent_log);
        let child_log = wire(&child_log);
        let grow = wire(&grow);
        let (r1cs, z) = b.build();
        BindingCase {
            r1cs,
            z,
            parent_root,
            old_root,
            new_root,
            child_root,
            parent_log,
            child_log,
            grow,
        }
    }

    #[test]
    fn equal_and_grow_share_one_child_depth_matrix() {
        let equal = binding_case(false);
        let grow = binding_case(true);
        assert!(equal.r1cs.satisfies(&equal.z));
        assert!(grow.r1cs.satisfies(&grow.z));
        assert_eq!(
            equal.r1cs.statement_digest(),
            grow.r1cs.statement_digest(),
            "grow selector must not change the child-depth matrix"
        );
    }

    #[test]
    fn root_depth_grow_and_zero_subtree_tamper_reject() {
        for grows in [false, true] {
            let case = binding_case(grows);
            assert!(case.r1cs.satisfies(&case.z));
            for (wire, label) in [
                (case.parent_root[0], "parent header root lane 0"),
                (case.parent_root[1], "parent header root lane 1"),
                (case.old_root[0], "old path root lane 0"),
                (case.old_root[1], "old path root lane 1"),
                (case.new_root[0], "new path root lane 0"),
                (case.new_root[1], "new path root lane 1"),
                (case.child_root[0], "child header root lane 0"),
                (case.child_root[1], "child header root lane 1"),
                (case.parent_log, "parent depth"),
                (case.child_log, "child depth"),
                (case.grow, "grow selector"),
            ] {
                let mut bad = case.z.clone();
                bad[wire] += Field::ONE;
                assert!(
                    !case.r1cs.satisfies(&bad),
                    "{label} tamper must fail in grows={grows} branch"
                );
            }
        }
    }

    struct DynamicBindingCase {
        r1cs: FieldR1cs,
        z: Vec<Field>,
        old_root: [usize; 2],
        grow: usize,
    }

    fn dynamic_binding_case(parent_depth: usize, child_depth: usize) -> DynamicBindingCase {
        let parent_digest = [0xA7u8; 32];
        let parent = digest_to_fields(parent_digest);
        let old = if child_depth == parent_depth + 1
            && (MIN_EXACT_STATE_DEPTH..MAX_EXACT_STATE_DEPTH).contains(&parent_depth)
        {
            let zeros = zero_slot_roots(parent_depth);
            digest_to_fields(state_node_hash(parent_digest, zeros[parent_depth]))
        } else {
            parent
        };
        let child = [Block128::from(71u128), Block128::from(72u128)];
        let mut b = FieldR1csBuilder::new();
        // Deliberately irrelevant: the dynamic binder must not consult this
        // native/class field as proof authority.
        let roots = root_wires(&mut b, old, child, 0);
        let parent_w = std::array::from_fn(|lane| alloc_block(&mut b, parent[lane]));
        let child_w = std::array::from_fn(|lane| alloc_block(&mut b, child[lane]));
        let parent_log = alloc_block(&mut b, Block128::from(parent_depth as u128));
        let child_log = alloc_block(&mut b, Block128::from(child_depth as u128));
        let depth = bind_exact_state_header_roots_dynamic(
            &mut b,
            &roots,
            &parent_w,
            &parent_log,
            &child_w,
            &child_log,
        );
        let old_root = std::array::from_fn(|lane| wire(&roots.old_root[lane]));
        let grow = wire(&depth.grow);
        let (r1cs, z) = b.build();
        DynamicBindingCase {
            r1cs,
            z,
            old_root,
            grow,
        }
    }

    #[test]
    fn dynamic_root_depth_accepts_equal_and_grow_with_one_matrix() {
        let equal24 = dynamic_binding_case(24, 24);
        let grow24 = dynamic_binding_case(24, 25);
        let grow31 = dynamic_binding_case(31, 32);
        let equal32 = dynamic_binding_case(32, 32);

        assert!(equal24.r1cs.satisfies(&equal24.z));
        assert!(grow24.r1cs.satisfies(&grow24.z));
        assert!(grow31.r1cs.satisfies(&grow31.z));
        assert!(equal32.r1cs.satisfies(&equal32.z));
        assert_eq!(equal24.z[equal24.grow], Field::ZERO);
        assert_eq!(grow24.z[grow24.grow], Field::ONE);
        assert_eq!(grow31.z[grow31.grow], Field::ONE);
        assert_eq!(equal32.z[equal32.grow], Field::ZERO);
        assert_eq!(equal24.r1cs.useful_rows, grow24.r1cs.useful_rows);
        assert_eq!(
            equal24.r1cs.statement_digest(),
            grow24.r1cs.statement_digest()
        );
        assert_eq!(
            equal24.r1cs.statement_digest(),
            equal32.r1cs.statement_digest(),
            "depth 24 and depth 32 must use the same root/depth statement"
        );

        for lane in 0..2 {
            let mut tampered = grow24.z.clone();
            tampered[grow24.old_root[lane]] += Field::ONE;
            assert!(
                !grow24.r1cs.satisfies(&tampered),
                "canonical grow-root lane {lane} must be bound"
            );
        }
    }

    #[test]
    fn dynamic_root_depth_rejects_gap_shrink_and_out_of_range() {
        for (parent, child, label) in [
            (24, 26, "gap"),
            (25, 24, "shrink"),
            (23, 24, "parent below range"),
            (32, 33, "child above range"),
        ] {
            let case = dynamic_binding_case(parent, child);
            assert!(
                !case.r1cs.satisfies(&case.z),
                "{label} transition {parent}->{child} must reject"
            );
        }
    }

    fn upper_selector_case(depth: usize) -> (FieldR1cs, Vec<F128>, [[F128; 2]; 2]) {
        let mut b = FieldR1csBuilder::new();
        let depth_value = alloc_block(&mut b, Block128::from(depth as u128));
        let depth = StateDepthTrace::bind(&mut b, &depth_value);
        let roots_by_depth: [PairedRootCellPair; PAIRED_UPDATE_DEPTH] =
            std::array::from_fn(|index| {
                std::array::from_fn(|side| {
                    std::array::from_fn(|lane| {
                        alloc_block(
                            &mut b,
                            Block128::from(
                                10_000 * (index + 1) as u128 + 100 * side as u128 + lane as u128,
                            ),
                        )
                    })
                })
            });
        let selected = select_upper_paired_roots(&mut b, &depth, &roots_by_depth);
        let selected_value = std::array::from_fn(|side| {
            std::array::from_fn(|lane| selected[side][lane].eval(b.values()))
        });
        let (r1cs, witness) = b.build();
        (r1cs, witness, selected_value)
    }

    #[test]
    fn upper_root_selector_chooses_depth8_and_depth16_with_one_matrix() {
        let (depth24, witness24, selected8) = upper_selector_case(24);
        let (depth32, witness32, selected16) = upper_selector_case(32);
        assert!(depth24.satisfies(&witness24));
        assert!(depth32.satisfies(&witness32));
        assert_eq!(
            selected8,
            std::array::from_fn(|side| {
                std::array::from_fn(|lane| {
                    flat_of(Block128::from(80_000 + 100 * side as u128 + lane as u128))
                })
            })
        );
        assert_eq!(
            selected16,
            std::array::from_fn(|side| {
                std::array::from_fn(|lane| {
                    flat_of(Block128::from(160_000 + 100 * side as u128 + lane as u128))
                })
            })
        );
        assert_eq!(depth24.useful_rows, depth32.useful_rows);
        assert_eq!(depth24.statement_digest(), depth32.statement_digest());
    }
}
