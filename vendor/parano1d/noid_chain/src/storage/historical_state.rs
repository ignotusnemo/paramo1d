// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Bounded-memory reconstruction of a recent canonical state boundary.
//!
//! The durable segment table always belongs to the current canonical tip.  A
//! snapshot export may nevertheless need the parent state of a retained block.
//! This module rolls the compact current-tip [`ChainState`] metadata backwards
//! through the retained undo journal from one stable MDBX MVCC snapshot,
//! without blocking a concurrent canonical writer or scanning untouched state
//! payloads. Undo pre-images are grouped by segment, and every non-required
//! segment is decoded, rolled back, exact-summarized, and evicted before the
//! next payload is read.
//!
//! This is deliberately an **exact-state-only** carrier. The direct exact
//! state-root hard cut made FRI roots non-consensus, and rebuilding them here
//! would add up to 256 full 2^16-cell hashes to block replay. FRI summaries in
//! the embedded `ChainState` are therefore unavailable and must never be used
//! through `root`, `seg_root`, openings, or FRI Merkle paths.
//!
//! The returned view retains raw columns only for the caller-declared
//! `required_segment_ids` (at most one consensus block's segment budget).
//! Those columns are historical and therefore cannot be reloaded from the
//! current-tip MDBX table after eviction.  Callers must choose the complete
//! required set up front and must never hydrate any other segment through
//! [`MdbxStore::get_segment`] or [`MdbxStore::get_segment_at_tip`].

use std::collections::{BTreeMap, BTreeSet};

use crate::block_header::{block_id, BlockHeader};
use crate::consensus::params::{
    BLOCK_MAX_ACTIONS, BLOCK_MAX_DISTINCT_SEGMENTS, LOG_SLOTS_MAX, UNDO_RETENTION_DEPTH,
};
use crate::fri_state::{SlotValue, StateError, LOG_SEGMENT_SIZE};
use crate::segmented_state::{ExactStateReadError, SegmentColumns, StateResizeError};
use crate::state::ChainState;

use super::mdbx_store::MdbxHistoricalReadSnapshot;
use super::{MdbxStore, StoreError};

const MAX_GROUPED_UNDO_CHANGES: usize = UNDO_RETENTION_DEPTH as usize * BLOCK_MAX_ACTIONS;

/// Stable identity of the durable source whose compact state metadata is used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CanonicalTipBinding {
    pub height: u64,
    pub hash: [u8; 32],
}

/// A recent canonical exact state plus its explicit historical payload set.
///
/// The inner state may be borrowed only by exact native/recursive replay code.
/// Its FRI summaries are intentionally unavailable. Only IDs returned by
/// [`Self::required_segment_ids`] are backed by historical raw columns, and
/// current-tip MDBX is not backing for any other target-height payload.
#[derive(Debug)]
pub struct HistoricalExactStateView {
    state: ChainState,
    source_tip: CanonicalTipBinding,
    target_header: BlockHeader,
    target_hash: [u8; 32],
    required_segment_ids: Vec<u16>,
}

impl HistoricalExactStateView {
    /// Borrow for commitment/counter inspection through exact-state APIs only.
    pub fn exact_state(&self) -> &ChainState {
        &self.state
    }

    /// Borrow for the immediate exact native/recursive replay.
    ///
    /// The replay implementation must not call any FRI-root/opening API and
    /// must access raw slots only in `required_segment_ids`.
    pub fn exact_state_mut_for_replay(&mut self) -> &mut ChainState {
        &mut self.state
    }

    /// Consume the guard for a move-only exact replay seam.
    ///
    /// The returned `ChainState` is **not** a general historical state: its FRI
    /// summaries are unavailable, current-tip MDBX is not its payload backing,
    /// and raw access is valid only for the required allowlist already owned by
    /// the replay. The consumer must finish the exact replay without
    /// invoking FRI roots/openings or attempting later segment hydration.
    pub fn into_exact_state_for_replay(self) -> ChainState {
        self.state
    }

    pub fn source_tip(&self) -> CanonicalTipBinding {
        self.source_tip
    }

    pub fn target_header(&self) -> &BlockHeader {
        &self.target_header
    }

    pub fn target_hash(&self) -> [u8; 32] {
        self.target_hash
    }

    pub fn required_segment_ids(&self) -> &[u16] {
        &self.required_segment_ids
    }

    /// Whether raw access to this target-height segment was declared up front.
    pub fn permits_raw_segment(&self, segment_id: u16) -> bool {
        self.required_segment_ids.binary_search(&segment_id).is_ok()
    }
}

#[derive(Debug)]
pub enum HistoricalStateError {
    Store(StoreError),
    MissingChainTip,
    MissingStateMeta,
    MissingHeader(u64),
    MissingUndo(u64),
    TargetAboveTip {
        target: u64,
        tip: u64,
    },
    TargetOutsideUndoWindow {
        target: u64,
        tip: u64,
    },
    SourceStateNotDurable,
    SourceStateMismatch(&'static str),
    SourceChanged,
    RequiredSegmentsNotStrict,
    TooManyRequiredSegments {
        actual: usize,
        maximum: usize,
    },
    RequiredSegmentOutOfDomain(u16),
    UnsupportedGeometry {
        target_log: u32,
        tip_log: u32,
    },
    UndoTooLarge(u64),
    Corrupt(&'static str),
    InvalidSegment(u16, &'static str),
    CreationIdExceedsTarget {
        segment_id: u16,
        local_index: u32,
        creation_id: u64,
        alloc_counter: u64,
    },
    ActiveSlotCountMismatch {
        expected: u64,
        actual: u64,
    },
    ExactStateRootMismatch,
    ResidentSegmentBudgetExceeded {
        actual: usize,
        maximum: usize,
    },
    ExactState(ExactStateReadError),
    State(StateError),
    Resize(StateResizeError),
}

impl std::fmt::Display for HistoricalStateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Store(error) => write!(f, "historical state store read: {error}"),
            Self::MissingChainTip => f.write_str("durable canonical tip is missing"),
            Self::MissingStateMeta => f.write_str("durable state metadata is missing"),
            Self::MissingHeader(height) => write!(f, "canonical header {height} is missing"),
            Self::MissingUndo(height) => write!(f, "undo log {height} is missing"),
            Self::TargetAboveTip { target, tip } => {
                write!(f, "historical target {target} is above source tip {tip}")
            }
            Self::TargetOutsideUndoWindow { target, tip } => write!(
                f,
                "historical target {target} is outside the retained undo window at tip {tip}"
            ),
            Self::SourceStateNotDurable => {
                f.write_str("source ChainState is not a clean durable boundary")
            }
            Self::SourceStateMismatch(context) => {
                write!(
                    f,
                    "source ChainState does not match canonical tip: {context}"
                )
            }
            Self::SourceChanged => {
                f.write_str("durable canonical source changed during reconstruction")
            }
            Self::RequiredSegmentsNotStrict => {
                f.write_str("required segment IDs must be strictly sorted and unique")
            }
            Self::TooManyRequiredSegments { actual, maximum } => write!(
                f,
                "required segment count {actual} exceeds block budget {maximum}"
            ),
            Self::RequiredSegmentOutOfDomain(id) => {
                write!(f, "required segment {id} lies outside the target domain")
            }
            Self::UnsupportedGeometry {
                target_log,
                tip_log,
            } => write!(
                f,
                "historical rollback changes segment geometry ({tip_log} -> {target_log})"
            ),
            Self::UndoTooLarge(height) => {
                write!(
                    f,
                    "undo log {height} exceeds the bounded reconstruction budget"
                )
            }
            Self::Corrupt(context) => write!(f, "corrupt historical state source: {context}"),
            Self::InvalidSegment(id, context) => {
                write!(f, "invalid historical segment {id}: {context}")
            }
            Self::CreationIdExceedsTarget {
                segment_id,
                local_index,
                creation_id,
                alloc_counter,
            } => write!(
                f,
                "segment {segment_id} slot {local_index} creation id {creation_id} exceeds target allocator {alloc_counter}"
            ),
            Self::ActiveSlotCountMismatch { expected, actual } => write!(
                f,
                "historical live count {actual} does not match target header {expected}"
            ),
            Self::ExactStateRootMismatch => {
                f.write_str("historical exact state root does not match target header")
            }
            Self::ResidentSegmentBudgetExceeded { actual, maximum } => write!(
                f,
                "historical resident segment count {actual} exceeds required budget {maximum}"
            ),
            Self::ExactState(error) => write!(f, "historical exact state: {error}"),
            Self::State(error) => write!(f, "historical raw state: {error:?}"),
            Self::Resize(error) => write!(f, "historical state resize: {error}"),
        }
    }
}

impl std::error::Error for HistoricalStateError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Store(error) => Some(error),
            Self::ExactState(error) => Some(error),
            Self::State(_) => None,
            Self::Resize(error) => Some(error),
            _ => None,
        }
    }
}

impl From<StoreError> for HistoricalStateError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl From<ExactStateReadError> for HistoricalStateError {
    fn from(error: ExactStateReadError) -> Self {
        Self::ExactState(error)
    }
}

impl From<StateError> for HistoricalStateError {
    fn from(error: StateError) -> Self {
        Self::State(error)
    }
}

impl From<StateResizeError> for HistoricalStateError {
    fn from(error: StateResizeError) -> Self {
        Self::Resize(error)
    }
}

type SegmentRollback = (u32, SlotValue);

/// Reconstruct `target_height` from a clean current-tip state boundary.
///
/// `required_segment_ids` must be the complete, strictly sorted and unique set
/// of target-state segments the immediate consumer will read.  At most
/// [`BLOCK_MAX_DISTINCT_SEGMENTS`] may be retained.  No untouched payload
/// outside that set is read from MDBX.
pub fn reconstruct_historical_exact_state(
    store: &MdbxStore,
    current_tip_state: &ChainState,
    source_tip: CanonicalTipBinding,
    target_height: u64,
    required_segment_ids: &[u16],
) -> Result<HistoricalExactStateView, HistoricalStateError> {
    reconstruct_historical_exact_state_inner(
        store,
        current_tip_state,
        source_tip,
        target_height,
        required_segment_ids,
        |_| {},
    )
}

fn reconstruct_historical_exact_state_inner(
    store: &MdbxStore,
    current_tip_state: &ChainState,
    source_tip: CanonicalTipBinding,
    target_height: u64,
    required_segment_ids: &[u16],
    after_undo_collection: impl FnOnce(&MdbxStore),
) -> Result<HistoricalExactStateView, HistoricalStateError> {
    let snapshot = store.historical_read_snapshot()?;
    let (durable_height, durable_hash) = snapshot
        .get_chain_tip()?
        .ok_or(HistoricalStateError::MissingChainTip)?;
    if (durable_height, durable_hash) != (source_tip.height, source_tip.hash) {
        return Err(HistoricalStateError::SourceChanged);
    }
    if target_height > source_tip.height {
        return Err(HistoricalStateError::TargetAboveTip {
            target: target_height,
            tip: source_tip.height,
        });
    }
    if source_tip.height.saturating_sub(target_height) > UNDO_RETENTION_DEPTH {
        return Err(HistoricalStateError::TargetOutsideUndoWindow {
            target: target_height,
            tip: source_tip.height,
        });
    }

    let tip_header = canonical_header(&snapshot, source_tip.height)?;
    if tip_header.height != source_tip.height || block_id(&tip_header) != source_tip.hash {
        return Err(HistoricalStateError::SourceStateMismatch(
            "tip header identity",
        ));
    }
    validate_log_slots(tip_header.log_slots)?;
    validate_header_counters(&tip_header)?;
    let source_meta = snapshot
        .get_state_meta()?
        .ok_or(HistoricalStateError::MissingStateMeta)?;
    if source_meta
        != (
            tip_header.log_slots,
            tip_header.active_slot_count,
            tip_header.alloc_counter,
        )
    {
        return Err(HistoricalStateError::SourceStateMismatch(
            "durable state metadata",
        ));
    }

    let mut state = current_tip_state
        .durable_metadata_clone()
        .ok_or(HistoricalStateError::SourceStateNotDurable)?;
    if state.state.log_slots() != tip_header.log_slots as usize
        || state.active_slot_count != tip_header.active_slot_count
        || state.alloc_counter != tip_header.alloc_counter
        || state.cached_state_root() != tip_header.state_root
    {
        return Err(HistoricalStateError::SourceStateMismatch(
            "compact state commitment or counters",
        ));
    }
    if state.state.materialized_segment_ids().next().is_some() {
        return Err(HistoricalStateError::SourceStateMismatch(
            "durable clone retained raw columns",
        ));
    }

    let target_header = canonical_header(&snapshot, target_height)?;
    if target_header.height != target_height {
        return Err(HistoricalStateError::Corrupt(
            "canonical header height does not match its key",
        ));
    }
    validate_log_slots(target_header.log_slots)?;
    validate_header_counters(&target_header)?;
    let target_hash = block_id(&target_header);
    let tip_effective_log = effective_log(tip_header.log_slots);
    let target_effective_log = effective_log(target_header.log_slots);
    if tip_effective_log != target_effective_log {
        return Err(HistoricalStateError::UnsupportedGeometry {
            target_log: target_header.log_slots,
            tip_log: tip_header.log_slots,
        });
    }

    validate_required_segments(required_segment_ids, target_header.log_slots)?;
    let grouped = collect_grouped_undo(&snapshot, target_height, source_tip, tip_effective_log)?;
    after_undo_collection(store);

    // Non-required historical payloads are processed first and immediately
    // evicted. Required touched payloads are processed last, so the resident
    // count grows monotonically only inside the caller's explicit budget.
    for required_phase in [false, true] {
        for (&segment_id, changes) in grouped.iter().filter(|(segment_id, _)| {
            required_segment_ids.binary_search(segment_id).is_ok() == required_phase
        }) {
            reconstruct_touched_segment(
                &snapshot,
                &mut state,
                source_tip,
                segment_id,
                tip_effective_log,
                changes,
                target_header.alloc_counter,
                target_header.height,
                required_phase,
                required_segment_ids,
            )?;
        }
    }

    if state.state.log_slots() < target_header.log_slots as usize {
        return Err(HistoricalStateError::Corrupt(
            "rollback target expands rather than shrinks the source domain",
        ));
    }
    state
        .state
        .shrink_exact_metadata_to_log_slots(target_header.log_slots as usize)?;

    let actual_live = compact_live_count(&state)?;
    if actual_live != target_header.active_slot_count {
        return Err(HistoricalStateError::ActiveSlotCountMismatch {
            expected: target_header.active_slot_count,
            actual: actual_live,
        });
    }
    state.active_slot_count = target_header.active_slot_count;
    state.alloc_counter = target_header.alloc_counter;
    if state.try_state_root()? != target_header.state_root {
        return Err(HistoricalStateError::ExactStateRootMismatch);
    }

    // A required segment absent from `grouped` was untouched by every block
    // after the target. Its current-tip bytes are therefore exactly its target
    // bytes and may be hydrated once in this final bounded pass.
    for &segment_id in required_segment_ids {
        if grouped.contains_key(&segment_id) {
            continue;
        }
        hydrate_untouched_required_segment(
            &snapshot,
            &mut state,
            source_tip,
            segment_id,
            tip_effective_log,
            target_header.alloc_counter,
            target_header.height,
            required_segment_ids,
        )?;
    }

    ensure_resident_allowlist(&state, required_segment_ids)?;

    // Recheck the stable MVCC view. The live writer may have advanced since
    // reconstruction began; that does not invalidate this internally
    // consistent source boundary.
    if snapshot.get_chain_tip()? != Some((source_tip.height, source_tip.hash))
        || snapshot.get_state_meta()? != Some(source_meta)
        || canonical_header(&snapshot, source_tip.height)? != tip_header
        || canonical_header(&snapshot, target_height)? != target_header
    {
        return Err(HistoricalStateError::SourceChanged);
    }

    Ok(HistoricalExactStateView {
        state,
        source_tip,
        target_header,
        target_hash,
        required_segment_ids: required_segment_ids.to_vec(),
    })
}

fn canonical_header(
    snapshot: &MdbxHistoricalReadSnapshot<'_>,
    height: u64,
) -> Result<BlockHeader, HistoricalStateError> {
    snapshot
        .get_header(height)?
        .ok_or(HistoricalStateError::MissingHeader(height))
}

fn validate_log_slots(log_slots: u32) -> Result<(), HistoricalStateError> {
    if log_slots == 0 || log_slots > LOG_SLOTS_MAX {
        return Err(HistoricalStateError::Corrupt(
            "header log_slots is outside the consensus domain",
        ));
    }
    Ok(())
}

fn validate_header_counters(header: &BlockHeader) -> Result<(), HistoricalStateError> {
    let capacity = 1u64
        .checked_shl(header.log_slots)
        .ok_or(HistoricalStateError::Corrupt(
            "header slot capacity does not fit u64",
        ))?;
    if header.active_slot_count > capacity {
        return Err(HistoricalStateError::Corrupt(
            "header active count exceeds its slot domain",
        ));
    }
    if header.active_slot_count > header.alloc_counter {
        return Err(HistoricalStateError::Corrupt(
            "header active count exceeds its allocation counter",
        ));
    }
    Ok(())
}

fn effective_log(log_slots: u32) -> u8 {
    log_slots.min(LOG_SEGMENT_SIZE as u32) as u8
}

fn segment_count(log_slots: u32) -> Result<usize, HistoricalStateError> {
    if log_slots <= LOG_SEGMENT_SIZE as u32 {
        return Ok(1);
    }
    1usize
        .checked_shl(log_slots - LOG_SEGMENT_SIZE as u32)
        .ok_or(HistoricalStateError::Corrupt(
            "segment domain does not fit usize",
        ))
}

fn validate_required_segments(
    required_segment_ids: &[u16],
    target_log_slots: u32,
) -> Result<(), HistoricalStateError> {
    if required_segment_ids.len() > BLOCK_MAX_DISTINCT_SEGMENTS {
        return Err(HistoricalStateError::TooManyRequiredSegments {
            actual: required_segment_ids.len(),
            maximum: BLOCK_MAX_DISTINCT_SEGMENTS,
        });
    }
    if !required_segment_ids
        .windows(2)
        .all(|pair| pair[0] < pair[1])
    {
        return Err(HistoricalStateError::RequiredSegmentsNotStrict);
    }
    let count = segment_count(target_log_slots)?;
    if let Some(&segment_id) = required_segment_ids
        .iter()
        .find(|&&segment_id| usize::from(segment_id) >= count)
    {
        return Err(HistoricalStateError::RequiredSegmentOutOfDomain(segment_id));
    }
    Ok(())
}

fn slot_is_in_domain(slot_index: u32, log_slots: u32) -> bool {
    log_slots >= 32 || u64::from(slot_index) < (1u64 << log_slots)
}

fn validate_undo_preimage_creation_boundary(
    previous: SlotValue,
    parent: &BlockHeader,
) -> Result<(), &'static str> {
    if previous.is_empty()
        || crate::consensus::params::creation_id_within_boundary(
            previous.creation_id(),
            parent.alloc_counter,
            parent.height,
        )
    {
        Ok(())
    } else {
        Err("undo pre-image creation id exceeds parent boundary")
    }
}

fn collect_grouped_undo(
    snapshot: &MdbxHistoricalReadSnapshot<'_>,
    target_height: u64,
    source_tip: CanonicalTipBinding,
    segment_log: u8,
) -> Result<BTreeMap<u16, Vec<SegmentRollback>>, HistoricalStateError> {
    let mut grouped = BTreeMap::<u16, Vec<SegmentRollback>>::new();
    let mut total_changes = 0usize;

    if target_height == source_tip.height {
        return Ok(grouped);
    }
    for height in (target_height + 1..=source_tip.height).rev() {
        let child = canonical_header(snapshot, height)?;
        let parent = canonical_header(snapshot, height - 1)?;
        if child.height != height || parent.height != height - 1 {
            return Err(HistoricalStateError::Corrupt(
                "retained header height does not match its key",
            ));
        }
        if child.prev_block_hash != block_id(&parent) {
            return Err(HistoricalStateError::Corrupt(
                "retained canonical headers are not linked",
            ));
        }
        if height == source_tip.height && block_id(&child) != source_tip.hash {
            return Err(HistoricalStateError::SourceChanged);
        }
        if child.log_slots != parent.log_slots
            && child.log_slots != parent.log_slots.saturating_add(1)
        {
            return Err(HistoricalStateError::Corrupt(
                "retained header slot-domain transition is invalid",
            ));
        }
        validate_header_counters(&child)?;
        validate_header_counters(&parent)?;
        let allocation_delta = child
            .alloc_counter
            .checked_sub(parent.alloc_counter)
            .ok_or(HistoricalStateError::Corrupt(
                "retained allocation counter decreases",
            ))?;
        if allocation_delta > BLOCK_MAX_ACTIONS as u64
            || child.active_slot_count.abs_diff(parent.active_slot_count) > BLOCK_MAX_ACTIONS as u64
        {
            return Err(HistoricalStateError::Corrupt(
                "retained counter delta exceeds the block action bound",
            ));
        }
        if effective_log(parent.log_slots) != segment_log
            || effective_log(child.log_slots) != segment_log
        {
            return Err(HistoricalStateError::UnsupportedGeometry {
                target_log: parent.log_slots,
                tip_log: child.log_slots,
            });
        }

        let undo = snapshot
            .get_undo_log(height)?
            .ok_or(HistoricalStateError::MissingUndo(height))?;
        if undo.block_height != height
            || undo.log_slots_before != parent.log_slots
            || undo.active_slot_count_before != parent.active_slot_count
            || undo.alloc_counter_before != parent.alloc_counter
        {
            return Err(HistoricalStateError::Corrupt(
                "undo metadata does not match parent header",
            ));
        }
        if undo.slot_changes.len() > BLOCK_MAX_ACTIONS {
            return Err(HistoricalStateError::UndoTooLarge(height));
        }
        total_changes = total_changes
            .checked_add(undo.slot_changes.len())
            .ok_or(HistoricalStateError::UndoTooLarge(height))?;
        if total_changes > MAX_GROUPED_UNDO_CHANGES {
            return Err(HistoricalStateError::UndoTooLarge(height));
        }

        let mut seen_slots = BTreeSet::new();
        for &(slot_index, previous) in undo.slot_changes.iter().rev() {
            if !seen_slots.insert(slot_index) {
                return Err(HistoricalStateError::Corrupt(
                    "undo contains a duplicate physical slot",
                ));
            }
            if !slot_is_in_domain(slot_index, child.log_slots) {
                return Err(HistoricalStateError::Corrupt(
                    "undo slot lies outside child slot domain",
                ));
            }
            if !slot_is_in_domain(slot_index, parent.log_slots) && !previous.is_empty() {
                return Err(HistoricalStateError::Corrupt(
                    "new expansion-half undo pre-image is not empty",
                ));
            }
            validate_undo_preimage_creation_boundary(previous, &parent)
                .map_err(HistoricalStateError::Corrupt)?;
            let segment_id = (slot_index >> segment_log) as u16;
            grouped
                .entry(segment_id)
                .or_default()
                .push((slot_index, previous));
        }
    }
    Ok(grouped)
}

#[allow(clippy::too_many_arguments)]
fn reconstruct_touched_segment(
    snapshot: &MdbxHistoricalReadSnapshot<'_>,
    state: &mut ChainState,
    source_tip: CanonicalTipBinding,
    segment_id: u16,
    effective_log: u8,
    changes: &[SegmentRollback],
    target_alloc_counter: u64,
    target_height: u64,
    retain: bool,
    required_segment_ids: &[u16],
) -> Result<(), HistoricalStateError> {
    let columns = load_source_segment(snapshot, state, source_tip, segment_id, effective_log)?;
    state.restore_evicted_segment(segment_id, columns)?;
    let circulating_supply_micronoid =
        state
            .supply_after_slot_updates(changes)
            .ok_or(HistoricalStateError::Corrupt(
                "historical circulating-supply rollback failed",
            ))?;
    state.state.apply_delta_unrooted(changes)?;
    state.circulating_supply_micronoid = circulating_supply_micronoid;
    validate_resident_segment(state, segment_id, target_alloc_counter, target_height)?;

    // Refresh only the consensus exact summary. FRI summaries deliberately
    // remain unavailable in `HistoricalExactStateView`.
    state.try_state_root()?;
    state.state.clear_dirty();
    if !retain {
        state.state.evict_segment(segment_id);
    }
    ensure_resident_allowlist(state, required_segment_ids)
}

fn hydrate_untouched_required_segment(
    snapshot: &MdbxHistoricalReadSnapshot<'_>,
    state: &mut ChainState,
    source_tip: CanonicalTipBinding,
    segment_id: u16,
    effective_log: u8,
    target_alloc_counter: u64,
    target_height: u64,
    required_segment_ids: &[u16],
) -> Result<(), HistoricalStateError> {
    let columns = load_source_segment(snapshot, state, source_tip, segment_id, effective_log)?;
    state.restore_evicted_segment(segment_id, columns)?;
    validate_resident_segment(state, segment_id, target_alloc_counter, target_height)?;
    state.state.clear_dirty();
    ensure_resident_allowlist(state, required_segment_ids)
}

fn load_source_segment(
    snapshot: &MdbxHistoricalReadSnapshot<'_>,
    state: &ChainState,
    source_tip: CanonicalTipBinding,
    segment_id: u16,
    effective_log: u8,
) -> Result<SegmentColumns, HistoricalStateError> {
    let expected_len = 1usize << effective_log;
    if snapshot.get_chain_tip()? != Some((source_tip.height, source_tip.hash)) {
        return Err(HistoricalStateError::SourceChanged);
    }
    match snapshot.get_segment(segment_id)? {
        Some((stored_log, columns)) => {
            if stored_log != effective_log
                || columns.values.len() != expected_len
                || columns.owners_hi.len() != expected_len
                || columns.owners_lo.len() != expected_len
            {
                return Err(HistoricalStateError::InvalidSegment(
                    segment_id,
                    "durable segment shape does not match source geometry",
                ));
            }
            Ok(columns)
        }
        None if state.state.segment_live_count(segment_id) != 0 => {
            Err(HistoricalStateError::InvalidSegment(
                segment_id,
                "source metadata names a live segment missing from MDBX",
            ))
        }
        None => Ok(SegmentColumns::new_zero(expected_len)),
    }
}

fn validate_resident_segment(
    state: &ChainState,
    segment_id: u16,
    alloc_counter: u64,
    target_height: u64,
) -> Result<(), HistoricalStateError> {
    let Some(columns) = state.state.try_get_segment_columns(segment_id) else {
        if state.state.segment_live_count(segment_id) != 0 {
            return Err(HistoricalStateError::InvalidSegment(
                segment_id,
                "live reconstructed segment has no resident columns",
            ));
        }
        return Ok(());
    };
    let expected_len = 1usize << state.state.effective_log_segment_size();
    if columns.values.len() != expected_len
        || columns.owners_hi.len() != expected_len
        || columns.owners_lo.len() != expected_len
    {
        return Err(HistoricalStateError::InvalidSegment(
            segment_id,
            "reconstructed columns have inconsistent lengths",
        ));
    }
    let mut counted_live = 0u32;
    for local_index in 0..expected_len {
        let slot = SlotValue {
            value: columns.values[local_index],
            owner_hi: columns.owners_hi[local_index],
            owner_lo: columns.owners_lo[local_index],
        };
        if slot.is_empty() {
            continue;
        }
        if !crate::consensus::params::creation_id_within_boundary(
            slot.creation_id(),
            alloc_counter,
            target_height,
        ) {
            return Err(HistoricalStateError::CreationIdExceedsTarget {
                segment_id,
                local_index: local_index as u32,
                creation_id: slot.creation_id(),
                alloc_counter,
            });
        }
        counted_live = counted_live
            .checked_add(1)
            .ok_or(HistoricalStateError::InvalidSegment(
                segment_id,
                "live count overflows u32",
            ))?;
    }
    if counted_live != state.state.segment_live_count(segment_id) {
        return Err(HistoricalStateError::InvalidSegment(
            segment_id,
            "column live count disagrees with compact summary",
        ));
    }
    Ok(())
}

fn compact_live_count(state: &ChainState) -> Result<u64, HistoricalStateError> {
    let mut total = 0u64;
    for segment_id in 0..state.state.num_segments() {
        total = total
            .checked_add(u64::from(state.state.segment_live_count(segment_id as u16)))
            .ok_or(HistoricalStateError::Corrupt(
                "compact live count overflows u64",
            ))?;
    }
    Ok(total)
}

fn ensure_resident_allowlist(
    state: &ChainState,
    required_segment_ids: &[u16],
) -> Result<(), HistoricalStateError> {
    let mut resident = 0usize;
    for segment_id in state.state.materialized_segment_ids() {
        if required_segment_ids.binary_search(&segment_id).is_err() {
            return Err(HistoricalStateError::Corrupt(
                "non-required historical segment remained resident",
            ));
        }
        resident += 1;
    }
    if resident > required_segment_ids.len() {
        return Err(HistoricalStateError::ResidentSegmentBudgetExceeded {
            actual: resident,
            maximum: required_segment_ids.len(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use noid_core::Block128;

    use crate::consensus::genesis::genesis_header;
    use crate::consensus::params::coinbase_creation_id;

    #[test]
    fn spent_coinbase_undo_preimage_uses_parent_height_boundary() {
        let mut parent = genesis_header();
        parent.height = 7;
        parent.alloc_counter = 3;

        let at_parent_height = SlotValue::from_parts(
            1,
            coinbase_creation_id(parent.height),
            Block128(1),
            Block128(2),
        );
        assert!(validate_undo_preimage_creation_boundary(at_parent_height, &parent).is_ok());

        let from_future_height = SlotValue::from_parts(
            1,
            coinbase_creation_id(parent.height + 1),
            Block128(1),
            Block128(2),
        );
        assert_eq!(
            validate_undo_preimage_creation_boundary(from_future_height, &parent),
            Err("undo pre-image creation id exceeds parent boundary")
        );
    }
}
