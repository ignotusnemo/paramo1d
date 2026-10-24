// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Self-recursive `HistoryStep` relation.
//!
//! A recursive transition verifies the complete previous joint C1 envelope,
//! including parent recursion and its direct Block authority,
//! carries the complete pinned two-class matrix bank, folds the fresh parent
//! claim into the exact authenticated class lane, and returns a
//! consuming terminal decision rather than a boolean acceptance shortcut.

use super::gated_recorder::BaseSelectableParentRecorder;
use super::*;
use crate::acceptance::history_step_bank::{
    block_acc_lanes, canonical_history_step_class_id, canonical_history_step_pcs_params,
    canonical_history_step_shape, history_step_bank_base_output_io,
    history_step_bank_block_accumulator, history_step_bank_post_commit_digest,
    history_step_bank_tip_class, observe_history_step_bank_fold_route_trace,
    route_carry_and_fold_history_step_lane_canonical, AcceptedHistoryStepBankTip,
    CanonicalHistoryStepClassId, HistoryStepBankEntryPins, HistoryStepBankError,
    PendingHistoryStepBankDecision, PinnedHistoryStepClassBank, ACC_LANES,
    HISTORY_STEP_BANK_FOLD_TRANSCRIPT_DOMAIN, HISTORY_STEP_CLASS_COUNT,
    HISTORY_STEP_TIER_SLOT_COUNT,
};
use noid_ivc_core::deep_chain::schedule::TranscriptOp;
use noid_ivc_core::field_circuit::{f128_from_u128, ExtExpr};
pub const HISTORY_STEP_WIRE_VERSION: u8 = 4;

const _: () = assert!(
    HISTORY_STEP_WIRE_VERSION == noid_chain::history_step::HISTORY_STEP_TERMINAL_VERSION,
    "recursive terminal wire version must equal the chain metadata version"
);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HistoryStepSidecarOperation {
    BaseShapeOnlyJointC1,
    ScratchJointC1Replay,
    PrepareParentColumns,
    ParentJointC1TraceReplay,
    FinalizeParentRegion,
    FinalizeCurrentDirectBlock,
}

impl core::fmt::Display for HistoryStepSidecarOperation {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::BaseShapeOnlyJointC1 => "base shape-only joint C1 proof",
            Self::ScratchJointC1Replay => "scratch joint C1 replay",
            Self::PrepareParentColumns => "parent-column preparation",
            Self::ParentJointC1TraceReplay => "parent joint C1 trace replay",
            Self::FinalizeParentRegion => "parent-region finalization",
            Self::FinalizeCurrentDirectBlock => "current direct-Block finalization",
        })
    }
}

#[derive(Debug)]
pub enum HistoryStepError {
    Cancelled,
    Input(HistoryStepInputError),
    Bank(HistoryStepBankError),
    Region(RegionSidecarError),
    Sidecar {
        operation: HistoryStepSidecarOperation,
        source: RegionSidecarError,
    },
    Verify(VerifyError),
    InvalidClass,
    ProtocolProfile,
    InvalidIo,
    ParentBoundary,
    ParentRecording,
    ClassPin,
    PcsParams,
    RuntimeMatrix(CanonicalHistoryStepClassId),
    RuntimeParentVk,
    RuntimeBlockVk(usize),
    RuntimeWitnessShape {
        class: CanonicalHistoryStepClassId,
        expected: usize,
        actual: usize,
    },
    RuntimeUsefulRows {
        class: CanonicalHistoryStepClassId,
        expected: usize,
        actual: usize,
    },
    RuntimeLayout,
    StagedSeal,
    TerminalMetadata,
    HeaderBinding,
    WireVersion,
    WireLength {
        expected: usize,
        actual: usize,
    },
    WireEncoding,
    ShapeOverflow {
        tier: usize,
        used: usize,
        limit: usize,
    },
}

fn auxiliary_sidecar_error(label: &str, error: RegionSidecarError) -> VerifyError {
    if std::env::var_os("NOID_HISTORY_STEP_AUX_DEBUG").is_some() {
        eprintln!("[history-step auxiliary] {label}: {error:?}");
    }
    VerifyError::Auxiliary
}

impl core::fmt::Display for HistoryStepError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Cancelled => f.write_str("HistoryStep proving was cancelled"),
            Self::Input(error) => write!(f, "HistoryStep input: {error}"),
            Self::Bank(error) => write!(f, "HistoryStep bank: {error}"),
            Self::Region(error) => write!(f, "HistoryStep sidecar: {error:?}"),
            Self::Sidecar { operation, source } => {
                write!(f, "HistoryStep sidecar {operation}: {source}")
            }
            Self::Verify(error) => write!(f, "HistoryStep proof: {error:?}"),
            Self::InvalidClass => f.write_str("HistoryStep class id is not canonical"),
            Self::ProtocolProfile => f.write_str("legacy HistoryStep cannot carry contract openings"),
            Self::InvalidIo => f.write_str("HistoryStep public IO is not canonical"),
            Self::ParentBoundary => {
                f.write_str("HistoryStep current start is not the parent terminal")
            }
            Self::ParentRecording => f.write_str("HistoryStep parent transcript recording drift"),
            Self::ClassPin => f.write_str("HistoryStep class pin mismatch"),
            Self::PcsParams => f.write_str("HistoryStep PCS parameters mismatch"),
            Self::RuntimeMatrix(class) => write!(
                f,
                "HistoryStep runtime matrix {} does not match the pinned bank",
                class.index(),
            ),
            Self::RuntimeParentVk => {
                f.write_str("HistoryStep runtime parent-recursion VK does not match the bank")
            }
            Self::RuntimeBlockVk(slot) => write!(
                f,
                "HistoryStep runtime block VK slot {slot} does not match the bank",
            ),
            Self::RuntimeWitnessShape {
                class,
                expected,
                actual,
            } => write!(
                f,
                "HistoryStep runtime witness for class {} has {actual} fields, expected {expected}",
                class.index(),
            ),
            Self::RuntimeUsefulRows {
                class,
                expected,
                actual,
            } => write!(
                f,
                "HistoryStep runtime witness for class {} has {actual} useful rows, pinned matrix has {expected}",
                class.index(),
            ),
            Self::RuntimeLayout => {
                f.write_str("HistoryStep runtime transcript layout did not reach its fixed point")
            }
            Self::StagedSeal => {
                f.write_str("HistoryStep staged witness does not match the sealed nonce boundary")
            }
            Self::TerminalMetadata => f.write_str("HistoryStep terminal metadata mismatch"),
            Self::HeaderBinding => {
                f.write_str("HistoryStep terminal does not bind the expected block header")
            }
            Self::WireVersion => f.write_str("HistoryStep terminal wire version is not supported"),
            Self::WireLength { expected, actual } => write!(
                f,
                "HistoryStep terminal wire length {actual} does not match canonical {expected}",
            ),
            Self::WireEncoding => f.write_str("HistoryStep terminal wire encoding is invalid"),
            Self::ShapeOverflow { tier, used, limit } => {
                write!(f, "HistoryStep B{tier} uses {used} rows, limit {limit}")
            }
        }
    }
}

impl std::error::Error for HistoryStepError {}

impl From<HistoryStepInputError> for HistoryStepError {
    fn from(value: HistoryStepInputError) -> Self {
        Self::Input(value)
    }
}

impl From<HistoryStepBankError> for HistoryStepError {
    fn from(value: HistoryStepBankError) -> Self {
        Self::Bank(value)
    }
}

impl From<RegionSidecarError> for HistoryStepError {
    fn from(value: RegionSidecarError) -> Self {
        Self::Region(value)
    }
}

impl From<VerifyError> for HistoryStepError {
    fn from(value: VerifyError) -> Self {
        Self::Verify(value)
    }
}

impl HistoryStepError {
    fn sidecar(operation: HistoryStepSidecarOperation, source: RegionSidecarError) -> Self {
        Self::Sidecar { operation, source }
    }
}

/// Fully materialized verifier authority. A persisted terminal is sufficient
/// to continue recursion: previous proving witnesses are never retained.
#[derive(Clone, Debug)]
pub struct HistoryStepParentTranscriptLayout {
    child: DuplexLayout,
    r_prev: DuplexLayout,
}

impl HistoryStepParentTranscriptLayout {
    pub fn new(child: DuplexLayout, r_prev: DuplexLayout) -> Self {
        Self { child, r_prev }
    }

    pub fn child(&self) -> &DuplexLayout {
        &self.child
    }

    pub fn r_prev(&self) -> &DuplexLayout {
        &self.r_prev
    }
}

/// Complete value-independent verifier material for the two-class bank.
/// Matrix digests are deliberately absent: they are frozen only after these
/// canonical VKs and transcript layouts have shaped the relation.
#[derive(Clone, Debug)]
pub struct HistoryStepRuntimeParts {
    parent_recursion_vk: LinkRegionSidecarVk,
    direct_block_vks: [BlockRegionSidecarVk; HISTORY_STEP_TIER_SLOT_COUNT],
    parent_transcripts: [HistoryStepParentTranscriptLayout; HISTORY_STEP_TIER_SLOT_COUNT],
    parent_geometry: HistoryStepParentGeometry,
}

impl HistoryStepRuntimeParts {
    pub(super) fn from_canonical_geometry(
        parent_recursion_vk: LinkRegionSidecarVk,
        direct_block_vks: [BlockRegionSidecarVk; HISTORY_STEP_TIER_SLOT_COUNT],
        parent_transcripts: [HistoryStepParentTranscriptLayout; HISTORY_STEP_TIER_SLOT_COUNT],
        parent_geometry: HistoryStepParentGeometry,
    ) -> Self {
        Self {
            parent_recursion_vk,
            direct_block_vks,
            parent_transcripts,
            parent_geometry,
        }
    }

    pub fn new(
        parent_recursion_vk: LinkRegionSidecarVk,
        direct_block_vks: [BlockRegionSidecarVk; HISTORY_STEP_TIER_SLOT_COUNT],
        parent_transcripts: [HistoryStepParentTranscriptLayout; HISTORY_STEP_TIER_SLOT_COUNT],
    ) -> Result<Self, HistoryStepError> {
        let parent_params = (0..HISTORY_STEP_TIER_SLOT_COUNT)
            .map(|slot| {
                let class = CanonicalHistoryStepClassId::new(slot)
                    .expect("runtime parent tier is canonical");
                canonical_history_step_pcs_params(class)
            })
            .collect::<Vec<_>>();
        let geometry = HistoryStepParentGeometry::new(
            &parent_params,
            parent_transcripts
                .iter()
                .map(|transcript| transcript.child.clone())
                .collect(),
            parent_transcripts
                .iter()
                .map(|transcript| transcript.r_prev.clone())
                .collect(),
        )?;
        if geometry
            .canonical_vk(&crate::acceptance::history_step_bank::history_step_bank_io_spec())?
            .transcript_digest()
            != parent_recursion_vk.transcript_digest()
        {
            return Err(HistoryStepError::RuntimeParentVk);
        }
        for (slot, vk) in direct_block_vks.iter().enumerate() {
            if crate::region_sidecar::selected_zk_block_geometry(
                noid_chain::consensus::params::BLOCK_PAGE_CLASS_TIERS[slot],
            )
            .is_none()
                || vk.version() != crate::region_sidecar::BLOCK_REGION_SELECTED_ZK_SIDECAR_VERSION
                || vk.supports_objects()
            {
                return Err(HistoryStepError::RuntimeBlockVk(slot));
            }
        }
        Ok(Self {
            parent_recursion_vk,
            direct_block_vks,
            parent_transcripts,
            parent_geometry: geometry,
        })
    }

    pub fn parent_recursion_vk(&self) -> &LinkRegionSidecarVk {
        &self.parent_recursion_vk
    }

    pub fn direct_block_vks(&self) -> &[BlockRegionSidecarVk; HISTORY_STEP_TIER_SLOT_COUNT] {
        &self.direct_block_vks
    }

    pub fn parent_transcripts(
        &self,
    ) -> &[HistoryStepParentTranscriptLayout; HISTORY_STEP_TIER_SLOT_COUNT] {
        &self.parent_transcripts
    }

    pub(super) fn with_direct_block_vk(
        &self,
        slot: usize,
        vk: BlockRegionSidecarVk,
    ) -> Result<Self, HistoryStepError> {
        if slot >= HISTORY_STEP_TIER_SLOT_COUNT {
            return Err(HistoryStepError::RuntimeBlockVk(slot));
        }
        let mut direct_block_vks = self.direct_block_vks.clone();
        direct_block_vks[slot] = vk;
        Self::new(
            self.parent_recursion_vk.clone(),
            direct_block_vks,
            self.parent_transcripts.clone(),
        )
    }
}

/// Bind the two frozen matrix identities to the exact runtime verifier
/// material. Shapes, PCS parameters and post-commit identities are derived;
/// callers cannot supply a second, potentially divergent copy of them.
pub fn pin_history_step_class_bank(
    matrix_digests: [[u8; 32]; HISTORY_STEP_CLASS_COUNT],
    parts: &HistoryStepRuntimeParts,
) -> Result<PinnedHistoryStepClassBank, HistoryStepError> {
    let spec = crate::acceptance::history_step_bank::history_step_bank_io_spec();
    let parent_recursion_vk_digest = parts.parent_recursion_vk.transcript_digest();
    let pins = std::array::from_fn(|index| {
        let class_id = CanonicalHistoryStepClassId::from_index(index)
            .expect("fixed HistoryStep bank index is canonical");
        let shape = canonical_history_step_shape(class_id);
        let pcs_params = canonical_history_step_pcs_params(class_id);
        let matrix_digest = matrix_digests[index];
        let direct_block_vk_digest =
            parts.direct_block_vks[class_id.current_slot()].transcript_digest();
        HistoryStepBankEntryPins {
            class_id,
            shape,
            pcs_params: pcs_params.clone(),
            matrix_digest,
            parent_recursion_vk_digest,
            direct_block_vk_digest,
            post_commit_digest: history_step_bank_post_commit_digest(
                class_id,
                &matrix_digest,
                &spec,
                &pcs_params,
                parent_recursion_vk_digest,
                direct_block_vk_digest,
            ),
        }
    });
    PinnedHistoryStepClassBank::validate(pins).map_err(Into::into)
}

struct RejectingHistoryStepMatrixSource;

impl HistoryStepMatrixSource for RejectingHistoryStepMatrixSource {
    fn load(
        &self,
        _class: CanonicalHistoryStepClassId,
    ) -> Result<HistoryStepMatrixLease, HistoryStepMatrixSourceError> {
        Err(HistoryStepMatrixSourceError)
    }
}

/// Derive one canonical direct-Block verifier shape from an honest owned
/// input. The returned absolute slices are provisional; the freezer replaces
/// them with the slices emitted by the integrated HistoryStep build before it
/// pins or exports any class.
pub fn derive_history_step_direct_block_vk<const TIER: usize>(
    current: HistoryStepBlockInput<TIER>,
) -> Result<BlockRegionSidecarVk, HistoryStepError> {
    validate_legacy_block_profile(&current)?;
    if crate::region_sidecar::selected_zk_block_geometry(TIER).is_none() {
        return Err(HistoryStepError::InvalidClass);
    }
    let HistoryStepBlockInput {
        start_accumulator,
        end_accumulator,
        components,
        authorization,
        sealed_header,
        parent_header,
        ..
    } = current;
    let mut builder = FieldR1csBuilder::new();
    let parent_seal = ParentSealTrace::alloc(&mut builder, &parent_header);
    let assembly = build_block_slots_selected_zk(
        &mut builder,
        &start_accumulator,
        &end_accumulator,
        &components,
        &sealed_header,
        TIER,
        authorization,
        &parent_header,
        &parent_seal.block_id,
        BlockRelationProfile::LegacyV1,
    );
    Ok(assembly.region_vk().clone())
}

pub(super) fn placeholder_history_step_recording_layout(slot_count: usize) -> DuplexLayout {
    compile_duplex(&[TranscriptOp::Absorb(vec![Some(0); 2 * slot_count])])
}

pub(super) fn history_step_query_lane_count(params: &PcsParams) -> usize {
    let log_dim = params.m - noid_ivc_core::pcs::LOG_PACKING - params.log_batch_size;
    let k_code = log_dim + params.log_inv_rate;
    let per_lane = 128 / k_code;
    noid_ivc_core::pcs::default_fri_queries(params.log_dim(), params.log_inv_rate)
        .div_ceil(per_lane)
}

/// Freeze the value-independent parent transcript geometry around both
/// canonical direct-Block VK shapes. The only iterative part is the
/// `[R]_prev` recording size: VK digests are witness lanes, so the transcript
/// schedule depends on this self-reference solely through its size class.
pub fn derive_history_step_runtime_parts(
    direct_block_vks: [BlockRegionSidecarVk; HISTORY_STEP_TIER_SLOT_COUNT],
) -> Result<HistoryStepRuntimeParts, HistoryStepError> {
    let parent_params: [PcsParams; HISTORY_STEP_TIER_SLOT_COUNT] = std::array::from_fn(|slot| {
        canonical_history_step_pcs_params(
            CanonicalHistoryStepClassId::new(slot).expect("canonical HistoryStep tier slot"),
        )
    });
    let mut child_layouts: [DuplexLayout; HISTORY_STEP_TIER_SLOT_COUNT] =
        std::array::from_fn(|_| placeholder_history_step_recording_layout(1usize << 14));
    let mut r_prev_layouts: [DuplexLayout; HISTORY_STEP_TIER_SLOT_COUNT] =
        std::array::from_fn(|_| placeholder_history_step_recording_layout(1usize << 14));

    for _ in 0..16 {
        let geometry = HistoryStepParentGeometry::new(
            &parent_params,
            child_layouts.to_vec(),
            r_prev_layouts.to_vec(),
        )?;
        let parent_recursion_vk = geometry
            .canonical_vk(&crate::acceptance::history_step_bank::history_step_bank_io_spec())?;
        let transcripts = std::array::from_fn(|slot| {
            HistoryStepParentTranscriptLayout::new(
                child_layouts[slot].clone(),
                r_prev_layouts[slot].clone(),
            )
        });
        let parts = HistoryStepRuntimeParts::new(
            parent_recursion_vk,
            direct_block_vks.clone(),
            transcripts,
        )?;
        let bank = pin_history_step_class_bank([[0u8; 32]; HISTORY_STEP_CLASS_COUNT], &parts)?;
        let runtime = HistoryStepRuntime::new(
            bank,
            Box::new(RejectingHistoryStepMatrixSource),
            parts.clone(),
        )?;
        let mut derived_children = Vec::with_capacity(HISTORY_STEP_TIER_SLOT_COUNT);
        let mut derived_r_prev = Vec::with_capacity(HISTORY_STEP_TIER_SLOT_COUNT);
        for slot in 0..HISTORY_STEP_TIER_SLOT_COUNT {
            let class_id =
                CanonicalHistoryStepClassId::new(slot).expect("canonical HistoryStep tier slot");
            let entry = runtime.bank().entry(class_id);
            let (field_proof, commitment_root) =
                shape_only_field_r1cs_proof_c1(&entry.shape(), entry.pcs_params());
            let envelope = HistoryStepProof {
                field_proof,
                commitment: Commitment {
                    root: commitment_root,
                    params: entry.pcs_params().clone(),
                },
                io: vec![F128::ZERO; runtime.bank().spec().io_len],
                sidecar: shape_only_joint_c1_region_sidecar_proof(
                    runtime.parent_recursion_vk(),
                    runtime
                        .direct_block_vk(slot)
                        .ok_or(HistoryStepError::RuntimeBlockVk(slot))?,
                    entry.shape().m,
                )?,
            };
            let complete = run_scratch_parent_recording_pass(
                &runtime,
                class_id,
                &envelope,
                &entry.matrix_digest(),
                &entry.post_commit_digest(),
            )?;
            let child = complete.child.ok_or(HistoryStepError::ParentRecording)?;
            derived_children.push(child.layout);
            derived_r_prev.push(complete.r_prev.layout);
        }
        let derived_children: [DuplexLayout; HISTORY_STEP_TIER_SLOT_COUNT] = derived_children
            .try_into()
            .map_err(|_| HistoryStepError::RuntimeLayout)?;
        let derived_r_prev: [DuplexLayout; HISTORY_STEP_TIER_SLOT_COUNT] = derived_r_prev
            .try_into()
            .map_err(|_| HistoryStepError::RuntimeLayout)?;
        if derived_children == child_layouts && derived_r_prev == r_prev_layouts {
            return Ok(parts);
        }
        child_layouts = derived_children;
        r_prev_layouts = derived_r_prev;
    }
    Err(HistoryStepError::RuntimeLayout)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HistoryStepMatrixSourceError;

/// Authenticated class-matrix provider. Production implementations return an
/// `Arc` lease over the executable-embedded compact relation; release tooling
/// may lease a resident matrix while constructing the bank.
pub trait HistoryStepMatrixSource: Send + Sync {
    fn load(
        &self,
        class: CanonicalHistoryStepClassId,
    ) -> Result<HistoryStepMatrixLease, HistoryStepMatrixSourceError>;
}

pub struct HistoryStepRuntime {
    bank: PinnedHistoryStepClassBank,
    matrix_source: Box<dyn HistoryStepMatrixSource>,
    parent_recursion_vk: LinkRegionSidecarVk,
    direct_block_vks: [BlockRegionSidecarVk; HISTORY_STEP_TIER_SLOT_COUNT],
    parent_geometry: HistoryStepParentGeometry,
    matrix_claim_cache: super::super::history_step_bank::HistoryStepMatrixClaimCache,
}

impl HistoryStepRuntime {
    pub fn new(
        bank: PinnedHistoryStepClassBank,
        matrix_source: Box<dyn HistoryStepMatrixSource>,
        parts: HistoryStepRuntimeParts,
    ) -> Result<Self, HistoryStepError> {
        let HistoryStepRuntimeParts {
            parent_recursion_vk,
            direct_block_vks,
            parent_transcripts: _,
            parent_geometry,
        } = parts;
        if parent_recursion_vk.transcript_digest()
            != bank
                .entry(CanonicalHistoryStepClassId::from_index(0).expect("class zero is canonical"))
                .parent_recursion_vk_digest()
        {
            return Err(HistoryStepError::RuntimeParentVk);
        }
        for (slot, vk) in direct_block_vks.iter().enumerate() {
            let class =
                CanonicalHistoryStepClassId::new(slot).expect("runtime block VK slot is canonical");
            if vk.supports_objects()
                || vk.transcript_digest() != bank.entry(class).direct_block_vk_digest()
            {
                return Err(HistoryStepError::RuntimeBlockVk(slot));
            }
        }
        Ok(Self {
            bank,
            matrix_source,
            parent_recursion_vk,
            direct_block_vks,
            parent_geometry,
            matrix_claim_cache: Default::default(),
        })
    }

    pub fn bank(&self) -> &PinnedHistoryStepClassBank {
        &self.bank
    }

    pub(crate) fn load_matrix(
        &self,
        class: CanonicalHistoryStepClassId,
    ) -> Result<HistoryStepMatrixLease, HistoryStepError> {
        let matrix = self
            .matrix_source
            .load(class)
            .map_err(|_| HistoryStepError::RuntimeMatrix(class))?;
        self.bank
            .authenticate_matrix_lease(class, &matrix)
            .map_err(|_| HistoryStepError::RuntimeMatrix(class))?;
        Ok(matrix)
    }

    /// Materialize one release-pinned matrix through the configured runtime
    /// source. GUI launch helpers use this in a short-lived process so the
    /// packed disk image is ready before mining while its large resident image
    /// is released immediately when the helper exits.
    pub fn prepare_matrix_cache(
        &self,
        class: CanonicalHistoryStepClassId,
    ) -> Result<(), HistoryStepError> {
        drop(self.load_matrix(class)?);
        Ok(())
    }

    pub fn parent_recursion_vk(&self) -> &LinkRegionSidecarVk {
        &self.parent_recursion_vk
    }

    pub fn direct_block_vk(&self, current_slot: usize) -> Option<&BlockRegionSidecarVk> {
        self.direct_block_vks.get(current_slot)
    }

    pub fn direct_block_vks(&self) -> &[BlockRegionSidecarVk; HISTORY_STEP_TIER_SLOT_COUNT] {
        &self.direct_block_vks
    }

    fn parent_geometry(&self) -> &HistoryStepParentGeometry {
        &self.parent_geometry
    }

    pub fn decide(
        &self,
        pending: PendingHistoryStepBankDecision,
    ) -> Result<AcceptedHistoryStepBankTip, HistoryStepError> {
        pending
            .finish_with_matrix_loader_cached(
                |class| self.load_matrix(class),
                &self.matrix_claim_cache,
            )
            .map_err(Into::into)
    }
}

/// One runtime HistoryStep witness. It contains no relation rows and cannot be
/// proved without leasing the exact class matrix authenticated by the runtime
/// bank.
pub struct BuiltHistoryStep {
    matrix: HistoryStepMatrixLease,
    witness: Vec<F128>,
    io: Vec<F128>,
    spec: PublicIoSpec,
    pcs_params: PcsParams,
    useful_rows: usize,
    class_id: CanonicalHistoryStepClassId,
    semantic_id: [u8; 32],
    nonce: u128,
    preparations: HistoryStepPreparations,
}

impl BuiltHistoryStep {
    pub const fn useful_rows(&self) -> usize {
        self.useful_rows
    }

    pub const fn class_id(&self) -> CanonicalHistoryStepClassId {
        self.class_id
    }

    pub const fn semantic_id(&self) -> [u8; 32] {
        self.semantic_id
    }

    pub const fn nonce(&self) -> u128 {
        self.nonce
    }

    pub fn parent_recursion_vk(&self) -> &LinkRegionSidecarVk {
        self.preparations.recursion.vk()
    }

    pub fn direct_block_vk(&self) -> &BlockRegionSidecarVk {
        self.preparations.direct_block.vk()
    }
}

/// Full frozen relation emitted only for release matrix construction. Runtime
/// block production uses [`BuiltHistoryStep`] and never materializes CSR rows.
pub struct FrozenHistoryStep {
    r1cs: FieldR1cs,
    /// Research/freezer witness retained so a newly composed matrix can be
    /// satisfaction-checked before any expensive terminal freeze.
    witness: Vec<F128>,
    useful_rows: usize,
    class_id: CanonicalHistoryStepClassId,
    preparations: HistoryStepPreparations,
}

/// Research-only exact direct-block relation. It excludes the parent-proof
/// replay and outer HistoryStep public-I/O glue, but includes the complete
/// selected authorization, Meta, transaction, fee and exact-State machinery.
/// This lets heterogeneous contract witnesses be compared before freezing a
/// new recursive matrix bank.
#[doc(hidden)]
pub struct FrozenDirectBlockResearch {
    r1cs: FieldR1cs,
    witness: Vec<F128>,
    useful_rows: usize,
    class_id: CanonicalHistoryStepClassId,
}

#[doc(hidden)]
impl FrozenDirectBlockResearch {
    pub fn matrix(&self) -> &FieldR1cs {
        &self.r1cs
    }

    pub fn witness(&self) -> &[F128] {
        &self.witness
    }

    pub const fn useful_rows(&self) -> usize {
        self.useful_rows
    }

    pub const fn class_id(&self) -> CanonicalHistoryStepClassId {
        self.class_id
    }
}

/// Assemble the complete direct-block portion against an already natively
/// prepared boundary, without requiring a newly frozen recursive parent.
#[doc(hidden)]
pub fn assemble_frozen_direct_block_research<const TIER: usize>(
    current: HistoryStepBlockInput<TIER>,
) -> Result<FrozenDirectBlockResearch, HistoryStepError> {
    let HistoryStepBlockInput {
        start_accumulator,
        end_accumulator,
        components,
        authorization,
        sealed_header,
        parent_header,
        ..
    } = current;
    let class_id = canonical_history_step_class_id(TIER).ok_or(HistoryStepError::InvalidClass)?;
    let mut builder = FieldR1csBuilder::new();
    let parent_id = digest_lanes(&noid_chain::hash_block_header(&parent_header))
        .map(|value| LinExpr::from_wire(builder.alloc_f128(flat_of(value))));
    let assembly = build_block_slots_selected_zk(
        &mut builder,
        &start_accumulator,
        &end_accumulator,
        &components,
        &sealed_header,
        TIER,
        authorization,
        &parent_header,
        &parent_id,
        BlockRelationProfile::V2,
    );
    let useful_rows = builder.num_wires();
    finalize_selected_zk_block_region(assembly, canonical_history_step_shape(class_id).m).map_err(
        |source| {
            HistoryStepError::sidecar(
                HistoryStepSidecarOperation::FinalizeCurrentDirectBlock,
                source,
            )
        },
    )?;
    let (r1cs, witness) = builder.build();
    Ok(FrozenDirectBlockResearch {
        r1cs,
        witness,
        useful_rows,
        class_id,
    })
}

impl FrozenHistoryStep {
    pub fn matrix(&self) -> &FieldR1cs {
        &self.r1cs
    }

    #[doc(hidden)]
    pub fn witness(&self) -> &[F128] {
        &self.witness
    }

    pub const fn useful_rows(&self) -> usize {
        self.useful_rows
    }

    pub const fn class_id(&self) -> CanonicalHistoryStepClassId {
        self.class_id
    }

    pub fn parent_recursion_vk(&self) -> &LinkRegionSidecarVk {
        self.preparations.recursion.vk()
    }

    pub fn direct_block_vk(&self) -> &BlockRegionSidecarVk {
        self.preparations.direct_block.vk()
    }

    pub fn into_matrix(self) -> FieldR1cs {
        self.r1cs
    }
}

#[derive(Clone, Debug)]
pub struct HistoryStepProof {
    pub(super) field_proof: C1FieldR1csProof,
    pub(super) commitment: Commitment,
    pub(super) io: Vec<F128>,
    pub(super) sidecar: JointC1RegionSidecarProof,
}

impl HistoryStepProof {
    pub fn field_proof(&self) -> &C1FieldR1csProof {
        &self.field_proof
    }

    pub fn commitment(&self) -> &Commitment {
        &self.commitment
    }

    pub fn io(&self) -> &[F128] {
        &self.io
    }
}

/// Persisted atomic history authority for exactly one accepted block.
pub struct HistoryStepTerminal {
    pub(super) height: u64,
    pub(super) semantic_id: [u8; 32],
    pub(super) class_id: CanonicalHistoryStepClassId,
    pub(super) accumulator: ChainAccumulator,
    pub(super) proof: HistoryStepProof,
}

impl HistoryStepTerminal {
    fn from_proof(
        runtime: &HistoryStepRuntime,
        class_id: CanonicalHistoryStepClassId,
        proof: HistoryStepProof,
    ) -> Result<Self, HistoryStepError> {
        validate_envelope_against_runtime(runtime, class_id, &proof)?;
        let accumulator = history_step_bank_block_accumulator(runtime.bank(), &proof.io)?;
        Ok(Self {
            height: accumulator.height,
            semantic_id: accumulator.tip_semantic_id,
            class_id,
            accumulator,
            proof,
        })
    }

    pub const fn wire_version(&self) -> u8 {
        noid_chain::history_step::history_step_terminal_wire_version_with_activation(
            self.height,
            noid_chain::consensus::params::V1_1_ACTIVATION_HEIGHT,
        )
    }

    pub const fn height(&self) -> u64 {
        self.height
    }

    pub const fn semantic_id(&self) -> [u8; 32] {
        self.semantic_id
    }

    pub const fn class_id(&self) -> CanonicalHistoryStepClassId {
        self.class_id
    }

    pub const fn accumulator(&self) -> &ChainAccumulator {
        &self.accumulator
    }

    pub fn proof(&self) -> &HistoryStepProof {
        &self.proof
    }
}

pub(super) fn validate_terminal_metadata(
    runtime: &HistoryStepRuntime,
    terminal: &HistoryStepTerminal,
    expected_boundary: Option<(&BlockHeader, &BlockHeader)>,
) -> Result<ChainAccumulator, HistoryStepError> {
    validate_envelope_against_runtime(runtime, terminal.class_id, &terminal.proof)?;
    let accumulator = history_step_bank_block_accumulator(runtime.bank(), &terminal.proof.io)?;
    let base = terminal.proof.io[runtime.bank().layout().base] == F128::ONE;
    if terminal.height != accumulator.height
        || terminal.semantic_id != accumulator.tip_semantic_id
        || terminal.accumulator != accumulator
        || terminal.height == 0
        || base != (terminal.height == 1)
    {
        return Err(HistoryStepError::TerminalMetadata);
    }
    if let Some((tip_header, epoch_anchor_header)) = expected_boundary {
        accumulator
            .validate_local_header_boundary(tip_header, epoch_anchor_header)
            .map_err(|_| HistoryStepError::HeaderBinding)?;
    }
    Ok(accumulator)
}

/// Consuming capability returned only after proof replay and every
/// authenticated matrix obligation have succeeded.
#[must_use = "accepted HistoryStep authority must be consumed by block application"]
pub struct AcceptedHistoryStepTerminal {
    height: u64,
    semantic_id: [u8; 32],
    class_id: CanonicalHistoryStepClassId,
    accumulator: ChainAccumulator,
}

impl AcceptedHistoryStepTerminal {
    pub const fn height(&self) -> u64 {
        self.height
    }

    pub const fn semantic_id(&self) -> [u8; 32] {
        self.semantic_id
    }

    pub const fn class_id(&self) -> CanonicalHistoryStepClassId {
        self.class_id
    }

    pub const fn accumulator(&self) -> &ChainAccumulator {
        &self.accumulator
    }
}

/// Exact already-proved parent authority consumed by one recursive assembly.
pub struct HistoryStepParent<'a> {
    terminal: &'a HistoryStepTerminal,
}

impl<'a> HistoryStepParent<'a> {
    pub fn new(
        runtime: &HistoryStepRuntime,
        terminal: &'a HistoryStepTerminal,
    ) -> Result<Self, HistoryStepError> {
        validate_terminal_metadata(runtime, terminal, None)?;
        Ok(Self { terminal })
    }

    pub fn envelope(&self) -> &'a HistoryStepProof {
        &self.terminal.proof
    }
}

fn validate_runtime_witness_geometry(
    class: CanonicalHistoryStepClassId,
    shape: FieldShape,
    matrix_shape: FieldShape,
    matrix_useful_rows: usize,
    witness_useful_rows: usize,
    witness_fields: usize,
) -> Result<(), HistoryStepError> {
    if matrix_shape != shape {
        return Err(HistoryStepError::RuntimeMatrix(class));
    }
    let expected_witness_fields = 1usize << shape.m;
    if witness_fields != expected_witness_fields {
        return Err(HistoryStepError::RuntimeWitnessShape {
            class,
            expected: expected_witness_fields,
            actual: witness_fields,
        });
    }
    if witness_useful_rows != matrix_useful_rows {
        return Err(HistoryStepError::RuntimeUsefulRows {
            class,
            expected: matrix_useful_rows,
            actual: witness_useful_rows,
        });
    }
    Ok(())
}

fn validate_built_against_bank(
    runtime: &HistoryStepRuntime,
    built: &BuiltHistoryStep,
    matrix: &HistoryStepMatrixLease,
) -> Result<(), HistoryStepError> {
    let bank = runtime.bank();
    if !built.class_id.is_canonical()
        || built.spec.transcript_lanes() != bank.spec().transcript_lanes()
        || built.io.len() != bank.spec().io_len
        || history_step_bank_tip_class(bank, &built.io)? != built.class_id
    {
        return Err(HistoryStepError::InvalidIo);
    }
    let entry = bank.entry(built.class_id);
    validate_runtime_witness_geometry(
        built.class_id,
        canonical_history_step_shape(built.class_id),
        matrix.field_shape(),
        matrix.useful_rows(),
        built.useful_rows,
        built.witness.len(),
    )?;
    if pcs_params_statement_bytes(&built.pcs_params)
        != pcs_params_statement_bytes(&canonical_history_step_pcs_params(built.class_id))
    {
        return Err(HistoryStepError::PcsParams);
    }
    if matrix.statement_digest() != entry.matrix_digest() {
        return Err(HistoryStepError::RuntimeMatrix(built.class_id));
    }
    if built.preparations.recursion.vk().transcript_digest() != entry.parent_recursion_vk_digest()
        || built.preparations.direct_block.vk().transcript_digest()
            != entry.direct_block_vk_digest()
    {
        return Err(HistoryStepError::ClassPin);
    }
    Ok(())
}

pub(super) fn validate_envelope_against_runtime(
    runtime: &HistoryStepRuntime,
    class_id: CanonicalHistoryStepClassId,
    envelope: &HistoryStepProof,
) -> Result<(), HistoryStepError> {
    let bank = runtime.bank();
    if !class_id.is_canonical()
        || envelope.io.len() != bank.spec().io_len
        || history_step_bank_tip_class(bank, &envelope.io)? != class_id
    {
        return Err(HistoryStepError::InvalidIo);
    }
    let entry = bank.entry(class_id);
    if pcs_params_statement_bytes(&envelope.commitment.params)
        != pcs_params_statement_bytes(entry.pcs_params())
    {
        return Err(HistoryStepError::PcsParams);
    }
    Ok(())
}

struct PreparedParentReplay {
    fresh: C1FreshLincheckClaim,
    child_recordings: Vec<LayoutRecordedChannel>,
    r_prev_recordings: Vec<LayoutRecordedChannel>,
}

pub(super) fn capture_scratch_recording(
    recording: &RecordedChannel,
    builder: &FieldR1csBuilder,
) -> LayoutRecordedChannel {
    LayoutRecordedChannel {
        layout: compile_duplex(&recording.ops),
        data_flat: recording.data_flat.clone(),
        challenges: recording
            .challenge_wires
            .iter()
            .map(|wire| Some(wire.eval(builder.values())))
            .collect(),
        post_state: recording.post_state,
        perms: recording.perms,
    }
}

/// Authenticated predecessor-class selector. Both shape-specific verifier
/// arms are present in every current-class matrix; this one-hot changes only
/// which arm may reject and which bank lane folds.
struct ParentClassSelectorTrace {
    class: LinExpr,
    one_hot: [LinExpr; HISTORY_STEP_TIER_SLOT_COUNT],
}

impl ParentClassSelectorTrace {
    fn bind(
        builder: &mut FieldR1csBuilder,
        authenticated_class: &LinExpr,
        native_class: CanonicalHistoryStepClassId,
    ) -> Result<Self, HistoryStepError> {
        if !native_class.is_canonical() {
            return Err(HistoryStepError::InvalidClass);
        }
        let candidates: [CanonicalHistoryStepClassId; HISTORY_STEP_TIER_SLOT_COUNT] =
            std::array::from_fn(|parent_slot| {
                CanonicalHistoryStepClassId::new(parent_slot).expect("canonical parent class")
            });
        let one_hot = std::array::from_fn(|parent_slot| {
            LinExpr::from_wire(builder.alloc_bool(native_class.index() == parent_slot))
        });
        let mut seen = LinExpr::zero();
        for selector in &one_hot {
            let overlap = mul(builder, selector, &seen);
            pin_eq(builder, &overlap, &LinExpr::zero());
            seen = seen.add(selector);
        }
        pin_eq(builder, &seen, &LinExpr::constant(F128::ONE));
        let class =
            one_hot
                .iter()
                .zip(candidates)
                .fold(LinExpr::zero(), |sum, (selector, candidate)| {
                    sum.add(&selector.scale(f128_from_u128(candidate.wire_id() as u128)))
                });
        pin_eq(builder, authenticated_class, &class);
        Ok(Self { class, one_hot })
    }

    #[cfg(test)]
    fn select(
        &self,
        builder: &mut FieldR1csBuilder,
        values: [LinExpr; HISTORY_STEP_TIER_SLOT_COUNT],
    ) -> LinExpr {
        self.one_hot
            .iter()
            .zip(values)
            .fold(LinExpr::zero(), |sum, (selector, value)| {
                sum.add(&mul(builder, selector, &value))
            })
    }
}

struct ScratchParentRecordingPass {
    child: Option<LayoutRecordedChannel>,
    r_prev: LayoutRecordedChannel,
    query_lane_values: Vec<F128>,
}

fn run_scratch_parent_recording_pass(
    runtime: &HistoryStepRuntime,
    class_id: CanonicalHistoryStepClassId,
    envelope: &HistoryStepProof,
    matrix_digest: &[u8; 32],
    post_commit_digest: &[u8; 32],
) -> Result<ScratchParentRecordingPass, HistoryStepError> {
    let entry = runtime.bank().entry(class_id);
    let mut builder = FieldR1csBuilder::new_witness_only();
    let statement_digest = alloc_pinned_flat_digest(&mut builder, matrix_digest);
    let post_commit_digest = alloc_pinned_flat_digest(&mut builder, post_commit_digest);
    let root = alloc_flat_digest(&mut builder, &envelope.commitment.root);
    let io = envelope
        .io
        .iter()
        .copied()
        .map(|value| LinExpr::from_wire(builder.alloc_f128(value)))
        .collect::<Vec<_>>();
    let proof = C1FieldR1csProofTrace::alloc_shape_mode(
        &mut builder,
        &envelope.field_proof,
        &entry.shape(),
        entry.pcs_params(),
        false,
    );
    let mut obligations = PcsWalkObligations::default();
    let mut channel = FsChannelUnionRecorder::new_c1(HISTORY_STEP_PROOF_DOMAIN);
    let mut child_recording = None;
    let mut sidecar_result = Ok(());
    verify_field_c1_trace_deferred_region_with_post_commit_context_expr(
        &mut builder,
        &mut channel,
        &entry.shape(),
        entry.pcs_params(),
        &statement_digest,
        &root,
        &proof,
        runtime.bank().spec(),
        &io,
        &post_commit_digest,
        Some(&mut obligations),
        |builder, context| match verify_joint_c1_region_sidecar_trace_post_commit(
            builder,
            context,
            runtime.parent_recursion_vk(),
            runtime
                .direct_block_vk(class_id.current_slot())
                .expect("canonical parent arm has a direct-Block VK"),
            &envelope.sidecar,
        ) {
            Ok(recording) => child_recording = Some(recording),
            Err(error) => {
                sidecar_result = Err(HistoryStepError::sidecar(
                    HistoryStepSidecarOperation::ScratchJointC1Replay,
                    error,
                ))
            }
        },
    );
    sidecar_result?;
    let r_prev = channel.finish();
    let query_lanes = history_step_query_lane_count(entry.pcs_params());
    let query_lane_start = r_prev
        .challenge_wires
        .len()
        .checked_sub(query_lanes)
        .ok_or(HistoryStepError::ParentRecording)?;
    let query_lane_values = r_prev
        .challenge_wires
        .iter()
        .skip(query_lane_start)
        .map(|wire| wire.eval(builder.values()))
        .collect();
    Ok(ScratchParentRecordingPass {
        child: child_recording
            .as_ref()
            .map(|recording| capture_scratch_recording(recording, &builder)),
        r_prev: capture_scratch_recording(&r_prev, &builder),
        query_lane_values,
    })
}

fn shape_only_parent_arm(
    runtime: &HistoryStepRuntime,
    class_id: CanonicalHistoryStepClassId,
    io: Vec<F128>,
) -> Result<(HistoryStepProof, ScratchParentRecordingPass), HistoryStepError> {
    let entry = runtime.bank().entry(class_id);
    let (field_proof, native_root) =
        shape_only_field_r1cs_proof_c1(&entry.shape(), entry.pcs_params());
    let mut envelope = HistoryStepProof {
        field_proof,
        commitment: Commitment {
            root: native_root,
            params: entry.pcs_params().clone(),
        },
        io,
        sidecar: shape_only_joint_c1_region_sidecar_proof(
            runtime.parent_recursion_vk(),
            runtime
                .direct_block_vk(class_id.current_slot())
                .ok_or(HistoryStepError::RuntimeBlockVk(class_id.current_slot()))?,
            entry.shape().m,
        )
        .map_err(|source| {
            HistoryStepError::sidecar(HistoryStepSidecarOperation::BaseShapeOnlyJointC1, source)
        })?,
    };
    let scratch = run_scratch_parent_recording_pass(
        runtime,
        class_id,
        &envelope,
        &entry.matrix_digest(),
        &entry.post_commit_digest(),
    )?;
    super::super::trace::self_verify::patch_shape_only_query_positions_c1(
        &mut envelope.field_proof,
        entry.pcs_params(),
        &scratch.query_lane_values,
    );
    if scratch.child.is_none() {
        return Err(HistoryStepError::ParentRecording);
    }
    Ok((envelope, scratch))
}

fn prepare_parent_replay<'a>(
    runtime: &HistoryStepRuntime,
    parent: &HistoryStepParent<'a>,
) -> Result<
    (
        PreparedParentReplay,
        [PreparedParentEnvelope<'a>; HISTORY_STEP_TIER_SLOT_COUNT],
    ),
    HistoryStepError,
> {
    let envelope = parent.envelope();
    let class_id = parent.terminal.class_id;
    validate_envelope_against_runtime(runtime, class_id, envelope)?;
    let bank = runtime.bank();
    let entry = bank.entry(class_id);
    let matrix_digest = entry.matrix_digest();
    let post_commit_digest = entry.post_commit_digest();
    let live_slot = class_id.current_slot();
    let ghost_slot = 1usize
        .checked_sub(live_slot)
        .ok_or(HistoryStepError::InvalidClass)?;
    let ghost_class =
        CanonicalHistoryStepClassId::new(ghost_slot).ok_or(HistoryStepError::InvalidClass)?;
    let (ghost_envelope, ghost_scratch) =
        shape_only_parent_arm(runtime, ghost_class, envelope.io.clone())?;
    let child_layout = runtime
        .parent_geometry()
        .child_layout(live_slot)
        .ok_or(HistoryStepError::ParentRecording)?
        .clone();
    let r_prev_layout = runtime
        .parent_geometry()
        .r_prev_layout(live_slot)
        .ok_or(HistoryStepError::ParentRecording)?
        .clone();

    let mut challenger =
        LayoutRecordingChallenger::new_c1(HISTORY_STEP_PROOF_DOMAIN, r_prev_layout.clone());
    let mut child_recording = None;
    let (_claim, fresh) = verify_field_c1_deferred_matrix_with_post_commit_context(
        &entry.shape(),
        &matrix_digest,
        &envelope.commitment,
        &envelope.field_proof,
        bank.spec(),
        &envelope.io,
        &post_commit_digest,
        &envelope.sidecar,
        &mut challenger,
        |sidecar, context| {
            let recording = verify_joint_c1_region_sidecar_post_commit_layout_captured(
                runtime.parent_recursion_vk(),
                runtime
                    .direct_block_vk(live_slot)
                    .ok_or(VerifyError::Auxiliary)?,
                sidecar,
                context,
                child_layout.clone(),
            )
            .map_err(|error| auxiliary_sidecar_error("parent joint C1 sidecar", error))?;
            child_recording = Some(recording);
            Ok(())
        },
    )?;
    let r_prev_recording = challenger
        .finish()
        .map_err(|_| HistoryStepError::ParentRecording)?;
    let child_recording = child_recording.ok_or(HistoryStepError::ParentRecording)?;
    if child_recording.layout != child_layout || r_prev_recording.layout != r_prev_layout {
        return Err(HistoryStepError::ParentRecording);
    }
    let ghost_child = ghost_scratch
        .child
        .ok_or(HistoryStepError::ParentRecording)?;
    let (envelopes, child_recordings, r_prev_recordings) = match live_slot {
        0 => (
            [
                PreparedParentEnvelope::Persisted(envelope),
                PreparedParentEnvelope::Local(ghost_envelope),
            ],
            vec![child_recording, ghost_child],
            vec![r_prev_recording, ghost_scratch.r_prev],
        ),
        1 => (
            [
                PreparedParentEnvelope::Local(ghost_envelope),
                PreparedParentEnvelope::Persisted(envelope),
            ],
            vec![ghost_child, child_recording],
            vec![ghost_scratch.r_prev, r_prev_recording],
        ),
        _ => return Err(HistoryStepError::InvalidClass),
    };
    Ok((
        PreparedParentReplay {
            fresh,
            child_recordings,
            r_prev_recordings,
        },
        envelopes,
    ))
}

enum PreparedParentEnvelope<'a> {
    Local(HistoryStepProof),
    Persisted(&'a HistoryStepProof),
}

impl PreparedParentEnvelope<'_> {
    fn proof(&self) -> &HistoryStepProof {
        match self {
            Self::Local(proof) => proof,
            Self::Persisted(proof) => proof,
        }
    }
}

struct PreparedHistoryStepParent<'a> {
    base: bool,
    selected_class: CanonicalHistoryStepClassId,
    current_class: CanonicalHistoryStepClassId,
    envelopes: [PreparedParentEnvelope<'a>; HISTORY_STEP_TIER_SLOT_COUNT],
    replay: PreparedParentReplay,
    fold_proofs: [C1MatrixFoldProof; HISTORY_STEP_TIER_SLOT_COUNT],
    io: Vec<F128>,
}

fn zero_fresh_claim(shape: FieldShape) -> C1FreshLincheckClaim {
    C1FreshLincheckClaim {
        alpha: F256::ZERO,
        z_skip: F256::ZERO,
        x_inner_rest: vec![F256::ZERO; shape.k_log - shape.k_skip],
        r_inner_rest: vec![F256::ZERO; shape.k_log - shape.k_skip],
        z_partial: vec![F256::ZERO; 1usize << shape.k_skip],
        value: F256::ZERO,
    }
}

pub(super) fn zero_fold_proof(k_log: usize) -> C1MatrixFoldProof {
    C1MatrixFoldProof {
        phase1_rounds: vec![[F256::ZERO; 2]; k_log + 1],
        g_v: F256::ZERO,
        g_e: F256::ZERO,
        phase2_rounds: vec![[F256::ZERO; 2]; k_log],
        final_matrix_eval: F256::ZERO,
    }
}

fn prepare_history_step_base<'a, const TIER: usize>(
    runtime: &HistoryStepRuntime,
    current: &HistoryStepBlockInput<TIER>,
) -> Result<PreparedHistoryStepParent<'a>, HistoryStepError> {
    validate_legacy_block_profile(&current)?;
    let genesis = genesis_accumulator();
    if current.start_accumulator != genesis || current.end_accumulator.height != 1 {
        return Err(HistoryStepError::ParentBoundary);
    }
    let selected_class = CanonicalHistoryStepClassId::from_index(0)
        .expect("class zero is the canonical internal base shape");
    let current_class =
        canonical_history_step_class_id(TIER).ok_or(HistoryStepError::InvalidClass)?;
    let base_io = history_step_bank_base_output_io(runtime.bank(), selected_class, &genesis)?;
    let class_0 = CanonicalHistoryStepClassId::new(0).expect("class zero");
    let (envelope_0, scratch_0) = shape_only_parent_arm(runtime, class_0, base_io.clone())?;
    let class_1 = CanonicalHistoryStepClassId::new(1).expect("class one");
    let (envelope_1, scratch_1) = shape_only_parent_arm(runtime, class_1, base_io)?;
    let child_0 = scratch_0.child.ok_or(HistoryStepError::ParentRecording)?;
    let child_1 = scratch_1.child.ok_or(HistoryStepError::ParentRecording)?;
    let fold_proofs = std::array::from_fn(|slot| {
        let class = CanonicalHistoryStepClassId::new(slot).expect("canonical parent class");
        zero_fold_proof(runtime.bank().entry(class).shape().k_log)
    });
    Ok(PreparedHistoryStepParent {
        base: true,
        selected_class,
        current_class,
        replay: PreparedParentReplay {
            fresh: zero_fresh_claim(runtime.bank().entry(selected_class).shape()),
            child_recordings: vec![child_0, child_1],
            r_prev_recordings: vec![scratch_0.r_prev, scratch_1.r_prev],
        },
        fold_proofs,
        io: history_step_bank_base_output_io(
            runtime.bank(),
            current_class,
            &current.end_accumulator,
        )?,
        envelopes: [
            PreparedParentEnvelope::Local(envelope_0),
            PreparedParentEnvelope::Local(envelope_1),
        ],
    })
}

fn prepare_history_step_recursive<'a, const TIER: usize>(
    runtime: &HistoryStepRuntime,
    parent: HistoryStepParent<'a>,
    current: &HistoryStepBlockInput<TIER>,
) -> Result<PreparedHistoryStepParent<'a>, HistoryStepError> {
    validate_legacy_block_profile(&current)?;
    let bank = runtime.bank();
    let envelope = parent.envelope();
    let selected_class = history_step_bank_tip_class(bank, &envelope.io)?;
    if selected_class != parent.terminal.class_id {
        return Err(HistoryStepError::InvalidClass);
    }
    let current_class =
        canonical_history_step_class_id(TIER).ok_or(HistoryStepError::InvalidClass)?;
    if block_acc_lanes(&current.start_accumulator)
        != envelope.io[bank.layout().block_accumulator..bank.layout().block_accumulator + ACC_LANES]
    {
        return Err(HistoryStepError::ParentBoundary);
    }
    let parent_matrix = runtime.load_matrix(selected_class)?;
    let (replay, envelopes) = prepare_parent_replay(runtime, &parent)?;
    let routed = route_carry_and_fold_history_step_lane_canonical(
        bank,
        &envelope.io,
        selected_class,
        current_class,
        &parent_matrix,
        &replay.fresh,
        &current.end_accumulator,
    )?;
    // Release the predecessor lease before the outer class is built.
    drop(parent_matrix);
    let (fold_proof, _claim, io) = routed.into_parts();
    let mut fold_proofs = std::array::from_fn(|slot| {
        let class = CanonicalHistoryStepClassId::new(slot).expect("canonical parent class");
        zero_fold_proof(runtime.bank().entry(class).shape().k_log)
    });
    fold_proofs[selected_class.current_slot()] = fold_proof;
    Ok(PreparedHistoryStepParent {
        base: false,
        selected_class,
        current_class,
        envelopes,
        replay,
        fold_proofs,
        io,
    })
}

/// Prove one witness-only HistoryStep against the exact matrix lease paired
/// with it during assembly. The joint C1 sidecar runs inside the single outer
/// Field post-commit context.
pub fn prove_built_history_step(
    runtime: &HistoryStepRuntime,
    built: &BuiltHistoryStep,
) -> Result<HistoryStepProof, HistoryStepError> {
    validate_built_against_bank(runtime, built, &built.matrix)?;
    let bank = runtime.bank();
    let entry = bank.entry(built.class_id);
    macro_rules! prove_with_matrix {
        ($prove:path, $matrix:expr) => {{
            let parent_plan = built.preparations.recursion.certified_c1_prover_plan()?;
            let direct_block_plan = built.preparations.direct_block.certified_c1_prover_plan()?;
            let mut challenger = FsLaneChallenger::new_c1(HISTORY_STEP_PROOF_DOMAIN);
            $prove(
                $matrix,
                &built.witness,
                &built.pcs_params,
                &built.spec,
                &built.io,
                &entry.post_commit_digest(),
                &mut challenger,
                |context| -> Result<JointC1RegionSidecarProof, RegionSidecarError> {
                    let (proof, claims) = crate::region_sidecar::prove_joint_c1_region_sidecar(
                        &parent_plan,
                        &direct_block_plan,
                        context.witness(),
                        context,
                    )?;
                    context.append_c1_claims(claims);
                    Ok(proof)
                },
            )
        }};
    }
    let (field_proof, sidecar, commitment, _) = match &built.matrix {
        HistoryStepMatrixLease::Resident(matrix) => prove_with_matrix!(
            prove_field_c1_with_public_io_and_post_commit_context,
            matrix.as_ref()
        ),
        HistoryStepMatrixLease::Compact(matrix) => prove_with_matrix!(
            prove_field_compact_c1_with_public_io_and_post_commit_context,
            matrix.as_ref()
        ),
    };
    Ok(HistoryStepProof {
        field_proof,
        commitment,
        io: built.io.clone(),
        sidecar: sidecar?,
    })
}

/// Cooperative-cancellation twin of [`prove_built_history_step`]. The flag
/// is sampled between the expensive transcript phases; if it remains clear,
/// the resulting proof is byte-identical to the ordinary path.
pub fn prove_built_history_step_cancellable(
    runtime: &HistoryStepRuntime,
    built: &BuiltHistoryStep,
    cancellation: &std::sync::atomic::AtomicBool,
) -> Result<HistoryStepProof, HistoryStepError> {
    if cancellation.load(std::sync::atomic::Ordering::Acquire) {
        return Err(HistoryStepError::Cancelled);
    }
    validate_built_against_bank(runtime, built, &built.matrix)?;
    let bank = runtime.bank();
    let entry = bank.entry(built.class_id);
    macro_rules! prove_with_matrix {
        ($prove:path, $matrix:expr) => {{
            let parent_plan = built.preparations.recursion.certified_c1_prover_plan()?;
            let direct_block_plan = built.preparations.direct_block.certified_c1_prover_plan()?;
            let mut challenger = FsLaneChallenger::new_c1(HISTORY_STEP_PROOF_DOMAIN);
            $prove(
                $matrix,
                &built.witness,
                &built.pcs_params,
                &built.spec,
                &built.io,
                &entry.post_commit_digest(),
                cancellation,
                &mut challenger,
                |context| -> Result<JointC1RegionSidecarProof, RegionSidecarError> {
                    let (proof, claims) = crate::region_sidecar::prove_joint_c1_region_sidecar(
                        &parent_plan,
                        &direct_block_plan,
                        context.witness(),
                        context,
                    )?;
                    context.append_c1_claims(claims);
                    Ok(proof)
                },
            )
            .map_err(|_| HistoryStepError::Cancelled)
        }};
    }
    let (field_proof, sidecar, commitment, _) = match &built.matrix {
        HistoryStepMatrixLease::Resident(matrix) => prove_with_matrix!(
            prove_field_c1_with_public_io_and_post_commit_context_cancellable,
            matrix.as_ref()
        ),
        HistoryStepMatrixLease::Compact(matrix) => prove_with_matrix!(
            prove_field_compact_c1_with_public_io_and_post_commit_context_cancellable,
            matrix.as_ref()
        ),
    }?;
    Ok(HistoryStepProof {
        field_proof,
        commitment,
        io: built.io.clone(),
        sidecar: sidecar?,
    })
}

pub fn prove_built_history_step_terminal(
    runtime: &HistoryStepRuntime,
    built: &BuiltHistoryStep,
) -> Result<HistoryStepTerminal, HistoryStepError> {
    let proof = prove_built_history_step(runtime, built)?;
    HistoryStepTerminal::from_proof(runtime, built.class_id, proof)
}

pub fn prove_built_history_step_terminal_cancellable(
    runtime: &HistoryStepRuntime,
    built: &BuiltHistoryStep,
    cancellation: &std::sync::atomic::AtomicBool,
) -> Result<HistoryStepTerminal, HistoryStepError> {
    let proof = prove_built_history_step_cancellable(runtime, built, cancellation)?;
    if cancellation.load(std::sync::atomic::Ordering::Acquire) {
        return Err(HistoryStepError::Cancelled);
    }
    HistoryStepTerminal::from_proof(runtime, built.class_id, proof)
}

/// Replay a HistoryStep tip and return the only acceptance path: a consuming terminal
/// decision that still requires the fresh tip matrix and every live bank lane.
pub fn verify_history_step_pending(
    runtime: &HistoryStepRuntime,
    class_id: CanonicalHistoryStepClassId,
    envelope: &HistoryStepProof,
) -> Result<PendingHistoryStepBankDecision, HistoryStepError> {
    validate_envelope_against_runtime(runtime, class_id, envelope)?;
    let bank = runtime.bank();
    let entry = bank.entry(class_id);
    let mut challenger = FsLaneChallenger::new_c1(HISTORY_STEP_PROOF_DOMAIN);
    let (_claim, fresh) = verify_field_c1_deferred_matrix_with_post_commit_context(
        &entry.shape(),
        &entry.matrix_digest(),
        &envelope.commitment,
        &envelope.field_proof,
        bank.spec(),
        &envelope.io,
        &entry.post_commit_digest(),
        &envelope.sidecar,
        &mut challenger,
        |sidecar, context| {
            verify_joint_c1_region_sidecar_post_commit(
                runtime.parent_recursion_vk(),
                runtime
                    .direct_block_vk(class_id.current_slot())
                    .ok_or(VerifyError::Auxiliary)?,
                sidecar,
                context,
            )
            .map_err(|error| auxiliary_sidecar_error("tip joint C1 sidecar", error))?;
            Ok(())
        },
    )?;
    let replay = bank.bind_verified_tip_replay(
        class_id,
        entry.matrix_digest(),
        entry.post_commit_digest(),
        fresh,
    )?;
    PendingHistoryStepBankDecision::begin(bank, &envelope.io, replay).map_err(Into::into)
}

pub fn verify_history_step_terminal(
    runtime: &HistoryStepRuntime,
    terminal: &HistoryStepTerminal,
    expected_header: &BlockHeader,
    epoch_anchor_header: &BlockHeader,
) -> Result<AcceptedHistoryStepTerminal, HistoryStepError> {
    let accumulator = validate_terminal_metadata(
        runtime,
        terminal,
        Some((expected_header, epoch_anchor_header)),
    )?;
    let pending = verify_history_step_pending(runtime, terminal.class_id, &terminal.proof)?;
    let accepted = runtime.decide(pending)?;
    if accepted.tip_class() != terminal.class_id
        || accepted.block_accumulator() != &block_acc_lanes(&accumulator)
        || accepted.base() != (terminal.height == 1)
    {
        return Err(HistoryStepError::TerminalMetadata);
    }
    Ok(AcceptedHistoryStepTerminal {
        height: terminal.height,
        semantic_id: terminal.semantic_id,
        class_id: terminal.class_id,
        accumulator,
    })
}

/// Replay the pre-fork terminal without discharging any matrix claims from
/// a local cache. A certificate must close every resulting obligation.
pub fn prepare_history_step_retirement(
    runtime: &HistoryStepRuntime,
    terminal: &HistoryStepTerminal,
    expected_header: &BlockHeader,
    epoch_anchor_header: &BlockHeader,
    target: crate::acceptance::history_step_bank::retirement::HistoryStepRetirementTarget,
) -> Result<
    crate::acceptance::history_step_bank::retirement::HistoryStepRetirementRequest,
    crate::acceptance::history_step_bank::retirement::HistoryStepRetirementError,
> {
    use crate::acceptance::history_step_bank::retirement::{
        HistoryStepRetirementError, HistoryStepRetirementRequest,
    };
    target.check_parent_height(expected_header.height)?;
    target.check_legacy_bank(runtime.bank().digest())?;
    validate_terminal_metadata(
        runtime,
        terminal,
        Some((expected_header, epoch_anchor_header)),
    )
    .map_err(HistoryStepRetirementError::Replay)?;
    let pending = verify_history_step_pending(runtime, terminal.class_id, &terminal.proof)
        .map_err(HistoryStepRetirementError::Replay)?;
    HistoryStepRetirementRequest::from_pending(
        pending,
        target,
        expected_header,
        epoch_anchor_header,
    )
}

#[derive(Clone, Copy)]
enum HistoryStepAssemblyMode {
    Frozen,
    WitnessOnly,
}

enum HistoryStepAssemblyOutput {
    Frozen(FrozenHistoryStep),
    WitnessOnly(BuiltHistoryStep),
}

pub(super) struct DeferredHistoryStepIo {
    tip_block_id: [DeferredWitnessSlot; 2],
    epoch_anchor_id: [DeferredWitnessSlot; 2],
}

pub(super) fn allocate_deferred_history_step_io(
    builder: &mut FieldR1csBuilder,
    spec: &PublicIoSpec,
    values: &[F128],
    block_accumulator: usize,
) -> (Vec<LinExpr>, DeferredHistoryStepIo) {
    assert_eq!(values.len(), spec.io_len);
    let base = spec.io_slice.start();
    while builder.num_wires() < base {
        builder.alloc_f128(F128::ZERO);
    }

    let mut tip_0 = None;
    let mut tip_1 = None;
    let mut epoch_0 = None;
    let mut epoch_1 = None;
    let cells = values
        .iter()
        .copied()
        .enumerate()
        .map(|(index, value)| {
            let relative = index.checked_sub(block_accumulator);
            let slot = match relative {
                Some(1) => &mut tip_0,
                Some(2) => &mut tip_1,
                Some(8) => &mut epoch_0,
                Some(9) => &mut epoch_1,
                _ => return LinExpr::from_wire(builder.alloc_f128(value)),
            };
            let (wire, deferred) = builder.alloc_deferred_f128(value);
            *slot = Some(deferred);
            LinExpr::from_wire(wire)
        })
        .collect();
    (
        cells,
        DeferredHistoryStepIo {
            tip_block_id: [
                tip_0.expect("HistoryStep IO has tip lane zero"),
                tip_1.expect("HistoryStep IO has tip lane one"),
            ],
            epoch_anchor_id: [
                epoch_0.expect("HistoryStep IO has epoch lane zero"),
                epoch_1.expect("HistoryStep IO has epoch lane one"),
            ],
        },
    )
}

impl DeferredHistoryStepIo {
    pub(super) fn seal(
        self,
        builder: &mut FieldR1csBuilder,
        io: &mut [F128],
        block_accumulator: usize,
        end_accumulator: &ChainAccumulator,
    ) -> Result<(), HistoryStepError> {
        let lanes = block_acc_lanes(end_accumulator);
        io[block_accumulator..block_accumulator + ACC_LANES].copy_from_slice(&lanes);
        for (slot, value) in self
            .tip_block_id
            .into_iter()
            .zip([lanes[1], lanes[2]])
            .chain(self.epoch_anchor_id.into_iter().zip([lanes[8], lanes[9]]))
        {
            builder
                .seal_deferred_f128(slot, value)
                .map_err(|_| HistoryStepError::StagedSeal)?;
        }
        Ok(())
    }
}

struct PreparedHistoryStepAssembly {
    mode: HistoryStepAssemblyMode,
    builder: FieldR1csBuilder,
    block_assembly: SelectedZkBlockSlotsAssembly,
    io_seal: DeferredHistoryStepIo,
    current_matrix: Option<HistoryStepMatrixLease>,
    io: Vec<F128>,
    spec: PublicIoSpec,
    pcs_params: PcsParams,
    shape: FieldShape,
    current_class: CanonicalHistoryStepClassId,
    parent_region: HistoryStepParentRegionPreparation,
}

/// Single-use nonce-independent HistoryStep assembly retained across PoW.
/// It has no serialization or cloning surface and owns every deferred slot.
#[must_use = "dropping a prepared HistoryStep cancels this block attempt"]
pub struct PreparedHistoryStepForPow<const TIER: usize> {
    assembly: PreparedHistoryStepAssembly,
    template_header: BlockHeader,
    start_accumulator: ChainAccumulator,
    parent_header: BlockHeader,
}

fn prepare_history_step_assembly<const TIER: usize>(
    runtime: &HistoryStepRuntime,
    prepared: PreparedHistoryStepParent<'_>,
    current: HistoryStepBlockInput<TIER>,
    mode: HistoryStepAssemblyMode,
) -> Result<PreparedHistoryStepAssembly, HistoryStepError> {
    let timing = std::env::var_os("NOIDH_HISTORY_ASSEMBLY_TIMING").is_some();
    let total_started = std::time::Instant::now();
    let mut stage_started = total_started;
    let lap = |label: &str, stage_started: &mut std::time::Instant| {
        if timing {
            eprintln!(
                "[history-assembly B{TIER}] {label}: {:.1} ms",
                stage_started.elapsed().as_secs_f64() * 1e3
            );
        }
        *stage_started = std::time::Instant::now();
    };
    let bank = runtime.bank();
    let PreparedHistoryStepParent {
        base,
        selected_class: selected_parent_class,
        current_class,
        envelopes,
        replay: prepared_parent,
        fold_proofs,
        io,
    } = prepared;
    let envelope = envelopes[selected_parent_class.current_slot()].proof();
    let effective_pages = current.components.effective_page_count();
    if noid_chain::consensus::paged_spend::BlockProofClass::for_page_count(effective_pages)
        .map(|class| class.page_capacity())
        != Some(TIER)
    {
        return Err(HistoryStepError::InvalidClass);
    }
    let layout = bank.layout();
    let spec = bank.spec().clone();
    let shape = canonical_history_step_shape(current_class);
    let pcs_params = canonical_history_step_pcs_params(current_class);
    let current_matrix = match mode {
        HistoryStepAssemblyMode::Frozen => None,
        HistoryStepAssemblyMode::WitnessOnly => Some(runtime.load_matrix(current_class)?),
    };

    let mut builder = match mode {
        HistoryStepAssemblyMode::Frozen => FieldR1csBuilder::new(),
        HistoryStepAssemblyMode::WitnessOnly => FieldR1csBuilder::new_witness_only(),
    };
    let (io_cells, io_seal) =
        allocate_deferred_history_step_io(&mut builder, &spec, &io, layout.block_accumulator);
    debug_assert_eq!(
        io_cells[layout.base].eval(builder.values()) == F128::ONE,
        base
    );
    let parent_gate = io_cells[layout.base].add_const(F128::ONE);
    let base_boolean = mul(&mut builder, &io_cells[layout.base], &parent_gate);
    pin_eq(&mut builder, &base_boolean, &LinExpr::zero());
    pin_eq(
        &mut builder,
        &io_cells[layout.tip_class],
        &LinExpr::constant(f128_from_u128(current_class.wire_id() as u128)),
    );
    lap("matrix lease + public IO", &mut stage_started);

    let r_pcs = envelopes
        .iter()
        .enumerate()
        .map(|(slot, envelope)| {
            let class = CanonicalHistoryStepClassId::new(slot).expect("canonical parent arm");
            let envelope = envelope.proof();
            RPcsProof {
                native: &envelope.field_proof.pcs_open,
                params: bank.entry(class).pcs_params(),
                commitment_root: flat_digest_lanes(&envelope.commitment.root),
            }
        })
        .collect::<Vec<_>>();
    let r_columns = prepare_history_step_parent_columns(
        &mut builder,
        &r_pcs,
        selected_parent_class.current_slot(),
        runtime.parent_geometry(),
        prepared_parent.child_recordings,
        prepared_parent.r_prev_recordings,
    )
    .map_err(|source| {
        HistoryStepError::sidecar(HistoryStepSidecarOperation::PrepareParentColumns, source)
    })?;
    lap("parent committed columns", &mut stage_started);

    // The universal parent columns above have one fixed geometry across the
    // complete two-class bank and establish the shared Link VK slices. Allocate the
    // current Block immediately after that fixed boundary. Both predecessor
    // proof arms are allocated below in canonical order, so parent selection
    // changes witness values only.
    let HistoryStepBlockInput {
        start_accumulator,
        end_accumulator,
        components,
        authorization,
        sealed_header,
        parent_header,
        semantic_id: _,
    } = current;
    // Parent seal: replay the exact parent header under both header domains.
    // Fixed geometry, so it lives inside the class-independent prefix. Its
    // glue pins land after the parent public IO is allocated below.
    let parent_seal = ParentSealTrace::alloc(&mut builder, &parent_header);
    let block_assembly: SelectedZkBlockSlotsAssembly = build_block_slots_selected_zk_prefix(
        &mut builder,
        &start_accumulator,
        &end_accumulator,
        &components,
        &sealed_header,
        TIER,
        authorization,
        &parent_header,
        &parent_seal.block_id,
        BlockRelationProfile::LegacyV1,
    );
    let block_slots = block_assembly.slots();
    // The parent header witness sits at the accumulator start height in both
    // the base and the recursive case.
    pin_eq(
        &mut builder,
        &parent_seal.height,
        &block_slots.start_acc.height,
    );
    lap("current Block trace prefix", &mut stage_started);

    let prev_roots = envelopes
        .iter()
        .map(|envelope| alloc_flat_digest(&mut builder, &envelope.proof().commitment.root))
        .collect::<Vec<_>>();
    let prev_io = envelope
        .io
        .iter()
        .copied()
        .map(|value| LinExpr::from_wire(builder.alloc_f128(value)))
        .collect::<Vec<_>>();
    let parent_selector = ParentClassSelectorTrace::bind(
        &mut builder,
        &prev_io[layout.tip_class],
        selected_parent_class,
    )?;

    // The complete whitelist and aggregate authority are inherited exactly;
    // no class digest is rebuilt or reset in a recursive transition.
    for index in layout.matrix_whitelist..layout.bank_digest + 2 {
        pin_eq(&mut builder, &io_cells[index], &prev_io[index]);
    }
    lap("parent public IO + selector", &mut stage_started);

    let mut obligations = Vec::with_capacity(HISTORY_STEP_TIER_SLOT_COUNT);
    let mut recorded_children = Vec::with_capacity(HISTORY_STEP_TIER_SLOT_COUNT);
    let mut recorded_r_prev = Vec::with_capacity(HISTORY_STEP_TIER_SLOT_COUNT);
    let mut fresh_parents = Vec::with_capacity(HISTORY_STEP_TIER_SLOT_COUNT);
    let mut arm_gates = Vec::with_capacity(HISTORY_STEP_TIER_SLOT_COUNT);
    for (slot, arm_envelope) in envelopes.iter().enumerate() {
        let class = CanonicalHistoryStepClassId::new(slot).expect("canonical parent arm");
        let entry = bank.entry(class);
        let arm_envelope = arm_envelope.proof();
        let proof = C1FieldR1csProofTrace::alloc_shape_mode(
            &mut builder,
            &arm_envelope.field_proof,
            &entry.shape(),
            entry.pcs_params(),
            false,
        );
        let statement_digest = std::array::from_fn(|lane| {
            prev_io[layout.matrix_whitelist + 2 * class.index() + lane].clone()
        });
        let post_commit_digest = std::array::from_fn(|lane| {
            prev_io[layout.post_commit_whitelist + 2 * class.index() + lane].clone()
        });
        let arm_gate = mul(&mut builder, &parent_gate, &parent_selector.one_hot[slot]);
        let mut arm_obligations = PcsWalkObligations::default();
        let mut replay_channel = BaseSelectableParentRecorder::new_c1(HISTORY_STEP_PROOF_DOMAIN);
        let mut recorded_child = None;
        let mut sidecar_result = Ok(());
        let (_parent_claim, fresh_parent) = with_pin_gate(&arm_gate, || {
            verify_field_c1_trace_deferred_region_with_post_commit_context_expr(
                &mut builder,
                &mut replay_channel,
                &entry.shape(),
                entry.pcs_params(),
                &statement_digest,
                &prev_roots[slot],
                &proof,
                bank.spec(),
                &prev_io,
                &post_commit_digest,
                Some(&mut arm_obligations),
                |builder, context| match verify_joint_c1_region_sidecar_trace_post_commit(
                    builder,
                    context,
                    runtime.parent_recursion_vk(),
                    runtime
                        .direct_block_vk(slot)
                        .expect("canonical parent arm has a direct-Block VK"),
                    &arm_envelope.sidecar,
                ) {
                    Ok(recording) => recorded_child = Some(recording),
                    Err(error) => {
                        sidecar_result = Err(HistoryStepError::sidecar(
                            HistoryStepSidecarOperation::ParentJointC1TraceReplay,
                            error,
                        ))
                    }
                },
            )
        });
        sidecar_result?;
        obligations.push(arm_obligations);
        recorded_children.push(recorded_child.ok_or(HistoryStepError::ParentRecording)?);
        recorded_r_prev.push(replay_channel.finish());
        fresh_parents.push(fresh_parent);
        arm_gates.push(arm_gate);
        if timing {
            eprintln!(
                "[history-assembly B{TIER}] parent verifier arm {slot}: {:.1} ms",
                stage_started.elapsed().as_secs_f64() * 1e3
            );
        }
        stage_started = std::time::Instant::now();
    }

    let mut accumulated = Vec::with_capacity(HISTORY_STEP_TIER_SLOT_COUNT);
    for slot in 0..HISTORY_STEP_TIER_SLOT_COUNT {
        let class = CanonicalHistoryStepClassId::new(slot).expect("canonical parent arm");
        let shape = bank.entry(class).shape();
        let lane = layout.matrix_lanes[class.index()];
        let incoming = C1MatrixAccClaimTrace {
            point: (0..lane.point_len())
                .map(|coordinate| {
                    ExtExpr::new(
                        prev_io[lane.point + 2 * coordinate].clone(),
                        prev_io[lane.point + 2 * coordinate + 1].clone(),
                    )
                })
                .collect(),
            value: ExtExpr::new(prev_io[lane.value].clone(), prev_io[lane.value + 1].clone()),
        };
        let incoming_live = prev_io[lane.live].clone();
        let fold_trace =
            C1MatrixFoldProofTrace::alloc(&mut builder, &fold_proofs[slot], shape.k_log);
        let mut fold_channel =
            FsChannelTrace::new_c1(&mut builder, HISTORY_STEP_BANK_FOLD_TRANSCRIPT_DOMAIN);
        observe_history_step_bank_fold_route_trace(
            &mut builder,
            &mut fold_channel,
            &parent_selector.class,
        );
        accumulated.push(with_pin_gate(&arm_gates[slot], || {
            verify_matrix_claim_fold_c1_trace(
                &mut builder,
                &mut fold_channel,
                shape.k_log,
                shape.k_skip,
                &fresh_parents[slot],
                &incoming,
                &incoming_live,
                &fold_trace,
            )
        }));
    }
    for (index, lane) in layout.matrix_lanes.iter().enumerate() {
        let class = CanonicalHistoryStepClassId::from_index(index)
            .expect("bank layout contains only canonical classes");
        // Every lane is gated by its own parent-tier selector bit: the
        // selected lane folds, the other three pass through because their
        // one-hot bit (and therefore the whole delta) is zero.
        let selector = &parent_selector.one_hot[class.index()];
        for coordinate in 0..lane.point_len() {
            for component in 0..2 {
                let offset = lane.point + 2 * coordinate + component;
                let previous = &prev_io[offset];
                let accumulated_component = if component == 0 {
                    &accumulated[index].point[coordinate].lo
                } else {
                    &accumulated[index].point[coordinate].hi
                };
                let selected_delta =
                    mul(&mut builder, selector, &accumulated_component.add(previous));
                let selected = previous.add(&mul(&mut builder, &parent_gate, &selected_delta));
                pin_eq(&mut builder, &io_cells[offset], &selected);
            }
        }
        for component in 0..2 {
            let offset = lane.value + component;
            let previous = &prev_io[offset];
            let accumulated_component = if component == 0 {
                &accumulated[index].value.lo
            } else {
                &accumulated[index].value.hi
            };
            let selected_delta = mul(&mut builder, selector, &accumulated_component.add(previous));
            let selected = previous.add(&mul(&mut builder, &parent_gate, &selected_delta));
            pin_eq(&mut builder, &io_cells[offset], &selected);
        }
        let previous_live = &prev_io[lane.live];
        let selected_live_delta = mul(
            &mut builder,
            selector,
            &LinExpr::constant(F128::ONE).add(previous_live),
        );
        let selected_live =
            previous_live.add(&mul(&mut builder, &parent_gate, &selected_live_delta));
        pin_eq(&mut builder, &io_cells[lane.live], &selected_live);
    }
    lap("matrix folds + bank lanes", &mut stage_started);

    let parent_region = with_pin_gate(&parent_gate, || {
        finalize_history_step_parent_region(
            &mut builder,
            r_columns,
            &obligations,
            &parent_selector.one_hot,
            &recorded_children,
            &recorded_r_prev,
        )
    })
    .map_err(|source| {
        HistoryStepError::sidecar(HistoryStepSidecarOperation::FinalizeParentRegion, source)
    })?;
    lap("parent region source binding", &mut stage_started);

    // Parent-seal glue. Recursive case: the replayed header must project to
    // the verified parent terminal tip (semantic lanes of the parent public
    // IO). Base case: the header witness must be the exact canonical genesis
    // header, pinned through both derived ids.
    {
        let genesis = noid_chain::consensus::genesis_header();
        let genesis_id = digest_lanes(&noid_chain::hash_block_header(&genesis));
        let genesis_semantic =
            digest_lanes(&noid_chain::block_header::semantic_header_id(&genesis));
        for lane in 0..2 {
            with_pin_gate(&parent_gate, || {
                pin_eq(
                    &mut builder,
                    &parent_seal.semantic_id[lane],
                    &prev_io[layout.block_accumulator + 1 + lane],
                );
            });
            with_pin_gate(&io_cells[layout.base], || {
                pin_eq(
                    &mut builder,
                    &parent_seal.block_id[lane],
                    &LinExpr::constant(flat_of(genesis_id[lane])),
                );
                pin_eq(
                    &mut builder,
                    &parent_seal.semantic_id[lane],
                    &LinExpr::constant(flat_of(genesis_semantic[lane])),
                );
            });
        }
    }

    let genesis_lanes = block_acc_lanes(&genesis_accumulator());
    for (index, start) in block_slots.start_acc.ordered_lanes().iter().enumerate() {
        with_pin_gate(&parent_gate, || {
            pin_eq(
                &mut builder,
                start,
                &prev_io[layout.block_accumulator + index],
            );
        });
        with_pin_gate(&io_cells[layout.base], || {
            pin_eq(
                &mut builder,
                start,
                &LinExpr::constant(genesis_lanes[index]),
            );
        });
    }
    for (index, end) in block_slots.end_acc.ordered_lanes().iter().enumerate() {
        pin_eq(
            &mut builder,
            end,
            &io_cells[layout.block_accumulator + index],
        );
    }
    if timing {
        eprintln!(
            "[history-assembly B{TIER}] remaining glue: {:.1} ms; prepare total: {:.1} ms",
            stage_started.elapsed().as_secs_f64() * 1e3,
            total_started.elapsed().as_secs_f64() * 1e3,
        );
    }

    Ok(PreparedHistoryStepAssembly {
        mode,
        builder,
        block_assembly,
        io_seal,
        current_matrix,
        io,
        spec,
        pcs_params,
        shape,
        current_class,
        parent_region,
    })
}

fn finish_history_step_assembly<const TIER: usize>(
    runtime: &HistoryStepRuntime,
    prepared: PreparedHistoryStepAssembly,
    sealed_header: &BlockHeader,
    end_accumulator: &ChainAccumulator,
) -> Result<HistoryStepAssemblyOutput, HistoryStepError> {
    let timing = std::env::var_os("NOIDH_HISTORY_ASSEMBLY_TIMING").is_some();
    let total_started = std::time::Instant::now();
    let mut stage_started = total_started;
    let PreparedHistoryStepAssembly {
        mode,
        mut builder,
        mut block_assembly,
        io_seal,
        current_matrix,
        mut io,
        spec,
        pcs_params,
        shape,
        current_class,
        parent_region,
    } = prepared;
    let layout = runtime.bank().layout();
    io_seal.seal(
        &mut builder,
        &mut io,
        layout.block_accumulator,
        end_accumulator,
    )?;
    block_assembly
        .seal_direct_tail(&mut builder, sealed_header, end_accumulator)
        .map_err(|_| HistoryStepError::StagedSeal)?;
    if timing {
        eprintln!(
            "[history-assembly B{TIER}] finish seals: {:.1} ms",
            stage_started.elapsed().as_secs_f64() * 1e3
        );
    }
    stage_started = std::time::Instant::now();

    let used = builder.num_wires();
    let limit = 1usize << shape.m;
    if used > limit {
        return Err(HistoryStepError::ShapeOverflow {
            tier: TIER,
            used,
            limit,
        });
    }
    let (r1cs, witness) = match mode {
        HistoryStepAssemblyMode::Frozen => {
            let (r1cs, witness) = builder.build();
            let (r1cs, witness) = super::super::expand_empty_field_tail(r1cs, witness, shape);
            debug_assert_eq!(r1cs.useful_rows, used);
            (Some(r1cs), witness)
        }
        HistoryStepAssemblyMode::WitnessOnly => {
            let (witness_rows, mut witness) = builder.build_witness_only();
            debug_assert_eq!(witness_rows, used);
            witness.resize(limit, F128::ZERO);
            (None, witness)
        }
    };
    if timing {
        eprintln!(
            "[history-assembly B{TIER}] builder finish + pad: {:.1} ms",
            stage_started.elapsed().as_secs_f64() * 1e3
        );
    }
    stage_started = std::time::Instant::now();
    let direct_block =
        finalize_selected_zk_block_region(block_assembly, shape.m).map_err(|source| {
            HistoryStepError::sidecar(
                HistoryStepSidecarOperation::FinalizeCurrentDirectBlock,
                source,
            )
        })?;
    if timing {
        eprintln!(
            "[history-assembly B{TIER}] current Block sidecar finalize: {:.1} ms",
            stage_started.elapsed().as_secs_f64() * 1e3
        );
    }
    stage_started = std::time::Instant::now();
    let preparations = HistoryStepPreparations {
        recursion: parent_region,
        direct_block,
    };
    Ok(match r1cs {
        Some(r1cs) => HistoryStepAssemblyOutput::Frozen(FrozenHistoryStep {
            r1cs,
            witness,
            useful_rows: used,
            class_id: current_class,
            preparations,
        }),
        None => {
            let matrix = current_matrix.expect("witness-only assembly leases its pinned matrix");
            let built = BuiltHistoryStep {
                matrix,
                witness,
                io,
                spec,
                pcs_params,
                useful_rows: used,
                class_id: current_class,
                semantic_id: noid_chain::block_header::semantic_header_id(sealed_header),
                nonce: sealed_header.nonce,
                preparations,
            };
            validate_built_against_bank(runtime, &built, &built.matrix)?;
            if timing {
                eprintln!(
                    "[history-assembly B{TIER}] bank validation: {:.1} ms; finish total: {:.1} ms",
                    stage_started.elapsed().as_secs_f64() * 1e3,
                    total_started.elapsed().as_secs_f64() * 1e3,
                );
            }
            HistoryStepAssemblyOutput::WitnessOnly(built)
        }
    })
}

pub fn assemble_history_step_base<const TIER: usize>(
    runtime: &HistoryStepRuntime,
    current: HistoryStepBlockInput<TIER>,
) -> Result<BuiltHistoryStep, HistoryStepError> {
    let sealed_header = *current.sealed_header();
    let end_accumulator = current.end_accumulator().clone();
    let prepared = prepare_history_step_base(runtime, &current)?;
    let assembly = prepare_history_step_assembly(
        runtime,
        prepared,
        current,
        HistoryStepAssemblyMode::WitnessOnly,
    )?;
    match finish_history_step_assembly::<TIER>(runtime, assembly, &sealed_header, &end_accumulator)?
    {
        HistoryStepAssemblyOutput::WitnessOnly(built) => Ok(built),
        HistoryStepAssemblyOutput::Frozen(_) => unreachable!("witness-only assembly mode"),
    }
}

pub fn assemble_history_step_recursive<const TIER: usize>(
    runtime: &HistoryStepRuntime,
    parent: HistoryStepParent<'_>,
    current: HistoryStepBlockInput<TIER>,
) -> Result<BuiltHistoryStep, HistoryStepError> {
    let sealed_header = *current.sealed_header();
    let end_accumulator = current.end_accumulator().clone();
    let prepared = prepare_history_step_recursive(runtime, parent, &current)?;
    let assembly = prepare_history_step_assembly(
        runtime,
        prepared,
        current,
        HistoryStepAssemblyMode::WitnessOnly,
    )?;
    match finish_history_step_assembly::<TIER>(runtime, assembly, &sealed_header, &end_accumulator)?
    {
        HistoryStepAssemblyOutput::WitnessOnly(built) => Ok(built),
        HistoryStepAssemblyOutput::Frozen(_) => unreachable!("witness-only assembly mode"),
    }
}

/// Release-freezer assembly. This is intentionally separate from runtime
/// block production so a node cannot accidentally rebuild canonical rows.
#[doc(hidden)]
pub fn assemble_frozen_history_step_base<const TIER: usize>(
    runtime: &HistoryStepRuntime,
    current: HistoryStepBlockInput<TIER>,
) -> Result<FrozenHistoryStep, HistoryStepError> {
    let sealed_header = *current.sealed_header();
    let end_accumulator = current.end_accumulator().clone();
    let prepared = prepare_history_step_base(runtime, &current)?;
    let assembly =
        prepare_history_step_assembly(runtime, prepared, current, HistoryStepAssemblyMode::Frozen)?;
    match finish_history_step_assembly::<TIER>(runtime, assembly, &sealed_header, &end_accumulator)?
    {
        HistoryStepAssemblyOutput::Frozen(built) => Ok(built),
        HistoryStepAssemblyOutput::WitnessOnly(_) => unreachable!("frozen assembly mode"),
    }
}

/// Recursive release-freezer twin of [`assemble_frozen_history_step_base`].
#[doc(hidden)]
pub fn assemble_frozen_history_step_recursive<const TIER: usize>(
    runtime: &HistoryStepRuntime,
    parent: HistoryStepParent<'_>,
    current: HistoryStepBlockInput<TIER>,
) -> Result<FrozenHistoryStep, HistoryStepError> {
    let sealed_header = *current.sealed_header();
    let end_accumulator = current.end_accumulator().clone();
    let prepared = prepare_history_step_recursive(runtime, parent, &current)?;
    let assembly =
        prepare_history_step_assembly(runtime, prepared, current, HistoryStepAssemblyMode::Frozen)?;
    match finish_history_step_assembly::<TIER>(runtime, assembly, &sealed_header, &end_accumulator)?
    {
        HistoryStepAssemblyOutput::Frozen(built) => Ok(built),
        HistoryStepAssemblyOutput::WitnessOnly(_) => unreachable!("frozen assembly mode"),
    }
}

/// Assemble every nonce-independent HistoryStep witness row before PoW.
/// The input must be the exact node-owned template with nonce zero and the
/// corresponding placeholder accumulator boundary.
pub fn prepare_history_step_for_pow<const TIER: usize>(
    runtime: &HistoryStepRuntime,
    parent: Option<&HistoryStepTerminal>,
    current: HistoryStepBlockInput<TIER>,
) -> Result<PreparedHistoryStepForPow<TIER>, HistoryStepError> {
    if current.sealed_header().nonce != 0 {
        return Err(HistoryStepError::StagedSeal);
    }
    let template_header = *current.sealed_header();
    let start_accumulator = current.start_accumulator().clone();
    let parent_header = *current.parent_header();
    let prepared_parent = match parent {
        Some(parent) => prepare_history_step_recursive(
            runtime,
            HistoryStepParent::new(runtime, parent)?,
            &current,
        )?,
        None => prepare_history_step_base(runtime, &current)?,
    };
    let assembly = prepare_history_step_assembly(
        runtime,
        prepared_parent,
        current,
        HistoryStepAssemblyMode::WitnessOnly,
    )?;
    Ok(PreparedHistoryStepForPow {
        assembly,
        template_header,
        start_accumulator,
        parent_header,
    })
}

impl<const TIER: usize> PreparedHistoryStepForPow<TIER> {
    /// Exact retained witness-buffer allocation used by admission accounting.
    pub fn retained_witness_bytes(&self) -> usize {
        self.assembly.builder.retained_witness_bytes()
    }

    /// Seal the only miner-controlled field and append the unchanged direct
    /// accumulator/`BLOCKHDR` suffix exactly once.
    pub fn seal_nonce(
        self,
        runtime: &HistoryStepRuntime,
        nonce: u128,
    ) -> Result<BuiltHistoryStep, HistoryStepError> {
        let Self {
            assembly,
            mut template_header,
            start_accumulator,
            parent_header,
        } = self;
        template_header.nonce = nonce;
        let end_accumulator = start_accumulator
            .advance(&parent_header, &template_header)
            .map_err(|_| HistoryStepError::StagedSeal)?;
        match finish_history_step_assembly::<TIER>(
            runtime,
            assembly,
            &template_header,
            &end_accumulator,
        )? {
            HistoryStepAssemblyOutput::WitnessOnly(built) => Ok(built),
            HistoryStepAssemblyOutput::Frozen(_) => unreachable!("prepared PoW is witness-only"),
        }
    }
}

/// Build and prove one atomic block-history unit. Height one is selected only
/// by the absence of a parent and must start at the exact genesis accumulator.
pub fn prove_history_step<const TIER: usize>(
    runtime: &HistoryStepRuntime,
    parent: Option<&HistoryStepTerminal>,
    current: HistoryStepBlockInput<TIER>,
) -> Result<HistoryStepTerminal, HistoryStepError> {
    let built = match parent {
        Some(parent) => assemble_history_step_recursive(
            runtime,
            HistoryStepParent::new(runtime, parent)?,
            current,
        )?,
        None => assemble_history_step_base(runtime, current)?,
    };
    prove_built_history_step_terminal(runtime, &built)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn selector_matrix(parent_slot: usize) -> (FieldR1cs, Vec<F128>) {
        let native = CanonicalHistoryStepClassId::new(parent_slot).unwrap();
        let mut builder = FieldR1csBuilder::new();
        let authenticated =
            LinExpr::from_wire(builder.alloc_f128(f128_from_u128(native.wire_id() as u128)));
        let selector =
            ParentClassSelectorTrace::bind(&mut builder, &authenticated, native).unwrap();
        let values = std::array::from_fn(|index| {
            LinExpr::from_wire(builder.alloc_f128(f128_from_u128((index + 17) as u128)))
        });
        let selected = selector.select(&mut builder, values);
        let expected =
            LinExpr::from_wire(builder.alloc_f128(f128_from_u128((parent_slot + 17) as u128)));
        pin_eq(&mut builder, &selected, &expected);
        builder.build()
    }

    #[test]
    fn parent_selection_changes_only_witness_not_outer_matrix() {
        let built = (0..HISTORY_STEP_TIER_SLOT_COUNT)
            .map(selector_matrix)
            .collect::<Vec<_>>();
        let digest = built[0].0.structural_statement_digest();
        for (matrix, witness) in &built {
            assert_eq!(matrix.structural_statement_digest(), digest);
            assert!(matrix.satisfies(witness));
        }
    }

    #[test]
    fn selector_rejects_a_forged_authenticated_class() {
        // The one-hot must reproduce the authenticated class wire exactly; a
        // witness claiming a different parent tier is unsatisfiable.
        let native = CanonicalHistoryStepClassId::new(1).unwrap();
        let mut builder = FieldR1csBuilder::new();
        let forged = LinExpr::from_wire(builder.alloc_f128(f128_from_u128(0)));
        let selector = ParentClassSelectorTrace::bind(&mut builder, &forged, native).unwrap();
        let _ = selector;
        let (r1cs, witness) = builder.build();
        assert!(!r1cs.satisfies(&witness));
    }

    #[test]
    fn runtime_witness_geometry_fails_closed_before_proving() {
        let class = CanonicalHistoryStepClassId::from_index(0).unwrap();
        let shape = canonical_history_step_shape(class);
        let fields = 1usize << shape.m;
        assert!(validate_runtime_witness_geometry(class, shape, shape, 91, 91, fields).is_ok());

        let wrong_shape = FieldShape {
            m: shape.m + 1,
            ..shape
        };
        assert!(matches!(
            validate_runtime_witness_geometry(class, shape, wrong_shape, 91, 91, fields),
            Err(HistoryStepError::RuntimeMatrix(actual)) if actual == class,
        ));
        assert!(matches!(
            validate_runtime_witness_geometry(class, shape, shape, 91, 91, fields - 1),
            Err(HistoryStepError::RuntimeWitnessShape {
                class: actual,
                expected,
                actual: fields_actual,
            }) if actual == class && expected == fields && fields_actual == fields - 1,
        ));
        assert!(matches!(
            validate_runtime_witness_geometry(class, shape, shape, 91, 90, fields),
            Err(HistoryStepError::RuntimeUsefulRows {
                class: actual,
                expected: 91,
                actual: 90,
            }) if actual == class,
        ));
    }

    // ----------------------------------------------------------------------
    // v2 phase-1 semantic-binding catalog: the exact parent-seal glue the
    // recursive assembly adds, exercised in isolation over real headers.
    // ----------------------------------------------------------------------

    fn seal_fixture_parent(height: u64) -> noid_chain::BlockHeader {
        noid_chain::BlockHeader {
            prev_block_hash: [0x10; 32],
            state_root: [0x22; 32],
            tx_root: [0x2A; 32],
            timestamp: height * 10,
            height,
            miner_address: noid_poseidon2b::primitives::Address([0x66; 32]),
            nonce: 0xC0FFEE ^ height as u128,
            difficulty_target: [0xFF; 32],
            log_slots: 8,
            active_slot_count: 7,
            alloc_counter: 9,
        }
    }

    /// Build the parent seal plus the exact glue pins the recursive assembly
    /// adds: derived block id against the child's `prev_block_hash` wires and
    /// derived semantic id against the verified parent-tip lanes.
    fn seal_glue_satisfies(
        parent: &noid_chain::BlockHeader,
        child_prev: [u8; 32],
        claimed_parent_tip: [u8; 32],
    ) -> bool {
        use crate::acceptance::trace::accepted_claim_batch::digest_lanes;

        let mut builder = FieldR1csBuilder::new();
        let seal = ParentSealTrace::alloc(&mut builder, parent);
        let prev_wires = digest_lanes(&child_prev).map(|lane| {
            LinExpr::from_wire(builder.alloc_f128(crate::acceptance::trace::flat_of(lane)))
        });
        let tip_wires = digest_lanes(&claimed_parent_tip).map(|lane| {
            LinExpr::from_wire(builder.alloc_f128(crate::acceptance::trace::flat_of(lane)))
        });
        for lane in 0..2 {
            pin_eq(&mut builder, &seal.block_id[lane], &prev_wires[lane]);
            pin_eq(&mut builder, &seal.semantic_id[lane], &tip_wires[lane]);
        }
        let (r1cs, witness) = builder.build();
        r1cs.satisfies(&witness)
    }

    /// The parent-seal replay must constrain `H_BLOCKHDR(parent header)` to
    /// equal the child header's `prev_block_hash`; a mismatched link or a
    /// tampered parent witness must be unsatisfiable.
    #[test]
    fn parent_seal_replay_rejects_wrong_prev_block_hash() {
        let parent = seal_fixture_parent(9);
        let link = noid_chain::hash_block_header(&parent);
        let tip = noid_chain::block_header::semantic_header_id(&parent);
        assert!(seal_glue_satisfies(&parent, link, tip));

        let mut wrong_link = link;
        wrong_link[0] ^= 1;
        assert!(!seal_glue_satisfies(&parent, wrong_link, tip));

        // A different nonce keeps the semantic projection but changes the
        // derived chain link: the replay must expose exactly that.
        let mut renonced = parent;
        renonced.nonce ^= 1;
        assert!(!seal_glue_satisfies(&renonced, link, tip));
        assert!(seal_glue_satisfies(
            &renonced,
            noid_chain::hash_block_header(&renonced),
            tip,
        ));

        // A tampered semantic field breaks the verified-tip glue.
        let mut tampered = parent;
        tampered.state_root = [0x77; 32];
        assert!(!seal_glue_satisfies(
            &tampered,
            noid_chain::hash_block_header(&tampered),
            tip,
        ));
    }

    /// At a 144-boundary parent height the accumulator epoch lanes must be
    /// written from the block id derived inside the parent-seal replay, and
    /// passed through unchanged at every other height (143 -> 144 edge).
    #[test]
    fn epoch_lane_updates_from_derived_parent_id_at_boundary() {
        use crate::acceptance::trace::accepted_claim_batch::{
            build_direct_accumulator_transition_slot, digest_lanes, AccumulatorWires,
            DirectChildWires,
        };

        for parent_height in [143u64, 144] {
            let parent = seal_fixture_parent(parent_height);
            let parent_id = noid_chain::hash_block_header(&parent);
            let start = ChainAccumulator {
                height: parent.height,
                tip_semantic_id: noid_chain::block_header::semantic_header_id(&parent),
                state_root: parent.state_root,
                log_slots: parent.log_slots,
                active_slot_count: parent.active_slot_count,
                alloc_counter: parent.alloc_counter,
                epoch_anchor_id: [0x33; 32],
            };
            let child = noid_chain::BlockHeader {
                prev_block_hash: parent_id,
                state_root: [0x44; 32],
                tx_root: [0x55; 32],
                timestamp: parent.timestamp + 10,
                height: parent.height + 1,
                miner_address: noid_poseidon2b::primitives::Address([0x66; 32]),
                nonce: 7,
                difficulty_target: [0xFF; 32],
                log_slots: parent.log_slots,
                active_slot_count: 8,
                alloc_counter: 10,
            };
            let end = start.advance(&parent, &child).unwrap();
            if parent_height % 144 == 0 {
                assert_eq!(end.epoch_anchor_id, parent_id);
            } else {
                assert_eq!(end.epoch_anchor_id, start.epoch_anchor_id);
            }

            // The transition consumes the REPLAY-derived parent id, exactly
            // as the recursive assembly wires it.
            let satisfies = |end: &ChainAccumulator| {
                let mut builder = FieldR1csBuilder::new();
                let seal = ParentSealTrace::alloc(&mut builder, &parent);
                let start_wires = AccumulatorWires::alloc(&mut builder, &start);
                let end_wires = AccumulatorWires::alloc(&mut builder, end);
                let child_wires = DirectChildWires {
                    semantic_id: digest_lanes(&noid_chain::block_header::semantic_header_id(
                        &child,
                    ))
                    .map(|lane| {
                        LinExpr::from_wire(
                            builder.alloc_f128(crate::acceptance::trace::flat_of(lane)),
                        )
                    }),
                    prev_block_hash: digest_lanes(&child.prev_block_hash).map(|lane| {
                        LinExpr::from_wire(
                            builder.alloc_f128(crate::acceptance::trace::flat_of(lane)),
                        )
                    }),
                    state_root: digest_lanes(&child.state_root).map(|lane| {
                        LinExpr::from_wire(
                            builder.alloc_f128(crate::acceptance::trace::flat_of(lane)),
                        )
                    }),
                    height: LinExpr::from_wire(builder.alloc_f128(
                        crate::acceptance::trace::flat_of(noid_core::Block128::from(
                            child.height as u128,
                        )),
                    )),
                    log_slots: LinExpr::from_wire(builder.alloc_f128(
                        crate::acceptance::trace::flat_of(noid_core::Block128::from(
                            child.log_slots as u128,
                        )),
                    )),
                    active_slot_count: LinExpr::from_wire(builder.alloc_f128(
                        crate::acceptance::trace::flat_of(noid_core::Block128::from(
                            child.active_slot_count as u128,
                        )),
                    )),
                    alloc_counter: LinExpr::from_wire(builder.alloc_f128(
                        crate::acceptance::trace::flat_of(noid_core::Block128::from(
                            child.alloc_counter as u128,
                        )),
                    )),
                };
                build_direct_accumulator_transition_slot(
                    &mut builder,
                    &start_wires,
                    &child_wires,
                    &end_wires,
                    &seal.block_id,
                );
                let (r1cs, witness) = builder.build();
                r1cs.satisfies(&witness)
            };
            assert!(satisfies(&end), "parent height {parent_height}");
            let mut wrong_epoch = end.clone();
            wrong_epoch.epoch_anchor_id[0] ^= 1;
            assert!(!satisfies(&wrong_epoch), "parent height {parent_height}");
        }
    }

    /// The height-1 base selector must accept only the pinned canonical
    /// genesis header; any other parent is unsatisfiable under the gated
    /// genesis-constant pins the base assembly adds.
    #[test]
    fn base_case_selector_rejects_non_genesis_parent() {
        use crate::acceptance::trace::accepted_claim_batch::digest_lanes;

        let base_pins_satisfy = |parent: &noid_chain::BlockHeader| {
            let genesis = noid_chain::consensus::genesis_header();
            let genesis_id = digest_lanes(&noid_chain::hash_block_header(&genesis));
            let genesis_semantic =
                digest_lanes(&noid_chain::block_header::semantic_header_id(&genesis));
            let mut builder = FieldR1csBuilder::new();
            let seal = ParentSealTrace::alloc(&mut builder, parent);
            for lane in 0..2 {
                pin_eq(
                    &mut builder,
                    &seal.block_id[lane],
                    &LinExpr::constant(crate::acceptance::trace::flat_of(genesis_id[lane])),
                );
                pin_eq(
                    &mut builder,
                    &seal.semantic_id[lane],
                    &LinExpr::constant(crate::acceptance::trace::flat_of(genesis_semantic[lane])),
                );
            }
            let (r1cs, witness) = builder.build();
            r1cs.satisfies(&witness)
        };

        assert!(base_pins_satisfy(&noid_chain::consensus::genesis_header()));
        assert!(!base_pins_satisfy(&seal_fixture_parent(0)));
        let mut renonced_genesis = noid_chain::consensus::genesis_header();
        renonced_genesis.nonce ^= 1;
        assert!(!base_pins_satisfy(&renonced_genesis));
    }
}

fn validate_legacy_block_profile<const TIER: usize>(
    current: &HistoryStepBlockInput<TIER>,
) -> Result<(), HistoryStepError> {
    if !current.components.v2_contract_inputs.is_empty() {
        return Err(HistoryStepError::ProtocolProfile);
    }
    Ok(())
}
