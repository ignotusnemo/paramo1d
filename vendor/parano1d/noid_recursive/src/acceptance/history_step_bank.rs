// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical class bank for the atomic `HistoryStep` relation.
//!
//! A `HistoryStep` class is selected by the current block
//! physical-page tier. The launch bank has exactly B25 and B255. Every class
//! exposes the same public-IO layout:
//!
//! * the exact ordered matrix and post-commit class whitelists;
//! * an aggregate digest of those pins;
//! * one monotone accumulator lane per bank matrix, at that matrix's width;
//! * the accepted block accumulator.
//!
//! A transition folds only the matrix claim emitted by the selected parent
//! proof and copies every other lane byte-for-byte.  The terminal decider is
//! a consuming typestate: it cannot return an accepted tip until the fresh
//! claim from the tip verifier and every live accumulated lane have been
//! evaluated against locally authenticated matrix rows.

use noid_chain::consensus::params::BLOCK_PAGE_CLASS_TIERS;
use noid_core::Block128;
use noid_ivc_core::challenger::{Challenger, FsLaneChallenger};
use noid_ivc_core::field::{F128, F256};
use noid_ivc_core::field_circuit::{f128_from_u128, f128_to_u128, FieldR1csBuilder, FsChannelOps};
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

use noid_ivc_core::field_r1cs::{CompactFieldR1cs, FieldR1cs};
use noid_ivc_core::matrix_claim::c1::{
    fresh_claim_value_c1, prove_matrix_claim_fold_c1, prove_matrix_claim_fold_compact_c1,
    stacked_matrix_mle_eval_c1, C1FreshLincheckClaim, C1MatrixAccClaim, C1MatrixClaimEvaluator,
    C1MatrixFoldProof,
};
use noid_ivc_core::pcs::{PcsParams, BASEFOLD_RATE_QUARTER_C1_QUERIES, LOG_PACKING};
use noid_ivc_core::proof::{pcs_params_statement_bytes, FieldShape};
use noid_ivc_core::public_io::{PublicIoSpec, WitnessSlice};
use noid_poseidon2b::native::poseidon2b_hash_byte_slices;

use super::trace::flat_of;
use super::trace::self_verify::flat_digest_lanes;
use crate::accumulator::{ChainAccumulator, CHAIN_ACCUMULATOR_LANES};

pub mod retirement;

pub const ACC_LANES: usize = CHAIN_ACCUMULATOR_LANES;
const HISTORY_STEP_PCS_LOG_INV_RATE: usize = 2;
const HISTORY_STEP_PCS_LOG_BATCH_SIZE: usize = 5;
pub const HISTORY_STEP_FRI_QUERIES: usize = BASEFOLD_RATE_QUARTER_C1_QUERIES;

pub(crate) fn block_acc_lanes(accumulator: &ChainAccumulator) -> [F128; ACC_LANES] {
    accumulator.to_lanes().map(flat_of)
}

pub const HISTORY_STEP_TIER_SLOT_COUNT: usize = BLOCK_PAGE_CLASS_TIERS.len();
/// One class per current tier. Every class shares one frozen outer shape,
/// so the predecessor replay is uniform by construction and the parent tier
/// never enters the outer matrix — it is an authenticated witness selection.
pub const HISTORY_STEP_CLASS_COUNT: usize = HISTORY_STEP_TIER_SLOT_COUNT;

/// One authenticated canonical class matrix leased from a runtime source.
///
/// Release tooling may retain a resident relation while it is constructing
/// the bank. Production sources keep the executable-embedded packed relation
/// compact. Both variants expose the exact same statement and matrix-fold
/// transcript; the enum prevents an external evaluator from substituting
/// rows behind a claimed digest.
pub enum HistoryStepMatrixLease {
    Resident(Arc<FieldR1cs>),
    Compact(Arc<CompactFieldR1cs>),
}

impl HistoryStepMatrixLease {
    pub fn resident(matrix: FieldR1cs) -> Self {
        Self::Resident(Arc::new(matrix))
    }

    pub fn compact(matrix: CompactFieldR1cs) -> Self {
        Self::Compact(Arc::new(matrix))
    }

    pub fn field_shape(&self) -> FieldShape {
        match self {
            Self::Resident(matrix) => FieldShape::of(matrix.as_ref()),
            Self::Compact(matrix) => matrix.shape(),
        }
    }

    pub fn useful_rows(&self) -> usize {
        match self {
            Self::Resident(matrix) => matrix.useful_rows,
            Self::Compact(matrix) => matrix.useful_rows(),
        }
    }

    /// Return the structurally authenticated statement identity. The resident
    /// path hashes its actual rows; compact values were minted only by a full
    /// canonical scan or the executable's paired release-build seal.
    pub fn statement_digest(&self) -> [u8; 32] {
        match self {
            Self::Resident(matrix) => matrix.structural_statement_digest(),
            Self::Compact(matrix) => matrix.statement_digest(),
        }
    }
}

/// Frozen outer dimensions selected solely by the current physical-page
/// class. Both matrices contain the same two-arm B25/B255 parent selector, so
/// parent shape changes witness data rather than the current matrix identity.
pub const HISTORY_STEP_CURRENT_CLASS_MS: [usize; HISTORY_STEP_TIER_SLOT_COUNT] = [22, 24];

const _: () = assert!(
    HISTORY_STEP_CURRENT_CLASS_MS[0]
        == noid_chain::consensus::paged_spend::BlockProofClass::B25.outer_m()
        && HISTORY_STEP_CURRENT_CLASS_MS[1]
            == noid_chain::consensus::paged_spend::BlockProofClass::B255.outer_m(),
    "HistoryStep and consensus proof-class dimensions must match"
);

const HISTORY_STEP_BANK_POST_COMMIT_DOMAIN: &[u8] = b"NOID/HISTORY-STEP/BANK-POST-COMMIT/V1";
const HISTORY_STEP_BANK_DIGEST_DOMAIN: &[u8] = b"NOID/HISTORY-STEP/CLASS-BANK/V1";
pub(crate) const HISTORY_STEP_BANK_FOLD_TRANSCRIPT_DOMAIN: &[u8] = b"history-step-bank-fold-v1";
const HISTORY_STEP_BANK_FOLD_ROUTE_DOMAIN: &[u8] = b"NOID/HISTORY-STEP/BANK-FOLD-ROUTE/V1";

/// Canonical class id: exactly the current block tier slot.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct CanonicalHistoryStepClassId(u8);

impl CanonicalHistoryStepClassId {
    pub const fn new(current_slot: usize) -> Option<Self> {
        if current_slot < HISTORY_STEP_TIER_SLOT_COUNT {
            Some(Self(current_slot as u8))
        } else {
            None
        }
    }

    pub const fn from_index(index: usize) -> Option<Self> {
        if index < HISTORY_STEP_CLASS_COUNT {
            Some(Self(index as u8))
        } else {
            None
        }
    }

    pub const fn index(self) -> usize {
        self.0 as usize
    }

    pub const fn current_slot(self) -> usize {
        self.index()
    }

    pub fn current_tier(self) -> usize {
        BLOCK_PAGE_CLASS_TIERS[self.current_slot()]
    }

    pub const fn wire_id(self) -> u8 {
        self.0
    }

    pub const fn is_canonical(self) -> bool {
        self.index() < HISTORY_STEP_CLASS_COUNT
    }
}

/// Resolve a class by the consensus tier value rather than registry position.
pub fn canonical_history_step_class_id(current_tier: usize) -> Option<CanonicalHistoryStepClassId> {
    let current_slot = BLOCK_PAGE_CLASS_TIERS
        .iter()
        .position(|tier| *tier == current_tier)?;
    CanonicalHistoryStepClassId::new(current_slot)
}

pub fn canonical_history_step_shape(class_id: CanonicalHistoryStepClassId) -> FieldShape {
    let m = HISTORY_STEP_CURRENT_CLASS_MS[class_id.current_slot()];
    FieldShape {
        m,
        k_log: m,
        k_skip: noid_ivc_core::zerocheck::K_SKIP,
        const_pin: Some(0),
    }
}

pub fn canonical_history_step_pcs_params(class_id: CanonicalHistoryStepClassId) -> PcsParams {
    let shape = canonical_history_step_shape(class_id);
    PcsParams {
        m: shape.m + LOG_PACKING,
        log_inv_rate: HISTORY_STEP_PCS_LOG_INV_RATE,
        log_batch_size: HISTORY_STEP_PCS_LOG_BATCH_SIZE,
        profile: Default::default(),
    }
}

/// One variable-width matrix accumulator lane.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HistoryStepBankLaneLayout {
    pub point: usize,
    pub value: usize,
    pub live: usize,
}

impl HistoryStepBankLaneLayout {
    fn new(offset: usize, k_log: usize) -> (Self, usize) {
        let point_len = 2 * k_log + 1;
        let point_lanes = 2 * point_len;
        (
            Self {
                point: offset,
                value: offset + point_lanes,
                live: offset + point_lanes + 2,
            },
            offset + point_lanes + 3,
        )
    }

    pub const fn point_len(self) -> usize {
        (self.value - self.point) / 2
    }
}

/// Shared public-IO layout of both launch classes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HistoryStepBankIoLayout {
    /// One only when the current block starts at the canonical genesis
    /// boundary. Every recursive step carries zero.
    pub base: usize,
    /// Current physical-page class id of this authenticated tip.
    pub tip_class: usize,
    /// First of `2 * HISTORY_STEP_CLASS_COUNT` flat-F128 matrix-digest lanes.
    pub matrix_whitelist: usize,
    /// First of `2 * 16` flat-F128 post-commit-digest lanes.
    pub post_commit_whitelist: usize,
    /// Two flat-F128 lanes for the ordered aggregate bank digest.
    pub bank_digest: usize,
    pub matrix_lanes: [HistoryStepBankLaneLayout; HISTORY_STEP_CLASS_COUNT],
    pub block_accumulator: usize,
    pub len: usize,
}

pub fn history_step_bank_io_layout() -> HistoryStepBankIoLayout {
    let base = 0;
    let tip_class = 1;
    let matrix_whitelist = 2;
    let post_commit_whitelist = matrix_whitelist + 2 * HISTORY_STEP_CLASS_COUNT;
    let bank_digest = post_commit_whitelist + 2 * HISTORY_STEP_CLASS_COUNT;
    let mut offset = bank_digest + 2;
    let matrix_lanes = std::array::from_fn(|index| {
        let class_id = CanonicalHistoryStepClassId::from_index(index).expect("canonical class");
        let (lane, next) =
            HistoryStepBankLaneLayout::new(offset, canonical_history_step_shape(class_id).k_log);
        offset = next;
        lane
    });
    HistoryStepBankIoLayout {
        base,
        tip_class,
        matrix_whitelist,
        post_commit_whitelist,
        bank_digest,
        matrix_lanes,
        block_accumulator: offset,
        len: offset + ACC_LANES,
    }
}

pub fn history_step_bank_io_spec() -> PublicIoSpec {
    let layout = history_step_bank_io_layout();
    PublicIoSpec {
        io_slice: WitnessSlice {
            log2_len: layout.len.next_power_of_two().trailing_zeros() as usize,
            index: 1,
        },
        io_len: layout.len,
        claims: Vec::new(),
    }
}

/// External release pins needed to authenticate one bank entry.
#[derive(Clone, Debug)]
pub struct HistoryStepBankEntryPins {
    pub class_id: CanonicalHistoryStepClassId,
    pub shape: FieldShape,
    pub pcs_params: PcsParams,
    pub matrix_digest: [u8; 32],
    pub parent_recursion_vk_digest: [u8; 32],
    pub direct_block_vk_digest: [u8; 32],
    pub post_commit_digest: [u8; 32],
}

#[derive(Clone, Debug)]
pub struct PinnedHistoryStepBankEntry {
    class_id: CanonicalHistoryStepClassId,
    shape: FieldShape,
    pcs_params: PcsParams,
    matrix_digest: [u8; 32],
    parent_recursion_vk_digest: [u8; 32],
    direct_block_vk_digest: [u8; 32],
    post_commit_digest: [u8; 32],
}

impl PinnedHistoryStepBankEntry {
    pub const fn class_id(&self) -> CanonicalHistoryStepClassId {
        self.class_id
    }

    pub const fn shape(&self) -> FieldShape {
        self.shape
    }

    pub fn pcs_params(&self) -> &PcsParams {
        &self.pcs_params
    }

    pub const fn matrix_digest(&self) -> [u8; 32] {
        self.matrix_digest
    }

    pub const fn parent_recursion_vk_digest(&self) -> [u8; 32] {
        self.parent_recursion_vk_digest
    }

    pub const fn direct_block_vk_digest(&self) -> [u8; 32] {
        self.direct_block_vk_digest
    }

    pub const fn post_commit_digest(&self) -> [u8; 32] {
        self.post_commit_digest
    }
}

#[derive(Clone, Debug)]
pub struct PinnedHistoryStepClassBank {
    entries: [PinnedHistoryStepBankEntry; HISTORY_STEP_CLASS_COUNT],
    layout: HistoryStepBankIoLayout,
    spec: PublicIoSpec,
    digest: [u8; 32],
}

impl PinnedHistoryStepClassBank {
    /// Validate exact slot order, class shapes, PCS profiles and composite
    /// identities before this collection can act as a bank authority.
    pub fn validate(
        pins: [HistoryStepBankEntryPins; HISTORY_STEP_CLASS_COUNT],
    ) -> Result<Self, HistoryStepBankError> {
        let layout = history_step_bank_io_layout();
        let spec = history_step_bank_io_spec();
        for (index, pin) in pins.iter().enumerate() {
            let expected_id = CanonicalHistoryStepClassId::from_index(index)
                .expect("fixed-size bank has only canonical indices");
            if pin.class_id != expected_id {
                return Err(HistoryStepBankError::EntryOrder {
                    index,
                    actual: pin.class_id,
                });
            }
            if pin.shape != canonical_history_step_shape(pin.class_id) {
                return Err(HistoryStepBankError::EntryShape(pin.class_id));
            }
            let expected_pcs = canonical_history_step_pcs_params(pin.class_id);
            if pcs_params_statement_bytes(&pin.pcs_params)
                != pcs_params_statement_bytes(&expected_pcs)
            {
                return Err(HistoryStepBankError::EntryPcs(pin.class_id));
            }
            if pin.parent_recursion_vk_digest != pins[0].parent_recursion_vk_digest {
                return Err(HistoryStepBankError::ParentRecursionVk(pin.class_id));
            }
            let expected_post_commit = history_step_bank_post_commit_digest(
                pin.class_id,
                &pin.matrix_digest,
                &spec,
                &pin.pcs_params,
                pin.parent_recursion_vk_digest,
                pin.direct_block_vk_digest,
            );
            if pin.post_commit_digest != expected_post_commit {
                return Err(HistoryStepBankError::EntryPostCommit(pin.class_id));
            }
        }
        let entries = pins.map(|pin| PinnedHistoryStepBankEntry {
            class_id: pin.class_id,
            shape: pin.shape,
            pcs_params: pin.pcs_params,
            matrix_digest: pin.matrix_digest,
            parent_recursion_vk_digest: pin.parent_recursion_vk_digest,
            direct_block_vk_digest: pin.direct_block_vk_digest,
            post_commit_digest: pin.post_commit_digest,
        });
        let digest = history_step_class_bank_digest(&entries, &spec);
        Ok(Self {
            entries,
            layout,
            spec,
            digest,
        })
    }

    pub fn entry(&self, class_id: CanonicalHistoryStepClassId) -> &PinnedHistoryStepBankEntry {
        &self.entries[class_id.index()]
    }

    pub fn entries(&self) -> &[PinnedHistoryStepBankEntry; HISTORY_STEP_CLASS_COUNT] {
        &self.entries
    }

    pub fn layout(&self) -> &HistoryStepBankIoLayout {
        &self.layout
    }

    pub fn spec(&self) -> &PublicIoSpec {
        &self.spec
    }

    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// Authenticate a resident matrix from its rows, never from a seedable
    /// digest cache.
    pub fn authenticate_resident_matrix(
        &self,
        class_id: CanonicalHistoryStepClassId,
        matrix: &FieldR1cs,
    ) -> Result<(), HistoryStepBankError> {
        let entry = self.entry(class_id);
        if FieldShape::of(matrix) != entry.shape {
            return Err(HistoryStepBankError::MatrixShape(class_id));
        }
        if matrix.structural_statement_digest() != entry.matrix_digest {
            return Err(HistoryStepBankError::MatrixDigest(class_id));
        }
        Ok(())
    }

    /// Authenticate either supported runtime representation against the
    /// exact class pin before it is used for a fold or terminal decision.
    pub fn authenticate_matrix_lease(
        &self,
        class_id: CanonicalHistoryStepClassId,
        matrix: &HistoryStepMatrixLease,
    ) -> Result<(), HistoryStepBankError> {
        let entry = self.entry(class_id);
        if matrix.field_shape() != entry.shape {
            return Err(HistoryStepBankError::MatrixShape(class_id));
        }
        if matrix.statement_digest() != entry.matrix_digest {
            return Err(HistoryStepBankError::MatrixDigest(class_id));
        }
        Ok(())
    }

    /// Create the verifier-owned handoff after a tip proof has emitted its
    /// deferred fresh lincheck claim.  This remains crate-private until the
    /// feature-gated verifier is wired to be the sole caller.
    pub(crate) fn bind_verified_tip_replay(
        &self,
        class_id: CanonicalHistoryStepClassId,
        observed_matrix_digest: [u8; 32],
        observed_post_commit_digest: [u8; 32],
        fresh: C1FreshLincheckClaim,
    ) -> Result<VerifiedHistoryStepTipReplay, HistoryStepBankError> {
        let entry = self.entry(class_id);
        if observed_matrix_digest != entry.matrix_digest {
            return Err(HistoryStepBankError::MatrixDigest(class_id));
        }
        if observed_post_commit_digest != entry.post_commit_digest {
            return Err(HistoryStepBankError::TipPostCommit(class_id));
        }
        validate_fresh_shape(&fresh, entry.shape, class_id)?;
        Ok(VerifiedHistoryStepTipReplay {
            class_id,
            bank_digest: self.digest,
            fresh,
        })
    }
}

/// Composite class identity for one exact bank entry.  The role order is
/// transcript-visible: predecessor recursion first, direct current block
/// second.  This changes only class composition/pins, not any primitive.
pub fn history_step_bank_post_commit_digest(
    class_id: CanonicalHistoryStepClassId,
    matrix_digest: &[u8; 32],
    spec: &PublicIoSpec,
    pcs_params: &PcsParams,
    parent_recursion_vk_digest: [u8; 32],
    direct_block_vk_digest: [u8; 32],
) -> [u8; 32] {
    let mut spec_bytes = Vec::new();
    for lane in spec.transcript_lanes() {
        spec_bytes.extend_from_slice(&lane.lo.to_le_bytes());
        spec_bytes.extend_from_slice(&lane.hi.to_le_bytes());
    }
    let pcs_bytes = pcs_params_statement_bytes(pcs_params);
    let class = [class_id.current_slot() as u8];
    poseidon2b_hash_byte_slices(
        HISTORY_STEP_BANK_POST_COMMIT_DOMAIN,
        &[
            b"class",
            &class,
            b"matrix",
            matrix_digest,
            b"public-io",
            &spec_bytes,
            b"pcs",
            &pcs_bytes,
            b"parent-recursion",
            &parent_recursion_vk_digest,
            b"direct-block",
            &direct_block_vk_digest,
        ],
    )
}

fn history_step_class_bank_digest(
    entries: &[PinnedHistoryStepBankEntry; HISTORY_STEP_CLASS_COUNT],
    spec: &PublicIoSpec,
) -> [u8; 32] {
    fn push_u64(bytes: &mut Vec<u8>, value: usize) {
        bytes.extend_from_slice(&(value as u64).to_le_bytes());
    }

    let mut bytes = Vec::new();
    for lane in spec.transcript_lanes() {
        bytes.extend_from_slice(&lane.lo.to_le_bytes());
        bytes.extend_from_slice(&lane.hi.to_le_bytes());
    }
    for entry in entries {
        bytes.push(entry.class_id.wire_id());
        push_u64(&mut bytes, entry.shape.m);
        push_u64(&mut bytes, entry.shape.k_log);
        push_u64(&mut bytes, entry.shape.k_skip);
        push_u64(
            &mut bytes,
            entry.shape.const_pin.map_or(0, |column| column + 1),
        );
        bytes.extend_from_slice(&pcs_params_statement_bytes(&entry.pcs_params));
        bytes.extend_from_slice(&entry.matrix_digest);
        bytes.extend_from_slice(&entry.post_commit_digest);
        bytes.extend_from_slice(&entry.parent_recursion_vk_digest);
        bytes.extend_from_slice(&entry.direct_block_vk_digest);
    }
    poseidon2b_hash_byte_slices(HISTORY_STEP_BANK_DIGEST_DOMAIN, &[&bytes])
}

fn write_digest(io: &mut [F128], offset: usize, digest: &[u8; 32]) {
    io[offset..offset + 2].copy_from_slice(&flat_digest_lanes(digest));
}

fn digest_matches(io: &[F128], offset: usize, digest: &[u8; 32]) -> bool {
    io[offset..offset + 2] == flat_digest_lanes(digest)
}

fn write_bank_pins(bank: &PinnedHistoryStepClassBank, io: &mut [F128]) {
    for entry in bank.entries() {
        let index = entry.class_id.index();
        write_digest(
            io,
            bank.layout.matrix_whitelist + 2 * index,
            &entry.matrix_digest,
        );
        write_digest(
            io,
            bank.layout.post_commit_whitelist + 2 * index,
            &entry.post_commit_digest,
        );
    }
    write_digest(io, bank.layout.bank_digest, &bank.digest);
}

/// Canonical base terminal before any predecessor matrix has been folded.
/// The caller supplies the block accumulator reached from the exact genesis
/// parent boundary; all matrix lanes start dead. The current block selects
/// either the B25 or B255 launch class.
pub fn history_step_bank_base_output_io(
    bank: &PinnedHistoryStepClassBank,
    class_id: CanonicalHistoryStepClassId,
    block_accumulator: &ChainAccumulator,
) -> Result<Vec<F128>, HistoryStepBankError> {
    let mut io = vec![F128::ZERO; bank.layout.len];
    io[bank.layout.base] = F128::ONE;
    io[bank.layout.tip_class] = f128_from_u128(class_id.wire_id() as u128);
    write_bank_pins(bank, &mut io);
    io[bank.layout.block_accumulator..bank.layout.block_accumulator + ACC_LANES]
        .copy_from_slice(&block_acc_lanes(block_accumulator));
    Ok(io)
}

#[derive(Clone, Debug)]
struct ParsedHistoryStepBankIo {
    base: bool,
    tip_class: CanonicalHistoryStepClassId,
    lanes: [Option<C1MatrixAccClaim>; HISTORY_STEP_CLASS_COUNT],
    block_accumulator: [F128; ACC_LANES],
}

fn parse_history_step_bank_io(
    bank: &PinnedHistoryStepClassBank,
    io: &[F128],
) -> Result<ParsedHistoryStepBankIo, HistoryStepBankError> {
    let layout = bank.layout();
    if io.len() != layout.len {
        return Err(HistoryStepBankError::IoLength {
            expected: layout.len,
            actual: io.len(),
        });
    }
    let base = match io[layout.base] {
        F128::ZERO => false,
        F128::ONE => true,
        _ => return Err(HistoryStepBankError::BaseFlag),
    };
    let tip_class = usize::try_from(f128_to_u128(io[layout.tip_class]))
        .ok()
        .and_then(CanonicalHistoryStepClassId::from_index)
        .ok_or(HistoryStepBankError::TipClass)?;
    for entry in bank.entries() {
        let index = entry.class_id.index();
        if !digest_matches(
            io,
            layout.matrix_whitelist + 2 * index,
            &entry.matrix_digest,
        ) {
            return Err(HistoryStepBankError::MatrixWhitelist(entry.class_id));
        }
        if !digest_matches(
            io,
            layout.post_commit_whitelist + 2 * index,
            &entry.post_commit_digest,
        ) {
            return Err(HistoryStepBankError::PostCommitWhitelist(entry.class_id));
        }
    }
    if !digest_matches(io, layout.bank_digest, &bank.digest) {
        return Err(HistoryStepBankError::BankDigest);
    }

    let mut parsed_lanes: [Option<C1MatrixAccClaim>; HISTORY_STEP_CLASS_COUNT] =
        std::array::from_fn(|_| None);
    for (index, lane) in layout.matrix_lanes.iter().enumerate() {
        let class_id = CanonicalHistoryStepClassId::from_index(index).expect("canonical class");
        match io[lane.live] {
            F128::ZERO => {
                if io[lane.point..lane.live]
                    .iter()
                    .any(|value| *value != F128::ZERO)
                {
                    return Err(HistoryStepBankError::NonCanonicalDeadLane(class_id));
                }
            }
            F128::ONE => {
                parsed_lanes[index] = Some(C1MatrixAccClaim {
                    point: io[lane.point..lane.value]
                        .chunks_exact(2)
                        .map(|coordinates| F256::new(coordinates[0], coordinates[1]))
                        .collect(),
                    value: F256::new(io[lane.value], io[lane.value + 1]),
                });
            }
            _ => return Err(HistoryStepBankError::LaneLiveness(class_id)),
        }
    }
    let mut block_accumulator = [F128::ZERO; ACC_LANES];
    block_accumulator
        .copy_from_slice(&io[layout.block_accumulator..layout.block_accumulator + ACC_LANES]);
    Ok(ParsedHistoryStepBankIo {
        base,
        tip_class,
        lanes: parsed_lanes,
        block_accumulator,
    })
}

/// Decode one exact accumulated lane after validating every bank pin.
pub fn history_step_bank_lane_claim(
    bank: &PinnedHistoryStepClassBank,
    io: &[F128],
    class_id: CanonicalHistoryStepClassId,
) -> Result<Option<C1MatrixAccClaim>, HistoryStepBankError> {
    Ok(parse_history_step_bank_io(bank, io)?.lanes[class_id.index()].clone())
}

/// Return the authenticated full parent class id used by the next fold route.
pub fn history_step_bank_tip_class(
    bank: &PinnedHistoryStepClassBank,
    io: &[F128],
) -> Result<CanonicalHistoryStepClassId, HistoryStepBankError> {
    Ok(parse_history_step_bank_io(bank, io)?.tip_class)
}

/// Decode the exact terminal chain boundary after all bank pins and lane
/// canonicality checks have passed.
pub fn history_step_bank_block_accumulator(
    bank: &PinnedHistoryStepClassBank,
    io: &[F128],
) -> Result<ChainAccumulator, HistoryStepBankError> {
    let parsed = parse_history_step_bank_io(bank, io)?;
    let lanes = parsed.block_accumulator.map(|lane| {
        let flat = (lane.lo as u128) | ((lane.hi as u128) << 64);
        Block128::from(noid_core::hardware::flat_to_tower_u128(flat))
    });
    ChainAccumulator::from_lanes(lanes).map_err(|_| HistoryStepBankError::BlockAccumulator)
}

fn install_folded_lane(
    bank: &PinnedHistoryStepClassBank,
    io: &mut [F128],
    class_id: CanonicalHistoryStepClassId,
    claim: &C1MatrixAccClaim,
) -> Result<(), HistoryStepBankError> {
    let lane = bank.layout.matrix_lanes[class_id.index()];
    if claim.point.len() != lane.point_len() {
        return Err(HistoryStepBankError::LaneWidth(class_id));
    }
    for (lanes, coordinate) in io[lane.point..lane.value]
        .chunks_exact_mut(2)
        .zip(&claim.point)
    {
        lanes[0] = coordinate.lo;
        lanes[1] = coordinate.hi;
    }
    io[lane.value] = claim.value.lo;
    io[lane.value + 1] = claim.value.hi;
    io[lane.live] = F128::ONE;
    Ok(())
}

/// Result of routing one parent class and folding its fresh matrix claim.
pub struct RoutedHistoryStepBankFold {
    fold_proof: C1MatrixFoldProof,
    outgoing_claim: C1MatrixAccClaim,
    io: Vec<F128>,
}

fn install_current_block_accumulator(
    bank: &PinnedHistoryStepClassBank,
    io: &mut [F128],
    current: &ChainAccumulator,
) {
    io[bank.layout.block_accumulator..bank.layout.block_accumulator + ACC_LANES]
        .copy_from_slice(&block_acc_lanes(current));
}

/// Prefix the native and trace fold transcripts identically.  Keeping this in
/// one helper prevents the selected bank lane from becoming an out-of-band
/// choice in either implementation.
pub(crate) fn observe_history_step_bank_fold_route<Ch: Challenger>(
    challenger: &mut Ch,
    selected_parent_class: CanonicalHistoryStepClassId,
) {
    challenger.observe_label(HISTORY_STEP_BANK_FOLD_ROUTE_DOMAIN);
    challenger.observe_bytes(&[selected_parent_class.wire_id()]);
}

/// Circuit twin of [`observe_history_step_bank_fold_route`].
pub(crate) fn observe_history_step_bank_fold_route_trace(
    builder: &mut FieldR1csBuilder,
    challenger: &mut impl FsChannelOps,
    selected_parent_class: &noid_ivc_core::field_circuit::LinExpr,
) {
    challenger.observe_label(builder, HISTORY_STEP_BANK_FOLD_ROUTE_DOMAIN);
    challenger.observe_lanes(builder, 1, core::slice::from_ref(selected_parent_class));
}

impl RoutedHistoryStepBankFold {
    pub fn fold_proof(&self) -> &C1MatrixFoldProof {
        &self.fold_proof
    }

    pub fn outgoing_claim(&self) -> &C1MatrixAccClaim {
        &self.outgoing_claim
    }

    pub fn io(&self) -> &[F128] {
        &self.io
    }

    pub fn into_parts(self) -> (C1MatrixFoldProof, C1MatrixAccClaim, Vec<F128>) {
        (self.fold_proof, self.outgoing_claim, self.io)
    }
}

/// Copy the complete parent bank IO, fold only the selected parent-class
/// lane, and replace only the accepted-block accumulator.  Non-selected lane
/// ranges are never rebuilt or zeroed.
pub fn route_carry_and_fold_history_step_lane<Ch: Challenger>(
    bank: &PinnedHistoryStepClassBank,
    parent_io: &[F128],
    selected_parent_class: CanonicalHistoryStepClassId,
    current_class: CanonicalHistoryStepClassId,
    selected_parent_matrix: &HistoryStepMatrixLease,
    fresh_parent_claim: &C1FreshLincheckClaim,
    current_block_accumulator: &ChainAccumulator,
    challenger: &mut Ch,
) -> Result<RoutedHistoryStepBankFold, HistoryStepBankError> {
    let parsed = parse_history_step_bank_io(bank, parent_io)?;
    if parsed.tip_class != selected_parent_class {
        return Err(HistoryStepBankError::SelectedParentClass {
            authenticated: parsed.tip_class,
            selected: selected_parent_class,
        });
    }
    bank.authenticate_matrix_lease(selected_parent_class, selected_parent_matrix)?;
    let entry = bank.entry(selected_parent_class);
    validate_fresh_shape(fresh_parent_claim, entry.shape, selected_parent_class)?;
    let incoming = parsed.lanes[selected_parent_class.index()]
        .clone()
        .unwrap_or_else(|| C1MatrixAccClaim::zero(entry.shape.k_log));
    let incoming_live = parsed.lanes[selected_parent_class.index()].is_some();

    observe_history_step_bank_fold_route(challenger, selected_parent_class);
    let (fold_proof, outgoing_claim) = match selected_parent_matrix {
        HistoryStepMatrixLease::Resident(matrix) => prove_matrix_claim_fold_c1(
            matrix.as_ref(),
            fresh_parent_claim,
            &incoming,
            incoming_live,
            challenger,
        ),
        HistoryStepMatrixLease::Compact(matrix) => prove_matrix_claim_fold_compact_c1(
            matrix.as_ref(),
            fresh_parent_claim,
            &incoming,
            incoming_live,
            challenger,
        ),
    };

    let mut io = parent_io.to_vec();
    io[bank.layout.base] = F128::ZERO;
    io[bank.layout.tip_class] = f128_from_u128(current_class.wire_id() as u128);
    install_folded_lane(bank, &mut io, selected_parent_class, &outgoing_claim)?;
    // The complete parent matrix fold above has no current-output argument.
    // Install the accepted block boundary only after its proof and outgoing
    // claim are fixed.
    install_current_block_accumulator(bank, &mut io, current_block_accumulator);
    // This postcondition catches accidental writes outside the selected lane
    // while keeping the implementation's carry semantics explicit.
    parse_history_step_bank_io(bank, &io)?;
    Ok(RoutedHistoryStepBankFold {
        fold_proof,
        outgoing_claim,
        io,
    })
}

/// Convenience wrapper that owns the canonical route challenger.
pub fn route_carry_and_fold_history_step_lane_canonical(
    bank: &PinnedHistoryStepClassBank,
    parent_io: &[F128],
    selected_parent_class: CanonicalHistoryStepClassId,
    current_class: CanonicalHistoryStepClassId,
    selected_parent_matrix: &HistoryStepMatrixLease,
    fresh_parent_claim: &C1FreshLincheckClaim,
    current_block_accumulator: &ChainAccumulator,
) -> Result<RoutedHistoryStepBankFold, HistoryStepBankError> {
    let mut challenger = FsLaneChallenger::new_c1(HISTORY_STEP_BANK_FOLD_TRANSCRIPT_DOMAIN);
    route_carry_and_fold_history_step_lane(
        bank,
        parent_io,
        selected_parent_class,
        current_class,
        selected_parent_matrix,
        fresh_parent_claim,
        current_block_accumulator,
        &mut challenger,
    )
}

fn validate_fresh_shape(
    fresh: &C1FreshLincheckClaim,
    shape: FieldShape,
    class_id: CanonicalHistoryStepClassId,
) -> Result<(), HistoryStepBankError> {
    let rest = shape
        .k_log
        .checked_sub(shape.k_skip)
        .ok_or(HistoryStepBankError::FreshClaimShape(class_id))?;
    let partial = 1usize
        .checked_shl(shape.k_skip as u32)
        .ok_or(HistoryStepBankError::FreshClaimShape(class_id))?;
    if fresh.x_inner_rest.len() != rest
        || fresh.r_inner_rest.len() != rest
        || fresh.z_partial.len() != partial
    {
        return Err(HistoryStepBankError::FreshClaimShape(class_id));
    }
    Ok(())
}

/// Verifier-owned handoff.  Its private fields prevent callers outside this
/// module from replacing the selected class or bank after proof replay.
#[must_use = "the verified tip replay must be discharged against its matrix bank"]
pub struct VerifiedHistoryStepTipReplay {
    class_id: CanonicalHistoryStepClassId,
    bank_digest: [u8; 32],
    fresh: C1FreshLincheckClaim,
}

enum PendingBankLane {
    Dead,
    Pending(C1MatrixAccClaim),
    Checked,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct MatrixRequirement {
    shape: FieldShape,
    digest: [u8; 32],
}

/// Process-local memoization of exact, successfully checked accumulated
/// claims. It retains no matrix and accepts no serialized or caller-minted
/// entries. A cache miss always takes the ordinary authenticated scan path.
/// Eight entries cover a few competing tips without growing with history.
#[derive(Default)]
pub(in crate::acceptance) struct HistoryStepMatrixClaimCache {
    entries: Mutex<VecDeque<CheckedMatrixClaim>>,
}

struct CheckedMatrixClaim {
    bank: [u8; 32],
    class: CanonicalHistoryStepClassId,
    matrix: MatrixRequirement,
    claim: C1MatrixAccClaim,
}

impl HistoryStepMatrixClaimCache {
    const CAPACITY: usize = 8;

    fn contains(
        &self,
        bank: [u8; 32],
        class: CanonicalHistoryStepClassId,
        matrix: MatrixRequirement,
        claim: &C1MatrixAccClaim,
    ) -> bool {
        let Ok(mut entries) = self.entries.lock() else {
            return false;
        };
        let Some(index) = entries.iter().position(|entry| {
            entry.bank == bank
                && entry.class == class
                && entry.matrix == matrix
                && entry.claim == *claim
        }) else {
            return false;
        };
        let entry = entries.remove(index).expect("located matrix claim");
        entries.push_back(entry);
        true
    }

    fn remember(&self, entry: CheckedMatrixClaim) {
        let Ok(mut entries) = self.entries.lock() else {
            return;
        };
        if entries.len() == Self::CAPACITY {
            entries.pop_front();
        }
        entries.push_back(entry);
    }
}

/// A replayed tip whose matrix obligations have not all been discharged.
/// The type is intentionally non-`Clone`, and `finish` consumes it.
#[must_use = "a HistoryStep tip is not accepted until finish() checks every matrix obligation"]
pub struct PendingHistoryStepBankDecision {
    tip_class: CanonicalHistoryStepClassId,
    tip_fresh: Option<C1FreshLincheckClaim>,
    lanes: [PendingBankLane; HISTORY_STEP_CLASS_COUNT],
    requirements: [MatrixRequirement; HISTORY_STEP_CLASS_COUNT],
    bank_digest: [u8; 32],
    base: bool,
    block_accumulator: [F128; ACC_LANES],
}

impl PendingHistoryStepBankDecision {
    /// Start only from a verifier-owned fresh claim and IO carrying every
    /// exact bank pin.  Proof replay itself remains in the sibling verifier.
    pub fn begin(
        bank: &PinnedHistoryStepClassBank,
        tip_io: &[F128],
        replay: VerifiedHistoryStepTipReplay,
    ) -> Result<Self, HistoryStepBankError> {
        if replay.bank_digest != bank.digest {
            return Err(HistoryStepBankError::BankDigest);
        }
        let parsed = parse_history_step_bank_io(bank, tip_io)?;
        if parsed.tip_class != replay.class_id {
            return Err(HistoryStepBankError::TipReplayClass {
                terminal: parsed.tip_class,
                replay: replay.class_id,
            });
        }
        let lanes = parsed.lanes.map(|claim| match claim {
            Some(claim) => PendingBankLane::Pending(claim),
            None => PendingBankLane::Dead,
        });
        let requirements = std::array::from_fn(|index| {
            let entry = &bank.entries[index];
            MatrixRequirement {
                shape: entry.shape,
                digest: entry.matrix_digest,
            }
        });
        Ok(Self {
            tip_class: parsed.tip_class,
            tip_fresh: Some(replay.fresh),
            lanes,
            requirements,
            bank_digest: replay.bank_digest,
            base: parsed.base,
            block_accumulator: parsed.block_accumulator,
        })
    }

    fn claims_for(
        &self,
        class_id: CanonicalHistoryStepClassId,
    ) -> Result<(Option<C1FreshLincheckClaim>, Option<C1MatrixAccClaim>), HistoryStepBankError>
    {
        let fresh = if class_id == self.tip_class {
            self.tip_fresh.clone()
        } else {
            None
        };
        let accumulated = match &self.lanes[class_id.index()] {
            PendingBankLane::Pending(claim) => Some(claim.clone()),
            PendingBankLane::Dead | PendingBankLane::Checked => None,
        };
        if fresh.is_none() && accumulated.is_none() {
            return Err(HistoryStepBankError::NoMatrixObligation(class_id));
        }
        Ok((fresh, accumulated))
    }

    fn complete_matrix_check(
        &mut self,
        class_id: CanonicalHistoryStepClassId,
        actual_shape: FieldShape,
        actual_digest: [u8; 32],
        fresh: Option<&C1FreshLincheckClaim>,
        accumulated: Option<&C1MatrixAccClaim>,
        actual_fresh_value: Option<F256>,
        actual_accumulated_value: Option<F256>,
    ) -> Result<(), HistoryStepBankError> {
        let requirement = self.requirements[class_id.index()];
        if actual_shape != requirement.shape {
            return Err(HistoryStepBankError::MatrixShape(class_id));
        }
        if actual_digest != requirement.digest {
            return Err(HistoryStepBankError::MatrixDigest(class_id));
        }
        if fresh.is_some_and(|claim| actual_fresh_value != Some(claim.value)) {
            return Err(HistoryStepBankError::FreshClaimValue(class_id));
        }
        if accumulated.is_some_and(|claim| actual_accumulated_value != Some(claim.value)) {
            return Err(HistoryStepBankError::AccumulatedClaimValue(class_id));
        }
        if fresh.is_some() {
            self.tip_fresh = None;
        }
        if accumulated.is_some() {
            self.lanes[class_id.index()] = PendingBankLane::Checked;
        }
        Ok(())
    }

    /// Check the tip fresh claim and/or this class's live accumulated claim
    /// in one authenticated matrix scan.  Disk-backed evaluators can be
    /// released immediately after the call.
    pub fn check_class_matrix(
        &mut self,
        class_id: CanonicalHistoryStepClassId,
        matrix: &mut dyn C1MatrixClaimEvaluator,
    ) -> Result<(), HistoryStepBankError> {
        let (fresh, accumulated) = self.claims_for(class_id)?;
        let evaluated = matrix
            .evaluate_matrix_claims_c1(fresh.as_ref(), accumulated.as_ref())
            .map_err(|_| HistoryStepBankError::MatrixEvaluation(class_id))?;
        if !evaluated.is_bound_to(fresh.as_ref(), accumulated.as_ref()) {
            return Err(HistoryStepBankError::MatrixEvaluationBinding(class_id));
        }
        self.complete_matrix_check(
            class_id,
            matrix.field_shape(),
            evaluated.structural_digest(),
            fresh.as_ref(),
            accumulated.as_ref(),
            evaluated.fresh_value(),
            evaluated.accumulated_value(),
        )
    }

    /// Resident-CSR twin used by local materialization and tests.  It hashes
    /// the actual rows and evaluates the exact same fresh/accumulated claims.
    pub fn check_class_field_r1cs(
        &mut self,
        class_id: CanonicalHistoryStepClassId,
        matrix: &FieldR1cs,
    ) -> Result<(), HistoryStepBankError> {
        let (fresh, accumulated) = self.claims_for(class_id)?;
        let requirement = self.requirements[class_id.index()];
        let actual_shape = FieldShape::of(matrix);
        if actual_shape != requirement.shape {
            return Err(HistoryStepBankError::MatrixShape(class_id));
        }
        let actual_digest = matrix.structural_statement_digest();
        if actual_digest != requirement.digest {
            return Err(HistoryStepBankError::MatrixDigest(class_id));
        }
        let actual_fresh_value = fresh
            .as_ref()
            .map(|claim| fresh_claim_value_c1(matrix, claim));
        let actual_accumulated_value = accumulated
            .as_ref()
            .map(|claim| stacked_matrix_mle_eval_c1(matrix, claim));
        self.complete_matrix_check(
            class_id,
            actual_shape,
            actual_digest,
            fresh.as_ref(),
            accumulated.as_ref(),
            actual_fresh_value,
            actual_accumulated_value,
        )
    }

    /// Representation-independent terminal check over the sealed runtime
    /// lease. Compact production matrices evaluate their authenticated packed
    /// rows directly and never require mutable ownership or CSR decoding.
    pub fn check_class_matrix_lease(
        &mut self,
        class_id: CanonicalHistoryStepClassId,
        matrix: &HistoryStepMatrixLease,
    ) -> Result<(), HistoryStepBankError> {
        match matrix {
            HistoryStepMatrixLease::Resident(matrix) => {
                self.check_class_field_r1cs(class_id, matrix.as_ref())
            }
            HistoryStepMatrixLease::Compact(matrix) => {
                let (fresh, accumulated) = self.claims_for(class_id)?;
                let evaluated = matrix
                    .evaluate_matrix_claims_c1_authenticated(fresh.as_ref(), accumulated.as_ref())
                    .map_err(|_| HistoryStepBankError::MatrixEvaluation(class_id))?;
                if !evaluated.is_bound_to(fresh.as_ref(), accumulated.as_ref()) {
                    return Err(HistoryStepBankError::MatrixEvaluationBinding(class_id));
                }
                self.complete_matrix_check(
                    class_id,
                    matrix.shape(),
                    evaluated.structural_digest(),
                    fresh.as_ref(),
                    accumulated.as_ref(),
                    evaluated.fresh_value(),
                    evaluated.accumulated_value(),
                )
            }
        }
    }

    /// Discharge the fresh tip and every live accumulated lane one matrix at
    /// a time. Each owned lease is dropped before the next class is loaded.
    pub fn finish_with_matrix_loader<E>(
        self,
        load: impl FnMut(CanonicalHistoryStepClassId) -> Result<HistoryStepMatrixLease, E>,
    ) -> Result<AcceptedHistoryStepBankTip, HistoryStepBankError> {
        self.finish_with_optional_cache(load, None)
    }

    pub(in crate::acceptance) fn finish_with_matrix_loader_cached<E>(
        self,
        load: impl FnMut(CanonicalHistoryStepClassId) -> Result<HistoryStepMatrixLease, E>,
        cache: &HistoryStepMatrixClaimCache,
    ) -> Result<AcceptedHistoryStepBankTip, HistoryStepBankError> {
        self.finish_with_optional_cache(load, Some(cache))
    }

    fn finish_with_optional_cache<E>(
        mut self,
        mut load: impl FnMut(CanonicalHistoryStepClassId) -> Result<HistoryStepMatrixLease, E>,
        cache: Option<&HistoryStepMatrixClaimCache>,
    ) -> Result<AcceptedHistoryStepBankTip, HistoryStepBankError> {
        for index in 0..HISTORY_STEP_CLASS_COUNT {
            let class = CanonicalHistoryStepClassId::from_index(index)
                .expect("resident bank contains only canonical classes");
            let has_fresh = self.tip_fresh.is_some() && class == self.tip_class;
            let has_accumulated = matches!(self.lanes[index], PendingBankLane::Pending(_));
            // Only a carried lane can bypass its matrix scan. The tip's
            // fresh obligation is always checked against its actual matrix,
            // even when the accumulated part happens to have a cache hit.
            if !has_fresh {
                if let (Some(cache), PendingBankLane::Pending(claim)) = (cache, &self.lanes[index])
                {
                    if cache.contains(self.bank_digest, class, self.requirements[index], claim) {
                        self.lanes[index] = PendingBankLane::Checked;
                        continue;
                    }
                }
            }
            if has_fresh || has_accumulated {
                let accumulated = match (&self.lanes[index], cache) {
                    (PendingBankLane::Pending(claim), Some(_)) => Some(claim.clone()),
                    _ => None,
                };
                let matrix =
                    load(class).map_err(|_| HistoryStepBankError::MatrixEvaluation(class))?;
                self.check_class_matrix_lease(class, &matrix)?;
                if let (Some(cache), Some(claim)) = (cache, accumulated) {
                    cache.remember(CheckedMatrixClaim {
                        bank: self.bank_digest,
                        class,
                        matrix: self.requirements[index],
                        claim,
                    });
                }
            }
        }
        self.finish()
    }

    /// Return an accepted terminal capability only after the tip fresh claim
    /// and every live bank lane were checked exactly once.
    pub fn finish(self) -> Result<AcceptedHistoryStepBankTip, HistoryStepBankError> {
        if self.tip_fresh.is_some() {
            return Err(HistoryStepBankError::TipMatrixUnchecked(self.tip_class));
        }
        for (index, lane) in self.lanes.iter().enumerate() {
            if matches!(lane, PendingBankLane::Pending(_)) {
                let class_id =
                    CanonicalHistoryStepClassId::from_index(index).expect("canonical class");
                return Err(HistoryStepBankError::LiveLaneUnchecked(class_id));
            }
        }
        Ok(AcceptedHistoryStepBankTip {
            tip_class: self.tip_class,
            bank_digest: self.bank_digest,
            base: self.base,
            block_accumulator: self.block_accumulator,
        })
    }
}

/// Unforgeable-in-safe-code terminal result of the complete bank decision.
#[must_use = "the accepted HistoryStep terminal must be consumed by sync acceptance"]
pub struct AcceptedHistoryStepBankTip {
    tip_class: CanonicalHistoryStepClassId,
    bank_digest: [u8; 32],
    base: bool,
    block_accumulator: [F128; ACC_LANES],
}

impl AcceptedHistoryStepBankTip {
    pub const fn tip_class(&self) -> CanonicalHistoryStepClassId {
        self.tip_class
    }

    pub const fn bank_digest(&self) -> [u8; 32] {
        self.bank_digest
    }

    pub const fn base(&self) -> bool {
        self.base
    }

    pub const fn block_accumulator(&self) -> &[F128; ACC_LANES] {
        &self.block_accumulator
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HistoryStepBankError {
    EntryOrder {
        index: usize,
        actual: CanonicalHistoryStepClassId,
    },
    EntryShape(CanonicalHistoryStepClassId),
    EntryPcs(CanonicalHistoryStepClassId),
    ParentRecursionVk(CanonicalHistoryStepClassId),
    DirectBlockVk(CanonicalHistoryStepClassId),
    EntryPostCommit(CanonicalHistoryStepClassId),
    IoLength {
        expected: usize,
        actual: usize,
    },
    BaseFlag,
    TipClass,
    BaseClass,
    SelectedParentClass {
        authenticated: CanonicalHistoryStepClassId,
        selected: CanonicalHistoryStepClassId,
    },
    ClassTransition {
        current: CanonicalHistoryStepClassId,
        parent: CanonicalHistoryStepClassId,
    },
    TipReplayClass {
        terminal: CanonicalHistoryStepClassId,
        replay: CanonicalHistoryStepClassId,
    },
    MatrixWhitelist(CanonicalHistoryStepClassId),
    PostCommitWhitelist(CanonicalHistoryStepClassId),
    BankDigest,
    LaneLiveness(CanonicalHistoryStepClassId),
    NonCanonicalDeadLane(CanonicalHistoryStepClassId),
    LaneWidth(CanonicalHistoryStepClassId),
    MatrixShape(CanonicalHistoryStepClassId),
    MatrixDigest(CanonicalHistoryStepClassId),
    TipPostCommit(CanonicalHistoryStepClassId),
    BlockAccumulator,
    FreshClaimShape(CanonicalHistoryStepClassId),
    NoMatrixObligation(CanonicalHistoryStepClassId),
    MatrixEvaluation(CanonicalHistoryStepClassId),
    MatrixEvaluationBinding(CanonicalHistoryStepClassId),
    FreshClaimValue(CanonicalHistoryStepClassId),
    AccumulatedClaimValue(CanonicalHistoryStepClassId),
    TipMatrixUnchecked(CanonicalHistoryStepClassId),
    LiveLaneUnchecked(CanonicalHistoryStepClassId),
}

impl core::fmt::Display for HistoryStepBankError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EntryOrder { index, actual } => write!(
                f,
                "HistoryStep bank index {index} contains class {}",
                actual.index()
            ),
            Self::EntryShape(class) => write!(f, "HistoryStep class {} shape drift", class.index()),
            Self::EntryPcs(class) => write!(f, "HistoryStep class {} PCS drift", class.index()),
            Self::ParentRecursionVk(class) => write!(
                f,
                "HistoryStep class {} does not use the universal parent-recursion VK",
                class.index(),
            ),
            Self::DirectBlockVk(class) => write!(
                f,
                "HistoryStep class {} does not use its current-tier Block VK",
                class.index(),
            ),
            Self::EntryPostCommit(class) => {
                write!(f, "HistoryStep class {} post-commit drift", class.index())
            }
            Self::IoLength { expected, actual } => {
                write!(f, "HistoryStep IO length {actual}, expected {expected}")
            }
            Self::BaseFlag => f.write_str("HistoryStep base selector is not boolean"),
            Self::TipClass => f.write_str("HistoryStep terminal class id is not canonical"),
            Self::BaseClass => {
                f.write_str("HistoryStep base arm does not use the genesis parent slot")
            }
            Self::SelectedParentClass {
                authenticated,
                selected,
            } => write!(
                f,
                "HistoryStep selected parent class {} differs from authenticated terminal {}",
                selected.index(),
                authenticated.index()
            ),
            Self::ClassTransition { current, parent } => write!(
                f,
                "HistoryStep class {} cannot follow parent class {}",
                current.index(),
                parent.index()
            ),
            Self::TipReplayClass { terminal, replay } => write!(
                f,
                "HistoryStep replay class {} differs from terminal class {}",
                replay.index(),
                terminal.index()
            ),
            Self::MatrixWhitelist(class) => {
                write!(
                    f,
                    "HistoryStep matrix whitelist slot {} drift",
                    class.index()
                )
            }
            Self::PostCommitWhitelist(class) => write!(
                f,
                "HistoryStep post-commit whitelist slot {} drift",
                class.index()
            ),
            Self::BankDigest => f.write_str("HistoryStep aggregate bank digest drift"),
            Self::LaneLiveness(class) => {
                write!(
                    f,
                    "HistoryStep lane {} liveness is not boolean",
                    class.index()
                )
            }
            Self::NonCanonicalDeadLane(class) => {
                write!(f, "HistoryStep dead lane {} is nonzero", class.index())
            }
            Self::LaneWidth(class) => {
                write!(f, "HistoryStep lane {} has the wrong width", class.index())
            }
            Self::MatrixShape(class) => {
                write!(
                    f,
                    "HistoryStep matrix {} has the wrong shape",
                    class.index()
                )
            }
            Self::MatrixDigest(class) => {
                write!(
                    f,
                    "HistoryStep matrix {} has the wrong digest",
                    class.index()
                )
            }
            Self::TipPostCommit(class) => write!(
                f,
                "HistoryStep tip {} has the wrong post-commit identity",
                class.index()
            ),
            Self::BlockAccumulator => {
                f.write_str("HistoryStep terminal block accumulator is not canonical")
            }
            Self::FreshClaimShape(class) => {
                write!(
                    f,
                    "HistoryStep fresh claim {} has the wrong shape",
                    class.index()
                )
            }
            Self::NoMatrixObligation(class) => {
                write!(
                    f,
                    "HistoryStep matrix {} has no pending obligation",
                    class.index()
                )
            }
            Self::MatrixEvaluation(class) => {
                write!(f, "HistoryStep matrix {} evaluation failed", class.index())
            }
            Self::MatrixEvaluationBinding(class) => write!(
                f,
                "HistoryStep matrix {} evaluation is bound to another request",
                class.index()
            ),
            Self::FreshClaimValue(class) => {
                write!(f, "HistoryStep fresh claim {} is false", class.index())
            }
            Self::AccumulatedClaimValue(class) => {
                write!(
                    f,
                    "HistoryStep accumulated claim {} is false",
                    class.index()
                )
            }
            Self::TipMatrixUnchecked(class) => {
                write!(
                    f,
                    "HistoryStep tip matrix {} was not checked",
                    class.index()
                )
            }
            Self::LiveLaneUnchecked(class) => {
                write!(f, "HistoryStep live lane {} was not checked", class.index())
            }
        }
    }
}

impl std::error::Error for HistoryStepBankError {}

#[cfg(test)]
mod cache_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use noid_ivc_core::challenger::Challenger;
    use noid_ivc_core::field_circuit::{FsChannelOps, LinExpr};

    fn test_pins() -> [HistoryStepBankEntryPins; HISTORY_STEP_CLASS_COUNT] {
        let spec = history_step_bank_io_spec();
        std::array::from_fn(|index| {
            let class_id = CanonicalHistoryStepClassId::from_index(index).unwrap();
            let shape = canonical_history_step_shape(class_id);
            let pcs_params = canonical_history_step_pcs_params(class_id);
            let matrix_digest = [index as u8 + 1; 32];
            let parent_recursion_vk_digest = [0x21; 32];
            let direct_block_vk_digest = [class_id.current_slot() as u8 + 0x41; 32];
            let post_commit_digest = history_step_bank_post_commit_digest(
                class_id,
                &matrix_digest,
                &spec,
                &pcs_params,
                parent_recursion_vk_digest,
                direct_block_vk_digest,
            );
            HistoryStepBankEntryPins {
                class_id,
                shape,
                pcs_params,
                matrix_digest,
                parent_recursion_vk_digest,
                direct_block_vk_digest,
                post_commit_digest,
            }
        })
    }

    #[test]
    fn canonical_class_id_is_the_current_tier_slot() {
        let first = CanonicalHistoryStepClassId::new(0).unwrap();
        let last = CanonicalHistoryStepClassId::new(1).unwrap();
        assert_eq!(first.index(), 0);
        assert_eq!(first.current_tier(), 25);
        assert_eq!(last.index(), 1);
        assert_eq!(last.current_tier(), 255);
        assert!(CanonicalHistoryStepClassId::new(2).is_none());
    }

    #[test]
    fn history_step_soundness_ledger_matches_basefold_target() {
        assert_eq!(
            noid_gkr::zk_auth_qrom::HISTORY_STEP_CLASSICAL_BITS,
            noid_ivc_core::pcs::BASEFOLD_UDR_TARGET_BITS
        );
        assert_eq!(noid_gkr::zk_auth_qrom::HISTORY_STEP_QROM_BITS, 83);
    }

    #[test]
    fn common_layout_retains_all_variable_width_lanes() {
        let layout = history_step_bank_io_layout();
        assert_eq!(layout.matrix_lanes.len(), HISTORY_STEP_CLASS_COUNT);
        for (index, lane) in layout.matrix_lanes.iter().enumerate() {
            let class_id = CanonicalHistoryStepClassId::from_index(index).unwrap();
            assert_eq!(
                lane.point_len(),
                2 * canonical_history_step_shape(class_id).k_log + 1
            );
        }
        assert!(layout.len <= 1usize << history_step_bank_io_spec().io_slice.log2_len);
    }

    #[test]
    fn validated_bank_pins_are_exact_and_ordered() {
        let bank = PinnedHistoryStepClassBank::validate(test_pins()).unwrap();
        assert_eq!(
            bank.entry(CanonicalHistoryStepClassId::new(0).unwrap())
                .shape()
                .m,
            22
        );
        let class = CanonicalHistoryStepClassId::new(1).unwrap();
        assert_eq!(bank.entry(class).shape().m, 24);

        let mut wrong = test_pins();
        wrong[1].post_commit_digest[0] ^= 1;
        assert!(matches!(
            PinnedHistoryStepClassBank::validate(wrong),
            Err(HistoryStepBankError::EntryPostCommit(class)) if class.index() == 1
        ));

        let mut split_parent_vk = test_pins();
        split_parent_vk[1].parent_recursion_vk_digest[0] ^= 1;
        assert!(matches!(
            PinnedHistoryStepClassBank::validate(split_parent_vk),
            Err(HistoryStepBankError::ParentRecursionVk(class)) if class.index() == 1,
        ));

        // A tampered direct-Block VK digest changes the recomputed
        // post-commit digest for exactly that class.
        let mut split_block_vk = test_pins();
        split_block_vk[1].direct_block_vk_digest[0] ^= 1;
        assert!(matches!(
            PinnedHistoryStepClassBank::validate(split_block_vk),
            Err(HistoryStepBankError::EntryPostCommit(class)) if class.index() == 1,
        ));
    }

    #[test]
    fn installing_one_lane_preserves_every_other_lane() {
        let bank = PinnedHistoryStepClassBank::validate(test_pins()).unwrap();
        let acc = crate::accumulator::genesis_accumulator();
        let mut io = history_step_bank_base_output_io(
            &bank,
            CanonicalHistoryStepClassId::new(0).unwrap(),
            &acc,
        )
        .unwrap();
        let before = io.clone();
        let selected = CanonicalHistoryStepClassId::new(1).unwrap();
        let lane = bank.layout.matrix_lanes[selected.index()];
        let claim = C1MatrixAccClaim {
            point: vec![F256::ONE; lane.point_len()],
            value: F256::ONE,
        };
        install_folded_lane(&bank, &mut io, selected, &claim).unwrap();
        for index in 0..HISTORY_STEP_CLASS_COUNT {
            if index == selected.index() {
                continue;
            }
            let other = bank.layout.matrix_lanes[index];
            assert_eq!(
                &io[other.point..=other.live],
                &before[other.point..=other.live]
            );
        }
        assert_eq!(
            history_step_bank_lane_claim(&bank, &io, selected).unwrap(),
            Some(claim)
        );
    }

    #[test]
    fn base_accepts_every_current_tier() {
        // The base case is genesis-anchored through the accumulator pins;
        // with tier-only classes every current tier is base-eligible and no
        // class encodes a parent slot to restrict.
        let bank = PinnedHistoryStepClassBank::validate(test_pins()).unwrap();
        let acc = crate::accumulator::genesis_accumulator();
        for current_slot in 0..HISTORY_STEP_TIER_SLOT_COUNT {
            let class = CanonicalHistoryStepClassId::new(current_slot).unwrap();
            let io = history_step_bank_base_output_io(&bank, class, &acc).unwrap();
            assert_eq!(history_step_bank_tip_class(&bank, &io).unwrap(), class);
            assert!(parse_history_step_bank_io(&bank, &io).unwrap().base);
        }
    }

    #[test]
    fn base_and_dead_lane_tampering_fail_closed() {
        let bank = PinnedHistoryStepClassBank::validate(test_pins()).unwrap();
        let class = CanonicalHistoryStepClassId::new(0).unwrap();
        let mut io = history_step_bank_base_output_io(
            &bank,
            class,
            &crate::accumulator::genesis_accumulator(),
        )
        .unwrap();

        io[bank.layout.base] = f128_from_u128(2);
        assert!(matches!(
            parse_history_step_bank_io(&bank, &io),
            Err(HistoryStepBankError::BaseFlag),
        ));
        io[bank.layout.base] = F128::ONE;

        let dead = bank.layout.matrix_lanes[1];
        io[dead.point] = F128::ONE;
        assert!(matches!(
            parse_history_step_bank_io(&bank, &io),
            Err(HistoryStepBankError::NonCanonicalDeadLane(id)) if id.index() == 1,
        ));
    }

    #[test]
    fn whitelist_and_aggregate_pins_fail_closed() {
        let bank = PinnedHistoryStepClassBank::validate(test_pins()).unwrap();
        let class = CanonicalHistoryStepClassId::new(1).unwrap();
        let canonical = history_step_bank_base_output_io(
            &bank,
            class,
            &crate::accumulator::genesis_accumulator(),
        )
        .unwrap();

        let mut matrix_tamper = canonical.clone();
        matrix_tamper[bank.layout.matrix_whitelist] += F128::ONE;
        assert!(matches!(
            parse_history_step_bank_io(&bank, &matrix_tamper),
            Err(HistoryStepBankError::MatrixWhitelist(id)) if id.index() == 0,
        ));

        let mut aggregate_tamper = canonical;
        aggregate_tamper[bank.layout.bank_digest + 1] += F128::ONE;
        assert!(matches!(
            parse_history_step_bank_io(&bank, &aggregate_tamper),
            Err(HistoryStepBankError::BankDigest),
        ));
    }

    #[test]
    fn route_selection_requires_the_authenticated_parent_class() {
        let bank = PinnedHistoryStepClassBank::validate(test_pins()).unwrap();
        let authenticated_parent = CanonicalHistoryStepClassId::new(1).unwrap();
        let wrong_selected = CanonicalHistoryStepClassId::new(0).unwrap();
        let current = CanonicalHistoryStepClassId::new(0).unwrap();
        let mut io = history_step_bank_base_output_io(
            &bank,
            CanonicalHistoryStepClassId::new(0).unwrap(),
            &crate::accumulator::genesis_accumulator(),
        )
        .unwrap();
        io[bank.layout.base] = F128::ZERO;
        io[bank.layout.tip_class] = f128_from_u128(authenticated_parent.wire_id() as u128);

        let k = 1usize << 7;
        let matrix = FieldR1cs {
            m: 7,
            k_log: 7,
            k_skip: 6,
            useful_rows: 1,
            a_0: noid_ivc_core::field_r1cs::SparseFieldMatrix::zero(k),
            b_0: noid_ivc_core::field_r1cs::SparseFieldMatrix::zero(k),
            const_pin: Some(0),
            digest_cache: std::sync::OnceLock::new(),
            csc_cache: std::sync::OnceLock::new(),
        };
        let fresh = C1FreshLincheckClaim {
            alpha: F256::ZERO,
            z_skip: F256::ZERO,
            x_inner_rest: vec![F256::ZERO],
            r_inner_rest: vec![F256::ZERO],
            z_partial: vec![F256::ZERO; 64],
            value: F256::ZERO,
        };
        let matrix = HistoryStepMatrixLease::resident(matrix);
        let mut challenger = FsLaneChallenger::new_c1(HISTORY_STEP_BANK_FOLD_TRANSCRIPT_DOMAIN);
        assert!(matches!(
            route_carry_and_fold_history_step_lane(
                &bank,
                &io,
                wrong_selected,
                current,
                &matrix,
                &fresh,
                &crate::accumulator::genesis_accumulator(),
                &mut challenger,
            ),
            Err(HistoryStepBankError::SelectedParentClass {
                authenticated,
                selected,
            }) if authenticated == authenticated_parent && selected == wrong_selected,
        ));
    }

    #[test]
    fn current_output_install_changes_exactly_the_accumulator_slice() {
        let bank = PinnedHistoryStepClassBank::validate(test_pins()).unwrap();
        let first_accumulator = crate::accumulator::genesis_accumulator();
        let mut second_accumulator = first_accumulator.clone();
        second_accumulator.tip_semantic_id = [0xA5; 32];
        second_accumulator.epoch_anchor_id = [0x5A; 32];
        let class = CanonicalHistoryStepClassId::new(0).unwrap();
        let canonical = history_step_bank_base_output_io(&bank, class, &first_accumulator).unwrap();
        let mut first = canonical.clone();
        let mut second = canonical;
        install_current_block_accumulator(&bank, &mut first, &first_accumulator);
        install_current_block_accumulator(&bank, &mut second, &second_accumulator);

        let block = bank.layout.block_accumulator;
        assert_eq!(&first[..block], &second[..block]);
        assert_eq!(&first[block + ACC_LANES..], &second[block + ACC_LANES..]);
        assert_eq!(
            &first[block..block + ACC_LANES],
            &block_acc_lanes(&first_accumulator)
        );
        assert_eq!(
            &second[block..block + ACC_LANES],
            &block_acc_lanes(&second_accumulator)
        );
    }

    #[test]
    #[ignore = "expensive staged-output independence audit"]
    fn parent_matrix_fold_is_independent_of_current_tip_and_epoch_output() {
        let selected = CanonicalHistoryStepClassId::new(0).unwrap();
        let current = CanonicalHistoryStepClassId::new(0).unwrap();
        let shape = canonical_history_step_shape(selected);
        let k = 1usize << shape.m;
        let matrix = FieldR1cs {
            m: shape.m,
            k_log: shape.k_log,
            k_skip: shape.k_skip,
            useful_rows: 1,
            a_0: noid_ivc_core::field_r1cs::SparseFieldMatrix::zero(k),
            b_0: noid_ivc_core::field_r1cs::SparseFieldMatrix::zero(k),
            const_pin: shape.const_pin,
            digest_cache: std::sync::OnceLock::new(),
            csc_cache: std::sync::OnceLock::new(),
        };
        let matrix_digest = matrix.structural_statement_digest();
        let mut pins = test_pins();
        pins[selected.index()].matrix_digest = matrix_digest;
        pins[selected.index()].post_commit_digest = history_step_bank_post_commit_digest(
            selected,
            &matrix_digest,
            &history_step_bank_io_spec(),
            &canonical_history_step_pcs_params(selected),
            pins[selected.index()].parent_recursion_vk_digest,
            pins[selected.index()].direct_block_vk_digest,
        );
        let bank = PinnedHistoryStepClassBank::validate(pins).unwrap();
        let mut parent_io = history_step_bank_base_output_io(
            &bank,
            selected,
            &crate::accumulator::genesis_accumulator(),
        )
        .unwrap();
        parent_io[bank.layout.base] = F128::ZERO;

        let fresh = C1FreshLincheckClaim {
            alpha: F256::ZERO,
            z_skip: F256::ZERO,
            x_inner_rest: vec![F256::ZERO; shape.k_log - shape.k_skip],
            r_inner_rest: vec![F256::ZERO; shape.k_log - shape.k_skip],
            z_partial: vec![F256::ZERO; 1usize << shape.k_skip],
            value: F256::ZERO,
        };
        let matrix = HistoryStepMatrixLease::resident(matrix);
        let first_accumulator = crate::accumulator::genesis_accumulator();
        let mut second_accumulator = first_accumulator.clone();
        second_accumulator.tip_semantic_id = [0xA5; 32];
        second_accumulator.epoch_anchor_id = [0x5A; 32];

        let first = route_carry_and_fold_history_step_lane_canonical(
            &bank,
            &parent_io,
            selected,
            current,
            &matrix,
            &fresh,
            &first_accumulator,
        )
        .unwrap();
        let second = route_carry_and_fold_history_step_lane_canonical(
            &bank,
            &parent_io,
            selected,
            current,
            &matrix,
            &fresh,
            &second_accumulator,
        )
        .unwrap();

        assert_eq!(first.fold_proof(), second.fold_proof());
        assert_eq!(first.outgoing_claim(), second.outgoing_claim());
        let block = bank.layout.block_accumulator;
        assert_eq!(&first.io()[..block], &second.io()[..block]);
        assert_eq!(
            &first.io()[block + ACC_LANES..],
            &second.io()[block + ACC_LANES..]
        );
        assert_eq!(
            &first.io()[block..block + ACC_LANES],
            &block_acc_lanes(&first_accumulator)
        );
        assert_eq!(
            &second.io()[block..block + ACC_LANES],
            &block_acc_lanes(&second_accumulator)
        );
    }

    #[derive(Default)]
    struct NativeRouteLog(Vec<(u8, Vec<u8>)>);

    impl Challenger for NativeRouteLog {
        fn observe_label(&mut self, label: &[u8]) {
            self.0.push((0, label.to_vec()));
        }

        fn observe_f128(&mut self, _value: F128) {}

        fn observe_bytes(&mut self, bytes: &[u8]) {
            self.0.push((1, bytes.to_vec()));
        }

        fn sample_f128(&mut self) -> F128 {
            F128::ZERO
        }
    }

    #[derive(Default)]
    struct TraceRouteLog(Vec<(u8, Vec<u8>)>);

    impl FsChannelOps for TraceRouteLog {
        fn observe_label(&mut self, _b: &mut FieldR1csBuilder, label: &[u8]) {
            self.0.push((0, label.to_vec()));
        }

        fn observe_f128(&mut self, _b: &mut FieldR1csBuilder, _value: &LinExpr) {}

        fn observe_f128_slice(&mut self, _b: &mut FieldR1csBuilder, _values: &[LinExpr]) {}

        fn sample_f128(&mut self, _b: &mut FieldR1csBuilder) -> LinExpr {
            LinExpr::zero()
        }

        fn sample_f128_vec(&mut self, _b: &mut FieldR1csBuilder, n: usize) -> Vec<LinExpr> {
            vec![LinExpr::zero(); n]
        }

        fn verify_pow(&mut self, _b: &mut FieldR1csBuilder, _nonce: &LinExpr, _bits: u32) {}

        fn observe_bytes_const(&mut self, _b: &mut FieldR1csBuilder, bytes: &[u8]) {
            self.0.push((1, bytes.to_vec()));
        }

        fn observe_lanes(&mut self, b: &mut FieldR1csBuilder, byte_len: u64, lanes: &[LinExpr]) {
            assert_eq!(byte_len, 1);
            assert_eq!(lanes.len(), 1);
            let value = f128_to_u128(lanes[0].eval(b.values()));
            self.0.push((1, vec![value as u8]));
        }
    }

    #[test]
    fn native_and_trace_fold_routes_bind_the_same_full_class_byte() {
        for index in 0..HISTORY_STEP_CLASS_COUNT {
            let class = CanonicalHistoryStepClassId::from_index(index).unwrap();
            let mut native = NativeRouteLog::default();
            observe_history_step_bank_fold_route(&mut native, class);
            let mut trace = TraceRouteLog::default();
            let mut builder = FieldR1csBuilder::new_witness_only();
            let class_wire = LinExpr::constant(f128_from_u128(class.wire_id() as u128));
            observe_history_step_bank_fold_route_trace(&mut builder, &mut trace, &class_wire);
            assert_eq!(native.0, trace.0, "class {index} route transcript drift");
            assert_eq!(native.0[1].1, vec![class.wire_id()]);
        }
    }
}
