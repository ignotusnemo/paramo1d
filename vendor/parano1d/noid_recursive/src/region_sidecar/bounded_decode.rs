// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Allocation-safe bincode-v1 shape preflight for fixed-class sidecars.
//!
//! Bincode's byte limit is not an allocation bound: a forged sequence length
//! can be consumed before the decoder discovers that the input is truncated.
//! This module walks the exact standalone fixed-int wire shape without allocating,
//! validates every sequence length against canonical class metadata, and only
//! then permits serde deserialization.

use noid_ivc_core::deep_chain::relations::{claimed_refs, ColRef, RELATION_DEGREE};
use noid_ivc_core::deep_chain::schedule::{
    carry_selection_terms, duplex_substitution_terms, DuplexFamilyRefs,
};
use noid_ivc_core::deep_chain::WALK_DEGREE;
use noid_ivc_core::field::F128;
use noid_poseidon2b::native::permutation::{N_ROUNDS, STATE_SIZE};

use crate::acceptance::trace::region_source_binding::{
    merkle_protocol_substitution_terms, merkle_protocol_zero_terms, DuplexUnionProof,
};

use super::merkle_trace::preflight_merkle_authority;
use super::trace::preflight_duplex_authority;
use super::{
    DuplexRegionSidecarProof, DuplexRegionVk, MerkleProtocolFamily, MerkleRegionSidecarProof,
    MerkleRegionVk, RegionSidecarError, DUPLEX_REGION_SIDECAR_VERSION,
    MERKLE_REGION_SIDECAR_VERSION,
};

const U64_BYTES: usize = 8;
const F128_BYTES: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct RelationShape {
    pub(super) rounds: usize,
    pub(super) values: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ProofTailShape {
    None,
    RelationOption(Option<RelationShape>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct FixedProofShape {
    pub(super) version: u8,
    pub(super) w_log: usize,
    pub(super) selection_values: usize,
    pub(super) substitution_values: usize,
    pub(super) shifts: usize,
    pub(super) tail: ProofTailShape,
}

/// Exact wire shape of a `version + authority` fixed-family child whose
/// deep-chain walk is serialized once by its enclosing proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct DeferredFixedProofShape {
    pub(super) version: u8,
    pub(super) w_log: usize,
    pub(super) selection_values: usize,
    pub(super) substitution_values: usize,
    pub(super) shifts: usize,
    pub(super) tail: ProofTailShape,
}

impl FixedProofShape {
    /// Preserve every V1 authority dimension while removing only the embedded
    /// walk field from the serialized child wrapper.
    pub(super) fn walk_deferred(self) -> DeferredFixedProofShape {
        DeferredFixedProofShape {
            version: self.version,
            w_log: self.w_log,
            selection_values: self.selection_values,
            substitution_values: self.substitution_values,
            shifts: self.shifts,
            tail: self.tail,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct MerkleProofShape {
    pub(super) version: u8,
    pub(super) w_log: usize,
    pub(super) zero_values: usize,
    pub(super) zero_shifts: usize,
    pub(super) selection_values: usize,
    pub(super) substitution_values: usize,
    pub(super) shifts: usize,
}

/// Exact wire shape of a `version + authority` Merkle child with its walk
/// deferred to an enclosing multi-instance proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct DeferredMerkleProofShape {
    pub(super) version: u8,
    pub(super) w_log: usize,
    pub(super) zero_values: usize,
    pub(super) zero_shifts: usize,
    pub(super) selection_values: usize,
    pub(super) substitution_values: usize,
    pub(super) shifts: usize,
}

impl MerkleProofShape {
    /// Preserve all relation/shift dimensions and omit exactly the walk.
    pub(super) fn walk_deferred(self) -> DeferredMerkleProofShape {
        DeferredMerkleProofShape {
            version: self.version,
            w_log: self.w_log,
            zero_values: self.zero_values,
            zero_shifts: self.zero_shifts,
            selection_values: self.selection_values,
            substitution_values: self.substitution_values,
            shifts: self.shifts,
        }
    }
}

/// Exact shape of [`noid_ivc_core::deep_chain::MultiDeepChainWalkProof`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct MultiWalkProofShape {
    pub(super) w_log: usize,
    pub(super) instances: usize,
}

pub(super) fn multi_walk_proof_shape(
    w_log: usize,
    instances: usize,
) -> Result<MultiWalkProofShape, RegionSidecarError> {
    if instances == 0 {
        return Err(RegionSidecarError::InvalidProof);
    }
    Ok(MultiWalkProofShape { w_log, instances })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum VecClass {
    ZeroRounds,
    ZeroValues,
    ZeroShifts,
    ZeroShiftRounds,
    SelectionRounds,
    SelectionValues,
    WalkLayers,
    WalkLayerRounds,
    SubstitutionRounds,
    SubstitutionValues,
    Shifts,
    ShiftRounds,
    SpineRounds,
    SpineValues,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LayoutField {
    Version,
    VecLength(VecClass),
    OptionTag,
}

struct FixedIntCursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> FixedIntCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn position(&self) -> usize {
        self.position
    }

    fn read_u8(&mut self) -> Result<u8, RegionSidecarError> {
        let value = *self
            .bytes
            .get(self.position)
            .ok_or(RegionSidecarError::InvalidProof)?;
        self.position += 1;
        Ok(value)
    }

    fn read_u64(&mut self) -> Result<u64, RegionSidecarError> {
        let end = self
            .position
            .checked_add(U64_BYTES)
            .ok_or(RegionSidecarError::InvalidProof)?;
        let raw: [u8; U64_BYTES] = self
            .bytes
            .get(self.position..end)
            .ok_or(RegionSidecarError::InvalidProof)?
            .try_into()
            .map_err(|_| RegionSidecarError::InvalidProof)?;
        self.position = end;
        Ok(u64::from_le_bytes(raw))
    }

    fn expect_vec_len(
        &mut self,
        expected: usize,
        class: VecClass,
        observe: &mut impl FnMut(LayoutField, usize),
    ) -> Result<(), RegionSidecarError> {
        observe(LayoutField::VecLength(class), self.position);
        let expected = u64::try_from(expected).map_err(|_| RegionSidecarError::InvalidProof)?;
        if self.read_u64()? != expected {
            return Err(RegionSidecarError::InvalidProof);
        }
        Ok(())
    }

    fn skip(&mut self, count: usize) -> Result<(), RegionSidecarError> {
        let end = self
            .position
            .checked_add(count)
            .ok_or(RegionSidecarError::InvalidProof)?;
        if end > self.bytes.len() {
            return Err(RegionSidecarError::InvalidProof);
        }
        self.position = end;
        Ok(())
    }

    fn skip_f128s(&mut self, count: usize) -> Result<(), RegionSidecarError> {
        self.skip(checked_mul(count, F128_BYTES)?)
    }

    fn finish(self) -> Result<(), RegionSidecarError> {
        if self.position != self.bytes.len() {
            return Err(RegionSidecarError::InvalidProof);
        }
        Ok(())
    }
}

/// Decode one homogeneous Duplex sidecar only after an allocation-free exact
/// bincode-v1 fixed-int shape pass tied to `vk` and `total_vars`.
pub fn decode_duplex_region_sidecar_bounded(
    vk: &DuplexRegionVk,
    total_vars: usize,
    bytes: &[u8],
) -> Result<DuplexRegionSidecarProof, RegionSidecarError> {
    vk.validate_in_witness(total_vars)?;
    let shape = duplex_proof_shape(vk);
    preflight_fixed_proof(bytes, &shape)?;
    record_serde_attempt();
    let proof: DuplexRegionSidecarProof =
        bincode::deserialize(bytes).map_err(|_| RegionSidecarError::InvalidProof)?;
    if proof.version != DUPLEX_REGION_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    preflight_duplex_authority(vk.w_log, &vk.refs, authority(&proof))?;
    Ok(proof)
}

/// Decode one canonical Walk-B sidecar after validating every zero/selection/
/// walk/substitution/shift sequence length without allocating.
pub fn decode_merkle_region_sidecar_bounded(
    vk: &MerkleRegionVk,
    total_vars: usize,
    bytes: &[u8],
) -> Result<MerkleRegionSidecarProof, RegionSidecarError> {
    vk.validate_in_witness(total_vars)?;
    let families = vk.protocol_families();
    let shape = merkle_proof_shape(vk, &families);
    preflight_merkle_proof(bytes, &shape)?;
    record_serde_attempt();
    let proof: MerkleRegionSidecarProof =
        bincode::deserialize(bytes).map_err(|_| RegionSidecarError::InvalidProof)?;
    if proof.version != MERKLE_REGION_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    preflight_merkle_authority(
        vk.w_log,
        &vk.fixed,
        &[0, 1, 2, 3],
        &families,
        &proof.authority,
    )?;
    Ok(proof)
}

fn authority(proof: &DuplexRegionSidecarProof) -> &DuplexUnionProof {
    &proof.authority
}

pub(super) fn duplex_proof_shape(vk: &DuplexRegionVk) -> FixedProofShape {
    duplex_like_proof_shape(DUPLEX_REGION_SIDECAR_VERSION, vk.w_log, &vk.refs)
}

pub(super) fn duplex_shape_for_vk(
    vk: &DuplexRegionVk,
    total_vars: usize,
) -> Result<FixedProofShape, RegionSidecarError> {
    vk.validate_certified_c1_in_witness(total_vars)?;
    Ok(duplex_proof_shape(vk))
}

pub(super) fn duplex_like_proof_shape(
    version: u8,
    w_log: usize,
    refs: &DuplexFamilyRefs,
) -> FixedProofShape {
    let selection_values = claimed_refs(&carry_selection_terms(&refs.c, F128::ONE)).len();
    let substitution_refs = claimed_refs(&duplex_substitution_terms(refs, F128::ONE));
    let shifts = substitution_refs
        .iter()
        .filter(|reference| {
            matches!(
                reference,
                noid_ivc_core::deep_chain::relations::ColRef::CommittedShift(_)
                    | noid_ivc_core::deep_chain::relations::ColRef::CommittedShift2(_)
            )
        })
        .count();
    FixedProofShape {
        version,
        w_log,
        selection_values,
        substitution_values: substitution_refs.len(),
        shifts,
        tail: ProofTailShape::None,
    }
}

pub(super) fn merkle_shape_for_vk(
    vk: &MerkleRegionVk,
    total_vars: usize,
) -> Result<MerkleProofShape, RegionSidecarError> {
    vk.validate_certified_c1_in_witness(total_vars)?;
    let families = vk.protocol_families();
    Ok(merkle_proof_shape(vk, &families))
}

fn merkle_proof_shape(vk: &MerkleRegionVk, families: &[MerkleProtocolFamily]) -> MerkleProofShape {
    let zero_refs = claimed_refs(&merkle_protocol_zero_terms(families, F128::ONE));
    let selection_values = claimed_refs(&carry_selection_terms(&[0, 1, 2, 3], F128::ONE)).len();
    let substitution_refs = claimed_refs(&merkle_protocol_substitution_terms(families, F128::ONE));
    MerkleProofShape {
        version: MERKLE_REGION_SIDECAR_VERSION,
        w_log: vk.w_log,
        zero_values: zero_refs.len(),
        zero_shifts: shift_count(&zero_refs),
        selection_values,
        substitution_values: substitution_refs.len(),
        shifts: shift_count(&substitution_refs),
    }
}

fn shift_count(references: &[ColRef]) -> usize {
    references
        .iter()
        .filter(|reference| {
            matches!(
                reference,
                ColRef::CommittedShift(_) | ColRef::CommittedShift2(_)
            )
        })
        .count()
}

pub(super) fn preflight_fixed_proof(
    bytes: &[u8],
    shape: &FixedProofShape,
) -> Result<(), RegionSidecarError> {
    scan_fixed_proof(bytes, shape, &mut |_, _| {})
}

pub(super) fn preflight_merkle_proof(
    bytes: &[u8],
    shape: &MerkleProofShape,
) -> Result<(), RegionSidecarError> {
    let ceiling = merkle_proof_encoded_len(shape)?;
    if bytes.len() > ceiling {
        return Err(RegionSidecarError::InvalidProof);
    }
    let mut cursor = FixedIntCursor::new(bytes);
    scan_merkle_proof_body(&mut cursor, shape, &mut |_, _| {})?;
    cursor.finish()
}

fn scan_fixed_proof(
    bytes: &[u8],
    shape: &FixedProofShape,
    observe: &mut impl FnMut(LayoutField, usize),
) -> Result<(), RegionSidecarError> {
    let ceiling = fixed_proof_encoded_len(shape)?;
    if bytes.len() > ceiling {
        return Err(RegionSidecarError::InvalidProof);
    }

    let mut cursor = FixedIntCursor::new(bytes);
    scan_fixed_proof_body(&mut cursor, shape, observe)?;
    cursor.finish()
}

fn scan_fixed_proof_body(
    cursor: &mut FixedIntCursor<'_>,
    shape: &FixedProofShape,
    observe: &mut impl FnMut(LayoutField, usize),
) -> Result<(), RegionSidecarError> {
    observe(LayoutField::Version, cursor.position());
    if cursor.read_u8()? != shape.version {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    scan_relation(
        cursor,
        RelationShape {
            rounds: shape.w_log,
            values: shape.selection_values,
        },
        VecClass::SelectionRounds,
        VecClass::SelectionValues,
        observe,
    )?;
    scan_walk(cursor, shape.w_log, observe)?;
    scan_relation(
        cursor,
        RelationShape {
            rounds: shape.w_log,
            values: shape.substitution_values,
        },
        VecClass::SubstitutionRounds,
        VecClass::SubstitutionValues,
        observe,
    )?;
    scan_shifts(
        cursor,
        shape.w_log,
        shape.shifts,
        VecClass::Shifts,
        VecClass::ShiftRounds,
        observe,
    )?;
    match shape.tail {
        ProofTailShape::None => {}
        ProofTailShape::RelationOption(expected) => {
            observe(LayoutField::OptionTag, cursor.position());
            let tag = cursor.read_u8()?;
            match (expected, tag) {
                (None, 0) => {}
                (Some(relation), 1) => scan_relation(
                    cursor,
                    relation,
                    VecClass::SpineRounds,
                    VecClass::SpineValues,
                    observe,
                )?,
                _ => return Err(RegionSidecarError::InvalidProof),
            }
        }
    }
    Ok(())
}

fn scan_merkle_proof_body(
    cursor: &mut FixedIntCursor<'_>,
    shape: &MerkleProofShape,
    observe: &mut impl FnMut(LayoutField, usize),
) -> Result<(), RegionSidecarError> {
    observe(LayoutField::Version, cursor.position());
    if cursor.read_u8()? != shape.version {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    scan_relation(
        cursor,
        RelationShape {
            rounds: shape.w_log,
            values: shape.zero_values,
        },
        VecClass::ZeroRounds,
        VecClass::ZeroValues,
        observe,
    )?;
    scan_shifts(
        cursor,
        shape.w_log,
        shape.zero_shifts,
        VecClass::ZeroShifts,
        VecClass::ZeroShiftRounds,
        observe,
    )?;
    scan_relation(
        cursor,
        RelationShape {
            rounds: shape.w_log,
            values: shape.selection_values,
        },
        VecClass::SelectionRounds,
        VecClass::SelectionValues,
        observe,
    )?;
    scan_walk(cursor, shape.w_log, observe)?;
    scan_relation(
        cursor,
        RelationShape {
            rounds: shape.w_log,
            values: shape.substitution_values,
        },
        VecClass::SubstitutionRounds,
        VecClass::SubstitutionValues,
        observe,
    )?;
    scan_shifts(
        cursor,
        shape.w_log,
        shape.shifts,
        VecClass::Shifts,
        VecClass::ShiftRounds,
        observe,
    )
}

fn scan_relation(
    cursor: &mut FixedIntCursor<'_>,
    shape: RelationShape,
    rounds_class: VecClass,
    values_class: VecClass,
    observe: &mut impl FnMut(LayoutField, usize),
) -> Result<(), RegionSidecarError> {
    cursor.expect_vec_len(shape.rounds, rounds_class, observe)?;
    cursor.skip_f128s(checked_mul(shape.rounds, RELATION_DEGREE)?)?;
    cursor.expect_vec_len(shape.values, values_class, observe)?;
    cursor.skip_f128s(shape.values)
}

fn scan_shifts(
    cursor: &mut FixedIntCursor<'_>,
    w_log: usize,
    count: usize,
    shifts_class: VecClass,
    rounds_class: VecClass,
    observe: &mut impl FnMut(LayoutField, usize),
) -> Result<(), RegionSidecarError> {
    cursor.expect_vec_len(count, shifts_class, observe)?;
    for _ in 0..count {
        cursor.expect_vec_len(w_log, rounds_class, observe)?;
        cursor.skip_f128s(checked_mul(w_log, 2)?)?;
        cursor.skip_f128s(1)?;
    }
    Ok(())
}

fn scan_walk(
    cursor: &mut FixedIntCursor<'_>,
    w_log: usize,
    observe: &mut impl FnMut(LayoutField, usize),
) -> Result<(), RegionSidecarError> {
    cursor.expect_vec_len(N_ROUNDS, VecClass::WalkLayers, observe)?;
    for _ in 0..N_ROUNDS {
        cursor.expect_vec_len(w_log, VecClass::WalkLayerRounds, observe)?;
        cursor.skip_f128s(checked_mul(w_log, WALK_DEGREE)?)?;
        cursor.skip_f128s(STATE_SIZE)?;
    }
    Ok(())
}

fn fixed_proof_encoded_len(shape: &FixedProofShape) -> Result<usize, RegionSidecarError> {
    let selection = relation_encoded_len(RelationShape {
        rounds: shape.w_log,
        values: shape.selection_values,
    })?;
    let substitution = relation_encoded_len(RelationShape {
        rounds: shape.w_log,
        values: shape.substitution_values,
    })?;
    let walk = walk_encoded_len(shape.w_log)?;
    let shifts = shifts_encoded_len(shape.w_log, shape.shifts)?;
    let tail = match shape.tail {
        ProofTailShape::None => 0,
        ProofTailShape::RelationOption(None) => 1,
        ProofTailShape::RelationOption(Some(relation)) => {
            checked_add(1, relation_encoded_len(relation)?)?
        }
    };
    [1usize, selection, walk, substitution, shifts, tail]
        .into_iter()
        .try_fold(0usize, checked_add)
}

fn merkle_proof_encoded_len(shape: &MerkleProofShape) -> Result<usize, RegionSidecarError> {
    let zero = relation_encoded_len(RelationShape {
        rounds: shape.w_log,
        values: shape.zero_values,
    })?;
    let zero_shifts = shifts_encoded_len(shape.w_log, shape.zero_shifts)?;
    let selection = relation_encoded_len(RelationShape {
        rounds: shape.w_log,
        values: shape.selection_values,
    })?;
    let walk = walk_encoded_len(shape.w_log)?;
    let substitution = relation_encoded_len(RelationShape {
        rounds: shape.w_log,
        values: shape.substitution_values,
    })?;
    let shifts = shifts_encoded_len(shape.w_log, shape.shifts)?;
    [
        1usize,
        zero,
        zero_shifts,
        selection,
        walk,
        substitution,
        shifts,
    ]
    .into_iter()
    .try_fold(0usize, checked_add)
}

fn walk_encoded_len(w_log: usize) -> Result<usize, RegionSidecarError> {
    let layer = checked_add(
        U64_BYTES,
        checked_add(
            checked_mul(checked_mul(w_log, WALK_DEGREE)?, F128_BYTES)?,
            checked_mul(STATE_SIZE, F128_BYTES)?,
        )?,
    )?;
    checked_add(U64_BYTES, checked_mul(N_ROUNDS, layer)?)
}

fn shifts_encoded_len(w_log: usize, count: usize) -> Result<usize, RegionSidecarError> {
    let shift = checked_add(
        U64_BYTES,
        checked_add(checked_mul(checked_mul(w_log, 2)?, F128_BYTES)?, F128_BYTES)?,
    )?;
    checked_add(U64_BYTES, checked_mul(count, shift)?)
}

fn relation_encoded_len(shape: RelationShape) -> Result<usize, RegionSidecarError> {
    [
        U64_BYTES,
        checked_mul(checked_mul(shape.rounds, RELATION_DEGREE)?, F128_BYTES)?,
        U64_BYTES,
        checked_mul(shape.values, F128_BYTES)?,
    ]
    .into_iter()
    .try_fold(0usize, checked_add)
}

fn checked_add(left: usize, right: usize) -> Result<usize, RegionSidecarError> {
    left.checked_add(right)
        .ok_or(RegionSidecarError::InvalidProof)
}

fn checked_mul(left: usize, right: usize) -> Result<usize, RegionSidecarError> {
    left.checked_mul(right)
        .ok_or(RegionSidecarError::InvalidProof)
}

#[cfg(test)]
pub(super) fn layout_offsets(
    bytes: &[u8],
    shape: &FixedProofShape,
) -> Result<Vec<(LayoutField, usize)>, RegionSidecarError> {
    let mut offsets = Vec::new();
    scan_fixed_proof(bytes, shape, &mut |field, offset| {
        if !offsets.iter().any(|(seen, _)| *seen == field) {
            offsets.push((field, offset));
        }
    })?;
    Ok(offsets)
}

#[cfg(test)]
pub(super) fn layout_offsets_merkle(
    bytes: &[u8],
    shape: &MerkleProofShape,
) -> Result<Vec<(LayoutField, usize)>, RegionSidecarError> {
    let ceiling = merkle_proof_encoded_len(shape)?;
    if bytes.len() > ceiling {
        return Err(RegionSidecarError::InvalidProof);
    }
    let mut cursor = FixedIntCursor::new(bytes);
    let mut offsets = Vec::new();
    scan_merkle_proof_body(&mut cursor, shape, &mut |field, offset| {
        if !offsets.iter().any(|(seen, _)| *seen == field) {
            offsets.push((field, offset));
        }
    })?;
    cursor.finish()?;
    Ok(offsets)
}

#[cfg(test)]
thread_local! {
    static SERDE_ATTEMPTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(super) fn record_serde_attempt() {
    SERDE_ATTEMPTS.with(|attempts| attempts.set(attempts.get() + 1));
}

#[cfg(not(test))]
pub(super) fn record_serde_attempt() {}

#[cfg(test)]
pub(super) fn serde_attempts() -> usize {
    SERDE_ATTEMPTS.with(std::cell::Cell::get)
}
