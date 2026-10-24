// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Recursive trace replay for recording-free Walk-B sidecars.
//!
//! Proof vectors are fully preflighted before any witness allocation. The
//! replay follows the native category order exactly: zero relation and its
//! shifts, carry selection, deep-chain walk, then substitution and its shifts.
//! Terminal PCS descriptors are reconstructed from canonical family refs and
//! resolved through the VK's nine exact slices.

use noid_ivc_core::deep_chain::relations::{claimed_refs, ColRef, FixedPattern, RelationTerm};
use noid_ivc_core::deep_chain::schedule::{carry_selection_terms, merkle_booleanity_terms};
use noid_ivc_core::field::F128;
use noid_ivc_core::field_circuit::FsChannelOps;
use noid_poseidon2b::native::permutation::{N_ROUNDS, STATE_SIZE};

use crate::acceptance::trace::deep_chain::{
    verify_column_relation_trace, verify_deep_chain_walk_trace, verify_shift_discharge_trace,
    C1LaneClaimGroupTrace, ColumnRelationProofTrace, DeepChainWalkProofTrace, LaneClaimGroupTrace,
    RelationTermTrace, ShiftDischargeProofTrace,
};
use crate::acceptance::trace::region_source_binding::{
    mds_alpha_weights, merkle_protocol_substitution_terms, merkle_protocol_zero_terms,
    MerkleProtocolFamily, MerkleUnionProof, MerkleUnionWalkDeferredProofRef,
};
use crate::acceptance::trace::region_source_binding_c1::{
    verify_c1_merkle_walk_prefix_trace, verify_c1_merkle_walk_suffix_trace,
    C1MerkleColumnClaimTrace, C1MerkleUnionTraceWalkPrefix,
};
use crate::acceptance::trace::self_verify::{
    C1QuirkyDirectClaimTrace, FieldPostCommitTraceContext, QuirkyDirectClaimTrace,
};
use crate::acceptance::trace::{mul, ExtExpr, FieldR1csBuilder, LinExpr};

use super::{
    C1MerkleRegionWalkDeferredProof, MerkleRegionSidecarProof, MerkleRegionVk, RegionSidecarError,
    MERKLE_REGION_COMMITTED_COLUMNS, MERKLE_REGION_SIDECAR_VERSION,
    MERKLE_SIDECAR_TRANSCRIPT_LABEL,
};

pub(crate) struct C1MerkleRegionTraceWalkContinuation<'a> {
    vk: &'a MerkleRegionVk,
    total_vars: usize,
    families: Vec<MerkleProtocolFamily>,
    prefix: C1MerkleUnionTraceWalkPrefix<'a>,
}

impl C1MerkleRegionTraceWalkContinuation<'_> {
    pub(crate) fn walk_group(&self) -> C1LaneClaimGroupTrace {
        self.prefix.walk_group().clone()
    }

    pub(crate) fn finish<C: FsChannelOps>(
        self,
        b: &mut FieldR1csBuilder,
        context: &mut FieldPostCommitTraceContext<'_, C>,
        walk_terminal: &C1LaneClaimGroupTrace,
    ) -> Result<Vec<C1QuirkyDirectClaimTrace>, RegionSidecarError> {
        if context.total_vars() != self.total_vars {
            return Err(RegionSidecarError::InvalidProof);
        }
        let terminal = verify_c1_merkle_walk_suffix_trace(
            b,
            context,
            self.vk.w_log,
            &self.vk.fixed,
            &self.families,
            self.prefix,
            walk_terminal,
        )?;
        resolve_c1_merkle_terminal_claims_trace(self.vk, self.total_vars, terminal)
    }
}

pub(crate) fn verify_c1_merkle_region_walk_deferred_prefix_trace<'a, C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    context: &mut FieldPostCommitTraceContext<'_, C>,
    vk: &'a MerkleRegionVk,
    proof: &'a C1MerkleRegionWalkDeferredProof,
) -> Result<C1MerkleRegionTraceWalkContinuation<'a>, RegionSidecarError> {
    let total_vars = context.total_vars();
    vk.validate_certified_c1_in_witness(total_vars)?;
    if proof.version != MERKLE_REGION_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    let families = vk.protocol_families();
    context.observe_label(b, MERKLE_SIDECAR_TRANSCRIPT_LABEL);
    crate::acceptance::trace::self_verify::observe_pinned_digest(
        b,
        context,
        &vk.transcript_digest(),
    );
    let prefix = verify_c1_merkle_walk_prefix_trace(
        b,
        context,
        vk.w_log,
        &vk.fixed,
        &[0, 1, 2, 3],
        &families,
        proof.authority.as_ref(),
    )?;
    Ok(C1MerkleRegionTraceWalkContinuation {
        vk,
        total_vars,
        families,
        prefix,
    })
}

fn resolve_c1_merkle_terminal_claims_trace(
    vk: &MerkleRegionVk,
    total_vars: usize,
    terminal: Vec<C1MerkleColumnClaimTrace>,
) -> Result<Vec<C1QuirkyDirectClaimTrace>, RegionSidecarError> {
    terminal
        .into_iter()
        .map(|claim| {
            let slice = *vk
                .slices
                .get(claim.column)
                .ok_or(RegionSidecarError::InvalidProof)?;
            if claim.point.len() != slice.log2_len {
                return Err(RegionSidecarError::InvalidProof);
            }
            let mut x_rest = claim.point;
            x_rest.extend(
                slice
                    .prefix_coords(total_vars)
                    .into_iter()
                    .map(|value| ExtExpr::constant(noid_ivc_core::field::F256::from_base(value))),
            );
            Ok(C1QuirkyDirectClaimTrace {
                z_skip: ExtExpr::zero(),
                k_skip: 0,
                x_rest,
                value: claim.value,
            })
        })
        .collect()
}

/// A structurally derived terminal claim on one of the shared nine columns.
/// This is transient trace state and never serialized proof authority.
pub(crate) struct MerkleColumnClaimTrace {
    pub(crate) column: usize,
    pub(crate) point: Vec<LinExpr>,
    pub(crate) value: LinExpr,
}

/// Trace typestate at Walk-B's transcript boundary immediately before the
/// caller-owned deep-chain walk.
pub(crate) struct MerkleUnionTraceWalkPrefix<'a> {
    proof: MerkleUnionWalkDeferredProofRef<'a>,
    terminal_claims: Vec<MerkleColumnClaimTrace>,
    walk_group: LaneClaimGroupTrace,
}

impl MerkleUnionTraceWalkPrefix<'_> {
    pub(crate) fn walk_group(&self) -> &LaneClaimGroupTrace {
        &self.walk_group
    }
}

fn constant_trace_terms(terms: Vec<RelationTerm>) -> Vec<RelationTermTrace> {
    terms
        .into_iter()
        .map(|term| RelationTermTrace {
            coeff: LinExpr::constant(term.coeff),
            factors: term.factors,
        })
        .collect()
}

/// Trace-coefficient twin of `merkle_protocol_zero_terms`, including its
/// category ordering independent of physical family order.
fn merkle_zero_terms_trace(
    b: &mut FieldR1csBuilder,
    families: &[MerkleProtocolFamily],
    lambda: &LinExpr,
) -> Vec<RelationTermTrace> {
    let mut terms = Vec::new();
    for family in families {
        if let MerkleProtocolFamily::TwoPermutation { refs, .. } = family {
            terms.extend(constant_trace_terms(merkle_booleanity_terms(refs)));
        }
    }

    let lambda_squared = mul(b, lambda, lambda);
    for family in families {
        if let MerkleProtocolFamily::FeedForward { refs, .. } = family {
            for (lane, weight) in [lambda.clone(), lambda_squared.clone()]
                .into_iter()
                .enumerate()
            {
                let nonstart = ColRef::Fixed(refs.nodens);
                let child = ColRef::Committed(refs.cr[lane]);
                let child_shift = ColRef::CommittedShift(refs.cr[lane]);
                let sibling_shift = ColRef::CommittedShift(refs.sib[lane]);
                let direction_shift = ColRef::CommittedShift(refs.d);
                let carry_shift = ColRef::CommittedShift(refs.c[lane]);
                for factors in [
                    vec![nonstart, child],
                    vec![nonstart, carry_shift],
                    vec![nonstart, child_shift],
                    vec![nonstart, direction_shift, child_shift],
                    vec![nonstart, direction_shift, sibling_shift],
                ] {
                    terms.push(RelationTermTrace {
                        coeff: weight.clone(),
                        factors,
                    });
                }
            }
        }
    }

    let mut paired_weights = Vec::new();
    if families
        .iter()
        .any(|family| matches!(family, MerkleProtocolFamily::PairedUpdate { .. }))
    {
        paired_weights.push(LinExpr::constant(F128::ONE));
        for _ in 1..6 {
            let next = mul(b, paired_weights.last().expect("paired weight"), lambda);
            paired_weights.push(next);
        }
    }
    for family in families {
        if let MerkleProtocolFamily::PairedUpdate { refs, .. } = family {
            let equations = [
                (
                    vec![
                        ColRef::Fixed(refs.old_even),
                        ColRef::Committed(refs.d),
                        ColRef::Committed(refs.d),
                    ],
                    vec![ColRef::Fixed(refs.old_even), ColRef::Committed(refs.d)],
                ),
                (
                    vec![ColRef::Fixed(refs.bridge), ColRef::Committed(refs.e[0])],
                    vec![
                        ColRef::Fixed(refs.bridge),
                        ColRef::CommittedShift2(refs.c[0]),
                    ],
                ),
                (
                    vec![ColRef::Fixed(refs.bridge), ColRef::Committed(refs.e[1])],
                    vec![
                        ColRef::Fixed(refs.bridge),
                        ColRef::CommittedShift2(refs.c[1]),
                    ],
                ),
                (
                    vec![
                        ColRef::Fixed(refs.copy_step),
                        ColRef::Committed(refs.sib[0]),
                    ],
                    vec![
                        ColRef::Fixed(refs.copy_step),
                        ColRef::CommittedShift(refs.sib[0]),
                    ],
                ),
                (
                    vec![
                        ColRef::Fixed(refs.copy_step),
                        ColRef::Committed(refs.sib[1]),
                    ],
                    vec![
                        ColRef::Fixed(refs.copy_step),
                        ColRef::CommittedShift(refs.sib[1]),
                    ],
                ),
                (
                    vec![ColRef::Fixed(refs.copy_step), ColRef::Committed(refs.d)],
                    vec![
                        ColRef::Fixed(refs.copy_step),
                        ColRef::CommittedShift(refs.d),
                    ],
                ),
            ];
            for (weight, (left, right)) in paired_weights.iter().zip(equations) {
                for factors in [left, right] {
                    terms.push(RelationTermTrace {
                        coeff: weight.clone(),
                        factors,
                    });
                }
            }
        }
    }
    terms
}

fn paired_substitution_terms_trace(
    weights: &[LinExpr],
    refs: &crate::acceptance::trace::paired_merkle_update::PairedMerkleUpdateRefs,
    region: usize,
) -> Vec<RelationTermTrace> {
    let mut terms = Vec::new();
    let mut push = |coefficient: LinExpr, mut factors: Vec<ColRef>| {
        if !factors
            .iter()
            .any(|factor| matches!(factor, ColRef::Fixed(_)))
        {
            factors.insert(0, ColRef::Fixed(region));
        }
        terms.push(RelationTermTrace {
            coeff: coefficient,
            factors,
        });
    };
    for lane in 0..2 {
        let carry_shift = ColRef::CommittedShift(refs.c[lane]);
        let entry = ColRef::Committed(refs.e[lane]);
        let entry_shift = ColRef::CommittedShift(refs.e[lane]);
        let entry_shift2 = ColRef::CommittedShift2(refs.e[lane]);
        let sibling = ColRef::Committed(refs.sib[lane]);
        let sibling_shift = ColRef::CommittedShift(refs.sib[lane]);
        let direction = ColRef::Committed(refs.d);
        let direction_shift = ColRef::CommittedShift(refs.d);
        for factors in [
            vec![carry_shift],
            vec![ColRef::Fixed(refs.even), carry_shift],
            vec![ColRef::Fixed(refs.even_start), entry],
            vec![ColRef::Fixed(refs.even_start), direction, entry],
            vec![ColRef::Fixed(refs.even_nonstart), entry_shift],
            vec![ColRef::Fixed(refs.even_nonstart), direction, entry_shift],
            vec![ColRef::Fixed(refs.even), direction, sibling],
            vec![ColRef::Fixed(refs.odd), sibling_shift],
            vec![ColRef::Fixed(refs.odd), direction_shift, sibling_shift],
            vec![ColRef::Fixed(refs.odd_start), direction_shift, entry_shift],
            vec![
                ColRef::Fixed(refs.odd_nonstart),
                direction_shift,
                entry_shift2,
            ],
        ] {
            push(weights[lane].clone(), factors);
        }
    }
    for lane in 2..STATE_SIZE {
        let carry_shift = ColRef::CommittedShift(refs.c[lane]);
        for factors in [
            vec![carry_shift],
            vec![ColRef::Fixed(refs.even), carry_shift],
            vec![ColRef::Fixed(refs.iv[lane - 2])],
        ] {
            push(weights[lane].clone(), factors);
        }
    }
    terms
}

/// Trace-coefficient twin of `merkle_protocol_substitution_terms`, preserving
/// the native FF → two-permutation → paired-update category order.
fn merkle_substitution_terms_trace(
    b: &mut FieldR1csBuilder,
    families: &[MerkleProtocolFamily],
    alpha: &LinExpr,
) -> (Vec<RelationTermTrace>, Vec<LinExpr>) {
    let (weights, alpha_powers) = mds_alpha_weights(b, alpha);
    let mut terms = Vec::new();

    for family in families {
        if let MerkleProtocolFamily::FeedForward { refs, region } = family {
            for lane in 0..STATE_SIZE {
                terms.push(RelationTermTrace {
                    coeff: weights[lane].clone(),
                    factors: vec![ColRef::Fixed(*region), ColRef::CommittedShift(refs.c[lane])],
                });
            }
            let node = ColRef::Fixed(refs.node);
            for lane in 0..2 {
                let child = ColRef::Committed(refs.cr[lane]);
                let sibling = ColRef::Committed(refs.sib[lane]);
                let direction = ColRef::Committed(refs.d);
                let carry_shift = ColRef::CommittedShift(refs.c[lane]);
                for factors in [
                    vec![node, carry_shift],
                    vec![node, child],
                    vec![node, direction, child],
                    vec![node, direction, sibling],
                ] {
                    terms.push(RelationTermTrace {
                        coeff: weights[lane].clone(),
                        factors,
                    });
                }
                let capacity_lane = 2 + lane;
                let capacity_shift = ColRef::CommittedShift(refs.c[capacity_lane]);
                for factors in [
                    vec![node, capacity_shift],
                    vec![node, sibling],
                    vec![node, direction, child],
                    vec![node, direction, sibling],
                    vec![ColRef::Fixed(refs.iv[lane])],
                ] {
                    terms.push(RelationTermTrace {
                        coeff: weights[capacity_lane].clone(),
                        factors,
                    });
                }
            }
        }
    }

    for family in families {
        if let MerkleProtocolFamily::TwoPermutation { refs, region } = family {
            let region = ColRef::Fixed(*region);
            for lane in 0..2 {
                let carry_shift = ColRef::CommittedShift(refs.c[lane]);
                let carry_shift2 = ColRef::CommittedShift2(refs.c[lane]);
                let sibling = ColRef::Committed(refs.sib[lane]);
                let sibling_shift = ColRef::CommittedShift(refs.sib[lane]);
                let entry = ColRef::Committed(refs.e[lane]);
                let entry_shift = ColRef::CommittedShift(refs.e[lane]);
                let direction = ColRef::Committed(refs.d);
                let direction_shift = ColRef::CommittedShift(refs.d);
                for factors in [
                    vec![region, carry_shift],
                    vec![ColRef::Fixed(refs.evenstart), carry_shift],
                    vec![ColRef::Fixed(refs.evenns), direction, carry_shift],
                    vec![ColRef::Fixed(refs.even), direction, sibling],
                    vec![ColRef::Fixed(refs.evenstart), entry],
                    vec![ColRef::Fixed(refs.evenstart), direction, entry],
                    vec![ColRef::Fixed(refs.odd), sibling_shift],
                    vec![ColRef::Fixed(refs.odd), direction_shift, sibling_shift],
                    vec![ColRef::Fixed(refs.oddns), direction_shift, carry_shift2],
                    vec![ColRef::Fixed(refs.oddstart), direction_shift, entry_shift],
                ] {
                    terms.push(RelationTermTrace {
                        coeff: weights[lane].clone(),
                        factors,
                    });
                }
            }
            for lane in 2..STATE_SIZE {
                let carry_shift = ColRef::CommittedShift(refs.c[lane]);
                for factors in [
                    vec![region, carry_shift],
                    vec![ColRef::Fixed(refs.even), carry_shift],
                    vec![ColRef::Fixed(refs.iv[lane - 2])],
                ] {
                    terms.push(RelationTermTrace {
                        coeff: weights[lane].clone(),
                        factors,
                    });
                }
            }
        }
    }

    for family in families {
        if let MerkleProtocolFamily::PairedUpdate { refs, region } = family {
            terms.extend(paired_substitution_terms_trace(&weights, refs, *region));
        }
    }
    (terms, alpha_powers)
}

fn validate_term_refs(terms: &[RelationTerm], fixed_len: usize) -> Result<(), RegionSidecarError> {
    let valid = terms.iter().all(|term| {
        term.factors.iter().all(|reference| match reference {
            ColRef::Committed(column)
            | ColRef::CommittedShift(column)
            | ColRef::CommittedShift2(column) => *column < MERKLE_REGION_COMMITTED_COLUMNS,
            ColRef::Internal(lane) => *lane < STATE_SIZE,
            ColRef::Fixed(pattern) => *pattern < fixed_len,
            ColRef::Window { .. } => false,
        })
    });
    if valid {
        Ok(())
    } else {
        Err(RegionSidecarError::InvalidProof)
    }
}

fn trace_term_factors_match(trace: &[RelationTermTrace], native: &[RelationTerm]) -> bool {
    trace.len() == native.len()
        && trace
            .iter()
            .zip(native)
            .all(|(trace_term, native_term)| trace_term.factors == native_term.factors)
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

/// Allocation-free shape gate for serialized Walk-B authority.
pub(crate) fn preflight_merkle_authority(
    w_log: usize,
    fixed: &[FixedPattern],
    carry_columns: &[usize; STATE_SIZE],
    families: &[MerkleProtocolFamily],
    proof: &MerkleUnionProof,
) -> Result<(), RegionSidecarError> {
    preflight_merkle_deferred_authority(
        w_log,
        fixed,
        carry_columns,
        families,
        proof.walk_deferred(),
    )?;
    if proof.walk.layers.len() != N_ROUNDS
        || proof
            .walk
            .layers
            .iter()
            .any(|layer| layer.round_coeffs.len() != w_log)
    {
        return Err(RegionSidecarError::InvalidProof);
    }
    Ok(())
}

/// Allocation-free shape gate for Walk-B authority whose walk is serialized
/// and verified by an enclosing protocol.
fn preflight_merkle_deferred_authority(
    w_log: usize,
    fixed: &[FixedPattern],
    carry_columns: &[usize; STATE_SIZE],
    families: &[MerkleProtocolFamily],
    proof: MerkleUnionWalkDeferredProofRef<'_>,
) -> Result<(), RegionSidecarError> {
    if w_log == 0 || w_log >= usize::BITS as usize || families.is_empty() || families.len() > 64 {
        return Err(RegionSidecarError::InvalidProof);
    }
    let zero_terms = merkle_protocol_zero_terms(families, F128::ONE);
    let selection_terms = carry_selection_terms(carry_columns, F128::ONE);
    let substitution_terms = merkle_protocol_substitution_terms(families, F128::ONE);
    validate_term_refs(&zero_terms, fixed.len())?;
    validate_term_refs(&selection_terms, fixed.len())?;
    validate_term_refs(&substitution_terms, fixed.len())?;
    let zero_refs = claimed_refs(&zero_terms);
    let selection_refs = claimed_refs(&selection_terms);
    let substitution_refs = claimed_refs(&substitution_terms);
    if proof.zero.rounds.len() != w_log
        || proof.zero.final_values.len() != zero_refs.len()
        || proof.zero_shifts.len() != shift_count(&zero_refs)
        || proof.selection.rounds.len() != w_log
        || proof.selection.final_values.len() != selection_refs.len()
        || shift_count(&selection_refs) != 0
        || proof.substitution.rounds.len() != w_log
        || proof.substitution.final_values.len() != substitution_refs.len()
        || proof.shifts.len() != shift_count(&substitution_refs)
        || proof
            .zero_shifts
            .iter()
            .chain(proof.shifts.iter())
            .any(|shift| shift.rounds.len() != w_log)
    {
        return Err(RegionSidecarError::InvalidProof);
    }
    Ok(())
}

fn verify_claim_pass_trace<C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    channel: &mut C,
    w_log: usize,
    references: &[ColRef],
    values: &[LinExpr],
    point: &[LinExpr],
    native_shifts: &[noid_ivc_core::deep_chain::relations::ShiftDischargeProof],
) -> Result<([LinExpr; STATE_SIZE], Vec<MerkleColumnClaimTrace>), RegionSidecarError> {
    if references.len() != values.len() {
        return Err(RegionSidecarError::InvalidProof);
    }
    let mut internal = std::array::from_fn(|_| LinExpr::zero());
    let mut terminal = Vec::new();
    let mut shift_cursor = 0usize;
    for (reference, value) in references.iter().zip(values) {
        match reference {
            ColRef::Committed(column) if *column < MERKLE_REGION_COMMITTED_COLUMNS => {
                terminal.push(MerkleColumnClaimTrace {
                    column: *column,
                    point: point.to_vec(),
                    value: value.clone(),
                });
            }
            ColRef::Internal(lane) if *lane < STATE_SIZE => internal[*lane] = value.clone(),
            ColRef::CommittedShift(column) | ColRef::CommittedShift2(column)
                if *column < MERKLE_REGION_COMMITTED_COLUMNS =>
            {
                let native = native_shifts
                    .get(shift_cursor)
                    .ok_or(RegionSidecarError::InvalidProof)?;
                shift_cursor += 1;
                let shift = ShiftDischargeProofTrace::alloc(b, native, w_log);
                let shift_log = usize::from(matches!(reference, ColRef::CommittedShift2(_)));
                let shifted_point = verify_shift_discharge_trace(
                    b, channel, w_log, point, value, shift_log, &shift,
                );
                terminal.push(MerkleColumnClaimTrace {
                    column: *column,
                    point: shifted_point,
                    value: shift.final_value,
                });
            }
            _ => return Err(RegionSidecarError::InvalidProof),
        }
    }
    if shift_cursor != native_shifts.len() {
        return Err(RegionSidecarError::InvalidProof);
    }
    Ok((internal, terminal))
}

/// Replay Walk-B's zero and carry-selection phases and stop before any walk
/// proof is allocated or observed.
#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_merkle_union_walk_prefix_trace<'a, C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    channel: &mut C,
    w_log: usize,
    fixed: &[FixedPattern],
    carry_columns: &[usize; STATE_SIZE],
    families: &[MerkleProtocolFamily],
    proof: MerkleUnionWalkDeferredProofRef<'a>,
) -> Result<MerkleUnionTraceWalkPrefix<'a>, RegionSidecarError> {
    preflight_merkle_deferred_authority(w_log, fixed, carry_columns, families, proof)?;

    let lambda = channel.sample_f128(b);
    let zero_native_terms = merkle_protocol_zero_terms(families, F128::ONE);
    let zero_terms = merkle_zero_terms_trace(b, families, &lambda);
    if !trace_term_factors_match(&zero_terms, &zero_native_terms) {
        return Err(RegionSidecarError::InvalidProof);
    }
    let zero_refs = claimed_refs(&zero_native_terms);
    let zero_rho = channel.sample_f128_vec(b, w_log);
    let zero = ColumnRelationProofTrace::alloc(b, proof.zero, w_log, zero_refs.len());
    let zero_point = verify_column_relation_trace(
        b,
        channel,
        w_log,
        &LinExpr::zero(),
        &zero_rho,
        &zero_terms,
        fixed,
        &zero,
    );
    let (_, mut terminal_claims) = verify_claim_pass_trace(
        b,
        channel,
        w_log,
        &zero_refs,
        &zero.final_values,
        &zero_point,
        proof.zero_shifts,
    )?;

    let beta = channel.sample_f128(b);
    let mut beta_power = LinExpr::constant(F128::ONE);
    let mut selection_terms = Vec::with_capacity(2 * STATE_SIZE);
    for lane in 0..STATE_SIZE {
        beta_power = mul(b, &beta_power, &beta);
        selection_terms.push(RelationTermTrace {
            coeff: beta_power.clone(),
            factors: vec![ColRef::Committed(carry_columns[lane])],
        });
        selection_terms.push(RelationTermTrace {
            coeff: beta_power.clone(),
            factors: vec![ColRef::Internal(lane)],
        });
    }
    let selection_refs = claimed_refs(&carry_selection_terms(carry_columns, F128::ONE));
    let selection_rho = channel.sample_f128_vec(b, w_log);
    let selection =
        ColumnRelationProofTrace::alloc(b, proof.selection, w_log, selection_refs.len());
    let selection_point = verify_column_relation_trace(
        b,
        channel,
        w_log,
        &LinExpr::zero(),
        &selection_rho,
        &selection_terms,
        fixed,
        &selection,
    );
    let (output_values, selection_terminal) = verify_claim_pass_trace(
        b,
        channel,
        w_log,
        &selection_refs,
        &selection.final_values,
        &selection_point,
        &[],
    )?;
    terminal_claims.extend(selection_terminal);

    Ok(MerkleUnionTraceWalkPrefix {
        proof,
        terminal_claims,
        walk_group: LaneClaimGroupTrace {
            point: selection_point,
            values: output_values,
        },
    })
}

/// Resume Walk-B after an externally verified walk terminal and replay its
/// substitution and shift-discharge suffix.
pub(crate) fn verify_merkle_union_walk_suffix_trace<C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    channel: &mut C,
    w_log: usize,
    fixed: &[FixedPattern],
    families: &[MerkleProtocolFamily],
    prefix: MerkleUnionTraceWalkPrefix<'_>,
    walk_terminal: &LaneClaimGroupTrace,
) -> Result<Vec<MerkleColumnClaimTrace>, RegionSidecarError> {
    if walk_terminal.point.len() != w_log {
        return Err(RegionSidecarError::InvalidProof);
    }
    let MerkleUnionTraceWalkPrefix {
        proof,
        mut terminal_claims,
        walk_group: _,
    } = prefix;

    let alpha = channel.sample_f128(b);
    let substitution_native_terms = merkle_protocol_substitution_terms(families, F128::ONE);
    let substitution_refs = claimed_refs(&substitution_native_terms);
    let (substitution_terms, alpha_powers) = merkle_substitution_terms_trace(b, families, &alpha);
    if !trace_term_factors_match(&substitution_terms, &substitution_native_terms) {
        return Err(RegionSidecarError::InvalidProof);
    }
    let mut target = LinExpr::zero();
    for lane in 0..STATE_SIZE {
        target = target.add(&mul(b, &alpha_powers[lane], &walk_terminal.values[lane]));
    }
    let substitution =
        ColumnRelationProofTrace::alloc(b, proof.substitution, w_log, substitution_refs.len());
    let substitution_point = verify_column_relation_trace(
        b,
        channel,
        w_log,
        &target,
        &walk_terminal.point,
        &substitution_terms,
        fixed,
        &substitution,
    );
    let (_, substitution_terminal) = verify_claim_pass_trace(
        b,
        channel,
        w_log,
        &substitution_refs,
        &substitution.final_values,
        &substitution_point,
        proof.shifts,
    )?;
    terminal_claims.extend(substitution_terminal);
    Ok(terminal_claims)
}

/// Generic recursive replay of one canonical Walk-B authority on the caller's
/// exact channel. It neither constructs a challenger nor accepts pending PCS
/// descriptors.
pub(crate) fn verify_merkle_union_proof_trace<C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    channel: &mut C,
    w_log: usize,
    fixed: &[FixedPattern],
    carry_columns: &[usize; STATE_SIZE],
    families: &[MerkleProtocolFamily],
    proof: &MerkleUnionProof,
) -> Result<Vec<MerkleColumnClaimTrace>, RegionSidecarError> {
    preflight_merkle_authority(w_log, fixed, carry_columns, families, proof)?;
    let prefix = verify_merkle_union_walk_prefix_trace(
        b,
        channel,
        w_log,
        fixed,
        carry_columns,
        families,
        proof.walk_deferred(),
    )?;
    let groups = vec![prefix.walk_group().clone()];
    let walk = DeepChainWalkProofTrace::alloc(b, &proof.walk, w_log);
    let walk_terminal = verify_deep_chain_walk_trace(b, channel, w_log, &groups, &walk);
    verify_merkle_union_walk_suffix_trace(
        b,
        channel,
        w_log,
        fixed,
        families,
        prefix,
        &walk_terminal,
    )
}

fn resolve_merkle_terminal_claims_trace(
    vk: &MerkleRegionVk,
    total_vars: usize,
    terminal: Vec<MerkleColumnClaimTrace>,
) -> Result<Vec<QuirkyDirectClaimTrace>, RegionSidecarError> {
    terminal
        .into_iter()
        .map(|claim| {
            let slice = *vk
                .slices
                .get(claim.column)
                .ok_or(RegionSidecarError::InvalidProof)?;
            if claim.point.len() != slice.log2_len {
                return Err(RegionSidecarError::InvalidProof);
            }
            let mut x_rest = claim.point;
            x_rest.extend(
                slice
                    .prefix_coords(total_vars)
                    .into_iter()
                    .map(LinExpr::constant),
            );
            Ok(QuirkyDirectClaimTrace {
                z_skip: LinExpr::zero(),
                k_skip: 0,
                x_rest,
                value: claim.value,
            })
        })
        .collect()
}

pub(crate) fn preflight_merkle_sidecar_trace(
    vk: &MerkleRegionVk,
    total_vars: usize,
    proof: &MerkleRegionSidecarProof,
) -> Result<Vec<MerkleProtocolFamily>, RegionSidecarError> {
    vk.validate_in_witness(total_vars)?;
    if proof.version != MERKLE_REGION_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    let families = vk.protocol_families();
    preflight_merkle_authority(
        vk.w_log,
        &vk.fixed,
        &[0, 1, 2, 3],
        &families,
        &proof.authority,
    )?;
    Ok(families)
}

/// Verify and append one canonical recording-free Walk-B sidecar inside an
/// already post-commit recursive trace context.
pub fn verify_merkle_region_sidecar_trace_post_commit<C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    context: &mut FieldPostCommitTraceContext<'_, C>,
    vk: &MerkleRegionVk,
    proof: &MerkleRegionSidecarProof,
) -> Result<(), RegionSidecarError> {
    let total_vars = context.total_vars();
    let families = preflight_merkle_sidecar_trace(vk, total_vars, proof)?;
    context.observe_label(b, MERKLE_SIDECAR_TRANSCRIPT_LABEL);
    crate::acceptance::trace::self_verify::observe_pinned_digest(
        b,
        context,
        &vk.transcript_digest(),
    );
    let terminal = verify_merkle_union_proof_trace(
        b,
        context,
        vk.w_log,
        &vk.fixed,
        &[0, 1, 2, 3],
        &families,
        &proof.authority,
    )?;
    let claims = resolve_merkle_terminal_claims_trace(vk, total_vars, terminal)?;
    context.append_claims(claims);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::trace::region_source_binding::{
        common_period_ones, prove_merkle_union_with_challenger, verify_merkle_union_with_challenger,
    };
    use noid_ivc_core::challenger::{Challenger, FsLaneChallenger};
    use noid_ivc_core::deep_chain::ff_merkle::{
        build_ff_merkle_path_columns, ff_merkle_fixed_patterns, FfMerklePathFamily,
        FfMerklePathWitness,
    };
    use noid_ivc_core::field_circuit::FsChannelTrace;

    #[test]
    fn merkle_trace_term_order_matches_all_native_categories() {
        // Deliberately interleave the physical descriptor order. Both native
        // and trace relations must regroup by protocol category.
        let families = [
            MerkleProtocolFamily::paired_update(0),
            MerkleProtocolFamily::feed_forward(12),
            MerkleProtocolFamily::two_permutation(18),
        ];
        let mut builder = FieldR1csBuilder::new();
        let lambda_value = F128::new(7, 11);
        let lambda = LinExpr::from_wire(builder.alloc_f128(lambda_value));
        let zero_trace = merkle_zero_terms_trace(&mut builder, &families, &lambda);
        let zero_native = merkle_protocol_zero_terms(&families, lambda_value);
        assert!(trace_term_factors_match(&zero_trace, &zero_native));
        for (trace, native) in zero_trace.iter().zip(&zero_native) {
            assert_eq!(trace.coeff.eval(builder.values()), native.coeff);
        }

        let alpha_value = F128::new(13, 17);
        let alpha = LinExpr::from_wire(builder.alloc_f128(alpha_value));
        let (substitution_trace, _) =
            merkle_substitution_terms_trace(&mut builder, &families, &alpha);
        let substitution_native = merkle_protocol_substitution_terms(&families, alpha_value);
        assert!(trace_term_factors_match(
            &substitution_trace,
            &substitution_native
        ));
        for (trace, native) in substitution_trace.iter().zip(&substitution_native) {
            assert_eq!(trace.coeff.eval(builder.values()), native.coeff);
        }
    }

    #[test]
    fn merkle_ff_authority_native_trace_lockstep_and_malformed_negatives() {
        const DOMAIN: &[u8] = b"merkle-ff-authority-native-trace-v1";
        let w_log = 2;
        let iv = [F128::new(0x1357, 0x2468), F128::new(0x3579, 0x468a)];
        let family = FfMerklePathFamily {
            depth: 3,
            n_paths: 1,
        };
        let columns = build_ff_merkle_path_columns(
            &family,
            iv,
            &[FfMerklePathWitness {
                entry: [F128::new(3, 5), F128::new(7, 11)],
                siblings: vec![
                    [F128::new(13, 17), F128::new(19, 23)],
                    [F128::new(29, 31), F128::new(37, 41)],
                    [F128::new(43, 47), F128::new(53, 59)],
                ],
                directions: vec![false, true, false],
            }],
            w_log,
        );
        let committed_owned = vec![
            columns.c[0].clone(),
            columns.c[1].clone(),
            columns.c[2].clone(),
            columns.c[3].clone(),
            columns.cr[0].clone(),
            columns.cr[1].clone(),
            columns.sib[0].clone(),
            columns.sib[1].clone(),
            columns.d.clone(),
        ];
        let committed = committed_owned
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>();
        let mut fixed = ff_merkle_fixed_patterns(&family, iv);
        fixed.push(common_period_ones(0, family.n_slots(), w_log));
        let families = [MerkleProtocolFamily::feed_forward(0)];
        let carry = [0, 1, 2, 3];

        let mut prover = FsLaneChallenger::new(DOMAIN);
        let (authority, prover_claims) = prove_merkle_union_with_challenger(
            w_log,
            &fixed,
            &carry,
            &families,
            &committed,
            &columns.s0,
            &columns.s_out,
            &mut prover,
        );
        let mut native = FsLaneChallenger::new(DOMAIN);
        let native_claims = verify_merkle_union_with_challenger(
            w_log,
            &fixed,
            &carry,
            &families,
            &authority,
            &mut native,
        )
        .unwrap();
        assert_eq!(prover_claims, native_claims);
        let native_next = native.sample_f128();

        let mut builder = FieldR1csBuilder::new();
        let mut trace = FsChannelTrace::new(&mut builder, DOMAIN);
        let trace_claims = verify_merkle_union_proof_trace(
            &mut builder,
            &mut trace,
            w_log,
            &fixed,
            &carry,
            &families,
            &authority,
        )
        .unwrap();
        assert_eq!(trace_claims.len(), native_claims.len());
        for (trace_claim, native_claim) in trace_claims.iter().zip(&native_claims) {
            assert_eq!(trace_claim.column, native_claim.column);
            assert_eq!(
                trace_claim
                    .point
                    .iter()
                    .map(|coordinate| coordinate.eval(builder.values()))
                    .collect::<Vec<_>>(),
                native_claim.point
            );
            assert_eq!(trace_claim.value.eval(builder.values()), native_claim.value);
        }
        let trace_next = trace.sample_f128(&mut builder);
        assert_eq!(trace_next.eval(builder.values()), native_next);
        let (r1cs, witness) = builder.build();
        assert!(r1cs.satisfies(&witness));

        let mut bad_authority = authority.clone();
        bad_authority.zero.rounds[0][0] += F128::ONE;
        let mut builder = FieldR1csBuilder::new();
        let mut trace = FsChannelTrace::new(&mut builder, DOMAIN);
        verify_merkle_union_proof_trace(
            &mut builder,
            &mut trace,
            w_log,
            &fixed,
            &carry,
            &families,
            &bad_authority,
        )
        .unwrap();
        let (r1cs, witness) = builder.build();
        assert!(!r1cs.satisfies(&witness), "proof mutation satisfied trace");

        let mut missing_shift = authority.clone();
        assert!(!missing_shift.shifts.is_empty());
        missing_shift.shifts.pop();
        assert_eq!(
            preflight_merkle_authority(w_log, &fixed, &carry, &families, &missing_shift),
            Err(RegionSidecarError::InvalidProof)
        );
        let mut malformed_walk = authority;
        malformed_walk.walk.layers.pop();
        assert_eq!(
            preflight_merkle_authority(w_log, &fixed, &carry, &families, &malformed_walk),
            Err(RegionSidecarError::InvalidProof)
        );
    }
}
