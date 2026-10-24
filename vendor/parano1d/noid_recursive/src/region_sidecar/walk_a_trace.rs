// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Recursive trace replay for recording-free Walk-A sidecars.

use noid_ivc_core::deep_chain::flat_mds;
use noid_ivc_core::deep_chain::relations::{claimed_refs, ColRef};
use noid_ivc_core::deep_chain::schedule::carry_selection_terms;
use noid_ivc_core::deep_chain::spine::spine_tree_exposure_terms;
use noid_ivc_core::field_circuit::FsChannelOps;
use noid_poseidon2b::native::permutation::{N_ROUNDS, STATE_SIZE};

use crate::acceptance::trace::deep_chain::{
    verify_column_relation_trace, verify_deep_chain_walk_trace, verify_shift_discharge_trace,
    C1LaneClaimGroupTrace, ColumnRelationProofTrace, DeepChainWalkProofTrace, LaneClaimGroupTrace,
    RelationTermTrace, ShiftDischargeProofTrace,
};
use crate::acceptance::trace::region_source_binding::{
    union_ref_terms, union_trace_terms, WalkAUnionWalkDeferredProofRef,
};
use crate::acceptance::trace::region_source_binding_c1::{
    verify_c1_walk_a_walk_prefix_trace, verify_c1_walk_a_walk_suffix_trace,
    C1WalkAColumnClaimTrace, C1WalkAUnionTraceWalkPrefix,
};
use crate::acceptance::trace::self_verify::{
    C1QuirkyDirectClaimTrace, FieldPostCommitTraceContext, QuirkyDirectClaimTrace,
};
use crate::acceptance::trace::{mul, ExtExpr, FieldR1csBuilder, LinExpr};

use super::*;

pub(crate) struct C1WalkARegionTraceWalkContinuation<'a> {
    vk: &'a WalkARegionVk,
    total_vars: usize,
    protocol: std::sync::Arc<CanonicalWalkAProtocol>,
    prefix: C1WalkAUnionTraceWalkPrefix<'a>,
}

impl C1WalkARegionTraceWalkContinuation<'_> {
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
        let terminal = verify_c1_walk_a_walk_suffix_trace(
            b,
            context,
            self.protocol.w_log,
            &self.protocol.fixed,
            &self.protocol.meta_c,
            &self.protocol.leaf_refs,
            &self.protocol.split_tails,
            self.protocol.es_sponge.as_ref(),
            self.protocol.spine.as_ref(),
            self.prefix,
            walk_terminal,
        )?;
        resolve_c1_walk_a_terminal_claims_trace(self.vk, self.total_vars, terminal)
    }
}

pub(crate) fn verify_c1_walk_a_region_walk_deferred_prefix_trace<'a, C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    context: &mut FieldPostCommitTraceContext<'_, C>,
    vk: &'a WalkARegionVk,
    proof: &'a C1WalkARegionWalkDeferredProof,
) -> Result<C1WalkARegionTraceWalkContinuation<'a>, RegionSidecarError> {
    let total_vars = context.total_vars();
    let protocol = vk.certified_c1_protocol_in_witness(total_vars)?;
    if proof.version() != WALK_A_REGION_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    context.observe_label(b, WALK_A_SIDECAR_TRANSCRIPT_LABEL);
    crate::acceptance::trace::self_verify::observe_pinned_digest(
        b,
        context,
        &vk.transcript_digest(),
    );
    let prefix = verify_c1_walk_a_walk_prefix_trace(
        b,
        context,
        protocol.w_log,
        &protocol.fixed,
        &protocol.meta_c,
        proof.authority().as_ref(),
    )?;
    Ok(C1WalkARegionTraceWalkContinuation {
        vk,
        total_vars,
        protocol,
        prefix,
    })
}

fn resolve_c1_walk_a_terminal_claims_trace(
    vk: &WalkARegionVk,
    total_vars: usize,
    terminal: Vec<C1WalkAColumnClaimTrace>,
) -> Result<Vec<C1QuirkyDirectClaimTrace>, RegionSidecarError> {
    terminal
        .into_iter()
        .map(|claim| {
            let slice = *vk
                .slices()
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
                    .map(|value| ExtExpr::constant(F256::from_base(value))),
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

/// A verifier-derived Walk-A terminal opening. This is transient trace state,
/// never serialized proof authority.
pub(super) struct WalkAColumnClaimTrace {
    pub(super) column: usize,
    pub(super) point: Vec<LinExpr>,
    pub(super) value: LinExpr,
}

/// Trace typestate after Walk-A carry selection and before a caller-owned
/// deep-chain walk. The deferred authority is retained so the suffix cannot
/// accidentally be paired with a different proof.
pub(super) struct WalkAUnionTraceWalkPrefix<'a> {
    proof: WalkAUnionWalkDeferredProofRef<'a>,
    terminal_claims: Vec<WalkAColumnClaimTrace>,
    walk_group: LaneClaimGroupTrace,
}

impl WalkAUnionTraceWalkPrefix<'_> {
    pub(super) fn walk_group(&self) -> &LaneClaimGroupTrace {
        &self.walk_group
    }
}

/// Replay Walk-A through carry selection and stop before any walk messages
/// are allocated or observed.
pub(super) fn verify_walk_a_union_walk_prefix_trace<'a, C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    channel: &mut C,
    protocol: &CanonicalWalkAProtocol,
    proof: WalkAUnionWalkDeferredProofRef<'a>,
) -> Result<WalkAUnionTraceWalkPrefix<'a>, RegionSidecarError> {
    preflight_walk_a_deferred_authority(protocol, proof)?;

    let w_log = protocol.w_log;
    let beta = channel.sample_f128(b);
    let mut beta_power = LinExpr::constant(F128::ONE);
    let mut selection_terms = Vec::with_capacity(2 * STATE_SIZE);
    for lane in 0..STATE_SIZE {
        beta_power = mul(b, &beta_power, &beta);
        selection_terms.push(RelationTermTrace {
            coeff: beta_power.clone(),
            factors: vec![ColRef::Committed(protocol.meta_c[lane])],
        });
        selection_terms.push(RelationTermTrace {
            coeff: beta_power.clone(),
            factors: vec![ColRef::Internal(lane)],
        });
    }
    let selection_refs = claimed_refs(&carry_selection_terms(&protocol.meta_c, F128::ONE));
    let rho = channel.sample_f128_vec(b, w_log);
    let selection =
        ColumnRelationProofTrace::alloc(b, proof.selection, w_log, selection_refs.len());
    let selection_point = verify_column_relation_trace(
        b,
        channel,
        w_log,
        &LinExpr::zero(),
        &rho,
        &selection_terms,
        &protocol.fixed,
        &selection,
    );
    let mut terminal_claims = Vec::new();
    let mut output_values: [LinExpr; STATE_SIZE] = std::array::from_fn(|_| LinExpr::zero());
    for (reference, value) in selection_refs.iter().zip(&selection.final_values) {
        match reference {
            ColRef::Committed(column) => terminal_claims.push(WalkAColumnClaimTrace {
                column: *column,
                point: selection_point.clone(),
                value: value.clone(),
            }),
            ColRef::Internal(lane) if *lane < STATE_SIZE => {
                output_values[*lane] = value.clone();
            }
            _ => return Err(RegionSidecarError::InvalidProof),
        }
    }

    Ok(WalkAUnionTraceWalkPrefix {
        proof,
        terminal_claims,
        walk_group: LaneClaimGroupTrace {
            point: selection_point,
            values: output_values,
        },
    })
}

/// Resume Walk-A after a caller-owned walk and verify substitution, shift
/// discharges and the optional spine exposure against its terminal claim.
pub(super) fn verify_walk_a_union_walk_suffix_trace<C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    channel: &mut C,
    protocol: &CanonicalWalkAProtocol,
    prefix: WalkAUnionTraceWalkPrefix<'_>,
    walk_terminal: &LaneClaimGroupTrace,
) -> Result<Vec<WalkAColumnClaimTrace>, RegionSidecarError> {
    let w_log = protocol.w_log;
    if walk_terminal.point.len() != w_log {
        return Err(RegionSidecarError::InvalidProof);
    }
    let WalkAUnionTraceWalkPrefix {
        proof,
        mut terminal_claims,
        walk_group: _,
    } = prefix;
    let zero = LinExpr::zero();

    let alpha = channel.sample_f128(b);
    let (mds_weights, alpha_powers) = mds_alpha_weights_trace(b, &alpha);
    let substitution_terms = union_trace_terms(
        &mds_weights,
        &protocol.leaf_refs,
        &protocol.split_tails,
        protocol.es_sponge.as_ref(),
        protocol.spine.as_ref(),
    );
    let substitution_ref_terms = union_ref_terms(
        &protocol.leaf_refs,
        &protocol.split_tails,
        protocol.es_sponge.as_ref(),
        protocol.spine.as_ref(),
    );
    let substitution_refs = claimed_refs(&substitution_ref_terms);
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
        &protocol.fixed,
        &substitution,
    );

    let mut shift_cursor = 0usize;
    for (reference, value) in substitution_refs.iter().zip(&substitution.final_values) {
        match reference {
            ColRef::Committed(column) => terminal_claims.push(WalkAColumnClaimTrace {
                column: *column,
                point: substitution_point.clone(),
                value: value.clone(),
            }),
            ColRef::CommittedShift(column) | ColRef::CommittedShift2(column) => {
                let shift_log = usize::from(matches!(reference, ColRef::CommittedShift2(_)));
                let native_shift = proof
                    .shifts
                    .get(shift_cursor)
                    .ok_or(RegionSidecarError::InvalidProof)?;
                shift_cursor += 1;
                let shift = ShiftDischargeProofTrace::alloc(b, native_shift, w_log);
                let point = verify_shift_discharge_trace(
                    b,
                    channel,
                    w_log,
                    &substitution_point,
                    value,
                    shift_log,
                    &shift,
                );
                terminal_claims.push(WalkAColumnClaimTrace {
                    column: *column,
                    point,
                    value: shift.final_value,
                });
            }
            _ => return Err(RegionSidecarError::InvalidProof),
        }
    }
    if shift_cursor != proof.shifts.len() {
        return Err(RegionSidecarError::InvalidProof);
    }

    if let (Some(spec), Some(native_exposure)) = (protocol.spine.as_ref(), proof.spine_exposure) {
        let gamma = channel.sample_f128(b);
        let mut gamma_power = LinExpr::constant(F128::ONE);
        let mut exposure_terms = Vec::with_capacity(4);
        for lane in 0..2 {
            gamma_power = mul(b, &gamma_power, &gamma);
            exposure_terms.push(RelationTermTrace {
                coeff: gamma_power.clone(),
                factors: vec![ColRef::Fixed(0), ColRef::Committed(lane)],
            });
            exposure_terms.push(RelationTermTrace {
                coeff: gamma_power.clone(),
                factors: vec![
                    ColRef::Fixed(0),
                    ColRef::Window {
                        col: 2 + lane,
                        stride_log: 1,
                        offset: 1,
                    },
                ],
            });
        }
        let exposure_ref_terms = spine_tree_exposure_terms([0, 1], [2, 3], 0, F128::ONE);
        let exposure_refs = claimed_refs(&exposure_ref_terms);
        let exposure_fixed = vec![spec.gate_pattern()];
        let exposure_log = spec.expo_wlog();
        let rho = channel.sample_f128_vec(b, exposure_log);
        let exposure =
            ColumnRelationProofTrace::alloc(b, native_exposure, exposure_log, exposure_refs.len());
        let exposure_point = verify_column_relation_trace(
            b,
            channel,
            exposure_log,
            &zero,
            &rho,
            &exposure_terms,
            &exposure_fixed,
            &exposure,
        );
        for (reference, value) in exposure_refs.iter().zip(&exposure.final_values) {
            let (column, point) = match reference {
                ColRef::Committed(local_column) if *local_column < 2 => (
                    spec.kid_meta[*local_column],
                    repoint_spine_trace(spec, &exposure_point, false),
                ),
                ColRef::Window {
                    col,
                    stride_log: 1,
                    offset: 1,
                } if (2..4).contains(col) => (
                    spec.c_meta[*col - 2],
                    repoint_spine_trace(spec, &exposure_point, true),
                ),
                _ => return Err(RegionSidecarError::InvalidProof),
            };
            if point.len() != w_log {
                return Err(RegionSidecarError::InvalidProof);
            }
            terminal_claims.push(WalkAColumnClaimTrace {
                column,
                point,
                value: value.clone(),
            });
        }
    }

    Ok(terminal_claims)
}

/// Replay the standalone Walk-A authority, including its embedded walk.
pub(super) fn verify_walk_a_union_proof_trace<C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    channel: &mut C,
    protocol: &CanonicalWalkAProtocol,
    proof: &WalkAUnionProof,
) -> Result<Vec<WalkAColumnClaimTrace>, RegionSidecarError> {
    preflight_walk_a_authority(protocol, proof)?;
    let prefix =
        verify_walk_a_union_walk_prefix_trace(b, channel, protocol, proof.walk_deferred())?;
    let walk_groups = vec![prefix.walk_group().clone()];
    let walk = DeepChainWalkProofTrace::alloc(b, &proof.walk, protocol.w_log);
    let walk_terminal =
        verify_deep_chain_walk_trace(b, channel, protocol.w_log, &walk_groups, &walk);
    verify_walk_a_union_walk_suffix_trace(b, channel, protocol, prefix, &walk_terminal)
}

fn resolve_walk_a_terminal_claims_trace(
    vk: &WalkARegionVk,
    total_vars: usize,
    terminal: Vec<WalkAColumnClaimTrace>,
) -> Result<Vec<QuirkyDirectClaimTrace>, RegionSidecarError> {
    terminal
        .into_iter()
        .map(|claim| {
            let slice = *vk
                .slices()
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

/// Verify and append one Walk-A V1 sidecar inside an already post-commit
/// recursive trace context. No fresh challenger or IO-tail authority exists.
pub fn verify_walk_a_region_sidecar_trace_post_commit<C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    context: &mut FieldPostCommitTraceContext<'_, C>,
    vk: &WalkARegionVk,
    proof: &WalkARegionSidecarProof,
) -> Result<(), RegionSidecarError> {
    let total_vars = context.total_vars();
    preflight_walk_a_sidecar_trace(vk, total_vars, proof)?;
    let protocol = vk.validate_in_witness(total_vars)?;

    context.observe_label(b, WALK_A_SIDECAR_TRANSCRIPT_LABEL);
    crate::acceptance::trace::self_verify::observe_pinned_digest(
        b,
        context,
        &vk.transcript_digest(),
    );
    let terminal = verify_walk_a_union_proof_trace(b, context, &protocol, &proof.authority)?;
    let claims = resolve_walk_a_terminal_claims_trace(vk, total_vars, terminal)?;
    context.append_claims(claims);
    Ok(())
}

pub(crate) fn preflight_walk_a_sidecar_trace(
    vk: &WalkARegionVk,
    total_vars: usize,
    proof: &WalkARegionSidecarProof,
) -> Result<(), RegionSidecarError> {
    let protocol = vk.validate_in_witness(total_vars)?;
    if proof.version != WALK_A_REGION_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    preflight_walk_a_authority(&protocol, &proof.authority)
}

pub(super) fn preflight_walk_a_authority(
    protocol: &CanonicalWalkAProtocol,
    proof: &WalkAUnionProof,
) -> Result<(), RegionSidecarError> {
    preflight_walk_a_deferred_authority(protocol, proof.walk_deferred())?;
    if proof.walk.layers.len() != N_ROUNDS
        || proof
            .walk
            .layers
            .iter()
            .any(|layer| layer.round_coeffs.len() != protocol.w_log)
    {
        return Err(RegionSidecarError::InvalidProof);
    }
    Ok(())
}

/// Allocation-free shape gate for Walk-A authority whose walk is owned by
/// the enclosing protocol.
fn preflight_walk_a_deferred_authority(
    protocol: &CanonicalWalkAProtocol,
    proof: WalkAUnionWalkDeferredProofRef<'_>,
) -> Result<(), RegionSidecarError> {
    let w_log = protocol.w_log;
    let selection_values = claimed_refs(&carry_selection_terms(&protocol.meta_c, F128::ONE)).len();
    let substitution_refs = claimed_refs(&union_ref_terms(
        &protocol.leaf_refs,
        &protocol.split_tails,
        protocol.es_sponge.as_ref(),
        protocol.spine.as_ref(),
    ));
    let shift_logs = substitution_refs
        .iter()
        .filter_map(|reference| match reference {
            ColRef::CommittedShift(_) => Some(0usize),
            ColRef::CommittedShift2(_) => Some(1usize),
            _ => None,
        });
    let mut shift_count = 0usize;
    for shift_log in shift_logs {
        if shift_log >= w_log {
            return Err(RegionSidecarError::InvalidProof);
        }
        shift_count += 1;
    }

    let relation_shape = |rounds: usize, values: usize, expected_values: usize| {
        rounds == w_log && values == expected_values
    };
    if !relation_shape(
        proof.selection.rounds.len(),
        proof.selection.final_values.len(),
        selection_values,
    ) || !relation_shape(
        proof.substitution.rounds.len(),
        proof.substitution.final_values.len(),
        substitution_refs.len(),
    ) || proof.shifts.len() != shift_count
        || proof.shifts.iter().any(|shift| shift.rounds.len() != w_log)
    {
        return Err(RegionSidecarError::InvalidProof);
    }

    match (protocol.spine.as_ref(), proof.spine_exposure) {
        (None, None) => {}
        (Some(spec), Some(exposure)) => {
            let exposure_values =
                claimed_refs(&spine_tree_exposure_terms([0, 1], [2, 3], 0, F128::ONE)).len();
            if exposure.rounds.len() != spec.expo_wlog()
                || exposure.final_values.len() != exposure_values
            {
                return Err(RegionSidecarError::InvalidProof);
            }
        }
        _ => return Err(RegionSidecarError::InvalidProof),
    }
    Ok(())
}

fn mds_alpha_weights_trace(
    b: &mut FieldR1csBuilder,
    alpha: &LinExpr,
) -> (Vec<LinExpr>, Vec<LinExpr>) {
    let mut alpha_powers = Vec::with_capacity(STATE_SIZE);
    let mut power = LinExpr::constant(F128::ONE);
    for _ in 0..STATE_SIZE {
        power = mul(b, &power, alpha);
        alpha_powers.push(power.clone());
    }
    let matrix = flat_mds(true);
    let weights = (0..STATE_SIZE)
        .map(|column| {
            let mut weight = LinExpr::zero();
            for row in 0..STATE_SIZE {
                weight = weight.add(&alpha_powers[row].scale(matrix[row][column]));
            }
            weight
        })
        .collect();
    (weights, alpha_powers)
}

fn repoint_spine_trace(
    spec: &SpineUnionSpec,
    exposure_point: &[LinExpr],
    c_window: bool,
) -> Vec<LinExpr> {
    let (rho_local, rest) = exposure_point.split_at(spec.local_log());
    let (rho_instance, rho_tx) = rest.split_at(spec.cap_log);
    let mut point = if c_window {
        let mut point = vec![LinExpr::constant(F128::ONE)];
        point.extend_from_slice(rho_local);
        point
    } else {
        let mut point = rho_local.to_vec();
        point.push(LinExpr::constant(F128::ZERO));
        point
    };
    point.extend_from_slice(rho_instance);
    point.extend(spec.base_bits().into_iter().map(LinExpr::constant));
    point.extend_from_slice(rho_tx);
    point.extend(spec.walk_high_bits.iter().copied().map(LinExpr::constant));
    point
}
