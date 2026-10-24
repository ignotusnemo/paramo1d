// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Recursive trace replay for recording-free duplex sidecars.

use noid_ivc_core::deep_chain::relations::{claimed_refs, ColRef, FixedPattern};
use noid_ivc_core::deep_chain::schedule::{
    carry_selection_terms, duplex_substitution_terms, DuplexFamilyRefs,
};
use noid_ivc_core::field::F128;
use noid_ivc_core::field_circuit::FsChannelOps;
use noid_poseidon2b::native::permutation::{N_ROUNDS, STATE_SIZE};

use crate::acceptance::trace::deep_chain::{
    verify_column_relation_trace, verify_deep_chain_walk_trace, verify_shift_discharge_trace,
    C1LaneClaimGroupTrace, ColumnRelationProofTrace, DeepChainWalkProofTrace, LaneClaimGroupTrace,
    RelationTermTrace, ShiftDischargeProofTrace,
};
use crate::acceptance::trace::region_source_binding::{
    duplex_sub_terms_trace, DuplexUnionProof, DuplexUnionWalkDeferredProofRef,
};
use crate::acceptance::trace::region_source_binding_c1::{
    verify_c1_duplex_walk_prefix_trace, verify_c1_duplex_walk_suffix_trace,
    C1DuplexColumnClaimTrace, C1DuplexUnionTraceWalkPrefix,
};
use crate::acceptance::trace::self_verify::{
    C1QuirkyDirectClaimTrace, FieldPostCommitTraceContext, QuirkyDirectClaimTrace,
};
use crate::acceptance::trace::{mul, ExtExpr, FieldR1csBuilder, LinExpr};

use super::{
    C1DuplexRegionWalkDeferredProof, DuplexRegionSidecarProof, DuplexRegionVk, RegionSidecarError,
    DUPLEX_REGION_SIDECAR_VERSION, DUPLEX_SIDECAR_TRANSCRIPT_LABEL,
};

pub(crate) struct C1DuplexRegionTraceWalkContinuation<'a> {
    vk: &'a DuplexRegionVk,
    total_vars: usize,
    prefix: C1DuplexUnionTraceWalkPrefix<'a>,
}

impl C1DuplexRegionTraceWalkContinuation<'_> {
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
        let terminal = verify_c1_duplex_walk_suffix_trace(
            b,
            context,
            self.vk.w_log,
            &self.vk.fixed,
            &self.vk.refs,
            &[],
            self.prefix,
            walk_terminal,
        )?;
        resolve_c1_duplex_terminal_claims_trace(self.vk, self.total_vars, terminal)
    }
}

pub(crate) fn verify_c1_duplex_region_walk_deferred_prefix_trace<'a, C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    context: &mut FieldPostCommitTraceContext<'_, C>,
    vk: &'a DuplexRegionVk,
    proof: &'a C1DuplexRegionWalkDeferredProof,
) -> Result<C1DuplexRegionTraceWalkContinuation<'a>, RegionSidecarError> {
    let total_vars = context.total_vars();
    vk.validate_in_witness(total_vars)?;
    if proof.version != DUPLEX_REGION_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    context.observe_label(b, DUPLEX_SIDECAR_TRANSCRIPT_LABEL);
    crate::acceptance::trace::self_verify::observe_pinned_digest(
        b,
        context,
        &vk.transcript_digest(),
    );
    let prefix = verify_c1_duplex_walk_prefix_trace(
        b,
        context,
        vk.w_log,
        &vk.fixed,
        &vk.refs,
        proof.authority.as_ref(),
    )?;
    Ok(C1DuplexRegionTraceWalkContinuation {
        vk,
        total_vars,
        prefix,
    })
}

fn resolve_c1_duplex_terminal_claims_trace(
    vk: &DuplexRegionVk,
    total_vars: usize,
    terminal: Vec<C1DuplexColumnClaimTrace>,
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

/// A structurally derived duplex terminal claim. It is transient trace state,
/// never serialized authority.
pub(crate) struct DuplexColumnClaimTrace {
    pub(crate) column: usize,
    pub(crate) point: Vec<LinExpr>,
    pub(crate) value: LinExpr,
}

/// Trace typestate after duplex carry selection and before the caller-owned
/// deep-chain walk. It retains the exact deferred authority consumed later by
/// the suffix.
pub(crate) struct DuplexUnionTraceWalkPrefix<'a> {
    proof: DuplexUnionWalkDeferredProofRef<'a>,
    terminal_claims: Vec<DuplexColumnClaimTrace>,
    walk_group: LaneClaimGroupTrace,
}

impl<'a> DuplexUnionTraceWalkPrefix<'a> {
    pub(crate) fn walk_group(&self) -> &LaneClaimGroupTrace {
        &self.walk_group
    }
}

/// Replay duplex carry selection without allocating or observing a walk.
pub(crate) fn verify_duplex_union_walk_prefix_trace<'a, C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    channel: &mut C,
    w_log: usize,
    fixed: &[FixedPattern],
    refs: &DuplexFamilyRefs,
    proof: DuplexUnionWalkDeferredProofRef<'a>,
) -> Result<DuplexUnionTraceWalkPrefix<'a>, RegionSidecarError> {
    preflight_duplex_deferred_authority(w_log, refs, proof)?;

    let beta = channel.sample_f128(b);
    let mut beta_power = LinExpr::constant(F128::ONE);
    let mut selection_terms = Vec::with_capacity(2 * STATE_SIZE);
    for lane in 0..STATE_SIZE {
        beta_power = mul(b, &beta_power, &beta);
        selection_terms.push(RelationTermTrace {
            coeff: beta_power.clone(),
            factors: vec![ColRef::Committed(refs.c[lane])],
        });
        selection_terms.push(RelationTermTrace {
            coeff: beta_power.clone(),
            factors: vec![ColRef::Internal(lane)],
        });
    }
    let selection_refs = claimed_refs(&carry_selection_terms(&refs.c, F128::ONE));
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
        fixed,
        &selection,
    );
    let mut terminal_claims = Vec::new();
    let mut output_values: [LinExpr; STATE_SIZE] = std::array::from_fn(|_| LinExpr::zero());
    for (reference, value) in selection_refs.iter().zip(&selection.final_values) {
        match reference {
            ColRef::Committed(column) => terminal_claims.push(DuplexColumnClaimTrace {
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

    Ok(DuplexUnionTraceWalkPrefix {
        proof,
        terminal_claims,
        walk_group: LaneClaimGroupTrace {
            point: selection_point,
            values: output_values,
        },
    })
}

/// Resume duplex replay after an externally verified walk terminal.
pub(crate) fn verify_duplex_union_walk_suffix_trace<C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    channel: &mut C,
    w_log: usize,
    fixed: &[FixedPattern],
    refs: &DuplexFamilyRefs,
    prefix: DuplexUnionTraceWalkPrefix<'_>,
    walk_terminal: &LaneClaimGroupTrace,
) -> Result<Vec<DuplexColumnClaimTrace>, RegionSidecarError> {
    if walk_terminal.point.len() != w_log {
        return Err(RegionSidecarError::InvalidProof);
    }
    let DuplexUnionTraceWalkPrefix {
        proof,
        mut terminal_claims,
        walk_group: _,
    } = prefix;

    let alpha = channel.sample_f128(b);
    let (substitution_terms, alpha_powers) = duplex_sub_terms_trace(b, refs, &alpha);
    let substitution_refs = claimed_refs(&duplex_substitution_terms(refs, F128::ONE));
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

    let mut shift_cursor = 0usize;
    for (reference, value) in substitution_refs.iter().zip(&substitution.final_values) {
        match reference {
            ColRef::Committed(column) => terminal_claims.push(DuplexColumnClaimTrace {
                column: *column,
                point: substitution_point.clone(),
                value: value.clone(),
            }),
            ColRef::CommittedShift(column) => {
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
                    0,
                    &shift,
                );
                terminal_claims.push(DuplexColumnClaimTrace {
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
    Ok(terminal_claims)
}

/// Replay homogeneous duplex authority on the caller's exact FS channel.
/// Every terminal column and point is derived from canonical refs and proof
/// endpoints; no pending descriptor is accepted from the prover.
pub(crate) fn verify_duplex_union_proof_trace<C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    channel: &mut C,
    w_log: usize,
    fixed: &[FixedPattern],
    refs: &DuplexFamilyRefs,
    proof: &DuplexUnionProof,
) -> Result<Vec<DuplexColumnClaimTrace>, RegionSidecarError> {
    preflight_duplex_authority(w_log, refs, proof)?;
    let prefix = verify_duplex_union_walk_prefix_trace(
        b,
        channel,
        w_log,
        fixed,
        refs,
        proof.walk_deferred(),
    )?;
    let walk_groups = vec![prefix.walk_group().clone()];
    let walk = DeepChainWalkProofTrace::alloc(b, &proof.walk, w_log);
    let walk_terminal = verify_deep_chain_walk_trace(b, channel, w_log, &walk_groups, &walk);
    verify_duplex_union_walk_suffix_trace(b, channel, w_log, fixed, refs, prefix, &walk_terminal)
}

fn resolve_duplex_terminal_claims_trace(
    vk: &DuplexRegionVk,
    total_vars: usize,
    terminal: Vec<DuplexColumnClaimTrace>,
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

/// Verify and append one homogeneous Duplex V1 sidecar inside an already
/// post-commit recursive trace context. The wrapper neither constructs a
/// challenger nor exposes an IO-tail claim list.
pub fn verify_duplex_region_sidecar_trace_post_commit<C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    context: &mut FieldPostCommitTraceContext<'_, C>,
    vk: &DuplexRegionVk,
    proof: &DuplexRegionSidecarProof,
) -> Result<(), RegionSidecarError> {
    let total_vars = context.total_vars();
    preflight_duplex_sidecar(vk, total_vars, proof)?;

    context.observe_label(b, DUPLEX_SIDECAR_TRANSCRIPT_LABEL);
    crate::acceptance::trace::self_verify::observe_pinned_digest(
        b,
        context,
        &vk.transcript_digest(),
    );
    let terminal = verify_duplex_union_proof_trace(
        b,
        context,
        vk.w_log,
        &vk.fixed,
        &vk.refs,
        &proof.authority,
    )?;
    let claims = resolve_duplex_terminal_claims_trace(vk, total_vars, terminal)?;
    context.append_claims(claims);
    Ok(())
}

pub(crate) fn preflight_duplex_authority(
    w_log: usize,
    refs: &DuplexFamilyRefs,
    proof: &DuplexUnionProof,
) -> Result<(), RegionSidecarError> {
    preflight_duplex_deferred_authority(w_log, refs, proof.walk_deferred())?;
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

/// Allocation-free shape gate for a duplex authority with no embedded walk.
pub(crate) fn preflight_duplex_deferred_authority(
    w_log: usize,
    refs: &DuplexFamilyRefs,
    proof: DuplexUnionWalkDeferredProofRef<'_>,
) -> Result<(), RegionSidecarError> {
    if w_log == 0 || w_log >= usize::BITS as usize {
        return Err(RegionSidecarError::InvalidProof);
    }
    let selection_values = claimed_refs(&carry_selection_terms(&refs.c, F128::ONE)).len();
    let substitution_refs = claimed_refs(&duplex_substitution_terms(refs, F128::ONE));
    let shift_count = substitution_refs
        .iter()
        .filter(|reference| matches!(reference, ColRef::CommittedShift(_)))
        .count();
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
    Ok(())
}

pub(crate) fn preflight_duplex_sidecar(
    vk: &DuplexRegionVk,
    total_vars: usize,
    proof: &DuplexRegionSidecarProof,
) -> Result<(), RegionSidecarError> {
    vk.validate_in_witness(total_vars)?;
    if proof.version != DUPLEX_REGION_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    preflight_duplex_authority(vk.w_log, &vk.refs, &proof.authority)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::trace::region_source_binding::{
        build_duplex_union, prove_duplex_union_with_challenger,
        verify_duplex_union_with_challenger, DuplexUnion,
    };
    use crate::acceptance::trace::self_verify::{
        alloc_flat_digest, verify_field_trace_deferred_region_with_post_commit_context,
        FieldR1csProofTrace,
    };
    use crate::region_sidecar::{verify_duplex_region_sidecar, DuplexRegionProverPlan};
    use noid_ivc_core::challenger::{Challenger, FsLaneChallenger};
    use noid_ivc_core::deep_chain::schedule::{compile_duplex, TranscriptOp};
    use noid_ivc_core::field_circuit::FsChannelTrace;
    use noid_ivc_core::field_r1cs::FieldR1cs;
    use noid_ivc_core::pcs::{self, Commitment, PcsParams};
    use noid_ivc_core::proof::{FieldR1csProof, FieldShape};
    use noid_ivc_core::public_io::{PublicIoSpec, WitnessSlice};
    use noid_ivc_core::verifier::{
        verify_field_deferred_matrix_with_post_commit_context, VerifyError,
    };
    use noid_ivc_prover::field_prover::prove_field_with_public_io_and_post_commit_context;

    const FIELD_DOMAIN: &[u8] = b"duplex-sidecar-trace-field-v1";
    const CLASS_DIGEST: [u8; 32] = [0xD6; 32];

    struct NativeCase {
        union: DuplexUnion,
        r1cs: FieldR1cs,
        params: PcsParams,
        spec: PublicIoSpec,
        io: Vec<F128>,
        vk: DuplexRegionVk,
        field_proof: FieldR1csProof,
        sidecar: DuplexRegionSidecarProof,
        commitment: Commitment,
        fresh_value: F128,
        post_challenge: F128,
    }

    fn params(m: usize) -> PcsParams {
        PcsParams {
            m: m + pcs::LOG_PACKING,
            log_inv_rate: 2,
            log_batch_size: 2,
            profile: Default::default(),
        }
    }

    fn native_case() -> NativeCase {
        let layout = compile_duplex(&[
            TranscriptOp::Absorb(vec![None, None, None]),
            TranscriptOp::Squeeze(3),
        ]);
        let union = build_duplex_union(
            &layout,
            [F128::new(0x1111, 0x2222), F128::new(0x3333, 0x4444)],
            &[vec![F128::new(5, 0), F128::new(7, 0), F128::new(11, 0)]],
        );
        let mut builder = FieldR1csBuilder::new();
        let column_len = 1usize << union.w_log;
        while builder.num_wires() % column_len != 0 {
            builder.alloc_f128(F128::ZERO);
        }
        let base = builder.num_wires() / column_len;
        for column in &union.committed {
            for value in column {
                builder.alloc_f128(*value);
            }
        }
        let slices = std::array::from_fn(|column| WitnessSlice {
            log2_len: union.w_log,
            index: base + column,
        });
        let (r1cs, z) = builder.build();
        let params = params(r1cs.m);
        let spec = PublicIoSpec {
            io_slice: WitnessSlice {
                log2_len: 0,
                index: 0,
            },
            io_len: 1,
            claims: Vec::new(),
        };
        let io = vec![F128::ONE];
        let vk = DuplexRegionVk::from_union([0x51; 32], slices, &union).unwrap();
        let plan = DuplexRegionProverPlan::new(&vk, &union.s0, &union.s_out).unwrap();
        let mut prover = FsLaneChallenger::new(FIELD_DOMAIN);
        let (field_proof, sidecar, commitment, _) =
            prove_field_with_public_io_and_post_commit_context(
                &r1cs,
                &z,
                &params,
                &spec,
                &io,
                &CLASS_DIGEST,
                &mut prover,
                |context| {
                    let witness = context.witness();
                    let (sidecar, claims) = plan.prove(witness, context).unwrap();
                    context.append_claims(claims);
                    sidecar
                },
            );

        let shape = FieldShape::of(&r1cs);
        let mut verifier = FsLaneChallenger::new(FIELD_DOMAIN);
        let (_, fresh) = verify_field_deferred_matrix_with_post_commit_context(
            &shape,
            &r1cs.statement_digest(),
            &commitment,
            &field_proof,
            &spec,
            &io,
            &CLASS_DIGEST,
            &sidecar,
            &mut verifier,
            |proof, context| {
                let total_vars = context.total_vars();
                let claims = verify_duplex_region_sidecar(&vk, total_vars, proof, context)
                    .map_err(|_| VerifyError::Auxiliary)?;
                context.append_claims(claims);
                Ok(())
            },
        )
        .unwrap();
        let post_challenge = verifier.sample_f128();

        NativeCase {
            union,
            r1cs,
            params,
            spec,
            io,
            vk,
            field_proof,
            sidecar,
            commitment,
            fresh_value: fresh.value,
            post_challenge,
        }
    }

    fn build_trace(
        case: &NativeCase,
        vk: &DuplexRegionVk,
        sidecar: &DuplexRegionSidecarProof,
    ) -> (FieldR1cs, Vec<F128>, F128, F128) {
        let shape = FieldShape::of(&case.r1cs);
        let digest = case.r1cs.statement_digest();
        let mut builder = FieldR1csBuilder::new();
        let mut channel = FsChannelTrace::new(&mut builder, FIELD_DOMAIN);
        let digest_expr = alloc_flat_digest(&mut builder, &digest);
        let root_expr = alloc_flat_digest(&mut builder, &case.commitment.root);
        let io_expr = case
            .io
            .iter()
            .map(|&value| LinExpr::from_wire(builder.alloc_f128(value)))
            .collect::<Vec<_>>();
        let proof_expr =
            FieldR1csProofTrace::alloc_shape(&mut builder, &case.field_proof, &shape, &case.params);
        let (_, fresh) = verify_field_trace_deferred_region_with_post_commit_context(
            &mut builder,
            &mut channel,
            &shape,
            &case.params,
            &digest_expr,
            &root_expr,
            &proof_expr,
            &case.spec,
            &io_expr,
            &CLASS_DIGEST,
            None,
            |builder, context| {
                verify_duplex_region_sidecar_trace_post_commit(builder, context, vk, sidecar)
                    .unwrap();
            },
        );
        let post = channel.sample_f128(&mut builder).eval(builder.values());
        let fresh_value = fresh.value.eval(builder.values());
        let (r1cs, witness) = builder.build();
        (r1cs, witness, fresh_value, post)
    }

    #[test]
    fn duplex_sidecar_trace_full_context_lockstep() {
        let case = native_case();
        let (r1cs, witness, fresh, post) = build_trace(&case, &case.vk, &case.sidecar);
        assert_eq!(fresh, case.fresh_value);
        assert_eq!(post, case.post_challenge);
        assert!(r1cs.satisfies(&witness));
    }

    #[test]
    fn duplex_authority_generic_native_trace_lockstep() {
        let case = native_case();
        let committed = case
            .union
            .committed
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>();
        let mut authority_prover = FsLaneChallenger::new(b"duplex-authority-trace-lockstep");
        authority_prover.observe_label(DUPLEX_SIDECAR_TRANSCRIPT_LABEL);
        authority_prover.observe_bytes(&case.vk.transcript_digest());
        let (authority, prover_claims) = prove_duplex_union_with_challenger(
            case.vk.w_log,
            &case.vk.fixed,
            &case.vk.refs,
            &[],
            &committed,
            &case.union.s0,
            &case.union.s_out,
            &mut authority_prover,
        );

        let mut native = FsLaneChallenger::new(b"duplex-authority-trace-lockstep");
        native.observe_label(DUPLEX_SIDECAR_TRANSCRIPT_LABEL);
        native.observe_bytes(&case.vk.transcript_digest());
        let native_claims = verify_duplex_union_with_challenger(
            case.vk.w_log,
            &case.vk.fixed,
            &case.vk.refs,
            &[],
            &authority,
            &mut native,
        )
        .unwrap();
        assert_eq!(prover_claims, native_claims);
        let expected = native.sample_f128();

        let mut builder = FieldR1csBuilder::new();
        let mut trace = FsChannelTrace::new(&mut builder, b"duplex-authority-trace-lockstep");
        trace.observe_label(&mut builder, DUPLEX_SIDECAR_TRANSCRIPT_LABEL);
        trace.observe_bytes_const(&mut builder, &case.vk.transcript_digest());
        let trace_claims = verify_duplex_union_proof_trace(
            &mut builder,
            &mut trace,
            case.vk.w_log,
            &case.vk.fixed,
            &case.vk.refs,
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
                    .map(|value| value.eval(builder.values()))
                    .collect::<Vec<_>>(),
                native_claim.point
            );
            assert_eq!(trace_claim.value.eval(builder.values()), native_claim.value);
        }
        let got = trace.sample_f128(&mut builder);
        assert_eq!(got.eval(builder.values()), expected);
        let (r1cs, witness) = builder.build();
        assert!(r1cs.satisfies(&witness));

        let mut bad_authority = authority.clone();
        bad_authority.selection.rounds[0][0] += F128::ONE;
        let mut builder = FieldR1csBuilder::new();
        let mut trace = FsChannelTrace::new(&mut builder, b"duplex-authority-trace-lockstep");
        trace.observe_label(&mut builder, DUPLEX_SIDECAR_TRANSCRIPT_LABEL);
        trace.observe_bytes_const(&mut builder, &case.vk.transcript_digest());
        verify_duplex_union_proof_trace(
            &mut builder,
            &mut trace,
            case.vk.w_log,
            &case.vk.fixed,
            &case.vk.refs,
            &bad_authority,
        )
        .unwrap();
        let (r1cs, witness) = builder.build();
        assert!(!r1cs.satisfies(&witness), "proof mutation satisfied trace");

        let mut bad_vk = case.vk.clone();
        bad_vk.purpose[0] ^= 1;
        let mut builder = FieldR1csBuilder::new();
        let mut trace = FsChannelTrace::new(&mut builder, b"duplex-authority-trace-lockstep");
        trace.observe_label(&mut builder, DUPLEX_SIDECAR_TRANSCRIPT_LABEL);
        trace.observe_bytes_const(&mut builder, &bad_vk.transcript_digest());
        verify_duplex_union_proof_trace(
            &mut builder,
            &mut trace,
            bad_vk.w_log,
            &bad_vk.fixed,
            &bad_vk.refs,
            &authority,
        )
        .unwrap();
        let (r1cs, witness) = builder.build();
        assert!(!r1cs.satisfies(&witness), "VK mutation satisfied trace");

        let mut malformed = authority.clone();
        malformed.shifts.pop();
        assert_eq!(
            preflight_duplex_authority(case.vk.w_log, &case.vk.refs, &malformed),
            Err(RegionSidecarError::InvalidProof)
        );
        let mut bad_version = case.sidecar.clone();
        bad_version.version = bad_version.version.wrapping_add(1);
        assert_eq!(
            preflight_duplex_sidecar(&case.vk, case.r1cs.m, &bad_version),
            Err(RegionSidecarError::UnsupportedVersion)
        );
    }
}
