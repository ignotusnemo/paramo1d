// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Link component of the mandatory joint C1 HistoryStep authority.
//!
//! Link replay has exactly three verticals: heterogeneous leaf and transcript
//! Walk L-A, feed-forward Merkle Walk L-B, and recordings Walk L-C. Their
//! prefixes run on the outer post-commit channel. Their walk instances are
//! combined with all six Block instances in the single joint ragged walk.
//!
//! In V5, walk L-C hosts the two transcripts needed by the authenticated
//! parent arm: its joint Block child and the `[R]_prev` replay's complete
//! outer Fiat-Shamir channel. The latter includes the previous HistoryStep's
//! full joint sidecar verification. One transcript selector is committed and
//! constrained to the same one-hot parent selector used by the recursive
//! verifier. The resulting trust chain is:
//!
//! 1. Link N's circuit runs both parent verifier arms inline and commits the
//!    selected arm's two Fiat-Shamir transcripts as walk L-C columns. Every
//!    absorbed witness lane is pinned to an A-cell, every squeezed challenge
//!    to its carry cell, and every protocol constant to a VK fixed pattern.
//! 2. Link N's joint C1 sidecar derives the three Link prefixes on Link N's
//!    outer Field post-commit channel. That channel seeds Block's child
//!    channel. The child proves one ordered nine-instance walk over Link then
//!    Block and completes the six Block suffixes. Its terminal is absorbed
//!    back into the outer channel before the three Link suffixes.
//! 3. Link N+1's `[R]_prev` replay verifies Link N's Field proof and the same
//!    complete joint C1 transcript. N+1 records the selected replay channel
//!    into N+1's L-C columns, which are covered by N+1's joint sidecar.
//! 4. The induction closes at the tip because the terminal decider natively
//!    verifies the identical joint C1 path. Its L-C authority covers both
//!    selected transcripts, so the authenticated chain continues to genesis.
//!
//! The `[R]_prev` recording layout hosts the sidecar verification transcript
//! that binds the VK describing that layout. The self-reference is broken by
//! absorbing the Link and rec-C VK digests as witness lanes pinned to matrix
//! constants, never as schedule constants. No VK digest feeds its own
//! preimage.

use noid_ivc_core::challenger::Challenger;
use noid_ivc_core::deep_chain::c1::C1LaneClaimGroup;
use noid_ivc_core::field::{F128, F256};
use noid_ivc_core::field_circuit::FsChannelOps;
use noid_ivc_core::pcs::{C1QuirkyDirectClaim, PcsParams};
use noid_ivc_core::public_io::PublicIoSpec;
use noid_poseidon2b::native::poseidon2b_hash_byte_slices;

use crate::acceptance::trace::deep_chain::C1LaneClaimGroupTrace;
use crate::acceptance::trace::r_pcs_region::{
    link_r_pcs_leaf_sidecar_purpose, link_r_pcs_path_sidecar_purpose, link_recordings_purpose,
};
use crate::acceptance::trace::self_verify::{
    C1QuirkyDirectClaimTrace, FieldPostCommitTraceContext,
};
use crate::acceptance::trace::FieldR1csBuilder;

use super::bounded_decode::{
    merkle_shape_for_vk, DeferredFixedProofShape, DeferredMerkleProofShape,
};
use super::combined_duplex::{
    combined_walk_deferred_bounded_shape, verify_c1_combined_duplex_region_walk_deferred_prefix,
    verify_c1_combined_duplex_region_walk_deferred_prefix_trace,
    C1CombinedDuplexRegionWalkDeferredProof,
};
use super::recording_duplex::{
    recording_duplex_bounded_shape, validate_recording_endpoints,
    verify_c1_recording_duplex_region_walk_deferred_prefix,
    verify_c1_recording_duplex_region_walk_deferred_prefix_trace,
    C1RecordingDuplexRegionWalkDeferredProof, RecordingDuplexRegionProverPlan,
    RecordingDuplexRegionVk,
};
use super::{
    verify_c1_merkle_region_walk_deferred_prefix,
    verify_c1_merkle_region_walk_deferred_prefix_trace, C1MerkleRegionWalkDeferredProof,
    CombinedDuplexRegionProverPlan, CombinedDuplexRegionVk, MerkleRegionProverPlan, MerkleRegionVk,
    RegionSidecarError, RegionWalkEndpoints,
};

pub const LINK_REGION_SIDECAR_VERSION: u8 = 5;

const LINK_REGION_VK_DIGEST_DOMAIN: &[u8] = b"NOID/REGION-SIDECAR/LINK-VK/V5";
const LINK_POST_COMMIT_CLASS_DIGEST_DOMAIN: &[u8] =
    b"NOID/REGION-SIDECAR/LINK-POST-COMMIT-CLASS/V5";
const LINK_REGION_TRANSCRIPT_LABEL: &[u8] = b"history-region-sidecar-link-v5";

/// Canonical key for the three mandatory link-region verticals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkRegionSidecarVk {
    leaf_a: CombinedDuplexRegionVk,
    path_b: MerkleRegionVk,
    rec_c: RecordingDuplexRegionVk,
    transcript_digest: [u8; 32],
}

impl LinkRegionSidecarVk {
    pub fn new(
        leaf_a: CombinedDuplexRegionVk,
        path_b: MerkleRegionVk,
        rec_c: RecordingDuplexRegionVk,
    ) -> Result<Self, RegionSidecarError> {
        let transcript_digest = link_region_sidecar_vk_digest(&leaf_a, &path_b, &rec_c);
        let vk = Self {
            leaf_a,
            path_b,
            rec_c,
            transcript_digest,
        };
        vk.validate_roles()?;
        Ok(vk)
    }

    pub fn leaf_a(&self) -> &CombinedDuplexRegionVk {
        &self.leaf_a
    }

    pub fn path_b(&self) -> &MerkleRegionVk {
        &self.path_b
    }

    pub fn rec_c(&self) -> &RecordingDuplexRegionVk {
        &self.rec_c
    }

    pub fn transcript_digest(&self) -> [u8; 32] {
        self.transcript_digest
    }

    fn validate_roles(&self) -> Result<(), RegionSidecarError> {
        if self.leaf_a.purpose() != &link_r_pcs_leaf_sidecar_purpose()
            || self.path_b.purpose() != &link_r_pcs_path_sidecar_purpose()
            || self.rec_c.purpose() != &link_recordings_purpose()
        {
            return Err(RegionSidecarError::UnsupportedVkShape);
        }
        Ok(())
    }
}

fn link_region_sidecar_vk_digest(
    leaf_a: &CombinedDuplexRegionVk,
    path_b: &MerkleRegionVk,
    rec_c: &RecordingDuplexRegionVk,
) -> [u8; 32] {
    let version = [LINK_REGION_SIDECAR_VERSION];
    poseidon2b_hash_byte_slices(
        LINK_REGION_VK_DIGEST_DOMAIN,
        &[
            &version,
            b"leaf-a",
            &leaf_a.transcript_digest(),
            b"path-b",
            &path_b.transcript_digest(),
            b"rec-c",
            &rec_c.transcript_digest(),
        ],
    )
}

/// Stable identity bound at the link Field proof's post-commit boundary.
pub fn link_post_commit_class_digest(
    matrix_digest: &[u8; 32],
    spec: &PublicIoSpec,
    pcs_params: &PcsParams,
    sidecar_vk: &LinkRegionSidecarVk,
) -> [u8; 32] {
    let mut spec_bytes = Vec::new();
    push_u64(&mut spec_bytes, spec.io_slice.log2_len);
    push_u64(&mut spec_bytes, spec.io_slice.index);
    push_u64(&mut spec_bytes, spec.io_len);
    push_u64(&mut spec_bytes, spec.claims.len());
    for claim in &spec.claims {
        push_u64(&mut spec_bytes, claim.slice.log2_len);
        push_u64(&mut spec_bytes, claim.slice.index);
        push_u64(&mut spec_bytes, claim.point.start);
        push_u64(&mut spec_bytes, claim.point.end);
        push_u64(&mut spec_bytes, claim.value);
    }

    let mut pcs_bytes = Vec::new();
    push_u64(&mut pcs_bytes, pcs_params.m);
    push_u64(&mut pcs_bytes, pcs_params.log_inv_rate);
    push_u64(&mut pcs_bytes, pcs_params.log_batch_size);
    let profile = pcs_params.profile.as_str().as_bytes();
    push_u64(&mut pcs_bytes, profile.len());
    pcs_bytes.extend_from_slice(profile);

    let version = [LINK_REGION_SIDECAR_VERSION];
    poseidon2b_hash_byte_slices(
        LINK_POST_COMMIT_CLASS_DIGEST_DOMAIN,
        &[
            &version,
            b"link",
            matrix_digest,
            &spec_bytes,
            &pcs_bytes,
            &sidecar_vk.transcript_digest(),
        ],
    )
}

/// Owned link-side walk endpoints.  Committed columns remain exclusively in
/// the enclosing Field witness and are selected through the two VKs.
pub struct LinkRegionProverInput {
    leaf_a: RegionWalkEndpoints,
    path_b: RegionWalkEndpoints,
    rec_c: RegionWalkEndpoints,
}

impl LinkRegionProverInput {
    pub fn new(
        vk: &LinkRegionSidecarVk,
        leaf_a: RegionWalkEndpoints,
        path_b: RegionWalkEndpoints,
        rec_c: RegionWalkEndpoints,
    ) -> Result<Self, RegionSidecarError> {
        vk.validate_roles()?;
        let input = Self {
            leaf_a,
            path_b,
            rec_c,
        };
        input.validate(vk)?;
        Ok(input)
    }

    fn validate(&self, vk: &LinkRegionSidecarVk) -> Result<(), RegionSidecarError> {
        CombinedDuplexRegionProverPlan::new(vk.leaf_a(), self.leaf_a.s0(), self.leaf_a.s_out())?;
        MerkleRegionProverPlan::new(vk.path_b(), self.path_b.s0(), self.path_b.s_out())?;
        validate_recording_endpoints(vk.rec_c(), &self.rec_c)?;
        Ok(())
    }

    fn validate_certified_c1(&self, vk: &LinkRegionSidecarVk) -> Result<(), RegionSidecarError> {
        CombinedDuplexRegionProverPlan::new_certified_c1(
            vk.leaf_a(),
            self.leaf_a.s0(),
            self.leaf_a.s_out(),
        )?;
        MerkleRegionProverPlan::new_certified_c1(
            vk.path_b(),
            self.path_b.s0(),
            self.path_b.s_out(),
        )?;
        RecordingDuplexRegionProverPlan::new_certified_c1(
            vk.rec_c(),
            self.rec_c.s0(),
            self.rec_c.s_out(),
        )?;
        Ok(())
    }
}

pub struct LinkRegionProverPlan<'a> {
    vk: &'a LinkRegionSidecarVk,
    input: &'a LinkRegionProverInput,
}

pub(crate) struct C1LinkRegionProverWalkContinuation<'a, 'z> {
    leaf_a: super::combined_duplex::C1CombinedDuplexRegionProverWalkContinuation<'a, 'z>,
    path_b: super::C1MerkleRegionProverWalkContinuation<'a, 'z>,
    rec_c: super::recording_duplex::C1RecordingDuplexProverWalkContinuation<'a, 'z>,
}

impl C1LinkRegionProverWalkContinuation<'_, '_> {
    pub(crate) fn groups(&self) -> [C1LaneClaimGroup; 3] {
        [
            self.leaf_a.group().clone(),
            self.path_b.group().clone(),
            self.rec_c.group().clone(),
        ]
    }

    pub(crate) fn states(&self) -> [&[Vec<F128>; 4]; 3] {
        [self.leaf_a.s0(), self.path_b.s0(), self.rec_c.s0()]
    }

    pub(crate) fn finish<Ch: Challenger>(
        self,
        terminals: &[C1LaneClaimGroup; 3],
        challenger: &mut Ch,
    ) -> Result<(C1LinkRegionWalkDeferredProof, Vec<C1QuirkyDirectClaim>), RegionSidecarError> {
        let (leaf_a, mut claims) = self.leaf_a.finish(&terminals[0], challenger)?;
        let (path_b, child_claims) = self.path_b.finish(&terminals[1], challenger)?;
        claims.extend(child_claims);
        let (rec_c, child_claims) = self.rec_c.finish(&terminals[2], challenger)?;
        claims.extend(child_claims);
        Ok((
            C1LinkRegionWalkDeferredProof {
                leaf_a,
                path_b,
                rec_c,
            },
            claims,
        ))
    }
}

pub(crate) struct C1LinkRegionVerifierWalkContinuation<'a> {
    leaf_a: super::combined_duplex::C1CombinedDuplexRegionVerifierWalkContinuation<'a>,
    path_b: super::C1MerkleRegionVerifierWalkContinuation<'a>,
    rec_c: super::recording_duplex::C1RecordingDuplexVerifierWalkContinuation<'a>,
}

impl C1LinkRegionVerifierWalkContinuation<'_> {
    pub(crate) fn groups(&self) -> [C1LaneClaimGroup; 3] {
        [
            self.leaf_a.group().clone(),
            self.path_b.group().clone(),
            self.rec_c.group().clone(),
        ]
    }

    pub(crate) fn finish<Ch: Challenger>(
        self,
        terminals: &[C1LaneClaimGroup; 3],
        challenger: &mut Ch,
    ) -> Result<Vec<C1QuirkyDirectClaim>, RegionSidecarError> {
        let mut claims = self.leaf_a.finish(&terminals[0], challenger)?;
        claims.extend(self.path_b.finish(&terminals[1], challenger)?);
        claims.extend(self.rec_c.finish(&terminals[2], challenger)?);
        Ok(claims)
    }
}

impl<'a> LinkRegionProverPlan<'a> {
    pub fn new(
        vk: &'a LinkRegionSidecarVk,
        input: &'a LinkRegionProverInput,
    ) -> Result<Self, RegionSidecarError> {
        vk.validate_roles()?;
        input.validate(vk)?;
        Ok(Self { vk, input })
    }

    pub(crate) fn new_certified_c1(
        vk: &'a LinkRegionSidecarVk,
        input: &'a LinkRegionProverInput,
    ) -> Result<Self, RegionSidecarError> {
        vk.validate_roles()?;
        input.validate_certified_c1(vk)?;
        Ok(Self { vk, input })
    }

    pub(crate) fn prove_c1_walk_deferred_prefix<'z, Ch: Challenger>(
        &self,
        z: &'z [F128],
        challenger: &mut Ch,
    ) -> Result<C1LinkRegionProverWalkContinuation<'a, 'z>, RegionSidecarError> {
        bind_link_vk(challenger, self.vk);
        let leaf_plan = CombinedDuplexRegionProverPlan::new_certified_c1(
            self.vk.leaf_a(),
            self.input.leaf_a.s0(),
            self.input.leaf_a.s_out(),
        )?;
        let path_plan = MerkleRegionProverPlan::new_certified_c1(
            self.vk.path_b(),
            self.input.path_b.s0(),
            self.input.path_b.s_out(),
        )?;
        let rec_plan = RecordingDuplexRegionProverPlan::new_certified_c1(
            self.vk.rec_c(),
            self.input.rec_c.s0(),
            self.input.rec_c.s_out(),
        )?;
        Ok(C1LinkRegionProverWalkContinuation {
            leaf_a: leaf_plan.prove_c1_walk_deferred_prefix(z, challenger)?,
            path_b: path_plan.prove_c1_walk_deferred_prefix(z, challenger)?,
            rec_c: rec_plan.prove_c1_walk_deferred_prefix(z, challenger)?,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct C1LinkRegionWalkDeferredProof {
    leaf_a: C1CombinedDuplexRegionWalkDeferredProof,
    path_b: C1MerkleRegionWalkDeferredProof,
    rec_c: C1RecordingDuplexRegionWalkDeferredProof,
}

impl C1LinkRegionWalkDeferredProof {
    pub(crate) fn new(
        leaf_a: C1CombinedDuplexRegionWalkDeferredProof,
        path_b: C1MerkleRegionWalkDeferredProof,
        rec_c: C1RecordingDuplexRegionWalkDeferredProof,
    ) -> Self {
        Self {
            leaf_a,
            path_b,
            rec_c,
        }
    }

    pub(crate) fn parts(
        &self,
    ) -> (
        &C1CombinedDuplexRegionWalkDeferredProof,
        &C1MerkleRegionWalkDeferredProof,
        &C1RecordingDuplexRegionWalkDeferredProof,
    ) {
        (&self.leaf_a, &self.path_b, &self.rec_c)
    }
}

pub(crate) fn verify_c1_link_region_walk_deferred_prefix<'a, Ch: Challenger>(
    vk: &'a LinkRegionSidecarVk,
    total_vars: usize,
    proof: &'a C1LinkRegionWalkDeferredProof,
    challenger: &mut Ch,
) -> Result<C1LinkRegionVerifierWalkContinuation<'a>, RegionSidecarError> {
    let timing = std::env::var_os("NOIDH_C1_VERIFY_TIMING").is_some();
    let total_started = std::time::Instant::now();
    vk.validate_roles()?;
    let validate_micros = total_started.elapsed().as_micros();
    bind_link_vk(challenger, vk);
    let bind_micros = total_started.elapsed().as_micros() - validate_micros;
    let leaf_started = std::time::Instant::now();
    let leaf_a = verify_c1_combined_duplex_region_walk_deferred_prefix(
        vk.leaf_a(),
        total_vars,
        &proof.leaf_a,
        challenger,
    )?;
    let leaf_micros = leaf_started.elapsed().as_micros();
    let path_started = std::time::Instant::now();
    let path_b = verify_c1_merkle_region_walk_deferred_prefix(
        vk.path_b(),
        total_vars,
        &proof.path_b,
        challenger,
    )?;
    let path_micros = path_started.elapsed().as_micros();
    let recording_started = std::time::Instant::now();
    let rec_c = verify_c1_recording_duplex_region_walk_deferred_prefix(
        vk.rec_c(),
        total_vars,
        &proof.rec_c,
        challenger,
    )?;
    let recording_micros = recording_started.elapsed().as_micros();
    if timing {
        eprintln!(
            "[link-c1 prefix] validate_us={validate_micros} bind_us={bind_micros} leaf_us={leaf_micros} path_us={path_micros} recording_us={recording_micros} total_us={}",
            total_started.elapsed().as_micros(),
        );
    }
    Ok(C1LinkRegionVerifierWalkContinuation {
        leaf_a,
        path_b,
        rec_c,
    })
}

pub(crate) struct C1LinkRegionTraceWalkContinuation<'a> {
    leaf_a: super::combined_duplex::C1CombinedDuplexRegionTraceWalkContinuation<'a>,
    path_b: super::C1MerkleRegionTraceWalkContinuation<'a>,
    rec_c: super::recording_duplex::C1RecordingDuplexTraceWalkContinuation<'a>,
}

impl C1LinkRegionTraceWalkContinuation<'_> {
    pub(crate) fn groups(&self) -> [C1LaneClaimGroupTrace; 3] {
        [
            self.leaf_a.walk_group(),
            self.path_b.walk_group(),
            self.rec_c.walk_group(),
        ]
    }

    pub(crate) fn finish<C: FsChannelOps>(
        self,
        b: &mut FieldR1csBuilder,
        context: &mut FieldPostCommitTraceContext<'_, C>,
        terminals: &[C1LaneClaimGroupTrace; 3],
    ) -> Result<Vec<C1QuirkyDirectClaimTrace>, RegionSidecarError> {
        let mut claims = self.leaf_a.finish(b, context, &terminals[0])?;
        claims.extend(self.path_b.finish(b, context, &terminals[1])?);
        claims.extend(self.rec_c.finish(b, context, &terminals[2])?);
        Ok(claims)
    }
}

pub(crate) fn verify_c1_link_region_walk_deferred_prefix_trace<'a, C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    context: &mut FieldPostCommitTraceContext<'_, C>,
    vk: &'a LinkRegionSidecarVk,
    proof: &'a C1LinkRegionWalkDeferredProof,
) -> Result<C1LinkRegionTraceWalkContinuation<'a>, RegionSidecarError> {
    vk.validate_roles()?;
    context.observe_label(b, LINK_REGION_TRANSCRIPT_LABEL);
    crate::acceptance::trace::self_verify::observe_pinned_digest(
        b,
        context,
        &vk.transcript_digest(),
    );
    let leaf_a = verify_c1_combined_duplex_region_walk_deferred_prefix_trace(
        b,
        context,
        vk.leaf_a(),
        &proof.leaf_a,
    )?;
    let path_b =
        verify_c1_merkle_region_walk_deferred_prefix_trace(b, context, vk.path_b(), &proof.path_b)?;
    let rec_c = verify_c1_recording_duplex_region_walk_deferred_prefix_trace(
        b,
        context,
        vk.rec_c(),
        &proof.rec_c,
    )?;
    Ok(C1LinkRegionTraceWalkContinuation {
        leaf_a,
        path_b,
        rec_c,
    })
}

pub(super) struct LinkC1ProofShapes {
    pub(super) leaf: DeferredFixedProofShape,
    pub(super) path: DeferredMerkleProofShape,
    pub(super) recording: DeferredFixedProofShape,
}

pub(super) fn link_c1_proof_shapes(
    vk: &LinkRegionSidecarVk,
    total_vars: usize,
) -> Result<LinkC1ProofShapes, RegionSidecarError> {
    vk.validate_roles()?;
    Ok(LinkC1ProofShapes {
        leaf: combined_walk_deferred_bounded_shape(vk.leaf_a(), total_vars)?,
        path: merkle_shape_for_vk(vk.path_b(), total_vars)?.walk_deferred(),
        recording: recording_duplex_bounded_shape(vk.rec_c(), total_vars)?.walk_deferred(),
    })
}

pub(crate) fn shape_only_c1_link_region_walk_deferred_proof(
    vk: &LinkRegionSidecarVk,
    total_vars: usize,
) -> Result<C1LinkRegionWalkDeferredProof, RegionSidecarError> {
    use noid_ivc_core::deep_chain::relations::c1::{C1ColumnRelationProof, C1ShiftDischargeProof};

    use crate::acceptance::trace::region_source_binding_c1::{
        C1DuplexUnionWalkDeferredProof, C1MerkleUnionWalkDeferredProof,
    };

    let relation = |rounds: usize, values: usize| C1ColumnRelationProof {
        rounds: vec![[F256::ZERO; noid_ivc_core::deep_chain::relations::RELATION_DEGREE]; rounds],
        final_values: vec![F256::ZERO; values],
    };
    let shifts = |count: usize, w_log: usize| -> Vec<C1ShiftDischargeProof> {
        (0..count)
            .map(|_| C1ShiftDischargeProof {
                rounds: vec![[F256::ZERO; 2]; w_log],
                final_value: F256::ZERO,
            })
            .collect()
    };
    let LinkC1ProofShapes {
        leaf,
        path,
        recording,
    } = link_c1_proof_shapes(vk, total_vars)?;
    if !matches!(
        leaf.tail,
        super::bounded_decode::ProofTailShape::None
            | super::bounded_decode::ProofTailShape::RelationOption(None)
    ) || !matches!(
        recording.tail,
        super::bounded_decode::ProofTailShape::None
            | super::bounded_decode::ProofTailShape::RelationOption(None)
    ) {
        return Err(RegionSidecarError::UnsupportedVkShape);
    }
    Ok(C1LinkRegionWalkDeferredProof {
        leaf_a: C1CombinedDuplexRegionWalkDeferredProof::new(C1DuplexUnionWalkDeferredProof {
            selection: relation(leaf.w_log, leaf.selection_values),
            substitution: relation(leaf.w_log, leaf.substitution_values),
            shifts: shifts(leaf.shifts, leaf.w_log),
        }),
        path_b: C1MerkleRegionWalkDeferredProof::new(C1MerkleUnionWalkDeferredProof {
            zero: relation(path.w_log, path.zero_values),
            zero_shifts: shifts(path.zero_shifts, path.w_log),
            selection: relation(path.w_log, path.selection_values),
            substitution: relation(path.w_log, path.substitution_values),
            shifts: shifts(path.shifts, path.w_log),
        }),
        rec_c: C1RecordingDuplexRegionWalkDeferredProof::new(
            F128::ZERO,
            C1DuplexUnionWalkDeferredProof {
                selection: relation(recording.w_log, recording.selection_values),
                substitution: relation(recording.w_log, recording.substitution_values),
                shifts: shifts(recording.shifts, recording.w_log),
            },
        ),
    })
}

fn bind_link_vk<Ch: Challenger>(challenger: &mut Ch, vk: &LinkRegionSidecarVk) {
    challenger.observe_label(LINK_REGION_TRANSCRIPT_LABEL);
    challenger.observe_bytes(&vk.transcript_digest());
}

fn push_u64(bytes: &mut Vec<u8>, value: usize) {
    let value = u64::try_from(value).expect("link sidecar class index exceeds u64");
    bytes.extend_from_slice(&value.to_le_bytes());
}
