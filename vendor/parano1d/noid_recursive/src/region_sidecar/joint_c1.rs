// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! One genuine C1 History sidecar transcript shared by Link and Block.
//!
//! Link's three prefixes are derived on the outer post-commit channel. That
//! channel then samples the seed of Block's child channel. The child proves
//! one ordered nine-instance walk over Link followed by Block and completes
//! Block's six suffixes. Its terminal digest is absorbed back into the outer
//! channel before Link's three suffixes. Thus every algebraic challenge and
//! proof message lives in GF(2^256), while the nine committed Poseidon state
//! tables remain in GF(2^128).

use noid_ivc_core::challenger::{Challenger, FsLaneChallenger};
use noid_ivc_core::deep_chain::c1::{
    prove_ragged_deep_chain_walk, verify_ragged_deep_chain_walk, C1LaneClaimGroup,
    C1MultiDeepChainWalkProof, C1MultiWalkLayerProof,
};
use noid_ivc_core::deep_chain::schedule::DuplexLayout;
use noid_ivc_core::field::{F128, F256};
use noid_ivc_core::field_circuit::{
    FsChannelOps, FsChannelUnionRecorder, LayoutRecordedChannel, LayoutRecordingChallenger,
    RecordedChannel,
};
use noid_ivc_core::pcs::C1QuirkyDirectClaim;
use noid_ivc_core::verifier::FieldPostCommitVerifierContext;
use noid_poseidon2b::native::permutation::N_ROUNDS;

use crate::acceptance::trace::deep_chain::{
    verify_c1_ragged_deep_chain_walk_trace, C1MultiDeepChainWalkProofTrace,
};
use crate::acceptance::trace::self_verify::FieldPostCommitTraceContext;
use crate::acceptance::trace::FieldR1csBuilder;

use super::block::{
    shape_only_c1_block_region_walk_deferred_proof, verify_c1_block_region_walk_deferred_prefix,
    verify_c1_block_region_walk_deferred_prefix_trace, BlockRegionProverPlan, BlockRegionSidecarVk,
    C1BlockRegionWalkDeferredProof, BLOCK_SIDECAR_CHILD_DOMAIN, BLOCK_SIDECAR_RECORDED_LABEL,
};
use super::link::{
    shape_only_c1_link_region_walk_deferred_proof, verify_c1_link_region_walk_deferred_prefix,
    verify_c1_link_region_walk_deferred_prefix_trace, C1LinkRegionWalkDeferredProof,
    LinkRegionProverPlan, LinkRegionSidecarVk,
};
use super::{RegionSidecarError, JOINT_C1_BLOCK_GROUPS, JOINT_C1_GROUPS, JOINT_C1_LINK_GROUPS};

pub(crate) const JOINT_C1_SIDECAR_VERSION: u8 = 1;
const JOINT_C1_TRANSCRIPT_LABEL: &[u8] = b"history-region-sidecar-joint-c1-v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct JointC1RegionSidecarProof {
    version: u8,
    link: C1LinkRegionWalkDeferredProof,
    block: C1BlockRegionWalkDeferredProof,
    walk: C1MultiDeepChainWalkProof,
}

pub(crate) fn shape_only_joint_c1_region_sidecar_proof(
    link_vk: &LinkRegionSidecarVk,
    block_vk: &BlockRegionSidecarVk,
    total_vars: usize,
) -> Result<JointC1RegionSidecarProof, RegionSidecarError> {
    let link = shape_only_c1_link_region_walk_deferred_proof(link_vk, total_vars)?;
    let block = shape_only_c1_block_region_walk_deferred_proof(block_vk, total_vars)?;
    let w_logs: [usize; JOINT_C1_GROUPS] = [
        link_vk.leaf_a().w_log(),
        link_vk.path_b().w_log(),
        link_vk.rec_c().w_log(),
        block_vk.wallet_a().w_log(),
        block_vk.meta_a().w_log(),
        block_vk.wallet_b().w_log(),
        block_vk.meta_b().w_log(),
        block_vk.owner_c().w_log(),
        block_vk.main_c().w_log(),
    ];
    let max_w_log = *w_logs.iter().max().expect("nine joint C1 children");
    let walk = C1MultiDeepChainWalkProof {
        layers: (0..N_ROUNDS)
            .map(|_| C1MultiWalkLayerProof {
                round_coeffs: vec![[F256::ZERO; noid_ivc_core::deep_chain::WALK_DEGREE]; max_w_log],
                next_values: vec![[F256::ZERO; 4]; w_logs.len()],
            })
            .collect(),
    };
    Ok(JointC1RegionSidecarProof {
        version: JOINT_C1_SIDECAR_VERSION,
        link,
        block,
        walk,
    })
}

struct JointC1ProofShapes {
    link_leaf: super::bounded_decode::DeferredFixedProofShape,
    link_path: super::bounded_decode::DeferredMerkleProofShape,
    link_recording: super::bounded_decode::DeferredFixedProofShape,
    block_wallet_a: super::bounded_decode::DeferredFixedProofShape,
    block_meta_a: super::bounded_decode::DeferredFixedProofShape,
    block_wallet_b: super::bounded_decode::DeferredMerkleProofShape,
    block_meta_b: super::bounded_decode::DeferredMerkleProofShape,
    block_owner_c: super::bounded_decode::DeferredFixedProofShape,
    block_main_c: super::bounded_decode::DeferredFixedProofShape,
    walk: super::bounded_decode::MultiWalkProofShape,
}

fn joint_c1_proof_shapes(
    link_vk: &LinkRegionSidecarVk,
    block_vk: &BlockRegionSidecarVk,
    total_vars: usize,
) -> Result<JointC1ProofShapes, RegionSidecarError> {
    let super::link::LinkC1ProofShapes {
        leaf: link_leaf,
        path: link_path,
        recording: link_recording,
    } = super::link::link_c1_proof_shapes(link_vk, total_vars)?;
    let super::block::BlockC1ProofShapes {
        wallet_a: block_wallet_a,
        meta_a: block_meta_a,
        wallet_b: block_wallet_b,
        meta_b: block_meta_b,
        owner_c: block_owner_c,
        main_c: block_main_c,
    } = super::block::block_c1_proof_shapes(block_vk, total_vars)?;
    let max_w_log = [
        link_leaf.w_log,
        link_path.w_log,
        link_recording.w_log,
        block_wallet_a.w_log,
        block_meta_a.w_log,
        block_wallet_b.w_log,
        block_meta_b.w_log,
        block_owner_c.w_log,
        block_main_c.w_log,
    ]
    .into_iter()
    .max()
    .ok_or(RegionSidecarError::InvalidProof)?;
    Ok(JointC1ProofShapes {
        link_leaf,
        link_path,
        link_recording,
        block_wallet_a,
        block_meta_a,
        block_wallet_b,
        block_meta_b,
        block_owner_c,
        block_main_c,
        walk: super::bounded_decode::multi_walk_proof_shape(max_w_log, 9)?,
    })
}

pub(crate) fn canonical_joint_c1_region_sidecar_len(
    link_vk: &LinkRegionSidecarVk,
    block_vk: &BlockRegionSidecarVk,
    total_vars: usize,
) -> Result<usize, RegionSidecarError> {
    use super::canonical_codec as canonical;

    let shape = joint_c1_proof_shapes(link_vk, block_vk, total_vars)?;
    let mut len = 1usize;
    for child in [
        &shape.link_leaf,
        &shape.block_wallet_a,
        &shape.block_meta_a,
        &shape.block_owner_c,
        &shape.block_main_c,
    ] {
        len = len
            .checked_add(canonical::c1_deferred_fixed_len(child)?)
            .ok_or(RegionSidecarError::InvalidProof)?;
    }
    let recording_len = canonical::c1_deferred_fixed_len(&shape.link_recording)?;
    len = len
        .checked_add(16)
        .and_then(|value| value.checked_add(recording_len))
        .ok_or(RegionSidecarError::InvalidProof)?;
    for child in [&shape.link_path, &shape.block_wallet_b, &shape.block_meta_b] {
        len = len
            .checked_add(canonical::c1_deferred_merkle_len(child)?)
            .ok_or(RegionSidecarError::InvalidProof)?;
    }
    len.checked_add(canonical::c1_multi_walk_len(&shape.walk)?)
        .ok_or(RegionSidecarError::InvalidProof)
}

pub(crate) fn encode_joint_c1_region_sidecar_canonical(
    link_vk: &LinkRegionSidecarVk,
    block_vk: &BlockRegionSidecarVk,
    total_vars: usize,
    proof: &JointC1RegionSidecarProof,
) -> Result<Vec<u8>, RegionSidecarError> {
    use super::canonical_codec as canonical;

    if proof.version != JOINT_C1_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    let shape = joint_c1_proof_shapes(link_vk, block_vk, total_vars)?;
    let expected = canonical_joint_c1_region_sidecar_len(link_vk, block_vk, total_vars)?;
    let mut out = Vec::with_capacity(expected);
    out.push(proof.version);
    let (link_leaf, link_path, link_recording) = proof.link.parts();
    canonical::encode_c1_duplex_deferred(
        &mut out,
        link_leaf.version(),
        link_leaf.authority(),
        &shape.link_leaf,
    )?;
    canonical::encode_c1_merkle_deferred(
        &mut out,
        link_path.version(),
        link_path.authority(),
        &shape.link_path,
    )?;
    canonical::put_f128(&mut out, link_recording.selector());
    canonical::encode_c1_duplex_deferred(
        &mut out,
        link_recording.version(),
        link_recording.authority(),
        &shape.link_recording,
    )?;
    let (wallet_a, meta_a, wallet_b, meta_b, owner_c, main_c) = proof.block.parts();
    canonical::encode_c1_walk_a_deferred(
        &mut out,
        wallet_a.version(),
        wallet_a.authority(),
        &shape.block_wallet_a,
    )?;
    canonical::encode_c1_walk_a_deferred(
        &mut out,
        meta_a.version(),
        meta_a.authority(),
        &shape.block_meta_a,
    )?;
    canonical::encode_c1_merkle_deferred(
        &mut out,
        wallet_b.version(),
        wallet_b.authority(),
        &shape.block_wallet_b,
    )?;
    canonical::encode_c1_merkle_deferred(
        &mut out,
        meta_b.version(),
        meta_b.authority(),
        &shape.block_meta_b,
    )?;
    canonical::encode_c1_duplex_deferred(
        &mut out,
        owner_c.version(),
        owner_c.authority(),
        &shape.block_owner_c,
    )?;
    canonical::encode_c1_duplex_deferred(
        &mut out,
        main_c.version(),
        main_c.authority(),
        &shape.block_main_c,
    )?;
    canonical::encode_c1_multi_walk(&mut out, &proof.walk, &shape.walk)?;
    if out.len() != expected {
        return Err(RegionSidecarError::InvalidProof);
    }
    Ok(out)
}

pub(crate) fn decode_joint_c1_region_sidecar_canonical(
    link_vk: &LinkRegionSidecarVk,
    block_vk: &BlockRegionSidecarVk,
    total_vars: usize,
    bytes: &[u8],
) -> Result<JointC1RegionSidecarProof, RegionSidecarError> {
    use super::canonical_codec as canonical;

    let shape = joint_c1_proof_shapes(link_vk, block_vk, total_vars)?;
    let expected = canonical_joint_c1_region_sidecar_len(link_vk, block_vk, total_vars)?;
    let mut reader = canonical::CanonicalProofReader::exact(bytes, expected)?;
    if reader.u8()? != JOINT_C1_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    let link = C1LinkRegionWalkDeferredProof::new(
        super::combined_duplex::C1CombinedDuplexRegionWalkDeferredProof::new(
            canonical::decode_c1_duplex_deferred(&mut reader, &shape.link_leaf)?,
        ),
        super::C1MerkleRegionWalkDeferredProof::new(canonical::decode_c1_merkle_deferred(
            &mut reader,
            &shape.link_path,
        )?),
        super::recording_duplex::C1RecordingDuplexRegionWalkDeferredProof::new(
            reader.f128()?,
            canonical::decode_c1_duplex_deferred(&mut reader, &shape.link_recording)?,
        ),
    );
    let block = C1BlockRegionWalkDeferredProof::new(
        super::C1WalkARegionWalkDeferredProof::new(canonical::decode_c1_walk_a_deferred(
            &mut reader,
            &shape.block_wallet_a,
        )?),
        super::C1WalkARegionWalkDeferredProof::new(canonical::decode_c1_walk_a_deferred(
            &mut reader,
            &shape.block_meta_a,
        )?),
        super::C1MerkleRegionWalkDeferredProof::new(canonical::decode_c1_merkle_deferred(
            &mut reader,
            &shape.block_wallet_b,
        )?),
        super::C1MerkleRegionWalkDeferredProof::new(canonical::decode_c1_merkle_deferred(
            &mut reader,
            &shape.block_meta_b,
        )?),
        super::C1DuplexRegionWalkDeferredProof::new(canonical::decode_c1_duplex_deferred(
            &mut reader,
            &shape.block_owner_c,
        )?),
        super::C1DuplexRegionWalkDeferredProof::new(canonical::decode_c1_duplex_deferred(
            &mut reader,
            &shape.block_main_c,
        )?),
    );
    let walk = canonical::decode_c1_multi_walk(&mut reader, &shape.walk)?;
    reader.finish()?;
    Ok(JointC1RegionSidecarProof {
        version: JOINT_C1_SIDECAR_VERSION,
        link,
        block,
        walk,
    })
}

pub(crate) fn prove_joint_c1_region_sidecar<Ch: Challenger>(
    link_plan: &LinkRegionProverPlan<'_>,
    block_plan: &BlockRegionProverPlan<'_>,
    witness: &[F128],
    outer: &mut Ch,
) -> Result<(JointC1RegionSidecarProof, Vec<C1QuirkyDirectClaim>), RegionSidecarError> {
    let timing = std::env::var_os("NOIDH_C1_JOINT_TIMING").is_some();
    let mut stage = std::time::Instant::now();
    let lap = |label: &str, stage: &mut std::time::Instant| {
        if timing {
            eprintln!(
                "[joint-c1-sidecar] {label}: {:.1} ms",
                stage.elapsed().as_secs_f64() * 1e3
            );
        }
        *stage = std::time::Instant::now();
    };
    outer.observe_label(JOINT_C1_TRANSCRIPT_LABEL);

    let link_prefix = link_plan.prove_c1_walk_deferred_prefix(witness, outer)?;
    let link_groups = link_prefix.groups();
    let link_states = link_prefix.states();
    lap("Link prefixes", &mut stage);

    outer.observe_label(BLOCK_SIDECAR_RECORDED_LABEL);
    let seed = outer.sample_f256();
    let mut child = FsLaneChallenger::new_c1(BLOCK_SIDECAR_CHILD_DOMAIN);
    child.observe_f256(seed);

    let block_prefix = block_plan.prove_c1_walk_deferred_prefix(witness, &mut child)?;
    let block_groups = block_prefix.groups();
    let block_states = block_prefix.states();
    lap("Block prefixes", &mut stage);

    let groups = link_groups
        .iter()
        .chain(&block_groups)
        .cloned()
        .collect::<Vec<_>>();
    let states = link_states
        .into_iter()
        .chain(block_states)
        .collect::<Vec<_>>();
    let (walk, terminals) = prove_ragged_deep_chain_walk(&states, &groups, &mut child);
    lap("nine-child walk", &mut stage);
    let mut terminals = terminals.into_iter();
    let link_terminals: [C1LaneClaimGroup; JOINT_C1_LINK_GROUPS] =
        std::array::from_fn(|_| terminals.next().expect("three Link walk terminals"));
    let block_terminals: [C1LaneClaimGroup; JOINT_C1_BLOCK_GROUPS] =
        std::array::from_fn(|_| terminals.next().expect("six Block walk terminals"));
    assert!(terminals.next().is_none(), "nine joint walk terminals");

    let (block, mut claims) = block_prefix.finish(&block_terminals, &mut child)?;
    lap("Block suffixes", &mut stage);
    let tail = child.sample_f256();
    outer.observe_f256(tail);
    let (link, link_claims) = link_prefix.finish(&link_terminals, outer)?;
    claims.extend(link_claims);
    lap("Link suffixes", &mut stage);

    Ok((
        JointC1RegionSidecarProof {
            version: JOINT_C1_SIDECAR_VERSION,
            link,
            block,
            walk,
        },
        claims,
    ))
}

pub(crate) fn verify_joint_c1_region_sidecar<Ch: Challenger>(
    link_vk: &LinkRegionSidecarVk,
    block_vk: &BlockRegionSidecarVk,
    total_vars: usize,
    proof: &JointC1RegionSidecarProof,
    outer: &mut Ch,
) -> Result<Vec<C1QuirkyDirectClaim>, RegionSidecarError> {
    verify_joint_c1_region_sidecar_with_child(link_vk, block_vk, total_vars, proof, outer, |seed| {
        let mut child = FsLaneChallenger::new_c1(BLOCK_SIDECAR_CHILD_DOMAIN);
        child.observe_f256(seed);
        child
    })
    .map(|(claims, _)| claims)
}

fn verify_joint_c1_region_sidecar_with_child<Outer, Child, MakeChild>(
    link_vk: &LinkRegionSidecarVk,
    block_vk: &BlockRegionSidecarVk,
    total_vars: usize,
    proof: &JointC1RegionSidecarProof,
    outer: &mut Outer,
    make_child: MakeChild,
) -> Result<(Vec<C1QuirkyDirectClaim>, Child), RegionSidecarError>
where
    Outer: Challenger,
    Child: Challenger,
    MakeChild: FnOnce(F256) -> Child,
{
    let timing = std::env::var_os("NOIDH_C1_VERIFY_TIMING").is_some();
    let total_started = std::time::Instant::now();
    if proof.version != JOINT_C1_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    outer.observe_label(JOINT_C1_TRANSCRIPT_LABEL);

    let link_prefix =
        verify_c1_link_region_walk_deferred_prefix(link_vk, total_vars, &proof.link, outer)?;
    let link_micros = total_started.elapsed().as_micros();
    let link_groups = link_prefix.groups();

    outer.observe_label(BLOCK_SIDECAR_RECORDED_LABEL);
    let seed = outer.sample_f256();
    let mut child = make_child(seed);

    let block_started = std::time::Instant::now();
    let block_prefix = verify_c1_block_region_walk_deferred_prefix(
        block_vk,
        total_vars,
        &proof.block,
        &mut child,
    )?;
    let block_micros = block_started.elapsed().as_micros();
    let block_groups = block_prefix.groups();
    let groups = link_groups
        .iter()
        .chain(&block_groups)
        .cloned()
        .collect::<Vec<_>>();
    let w_logs = groups
        .iter()
        .map(|group| group.point.len())
        .collect::<Vec<_>>();
    let walk_started = std::time::Instant::now();
    let terminals = verify_ragged_deep_chain_walk(&w_logs, &groups, &proof.walk, &mut child)
        .map_err(|_| RegionSidecarError::InvalidProof)?;
    let walk_micros = walk_started.elapsed().as_micros();
    let mut terminals = terminals.into_iter();
    let link_terminals: [C1LaneClaimGroup; JOINT_C1_LINK_GROUPS] =
        std::array::from_fn(|_| terminals.next().expect("three Link walk terminals"));
    let block_terminals: [C1LaneClaimGroup; JOINT_C1_BLOCK_GROUPS] =
        std::array::from_fn(|_| terminals.next().expect("six Block walk terminals"));
    if terminals.next().is_some() {
        return Err(RegionSidecarError::InvalidProof);
    }

    let block_finish_started = std::time::Instant::now();
    let mut claims = block_prefix.finish(&block_terminals, &mut child)?;
    let block_finish_micros = block_finish_started.elapsed().as_micros();
    let handoff_started = std::time::Instant::now();
    let tail = child.sample_f256();
    outer.observe_f256(tail);
    let handoff_micros = handoff_started.elapsed().as_micros();
    let link_finish_started = std::time::Instant::now();
    claims.extend(link_prefix.finish(&link_terminals, outer)?);
    let link_finish_micros = link_finish_started.elapsed().as_micros();
    if timing {
        eprintln!(
            "[joint-c1 verify] link_us={link_micros} block_us={block_micros} walk_us={walk_micros} block_finish_us={block_finish_micros} handoff_us={handoff_micros} link_finish_us={link_finish_micros} total_us={}",
            total_started.elapsed().as_micros(),
        );
    }
    Ok((claims, child))
}

pub(crate) fn verify_joint_c1_region_sidecar_post_commit<Ch: Challenger>(
    link_vk: &LinkRegionSidecarVk,
    block_vk: &BlockRegionSidecarVk,
    proof: &JointC1RegionSidecarProof,
    context: &mut FieldPostCommitVerifierContext<'_, Ch>,
) -> Result<(), RegionSidecarError> {
    let claims =
        verify_joint_c1_region_sidecar(link_vk, block_vk, context.total_vars(), proof, context)?;
    context.append_c1_claims(claims);
    Ok(())
}

pub(crate) fn verify_joint_c1_region_sidecar_post_commit_layout_captured<Ch: Challenger>(
    link_vk: &LinkRegionSidecarVk,
    block_vk: &BlockRegionSidecarVk,
    proof: &JointC1RegionSidecarProof,
    context: &mut FieldPostCommitVerifierContext<'_, Ch>,
    layout: DuplexLayout,
) -> Result<LayoutRecordedChannel, RegionSidecarError> {
    let (claims, child) = verify_joint_c1_region_sidecar_with_child(
        link_vk,
        block_vk,
        context.total_vars(),
        proof,
        context,
        |seed| {
            let mut child = LayoutRecordingChallenger::new_c1(BLOCK_SIDECAR_CHILD_DOMAIN, layout);
            child.observe_f256(seed);
            child
        },
    )?;
    context.append_c1_claims(claims);
    child.finish().map_err(|_| RegionSidecarError::InvalidProof)
}

pub(crate) fn verify_joint_c1_region_sidecar_trace_post_commit<C: FsChannelOps>(
    b: &mut FieldR1csBuilder,
    outer: &mut FieldPostCommitTraceContext<'_, C>,
    link_vk: &LinkRegionSidecarVk,
    block_vk: &BlockRegionSidecarVk,
    proof: &JointC1RegionSidecarProof,
) -> Result<RecordedChannel, RegionSidecarError> {
    if proof.version != JOINT_C1_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    outer.observe_label(b, JOINT_C1_TRANSCRIPT_LABEL);
    let link_prefix =
        verify_c1_link_region_walk_deferred_prefix_trace(b, outer, link_vk, &proof.link)?;
    let link_groups = link_prefix.groups();

    outer.observe_label(b, BLOCK_SIDECAR_RECORDED_LABEL);
    let seed = outer.sample_f256(b);
    let mut recorder = FsChannelUnionRecorder::new_c1(BLOCK_SIDECAR_CHILD_DOMAIN);
    recorder.observe_f256(b, &seed);
    let mut child = outer.child(&mut recorder);
    let block_prefix =
        verify_c1_block_region_walk_deferred_prefix_trace(b, &mut child, block_vk, &proof.block)?;
    let block_groups = block_prefix.groups();
    let groups = link_groups
        .iter()
        .chain(&block_groups)
        .cloned()
        .collect::<Vec<_>>();
    let w_logs = groups
        .iter()
        .map(|group| group.point.len())
        .collect::<Vec<_>>();
    let max_w_log = *w_logs
        .iter()
        .max()
        .ok_or(RegionSidecarError::InvalidProof)?;
    if proof.walk.layers.len() != N_ROUNDS
        || proof.walk.layers.iter().any(|layer| {
            layer.round_coeffs.len() != max_w_log || layer.next_values.len() != w_logs.len()
        })
    {
        return Err(RegionSidecarError::InvalidProof);
    }
    let walk = C1MultiDeepChainWalkProofTrace::alloc_ragged(b, &proof.walk, &w_logs);
    let terminals = verify_c1_ragged_deep_chain_walk_trace(b, &mut child, &w_logs, &groups, &walk);
    if terminals.len() != JOINT_C1_GROUPS {
        return Err(RegionSidecarError::InvalidProof);
    }
    let mut terminals = terminals.into_iter();
    let link_terminals =
        std::array::from_fn(|_| terminals.next().expect("checked three Link terminals"));
    let block_terminals =
        std::array::from_fn(|_| terminals.next().expect("checked six Block terminals"));
    if terminals.next().is_some() {
        return Err(RegionSidecarError::InvalidProof);
    }
    let claims = block_prefix.finish(b, &mut child, &block_terminals)?;
    child.append_c1_claims(claims);
    outer.adopt_child_claims(child);

    let tail = recorder.sample_f256(b);
    outer.observe_f256(b, &tail);
    let claims = link_prefix.finish(b, outer, &link_terminals)?;
    outer.append_c1_claims(claims);
    Ok(recorder.finish())
}
