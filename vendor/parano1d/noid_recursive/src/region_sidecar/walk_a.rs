// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Recording-free post-commit authority for Walk-A leaf unions.

use std::sync::Arc;

use noid_ivc_core::challenger::Challenger;
use noid_ivc_core::deep_chain::c1::C1LaneClaimGroup;
use noid_ivc_core::deep_chain::capsule_leaf::{
    c1_capsule_leaf_fixed_patterns, capsule_leaf_fixed_patterns, capsule_leaf_iv_flat,
    C1CapsuleLeafKind, C1_CAPSULE_LEAF_STRIDE, CAPSULE_LEAF_STRIDE,
};
use noid_ivc_core::deep_chain::leaf_hash::{
    slot_leaf_iv_flat, sponge_leaf_fixed_patterns, SpongeLeafRefs, SPONGE_LEAF_SLOTS,
};
use noid_ivc_core::deep_chain::relations::{claimed_refs, ColRef, FixedPattern};
use noid_ivc_core::deep_chain::schedule::{
    carry_selection_terms, flat_of_tower_u128, DuplexLayout, LaneSource,
};
use noid_ivc_core::deep_chain::source_tree::SourceTreeRefs;
use noid_ivc_core::deep_chain::spine::{
    spine_contract_wrap_fixed_patterns, spine_tree_exposure_terms, spine_tree_fixed_patterns,
    spine_wrap_fixed_patterns, SPINE_TREE_SLOTS, SPINE_V2_WRAP_SLOTS, SPINE_WRAP_SLOTS,
};
use noid_ivc_core::field::{F128, F256};
use noid_ivc_core::pcs::{C1QuirkyDirectClaim, QuirkyDirectClaim};
use noid_ivc_core::public_io::WitnessSlice;
use noid_poseidon2b::native::poseidon2b_hash_byte_slices;

use crate::acceptance::zk_auth_capsule_schedule::{
    ZkAuthCapsuleDuplexSchedules, ZK_AUTH_MAIN_PREFIX_SLOTS, ZK_AUTH_MAIN_TAIL_SLOTS,
    ZK_AUTH_OWNER_PREFIX_SLOTS, ZK_AUTH_OWNER_TAIL_SLOTS, ZK_AUTH_WALLET_A_MAIN_BRIDGE_SLOT,
    ZK_AUTH_WALLET_A_MAIN_TAIL_BASE, ZK_AUTH_WALLET_A_MID_BASE, ZK_AUTH_WALLET_A_OWNER_BRIDGE_SLOT,
    ZK_AUTH_WALLET_A_OWNER_TAIL_BASE, ZK_AUTH_WALLET_A_SOURCE_BASE, ZK_AUTH_WALLET_A_TILE_LOG,
};

use crate::acceptance::trace::region_source_binding::{
    common_period_ones, common_period_pattern, dyadic_region_bits, pattern_in_dyadic_region,
    prove_walk_a_union_with_challenger, union_ref_terms, verify_walk_a_union_with_challenger,
    SpineUnionSpec, SplitDuplexTailRefs, WalkAColumnClaim, WalkAUnionProof,
};
use crate::acceptance::trace::region_source_binding_c1::{
    prove_c1_walk_a_walk_prefix, prove_c1_walk_a_walk_suffix, verify_c1_walk_a_walk_prefix,
    verify_c1_walk_a_walk_suffix, C1WalkAColumnClaim, C1WalkAProverWalkPrefix,
    C1WalkAUnionWalkDeferredProof, C1WalkAVerifierWalkPrefix,
};

use super::bounded_decode::{
    preflight_fixed_proof, record_serde_attempt, FixedProofShape, ProofTailShape, RelationShape,
};
use super::{push_f128, push_usize, validate_c1_endpoint_lengths, witness_log, RegionSidecarError};

#[path = "walk_a_trace.rs"]
mod walk_a_trace;
pub use walk_a_trace::*;

pub const WALK_A_REGION_SIDECAR_VERSION: u8 = 1;
pub const WALK_A_WALLET_COMMITTED_COLUMNS: usize = 6;
pub const WALK_A_META_COMMITTED_COLUMNS: usize = 8;
pub const MAX_WALK_A_PATTERN_LOG: usize = 20;
/// The production classes cover at most the padded B255 class (`2^8` slots).
pub const MAX_WALK_A_TX_LOG: usize = 8;
/// Published selected capsule geometry.  VK validity must not depend on
/// debug-only reductions of the native prover's exercised query count.
pub const MAX_WALK_A_QUERY_LOG: usize = 6;

const MAX_WALK_A_FIXED_CELLS: usize = 1 << 22;
const WALK_A_LAYOUT_DIGEST_DOMAIN: &[u8] = b"NOID/REGION-SIDECAR/WALK-A-LAYOUT/V1";
const WALK_A_VK_DIGEST_DOMAIN: &[u8] = b"NOID/REGION-SIDECAR/WALK-A-VK/V1";
const WALK_A_SIDECAR_TRANSCRIPT_LABEL: &[u8] = b"history-region-sidecar-walk-a-v1";

const WALLET_IN0: usize = 0;
const WALLET_C0: usize = 2;
const META_KID0: usize = 0;
const META_IN0: usize = 2;
const META_C0: usize = 4;

/// Compact, typed description of the only two Walk-A layouts accepted by V1.
/// All fixed tables, refs, relation terms and spine re-pointing geometry are
/// reconstructed from this descriptor by both sides.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalkARegionDescriptor {
    /// Two capsule-leaf families, each containing `2^nq_log` tiles per tx.
    Wallet { tx_log: usize, nq_log: usize },
    /// Optional exact-state sponge and/or tx-body spine regions.
    Meta {
        tx_log: usize,
        exact_state_region_log: Option<usize>,
        spine_cap_log: Option<usize>,
    },
    /// V2 body spine with bounded object program and policy commitments.
    ObjectMeta {
        tx_log: usize,
        exact_state_region_log: Option<usize>,
        spine_cap_log: Option<usize>,
    },
}

impl WalkARegionDescriptor {
    fn tag(self) -> u8 {
        match self {
            Self::Wallet { .. } => 0,
            Self::Meta { .. } => 1,
            Self::ObjectMeta { .. } => 2,
        }
    }

    fn encode(self, bytes: &mut Vec<u8>) {
        bytes.push(self.tag());
        match self {
            Self::Wallet { tx_log, nq_log } => {
                push_usize(bytes, tx_log);
                push_usize(bytes, nq_log);
            }
            Self::Meta {
                tx_log,
                exact_state_region_log,
                spine_cap_log,
            }
            | Self::ObjectMeta {
                tx_log,
                exact_state_region_log,
                spine_cap_log,
            } => {
                push_usize(bytes, tx_log);
                encode_option_usize(bytes, exact_state_region_log);
                encode_option_usize(bytes, spine_cap_log);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum WalkARegionSlices {
    Wallet([WitnessSlice; WALK_A_WALLET_COMMITTED_COLUMNS]),
    Meta([WitnessSlice; WALK_A_META_COMMITTED_COLUMNS]),
}

impl WalkARegionSlices {
    fn as_slice(&self) -> &[WitnessSlice] {
        match self {
            Self::Wallet(slices) => slices,
            Self::Meta(slices) => slices,
        }
    }

    fn matches(&self, descriptor: WalkARegionDescriptor) -> bool {
        matches!(
            (self, descriptor),
            (Self::Wallet(_), WalkARegionDescriptor::Wallet { .. })
                | (Self::Meta(_), WalkARegionDescriptor::Meta { .. })
                | (Self::Meta(_), WalkARegionDescriptor::ObjectMeta { .. })
        )
    }
}

#[derive(Clone, Debug)]
struct CanonicalWalkAProtocol {
    w_log: usize,
    fixed: Arc<[FixedPattern]>,
    meta_c: [usize; 4],
    leaf_refs: Vec<(SpongeLeafRefs, usize)>,
    split_tails: Vec<SplitDuplexTailRefs>,
    es_sponge: Option<(SpongeLeafRefs, usize)>,
    spine: Option<SpineUnionSpec>,
    spine_region_base: Option<usize>,
}

/// Canonical verification key for one recording-free Walk-A vertical.
#[derive(Clone, Debug)]
pub struct WalkARegionVk {
    purpose: [u8; 32],
    descriptor: WalkARegionDescriptor,
    w_log: usize,
    slices: WalkARegionSlices,
    fixed: Arc<[FixedPattern]>,
    layout_digest: [u8; 32],
    protocol: Arc<CanonicalWalkAProtocol>,
}

impl PartialEq for WalkARegionVk {
    fn eq(&self, other: &Self) -> bool {
        self.purpose == other.purpose
            && self.descriptor == other.descriptor
            && self.w_log == other.w_log
            && self.slices == other.slices
            && self.fixed == other.fixed
            && self.layout_digest == other.layout_digest
    }
}

impl Eq for WalkARegionVk {}

impl WalkARegionVk {
    pub fn new_wallet(
        purpose: [u8; 32],
        tx_log: usize,
        nq_log: usize,
        slices: [WitnessSlice; WALK_A_WALLET_COMMITTED_COLUMNS],
    ) -> Result<Self, RegionSidecarError> {
        Self::new(
            purpose,
            WalkARegionDescriptor::Wallet { tx_log, nq_log },
            WalkARegionSlices::Wallet(slices),
        )
    }

    pub fn new_meta(
        purpose: [u8; 32],
        tx_log: usize,
        exact_state_region_log: Option<usize>,
        spine_cap_log: Option<usize>,
        slices: [WitnessSlice; WALK_A_META_COMMITTED_COLUMNS],
    ) -> Result<Self, RegionSidecarError> {
        Self::new(
            purpose,
            WalkARegionDescriptor::Meta {
                tx_log,
                exact_state_region_log,
                spine_cap_log,
            },
            WalkARegionSlices::Meta(slices),
        )
    }

    pub fn new_object_meta(
        purpose: [u8; 32],
        tx_log: usize,
        exact_state_region_log: Option<usize>,
        spine_cap_log: Option<usize>,
        slices: [WitnessSlice; WALK_A_META_COMMITTED_COLUMNS],
    ) -> Result<Self, RegionSidecarError> {
        Self::new(
            purpose,
            WalkARegionDescriptor::ObjectMeta {
                tx_log,
                exact_state_region_log,
                spine_cap_log,
            },
            WalkARegionSlices::Meta(slices),
        )
    }

    fn new(
        purpose: [u8; 32],
        descriptor: WalkARegionDescriptor,
        slices: WalkARegionSlices,
    ) -> Result<Self, RegionSidecarError> {
        let protocol = Arc::new(canonical_protocol(descriptor)?);
        let layout_digest = walk_a_layout_digest(descriptor, &protocol);
        let vk = Self {
            purpose,
            descriptor,
            w_log: protocol.w_log,
            slices,
            fixed: Arc::clone(&protocol.fixed),
            layout_digest,
            protocol,
        };
        vk.validate_structure()?;
        Ok(vk)
    }

    pub fn purpose(&self) -> &[u8; 32] {
        &self.purpose
    }

    pub fn descriptor(&self) -> WalkARegionDescriptor {
        self.descriptor
    }

    pub fn w_log(&self) -> usize {
        self.w_log
    }

    pub fn slices(&self) -> &[WitnessSlice] {
        self.slices.as_slice()
    }

    pub fn fixed(&self) -> &[FixedPattern] {
        &self.fixed
    }

    pub fn layout_digest(&self) -> &[u8; 32] {
        &self.layout_digest
    }

    /// Stable key digest absorbed after the enclosing witness commitment.
    pub fn transcript_digest(&self) -> [u8; 32] {
        let mut bytes = Vec::new();
        bytes.push(WALK_A_REGION_SIDECAR_VERSION);
        bytes.extend_from_slice(&self.purpose);
        self.descriptor.encode(&mut bytes);
        push_usize(&mut bytes, self.w_log());
        push_usize(&mut bytes, self.slices().len());
        for slice in self.slices() {
            push_usize(&mut bytes, slice.log2_len);
            push_usize(&mut bytes, slice.index);
        }
        bytes.extend_from_slice(&self.layout_digest);
        poseidon2b_hash_byte_slices(WALK_A_VK_DIGEST_DOMAIN, &[&bytes])
    }

    fn validate_structure(&self) -> Result<CanonicalWalkAProtocol, RegionSidecarError> {
        if !self.slices.matches(self.descriptor) {
            return Err(RegionSidecarError::UnsupportedVkShape);
        }
        let protocol = canonical_protocol(self.descriptor)?;
        if self.w_log != protocol.w_log
            || self.fixed != protocol.fixed
            || self.layout_digest != walk_a_layout_digest(self.descriptor, &protocol)
        {
            return Err(RegionSidecarError::UnsupportedVkShape);
        }
        let slices = self.slices();
        let base = slices[0].index;
        for (column, slice) in slices.iter().enumerate() {
            if slice.log2_len != protocol.w_log
                || slice.index
                    != base
                        .checked_add(column)
                        .ok_or(RegionSidecarError::BadSlice)?
            {
                return Err(RegionSidecarError::BadSlice);
            }
        }
        Ok(protocol)
    }

    fn validate_in_witness(
        &self,
        total_vars: usize,
    ) -> Result<CanonicalWalkAProtocol, RegionSidecarError> {
        let protocol = self.validate_structure()?;
        if self.slices().iter().any(|slice| !slice.fits(total_vars)) {
            return Err(RegionSidecarError::BadSlice);
        }
        Ok(protocol)
    }

    /// Per-proof C1 access to the protocol certified by the checked VK
    /// constructor. The only statement-dependent condition is that every
    /// committed slice fits the enclosing witness.
    fn certified_c1_protocol_in_witness(
        &self,
        total_vars: usize,
    ) -> Result<Arc<CanonicalWalkAProtocol>, RegionSidecarError> {
        if self.slices().iter().any(|slice| !slice.fits(total_vars)) {
            return Err(RegionSidecarError::BadSlice);
        }
        Ok(Arc::clone(&self.protocol))
    }
}

/// Prover-only Walk-A endpoints.  Committed and spine-exposure columns are
/// read or canonically extracted exclusively from the outer witness `z`.
pub struct WalkARegionProverPlan<'a> {
    vk: &'a WalkARegionVk,
    s0: &'a [Vec<F128>; 4],
    s_out: &'a [Vec<F128>; 4],
}

pub(crate) struct C1WalkARegionProverWalkContinuation<'a, 'z> {
    vk: &'a WalkARegionVk,
    total_vars: usize,
    protocol: Arc<CanonicalWalkAProtocol>,
    committed: Vec<&'z [F128]>,
    exposure_owned: Option<[Vec<F128>; 4]>,
    s0: &'a [Vec<F128>; 4],
    prefix: C1WalkAProverWalkPrefix,
}

impl C1WalkARegionProverWalkContinuation<'_, '_> {
    pub(crate) fn group(&self) -> &C1LaneClaimGroup {
        self.prefix.walk_group()
    }

    pub(crate) fn s0(&self) -> &[Vec<F128>; 4] {
        self.s0
    }

    pub(crate) fn finish<Ch: Challenger>(
        self,
        terminal: &C1LaneClaimGroup,
        challenger: &mut Ch,
    ) -> Result<(C1WalkARegionWalkDeferredProof, Vec<C1QuirkyDirectClaim>), RegionSidecarError>
    {
        let Self {
            vk,
            total_vars,
            protocol,
            committed,
            exposure_owned,
            s0: _,
            prefix,
        } = self;
        let exposure_refs = exposure_owned.as_ref().map(|columns| {
            [
                columns[0].as_slice(),
                columns[1].as_slice(),
                columns[2].as_slice(),
                columns[3].as_slice(),
            ]
        });
        let (authority, terminal_claims) = prove_c1_walk_a_walk_suffix(
            protocol.w_log,
            &protocol.fixed,
            &protocol.leaf_refs,
            &protocol.split_tails,
            protocol.es_sponge.as_ref(),
            protocol.spine.as_ref(),
            &committed,
            exposure_refs.as_ref(),
            prefix,
            terminal,
            challenger,
        );
        let claims = resolve_c1_walk_a_terminal_claims(vk, total_vars, terminal_claims)?;
        Ok((C1WalkARegionWalkDeferredProof::new(authority), claims))
    }
}

pub(crate) struct C1WalkARegionVerifierWalkContinuation<'a> {
    vk: &'a WalkARegionVk,
    total_vars: usize,
    protocol: Arc<CanonicalWalkAProtocol>,
    prefix: C1WalkAVerifierWalkPrefix<'a>,
}

impl C1WalkARegionVerifierWalkContinuation<'_> {
    pub(crate) fn group(&self) -> &C1LaneClaimGroup {
        self.prefix.walk_group()
    }

    pub(crate) fn finish<Ch: Challenger>(
        self,
        terminal: &C1LaneClaimGroup,
        challenger: &mut Ch,
    ) -> Result<Vec<C1QuirkyDirectClaim>, RegionSidecarError> {
        let terminal_claims = verify_c1_walk_a_walk_suffix(
            self.protocol.w_log,
            &self.protocol.fixed,
            &self.protocol.leaf_refs,
            &self.protocol.split_tails,
            self.protocol.es_sponge.as_ref(),
            self.protocol.spine.as_ref(),
            self.prefix,
            terminal,
            challenger,
        )
        .map_err(|_| RegionSidecarError::InvalidProof)?;
        resolve_c1_walk_a_terminal_claims(self.vk, self.total_vars, terminal_claims)
    }
}

impl<'a> WalkARegionProverPlan<'a> {
    pub fn new(
        vk: &'a WalkARegionVk,
        s0: &'a [Vec<F128>; 4],
        s_out: &'a [Vec<F128>; 4],
    ) -> Result<Self, RegionSidecarError> {
        let protocol = vk.validate_structure()?;
        let expected = 1usize << protocol.w_log;
        if s0.iter().any(|column| column.len() != expected)
            || s_out.iter().any(|column| column.len() != expected)
        {
            return Err(RegionSidecarError::BadWalkColumns);
        }
        Ok(Self { vk, s0, s_out })
    }

    pub(super) fn new_certified_c1(
        vk: &'a WalkARegionVk,
        s0: &'a [Vec<F128>; 4],
        s_out: &'a [Vec<F128>; 4],
    ) -> Result<Self, RegionSidecarError> {
        validate_c1_endpoint_lengths(vk.w_log, s0, s_out)?;
        Ok(Self { vk, s0, s_out })
    }

    pub(crate) fn prove_c1_walk_deferred_prefix<'z, Ch: Challenger>(
        &self,
        z: &'z [F128],
        challenger: &mut Ch,
    ) -> Result<C1WalkARegionProverWalkContinuation<'a, 'z>, RegionSidecarError> {
        let total_vars = witness_log(z)?;
        let protocol = self.vk.certified_c1_protocol_in_witness(total_vars)?;
        let committed = self
            .vk
            .slices()
            .iter()
            .map(|slice| &z[slice.start()..slice.start() + slice.len()])
            .collect::<Vec<_>>();
        let exposure_owned = extract_spine_exposure(&protocol, &committed)?;
        bind_walk_a_vk(challenger, self.vk);
        let prefix = prove_c1_walk_a_walk_prefix(
            protocol.w_log,
            &protocol.fixed,
            &protocol.meta_c,
            &committed,
            self.s_out,
            challenger,
        );
        Ok(C1WalkARegionProverWalkContinuation {
            vk: self.vk,
            total_vars,
            protocol,
            committed,
            exposure_owned,
            s0: self.s0,
            prefix,
        })
    }

    /// Must run inside the enclosing FieldR1cs post-commit callback on its
    /// exact challenger.  No recording or challenger-construction shortcut is
    /// exposed by this API.
    pub fn prove<Ch: Challenger>(
        &self,
        z: &[F128],
        challenger: &mut Ch,
    ) -> Result<(WalkARegionSidecarProof, Vec<QuirkyDirectClaim>), RegionSidecarError> {
        let total_vars = witness_log(z)?;
        let protocol = self.vk.validate_in_witness(total_vars)?;
        let committed = self
            .vk
            .slices()
            .iter()
            .map(|slice| &z[slice.start()..slice.start() + slice.len()])
            .collect::<Vec<_>>();
        let exposure_owned = extract_spine_exposure(&protocol, &committed)?;
        let exposure_refs = exposure_owned.as_ref().map(|columns| {
            [
                columns[0].as_slice(),
                columns[1].as_slice(),
                columns[2].as_slice(),
                columns[3].as_slice(),
            ]
        });

        bind_walk_a_vk(challenger, self.vk);
        let (authority, terminal) = prove_walk_a_union_with_challenger(
            protocol.w_log,
            &protocol.fixed,
            &protocol.meta_c,
            &protocol.leaf_refs,
            &protocol.split_tails,
            protocol.es_sponge.as_ref(),
            protocol.spine.as_ref(),
            &committed,
            self.s0,
            self.s_out,
            exposure_refs.as_ref(),
            challenger,
        );
        let claims = resolve_walk_a_terminal_claims(self.vk, total_vars, terminal)?;
        Ok((
            WalkARegionSidecarProof {
                version: WALK_A_REGION_SIDECAR_VERSION,
                authority,
            },
            claims,
        ))
    }
}

/// Serializable Walk-A authority without pending descriptors or shift
/// column/kind metadata.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct WalkARegionSidecarProof {
    version: u8,
    authority: WalkAUnionProof,
}

impl WalkARegionSidecarProof {
    pub fn byte_len(&self) -> usize {
        bincode::serialized_size(self).expect("Walk-A sidecar serialized length") as usize
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct C1WalkARegionWalkDeferredProof {
    version: u8,
    authority: C1WalkAUnionWalkDeferredProof,
}

impl C1WalkARegionWalkDeferredProof {
    pub(crate) fn new(authority: C1WalkAUnionWalkDeferredProof) -> Self {
        Self {
            version: WALK_A_REGION_SIDECAR_VERSION,
            authority,
        }
    }

    pub(crate) fn version(&self) -> u8 {
        self.version
    }

    pub(crate) fn authority(&self) -> &C1WalkAUnionWalkDeferredProof {
        &self.authority
    }
}

/// Decode one Walk-A sidecar only after an allocation-free exact bincode-v1
/// shape pass tied to the canonical class reconstructed from `vk`.
pub fn decode_walk_a_region_sidecar_bounded(
    vk: &WalkARegionVk,
    total_vars: usize,
    bytes: &[u8],
) -> Result<WalkARegionSidecarProof, RegionSidecarError> {
    let protocol = vk.validate_in_witness(total_vars)?;
    let shape = walk_a_proof_shape(&protocol);
    preflight_fixed_proof(bytes, &shape)?;
    record_serde_attempt();
    let proof: WalkARegionSidecarProof =
        bincode::deserialize(bytes).map_err(|_| RegionSidecarError::InvalidProof)?;
    if proof.version != WALK_A_REGION_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    walk_a_trace::preflight_walk_a_authority(&protocol, &proof.authority)?;
    Ok(proof)
}

fn walk_a_proof_shape(protocol: &CanonicalWalkAProtocol) -> FixedProofShape {
    let selection_values = claimed_refs(&carry_selection_terms(&protocol.meta_c, F128::ONE)).len();
    let substitution_refs = claimed_refs(&union_ref_terms(
        &protocol.leaf_refs,
        &protocol.split_tails,
        protocol.es_sponge.as_ref(),
        protocol.spine.as_ref(),
    ));
    let shifts = substitution_refs
        .iter()
        .filter(|reference| {
            matches!(
                reference,
                ColRef::CommittedShift(_) | ColRef::CommittedShift2(_)
            )
        })
        .count();
    let exposure_values =
        || claimed_refs(&spine_tree_exposure_terms([0, 1], [2, 3], 0, F128::ONE)).len();
    FixedProofShape {
        version: WALK_A_REGION_SIDECAR_VERSION,
        w_log: protocol.w_log,
        selection_values,
        substitution_values: substitution_refs.len(),
        shifts,
        tail: ProofTailShape::RelationOption(protocol.spine.as_ref().map(|spec| RelationShape {
            rounds: spec.expo_wlog(),
            values: exposure_values(),
        })),
    }
}

pub(super) fn walk_a_bounded_shape(
    vk: &WalkARegionVk,
    total_vars: usize,
) -> Result<FixedProofShape, RegionSidecarError> {
    let protocol = vk.certified_c1_protocol_in_witness(total_vars)?;
    Ok(walk_a_proof_shape(&protocol))
}

pub(crate) fn verify_c1_walk_a_region_walk_deferred_prefix<'a, Ch: Challenger>(
    vk: &'a WalkARegionVk,
    total_vars: usize,
    proof: &'a C1WalkARegionWalkDeferredProof,
    challenger: &mut Ch,
) -> Result<C1WalkARegionVerifierWalkContinuation<'a>, RegionSidecarError> {
    let timing = std::env::var_os("NOIDH_C1_VERIFY_TIMING").is_some();
    let total_started = std::time::Instant::now();
    let protocol = vk.certified_c1_protocol_in_witness(total_vars)?;
    let validate_micros = total_started.elapsed().as_micros();
    if proof.version() != WALK_A_REGION_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    bind_walk_a_vk(challenger, vk);
    let bind_micros = total_started.elapsed().as_micros() - validate_micros;
    let prefix_started = std::time::Instant::now();
    let prefix = verify_c1_walk_a_walk_prefix(
        protocol.w_log,
        &protocol.fixed,
        &protocol.meta_c,
        proof.authority().as_ref(),
        challenger,
    )
    .map_err(|_| RegionSidecarError::InvalidProof)?;
    if timing {
        eprintln!(
            "[walk-a-c1 prefix] w_log={} validate_us={validate_micros} bind_us={bind_micros} proof_us={} total_us={}",
            protocol.w_log,
            prefix_started.elapsed().as_micros(),
            total_started.elapsed().as_micros(),
        );
    }
    Ok(C1WalkARegionVerifierWalkContinuation {
        vk,
        total_vars,
        protocol,
        prefix,
    })
}

/// Verify one recording-free Walk-A vertical and derive all outer PCS claims
/// solely from the canonical VK and verified proof endpoints.
pub fn verify_walk_a_region_sidecar<Ch: Challenger>(
    vk: &WalkARegionVk,
    total_vars: usize,
    proof: &WalkARegionSidecarProof,
    challenger: &mut Ch,
) -> Result<Vec<QuirkyDirectClaim>, RegionSidecarError> {
    let protocol = vk.validate_in_witness(total_vars)?;
    if proof.version != WALK_A_REGION_SIDECAR_VERSION {
        return Err(RegionSidecarError::UnsupportedVersion);
    }
    bind_walk_a_vk(challenger, vk);
    let terminal = verify_walk_a_union_with_challenger(
        protocol.w_log,
        &protocol.fixed,
        &protocol.meta_c,
        &protocol.leaf_refs,
        &protocol.split_tails,
        protocol.es_sponge.as_ref(),
        protocol.spine.as_ref(),
        &proof.authority,
        challenger,
    )
    .map_err(|_| RegionSidecarError::InvalidProof)?;
    resolve_walk_a_terminal_claims(vk, total_vars, terminal)
}

fn push_dense_c1_leaf_family(
    fixed: &mut Vec<FixedPattern>,
    kind: C1CapsuleLeafKind,
    offset: usize,
    leaves: usize,
    block_log: usize,
) -> (SpongeLeafRefs, usize) {
    let block_slots = 1usize << block_log;
    let active_slots = kind.active_slots();
    assert!(offset + leaves * active_slots <= block_slots);
    let template = c1_capsule_leaf_fixed_patterns(kind);
    let iv = [template[1].table[0], template[2].table[0]];
    let mut region = vec![F128::ZERO; block_slots];
    let mut carry = vec![F128::ZERO; block_slots];
    let mut iv0 = vec![F128::ZERO; block_slots];
    let mut iv1 = vec![F128::ZERO; block_slots];
    for leaf in 0..leaves {
        let base = offset + leaf * active_slots;
        region[base..base + active_slots].fill(F128::ONE);
        carry[base + 1..base + active_slots].fill(F128::ONE);
        iv0[base] = iv[0];
        iv1[base] = iv[1];
    }
    let base = fixed.len();
    fixed.extend([
        FixedPattern::new(block_log, region),
        FixedPattern::new(block_log, carry),
        FixedPattern::new(block_log, iv0),
        FixedPattern::new(block_log, iv1),
    ]);
    (
        SpongeLeafRefs {
            in_: [WALLET_IN0, WALLET_IN0 + 1],
            c: std::array::from_fn(|lane| WALLET_C0 + lane),
            odd: base + 1,
            iv: [base + 2, base + 3],
        },
        base,
    )
}

fn push_split_duplex_tail(
    fixed: &mut Vec<FixedPattern>,
    layout: &DuplexLayout,
    prefix_slots: usize,
    expected_tail_slots: usize,
    bridge_slot: usize,
    tail_base: usize,
    block_log: usize,
) -> SplitDuplexTailRefs {
    let block_slots = 1usize << block_log;
    assert_eq!(tail_base, bridge_slot + 1);
    assert_eq!(layout.slots.len() - prefix_slots, expected_tail_slots);
    assert!(tail_base + expected_tail_slots <= block_slots);
    let mut region = vec![F128::ZERO; block_slots];
    let mut carry = vec![F128::ZERO; block_slots];
    let mut first = vec![F128::ZERO; block_slots];
    let mut consts: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; block_slots]);
    region[tail_base..tail_base + expected_tail_slots].fill(F128::ONE);
    carry[tail_base + 1..tail_base + expected_tail_slots].fill(F128::ONE);
    first[tail_base] = F128::ONE;
    for (local, slot) in layout.slots[prefix_slots..].iter().enumerate() {
        for lane in 0..2 {
            if let Some(LaneSource::Const(value)) = slot.lanes[lane] {
                consts[lane][tail_base + local] = flat_of_tower_u128(value);
            }
        }
    }
    let base = fixed.len();
    fixed.extend([
        FixedPattern::new(block_log, region),
        FixedPattern::new(block_log, carry),
        FixedPattern::new(block_log, first),
        FixedPattern::new(block_log, consts[0].clone()),
        FixedPattern::new(block_log, consts[1].clone()),
    ]);
    SplitDuplexTailRefs {
        a: [WALLET_IN0, WALLET_IN0 + 1],
        c: std::array::from_fn(|lane| WALLET_C0 + lane),
        region: base,
        carry: base + 1,
        first: base + 2,
        consts: [base + 3, base + 4],
    }
}

fn canonical_protocol(
    descriptor: WalkARegionDescriptor,
) -> Result<CanonicalWalkAProtocol, RegionSidecarError> {
    let protocol = match descriptor {
        WalkARegionDescriptor::Wallet { tx_log, nq_log } => {
            if tx_log > MAX_WALK_A_TX_LOG {
                return Err(RegionSidecarError::UnsupportedVkShape);
            }
            let tx_count = checked_pow2(tx_log)?;
            if nq_log > MAX_WALK_A_QUERY_LOG {
                return Err(RegionSidecarError::UnsupportedVkShape);
            }
            let nq = checked_pow2(nq_log)?;
            if nq_log == MAX_WALK_A_QUERY_LOG {
                let block_log = ZK_AUTH_WALLET_A_TILE_LOG;
                let block_slots = 1usize << block_log;
                let total_slots = tx_count
                    .checked_mul(block_slots)
                    .ok_or(RegionSidecarError::BadVk)?;
                let w_log = total_slots.trailing_zeros() as usize;
                preflight_w_log(w_log)?;

                let mut fixed = Vec::with_capacity(18);
                let leaf_refs = vec![
                    push_dense_c1_leaf_family(
                        &mut fixed,
                        C1CapsuleLeafKind::MixedSource,
                        ZK_AUTH_WALLET_A_SOURCE_BASE,
                        nq,
                        block_log,
                    ),
                    push_dense_c1_leaf_family(
                        &mut fixed,
                        C1CapsuleLeafKind::WideMid,
                        ZK_AUTH_WALLET_A_MID_BASE,
                        nq,
                        block_log,
                    ),
                ];
                let schedules = ZkAuthCapsuleDuplexSchedules::selected();
                let owner_layout = schedules.owner_layout();
                let main_layout = schedules.main_layout();
                let split_tails = vec![
                    push_split_duplex_tail(
                        &mut fixed,
                        &owner_layout,
                        ZK_AUTH_OWNER_PREFIX_SLOTS,
                        ZK_AUTH_OWNER_TAIL_SLOTS,
                        ZK_AUTH_WALLET_A_OWNER_BRIDGE_SLOT,
                        ZK_AUTH_WALLET_A_OWNER_TAIL_BASE,
                        block_log,
                    ),
                    push_split_duplex_tail(
                        &mut fixed,
                        &main_layout,
                        ZK_AUTH_MAIN_PREFIX_SLOTS,
                        ZK_AUTH_MAIN_TAIL_SLOTS,
                        ZK_AUTH_WALLET_A_MAIN_BRIDGE_SLOT,
                        ZK_AUTH_WALLET_A_MAIN_TAIL_BASE,
                        block_log,
                    ),
                ];
                let protocol = CanonicalWalkAProtocol {
                    w_log,
                    fixed: fixed.into(),
                    meta_c: std::array::from_fn(|lane| WALLET_C0 + lane),
                    leaf_refs,
                    split_tails,
                    es_sponge: None,
                    spine: None,
                    spine_region_base: None,
                };
                validate_fixed_preflight(protocol.w_log, &protocol.fixed)?;
                return Ok(protocol);
            }
            let family_slots = nq
                .checked_mul(CAPSULE_LEAF_STRIDE)
                .ok_or(RegionSidecarError::BadVk)?;
            let block_slots = family_slots
                .checked_mul(2)
                .ok_or(RegionSidecarError::BadVk)?;
            let total_slots = tx_count
                .checked_mul(block_slots)
                .ok_or(RegionSidecarError::BadVk)?;
            if !block_slots.is_power_of_two() || !total_slots.is_power_of_two() {
                return Err(RegionSidecarError::BadVk);
            }
            let block_log = block_slots.trailing_zeros() as usize;
            let w_log = total_slots.trailing_zeros() as usize;
            preflight_w_log(w_log)?;
            let fixed_cells = block_slots
                .checked_mul(8)
                .ok_or(RegionSidecarError::BadVk)?;
            if fixed_cells > MAX_WALK_A_FIXED_CELLS {
                return Err(RegionSidecarError::UnsupportedVkShape);
            }

            let mut fixed = Vec::with_capacity(8);
            let mut leaf_refs = Vec::with_capacity(2);
            for family in 0..2 {
                let base = fixed.len();
                let offset = family * family_slots;
                fixed.push(common_period_ones(offset, family_slots, block_log));
                for pattern in capsule_leaf_fixed_patterns(capsule_leaf_iv_flat()) {
                    fixed.push(common_period_pattern(&pattern.table, offset, nq, block_log));
                }
                leaf_refs.push((
                    SpongeLeafRefs {
                        in_: [WALLET_IN0, WALLET_IN0 + 1],
                        c: std::array::from_fn(|lane| WALLET_C0 + lane),
                        odd: base + 1,
                        iv: [base + 2, base + 3],
                    },
                    base,
                ));
            }
            CanonicalWalkAProtocol {
                w_log,
                fixed: fixed.into(),
                meta_c: std::array::from_fn(|lane| WALLET_C0 + lane),
                leaf_refs,
                split_tails: Vec::new(),
                es_sponge: None,
                spine: None,
                spine_region_base: None,
            }
        }
        WalkARegionDescriptor::Meta {
            tx_log,
            exact_state_region_log,
            spine_cap_log,
        } => canonical_meta_protocol(tx_log, exact_state_region_log, spine_cap_log, false)?,
        WalkARegionDescriptor::ObjectMeta {
            tx_log,
            exact_state_region_log,
            spine_cap_log,
        } => canonical_meta_protocol(tx_log, exact_state_region_log, spine_cap_log, true)?,
    };
    validate_fixed_preflight(protocol.w_log, &protocol.fixed)?;
    Ok(protocol)
}

fn canonical_meta_protocol(
    tx_log: usize,
    exact_state_region_log: Option<usize>,
    spine_cap_log: Option<usize>,
    objects: bool,
) -> Result<CanonicalWalkAProtocol, RegionSidecarError> {
    let wrap_slots = if objects {
        SPINE_V2_WRAP_SLOTS
    } else {
        SPINE_WRAP_SLOTS
    };
    if tx_log > MAX_WALK_A_TX_LOG {
        return Err(RegionSidecarError::UnsupportedVkShape);
    }
    if exact_state_region_log.is_none() && spine_cap_log.is_none() {
        return Err(RegionSidecarError::UnsupportedVkShape);
    }
    let tx_count = checked_pow2(tx_log)?;
    let es_slots = match exact_state_region_log {
        Some(log) => {
            let slots = checked_pow2(log)?;
            if slots < SPONGE_LEAF_SLOTS {
                return Err(RegionSidecarError::UnsupportedVkShape);
            }
            Some(slots)
        }
        None => None,
    };
    let spine_geometry = match spine_cap_log {
        Some(cap_log) => {
            let cap = checked_pow2(cap_log)?;
            let live = cap
                .checked_mul(
                    SPINE_TREE_SLOTS
                        .checked_add(wrap_slots)
                        .ok_or(RegionSidecarError::BadVk)?,
                )
                .ok_or(RegionSidecarError::BadVk)?;
            let block_slots = live
                .checked_next_power_of_two()
                .ok_or(RegionSidecarError::BadVk)?;
            let region_slots = tx_count
                .checked_mul(block_slots)
                .ok_or(RegionSidecarError::BadVk)?;
            Some((cap_log, cap, block_slots, region_slots))
        }
        None => None,
    };
    let spine_slots = spine_geometry.map(|(_, _, _, slots)| slots);
    let both = es_slots.is_some() && spine_slots.is_some();
    let wallet_overflow = matches!(
        (tx_log, exact_state_region_log, spine_cap_log),
        (5, Some(10), Some(0)) | (8, Some(13), Some(0))
    ) || (objects
        && super::block::object_block_geometries().any(|geometry| {
            tx_log == geometry.tx_log
                && exact_state_region_log == Some(geometry.exact_state_region_log)
                && spine_cap_log == Some(geometry.spine_cap_log)
        }));
    let overflow_family_slots = if wallet_overflow {
        tx_count
            .checked_mul(C1_CAPSULE_LEAF_STRIDE)
            .ok_or(RegionSidecarError::BadVk)?
    } else {
        0
    };
    let first_region_live = es_slots
        .unwrap_or(0)
        .checked_add(
            overflow_family_slots
                .checked_mul(2)
                .ok_or(RegionSidecarError::BadVk)?,
        )
        .ok_or(RegionSidecarError::BadVk)?;
    let first_region_slots = if first_region_live == 0 {
        0
    } else {
        first_region_live
            .checked_next_power_of_two()
            .ok_or(RegionSidecarError::BadVk)?
    };
    let half = first_region_slots.max(spine_slots.unwrap_or(0));
    if half == 0 || !half.is_power_of_two() {
        return Err(RegionSidecarError::BadVk);
    }
    let total_slots = if both {
        half.checked_mul(2).ok_or(RegionSidecarError::BadVk)?
    } else {
        half
    };
    let w_log = total_slots.trailing_zeros() as usize;
    preflight_w_log(w_log)?;
    // Allocation-free fixed-table budget. ES contributes one scalar region
    // table plus three two-slot sponge tables; each of the nine spine
    // patterns expands to one full per-tx block table.
    let mut fixed_cells = if es_slots.is_some() { 7usize } else { 0 };
    if let Some((_, _, block_slots, _)) = spine_geometry {
        fixed_cells = fixed_cells
            .checked_add(
                block_slots
                    .checked_mul(9)
                    .ok_or(RegionSidecarError::BadVk)?,
            )
            .ok_or(RegionSidecarError::BadVk)?;
    }
    if fixed_cells > MAX_WALK_A_FIXED_CELLS {
        return Err(RegionSidecarError::UnsupportedVkShape);
    }
    let es_base = 0usize;
    let spine_base = if both { half } else { 0 };

    let mut fixed = Vec::new();
    let es_sponge = es_slots.map(|slots| {
        let base = fixed.len();
        fixed.push(pattern_in_dyadic_region(
            FixedPattern::new(0, vec![F128::ONE]),
            es_base,
            slots,
            w_log,
        ));
        for pattern in sponge_leaf_fixed_patterns(slot_leaf_iv_flat()) {
            fixed.push(pattern_in_dyadic_region(pattern, es_base, slots, w_log));
        }
        (
            SpongeLeafRefs {
                in_: [META_IN0, META_IN0 + 1],
                c: std::array::from_fn(|lane| META_C0 + lane),
                odd: base + 1,
                iv: [base + 2, base + 3],
            },
            base,
        )
    });

    let mut leaf_refs = Vec::new();
    if wallet_overflow {
        let overflow_base = es_slots.expect("selected Meta-A includes exact state");
        for (family, kind) in [C1CapsuleLeafKind::MixedSource, C1CapsuleLeafKind::WideMid]
            .into_iter()
            .enumerate()
        {
            let region_base = overflow_base + family * overflow_family_slots;
            let base = fixed.len();
            fixed.push(pattern_in_dyadic_region(
                FixedPattern::new(0, vec![F128::ONE]),
                region_base,
                overflow_family_slots,
                w_log,
            ));
            for pattern in c1_capsule_leaf_fixed_patterns(kind) {
                fixed.push(pattern_in_dyadic_region(
                    pattern,
                    region_base,
                    overflow_family_slots,
                    w_log,
                ));
            }
            leaf_refs.push((
                SpongeLeafRefs {
                    in_: [META_IN0, META_IN0 + 1],
                    c: std::array::from_fn(|lane| META_C0 + lane),
                    odd: base + 1,
                    iv: [base + 2, base + 3],
                },
                base,
            ));
        }
    }

    let spine = if let Some((cap_log, cap, block_slots, region_slots)) = spine_geometry {
        let base = fixed.len();
        let block_log = block_slots.trailing_zeros() as usize;
        for pattern in spine_tree_fixed_patterns() {
            let tiled = common_period_pattern(&pattern.table, 0, cap, block_log);
            fixed.push(pattern_in_dyadic_region(
                tiled,
                spine_base,
                region_slots,
                w_log,
            ));
        }
        let wrap_base = cap
            .checked_mul(SPINE_TREE_SLOTS)
            .ok_or(RegionSidecarError::BadVk)?;
        let wrap_patterns = if objects {
            spine_contract_wrap_fixed_patterns()
        } else {
            spine_wrap_fixed_patterns()
        };
        for pattern in wrap_patterns {
            let tiled = common_period_pattern(&pattern.table, wrap_base, cap, block_log);
            fixed.push(pattern_in_dyadic_region(
                tiled,
                spine_base,
                region_slots,
                w_log,
            ));
        }
        Some(SpineUnionSpec {
            tree_refs: SourceTreeRefs {
                code: [META_IN0, META_IN0 + 1],
                kid: [META_KID0, META_KID0 + 1],
                c: std::array::from_fn(|lane| META_C0 + lane),
                even_int: base,
                odd_int: base + 1,
                leafodd: base + 2,
                iv: [base + 3, base + 4],
            },
            wrap_refs: SpongeLeafRefs {
                in_: [META_IN0, META_IN0 + 1],
                c: std::array::from_fn(|lane| META_C0 + lane),
                odd: base + 6,
                iv: [base + 7, base + 8],
            },
            wrap_region: base + 5,
            kid_meta: [META_KID0, META_KID0 + 1],
            c_meta: [META_C0, META_C0 + 1],
            cap_log,
            tx_log,
            tree_base: 0,
            block_log_a: block_log,
            walk_high_bits: dyadic_region_bits(spine_base, region_slots, w_log)
                .into_iter()
                .map(|bit| if bit { F128::ONE } else { F128::ZERO })
                .collect(),
        })
    } else {
        None
    };

    Ok(CanonicalWalkAProtocol {
        w_log,
        fixed: fixed.into(),
        meta_c: std::array::from_fn(|lane| META_C0 + lane),
        leaf_refs,
        split_tails: Vec::new(),
        es_sponge,
        spine,
        spine_region_base: spine_geometry.map(|_| spine_base),
    })
}

fn extract_spine_exposure(
    protocol: &CanonicalWalkAProtocol,
    committed: &[&[F128]],
) -> Result<Option<[Vec<F128>; 4]>, RegionSidecarError> {
    let Some(spec) = protocol.spine.as_ref() else {
        return Ok(None);
    };
    if committed.len() != WALK_A_META_COMMITTED_COLUMNS {
        return Err(RegionSidecarError::BadWalkColumns);
    }
    let base = protocol
        .spine_region_base
        .ok_or(RegionSidecarError::BadVk)?;
    let tx_count = checked_pow2(spec.tx_log)?;
    let cap = checked_pow2(spec.cap_log)?;
    let block_slots = checked_pow2(spec.block_log_a)?;
    let instances = tx_count.checked_mul(cap).ok_or(RegionSidecarError::BadVk)?;
    let kid_len = instances
        .checked_mul(SPINE_TREE_SLOTS / 2)
        .ok_or(RegionSidecarError::BadVk)?;
    let c_len = instances
        .checked_mul(SPINE_TREE_SLOTS)
        .ok_or(RegionSidecarError::BadVk)?;
    let mut output = [
        Vec::with_capacity(kid_len),
        Vec::with_capacity(kid_len),
        Vec::with_capacity(c_len),
        Vec::with_capacity(c_len),
    ];
    for tx in 0..tx_count {
        for instance in 0..cap {
            let tree = base
                .checked_add(
                    tx.checked_mul(block_slots)
                        .ok_or(RegionSidecarError::BadVk)?,
                )
                .and_then(|offset| offset.checked_add(spec.tree_base))
                .and_then(|offset| offset.checked_add(instance.checked_mul(SPINE_TREE_SLOTS)?))
                .ok_or(RegionSidecarError::BadVk)?;
            let kid_end = tree
                .checked_add(SPINE_TREE_SLOTS / 2)
                .ok_or(RegionSidecarError::BadVk)?;
            let c_end = tree
                .checked_add(SPINE_TREE_SLOTS)
                .ok_or(RegionSidecarError::BadVk)?;
            if c_end > committed[0].len() {
                return Err(RegionSidecarError::BadWalkColumns);
            }
            output[0].extend_from_slice(&committed[META_KID0][tree..kid_end]);
            output[1].extend_from_slice(&committed[META_KID0 + 1][tree..kid_end]);
            output[2].extend_from_slice(&committed[META_C0][tree..c_end]);
            output[3].extend_from_slice(&committed[META_C0 + 1][tree..c_end]);
        }
    }
    if output[0].len() != (1usize << spec.expo_wlog())
        || output[1].len() != output[0].len()
        || output[2].len() != output[0].len() * 2
        || output[3].len() != output[2].len()
    {
        return Err(RegionSidecarError::BadWalkColumns);
    }
    Ok(Some(output))
}

fn resolve_walk_a_terminal_claims(
    vk: &WalkARegionVk,
    total_vars: usize,
    terminal: Vec<WalkAColumnClaim>,
) -> Result<Vec<QuirkyDirectClaim>, RegionSidecarError> {
    let slices = vk.slices();
    let mut claims = Vec::with_capacity(terminal.len());
    for claim in terminal {
        let slice = *slices
            .get(claim.column)
            .ok_or(RegionSidecarError::InvalidProof)?;
        if claim.point.len() != slice.log2_len {
            return Err(RegionSidecarError::InvalidProof);
        }
        let mut x_rest = claim.point;
        x_rest.extend(slice.prefix_coords(total_vars));
        claims.push(QuirkyDirectClaim {
            z_skip: F128::ZERO,
            k_skip: 0,
            x_rest,
            value: claim.value,
        });
    }
    Ok(claims)
}

fn resolve_c1_walk_a_terminal_claims(
    vk: &WalkARegionVk,
    total_vars: usize,
    terminal: Vec<C1WalkAColumnClaim>,
) -> Result<Vec<C1QuirkyDirectClaim>, RegionSidecarError> {
    let slices = vk.slices();
    let mut claims = Vec::with_capacity(terminal.len());
    for claim in terminal {
        let slice = *slices
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
                .map(F256::from_base),
        );
        claims.push(C1QuirkyDirectClaim {
            z_skip: F256::ZERO,
            k_skip: 0,
            x_rest,
            value: claim.value,
        });
    }
    Ok(claims)
}

fn bind_walk_a_vk<Ch: Challenger>(challenger: &mut Ch, vk: &WalkARegionVk) {
    challenger.observe_label(WALK_A_SIDECAR_TRANSCRIPT_LABEL);
    challenger.observe_bytes(&vk.transcript_digest());
}

fn walk_a_layout_digest(
    descriptor: WalkARegionDescriptor,
    protocol: &CanonicalWalkAProtocol,
) -> [u8; 32] {
    let mut bytes = Vec::new();
    bytes.push(WALK_A_REGION_SIDECAR_VERSION);
    descriptor.encode(&mut bytes);
    push_usize(&mut bytes, protocol.w_log);
    for column in protocol.meta_c {
        push_usize(&mut bytes, column);
    }
    push_usize(&mut bytes, protocol.leaf_refs.len());
    for (refs, region) in &protocol.leaf_refs {
        encode_sponge_refs(&mut bytes, refs, *region);
    }
    push_usize(&mut bytes, protocol.split_tails.len());
    for refs in &protocol.split_tails {
        for index in refs.a.into_iter().chain(refs.c).chain([
            refs.region,
            refs.carry,
            refs.first,
            refs.consts[0],
            refs.consts[1],
        ]) {
            push_usize(&mut bytes, index);
        }
    }
    match protocol.es_sponge.as_ref() {
        None => bytes.push(0),
        Some((refs, region)) => {
            bytes.push(1);
            encode_sponge_refs(&mut bytes, refs, *region);
        }
    }
    match protocol.spine.as_ref() {
        None => bytes.push(0),
        Some(spec) => {
            bytes.push(1);
            encode_source_tree_refs(&mut bytes, &spec.tree_refs);
            encode_sponge_refs(&mut bytes, &spec.wrap_refs, spec.wrap_region);
            for index in spec.kid_meta.into_iter().chain(spec.c_meta) {
                push_usize(&mut bytes, index);
            }
            for value in [spec.cap_log, spec.tx_log, spec.tree_base, spec.block_log_a] {
                push_usize(&mut bytes, value);
            }
            push_usize(&mut bytes, spec.walk_high_bits.len());
            for value in &spec.walk_high_bits {
                push_f128(&mut bytes, *value);
            }
            push_usize(
                &mut bytes,
                protocol.spine_region_base.expect("spine region base"),
            );
        }
    }
    push_usize(&mut bytes, protocol.fixed.len());
    for pattern in protocol.fixed.iter() {
        encode_fixed_pattern(&mut bytes, pattern);
    }
    poseidon2b_hash_byte_slices(WALK_A_LAYOUT_DIGEST_DOMAIN, &[&bytes])
}

fn validate_fixed_preflight(
    w_log: usize,
    fixed: &[FixedPattern],
) -> Result<(), RegionSidecarError> {
    let mut cells = 0usize;
    for pattern in fixed {
        let expected = checked_pow2(pattern.low_log)?;
        if pattern.low_log > w_log || pattern.table.len() != expected {
            return Err(RegionSidecarError::UnsupportedVkShape);
        }
        if let Some((first, bits)) = &pattern.hi_gate {
            if *first < pattern.low_log
                || bits.is_empty()
                || first.checked_add(bits.len()) != Some(w_log)
            {
                return Err(RegionSidecarError::UnsupportedVkShape);
            }
        }
        cells = cells
            .checked_add(pattern.table.len())
            .ok_or(RegionSidecarError::BadVk)?;
    }
    if cells > MAX_WALK_A_FIXED_CELLS {
        return Err(RegionSidecarError::UnsupportedVkShape);
    }
    Ok(())
}

fn preflight_w_log(w_log: usize) -> Result<(), RegionSidecarError> {
    if w_log == 0 || w_log > MAX_WALK_A_PATTERN_LOG || w_log >= usize::BITS as usize {
        return Err(RegionSidecarError::BadVk);
    }
    Ok(())
}

fn checked_pow2(log: usize) -> Result<usize, RegionSidecarError> {
    if log >= usize::BITS as usize {
        return Err(RegionSidecarError::BadVk);
    }
    Ok(1usize << log)
}

fn encode_option_usize(bytes: &mut Vec<u8>, value: Option<usize>) {
    match value {
        None => bytes.push(0),
        Some(value) => {
            bytes.push(1);
            push_usize(bytes, value);
        }
    }
}

fn encode_fixed_pattern(bytes: &mut Vec<u8>, pattern: &FixedPattern) {
    push_usize(bytes, pattern.low_log);
    push_usize(bytes, pattern.table.len());
    for value in &pattern.table {
        push_f128(bytes, *value);
    }
    match &pattern.hi_gate {
        None => bytes.push(0),
        Some((first, bits)) => {
            bytes.push(1);
            push_usize(bytes, *first);
            push_usize(bytes, bits.len());
            bytes.extend(bits.iter().map(|bit| u8::from(*bit)));
        }
    }
}

fn encode_sponge_refs(bytes: &mut Vec<u8>, refs: &SpongeLeafRefs, region: usize) {
    for index in refs
        .in_
        .into_iter()
        .chain(refs.c)
        .chain(std::iter::once(refs.odd))
        .chain(refs.iv)
        .chain(std::iter::once(region))
    {
        push_usize(bytes, index);
    }
}

fn encode_source_tree_refs(bytes: &mut Vec<u8>, refs: &SourceTreeRefs) {
    for index in refs
        .code
        .into_iter()
        .chain(refs.kid)
        .chain(refs.c)
        .chain(std::iter::once(refs.even_int))
        .chain(std::iter::once(refs.odd_int))
        .chain(std::iter::once(refs.leafodd))
        .chain(refs.iv)
    {
        push_usize(bytes, index);
    }
}

#[cfg(test)]
pub(in crate::region_sidecar) mod tests {
    use super::super::bounded_decode;
    use super::*;
    use crate::acceptance::trace::region_source_binding::run_union_native;
    use crate::acceptance::trace::self_verify::{
        alloc_flat_digest, verify_field_trace_deferred_region_with_post_commit_context,
        FieldR1csProofTrace,
    };
    use noid_ivc_core::challenger::{Challenger, FsLaneChallenger};
    use noid_ivc_core::deep_chain::capsule_leaf::{
        build_capsule_leaf_columns, CapsuleLeafData, CAPSULE_LEAF_SYMBOLS,
    };
    use noid_ivc_core::deep_chain::leaf_hash::build_sponge_leaf_columns;
    use noid_ivc_core::deep_chain::relations::{
        prove_column_relation, verify_column_relation, RelationColumns,
    };
    use noid_ivc_core::deep_chain::schedule::carry_selection_terms;
    use noid_ivc_core::deep_chain::source_tree::run_perm;
    use noid_ivc_core::deep_chain::spine::{build_spine_instance_columns, SpineInstanceFlat};
    use noid_ivc_core::field_circuit::{FieldR1csBuilder, FsChannelTrace, LinExpr};
    use noid_ivc_core::field_r1cs::FieldR1cs;
    use noid_ivc_core::lincheck::build_eq_table;
    use noid_ivc_core::pcs::{self, Commitment, PcsParams};
    use noid_ivc_core::proof::{FieldR1csProof, FieldShape};
    use noid_ivc_core::public_io::PublicIoSpec;
    use noid_ivc_core::verifier::{
        verify_field_deferred_matrix_with_post_commit_context, verify_field_with_public_io,
        verify_field_with_public_io_and_post_commit, VerifyError,
    };
    use noid_ivc_prover::field_prover::{
        prove_field_with_public_io_and_post_commit,
        prove_field_with_public_io_and_post_commit_context,
    };

    const DIRECT_DOMAIN: &[u8] = b"walk-a-sidecar-direct-v1";
    const FIELD_DOMAIN: &[u8] = b"walk-a-sidecar-field-v1";
    const TRACE_AUTHORITY_DOMAIN: &[u8] = b"walk-a-sidecar-trace-authority-v1";
    const TRACE_CLASS_DIGEST: [u8; 32] = [0xA7; 32];

    struct Fixture {
        descriptor: WalkARegionDescriptor,
        committed: Vec<Vec<F128>>,
        s0: [Vec<F128>; 4],
        s_out: [Vec<F128>; 4],
    }

    impl Fixture {
        fn w_log(&self) -> usize {
            self.committed[0].len().trailing_zeros() as usize
        }

        fn packed(&self) -> (Vec<F128>, Vec<WitnessSlice>) {
            let w = 1usize << self.w_log();
            let total = (self.committed.len() * w).next_power_of_two();
            let mut z = vec![F128::ZERO; total];
            for (column, values) in self.committed.iter().enumerate() {
                z[column * w..(column + 1) * w].copy_from_slice(values);
            }
            let slices = (0..self.committed.len())
                .map(|index| WitnessSlice {
                    log2_len: self.w_log(),
                    index,
                })
                .collect();
            (z, slices)
        }

        fn vk(&self, purpose: [u8; 32], slices: &[WitnessSlice]) -> WalkARegionVk {
            match self.descriptor {
                WalkARegionDescriptor::Wallet { tx_log, nq_log } => WalkARegionVk::new_wallet(
                    purpose,
                    tx_log,
                    nq_log,
                    slices.try_into().expect("six wallet slices"),
                )
                .unwrap(),
                WalkARegionDescriptor::Meta {
                    tx_log,
                    exact_state_region_log,
                    spine_cap_log,
                } => WalkARegionVk::new_meta(
                    purpose,
                    tx_log,
                    exact_state_region_log,
                    spine_cap_log,
                    slices.try_into().expect("eight meta slices"),
                )
                .unwrap(),
                WalkARegionDescriptor::ObjectMeta {
                    tx_log,
                    exact_state_region_log,
                    spine_cap_log,
                } => WalkARegionVk::new_object_meta(
                    purpose,
                    tx_log,
                    exact_state_region_log,
                    spine_cap_log,
                    slices.try_into().expect("eight meta slices"),
                )
                .unwrap(),
            }
        }
    }

    fn wallet_fixture() -> Fixture {
        let descriptor = WalkARegionDescriptor::Wallet {
            tx_log: 0,
            nq_log: 0,
        };
        let protocol = canonical_protocol(descriptor).unwrap();
        let w = 1usize << protocol.w_log;
        let mut committed = vec![vec![F128::ZERO; w]; WALK_A_WALLET_COMMITTED_COLUMNS];
        let mut s0: [Vec<F128>; 4] = std::array::from_fn(|_| vec![F128::ZERO; w]);
        let mut s_out: [Vec<F128>; 4] = std::array::from_fn(|_| vec![F128::ZERO; w]);
        for family in 0..2 {
            let leaf = CapsuleLeafData {
                msg_log: 12 + family,
                leaf_index: 3 + family,
                syms: std::array::from_fn(|index| {
                    F128::new((100 * family + index + 1) as u64, (index * 7) as u64)
                }),
            };
            let (columns, _) = build_capsule_leaf_columns(&[leaf], 4);
            let offset = family * CAPSULE_LEAF_STRIDE;
            for lane in 0..2 {
                committed[WALLET_IN0 + lane][offset..offset + CAPSULE_LEAF_STRIDE]
                    .copy_from_slice(&columns.in_[lane]);
            }
            for lane in 0..4 {
                committed[WALLET_C0 + lane][offset..offset + CAPSULE_LEAF_STRIDE]
                    .copy_from_slice(&columns.c[lane]);
                s0[lane][offset..offset + CAPSULE_LEAF_STRIDE].copy_from_slice(&columns.s0[lane]);
                s_out[lane][offset..offset + CAPSULE_LEAF_STRIDE]
                    .copy_from_slice(&columns.s_out[lane]);
            }
        }
        Fixture {
            descriptor,
            committed,
            s0,
            s_out,
        }
    }

    fn meta_fixture(exact_state: bool, spine: bool) -> Fixture {
        meta_fixture_profile(exact_state, spine, false)
    }

    fn meta_fixture_profile(exact_state: bool, spine: bool, objects: bool) -> Fixture {
        let descriptor = if objects {
            WalkARegionDescriptor::ObjectMeta {
                tx_log: 0,
                exact_state_region_log: exact_state.then_some(1),
                spine_cap_log: spine.then_some(0),
            }
        } else {
            WalkARegionDescriptor::Meta {
                tx_log: 0,
                exact_state_region_log: exact_state.then_some(1),
                spine_cap_log: spine.then_some(0),
            }
        };
        let protocol = canonical_protocol(descriptor).unwrap();
        let w = 1usize << protocol.w_log;
        let (ghost_s0, ghost_out) = run_perm([F128::ZERO; 4]);
        let mut committed = vec![vec![F128::ZERO; w]; WALK_A_META_COMMITTED_COLUMNS];
        let mut s0: [Vec<F128>; 4] = std::array::from_fn(|lane| vec![ghost_s0[lane]; w]);
        let mut s_out: [Vec<F128>; 4] = std::array::from_fn(|lane| vec![ghost_out[lane]; w]);
        for lane in 0..4 {
            committed[META_C0 + lane].fill(ghost_out[lane]);
        }

        if exact_state {
            let (columns, _) = build_sponge_leaf_columns(
                &[(F128::new(17, 1), F128::new(19, 2), F128::new(23, 3))],
                1,
            );
            for lane in 0..2 {
                committed[META_IN0 + lane][..SPONGE_LEAF_SLOTS].copy_from_slice(&columns.in_[lane]);
            }
            for lane in 0..4 {
                committed[META_C0 + lane][..SPONGE_LEAF_SLOTS].copy_from_slice(&columns.c[lane]);
                s0[lane][..SPONGE_LEAF_SLOTS].copy_from_slice(&columns.s0[lane]);
                s_out[lane][..SPONGE_LEAF_SLOTS].copy_from_slice(&columns.s_out[lane]);
            }
        }

        if spine {
            let instance = SpineInstanceFlat {
                leaves: std::array::from_fn(|leaf| {
                    [
                        F128::new((2 * leaf + 1) as u64, 0xA5),
                        F128::new((2 * leaf + 2) as u64, 0x5A),
                    ]
                }),
            };
            let columns = if objects {
                noid_ivc_core::deep_chain::spine::build_spine_instance_columns_with_contract(
                    &instance, None,
                )
            } else {
                build_spine_instance_columns(&instance)
            };
            let wrap_slots = if objects {
                SPINE_V2_WRAP_SLOTS
            } else {
                SPINE_WRAP_SLOTS
            };
            let base = protocol.spine_region_base.unwrap();
            let wrap = base + SPINE_TREE_SLOTS;
            for lane in 0..2 {
                committed[META_KID0 + lane][base..base + SPINE_TREE_SLOTS]
                    .copy_from_slice(&columns.tree_kid[lane]);
                committed[META_IN0 + lane][wrap..wrap + wrap_slots]
                    .copy_from_slice(&columns.wrap_in[lane]);
            }
            for lane in 0..4 {
                committed[META_C0 + lane][base..base + SPINE_TREE_SLOTS]
                    .copy_from_slice(&columns.tree_c[lane]);
                committed[META_C0 + lane][wrap..wrap + wrap_slots]
                    .copy_from_slice(&columns.wrap_c[lane]);
                s0[lane][base..base + SPINE_TREE_SLOTS].copy_from_slice(&columns.tree_s0[lane]);
                s0[lane][wrap..wrap + wrap_slots].copy_from_slice(&columns.wrap_s0[lane]);
                s_out[lane][base..base + SPINE_TREE_SLOTS]
                    .copy_from_slice(&columns.tree_s_out[lane]);
                s_out[lane][wrap..wrap + wrap_slots].copy_from_slice(&columns.wrap_s_out[lane]);
            }
        }

        Fixture {
            descriptor,
            committed,
            s0,
            s_out,
        }
    }

    fn params(m: usize) -> PcsParams {
        PcsParams {
            m: m + pcs::LOG_PACKING,
            log_inv_rate: 2,
            log_batch_size: 2,
            profile: Default::default(),
        }
    }

    fn assert_claims_equal(left: &[QuirkyDirectClaim], right: &[QuirkyDirectClaim]) {
        assert_eq!(left.len(), right.len());
        for (left, right) in left.iter().zip(right) {
            assert_eq!(left.z_skip, right.z_skip);
            assert_eq!(left.k_skip, right.k_skip);
            assert_eq!(left.x_rest, right.x_rest);
            assert_eq!(left.value, right.value);
        }
    }

    fn direct_roundtrip_with_purpose(
        fixture: &Fixture,
        purpose: [u8; 32],
    ) -> (WalkARegionVk, Vec<F128>, WalkARegionSidecarProof) {
        let (z, slices) = fixture.packed();
        let vk = fixture.vk(purpose, &slices);
        let plan = WalkARegionProverPlan::new(&vk, &fixture.s0, &fixture.s_out).unwrap();
        let mut prover = FsLaneChallenger::new(DIRECT_DOMAIN);
        prover.observe_bytes(b"outer-witness-root");
        let (proof, prover_claims) = plan.prove(&z, &mut prover).unwrap();
        let mut verifier = FsLaneChallenger::new(DIRECT_DOMAIN);
        verifier.observe_bytes(b"outer-witness-root");
        let verifier_claims = verify_walk_a_region_sidecar(
            &vk,
            z.len().trailing_zeros() as usize,
            &proof,
            &mut verifier,
        )
        .unwrap();
        assert_claims_equal(&prover_claims, &verifier_claims);
        assert_eq!(prover.sample_f128(), verifier.sample_f128());
        (vk, z, proof)
    }

    fn direct_roundtrip(fixture: &Fixture) -> (WalkARegionVk, Vec<F128>, WalkARegionSidecarProof) {
        direct_roundtrip_with_purpose(fixture, [fixture.w_log() as u8; 32])
    }

    struct AuthorityCase {
        protocol: CanonicalWalkAProtocol,
        vk: WalkARegionVk,
        proof: WalkAUnionProof,
        claims: Vec<WalkAColumnClaim>,
        post_challenge: F128,
    }

    fn authority_case(fixture: &Fixture, purpose: [u8; 32]) -> AuthorityCase {
        let protocol = canonical_protocol(fixture.descriptor).unwrap();
        let (_, slices) = fixture.packed();
        let vk = fixture.vk(purpose, &slices);
        let committed = fixture
            .committed
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>();
        let exposure_owned = extract_spine_exposure(&protocol, &committed).unwrap();
        let exposure_refs = exposure_owned.as_ref().map(|columns| {
            [
                columns[0].as_slice(),
                columns[1].as_slice(),
                columns[2].as_slice(),
                columns[3].as_slice(),
            ]
        });

        let mut prover = FsLaneChallenger::new(TRACE_AUTHORITY_DOMAIN);
        bind_walk_a_vk(&mut prover, &vk);
        let (proof, prover_claims) = prove_walk_a_union_with_challenger(
            protocol.w_log,
            &protocol.fixed,
            &protocol.meta_c,
            &protocol.leaf_refs,
            &protocol.split_tails,
            protocol.es_sponge.as_ref(),
            protocol.spine.as_ref(),
            &committed,
            &fixture.s0,
            &fixture.s_out,
            exposure_refs.as_ref(),
            &mut prover,
        );

        let mut verifier = FsLaneChallenger::new(TRACE_AUTHORITY_DOMAIN);
        bind_walk_a_vk(&mut verifier, &vk);
        let claims = verify_walk_a_union_with_challenger(
            protocol.w_log,
            &protocol.fixed,
            &protocol.meta_c,
            &protocol.leaf_refs,
            &protocol.split_tails,
            protocol.es_sponge.as_ref(),
            protocol.spine.as_ref(),
            &proof,
            &mut verifier,
        )
        .unwrap();
        assert_eq!(prover_claims, claims);
        let prover_post = prover.sample_f128();
        let post_challenge = verifier.sample_f128();
        assert_eq!(prover_post, post_challenge);

        AuthorityCase {
            protocol,
            vk,
            proof,
            claims,
            post_challenge,
        }
    }

    fn build_authority_trace(
        case: &AuthorityCase,
        vk: &WalkARegionVk,
        proof: &WalkAUnionProof,
    ) -> (FieldR1cs, Vec<F128>, Vec<WalkAColumnClaim>, F128) {
        let mut builder = FieldR1csBuilder::new();
        let mut channel = FsChannelTrace::new(&mut builder, TRACE_AUTHORITY_DOMAIN);
        channel.observe_label(&mut builder, WALK_A_SIDECAR_TRANSCRIPT_LABEL);
        channel.observe_bytes_const(&mut builder, &vk.transcript_digest());
        let trace_claims = walk_a_trace::verify_walk_a_union_proof_trace(
            &mut builder,
            &mut channel,
            &case.protocol,
            proof,
        )
        .unwrap();
        let claims = trace_claims
            .iter()
            .map(|claim| WalkAColumnClaim {
                column: claim.column,
                point: claim
                    .point
                    .iter()
                    .map(|value| value.eval(builder.values()))
                    .collect(),
                value: claim.value.eval(builder.values()),
            })
            .collect();
        let post = channel.sample_f128(&mut builder).eval(builder.values());
        let (r1cs, witness) = builder.build();
        (r1cs, witness, claims, post)
    }

    struct FieldTraceCase {
        r1cs: FieldR1cs,
        params: PcsParams,
        spec: PublicIoSpec,
        io: Vec<F128>,
        vk: WalkARegionVk,
        field_proof: FieldR1csProof,
        sidecar: WalkARegionSidecarProof,
        commitment: Commitment,
        fresh_value: F128,
        post_challenge: F128,
    }

    fn field_trace_case() -> FieldTraceCase {
        let fixture = meta_fixture(true, true);
        let mut builder = FieldR1csBuilder::new();
        let column_len = 1usize << fixture.w_log();
        while builder.num_wires() % column_len != 0 {
            builder.alloc_f128(F128::ZERO);
        }
        let base = builder.num_wires() / column_len;
        for column in &fixture.committed {
            for value in column {
                builder.alloc_f128(*value);
            }
        }
        let slices: [WitnessSlice; WALK_A_META_COMMITTED_COLUMNS] =
            std::array::from_fn(|column| WitnessSlice {
                log2_len: fixture.w_log(),
                index: base + column,
            });
        let (r1cs, z) = builder.build();
        let params = params(r1cs.m);
        let vk = WalkARegionVk::new_meta([0xC1; 32], 0, Some(1), Some(0), slices).unwrap();
        let plan = WalkARegionProverPlan::new(&vk, &fixture.s0, &fixture.s_out).unwrap();
        let spec = PublicIoSpec {
            io_slice: WitnessSlice {
                log2_len: 0,
                index: 0,
            },
            io_len: 1,
            claims: Vec::new(),
        };
        let io = vec![F128::ONE];
        let mut prover = FsLaneChallenger::new(FIELD_DOMAIN);
        let (field_proof, sidecar, commitment, _) =
            prove_field_with_public_io_and_post_commit_context(
                &r1cs,
                &z,
                &params,
                &spec,
                &io,
                &TRACE_CLASS_DIGEST,
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
            &TRACE_CLASS_DIGEST,
            &sidecar,
            &mut verifier,
            |proof, context| {
                let claims =
                    verify_walk_a_region_sidecar(&vk, context.total_vars(), proof, context)
                        .map_err(|_| VerifyError::Auxiliary)?;
                context.append_claims(claims);
                Ok(())
            },
        )
        .unwrap();
        let post_challenge = verifier.sample_f128();

        FieldTraceCase {
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

    fn assert_reference_parity(fixture: &Fixture) {
        let protocol = canonical_protocol(fixture.descriptor).unwrap();
        let committed = fixture
            .committed
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>();
        let exposure_owned = extract_spine_exposure(&protocol, &committed).unwrap();
        let exposure_refs = exposure_owned.as_ref().map(|columns| {
            [
                columns[0].as_slice(),
                columns[1].as_slice(),
                columns[2].as_slice(),
                columns[3].as_slice(),
            ]
        });
        let reference = run_union_native(
            &committed,
            &fixture.s0,
            &fixture.s_out,
            &protocol.fixed,
            &protocol.meta_c,
            &protocol.leaf_refs,
            protocol.es_sponge.as_ref(),
            protocol.spine.as_ref(),
            exposure_refs.as_ref(),
            protocol.w_log,
            b"walk-a-reference-parity",
        );
        let mut challenger = FsLaneChallenger::new(b"walk-a-reference-parity");
        let (authority, claims) = prove_walk_a_union_with_challenger(
            protocol.w_log,
            &protocol.fixed,
            &protocol.meta_c,
            &protocol.leaf_refs,
            &protocol.split_tails,
            protocol.es_sponge.as_ref(),
            protocol.spine.as_ref(),
            &committed,
            &fixture.s0,
            &fixture.s_out,
            exposure_refs.as_ref(),
            &mut challenger,
        );
        assert_eq!(authority.selection, reference.sel_proof);
        assert_eq!(authority.walk, reference.walk_proof);
        assert_eq!(authority.substitution, reference.sub_proof);
        assert_eq!(authority.spine_exposure, reference.spine_expo_proof);
        assert_eq!(authority.shifts.len(), reference.shifts.len());
        for (proof, (_, _, reference_proof)) in authority.shifts.iter().zip(&reference.shifts) {
            assert_eq!(proof, reference_proof);
        }
        let reference_claims = reference
            .pending
            .iter()
            .chain(&reference.spine_expo_pending)
            .map(|(column, point, value)| (*column, point.clone(), *value))
            .collect::<Vec<_>>();
        let claims = claims
            .into_iter()
            .map(|claim| (claim.column, claim.point, claim.value))
            .collect::<Vec<_>>();
        assert_eq!(claims, reference_claims);
    }

    #[test]
    fn object_meta_has_a_distinct_authenticated_recipe() {
        let legacy = meta_fixture_profile(true, true, false);
        let objects = meta_fixture_profile(true, true, true);
        let (old_vk, old_z, old_proof) = direct_roundtrip_with_purpose(&legacy, [0x42; 32]);
        let (new_vk, new_z, new_proof) = direct_roundtrip_with_purpose(&objects, [0x42; 32]);
        assert_eq!(old_vk.slices(), new_vk.slices());
        assert_ne!(old_vk.transcript_digest(), new_vk.transcript_digest());
        assert_ne!(old_vk.descriptor(), new_vk.descriptor());
        for (vk, z, proof) in [(&old_vk, &new_z, &new_proof), (&new_vk, &old_z, &old_proof)] {
            let mut verifier = FsLaneChallenger::new(DIRECT_DOMAIN);
            verifier.observe_bytes(b"outer-witness-root");
            assert!(verify_walk_a_region_sidecar(
                vk,
                z.len().trailing_zeros() as usize,
                proof,
                &mut verifier,
            )
            .is_err());
        }
        assert_reference_parity(&objects);
    }

    #[test]
    fn wallet_meta_variants_roundtrip_and_match_reference_tuple_order() {
        let wallet = wallet_fixture();
        let es = meta_fixture(true, false);
        let spine = meta_fixture(false, true);
        let both = meta_fixture(true, true);

        let (_, _, wallet_proof) = direct_roundtrip(&wallet);
        assert_eq!(wallet_proof.authority.spine_exposure, None);
        let (_, _, es_proof) = direct_roundtrip(&es);
        assert_eq!(es_proof.authority.spine_exposure, None);
        let (_, _, spine_proof) = direct_roundtrip(&spine);
        assert!(spine_proof.authority.spine_exposure.is_some());
        let (_, _, both_proof) = direct_roundtrip(&both);
        assert!(both_proof.authority.spine_exposure.is_some());

        assert_reference_parity(&wallet);
        assert_reference_parity(&es);
        assert_reference_parity(&spine);
        assert_reference_parity(&both);
    }

    #[test]
    fn walk_a_bounded_decode_rejects_forged_lengths_and_spine_tags_before_serde() {
        let (wallet_vk, wallet_z, wallet_proof) = direct_roundtrip(&wallet_fixture());
        let wallet_bytes = bincode::serialize(&wallet_proof).unwrap();
        let (meta_vk, meta_z, meta_proof) = direct_roundtrip(&meta_fixture(true, true));
        let meta_bytes = bincode::serialize(&meta_proof).unwrap();

        let before = bounded_decode::serde_attempts();
        assert_eq!(
            decode_walk_a_region_sidecar_bounded(
                &wallet_vk,
                wallet_z.len().trailing_zeros() as usize,
                &wallet_bytes,
            )
            .unwrap(),
            wallet_proof
        );
        assert_eq!(
            decode_walk_a_region_sidecar_bounded(
                &meta_vk,
                meta_z.len().trailing_zeros() as usize,
                &meta_bytes,
            )
            .unwrap(),
            meta_proof
        );
        assert_eq!(bounded_decode::serde_attempts(), before + 2);

        let malformed_start = bounded_decode::serde_attempts();
        let wallet_total_vars = wallet_z.len().trailing_zeros() as usize;
        let meta_total_vars = meta_z.len().trailing_zeros() as usize;

        let mut trailing = wallet_bytes.clone();
        trailing.push(0);
        assert_eq!(
            decode_walk_a_region_sidecar_bounded(&wallet_vk, wallet_total_vars, &trailing)
                .unwrap_err(),
            RegionSidecarError::InvalidProof
        );
        assert_eq!(
            decode_walk_a_region_sidecar_bounded(
                &wallet_vk,
                wallet_total_vars,
                &wallet_bytes[..wallet_bytes.len() - 1],
            )
            .unwrap_err(),
            RegionSidecarError::InvalidProof
        );
        let mut wrong_version = wallet_bytes.clone();
        wrong_version[0] = WALK_A_REGION_SIDECAR_VERSION.wrapping_add(1);
        assert_eq!(
            decode_walk_a_region_sidecar_bounded(&wallet_vk, wallet_total_vars, &wrong_version)
                .unwrap_err(),
            RegionSidecarError::UnsupportedVersion
        );

        let meta_protocol = canonical_protocol(meta_vk.descriptor).unwrap();
        let meta_shape = walk_a_proof_shape(&meta_protocol);
        let meta_offsets = bounded_decode::layout_offsets(&meta_bytes, &meta_shape).unwrap();
        let vec_offsets = meta_offsets
            .iter()
            .filter_map(|(field, offset)| {
                matches!(field, bounded_decode::LayoutField::VecLength(_)).then_some(*offset)
            })
            .collect::<Vec<_>>();
        assert_eq!(vec_offsets.len(), 10, "all Walk-A Vec classes covered");
        for offset in vec_offsets {
            let mut forged = meta_bytes.clone();
            forged[offset..offset + 8].copy_from_slice(&u64::MAX.to_le_bytes());
            assert_eq!(
                decode_walk_a_region_sidecar_bounded(&meta_vk, meta_total_vars, &forged)
                    .unwrap_err(),
                RegionSidecarError::InvalidProof
            );
        }

        let wallet_protocol = canonical_protocol(wallet_vk.descriptor).unwrap();
        let wallet_shape = walk_a_proof_shape(&wallet_protocol);
        let wallet_option = bounded_decode::layout_offsets(&wallet_bytes, &wallet_shape)
            .unwrap()
            .into_iter()
            .find_map(|(field, offset)| {
                (field == bounded_decode::LayoutField::OptionTag).then_some(offset)
            })
            .unwrap();
        let mut unexpected_spine = wallet_bytes.clone();
        unexpected_spine[wallet_option] = 1;
        assert_eq!(
            decode_walk_a_region_sidecar_bounded(&wallet_vk, wallet_total_vars, &unexpected_spine,)
                .unwrap_err(),
            RegionSidecarError::InvalidProof
        );

        let meta_option = meta_offsets
            .into_iter()
            .find_map(|(field, offset)| {
                (field == bounded_decode::LayoutField::OptionTag).then_some(offset)
            })
            .unwrap();
        let mut missing_spine = meta_bytes.clone();
        missing_spine[meta_option] = 0;
        assert_eq!(
            decode_walk_a_region_sidecar_bounded(&meta_vk, meta_total_vars, &missing_spine)
                .unwrap_err(),
            RegionSidecarError::InvalidProof
        );

        assert_eq!(
            bounded_decode::serde_attempts(),
            malformed_start,
            "malformed Walk-A bytes reached allocation-bearing serde"
        );
    }

    #[test]
    fn walk_a_trace_authority_wallet_meta_lockstep_and_negatives() {
        let wallet = authority_case(&wallet_fixture(), [0x71; 32]);
        let meta = authority_case(&meta_fixture(true, true), [0x72; 32]);

        for case in [&wallet, &meta] {
            let (r1cs, witness, claims, post) = build_authority_trace(case, &case.vk, &case.proof);
            assert_eq!(claims, case.claims);
            assert_eq!(post, case.post_challenge);
            assert!(r1cs.satisfies(&witness));
        }

        let mut bad_proof = wallet.proof.clone();
        bad_proof.selection.rounds[0][0] += F128::ONE;
        let (r1cs, witness, _, _) = build_authority_trace(&wallet, &wallet.vk, &bad_proof);
        assert!(!r1cs.satisfies(&witness), "proof mutation satisfied trace");

        let mut bad_vk = wallet.vk.clone();
        bad_vk.purpose[0] ^= 1;
        let (r1cs, witness, _, _) = build_authority_trace(&wallet, &bad_vk, &wallet.proof);
        assert!(!r1cs.satisfies(&witness), "VK mutation satisfied trace");

        let mut bad_spine_proof = meta.proof.clone();
        bad_spine_proof.spine_exposure.as_mut().unwrap().rounds[0][0] += F128::ONE;
        let (r1cs, witness, _, _) = build_authority_trace(&meta, &meta.vk, &bad_spine_proof);
        assert!(
            !r1cs.satisfies(&witness),
            "spine exposure mutation satisfied trace"
        );

        let mut missing_spine = meta.proof.clone();
        missing_spine.spine_exposure = None;
        assert_eq!(
            walk_a_trace::preflight_walk_a_authority(&meta.protocol, &missing_spine),
            Err(RegionSidecarError::InvalidProof)
        );
        let mut unexpected_spine = wallet.proof.clone();
        unexpected_spine.spine_exposure = meta.proof.spine_exposure.clone();
        assert_eq!(
            walk_a_trace::preflight_walk_a_authority(&wallet.protocol, &unexpected_spine),
            Err(RegionSidecarError::InvalidProof)
        );

        let mut malformed = meta.proof.clone();
        malformed.substitution.rounds.pop();
        assert_eq!(
            walk_a_trace::preflight_walk_a_authority(&meta.protocol, &malformed),
            Err(RegionSidecarError::InvalidProof)
        );
        let mut malformed = meta.proof.clone();
        malformed.spine_exposure.as_mut().unwrap().rounds.pop();
        assert_eq!(
            walk_a_trace::preflight_walk_a_authority(&meta.protocol, &malformed),
            Err(RegionSidecarError::InvalidProof)
        );
    }

    #[test]
    fn walk_a_trace_meta_full_context_lockstep() {
        let case = field_trace_case();
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
            &TRACE_CLASS_DIGEST,
            None,
            |builder, context| {
                verify_walk_a_region_sidecar_trace_post_commit(
                    builder,
                    context,
                    &case.vk,
                    &case.sidecar,
                )
                .unwrap();
            },
        );
        let post = channel.sample_f128(&mut builder).eval(builder.values());
        assert_eq!(fresh.value.eval(builder.values()), case.fresh_value);
        assert_eq!(post, case.post_challenge);
        let (r1cs, witness) = builder.build();
        assert!(r1cs.satisfies(&witness));
    }

    #[test]
    fn spine_exposure_presence_and_mutations_are_rejected() {
        let fixture = meta_fixture(false, true);
        let (vk, z, proof) = direct_roundtrip(&fixture);
        let verify = |candidate: &WalkARegionSidecarProof| {
            let mut challenger = FsLaneChallenger::new(DIRECT_DOMAIN);
            challenger.observe_bytes(b"outer-witness-root");
            verify_walk_a_region_sidecar(
                &vk,
                z.len().trailing_zeros() as usize,
                candidate,
                &mut challenger,
            )
        };

        let mut bad = proof.clone();
        bad.authority.spine_exposure.as_mut().unwrap().rounds[0][0] += F128::ONE;
        assert!(verify(&bad).is_err(), "spine exposure mutation");

        let mut missing = proof.clone();
        missing.authority.spine_exposure = None;
        assert!(verify(&missing).is_err(), "missing mandatory exposure");

        let es_fixture = meta_fixture(true, false);
        let (es_vk, es_z, mut es_proof) = direct_roundtrip(&es_fixture);
        es_proof.authority.spine_exposure = Some(es_proof.authority.substitution.clone());
        let mut challenger = FsLaneChallenger::new(DIRECT_DOMAIN);
        challenger.observe_bytes(b"outer-witness-root");
        assert!(
            verify_walk_a_region_sidecar(
                &es_vk,
                es_z.len().trailing_zeros() as usize,
                &es_proof,
                &mut challenger,
            )
            .is_err(),
            "unexpected exposure on ES-only layout"
        );
    }

    #[test]
    fn wallet_field_postcommit_serde_mutations_and_core_downgrade() {
        let fixture = wallet_fixture();
        let mut builder = FieldR1csBuilder::new();
        let column_len = 1usize << fixture.w_log();
        while builder.num_wires() % column_len != 0 {
            builder.alloc_f128(F128::ZERO);
        }
        let base = builder.num_wires() / column_len;
        for column in &fixture.committed {
            for value in column {
                builder.alloc_f128(*value);
            }
        }
        let slices: [WitnessSlice; WALK_A_WALLET_COMMITTED_COLUMNS] =
            std::array::from_fn(|column| WitnessSlice {
                log2_len: fixture.w_log(),
                index: base + column,
            });
        let (r1cs, z) = builder.build();
        let vk = WalkARegionVk::new_wallet([0xA1; 32], 0, 0, slices).unwrap();
        let plan = WalkARegionProverPlan::new(&vk, &fixture.s0, &fixture.s_out).unwrap();
        let spec = PublicIoSpec {
            io_slice: WitnessSlice {
                log2_len: 0,
                index: 0,
            },
            io_len: 1,
            claims: Vec::new(),
        };
        let io = [F128::ONE];
        let mut prover = FsLaneChallenger::new(FIELD_DOMAIN);
        let (field_proof, sidecar, commitment, _) = prove_field_with_public_io_and_post_commit(
            &r1cs,
            &z,
            &params(r1cs.m),
            &spec,
            &io,
            &mut prover,
            |z, _, challenger| plan.prove(z, challenger).unwrap(),
        );

        let encoded = bincode::serialize(&sidecar).unwrap();
        assert_eq!(encoded.len(), sidecar.byte_len());
        let decoded: WalkARegionSidecarProof = bincode::deserialize(&encoded).unwrap();
        assert_eq!(decoded, sidecar);

        let verify = |candidate_vk: &WalkARegionVk, candidate: &WalkARegionSidecarProof| {
            let mut challenger = FsLaneChallenger::new(FIELD_DOMAIN);
            verify_field_with_public_io_and_post_commit(
                &r1cs,
                &commitment,
                &field_proof,
                &spec,
                &io,
                candidate,
                &mut challenger,
                |proof, challenger| {
                    verify_walk_a_region_sidecar(candidate_vk, r1cs.m, proof, challenger)
                        .map_err(|_| VerifyError::Auxiliary)
                },
            )
        };
        assert!(verify(&vk, &decoded).is_ok());

        let mut bad = decoded.clone();
        bad.version = 2;
        assert!(verify(&vk, &bad).is_err(), "version mutation");
        let mut bad = decoded.clone();
        bad.authority.selection.rounds[0][0] += F128::ONE;
        assert!(verify(&vk, &bad).is_err(), "selection mutation");
        let mut bad = decoded.clone();
        bad.authority.walk.layers[0].round_coeffs[0][0] += F128::ONE;
        assert!(verify(&vk, &bad).is_err(), "walk mutation");
        let mut bad = decoded.clone();
        bad.authority.substitution.rounds[0][0] += F128::ONE;
        assert!(verify(&vk, &bad).is_err(), "substitution mutation");
        let mut bad = decoded.clone();
        bad.authority.shifts[0].rounds[0][0] += F128::ONE;
        assert!(verify(&vk, &bad).is_err(), "shift mutation");
        let mut bad = decoded.clone();
        bad.authority.shifts.push(bad.authority.shifts[0].clone());
        assert!(verify(&vk, &bad).is_err(), "extra shift");
        let mut bad = decoded.clone();
        bad.authority.spine_exposure = Some(bad.authority.substitution.clone());
        assert!(verify(&vk, &bad).is_err(), "unexpected exposure");

        let mut bad_vk = vk.clone();
        bad_vk.purpose[0] ^= 1;
        assert!(verify(&bad_vk, &decoded).is_err(), "purpose mutation");
        let mut bad_vk = vk.clone();
        bad_vk.descriptor = WalkARegionDescriptor::Wallet {
            tx_log: 0,
            nq_log: 1,
        };
        assert!(verify(&bad_vk, &decoded).is_err(), "descriptor mutation");
        let mut bad_vk = vk.clone();
        Arc::make_mut(&mut bad_vk.fixed)[0].table[0] += F128::ONE;
        assert!(verify(&bad_vk, &decoded).is_err(), "fixed-table mutation");
        let mut bad_vk = vk.clone();
        if let WalkARegionSlices::Wallet(slices) = &mut bad_vk.slices {
            slices.swap(0, 1);
        }
        assert!(verify(&bad_vk, &decoded).is_err(), "slice order mutation");

        let mut core_only = FsLaneChallenger::new(FIELD_DOMAIN);
        assert!(
            verify_field_with_public_io(
                &r1cs,
                &commitment,
                &field_proof,
                &spec,
                &io,
                &mut core_only,
            )
            .is_err(),
            "a sidecar-bearing transcript must not downgrade to core-only verification"
        );
    }

    #[test]
    fn meta_both_field_postcommit_opens_repointed_spine_claims() {
        // `both` places the spine in the upper dyadic half, so this gate
        // exercises both the compact Window re-point and its constant region
        // coordinate against the actual outer PCS commitment.
        let fixture = meta_fixture(true, true);
        let mut builder = FieldR1csBuilder::new();
        let column_len = 1usize << fixture.w_log();
        while builder.num_wires() % column_len != 0 {
            builder.alloc_f128(F128::ZERO);
        }
        let base = builder.num_wires() / column_len;
        for column in &fixture.committed {
            for value in column {
                builder.alloc_f128(*value);
            }
        }
        let slices: [WitnessSlice; WALK_A_META_COMMITTED_COLUMNS] =
            std::array::from_fn(|column| WitnessSlice {
                log2_len: fixture.w_log(),
                index: base + column,
            });
        let (r1cs, z) = builder.build();
        let vk = WalkARegionVk::new_meta([0xB1; 32], 0, Some(1), Some(0), slices).unwrap();
        let plan = WalkARegionProverPlan::new(&vk, &fixture.s0, &fixture.s_out).unwrap();
        let spec = PublicIoSpec {
            io_slice: WitnessSlice {
                log2_len: 0,
                index: 0,
            },
            io_len: 1,
            claims: Vec::new(),
        };
        let io = [F128::ONE];
        let mut prover = FsLaneChallenger::new(FIELD_DOMAIN);
        let (field_proof, sidecar, commitment, _) = prove_field_with_public_io_and_post_commit(
            &r1cs,
            &z,
            &params(r1cs.m),
            &spec,
            &io,
            &mut prover,
            |z, _, challenger| plan.prove(z, challenger).unwrap(),
        );
        assert!(sidecar.authority.spine_exposure.is_some());

        let mut verifier = FsLaneChallenger::new(FIELD_DOMAIN);
        assert!(
            verify_field_with_public_io_and_post_commit(
                &r1cs,
                &commitment,
                &field_proof,
                &spec,
                &io,
                &sidecar,
                &mut verifier,
                |proof, challenger| {
                    verify_walk_a_region_sidecar(&vk, r1cs.m, proof, challenger)
                        .map_err(|_| VerifyError::Auxiliary)
                },
            )
            .is_ok(),
            "spine exposure claims did not open at their re-pointed KID/C slices"
        );
    }

    #[test]
    fn precommit_selection_kernel_fails_after_root_and_vk_binding() {
        let fixture = wallet_fixture();
        let protocol = canonical_protocol(fixture.descriptor).unwrap();
        let mut old_prover = FsLaneChallenger::new(b"walk-a-precommit-kernel-v0");
        let beta = old_prover.sample_f128();
        let rho = old_prover.sample_f128_vec(protocol.w_log);
        let mut delta = vec![F128::ZERO; 1usize << protocol.w_log];
        delta[0] = rho[0];
        delta[1] = F128::ONE + rho[0];
        let eval = delta
            .iter()
            .zip(build_eq_table(&rho))
            .fold(F128::ZERO, |sum, (value, weight)| sum + *value * weight);
        assert_eq!(eval, F128::ZERO);
        assert!(delta.iter().any(|value| *value != F128::ZERO));

        let zero = vec![F128::ZERO; delta.len()];
        let mut committed_owned: [Vec<F128>; WALK_A_WALLET_COMMITTED_COLUMNS] =
            std::array::from_fn(|_| zero.clone());
        committed_owned[protocol.meta_c[0]] = delta.clone();
        let committed = committed_owned
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>();
        let internal_owned: [Vec<F128>; 4] = std::array::from_fn(|_| zero.clone());
        let internal = internal_owned.iter().map(Vec::as_slice).collect::<Vec<_>>();
        let terms = carry_selection_terms(&protocol.meta_c, beta);
        let (old_proof, _, _) = prove_column_relation(
            F128::ZERO,
            &rho,
            &terms,
            &RelationColumns {
                committed: &committed,
                internal: &internal,
                fixed: &[],
            },
            &mut old_prover,
        );
        let mut old_verifier = FsLaneChallenger::new(b"walk-a-precommit-kernel-v0");
        let old_beta = old_verifier.sample_f128();
        let old_rho = old_verifier.sample_f128_vec(protocol.w_log);
        assert!(verify_column_relation(
            protocol.w_log,
            F128::ZERO,
            &old_rho,
            &carry_selection_terms(&protocol.meta_c, old_beta),
            &[],
            &old_proof,
            &mut old_verifier,
        )
        .is_ok());

        let (_, slices) = fixture.packed();
        let vk = fixture.vk([0xC1; 32], &slices);
        let mut postcommit = FsLaneChallenger::new(b"walk-a-precommit-kernel-v0");
        postcommit.observe_bytes(b"outer-witness-root");
        bind_walk_a_vk(&mut postcommit, &vk);
        let post_beta = postcommit.sample_f128();
        let post_rho = postcommit.sample_f128_vec(protocol.w_log);
        let post_eval = delta
            .iter()
            .zip(build_eq_table(&post_rho))
            .fold(F128::ZERO, |sum, (value, weight)| sum + *value * weight);
        assert_ne!(post_eval, F128::ZERO);
        assert!(
            verify_column_relation(
                protocol.w_log,
                F128::ZERO,
                &post_rho,
                &carry_selection_terms(&protocol.meta_c, post_beta),
                &[],
                &old_proof,
                &mut postcommit,
            )
            .is_err(),
            "precommit rho-kernel proof survived postcommit binding"
        );
    }

    #[test]
    fn descriptor_and_slice_preflight_rejects_malformed_keys() {
        let wallet = wallet_fixture();
        let (_, slices) = wallet.packed();
        let wallet_slices: [WitnessSlice; WALK_A_WALLET_COMMITTED_COLUMNS] =
            slices.try_into().unwrap();
        assert_eq!(
            WalkARegionVk::new_wallet([0; 32], 0, usize::BITS as usize, wallet_slices),
            Err(RegionSidecarError::UnsupportedVkShape)
        );
        assert_eq!(
            WalkARegionVk::new_wallet([0; 32], MAX_WALK_A_TX_LOG + 1, 0, wallet_slices),
            Err(RegionSidecarError::UnsupportedVkShape)
        );
        assert_eq!(
            WalkARegionVk::new_meta(
                [0; 32],
                0,
                None,
                None,
                std::array::from_fn(|index| WitnessSlice { log2_len: 1, index }),
            ),
            Err(RegionSidecarError::UnsupportedVkShape)
        );
        assert_eq!(
            WalkARegionVk::new_meta(
                [0; 32],
                63,
                Some(1),
                None,
                std::array::from_fn(|index| WitnessSlice { log2_len: 1, index }),
            ),
            Err(RegionSidecarError::UnsupportedVkShape)
        );
        // cap=2^13 gives a 2^19 per-tx spine block. Nine expanded fixed
        // tables exceed V1's 2^22-cell budget and must be rejected before
        // any of those tables is allocated.
        assert_eq!(
            WalkARegionVk::new_meta(
                [0; 32],
                0,
                None,
                Some(13),
                std::array::from_fn(|index| WitnessSlice {
                    log2_len: 19,
                    index,
                }),
            ),
            Err(RegionSidecarError::UnsupportedVkShape)
        );
        let mut noncontiguous = wallet_slices;
        noncontiguous[5].index += 1;
        assert_eq!(
            WalkARegionVk::new_wallet([0; 32], 0, 0, noncontiguous),
            Err(RegionSidecarError::BadSlice)
        );
        let _ = CAPSULE_LEAF_SYMBOLS;
    }
}
