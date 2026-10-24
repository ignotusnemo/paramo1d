// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Allocation-bounded canonical wire codec for the selected authorization.
//!
//! The proof contains exactly six variable-length bincode fields.  This module
//! scans all six fixed-width `u64` length prefixes and the complete byte layout
//! before serde is allowed to allocate any vector.  Every other proof field is
//! a fixed tuple, array, integer, or field element.

use bincode::Options;
use noid_core::Block256;
use noid_fri_binius::zk_capsule_pcs::{
    ZkCapsulePcsMidCommitment, ZkCapsulePcsOpening, ZkCapsulePcsSourceCommitment,
    ZkCapsulePcsTailReveal,
};
use noid_fri_binius::zk_phase_a::ZkPhaseAProof;
use serde::Deserialize;

use crate::zk_authorization::{
    ZkAuthCapsuleOwnerProof, ZkAuthorizationError, ZkAuthorizationProof,
    ZkAuthorizationProofComponent, ZkAuthorizationUpper, ZK_AUTHORIZATION_PAYLOAD_ROOFLINE_BYTES,
    ZK_AUTHORIZATION_WORST_SERIALIZED_BYTES, ZK_AUTH_GRIND_NONCE_BYTES, ZK_AUTH_OWNER_PROOF_BYTES,
    ZK_AUTH_PHASE_A_PROOF_BYTES, ZK_AUTH_PHASE_B_VALUE_BYTES, ZK_AUTH_SIGMA_BYTES,
    ZK_AUTH_UPPER_BYTES,
};
use noid_fri_binius::zk_capsule_pcs::{
    ZK_CAPSULE_PCS_MID_COMMITMENT_BYTES, ZK_CAPSULE_PCS_MID_SYMBOLS,
    ZK_CAPSULE_PCS_SOURCE_COMMITMENT_BYTES, ZK_CAPSULE_PCS_SOURCE_SYMBOLS,
    ZK_CAPSULE_PCS_TAIL_BYTES, ZK_CAPSULE_PCS_WORST_MID_SIBLINGS,
    ZK_CAPSULE_PCS_WORST_SOURCE_SIBLINGS,
};

/// Maximum canonical selected-authorization encoding.  The slightly larger
/// payload roofline is a design allowance, not permission for an unrecognized
/// wire shape.
pub const ZK_AUTHORIZATION_MAX_WIRE_BYTES: usize = ZK_AUTHORIZATION_WORST_SERIALIZED_BYTES;

const LENGTH_BYTES: usize = 8;
const BASE_FIELD_BYTES: usize = 16;
const WIDE_FIELD_BYTES: usize = 32;
const HASH_BYTES: usize = 32;
const VECTOR_COUNT: usize = 6;

const SOURCE_CAP_HASHES: usize = ZK_CAPSULE_PCS_SOURCE_COMMITMENT_BYTES / HASH_BYTES;
const MID_CAP_HASHES: usize = ZK_CAPSULE_PCS_MID_COMMITMENT_BYTES / HASH_BYTES;

const FIXED_AFTER_SOURCE_CAP: usize = ZK_AUTH_OWNER_PROOF_BYTES
    + ZK_AUTH_SIGMA_BYTES
    + ZK_AUTH_PHASE_A_PROOF_BYTES
    + ZK_AUTH_PHASE_B_VALUE_BYTES
    + ZK_AUTH_UPPER_BYTES;
const FIXED_AFTER_MID_CAP: usize = ZK_CAPSULE_PCS_TAIL_BYTES + ZK_AUTH_GRIND_NONCE_BYTES;

const _: () = assert!(ZK_AUTHORIZATION_MAX_WIRE_BYTES == 92_696);
const _: () = assert!(ZK_AUTHORIZATION_MAX_WIRE_BYTES <= ZK_AUTHORIZATION_PAYLOAD_ROOFLINE_BYTES);
const _: () = assert!(SOURCE_CAP_HASHES == 8);
const _: () = assert!(MID_CAP_HASHES == 8);
const _: () = assert!(ZK_CAPSULE_PCS_SOURCE_SYMBOLS == 1_560);
const _: () = assert!(ZK_CAPSULE_PCS_MID_SYMBOLS == 1_040);
const _: () = assert!(VECTOR_COUNT * LENGTH_BYTES == 48);
const _: () = assert!(
    ZK_CAPSULE_PCS_SOURCE_COMMITMENT_BYTES
        + FIXED_AFTER_SOURCE_CAP
        + ZK_CAPSULE_PCS_MID_COMMITMENT_BYTES
        + FIXED_AFTER_MID_CAP
        + ZK_CAPSULE_PCS_SOURCE_SYMBOLS * BASE_FIELD_BYTES
        + ZK_CAPSULE_PCS_MID_SYMBOLS * WIDE_FIELD_BYTES
        + (ZK_CAPSULE_PCS_WORST_SOURCE_SIBLINGS + ZK_CAPSULE_PCS_WORST_MID_SIBLINGS) * HASH_BYTES
        + VECTOR_COUNT * LENGTH_BYTES
        == ZK_AUTHORIZATION_MAX_WIRE_BYTES
);

/// Canonical encoding failure.  No string-bearing bincode error escapes this
/// boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkAuthorizationWireEncodeError {
    InvalidShape {
        component: ZkAuthorizationProofComponent,
        expected: usize,
        actual: usize,
        is_maximum: bool,
    },
    Serialize,
    TooLarge {
        actual: usize,
        max: usize,
    },
    InternalLayout,
}

impl std::fmt::Display for ZkAuthorizationWireEncodeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ZkAuthorizationWireEncodeError {}

/// Allocation-free failures emitted by the byte scanner or by the bounded
/// serde step which follows it.  The error itself owns no heap data.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkAuthorizationWireDecodeError {
    TooLarge {
        actual: usize,
        max: usize,
    },
    Truncated {
        offset: usize,
        needed: usize,
        remaining: usize,
    },
    InvalidLength {
        component: ZkAuthorizationProofComponent,
        expected: u64,
        actual: u64,
        is_maximum: bool,
    },
    LengthArithmetic {
        component: ZkAuthorizationProofComponent,
    },
    TrailingBytes {
        offset: usize,
        remaining: usize,
    },
    Deserialize,
    DecodedShape,
}

impl std::fmt::Display for ZkAuthorizationWireDecodeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ZkAuthorizationWireDecodeError {}

fn wire_options() -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .with_limit(ZK_AUTHORIZATION_MAX_WIRE_BYTES as u64)
        .reject_trailing_bytes()
}

#[derive(Clone, Copy, Debug)]
struct WirePreflight {
    #[cfg_attr(not(test), allow(dead_code))]
    vector_length_offsets: [usize; VECTOR_COUNT],
}

/// Private serde mirror of the complete proof wire.
///
/// The public proof type deliberately does not implement `Deserialize`, so
/// this DTO is reachable only after [`preflight_wire`] has bounded every
/// allocation-bearing field.  Field order must remain identical to
/// `ZkAuthorizationProof`; the byte-exact layout tests below pin that contract.
#[derive(Deserialize)]
struct ZkAuthorizationWireDto {
    source_commitment: ZkCapsulePcsSourceCommitment,
    owner: ZkAuthCapsuleOwnerProof,
    sigma: Block256,
    phase_a: ZkPhaseAProof<Block256>,
    phase_b_value: Block256,
    upper: ZkAuthorizationUpper,
    mid_commitment: ZkCapsulePcsMidCommitment,
    tail: ZkCapsulePcsTailReveal,
    grind_nonce: u64,
    opening: ZkCapsulePcsOpening,
}

impl From<ZkAuthorizationWireDto> for ZkAuthorizationProof {
    fn from(dto: ZkAuthorizationWireDto) -> Self {
        Self {
            source_commitment: dto.source_commitment,
            owner: dto.owner,
            sigma: dto.sigma,
            phase_a: dto.phase_a,
            phase_b_value: dto.phase_b_value,
            upper: dto.upper,
            mid_commitment: dto.mid_commitment,
            tail: dto.tail,
            grind_nonce: dto.grind_nonce,
            opening: dto.opening,
        }
    }
}

struct WireCursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> WireCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take(&mut self, count: usize) -> Result<&'a [u8], ZkAuthorizationWireDecodeError> {
        let end =
            self.offset
                .checked_add(count)
                .ok_or(ZkAuthorizationWireDecodeError::Truncated {
                    offset: self.offset,
                    needed: count,
                    remaining: self.bytes.len().saturating_sub(self.offset),
                })?;
        if end > self.bytes.len() {
            return Err(ZkAuthorizationWireDecodeError::Truncated {
                offset: self.offset,
                needed: count,
                remaining: self.bytes.len().saturating_sub(self.offset),
            });
        }
        let start = self.offset;
        self.offset = end;
        Ok(&self.bytes[start..end])
    }

    fn skip(&mut self, count: usize) -> Result<(), ZkAuthorizationWireDecodeError> {
        self.take(count).map(|_| ())
    }

    fn read_length(&mut self) -> Result<(usize, u64), ZkAuthorizationWireDecodeError> {
        let offset = self.offset;
        let encoded: [u8; LENGTH_BYTES] = self
            .take(LENGTH_BYTES)?
            .try_into()
            .expect("exact fixed-width length prefix");
        Ok((offset, u64::from_le_bytes(encoded)))
    }
}

fn invalid_length(
    component: ZkAuthorizationProofComponent,
    expected: usize,
    actual: u64,
    is_maximum: bool,
) -> ZkAuthorizationWireDecodeError {
    ZkAuthorizationWireDecodeError::InvalidLength {
        component,
        expected: expected as u64,
        actual,
        is_maximum,
    }
}

fn exact_length(
    component: ZkAuthorizationProofComponent,
    expected: usize,
    actual: u64,
) -> Result<usize, ZkAuthorizationWireDecodeError> {
    if actual != expected as u64 {
        return Err(invalid_length(component, expected, actual, false));
    }
    Ok(expected)
}

fn bounded_length(
    component: ZkAuthorizationProofComponent,
    maximum: usize,
    actual: u64,
) -> Result<usize, ZkAuthorizationWireDecodeError> {
    if actual > maximum as u64 {
        return Err(invalid_length(component, maximum, actual, true));
    }
    usize::try_from(actual)
        .map_err(|_| ZkAuthorizationWireDecodeError::LengthArithmetic { component })
}

fn skip_elements(
    cursor: &mut WireCursor<'_>,
    component: ZkAuthorizationProofComponent,
    elements: usize,
    element_bytes: usize,
) -> Result<(), ZkAuthorizationWireDecodeError> {
    let bytes = elements
        .checked_mul(element_bytes)
        .ok_or(ZkAuthorizationWireDecodeError::LengthArithmetic { component })?;
    cursor.skip(bytes)
}

/// Scan the complete fixed-int bincode layout without allocating.  The order
/// mirrors `ZkAuthorizationProof` and the nested `MerkleCap` /
/// `SourceBatchedMerkleProof` structs exactly.
fn preflight_wire(bytes: &[u8]) -> Result<WirePreflight, ZkAuthorizationWireDecodeError> {
    if bytes.len() > ZK_AUTHORIZATION_MAX_WIRE_BYTES {
        return Err(ZkAuthorizationWireDecodeError::TooLarge {
            actual: bytes.len(),
            max: ZK_AUTHORIZATION_MAX_WIRE_BYTES,
        });
    }

    let mut cursor = WireCursor::new(bytes);
    let mut offsets = [0usize; VECTOR_COUNT];

    // source_commitment.cap.hashes: Vec<[u8; 32]>
    let (offset, length) = cursor.read_length()?;
    offsets[0] = offset;
    let length = exact_length(
        ZkAuthorizationProofComponent::SourceCap,
        SOURCE_CAP_HASHES,
        length,
    )?;
    skip_elements(
        &mut cursor,
        ZkAuthorizationProofComponent::SourceCap,
        length,
        HASH_BYTES,
    )?;

    // Owner, sigma, Phase A, Phase-B value and the fixed 256-field upper.
    cursor.skip(FIXED_AFTER_SOURCE_CAP)?;

    // mid_commitment.cap.hashes: Vec<[u8; 32]>
    let (offset, length) = cursor.read_length()?;
    offsets[1] = offset;
    let length = exact_length(
        ZkAuthorizationProofComponent::MidCap,
        MID_CAP_HASHES,
        length,
    )?;
    skip_elements(
        &mut cursor,
        ZkAuthorizationProofComponent::MidCap,
        length,
        HASH_BYTES,
    )?;

    // Fixed tail coefficients and grind nonce.
    cursor.skip(FIXED_AFTER_MID_CAP)?;

    // opening.source_joint_symbols: Vec<Block128>
    let (offset, length) = cursor.read_length()?;
    offsets[2] = offset;
    let length = exact_length(
        ZkAuthorizationProofComponent::SourceSymbols,
        ZK_CAPSULE_PCS_SOURCE_SYMBOLS,
        length,
    )?;
    skip_elements(
        &mut cursor,
        ZkAuthorizationProofComponent::SourceSymbols,
        length,
        BASE_FIELD_BYTES,
    )?;

    // opening.source_batch.siblings: Vec<[u8; 32]>
    let (offset, length) = cursor.read_length()?;
    offsets[3] = offset;
    let length = bounded_length(
        ZkAuthorizationProofComponent::SourceSiblings,
        ZK_CAPSULE_PCS_WORST_SOURCE_SIBLINGS,
        length,
    )?;
    skip_elements(
        &mut cursor,
        ZkAuthorizationProofComponent::SourceSiblings,
        length,
        HASH_BYTES,
    )?;

    // opening.mid_symbols: Vec<Block256>
    let (offset, length) = cursor.read_length()?;
    offsets[4] = offset;
    let length = exact_length(
        ZkAuthorizationProofComponent::MidSymbols,
        ZK_CAPSULE_PCS_MID_SYMBOLS,
        length,
    )?;
    skip_elements(
        &mut cursor,
        ZkAuthorizationProofComponent::MidSymbols,
        length,
        WIDE_FIELD_BYTES,
    )?;

    // opening.mid_batch.siblings: Vec<[u8; 32]>
    let (offset, length) = cursor.read_length()?;
    offsets[5] = offset;
    let length = bounded_length(
        ZkAuthorizationProofComponent::MidSiblings,
        ZK_CAPSULE_PCS_WORST_MID_SIBLINGS,
        length,
    )?;
    skip_elements(
        &mut cursor,
        ZkAuthorizationProofComponent::MidSiblings,
        length,
        HASH_BYTES,
    )?;

    if cursor.offset != bytes.len() {
        return Err(ZkAuthorizationWireDecodeError::TrailingBytes {
            offset: cursor.offset,
            remaining: bytes.len() - cursor.offset,
        });
    }

    Ok(WirePreflight {
        vector_length_offsets: offsets,
    })
}

fn encode_shape_error(error: ZkAuthorizationError) -> ZkAuthorizationWireEncodeError {
    match error {
        ZkAuthorizationError::ProofShape {
            component,
            expected,
            actual,
            is_maximum,
        } => ZkAuthorizationWireEncodeError::InvalidShape {
            component,
            expected,
            actual,
            is_maximum,
        },
        _ => ZkAuthorizationWireEncodeError::InternalLayout,
    }
}

impl ZkAuthorizationProof {
    /// Serialize the proof in the one canonical fixed-int, little-endian wire
    /// format after checking every variable-length component.
    pub fn to_bytes(&self) -> Result<Vec<u8>, ZkAuthorizationWireEncodeError> {
        self.preflight_shape().map_err(encode_shape_error)?;
        let bytes = wire_options()
            .serialize(self)
            .map_err(|_| ZkAuthorizationWireEncodeError::Serialize)?;
        if bytes.len() > ZK_AUTHORIZATION_MAX_WIRE_BYTES {
            return Err(ZkAuthorizationWireEncodeError::TooLarge {
                actual: bytes.len(),
                max: ZK_AUTHORIZATION_MAX_WIRE_BYTES,
            });
        }
        preflight_wire(&bytes).map_err(|_| ZkAuthorizationWireEncodeError::InternalLayout)?;
        Ok(bytes)
    }

    /// Reject size, all six vector lengths, truncation and trailing bytes before
    /// invoking serde.  Any allocations performed by bincode are consequently
    /// bounded by the exact canonical proof geometry.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ZkAuthorizationWireDecodeError> {
        let _shape = preflight_wire(bytes)?;
        let proof: ZkAuthorizationWireDto = wire_options()
            .deserialize(bytes)
            .map_err(|_| ZkAuthorizationWireDecodeError::Deserialize)?;
        let proof = Self::from(proof);
        proof
            .preflight_shape()
            .map_err(|_| ZkAuthorizationWireDecodeError::DecodedShape)?;
        Ok(proof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zk_auth_capsule::ZK_AUTH_CAPSULE_TERMINAL_OPERAND_CLAIMS;
    use crate::zk_authorization::{
        ZkAuthCapsuleOwnerProof, ZkAuthorizationUpper, ZK_AUTH_OWNER_PROOF_ROUNDS,
    };
    use crate::zk_mlecheck::{ZkMleCheckRoundProof, ZK_MLECHECK_ROUND_PROOF_COEFFS};
    use noid_core::{Block128, Block256};
    use noid_fri_binius::interleaved_commit::{MerkleCap, SourceBatchedMerkleProof, SourceHash};
    use noid_fri_binius::zk_capsule_algebra::{TAIL_SYMBOLS, UPPER_SYMBOLS};
    use noid_fri_binius::zk_capsule_pcs::{
        ZkCapsulePcsMidCommitment, ZkCapsulePcsOpening, ZkCapsulePcsSourceCommitment,
        ZkCapsulePcsTailReveal,
    };
    use noid_fri_binius::zk_phase_a::ZkPhaseAProof;

    fn hash(index: usize) -> SourceHash {
        let mut hash = [0u8; HASH_BYTES];
        hash[..8].copy_from_slice(&(index as u64).to_le_bytes());
        hash
    }

    fn wide(index: usize) -> Block256 {
        Block256::new(
            Block128::from(index as u128),
            Block128::from((index as u128).rotate_left(37) ^ 0xC1_0256),
        )
    }

    fn fixture(source_siblings: usize, mid_siblings: usize) -> ZkAuthorizationProof {
        let owner = ZkAuthCapsuleOwnerProof {
            mask_mu: wide(1),
            rounds: std::array::from_fn(|round| ZkMleCheckRoundProof {
                coeffs_without_constant: std::array::from_fn(|coefficient| {
                    wide(round * ZK_MLECHECK_ROUND_PROOF_COEFFS + coefficient + 2)
                }),
            }),
            mask_final: wide(113),
            terminal_operand_claims: std::array::from_fn(|index| wide(index + 114)),
        };
        assert_eq!(owner.rounds.len(), ZK_AUTH_OWNER_PROOF_ROUNDS);
        assert_eq!(
            owner.terminal_operand_claims.len(),
            ZK_AUTH_CAPSULE_TERMINAL_OPERAND_CLAIMS
        );

        ZkAuthorizationProof {
            source_commitment: ZkCapsulePcsSourceCommitment {
                cap: MerkleCap {
                    hashes: (0..SOURCE_CAP_HASHES).map(hash).collect(),
                },
            },
            owner,
            sigma: wide(119),
            phase_a: ZkPhaseAProof::default(),
            phase_b_value: wide(120),
            upper: ZkAuthorizationUpper::new(std::array::from_fn(|index| wide(index + 121))),
            mid_commitment: ZkCapsulePcsMidCommitment {
                cap: MerkleCap {
                    hashes: (10_000..10_000 + MID_CAP_HASHES).map(hash).collect(),
                },
            },
            tail: ZkCapsulePcsTailReveal {
                coefficients: std::array::from_fn(|index| wide(index + UPPER_SYMBOLS + 121)),
            },
            grind_nonce: 0xA11C_E002,
            opening: ZkCapsulePcsOpening {
                source_joint_symbols: (0..ZK_CAPSULE_PCS_SOURCE_SYMBOLS)
                    .map(|index| Block128::from((index + 1_000) as u128))
                    .collect(),
                source_batch: SourceBatchedMerkleProof {
                    siblings: (20_000..20_000 + source_siblings).map(hash).collect(),
                },
                mid_symbols: (0..ZK_CAPSULE_PCS_MID_SYMBOLS)
                    .map(|index| wide(index + 3_000))
                    .collect(),
                mid_batch: SourceBatchedMerkleProof {
                    siblings: (30_000..30_000 + mid_siblings).map(hash).collect(),
                },
            },
        }
    }

    #[test]
    fn canonical_roundtrip_is_byte_exact() {
        let proof = fixture(17, 9);
        let bytes = proof.to_bytes().expect("canonical encode");
        assert_eq!(bytes.len(), proof.serialized_byte_len());
        let decoded = ZkAuthorizationProof::from_bytes(&bytes).expect("bounded decode");
        assert_eq!(decoded.to_bytes().unwrap(), bytes);
    }

    #[test]
    fn worst_canonical_shape_matches_the_selected_bound() {
        let proof = fixture(
            ZK_CAPSULE_PCS_WORST_SOURCE_SIBLINGS,
            ZK_CAPSULE_PCS_WORST_MID_SIBLINGS,
        );
        let bytes = proof.to_bytes().expect("worst canonical encode");
        assert_eq!(proof.modeled_byte_len(), 92_648);
        assert_eq!(bytes.len(), ZK_AUTHORIZATION_MAX_WIRE_BYTES);
        assert_eq!(bytes.len(), ZK_AUTHORIZATION_WORST_SERIALIZED_BYTES);
        assert!(bytes.len() <= ZK_AUTHORIZATION_PAYLOAD_ROOFLINE_BYTES);
        ZkAuthorizationProof::from_bytes(&bytes).expect("worst bounded decode");
    }

    #[test]
    fn every_vector_length_is_scanned_before_deserialization() {
        let proof = fixture(17, 9);
        let bytes = proof.to_bytes().unwrap();
        let preflight = preflight_wire(&bytes).unwrap();
        let components = [
            ZkAuthorizationProofComponent::SourceCap,
            ZkAuthorizationProofComponent::MidCap,
            ZkAuthorizationProofComponent::SourceSymbols,
            ZkAuthorizationProofComponent::SourceSiblings,
            ZkAuthorizationProofComponent::MidSymbols,
            ZkAuthorizationProofComponent::MidSiblings,
        ];

        for (&offset, &component) in preflight.vector_length_offsets.iter().zip(&components) {
            let mut hostile = bytes.clone();
            hostile[offset..offset + LENGTH_BYTES].copy_from_slice(&u64::MAX.to_le_bytes());
            assert!(matches!(
                ZkAuthorizationProof::from_bytes(&hostile),
                Err(ZkAuthorizationWireDecodeError::InvalidLength {
                    component: observed,
                    actual: u64::MAX,
                    ..
                }) if observed == component
            ));
        }
    }

    #[test]
    fn truncation_and_trailing_bytes_reject_in_manual_preflight() {
        let proof = fixture(17, 9);
        let bytes = proof.to_bytes().unwrap();
        let preflight = preflight_wire(&bytes).unwrap();
        let mut cuts = vec![0, 1, LENGTH_BYTES - 1, bytes.len() - 1];
        for offset in preflight.vector_length_offsets {
            cuts.push(offset);
            cuts.push((offset + LENGTH_BYTES - 1).min(bytes.len() - 1));
        }
        cuts.sort_unstable();
        cuts.dedup();
        for cut in cuts {
            assert!(matches!(
                ZkAuthorizationProof::from_bytes(&bytes[..cut]),
                Err(ZkAuthorizationWireDecodeError::Truncated { .. })
            ));
        }

        let mut trailing = bytes;
        trailing.push(0);
        assert!(matches!(
            ZkAuthorizationProof::from_bytes(&trailing),
            Err(ZkAuthorizationWireDecodeError::TrailingBytes { remaining: 1, .. })
        ));
    }

    #[test]
    fn oversize_rejects_before_reading_even_one_length() {
        let bytes = vec![0u8; ZK_AUTHORIZATION_MAX_WIRE_BYTES + 1];
        assert!(matches!(
            ZkAuthorizationProof::from_bytes(&bytes),
            Err(ZkAuthorizationWireDecodeError::TooLarge { actual, max })
                if actual == ZK_AUTHORIZATION_MAX_WIRE_BYTES + 1
                    && max == ZK_AUTHORIZATION_MAX_WIRE_BYTES
        ));
    }

    #[test]
    fn exact_and_maximum_length_violations_reject() {
        let proof = fixture(17, 9);
        let bytes = proof.to_bytes().unwrap();
        let offsets = preflight_wire(&bytes).unwrap().vector_length_offsets;
        let invalid = [
            (0, (SOURCE_CAP_HASHES + 1) as u64),
            (1, (MID_CAP_HASHES + 1) as u64),
            (2, (ZK_CAPSULE_PCS_SOURCE_SYMBOLS + 1) as u64),
            (3, (ZK_CAPSULE_PCS_WORST_SOURCE_SIBLINGS + 1) as u64),
            (4, (ZK_CAPSULE_PCS_MID_SYMBOLS + 1) as u64),
            (5, (ZK_CAPSULE_PCS_WORST_MID_SIBLINGS + 1) as u64),
        ];
        for (vector, length) in invalid {
            let mut hostile = bytes.clone();
            let offset = offsets[vector];
            hostile[offset..offset + LENGTH_BYTES].copy_from_slice(&length.to_le_bytes());
            assert!(matches!(
                ZkAuthorizationProof::from_bytes(&hostile),
                Err(ZkAuthorizationWireDecodeError::InvalidLength { actual, .. })
                    if actual == length
            ));
        }
    }

    #[test]
    fn invalid_object_shape_never_reaches_the_encoder() {
        let mut proof = fixture(17, 9);
        proof.source_commitment.cap.hashes.pop();
        assert!(matches!(
            proof.to_bytes(),
            Err(ZkAuthorizationWireEncodeError::InvalidShape {
                component: ZkAuthorizationProofComponent::SourceCap,
                ..
            })
        ));
    }

    #[test]
    fn fixed_width_arrays_have_no_hidden_length_prefixes() {
        assert_eq!(TAIL_SYMBOLS, 16);
        assert_eq!(UPPER_SYMBOLS, 256);
        let bytes = fixture(0, 0).to_bytes().unwrap();
        let offsets = preflight_wire(&bytes).unwrap().vector_length_offsets;
        assert_eq!(offsets[0], 0);
        assert_eq!(offsets[1], 12_968);
        assert_eq!(offsets[2], 13_752);
        assert_eq!(offsets[3], 38_720);
        assert_eq!(offsets[4], 38_728);
        assert_eq!(offsets[5], 72_016);
        assert_eq!(bytes.len(), 72_024);
    }
}
