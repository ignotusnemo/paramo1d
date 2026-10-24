// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Native algebra for the future witness-hiding authorization capsule.
//!
//! This module fixes natural novel-coefficient order, LOW-to-HIGH MLE folds,
//! contiguous affine-code leaves, the Phase-B `upper` linkage, and query-index
//! conventions in executable form. It is deliberately disconnected from the
//! active proof, wire format, transcript, and verifier.

use noid_core::mle::evaluate::evaluate_slice;
use noid_core::mle::fold::fold_variable_inplace;
use noid_core::{Block128, Block256, TowerField};

use crate::zk_affine_code::{AffineHighPaddingRankCertificate, ZkAffineCodeError, ZkAffineLchCode};
use crate::zk_capsule::ZK_AUTH_CAPSULE_GEOMETRY;

pub const JOINT_SOURCE_BANK_SYMBOLS: usize = ZK_AUTH_CAPSULE_GEOMETRY.source_bank_symbols_per_leaf;
pub const JOINT_SOURCE_COMPANION_SYMBOLS: usize =
    ZK_AUTH_CAPSULE_GEOMETRY.source_companion_symbols_per_leaf;
pub const JOINT_SOURCE_COMPANION_LANES: usize = 2 * JOINT_SOURCE_COMPANION_SYMBOLS;
pub const JOINT_SOURCE_LOGICAL_SYMBOLS: usize = ZK_AUTH_CAPSULE_GEOMETRY.source_leaf_symbols;
/// Canonical wire lanes per mixed source leaf: for each of eight positions,
/// one bank lane followed by the companion's low and high lanes.
pub const JOINT_SOURCE_LEAF_SYMBOLS: usize =
    JOINT_SOURCE_BANK_SYMBOLS + JOINT_SOURCE_COMPANION_LANES;
pub const SOURCE_STANDARD_FOLDS: usize = ZK_AUTH_CAPSULE_GEOMETRY.source_standard_fold_log;
pub const MID_STANDARD_FOLDS: usize = ZK_AUTH_CAPSULE_GEOMETRY.second_wide_fold_log;
pub const OWNER_STATE_POINT_VARS: usize = ZK_AUTH_CAPSULE_GEOMETRY.state_vars;
pub const OWNER_BANK_POINT_VARS: usize = ZK_AUTH_CAPSULE_GEOMETRY.bank_log;
pub const OWNER_STATE_RELATION_LEN: usize = ZK_AUTH_CAPSULE_GEOMETRY.state_len;
pub const OWNER_BANK_RELATION_LEN: usize = ZK_AUTH_CAPSULE_GEOMETRY.bank_len;
pub const PHASE_B_LOW_VARS: usize =
    SOURCE_STANDARD_FOLDS + MID_STANDARD_FOLDS + ZK_AUTH_CAPSULE_GEOMETRY.tail_local_fold_log;
pub const PHASE_B_HIGH_VARS: usize = OWNER_BANK_POINT_VARS - PHASE_B_LOW_VARS;
pub const UPPER_SYMBOLS: usize = 1 << PHASE_B_LOW_VARS;
pub const TAIL_SYMBOLS: usize = ZK_AUTH_CAPSULE_GEOMETRY.tail_len;
pub const FINAL_H_SYMBOLS: usize = ZK_AUTH_CAPSULE_GEOMETRY.final_h_len;
pub const SOURCE_QUERY_BITS: usize = ZK_AUTH_CAPSULE_GEOMETRY.query_width_bits;

const SOURCE_LOCAL_BITS: usize = SOURCE_STANDARD_FOLDS;
const MID_LOCAL_BITS: usize = MID_STANDARD_FOLDS;

const _: () =
    assert!(JOINT_SOURCE_BANK_SYMBOLS + JOINT_SOURCE_COMPANION_LANES == JOINT_SOURCE_LEAF_SYMBOLS);
const _: () = assert!(JOINT_SOURCE_LEAF_SYMBOLS == 24);
const _: () = assert!(JOINT_SOURCE_LOGICAL_SYMBOLS == 16);
const _: () = assert!(JOINT_SOURCE_BANK_SYMBOLS == 1 << SOURCE_STANDARD_FOLDS);
const _: () = assert!(ZK_AUTH_CAPSULE_GEOMETRY.mid_leaf_symbols == 1 << MID_STANDARD_FOLDS);
const _: () = assert!(OWNER_BANK_POINT_VARS - OWNER_STATE_POINT_VARS == 2);
const _: () = assert!(PHASE_B_LOW_VARS == 8);
const _: () = assert!(PHASE_B_HIGH_VARS == 3);
const _: () = assert!(UPPER_SYMBOLS == 256);
const _: () = assert!(TAIL_SYMBOLS == 2 * FINAL_H_SYMBOLS);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkCapsuleAlgebraError {
    SourceLeafOutOfRange,
    MidLeafOutOfRange,
    SourceCodewordLengthMismatch,
    MidCodewordLengthMismatch,
    AffineCode(ZkAffineCodeError),
}

impl From<ZkAffineCodeError> for ZkCapsuleAlgebraError {
    fn from(value: ZkAffineCodeError) -> Self {
        Self::AffineCode(value)
    }
}

/// Native decomposition of one uniform 13-bit joint-source-leaf query.
///
/// Bit numbering is LSB-first. For source bits `s[0..13]`:
///
/// - source path directions are `s[0..10]`, source cap is `s[10..13]`;
/// - after three adjacent folds, the source leaf is the mid position;
/// - mid member bits are `s[0..4]` and mid leaf bits are `s[4..13]`;
/// - mid path is `s[4..10]`, mid cap is `s[10..13]`.
///
/// The path-direction union carries `s[0..10]`. Three shared auxiliary cells
/// carry `s[10..13]` and select both eight-node caps. The dense paths expose
/// both roots from their final feed-forward node expressions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZkCapsuleQueryMapping {
    pub source_leaf_index: usize,
    pub source_bits_lsb: [bool; SOURCE_QUERY_BITS],
    pub source_path_index: usize,
    pub source_cap_index: usize,
    pub mid_position: usize,
    pub mid_leaf_index: usize,
    pub mid_member_index: usize,
    pub mid_path_index: usize,
    pub mid_cap_index: usize,
}

impl ZkCapsuleQueryMapping {
    /// Recompose the source leaf from its source-tree path and cap indices.
    #[inline]
    pub const fn source_tree_roundtrip(&self) -> usize {
        (self.source_cap_index << ZK_AUTH_CAPSULE_GEOMETRY.source_path_depth)
            | self.source_path_index
    }

    /// Recompose the mid leaf from its mid-tree path and cap indices.
    #[inline]
    pub const fn mid_tree_roundtrip(&self) -> usize {
        (self.mid_cap_index << ZK_AUTH_CAPSULE_GEOMETRY.mid_path_depth) | self.mid_path_index
    }

    /// Recompose the source leaf from the mid leaf and selected mid cell.
    #[inline]
    pub const fn source_from_mid_roundtrip(&self) -> usize {
        (self.mid_leaf_index << MID_LOCAL_BITS) | self.mid_member_index
    }
}

/// Pack one bank coset and one wide companion coset as
/// `[bank0, companion0.lo, companion0.hi, ..., bank7, companion7.hi]`.
pub fn interleave_joint_source_leaf(
    bank: &[Block128; JOINT_SOURCE_BANK_SYMBOLS],
    companion: &[Block256; JOINT_SOURCE_COMPANION_SYMBOLS],
) -> [Block128; JOINT_SOURCE_LEAF_SYMBOLS] {
    std::array::from_fn(|slot| {
        let position = slot / 3;
        match slot % 3 {
            0 => bank[position],
            1 => companion[position].lo,
            _ => companion[position].hi,
        }
    })
}

/// The eight contiguous affine-code positions opened from each equal encoded
/// bank for one joint source leaf.
pub fn joint_source_leaf_positions(
    source_leaf_index: usize,
) -> Result<[usize; JOINT_SOURCE_BANK_SYMBOLS], ZkCapsuleAlgebraError> {
    let g = ZK_AUTH_CAPSULE_GEOMETRY;
    if source_leaf_index >= g.source_leaf_count {
        return Err(ZkCapsuleAlgebraError::SourceLeafOutOfRange);
    }
    let start = source_leaf_index << SOURCE_LOCAL_BITS;
    Ok(std::array::from_fn(|member| start | member))
}

/// Apply the affine encoder's structural hiding certificate to the actual
/// source-leaf query map. Repeated leaves are harmless: their eight codeword
/// positions are deduplicated before the rank is certified.
pub fn certify_source_query_hiding_rank(
    code: &ZkAffineLchCode,
    source_leaf_indices: &[usize],
) -> Result<AffineHighPaddingRankCertificate, ZkCapsuleAlgebraError> {
    let mut positions = Vec::with_capacity(source_leaf_indices.len() * JOINT_SOURCE_BANK_SYMBOLS);
    for &leaf in source_leaf_indices {
        positions.extend_from_slice(&joint_source_leaf_positions(leaf)?);
    }
    Ok(code.certify_high_padding_rank(&positions)?)
}

/// Materialize one adjacent joint leaf from the two equal affine codewords.
pub fn build_joint_source_leaf(
    bank_codeword: &[Block128],
    companion_codeword: &[Block256],
    source_leaf_index: usize,
) -> Result<[Block128; JOINT_SOURCE_LEAF_SYMBOLS], ZkCapsuleAlgebraError> {
    let g = ZK_AUTH_CAPSULE_GEOMETRY;
    if bank_codeword.len() != g.source_domain_len || companion_codeword.len() != g.source_domain_len
    {
        return Err(ZkCapsuleAlgebraError::SourceCodewordLengthMismatch);
    }
    let positions = joint_source_leaf_positions(source_leaf_index)?;
    let bank = std::array::from_fn(|member| bank_codeword[positions[member]]);
    let companion = std::array::from_fn(|member| companion_codeword[positions[member]]);
    Ok(interleave_joint_source_leaf(&bank, &companion))
}

/// Materialize the C1 committed source leaf after the invertible local LCH
/// transform.  Bank and companion use the same transform, so the operation
/// commutes with the later characteristic-two masking line.
pub fn build_fold_normal_joint_source_leaf(
    code: &ZkAffineLchCode,
    bank_codeword: &[Block128],
    companion_codeword: &[Block256],
    source_leaf_index: usize,
) -> Result<[Block128; JOINT_SOURCE_LEAF_SYMBOLS], ZkCapsuleAlgebraError> {
    let raw = build_joint_source_leaf(bank_codeword, companion_codeword, source_leaf_index)?;
    let bank: [Block128; JOINT_SOURCE_BANK_SYMBOLS] = std::array::from_fn(|member| raw[3 * member]);
    let companion: [Block256; JOINT_SOURCE_COMPANION_SYMBOLS] =
        std::array::from_fn(|member| Block256::new(raw[3 * member + 1], raw[3 * member + 2]));
    let bank = code.fold_normalize_coset(&bank, 0, source_leaf_index)?;
    let companion = code.fold_normalize_coset(&companion, 0, source_leaf_index)?;
    let bank: [Block128; JOINT_SOURCE_BANK_SYMBOLS] = bank
        .try_into()
        .unwrap_or_else(|_| unreachable!("source transform preserves eight symbols"));
    let companion: [Block256; JOINT_SOURCE_COMPANION_SYMBOLS] = companion
        .try_into()
        .unwrap_or_else(|_| unreachable!("source transform preserves eight symbols"));
    Ok(interleave_joint_source_leaf(&bank, &companion))
}

/// Materialize one contiguous 16-symbol mid leaf.
pub fn build_mid_leaf<F: Copy>(
    mid_codeword: &[F],
    mid_leaf_index: usize,
) -> Result<[F; 1 << MID_STANDARD_FOLDS], ZkCapsuleAlgebraError> {
    let g = ZK_AUTH_CAPSULE_GEOMETRY;
    if mid_codeword.len() != 1usize << g.mid_domain_log {
        return Err(ZkCapsuleAlgebraError::MidCodewordLengthMismatch);
    }
    if mid_leaf_index >= g.mid_leaf_count {
        return Err(ZkCapsuleAlgebraError::MidLeafOutOfRange);
    }
    let start = mid_leaf_index << MID_LOCAL_BITS;
    Ok(std::array::from_fn(|member| mid_codeword[start | member]))
}

/// Materialize the C1 committed mid leaf after its invertible four-round
/// local LCH transform.
pub fn build_fold_normal_mid_leaf<F>(
    code: &ZkAffineLchCode,
    mid_codeword: &[F],
    mid_leaf_index: usize,
) -> Result<[F; 1 << MID_STANDARD_FOLDS], ZkCapsuleAlgebraError>
where
    F: TowerField + From<Block128>,
{
    let raw = build_mid_leaf(mid_codeword, mid_leaf_index)?;
    Ok(code
        .fold_normalize_coset(&raw, SOURCE_STANDARD_FOLDS, mid_leaf_index)?
        .try_into()
        .unwrap_or_else(|_| unreachable!("mid transform preserves sixteen symbols")))
}

/// Apply the characteristic-two masking line to all eight adjacent pairs.
///
/// `(1 - gamma) * bank + gamma * companion` is evaluated as
/// `bank + gamma * (bank + companion)`.
pub fn joint_source_line_fold<F>(
    joint_leaf: &[Block128; JOINT_SOURCE_LEAF_SYMBOLS],
    gamma: F,
) -> [F; JOINT_SOURCE_BANK_SYMBOLS]
where
    F: TowerField + From<Block128> + From<Block256>,
{
    std::array::from_fn(|position| {
        let bank = joint_leaf[3 * position];
        let companion = Block256::new(joint_leaf[3 * position + 1], joint_leaf[3 * position + 2]);
        let bank = F::from(bank);
        bank + gamma * (bank + F::from(companion))
    })
}

/// Fold one contiguous source coset through the selected affine LCH schedule.
/// Challenges consume logical variables 0, 1, and 2 in that order.
pub fn source_standard_fold3<F>(
    code: &ZkAffineLchCode,
    symbols: &[F; JOINT_SOURCE_BANK_SYMBOLS],
    source_leaf_index: usize,
    challenges: &[F; SOURCE_STANDARD_FOLDS],
) -> Result<F, ZkCapsuleAlgebraError>
where
    F: TowerField + From<Block128>,
{
    if source_leaf_index >= ZK_AUTH_CAPSULE_GEOMETRY.source_leaf_count {
        return Err(ZkCapsuleAlgebraError::SourceLeafOutOfRange);
    }
    Ok(code.fold_contiguous_coset_extension(symbols, 0, source_leaf_index, challenges)?)
}

/// Apply the masking-line fold and then the three LOW-to-HIGH source folds.
pub fn fold_joint_source_leaf<F>(
    code: &ZkAffineLchCode,
    joint_leaf: &[Block128; JOINT_SOURCE_LEAF_SYMBOLS],
    gamma: F,
    source_leaf_index: usize,
    challenges: &[F; SOURCE_STANDARD_FOLDS],
) -> Result<F, ZkCapsuleAlgebraError>
where
    F: TowerField + From<Block128> + From<Block256>,
{
    let virtual_masked = joint_source_line_fold(joint_leaf, gamma);
    source_standard_fold3(code, &virtual_masked, source_leaf_index, challenges)
}

/// Fold a C1 fold-normal source leaf.  All index-dependent inverse LCH
/// butterflies were applied before commitment, leaving only the actual wide
/// challenge products here.
pub fn fold_normal_joint_source_leaf<F>(
    joint_leaf: &[Block128; JOINT_SOURCE_LEAF_SYMBOLS],
    gamma: F,
    challenges: &[F; SOURCE_STANDARD_FOLDS],
) -> F
where
    F: TowerField + From<Block128> + From<Block256>,
{
    let virtual_masked = joint_source_line_fold(joint_leaf, gamma);
    evaluate_slice(&virtual_masked, challenges)
}

/// Fold one contiguous mid coset through logical variables 3..6.
pub fn mid_standard_fold4<F>(
    code: &ZkAffineLchCode,
    symbols: &[F; 1 << MID_STANDARD_FOLDS],
    mid_leaf_index: usize,
    challenges: &[F; MID_STANDARD_FOLDS],
) -> Result<F, ZkCapsuleAlgebraError>
where
    F: TowerField + From<Block128>,
{
    if mid_leaf_index >= ZK_AUTH_CAPSULE_GEOMETRY.mid_leaf_count {
        return Err(ZkCapsuleAlgebraError::MidLeafOutOfRange);
    }
    Ok(code.fold_contiguous_coset_extension(
        symbols,
        SOURCE_STANDARD_FOLDS,
        mid_leaf_index,
        challenges,
    )?)
}

/// Fold a C1 fold-normal mid leaf at the four actual wide challenges.
pub fn fold_normal_mid_leaf<F>(
    symbols: &[F; 1 << MID_STANDARD_FOLDS],
    challenges: &[F; MID_STANDARD_FOLDS],
) -> F
where
    F: TowerField,
{
    evaluate_slice(symbols, challenges)
}

/// Recover one raw mid-codeword member from its committed fold-normal leaf.
/// Native verification uses the explicit inverse for clarity; the recursive
/// trace evaluates the same selected inverse network without materializing a
/// second committed leaf.
pub fn fold_normal_mid_raw_member<F>(
    code: &ZkAffineLchCode,
    symbols: &[F; 1 << MID_STANDARD_FOLDS],
    mid_leaf_index: usize,
    member_index: usize,
) -> Result<F, ZkCapsuleAlgebraError>
where
    F: TowerField + From<Block128>,
{
    if member_index >= 1 << MID_STANDARD_FOLDS {
        return Err(ZkCapsuleAlgebraError::MidLeafOutOfRange);
    }
    let raw = code.fold_denormalize_coset(symbols, SOURCE_STANDARD_FOLDS, mid_leaf_index)?;
    Ok(raw[member_index])
}

/// Re-encode the revealed 16-cell tail with the surviving prefix of the
/// master affine transform after seven LOW-to-HIGH folds.
pub fn encode_tail16<F>(
    code: &ZkAffineLchCode,
    tail: &[F; TAIL_SYMBOLS],
) -> Result<Vec<F>, ZkCapsuleAlgebraError>
where
    F: TowerField + From<Block128>,
{
    Ok(code.encode_extension_after_low_folds(tail, SOURCE_STANDARD_FOLDS + MID_STANDARD_FOLDS)?)
}

/// Fold logical variable 7 locally. Adjacent cells, not the two table halves,
/// are paired because the entire Phase-B order is LOW-to-HIGH.
pub fn tail16_local_fold<F: TowerField>(
    tail: &[F; TAIL_SYMBOLS],
    challenge: F,
) -> [F; FINAL_H_SYMBOLS] {
    std::array::from_fn(|index| {
        let at_zero = tail[2 * index];
        let at_one = tail[2 * index + 1];
        at_zero + challenge * (at_zero + at_one)
    })
}

/// Contract the three highest claim coordinates for each Boolean assignment
/// of the eight LOW Phase-B variables. The result is the public `upper[256]`.
pub fn contract_high3_for_each_low8<F: TowerField>(
    bank: &[F; OWNER_BANK_RELATION_LEN],
    high_point: &[F; PHASE_B_HIGH_VARS],
) -> [F; UPPER_SYMBOLS] {
    std::array::from_fn(|low_index| {
        let high_line: [F; 1 << PHASE_B_HIGH_VARS] =
            std::array::from_fn(|high_index| bank[low_index | (high_index << PHASE_B_LOW_VARS)]);
        evaluate_slice(&high_line, high_point)
    })
}

/// Evaluate `upper` at either the original low claim point or the random
/// Phase-B fold point.
pub fn evaluate_upper_at_low8<F: TowerField>(
    upper: &[F; UPPER_SYMBOLS],
    low_point: &[F; PHASE_B_LOW_VARS],
) -> F {
    evaluate_slice(upper, low_point)
}

/// Fold all eight LOW variables of a bank table in protocol order. The result
/// is the 8-cell high-variable table linked to `upper(beta)`.
pub fn fold_bank_low8<F: TowerField>(
    bank: &[F; OWNER_BANK_RELATION_LEN],
    beta_low: &[F; PHASE_B_LOW_VARS],
) -> [F; FINAL_H_SYMBOLS] {
    let mut folded = bank.to_vec();
    for &challenge in beta_low {
        fold_variable_inplace(&mut folded, challenge, 0);
    }
    folded
        .try_into()
        .expect("eight low folds of a 2^11 table leave 2^3 cells")
}

/// Construct `r9 || [0, 0]` solely to check fundamental-slice alignment.
///
/// # Warning
///
/// The resulting bank evaluation selects the raw `[0, 512)` slice and must
/// never be serialized as an authorization opening claim. Protocol terminal
/// points remain arbitrary 11-variable challenges and use
/// [`evaluate_fundamental_slice_embedding`] instead.
pub fn fundamental_slice_alignment_point<F: TowerField>(
    state_point: &[F; OWNER_STATE_POINT_VARS],
) -> [F; OWNER_BANK_POINT_VARS] {
    let mut lifted = [F::ZERO; OWNER_BANK_POINT_VARS];
    lifted[..OWNER_STATE_POINT_VARS].copy_from_slice(state_point);
    lifted
}

/// Equality-selector weight of the two high Boolean coordinates `[0, 0]`.
pub fn eq_high_zero<F: TowerField>(high: &[F; 2]) -> F {
    (F::ONE - high[0]) * (F::ONE - high[1])
}

/// Embed one 9-variable relation table into the high-`00` state slice of an
/// 11-variable table, with every other high slice identically zero.
pub fn fundamental_slice_relation_embedding<F: TowerField>(
    relation: &[F; OWNER_STATE_RELATION_LEN],
) -> [F; OWNER_BANK_RELATION_LEN] {
    let mut embedded = [F::ZERO; OWNER_BANK_RELATION_LEN];
    embedded[..OWNER_STATE_RELATION_LEN].copy_from_slice(relation);
    embedded
}

/// Evaluate the state-slice embedding at an arbitrary 11-variable terminal
/// point without replacing its two high challenges by zero.
pub fn evaluate_fundamental_slice_embedding<F: TowerField>(
    relation: &[F; OWNER_STATE_RELATION_LEN],
    terminal_point: &[F; OWNER_BANK_POINT_VARS],
) -> F {
    let high_point = [
        terminal_point[OWNER_STATE_POINT_VARS],
        terminal_point[OWNER_STATE_POINT_VARS + 1],
    ];
    evaluate_slice(relation, &terminal_point[..OWNER_STATE_POINT_VARS]) * eq_high_zero(&high_point)
}

/// Convert a checked joint-source-leaf index to its LSB-first query bits.
pub fn source_query_bits(
    source_leaf_index: usize,
) -> Result<[bool; SOURCE_QUERY_BITS], ZkCapsuleAlgebraError> {
    if source_leaf_index >= ZK_AUTH_CAPSULE_GEOMETRY.source_leaf_count {
        return Err(ZkCapsuleAlgebraError::SourceLeafOutOfRange);
    }
    Ok(std::array::from_fn(|bit| {
        (source_leaf_index >> bit) & 1 == 1
    }))
}

/// Recompose a joint source leaf from the complete LSB-first query bit set.
pub fn source_leaf_from_query_bits(bits: &[bool; SOURCE_QUERY_BITS]) -> usize {
    bits.iter().enumerate().fold(0usize, |index, (bit, set)| {
        index | (usize::from(*set) << bit)
    })
}

/// Map one uniform joint-source-leaf query into both authenticated trees.
pub fn map_source_query_leaf(
    source_leaf_index: usize,
) -> Result<ZkCapsuleQueryMapping, ZkCapsuleAlgebraError> {
    let g = ZK_AUTH_CAPSULE_GEOMETRY;
    let source_bits_lsb = source_query_bits(source_leaf_index)?;
    let source_path_index = source_leaf_index & ((1usize << g.source_path_depth) - 1);
    let source_cap_index = source_leaf_index >> g.source_path_depth;

    // Three adjacent folds collapse source leaf L directly to mid position L.
    let mid_position = source_leaf_index;
    let mid_leaf_index = mid_position >> MID_LOCAL_BITS;
    let mid_member_index = mid_position & ((1usize << MID_LOCAL_BITS) - 1);
    let mid_path_index = mid_leaf_index & ((1usize << g.mid_path_depth) - 1);
    let mid_cap_index = mid_leaf_index >> g.mid_path_depth;

    Ok(ZkCapsuleQueryMapping {
        source_leaf_index,
        source_bits_lsb,
        source_path_index,
        source_cap_index,
        mid_position,
        mid_leaf_index,
        mid_member_index,
        mid_path_index,
        mid_cap_index,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn elem(index: usize, domain: u128) -> Block128 {
        Block128::from(
            domain
                .wrapping_mul(index as u128 + 1)
                .rotate_left((index % 127) as u32)
                ^ (index as u128 * 0x9E37_79B9),
        )
    }

    fn message(domain: u128) -> [Block128; OWNER_BANK_RELATION_LEN] {
        std::array::from_fn(|index| elem(index, domain))
    }

    #[test]
    fn joint_leaf_layout_and_contiguous_positions_are_exact() {
        let bank = std::array::from_fn(|i| elem(i, 0xB4A9));
        let companion =
            std::array::from_fn(|i| Block256::new(elem(i, 0xC09A), elem(i + 100, 0xC09B)));
        let joint = interleave_joint_source_leaf(&bank, &companion);
        for position in 0..JOINT_SOURCE_BANK_SYMBOLS {
            assert_eq!(joint[3 * position], bank[position]);
            assert_eq!(joint[3 * position + 1], companion[position].lo);
            assert_eq!(joint[3 * position + 2], companion[position].hi);
        }

        for leaf in [
            0,
            1,
            255,
            256,
            ZK_AUTH_CAPSULE_GEOMETRY.source_leaf_count - 1,
        ] {
            let positions = joint_source_leaf_positions(leaf).unwrap();
            assert_eq!(positions, std::array::from_fn(|member| 8 * leaf + member));
        }

        let code = ZkAffineLchCode::selected().unwrap();
        let leaves: Vec<usize> = (0..ZK_AUTH_CAPSULE_GEOMETRY.query_count()).collect();
        let certificate = certify_source_query_hiding_rank(&code, &leaves).unwrap();
        assert_eq!(certificate.distinct_query_count, 520);
        assert_eq!(certificate.certified_rank, 520);

        let repeated = [17usize; 65];
        let certificate = certify_source_query_hiding_rank(&code, &repeated).unwrap();
        assert_eq!(certificate.distinct_query_count, 8);
        assert_eq!(certificate.certified_rank, 8);
    }

    #[test]
    fn gamma_then_source_and_mid_folds_match_full_affine_codewords() {
        let code = ZkAffineLchCode::selected().unwrap();
        let bank = message(0xB4A9);
        let companion: [Block256; OWNER_BANK_RELATION_LEN] =
            std::array::from_fn(|index| Block256::new(elem(index, 0xC09A), elem(index, 0xC09B)));
        let gamma = Block256::new(elem(3, 0x6A77A), elem(4, 0x6A77B));
        let source_challenges =
            std::array::from_fn(|i| Block256::new(elem(i, 0x503CE), elem(i, 0x503CF)));
        let mid_challenges =
            std::array::from_fn(|i| Block256::new(elem(i, 0xA11D), elem(i, 0xA11E)));

        let bank_code = code.encode(&bank).unwrap();
        let companion_code = code
            .encode_extension_after_low_folds(&companion, 0)
            .unwrap();
        let virtual_message: Vec<Block256> = bank
            .iter()
            .zip(companion.iter())
            .map(|(&b, &c)| {
                let b = Block256::from(b);
                b + gamma * (b + c)
            })
            .collect();
        let mut mid_code = code
            .encode_extension_after_low_folds(&virtual_message, 0)
            .unwrap();
        for (round, &challenge) in source_challenges.iter().enumerate() {
            mid_code = code
                .fold_codeword_once_extension(&mid_code, round, challenge)
                .unwrap();
        }

        for source_leaf in [
            0,
            1,
            127,
            4_097,
            ZK_AUTH_CAPSULE_GEOMETRY.source_leaf_count - 1,
        ] {
            let joint = build_joint_source_leaf(&bank_code, &companion_code, source_leaf).unwrap();
            assert_eq!(
                fold_joint_source_leaf(&code, &joint, gamma, source_leaf, &source_challenges,)
                    .unwrap(),
                mid_code[source_leaf]
            );
            let normal = build_fold_normal_joint_source_leaf(
                &code,
                &bank_code,
                &companion_code,
                source_leaf,
            )
            .unwrap();
            assert_eq!(
                fold_normal_joint_source_leaf(&normal, gamma, &source_challenges),
                mid_code[source_leaf]
            );
        }

        let mut tail_code = mid_code.clone();
        for (inner, &challenge) in mid_challenges.iter().enumerate() {
            tail_code = code
                .fold_codeword_once_extension(&tail_code, SOURCE_STANDARD_FOLDS + inner, challenge)
                .unwrap();
        }
        for mid_leaf in [0, 1, 31, 255, ZK_AUTH_CAPSULE_GEOMETRY.mid_leaf_count - 1] {
            let leaf = build_mid_leaf(&mid_code, mid_leaf).unwrap();
            assert_eq!(
                mid_standard_fold4(&code, &leaf, mid_leaf, &mid_challenges).unwrap(),
                tail_code[mid_leaf]
            );
            let normal = build_fold_normal_mid_leaf(&code, &mid_code, mid_leaf).unwrap();
            assert_eq!(
                fold_normal_mid_leaf(&normal, &mid_challenges),
                tail_code[mid_leaf]
            );
            for member in 0..1 << MID_STANDARD_FOLDS {
                assert_eq!(
                    fold_normal_mid_raw_member(&code, &normal, mid_leaf, member).unwrap(),
                    leaf[member]
                );
            }
        }
    }

    #[test]
    fn phase_b_upper_and_tail_link_the_same_bank() {
        let code = ZkAffineLchCode::selected().unwrap();
        let bank = message(0xB411C);
        let claim_point: [Block128; OWNER_BANK_POINT_VARS] =
            std::array::from_fn(|i| elem(i, 0xC1A1));
        let low_point: [Block128; PHASE_B_LOW_VARS] = std::array::from_fn(|i| claim_point[i]);
        let high_point: [Block128; PHASE_B_HIGH_VARS] =
            std::array::from_fn(|i| claim_point[PHASE_B_LOW_VARS + i]);
        let beta: [Block128; PHASE_B_LOW_VARS] = std::array::from_fn(|i| elem(i, 0xBE7A));

        let upper = contract_high3_for_each_low8(&bank, &high_point);
        assert_eq!(
            evaluate_upper_at_low8(&upper, &low_point),
            evaluate_slice(&bank, &claim_point)
        );

        let h = fold_bank_low8(&bank, &beta);
        assert_eq!(
            evaluate_upper_at_low8(&upper, &beta),
            evaluate_slice(&h, &high_point)
        );

        let mut after_seven = bank.to_vec();
        for &challenge in &beta[..SOURCE_STANDARD_FOLDS + MID_STANDARD_FOLDS] {
            fold_variable_inplace(&mut after_seven, challenge, 0);
        }
        let tail: [Block128; TAIL_SYMBOLS] = after_seven.try_into().unwrap();
        assert_eq!(tail16_local_fold(&tail, beta[7]), h);
        assert_eq!(encode_tail16(&code, &tail).unwrap().len(), 512);
    }

    #[test]
    fn fundamental_slice_embedding_uses_arbitrary_terminal_high_coordinates() {
        let relation = std::array::from_fn(|i| elem(i, 0xAE1A710));
        let embedded = fundamental_slice_relation_embedding(&relation);
        let terminal = std::array::from_fn(|i| elem(i + 17, 0x7E2A11));
        let low_point = std::array::from_fn(|i| terminal[i]);
        let alignment_point = fundamental_slice_alignment_point(&low_point);

        assert_eq!(
            evaluate_slice(&embedded, &alignment_point),
            evaluate_slice(&relation, &low_point)
        );
        assert_eq!(
            evaluate_slice(&embedded, &terminal),
            evaluate_fundamental_slice_embedding(&relation, &terminal)
        );
        assert_eq!(eq_high_zero(&[Block128::ZERO; 2]), Block128::ONE);
        assert_eq!(
            eq_high_zero(&[Block128::ONE, Block128::ZERO]),
            Block128::ZERO
        );
    }

    #[test]
    fn source_and_mid_query_mapping_roundtrips_exhaustively() {
        let g = ZK_AUTH_CAPSULE_GEOMETRY;
        assert_eq!(g.source_tree_depth, SOURCE_QUERY_BITS);
        assert_eq!(g.source_leaf_count, 1 << SOURCE_QUERY_BITS);

        for source_leaf in 0..g.source_leaf_count {
            let mapping = map_source_query_leaf(source_leaf).unwrap();
            assert_eq!(
                source_leaf_from_query_bits(&mapping.source_bits_lsb),
                source_leaf
            );
            assert_eq!(mapping.source_tree_roundtrip(), source_leaf);
            assert_eq!(mapping.mid_tree_roundtrip(), mapping.mid_leaf_index);
            assert_eq!(mapping.source_from_mid_roundtrip(), source_leaf);
            assert_eq!(mapping.mid_position, source_leaf);
            assert_eq!(mapping.mid_member_index, source_leaf & 15);
            assert_eq!(mapping.mid_leaf_index, source_leaf >> 4);
            assert_eq!(
                joint_source_leaf_positions(source_leaf).unwrap(),
                std::array::from_fn(|member| (source_leaf << SOURCE_LOCAL_BITS) | member)
            );
            assert_eq!(
                mapping.mid_position,
                (mapping.mid_leaf_index << MID_LOCAL_BITS) | mapping.mid_member_index
            );

            // Dense C1 paths carry source q0..q9 and mid q4..q9.  The shared
            // q10..q12 suffix selects both eight-node caps.
            for bit in 0..10 {
                assert_eq!(
                    (mapping.source_path_index >> bit) & 1,
                    (source_leaf >> bit) & 1
                );
            }
            for bit in 0..6 {
                assert_eq!(
                    (mapping.mid_path_index >> bit) & 1,
                    (source_leaf >> (bit + 4)) & 1
                );
            }
            assert_eq!(mapping.source_cap_index, source_leaf >> 10);
            assert_eq!(mapping.mid_cap_index, source_leaf >> 10);
        }

        assert_eq!(
            map_source_query_leaf(g.source_leaf_count),
            Err(ZkCapsuleAlgebraError::SourceLeafOutOfRange)
        );
    }

    #[test]
    fn source_queries_lift_each_tail_code_coordinate_with_exact_uniform_density() {
        let g = ZK_AUTH_CAPSULE_GEOMETRY;
        let mut preimages = vec![0usize; g.mid_leaf_count];
        for source_leaf in 0..g.source_leaf_count {
            let mapping = map_source_query_leaf(source_leaf).unwrap();
            preimages[mapping.mid_leaf_index] += 1;
        }
        assert!(
            preimages
                .iter()
                .all(|&count| count == 1usize << MID_LOCAL_BITS),
            "q -> q>>4 must give every tail-code coordinate sixteen preimages"
        );

        // An arbitrary tail-code error set therefore lifts to exactly the same
        // relative density in the uniform source-query domain.
        let marked = (0..g.mid_leaf_count)
            .filter(|index| (index * 17 + 5) % 29 < 7)
            .collect::<std::collections::BTreeSet<_>>();
        let lifted = (0..g.source_leaf_count)
            .filter(|&source_leaf| {
                let tail_position = map_source_query_leaf(source_leaf).unwrap().mid_leaf_index;
                marked.contains(&tail_position)
            })
            .count();
        assert_eq!(lifted, marked.len() * (1usize << MID_LOCAL_BITS));
        assert_eq!(
            lifted * g.mid_leaf_count,
            marked.len() * g.source_leaf_count
        );
    }

    #[test]
    fn tail_local_fold_consumes_the_low_remaining_variable() {
        let tail = std::array::from_fn(|i| elem(i, 0x7A11));
        let challenge = elem(4, 0x10CA1);
        let got = tail16_local_fold(&tail, challenge);
        let expected =
            std::array::from_fn(|i| tail[2 * i] + challenge * (tail[2 * i] + tail[2 * i + 1]));

        assert_eq!(got, expected);
        assert_eq!(
            tail16_local_fold(&tail, Block128::ZERO),
            std::array::from_fn(|i| tail[2 * i])
        );
        assert_eq!(
            tail16_local_fold(&tail, Block128::ONE),
            std::array::from_fn(|i| tail[2 * i + 1])
        );
    }
}
