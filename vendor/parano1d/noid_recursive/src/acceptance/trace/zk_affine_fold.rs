// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Bounded recursive trace primitives for the selected natural-order affine
//! LCH folds used by the witness-hiding authorization capsule.
//!
//! Capsule query positions are transcript witnesses, so no production helper
//! in this module accepts a build-time leaf index. Instead, each public
//! twiddle is represented as its exact affine function of the already
//! boolean, transcript-bound query-bit expressions. This keeps the recursive
//! matrix class-fixed across proofs.
//!
//! For one pair, the twiddle-dependent inverse-butterfly product and the fold
//! challenge product cost exactly two rows:
//!
//! ```text
//! v   = right + left
//! u   = left + v * twiddle(query_bits)
//! out = u + challenge * (u + v)
//! ```
//!
//! All remaining inverse-butterfly algebra is F128-linear. The source helper
//! additionally pays eight products for its `gamma` masking line.
//!
//! This module only provides arithmetic building blocks. It does not connect
//! them to a proof, transcript, Merkle opening, or acceptance region.

use noid_fri_binius::zk_affine_code::{ZkAffineCodeError, ZkAffineLchCode, AFFINE_CODE_LOG_LEN};
use noid_fri_binius::zk_capsule_algebra::{
    JOINT_SOURCE_BANK_SYMBOLS, JOINT_SOURCE_LEAF_SYMBOLS, MID_STANDARD_FOLDS, SOURCE_QUERY_BITS,
    SOURCE_STANDARD_FOLDS,
};

use super::{flat_of, mul_ext, mul_ext_base, ExtExpr, FieldR1csBuilder, LinExpr};

const MID_LEAF_QUERY_BIT_OFFSET: usize = MID_STANDARD_FOLDS;

const _: () = assert!(JOINT_SOURCE_BANK_SYMBOLS == 8);
const _: () = assert!(JOINT_SOURCE_LEAF_SYMBOLS == 24);
const _: () = assert!(SOURCE_STANDARD_FOLDS == 3);
const _: () = assert!(MID_STANDARD_FOLDS == 4);
const _: () = assert!(SOURCE_QUERY_BITS == 13);
const _: () = assert!(SOURCE_QUERY_BITS - MID_LEAF_QUERY_BIT_OFFSET == 9);

/// Build the exact selected-code twiddle as an affine expression in the
/// dynamic high bits of one global pair index.
///
/// `static_pair_index` supplies the low `dynamic_bit_shift` bits. Every bit
/// above it is supplied as an expression in LSB-first order. The selected LCH
/// twiddle table is affine in those block bits, so the coefficient of dynamic
/// bit `i` is obtained from the protocol-owned table itself as
/// `twiddle(base) + twiddle(base ^ (1 << (shift + i)))`.
fn affine_twiddle_from_pair_bits(
    code: &ZkAffineLchCode,
    layer: usize,
    static_pair_index: usize,
    dynamic_bit_shift: usize,
    dynamic_bits_lsb: &[LinExpr],
) -> Result<LinExpr, ZkAffineCodeError> {
    assert!(static_pair_index < (1usize << dynamic_bit_shift));
    assert_eq!(
        dynamic_bit_shift + dynamic_bits_lsb.len(),
        layer,
        "query bits must cover every non-static global pair-index bit"
    );

    let base = code.twiddle(layer, static_pair_index)?;
    let mut twiddle = LinExpr::constant(flat_of(base));
    for (bit, bit_expr) in dynamic_bits_lsb.iter().enumerate() {
        let pair_bit = dynamic_bit_shift + bit;
        let toggled = code.twiddle(layer, static_pair_index | (1usize << pair_bit))?;
        let delta = base + toggled;
        twiddle = twiddle.add(&bit_expr.scale(flat_of(delta)));
    }
    Ok(twiddle)
}

/// One affine-LCH pair fold whose complete global pair index is represented by
/// static low pair-within-coset bits and dynamic transcript query bits.
///
/// This is intentionally private: a production caller cannot substitute a
/// proof-dependent leaf index as a build-time `usize`.
fn affine_lch_fold_pair_from_bits_trace(
    b: &mut FieldR1csBuilder,
    code: &ZkAffineLchCode,
    folds_done: usize,
    static_pair_index: usize,
    dynamic_bit_shift: usize,
    dynamic_pair_bits_lsb: &[LinExpr],
    left: &ExtExpr,
    right: &ExtExpr,
    challenge: &ExtExpr,
) -> Result<ExtExpr, ZkAffineCodeError> {
    if folds_done >= AFFINE_CODE_LOG_LEN {
        return Err(ZkAffineCodeError::FoldCountOutOfRange);
    }
    let layer = AFFINE_CODE_LOG_LEN - folds_done - 1;
    let twiddle = affine_twiddle_from_pair_bits(
        code,
        layer,
        static_pair_index,
        dynamic_bit_shift,
        dynamic_pair_bits_lsb,
    )?;

    // Exact inverse of the selected forward butterfly. The public twiddle was
    // linear for a fixed index; with a transcript-witness index its product
    // with v is the first required multiplication row.
    let v = right.add(left);
    let u = left.add(&mul_ext_base(b, &v, &twiddle));
    let u_plus_v = u.add(&v);
    Ok(u.add(&mul_ext(b, challenge, &u_plus_v)))
}

/// Fold one complete contiguous coset whose coset index is supplied entirely
/// by transcript query bits in LSB-first order.
///
/// At each inner layer, `pair` supplies the static low bits of the global pair
/// index and the coset bits are shifted above them, exactly matching native
/// `global_pair_index = coset_index * next_len + pair`.
fn affine_lch_fold_contiguous_coset_from_bits_trace(
    b: &mut FieldR1csBuilder,
    code: &ZkAffineLchCode,
    symbols: &[ExtExpr],
    folds_done: usize,
    coset_index_bits_lsb: &[LinExpr],
    challenges: &[ExtExpr],
) -> Result<ExtExpr, ZkAffineCodeError> {
    let Some(total_folds) = folds_done.checked_add(challenges.len()) else {
        return Err(ZkAffineCodeError::FoldCountOutOfRange);
    };
    if total_folds > AFFINE_CODE_LOG_LEN {
        return Err(ZkAffineCodeError::FoldCountOutOfRange);
    }
    let expected_coset_len = 1usize << challenges.len();
    if symbols.len() != expected_coset_len {
        return Err(ZkAffineCodeError::CosetLength {
            expected: expected_coset_len,
            actual: symbols.len(),
        });
    }
    assert_eq!(
        coset_index_bits_lsb.len(),
        AFFINE_CODE_LOG_LEN - total_folds,
        "query bits must encode the full bounded coset index"
    );

    let mut current = symbols.to_vec();
    for (inner_fold, challenge) in challenges.iter().enumerate() {
        let next_len = current.len() / 2;
        let static_pair_bits = next_len.trailing_zeros() as usize;
        let mut next = Vec::with_capacity(next_len);
        for pair in 0..next_len {
            next.push(affine_lch_fold_pair_from_bits_trace(
                b,
                code,
                folds_done + inner_fold,
                pair,
                static_pair_bits,
                coset_index_bits_lsb,
                &current[2 * pair],
                &current[2 * pair + 1],
                challenge,
            )?);
        }
        current = next;
    }
    Ok(current[0].clone())
}

/// Trace twin of the eight characteristic-two masking-line products:
/// `bank + gamma * (bank + companion)`.
///
/// A witness `gamma` costs exactly eight multiplication rows.
pub fn joint_source_line_fold_trace(
    b: &mut FieldR1csBuilder,
    joint_leaf: &[LinExpr; JOINT_SOURCE_LEAF_SYMBOLS],
    gamma: &ExtExpr,
) -> [ExtExpr; JOINT_SOURCE_BANK_SYMBOLS] {
    std::array::from_fn(|symbol| {
        let bank = ExtExpr::from_base(joint_leaf[3 * symbol].clone());
        let companion = ExtExpr::new(
            joint_leaf[3 * symbol + 1].clone(),
            joint_leaf[3 * symbol + 2].clone(),
        );
        bank.add(&mul_ext(b, gamma, &bank.add(&companion)))
    })
}

/// Three selected affine-LCH folds over one contiguous eight-symbol source
/// coset. `source_query_bits[0..13]` are the transcript-bound source-leaf
/// index bits `q0..q12`, LSB first. Challenges consume logical variables
/// 0, 1, and 2 LOW-to-HIGH.
///
/// The query bits must already have been booleanity-constrained and rebound
/// to the transcript seed. This helper allocates exactly
/// `2 * (4 + 2 + 1) = 14` multiplication rows.
pub fn source_standard_fold3_trace(
    b: &mut FieldR1csBuilder,
    code: &ZkAffineLchCode,
    symbols: &[ExtExpr; JOINT_SOURCE_BANK_SYMBOLS],
    source_query_bits: &[LinExpr; SOURCE_QUERY_BITS],
    challenges: &[ExtExpr; SOURCE_STANDARD_FOLDS],
) -> Result<ExtExpr, ZkAffineCodeError> {
    affine_lch_fold_contiguous_coset_from_bits_trace(
        b,
        code,
        symbols,
        0,
        source_query_bits,
        challenges,
    )
}

/// Apply the joint source `gamma` line and then the three selected LOW-to-HIGH
/// affine-LCH folds. With witness challenges this allocates exactly
/// `8 + 2 * (4 + 2 + 1) = 22` multiplication rows.
pub fn fold_joint_source_leaf_trace(
    b: &mut FieldR1csBuilder,
    code: &ZkAffineLchCode,
    joint_leaf: &[LinExpr; JOINT_SOURCE_LEAF_SYMBOLS],
    gamma: &ExtExpr,
    source_query_bits: &[LinExpr; SOURCE_QUERY_BITS],
    challenges: &[ExtExpr; SOURCE_STANDARD_FOLDS],
) -> Result<ExtExpr, ZkAffineCodeError> {
    let masked = joint_source_line_fold_trace(b, joint_leaf, gamma);
    source_standard_fold3_trace(b, code, &masked, source_query_bits, challenges)
}

/// Plain multilinear fold of a committed fold-normal table.  The local LCH
/// inverse butterflies are already part of the committed leaf, so only the
/// actual extension-field challenges allocate rows here.
fn fold_normal_table_trace(
    b: &mut FieldR1csBuilder,
    symbols: &[ExtExpr],
    challenges: &[ExtExpr],
) -> ExtExpr {
    assert_eq!(symbols.len(), 1usize << challenges.len());
    let mut current = symbols.to_vec();
    for challenge in challenges {
        current = current
            .chunks_exact(2)
            .map(|pair| pair[0].add(&mul_ext(b, challenge, &pair[0].add(&pair[1]))))
            .collect();
    }
    debug_assert_eq!(current.len(), 1);
    current.pop().expect("fold-normal table leaves one value")
}

/// Apply the wide masking line and three ordinary MLE folds to a C1 source
/// leaf.  This costs `8 * 3 + 7 * 3 = 45` base-field rows.
pub fn fold_normal_joint_source_leaf_trace(
    b: &mut FieldR1csBuilder,
    joint_leaf: &[LinExpr; JOINT_SOURCE_LEAF_SYMBOLS],
    gamma: &ExtExpr,
    challenges: &[ExtExpr; SOURCE_STANDARD_FOLDS],
) -> ExtExpr {
    let masked = joint_source_line_fold_trace(b, joint_leaf, gamma);
    fold_normal_table_trace(b, &masked, challenges)
}

/// Four ordinary MLE folds of a C1 fold-normal mid leaf.  Fifteen
/// extension-field products cost exactly 45 base-field rows.
pub fn fold_normal_mid_leaf_trace(
    b: &mut FieldR1csBuilder,
    symbols: &[ExtExpr; 1 << MID_STANDARD_FOLDS],
    challenges: &[ExtExpr; MID_STANDARD_FOLDS],
) -> ExtExpr {
    fold_normal_table_trace(b, symbols, challenges)
}

/// Select one raw mid-codeword member directly from its committed
/// fold-normal table.
///
/// Reversing normalization one dimension at a time and immediately choosing
/// the requested branch fuses the inverse transform with the 16-way mux.  At
/// reverse dimension `r`, the selected branch is
/// `u + (twiddle + q_r) * v`.  The twiddle's pair index consists of the
/// already selected higher member bits followed by the nine mid-leaf bits.
/// This uses one wide-by-base product for each of the 15 internal nodes, or
/// exactly 30 base-field rows, instead of materializing a raw leaf and then
/// selecting it.
pub fn select_fold_normal_mid_raw_member_trace(
    b: &mut FieldR1csBuilder,
    code: &ZkAffineLchCode,
    symbols: &[ExtExpr; 1 << MID_STANDARD_FOLDS],
    source_query_bits: &[LinExpr; SOURCE_QUERY_BITS],
) -> Result<ExtExpr, ZkAffineCodeError> {
    let member_bits = &source_query_bits[..MID_STANDARD_FOLDS];
    let mid_leaf_bits = &source_query_bits[MID_LEAF_QUERY_BIT_OFFSET..];
    let mut current = symbols.to_vec();

    for reverse_round in (0..MID_STANDARD_FOLDS).rev() {
        let half = 1usize << reverse_round;
        debug_assert_eq!(current.len(), 2 * half);
        let mut pair_bits =
            Vec::with_capacity(MID_STANDARD_FOLDS - reverse_round - 1 + mid_leaf_bits.len());
        pair_bits.extend_from_slice(&member_bits[reverse_round + 1..]);
        pair_bits.extend_from_slice(mid_leaf_bits);
        let layer = AFFINE_CODE_LOG_LEN - SOURCE_STANDARD_FOLDS - reverse_round - 1;
        debug_assert_eq!(pair_bits.len(), layer);
        let twiddle = affine_twiddle_from_pair_bits(code, layer, 0, 0, &pair_bits)?;
        let branch_scalar = twiddle.add(&member_bits[reverse_round]);
        current = (0..half)
            .map(|coefficient| {
                current[coefficient].add(&mul_ext_base(
                    b,
                    &current[half + coefficient],
                    &branch_scalar,
                ))
            })
            .collect();
    }

    debug_assert_eq!(current.len(), 1);
    Ok(current
        .pop()
        .expect("selected inverse network leaves one member"))
}

/// Four selected affine-LCH folds over one contiguous 16-symbol mid coset.
/// `source_query_bits[4..13]` are exactly the mid-leaf index bits `q4..q12`,
/// LSB first; `q0..q3` select a member within the mid leaf and do not enter
/// these twiddles. Challenges consume logical variables 3 through 6
/// LOW-to-HIGH.
///
/// The query bits must already have been booleanity-constrained and rebound
/// to the transcript seed. This helper allocates exactly
/// `2 * (8 + 4 + 2 + 1) = 30` multiplication rows.
pub fn mid_standard_fold4_trace(
    b: &mut FieldR1csBuilder,
    code: &ZkAffineLchCode,
    symbols: &[ExtExpr; 1 << MID_STANDARD_FOLDS],
    source_query_bits: &[LinExpr; SOURCE_QUERY_BITS],
    challenges: &[ExtExpr; MID_STANDARD_FOLDS],
) -> Result<ExtExpr, ZkAffineCodeError> {
    affine_lch_fold_contiguous_coset_from_bits_trace(
        b,
        code,
        symbols,
        SOURCE_STANDARD_FOLDS,
        &source_query_bits[MID_LEAF_QUERY_BIT_OFFSET..],
        challenges,
    )
}

#[cfg(test)]
mod tests {
    use super::super::{
        alloc_block256, alloc_blocks, alloc_blocks256, flat_of_ext, pin_eq_ext, F128,
    };
    use super::*;
    use noid_core::{Block128, Block256};
    use noid_fri_binius::zk_capsule::ZK_AUTH_CAPSULE_GEOMETRY;
    use noid_fri_binius::zk_capsule_algebra::{fold_joint_source_leaf, mid_standard_fold4};

    fn elem(index: usize, domain: u128) -> Block128 {
        Block128::from(
            domain
                .wrapping_mul(index as u128 + 1)
                .rotate_left(((11 * index + 7) % 127) as u32)
                ^ (0x9E37_79B9_7F4A_7C15u128 * (index as u128 + 3)),
        )
    }

    fn expr_array<const N: usize>(
        b: &mut FieldR1csBuilder,
        values: &[Block128; N],
    ) -> [LinExpr; N] {
        alloc_blocks(b, values)
            .try_into()
            .unwrap_or_else(|_| unreachable!("array length is statically N"))
    }

    fn ext_elem(index: usize, domain: u128) -> Block256 {
        Block256::new(elem(index, domain), elem(index + 101, domain ^ 0xC1_256))
    }

    fn ext_expr_array<const N: usize>(
        b: &mut FieldR1csBuilder,
        values: &[Block256; N],
    ) -> [ExtExpr; N] {
        alloc_blocks256(b, values)
            .try_into()
            .unwrap_or_else(|_| unreachable!("array length is statically N"))
    }

    fn alloc_source_query_bits(
        b: &mut FieldR1csBuilder,
        source_leaf_index: usize,
    ) -> [LinExpr; SOURCE_QUERY_BITS] {
        assert!(source_leaf_index < ZK_AUTH_CAPSULE_GEOMETRY.source_leaf_count);
        std::array::from_fn(|bit| {
            LinExpr::from_wire(b.alloc_bool((source_leaf_index >> bit) & 1 == 1))
        })
    }

    #[test]
    fn source_joint_fold_is_native_exact_class_fixed_and_fifty_nine_rows() {
        let code = ZkAffineLchCode::selected().unwrap();
        let joint_leaf: [Block128; JOINT_SOURCE_LEAF_SYMBOLS] =
            std::array::from_fn(|i| elem(i, 0x51_0A_7CE));
        let gamma = ext_elem(31, 0x6A_6D_6D_61);
        let challenges: [Block256; SOURCE_STANDARD_FOLDS] =
            std::array::from_fn(|i| ext_elem(40 + i, 0x50_48_41_53_45_42));
        let query_indices = [0x12A5usize, 0x0A5Ausize];
        let mut digests = Vec::new();

        for (case, source_leaf_index) in query_indices.into_iter().enumerate() {
            let expected =
                fold_joint_source_leaf(&code, &joint_leaf, gamma, source_leaf_index, &challenges)
                    .unwrap();

            let mut b = FieldR1csBuilder::new();
            let joint_e = expr_array(&mut b, &joint_leaf);
            let gamma_e = alloc_block256(&mut b, gamma);
            let query_bits = alloc_source_query_bits(&mut b, source_leaf_index);
            let query_bit_zero_wire = query_bits[0].terms[0].0 as usize;
            let challenge_e = ext_expr_array(&mut b, &challenges);
            let expected_e = alloc_block256(&mut b, expected);
            let helper_start = b.num_wires();
            let got = fold_joint_source_leaf_trace(
                &mut b,
                &code,
                &joint_e,
                &gamma_e,
                &query_bits,
                &challenge_e,
            )
            .unwrap();
            assert_eq!(
                b.num_wires() - helper_start,
                59,
                "eight wide gamma products plus seven wide affine-fold nodes"
            );
            assert_eq!(got.eval(b.values()), flat_of_ext(expected), "native parity");
            pin_eq_ext(&mut b, &got, &expected_e);

            let (r1cs, witness) = b.build();
            assert!(r1cs.satisfies(&witness), "honest source fold trace");

            if case == 0 {
                let mut tampered_product = witness.clone();
                tampered_product[helper_start + 24] += F128::ONE;
                assert!(
                    !r1cs.satisfies(&tampered_product),
                    "tampered dynamic-twiddle product survived"
                );

                let mut tampered_query = witness.clone();
                tampered_query[query_bit_zero_wire] += F128::ONE;
                assert!(
                    !r1cs.satisfies(&tampered_query),
                    "boolean query-bit toggle was not bound into the fold"
                );
            }
            digests.push(r1cs.statement_digest());
        }

        assert_eq!(
            digests[0], digests[1],
            "source query values must not change the recursive matrix"
        );
    }

    #[test]
    fn mid_fold_is_native_exact_class_fixed_and_seventy_five_rows() {
        let code = ZkAffineLchCode::selected().unwrap();
        let symbols: [Block256; 1 << MID_STANDARD_FOLDS] =
            std::array::from_fn(|i| ext_elem(80 + i, 0x4D_49_44));
        let challenges: [Block256; MID_STANDARD_FOLDS] =
            std::array::from_fn(|i| ext_elem(120 + i, 0x46_4F_4C_44));
        let source_query_indices = [0x12A5usize, 0x0A5Ausize];
        let mut digests = Vec::new();

        for (case, source_leaf_index) in source_query_indices.into_iter().enumerate() {
            let mid_leaf_index = source_leaf_index >> MID_LEAF_QUERY_BIT_OFFSET;
            let expected =
                mid_standard_fold4(&code, &symbols, mid_leaf_index, &challenges).unwrap();

            let mut b = FieldR1csBuilder::new();
            let symbol_e = ext_expr_array(&mut b, &symbols);
            let query_bits = alloc_source_query_bits(&mut b, source_leaf_index);
            let query_bit_four_wire = query_bits[MID_LEAF_QUERY_BIT_OFFSET].terms[0].0 as usize;
            let challenge_e = ext_expr_array(&mut b, &challenges);
            let expected_e = alloc_block256(&mut b, expected);
            let helper_start = b.num_wires();
            let got = mid_standard_fold4_trace(&mut b, &code, &symbol_e, &query_bits, &challenge_e)
                .unwrap();
            assert_eq!(
                b.num_wires() - helper_start,
                75,
                "four wide dynamic-index affine layers must cost 5 * (8 + 4 + 2 + 1)"
            );
            assert_eq!(got.eval(b.values()), flat_of_ext(expected), "native parity");
            pin_eq_ext(&mut b, &got, &expected_e);

            let (r1cs, witness) = b.build();
            assert!(r1cs.satisfies(&witness), "honest mid fold trace");

            if case == 0 {
                let mut tampered_product = witness.clone();
                tampered_product[helper_start + 74] += F128::ONE;
                assert!(
                    !r1cs.satisfies(&tampered_product),
                    "tampered terminal affine-fold product survived"
                );

                let mut tampered_query = witness.clone();
                tampered_query[query_bit_four_wire] += F128::ONE;
                assert!(
                    !r1cs.satisfies(&tampered_query),
                    "mid-leaf query-bit toggle was not bound into the fold"
                );
            }
            digests.push(r1cs.statement_digest());
        }

        assert_eq!(
            digests[0], digests[1],
            "mid query values must not change the recursive matrix"
        );
    }
}
