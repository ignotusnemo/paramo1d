// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Production recursive selector for the affine capsule tail.
//!
//! After seven LOW-to-HIGH folds the selected affine LCH code commits a
//! 16-coefficient tail as a 512-cell codeword.  Evaluating one transcript-
//! selected codeword cell does not require a 512-way mux: the four surviving
//! novel-basis coordinates are affine in the nine query bits, and a
//! coefficient-form Horner tree costs exactly `8 + 4 + 2 + 1 = 15` field
//! multiplications.
//!
//! The selected capsule region calls this fixed and independently tested trace
//! primitive for every Phase-B query.

use std::sync::OnceLock;

use noid_core::{Block128, TowerField};
use noid_fri_binius::zk_affine_code::ZkAffineLchCode;

use super::{const_block, flat_of, mul_ext_base, ExtExpr, FieldR1csBuilder, LinExpr};

pub const ZK_AFFINE_TAIL_FOLDS_DONE: usize = 7;
pub const ZK_AFFINE_TAIL_LOG: usize = 4;
pub const ZK_AFFINE_TAIL_LEN: usize = 1 << ZK_AFFINE_TAIL_LOG;
pub const ZK_AFFINE_TAIL_QUERY_BITS: usize = 9;
pub const ZK_AFFINE_TAIL_CODE_LEN: usize = 1 << ZK_AFFINE_TAIL_QUERY_BITS;
pub const ZK_AFFINE_TAIL_SELECTOR_ROWS: usize = 2 * (ZK_AFFINE_TAIL_LEN - 1);

const _: () = assert!(ZK_AFFINE_TAIL_SELECTOR_ROWS == 30);
const _: () = assert!(
    ZK_AFFINE_TAIL_CODE_LEN
        == 1 << (noid_fri_binius::zk_affine_code::AFFINE_CODE_LOG_LEN - ZK_AFFINE_TAIL_FOLDS_DONE)
);

#[derive(Clone, Copy)]
struct AffineTailCoordinates {
    bases: [Block128; ZK_AFFINE_TAIL_LOG],
    bit_deltas: [[Block128; ZK_AFFINE_TAIL_QUERY_BITS]; ZK_AFFINE_TAIL_LOG],
}

fn selected_tail_coordinates() -> &'static AffineTailCoordinates {
    static COORDINATES: OnceLock<AffineTailCoordinates> = OnceLock::new();
    COORDINATES.get_or_init(|| {
        let code = ZkAffineLchCode::selected().expect("selected affine LCH code");
        let coordinate_codewords: [Vec<Block128>; ZK_AFFINE_TAIL_LOG] =
            std::array::from_fn(|coordinate| {
                let mut coefficient = [Block128::ZERO; ZK_AFFINE_TAIL_LEN];
                coefficient[1 << coordinate] = Block128::ONE;
                code.encode_after_low_folds(&coefficient, ZK_AFFINE_TAIL_FOLDS_DONE)
                    .expect("selected affine tail basis codeword")
            });
        let bases = std::array::from_fn(|coordinate| coordinate_codewords[coordinate][0]);
        let bit_deltas = std::array::from_fn(|coordinate| {
            std::array::from_fn(|query_bit| {
                coordinate_codewords[coordinate][1 << query_bit] + bases[coordinate]
            })
        });
        AffineTailCoordinates { bases, bit_deltas }
    })
}

/// Select `Code(tail16)[query]` from nine LSB-first transcript query bits.
///
/// The caller supplies already-bound query-bit expressions. Booleanity and
/// seed recomposition belong to the query-carrier layer; duplicating them here
/// would both waste rows and obscure the exact 15-row selector contract.
pub fn select_affine_tail16_trace(
    b: &mut FieldR1csBuilder,
    tail: &[ExtExpr; ZK_AFFINE_TAIL_LEN],
    query_bits: &[LinExpr; ZK_AFFINE_TAIL_QUERY_BITS],
) -> ExtExpr {
    let coordinates = selected_tail_coordinates();
    let coordinate_exprs: [LinExpr; ZK_AFFINE_TAIL_LOG] = std::array::from_fn(|coordinate| {
        let mut value = const_block(coordinates.bases[coordinate]);
        for (query_bit, bit) in query_bits.iter().enumerate() {
            value = value.add(&bit.scale(flat_of(coordinates.bit_deltas[coordinate][query_bit])));
        }
        value
    });

    let mut coefficients = tail.to_vec();
    for coordinate in &coordinate_exprs {
        coefficients = coefficients
            .chunks_exact(2)
            .map(|pair| pair[0].add(&mul_ext_base(b, &pair[1], coordinate)))
            .collect();
    }
    debug_assert_eq!(coefficients.len(), 1);
    coefficients.pop().expect("affine tail Horner terminal")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::trace::{
        alloc_block, alloc_block256, flat_of_ext, pin_eq_ext, F128, F256,
    };
    use noid_core::Block256;

    fn tail(seed: u128) -> [Block256; ZK_AFFINE_TAIL_LEN] {
        std::array::from_fn(|index| {
            Block256::new(
                Block128::from(
                    seed.rotate_left((index * 7 % 127) as u32)
                        ^ (index as u128 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15),
                ),
                Block128::from(
                    seed.rotate_right((index * 11 % 127) as u32)
                        ^ (index as u128 + 5).wrapping_mul(0xD1B5_4A32_D192_ED03),
                ),
            )
        })
    }

    fn query_bits(b: &mut FieldR1csBuilder, query: usize) -> [LinExpr; ZK_AFFINE_TAIL_QUERY_BITS] {
        std::array::from_fn(|bit| alloc_block(b, Block128::from(((query >> bit) & 1) as u128)))
    }

    #[test]
    fn affine_tail_factorization_is_exhaustive_over_all_positions_and_coefficients() {
        let code = ZkAffineLchCode::selected().expect("selected affine code");
        let coordinates = selected_tail_coordinates();
        let basis_codewords: Vec<Vec<Block128>> = (0..ZK_AFFINE_TAIL_LEN)
            .map(|coefficient| {
                let mut tail = [Block128::ZERO; ZK_AFFINE_TAIL_LEN];
                tail[coefficient] = Block128::ONE;
                code.encode_after_low_folds(&tail, ZK_AFFINE_TAIL_FOLDS_DONE)
                    .expect("basis tail encode")
            })
            .collect();

        for query in 0..ZK_AFFINE_TAIL_CODE_LEN {
            let coordinate_values: [Block128; ZK_AFFINE_TAIL_LOG] =
                std::array::from_fn(|coordinate| {
                    let mut value = coordinates.bases[coordinate];
                    for query_bit in 0..ZK_AFFINE_TAIL_QUERY_BITS {
                        if (query >> query_bit) & 1 == 1 {
                            value += coordinates.bit_deltas[coordinate][query_bit];
                        }
                    }
                    value
                });
            for (coefficient, codeword) in basis_codewords.iter().enumerate() {
                let mut factored = Block128::ONE;
                for (coordinate, value) in coordinate_values.iter().enumerate() {
                    if (coefficient >> coordinate) & 1 == 1 {
                        factored *= *value;
                    }
                }
                assert_eq!(
                    factored, codeword[query],
                    "tail basis factorization at query {query}, coefficient {coefficient}"
                );
            }
        }
    }

    #[test]
    fn affine_tail_trace_matches_all_512_positions_at_exactly_30_rows_each() {
        let native_tail = tail(0xA771_1E5E);
        let codeword = ZkAffineLchCode::selected()
            .expect("selected affine code")
            .encode_extension_after_low_folds(&native_tail, ZK_AFFINE_TAIL_FOLDS_DONE)
            .expect("tail encode");
        let mut b = FieldR1csBuilder::new();
        let tail_w: [ExtExpr; ZK_AFFINE_TAIL_LEN] =
            std::array::from_fn(|index| alloc_block256(&mut b, native_tail[index]));

        for query in 0..ZK_AFFINE_TAIL_CODE_LEN {
            let bits = query_bits(&mut b, query);
            let before = b.num_wires();
            let selected = select_affine_tail16_trace(&mut b, &tail_w, &bits);
            assert_eq!(
                b.num_wires() - before,
                ZK_AFFINE_TAIL_SELECTOR_ROWS,
                "query {query} row count"
            );
            assert_eq!(selected.eval(b.values()), flat_of_ext(codeword[query]));
        }

        let (r1cs, witness) = b.build();
        assert!(r1cs.satisfies(&witness));
    }

    fn relation(seed: u128, query: usize) -> ([u8; 32], usize, F256) {
        let native_tail = tail(seed);
        let mut b = FieldR1csBuilder::new();
        let tail_w: [ExtExpr; ZK_AFFINE_TAIL_LEN] =
            std::array::from_fn(|index| alloc_block256(&mut b, native_tail[index]));
        let bits = query_bits(&mut b, query);
        let before = b.num_wires();
        let selected = select_affine_tail16_trace(&mut b, &tail_w, &bits);
        assert_eq!(b.num_wires() - before, ZK_AFFINE_TAIL_SELECTOR_ROWS);
        let value = selected.eval(b.values());
        let (r1cs, witness) = b.build();
        assert!(r1cs.satisfies(&witness));
        (r1cs.statement_digest(), r1cs.useful_rows, value)
    }

    #[test]
    fn affine_tail_trace_matrix_is_content_and_query_invariant() {
        let cases = [
            relation(0x11, 0),
            relation(0x22, 1),
            relation(0x33, 0x12d),
            relation(0x44, ZK_AFFINE_TAIL_CODE_LEN - 1),
        ];
        for case in &cases[1..] {
            assert_eq!(case.0, cases[0].0, "tail selector matrix drift");
            assert_eq!(case.1, cases[0].1, "tail selector row-count drift");
        }
        assert!(cases.windows(2).any(|pair| pair[0].2 != pair[1].2));
    }

    #[test]
    fn affine_tail_product_and_selected_value_tampering_reject() {
        let native_tail = tail(0xBAD5_E1EC_70A5_Eu128);
        let query = 0x16busize;
        let expected = ZkAffineLchCode::selected()
            .expect("selected affine code")
            .encode_extension_after_low_folds(&native_tail, ZK_AFFINE_TAIL_FOLDS_DONE)
            .expect("tail encode")[query];

        let mut b = FieldR1csBuilder::new();
        let tail_w: [ExtExpr; ZK_AFFINE_TAIL_LEN] =
            std::array::from_fn(|index| alloc_block256(&mut b, native_tail[index]));
        let bits = query_bits(&mut b, query);
        let helper_start = b.num_wires();
        let selected = select_affine_tail16_trace(&mut b, &tail_w, &bits);
        assert_eq!(b.num_wires() - helper_start, ZK_AFFINE_TAIL_SELECTOR_ROWS);
        let expected_w = alloc_block256(&mut b, expected);
        let expected_wire = expected_w.lo.terms[0].0 as usize;
        pin_eq_ext(&mut b, &selected, &expected_w);

        let (r1cs, witness) = b.build();
        assert!(r1cs.satisfies(&witness));

        let mut bad_product = witness.clone();
        bad_product[helper_start] += F128::ONE;
        assert!(
            !r1cs.satisfies(&bad_product),
            "tampered affine-tail Horner product survived"
        );

        let mut bad_selected = witness;
        bad_selected[expected_wire] += F128::ONE;
        assert!(
            !r1cs.satisfies(&bad_selected),
            "tampered selected affine-tail value survived"
        );
    }
}
