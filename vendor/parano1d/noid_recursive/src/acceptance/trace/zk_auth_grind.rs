// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Production check for the authorization capsule's pre-query
//! transcript grind.
//!
//! The input is the exact post-nonce transcript squeeze alias, already
//! produced and bound by the Main duplex region.  The low 16 tower
//! coefficients are fixed to zero, while the remaining 112 coefficients are
//! allocated as Boolean bits and exactly recomposed to the alias.  The
//! 16-bit mainnet window is a protocol constant here and never inherits the
//! active capsule's debug/release `cfg` split.
//!
//! Exact incremental row ledger after the caller-owned `grind` expression:
//!
//! ```text
//! 112 free high-bit Boolean rows   112
//! exact 128-bit recomposition pin    1
//!                                  ---
//! total                            113
//! ```
//!
//! The absorbed nonce is deliberately not an input to this arithmetic unit.
//! A canonical `u64` nonce belongs at the proof/wire boundary: if the Main
//! transcript consumes an exact alias of a typed `u64` field, another range
//! check here would duplicate it.  If a future adapter instead exposes a
//! free field-valued nonce, that adapter must range-bind its upper 64 tower
//! bits to zero to preserve the specified wire language.  The range does not
//! alter the `2^-16` success probability of an individual grind attempt, but
//! it does define which nonce encodings the protocol accepts.

use super::fri_pcs::expr_tower_value;
use super::{flat_const, pin_eq, FieldR1csBuilder, LinExpr};

/// Mainnet authorization grind window, in low tower-basis bits.
pub const ZK_AUTH_GRIND_BITS: usize = 16;
pub const ZK_AUTH_GRIND_TOWER_BITS: usize = 128;
pub const ZK_AUTH_GRIND_HIGH_BITS: usize = ZK_AUTH_GRIND_TOWER_BITS - ZK_AUTH_GRIND_BITS;
pub const ZK_AUTH_GRIND_BOOLEAN_ROWS: usize = ZK_AUTH_GRIND_HIGH_BITS;
pub const ZK_AUTH_GRIND_RECOMPOSITION_ROWS: usize = 1;
/// Exact incremental rows after the transcript-owned `grind` alias exists.
pub const ZK_AUTH_GRIND_TRACE_ROWS: usize =
    ZK_AUTH_GRIND_BOOLEAN_ROWS + ZK_AUTH_GRIND_RECOMPOSITION_ROWS;

const _: () = assert!(ZK_AUTH_GRIND_BITS == 16);
const _: () = assert!(ZK_AUTH_GRIND_TOWER_BITS == u128::BITS as usize);
const _: () = assert!(ZK_AUTH_GRIND_HIGH_BITS == 112);
const _: () = assert!(ZK_AUTH_GRIND_TRACE_ROWS == 113);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkAuthGrindTraceError {
    /// The transcript squeeze was accidentally embedded in the recursive
    /// matrix instead of entering through its allocated duplex-cell alias.
    DynamicInputIsConstant,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkAuthGrindTraceOutput {
    /// The forced-zero low tower coefficients, exposed as constant aliases.
    pub low_bits_lsb: [LinExpr; ZK_AUTH_GRIND_BITS],
    /// Boolean tower coefficients 16 through 127, LSB first within this
    /// suffix. They are the only free coefficients needed by recomposition.
    pub high_bits_lsb: [LinExpr; ZK_AUTH_GRIND_HIGH_BITS],
}

/// Enforce the fixed 16-low-tower-bit authorization grind predicate.
///
/// The full dynamic-input preflight runs before any rows are appended.  An
/// invalid nonzero low window is represented by an unsatisfied fixed-shape
/// trace, not by a witness-dependent construction error.
pub fn verify_zk_auth_grind_trace(
    b: &mut FieldR1csBuilder,
    grind: &LinExpr,
) -> Result<ZkAuthGrindTraceOutput, ZkAuthGrindTraceError> {
    if grind.is_const() {
        return Err(ZkAuthGrindTraceError::DynamicInputIsConstant);
    }

    let trace_start = b.num_wires();
    let tower = expr_tower_value(b, grind).0;
    let low_bits_lsb = std::array::from_fn(|_| LinExpr::zero());
    let high_bits_lsb: [LinExpr; ZK_AUTH_GRIND_HIGH_BITS] = std::array::from_fn(|index| {
        let bit = ZK_AUTH_GRIND_BITS + index;
        LinExpr::from_wire(b.alloc_bool(((tower >> bit) & 1) == 1))
    });
    let recomposed =
        high_bits_lsb
            .iter()
            .enumerate()
            .fold(LinExpr::zero(), |sum, (index, expression)| {
                sum.add(&expression.scale(flat_const(1u128 << (ZK_AUTH_GRIND_BITS + index))))
            });
    pin_eq(b, &recomposed, grind);

    debug_assert_eq!(b.num_wires() - trace_start, ZK_AUTH_GRIND_TRACE_ROWS);
    Ok(ZkAuthGrindTraceOutput {
        low_bits_lsb,
        high_bits_lsb,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::trace::{alloc_block, flat_of, F128};
    use noid_core::{Block128, TowerField};
    use noid_ivc_core::field_r1cs::FieldR1cs;

    fn native_accepts(value: Block128) -> bool {
        value.0 & ((1u128 << ZK_AUTH_GRIND_BITS) - 1) == 0
    }

    fn input_wire(expression: &LinExpr) -> usize {
        assert_eq!(expression.terms.len(), 1);
        assert_eq!(expression.terms[0].1, F128::ONE);
        assert_eq!(expression.constant, F128::ZERO);
        expression.terms[0].0 as usize
    }

    struct BuiltGrind {
        r1cs: FieldR1cs,
        witness: Vec<F128>,
        trace_rows: usize,
        grind_wire: usize,
        high_bit_wires: [usize; ZK_AUTH_GRIND_HIGH_BITS],
    }

    fn build(value: Block128) -> BuiltGrind {
        let mut b = FieldR1csBuilder::new();
        let grind = alloc_block(&mut b, value);
        let grind_wire = input_wire(&grind);
        let before = b.num_wires();
        let output = verify_zk_auth_grind_trace(&mut b, &grind).expect("dynamic grind alias");
        let trace_rows = b.num_wires() - before;
        assert!(output.low_bits_lsb.iter().all(|bit| bit.is_const()));
        let high_bit_wires = std::array::from_fn(|bit| input_wire(&output.high_bits_lsb[bit]));
        let (r1cs, witness) = b.build();
        BuiltGrind {
            r1cs,
            witness,
            trace_rows,
            grind_wire,
            high_bit_wires,
        }
    }

    #[test]
    fn fixed_mainnet_grind_matches_native_low16_predicate() {
        assert_eq!(ZK_AUTH_GRIND_BITS, 16);
        let cases = [
            Block128::ZERO,
            Block128::from(1u128 << 16),
            Block128::from(0xDEAD_BEEF_CAFE_BABEu128 << 16),
            Block128::from(1u128),
            Block128::from(1u128 << 15),
            Block128::from((0x1234_5678_9ABC_DEF0u128 << 16) | 0xA55A),
        ];

        for value in cases {
            let built = build(value);
            assert_eq!(built.trace_rows, ZK_AUTH_GRIND_TRACE_ROWS);
            assert_eq!(
                built.r1cs.satisfies(&built.witness),
                native_accepts(value),
                "recursive/native grind parity for {:032x}",
                value.0
            );
        }
    }

    #[test]
    fn every_high_tower_bit_is_accepted_when_low16_are_zero() {
        for bit in ZK_AUTH_GRIND_BITS..ZK_AUTH_GRIND_TOWER_BITS {
            let value = Block128::from(1u128 << bit);
            assert!(native_accepts(value));
            let built = build(value);
            assert!(
                built.r1cs.satisfies(&built.witness),
                "rejected allowed high tower bit {bit}"
            );
        }
    }

    #[test]
    fn low_tower_bit_and_decomposition_tampering_reject() {
        let built = build(Block128::from(
            0xD15C_A11E_CAFE_BABE_0123_4567_89ABu128 << 16,
        ));
        assert!(built.r1cs.satisfies(&built.witness));

        for bit in 0..ZK_AUTH_GRIND_BITS {
            let mut tampered_squeeze = built.witness.clone();
            tampered_squeeze[built.grind_wire] += flat_of(Block128::from(1u128 << bit));
            assert!(
                !built.r1cs.satisfies(&tampered_squeeze),
                "transcript grind low bit {bit} escaped recomposition"
            );
        }

        for bit in 0..ZK_AUTH_GRIND_HIGH_BITS {
            let mut tampered_bit = built.witness.clone();
            tampered_bit[built.high_bit_wires[bit]] += F128::ONE;
            assert!(
                !built.r1cs.satisfies(&tampered_bit),
                "decomposed grind high bit {bit} escaped recomposition"
            );
        }
    }

    #[test]
    fn grind_trace_has_exact_row_ledger_and_content_invariant_shape() {
        let left = build(Block128::from(0x1234_5678_9ABC_DEF0u128 << 16));
        let right = build(Block128::from(
            0xFEDC_BA98_7654_3210_0123_4567_89ABu128 << 16,
        ));
        assert!(left.r1cs.satisfies(&left.witness));
        assert!(right.r1cs.satisfies(&right.witness));

        assert_eq!(ZK_AUTH_GRIND_HIGH_BITS, 112);
        assert_eq!(ZK_AUTH_GRIND_BOOLEAN_ROWS, 112);
        assert_eq!(ZK_AUTH_GRIND_RECOMPOSITION_ROWS, 1);
        assert_eq!(ZK_AUTH_GRIND_TRACE_ROWS, 113);
        assert_eq!(left.trace_rows, ZK_AUTH_GRIND_TRACE_ROWS);
        assert_eq!(right.trace_rows, ZK_AUTH_GRIND_TRACE_ROWS);
        assert_eq!(left.r1cs.useful_rows, 1 + 1 + ZK_AUTH_GRIND_TRACE_ROWS);
        assert_eq!(right.r1cs.useful_rows, 1 + 1 + ZK_AUTH_GRIND_TRACE_ROWS);
        assert_eq!(
            left.r1cs.structural_statement_digest(),
            right.r1cs.structural_statement_digest(),
            "grind trace matrix depends on squeeze contents"
        );
    }

    #[test]
    fn constant_grind_preflight_is_atomic() {
        let mut b = FieldR1csBuilder::new();
        let constant = LinExpr::constant(flat_of(Block128::from(1u128 << 16)));
        let before = b.num_wires();
        assert!(matches!(
            verify_zk_auth_grind_trace(&mut b, &constant),
            Err(ZkAuthGrindTraceError::DynamicInputIsConstant)
        ));
        assert_eq!(b.num_wires(), before);
    }
}
