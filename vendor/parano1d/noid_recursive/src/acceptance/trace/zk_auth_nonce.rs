// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical `u64` range binding for the selected authorization grind nonce.
//!
//! The serialized proof carries an eight-byte little-endian nonce, while the
//! Main duplex absorb column stores one F128 cell.  Native construction from a
//! Rust `u64` is not a recursive constraint: without this gate a malicious
//! witness could put non-zero tower bits 64..127 in the committed cell and use
//! a larger nonce language than the canonical wire format.
//!
//! This trace allocates the low 64 tower bits as booleans and pins their exact
//! recomposition to the transcript cell.  Equality in F128 simultaneously
//! forces every upper tower bit to zero.

use super::fri_pcs::expr_tower_value;
use super::{flat_const, pin_eq, FieldR1csBuilder, LinExpr};

pub const ZK_AUTH_NONCE_BITS: usize = u64::BITS as usize;
pub const ZK_AUTH_NONCE_BOOLEAN_ROWS: usize = ZK_AUTH_NONCE_BITS;
pub const ZK_AUTH_NONCE_RECOMPOSITION_ROWS: usize = 1;
pub const ZK_AUTH_NONCE_TRACE_ROWS: usize =
    ZK_AUTH_NONCE_BOOLEAN_ROWS + ZK_AUTH_NONCE_RECOMPOSITION_ROWS;

const _: () = assert!(ZK_AUTH_NONCE_BITS == 64);
const _: () = assert!(ZK_AUTH_NONCE_TRACE_ROWS == 65);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkAuthNonceTraceError {
    /// The proof-carried nonce must enter through the exact Main absorb cell.
    DynamicInputIsConstant,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkAuthNonceTraceOutput {
    /// Exact low-to-high tower-bit decomposition of the canonical nonce.
    pub bits_lsb: [LinExpr; ZK_AUTH_NONCE_BITS],
}

/// Bind one transcript-owned field expression to the canonical `u64` range.
pub fn verify_zk_auth_nonce_trace(
    b: &mut FieldR1csBuilder,
    nonce: &LinExpr,
) -> Result<ZkAuthNonceTraceOutput, ZkAuthNonceTraceError> {
    if nonce.is_const() {
        return Err(ZkAuthNonceTraceError::DynamicInputIsConstant);
    }

    let trace_start = b.num_wires();
    let tower = expr_tower_value(b, nonce).0;
    let bits_lsb =
        std::array::from_fn(|bit| LinExpr::from_wire(b.alloc_bool(((tower >> bit) & 1) == 1)));
    let recomposed = bits_lsb
        .iter()
        .enumerate()
        .fold(LinExpr::zero(), |sum, (bit, expression)| {
            sum.add(&expression.scale(flat_const(1u128 << bit)))
        });
    pin_eq(b, &recomposed, nonce);

    debug_assert_eq!(b.num_wires() - trace_start, ZK_AUTH_NONCE_TRACE_ROWS);
    Ok(ZkAuthNonceTraceOutput { bits_lsb })
}

#[cfg(test)]
mod tests {
    use noid_core::Block128;
    use noid_ivc_core::field::F128;
    use noid_ivc_core::field_r1cs::FieldR1cs;

    use super::super::{alloc_block, flat_of};
    use super::*;

    fn input_wire(expression: &LinExpr) -> usize {
        assert_eq!(expression.terms.len(), 1);
        assert_eq!(expression.terms[0].1, F128::ONE);
        assert_eq!(expression.constant, F128::ZERO);
        expression.terms[0].0 as usize
    }

    struct BuiltNonce {
        r1cs: FieldR1cs,
        witness: Vec<F128>,
        trace_rows: usize,
        nonce_wire: usize,
        bit_wires: [usize; ZK_AUTH_NONCE_BITS],
    }

    fn build(value: Block128) -> BuiltNonce {
        let mut b = FieldR1csBuilder::new();
        let nonce = alloc_block(&mut b, value);
        let nonce_wire = input_wire(&nonce);
        let before = b.num_wires();
        let output = verify_zk_auth_nonce_trace(&mut b, &nonce).expect("dynamic nonce");
        let trace_rows = b.num_wires() - before;
        let bit_wires = std::array::from_fn(|bit| input_wire(&output.bits_lsb[bit]));
        let (r1cs, witness) = b.build();
        BuiltNonce {
            r1cs,
            witness,
            trace_rows,
            nonce_wire,
            bit_wires,
        }
    }

    #[test]
    fn canonical_u64_boundaries_accept_and_upper_tower_bits_reject() {
        for value in [0u64, 1, u64::MAX, 0xA55A_0123_4567_89AB] {
            let built = build(Block128::from(value as u128));
            assert_eq!(built.trace_rows, ZK_AUTH_NONCE_TRACE_ROWS);
            assert!(built.r1cs.satisfies(&built.witness));
        }

        for bit in ZK_AUTH_NONCE_BITS..u128::BITS as usize {
            let built = build(Block128::from(1u128 << bit));
            assert!(
                !built.r1cs.satisfies(&built.witness),
                "accepted non-canonical nonce tower bit {bit}"
            );
        }
    }

    #[test]
    fn transcript_cell_and_every_low_bit_are_live_constraints() {
        let built = build(Block128::from(0xD15C_A11E_CAFE_BABEu128));
        assert!(built.r1cs.satisfies(&built.witness));

        let mut changed_nonce = built.witness.clone();
        changed_nonce[built.nonce_wire] += flat_of(Block128::from(1u128 << 96));
        assert!(!built.r1cs.satisfies(&changed_nonce));

        for bit in 0..ZK_AUTH_NONCE_BITS {
            let mut changed_bit = built.witness.clone();
            changed_bit[built.bit_wires[bit]] += F128::ONE;
            assert!(
                !built.r1cs.satisfies(&changed_bit),
                "nonce bit {bit} escaped recomposition"
            );
        }
    }

    #[test]
    fn nonce_trace_has_exact_content_invariant_shape() {
        let left = build(Block128::from(7u128));
        let right = build(Block128::from(u64::MAX as u128));
        assert_eq!(ZK_AUTH_NONCE_TRACE_ROWS, 65);
        assert_eq!(left.trace_rows, ZK_AUTH_NONCE_TRACE_ROWS);
        assert_eq!(right.trace_rows, ZK_AUTH_NONCE_TRACE_ROWS);
        assert_eq!(
            left.r1cs.structural_statement_digest(),
            right.r1cs.structural_statement_digest()
        );
    }

    #[test]
    fn constant_nonce_preflight_is_atomic() {
        let mut b = FieldR1csBuilder::new();
        let nonce = LinExpr::constant(flat_of(Block128::from(9u128)));
        let before = b.num_wires();
        assert_eq!(
            verify_zk_auth_nonce_trace(&mut b, &nonce),
            Err(ZkAuthNonceTraceError::DynamicInputIsConstant)
        );
        assert_eq!(b.num_wires(), before);
    }
}
