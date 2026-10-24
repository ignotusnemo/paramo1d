// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Exact 144-block transaction-epoch boundary arithmetic.
//!
//! The trace proves `height = 144 * quotient + remainder`, `remainder < 144`,
//! and derives `boundary = (remainder == 0)`. Only quotient and remainder are
//! witness values. The boundary selector is an expression over constrained
//! remainder bits and is never supplied by the prover as an independent bit.

use noid_chain::consensus::params::TX_EPOCH_BLOCKS;
use noid_chain::consensus::{checked_tx_epoch_height_decomposition, TxEpochHeightDecomposition};
use noid_core::Block128;

use super::{
    alloc_block, const_block, flat_const, integer_add_no_overflow, mul, pin_eq, pin_lt_strict,
    range_check_bits, FieldR1csBuilder, LinExpr, Wire, F128,
};

const HEIGHT_BITS: usize = 64;
const QUOTIENT_BITS: usize = 57;
const REMAINDER_BITS: usize = 8;
const _: () = assert!(TX_EPOCH_BLOCKS == 144);

/// Constrained transaction-epoch decomposition.
///
/// `boundary` is derived, not allocated. The quotient and remainder expressions
/// are exposed for diagnostics and native/trace parity tests; consumers should
/// use `boundary` as the digest-selection bit in the direct accumulator cut.
pub struct TxEpochBoundaryTrace {
    pub quotient: LinExpr,
    pub remainder: LinExpr,
    pub boundary: LinExpr,
}

/// Prove the exact transaction-epoch decomposition of a 64-bit height.
///
/// The honest quotient/remainder witness is obtained from the checked native
/// specification. Circuit constraints, rather than that native calculation,
/// make altered quotient/remainder witnesses unsatisfiable.
pub fn constrain_tx_epoch_boundary(
    b: &mut FieldR1csBuilder,
    height: &LinExpr,
) -> TxEpochBoundaryTrace {
    use noid_core::hardware::flat_to_tower_u128;

    let flat = height.eval(b.values());
    let tower = flat_to_tower_u128((flat.lo as u128) | ((flat.hi as u128) << 64));
    let native_height = u64::try_from(tower).expect("transaction-epoch height fits u64");
    let decomposition = checked_tx_epoch_height_decomposition(native_height)
        .expect("every u64 height has a checked transaction-epoch decomposition");
    constrain_tx_epoch_boundary_with_decomposition(b, height, decomposition)
}

fn shifted_integer_from_bits(bits: &[Wire], shift: usize) -> LinExpr {
    assert!(bits.len() + shift <= HEIGHT_BITS);
    bits.iter()
        .enumerate()
        .fold(LinExpr::zero(), |sum, (index, bit)| {
            sum.add(&LinExpr::from_wire(*bit).scale(flat_const(1u128 << (index + shift))))
        })
}

fn constrain_tx_epoch_boundary_with_decomposition(
    b: &mut FieldR1csBuilder,
    height: &LinExpr,
    decomposition: TxEpochHeightDecomposition,
) -> TxEpochBoundaryTrace {
    let quotient = alloc_block(b, Block128::from(decomposition.quotient as u128));
    let quotient_bits = range_check_bits(b, &quotient, QUOTIENT_BITS);
    let remainder = alloc_block(b, Block128::from(decomposition.remainder as u128));
    let remainder_bits = range_check_bits(b, &remainder, REMAINDER_BITS);

    let epoch = const_block(Block128::from(TX_EPOCH_BLOCKS as u128));
    let epoch_bits = range_check_bits(b, &epoch, REMAINDER_BITS);
    pin_lt_strict(b, &remainder_bits, &epoch_bits);

    // 144*q = (q << 7) + (q << 4), with integer carries and no u64 overflow.
    let q_times_128 = shifted_integer_from_bits(&quotient_bits, 7);
    let q_times_16 = shifted_integer_from_bits(&quotient_bits, 4);
    let q_times_144 = integer_add_no_overflow(b, &q_times_128, &q_times_16, HEIGHT_BITS);
    let recomposed = integer_add_no_overflow(b, &q_times_144, &remainder, HEIGHT_BITS);
    pin_eq(b, height, &recomposed);

    // For boolean remainder bits, this product is one exactly for r=0.
    let boundary = remainder_bits
        .iter()
        .fold(LinExpr::constant(F128::ONE), |is_zero, bit| {
            mul(b, &is_zero, &LinExpr::from_wire(*bit).add_const(F128::ONE))
        });

    TxEpochBoundaryTrace {
        quotient,
        remainder,
        boundary,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::trace::{pin_eq, test_support::tower_value};

    fn satisfies(
        height: u64,
        decomposition: TxEpochHeightDecomposition,
        claimed_boundary: bool,
    ) -> bool {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut b = FieldR1csBuilder::new();
            let height = alloc_block(&mut b, Block128::from(height as u128));
            let trace =
                constrain_tx_epoch_boundary_with_decomposition(&mut b, &height, decomposition);
            let expected = const_block(Block128::from(u128::from(claimed_boundary)));
            pin_eq(&mut b, &trace.boundary, &expected);
            let (r1cs, witness) = b.build();
            r1cs.satisfies(&witness)
        }))
        .unwrap_or(false)
    }

    #[test]
    fn exact_boundary_trace_matches_native_cases() {
        for (height, expected_boundary) in [
            (0, true),
            (1, false),
            (143, false),
            (144, true),
            (145, false),
            (287, false),
            (288, true),
            (289, false),
        ] {
            let decomposition = checked_tx_epoch_height_decomposition(height).unwrap();
            assert!(
                satisfies(height, decomposition, expected_boundary),
                "honest height {height} was unsatisfiable"
            );

            let mut b = FieldR1csBuilder::new();
            let height_w = alloc_block(&mut b, Block128::from(height as u128));
            let trace = constrain_tx_epoch_boundary(&mut b, &height_w);
            assert_eq!(
                tower_value(&b, &trace.quotient),
                Block128::from(decomposition.quotient as u128)
            );
            assert_eq!(
                tower_value(&b, &trace.remainder),
                Block128::from(decomposition.remainder as u128)
            );
            assert_eq!(
                tower_value(&b, &trace.boundary),
                Block128::from(u128::from(expected_boundary))
            );
            let (r1cs, witness) = b.build();
            assert!(r1cs.satisfies(&witness));
        }
    }

    #[test]
    fn quotient_remainder_boundary_and_height_mutations_are_unsatisfiable() {
        assert!(satisfies(
            144,
            TxEpochHeightDecomposition {
                quotient: 1,
                remainder: 0,
            },
            true,
        ));

        // q mutation: 0*144+0 != 144.
        assert!(!satisfies(
            144,
            TxEpochHeightDecomposition {
                quotient: 0,
                remainder: 0,
            },
            true,
        ));
        // r mutation: 1*144+2 != 145.
        assert!(!satisfies(
            145,
            TxEpochHeightDecomposition {
                quotient: 1,
                remainder: 2,
            },
            false,
        ));
        // Non-canonical alternative decomposition 144 = 0*144 + 144 is
        // rejected by the strict remainder bound.
        assert!(!satisfies(
            144,
            TxEpochHeightDecomposition {
                quotient: 0,
                remainder: 144,
            },
            false,
        ));
        // Boundary mutation: r=0 derives one, so claiming zero is impossible.
        assert!(!satisfies(
            144,
            TxEpochHeightDecomposition {
                quotient: 1,
                remainder: 0,
            },
            false,
        ));
        // Height mutation against the honest decomposition for 144.
        assert!(!satisfies(
            145,
            TxEpochHeightDecomposition {
                quotient: 1,
                remainder: 0,
            },
            true,
        ));
    }
}
