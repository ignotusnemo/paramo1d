// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Exact in-circuit stateless development-allocation schedule.

use noid_chain::consensus::development_allocation::{
    development_allocation, DEVELOPMENT_ALLOCATION_END_HEIGHT, TARGET_BLOCKS_PER_DAY,
};
use noid_core::Block128;

use super::exact_state::{StateDepthTrace, MAX_EXACT_STATE_DEPTH, MIN_EXACT_STATE_DEPTH};
use super::{
    alloc_block, const_block, flat_const, integer_add_no_overflow, mul, pin_eq, pin_lt_strict,
    range_check_bits, FieldR1csBuilder, LinExpr, Wire, F128,
};

const HEIGHT_BITS: usize = 64;
const PAYOUT_QUOTIENT_BITS: usize = 52;
const PAYOUT_REMAINDER_BITS: usize = 13;
const _: () = assert!(TARGET_BLOCKS_PER_DAY == (1 << 12) + (1 << 7) + (1 << 6) + (1 << 5));

pub struct DevelopmentAllocationTrace {
    /// Canonical range-check bits of the accepted child height. Consumers
    /// such as the v2 timed object policy reuse these exact wires.
    pub height_bits: [Wire; HEIGHT_BITS],
    pub active: LinExpr,
    pub payout_due: LinExpr,
    pub share_each: LinExpr,
    pub miner_subsidy: LinExpr,
    pub payout_each: LinExpr,
}

fn shifted_integer_from_bits(bits: &[Wire], shift: usize) -> LinExpr {
    assert!(bits.len() + shift <= HEIGHT_BITS);
    bits.iter()
        .enumerate()
        .fold(LinExpr::zero(), |sum, (index, &wire)| {
            sum.add(&LinExpr::from_wire(wire).scale(flat_const(1u128 << (index + shift))))
        })
}

fn less_than_bits(b: &mut FieldR1csBuilder, lhs: &[LinExpr], rhs: &[LinExpr]) -> LinExpr {
    assert_eq!(lhs.len(), rhs.len());
    let mut borrow = LinExpr::zero();
    for (left, right) in lhs.iter().zip(rhs) {
        let left_zero_right_one = mul(b, &left.add_const(F128::ONE), right);
        let borrow_when_equal = mul(b, &borrow, &left.add(right).add_const(F128::ONE));
        borrow = left_zero_right_one.add(&borrow_when_equal);
    }
    borrow
}

fn constant_bits(value: u64, width: usize) -> Vec<LinExpr> {
    (0..width)
        .map(|bit| {
            if (value >> bit) & 1 == 1 {
                LinExpr::constant(F128::ONE)
            } else {
                LinExpr::zero()
            }
        })
        .collect()
}

fn selected_depth_constant(depth: &StateDepthTrace, values: &[u64]) -> LinExpr {
    assert_eq!(
        values.len(),
        MAX_EXACT_STATE_DEPTH - MIN_EXACT_STATE_DEPTH + 1
    );
    depth
        .one_hot
        .iter()
        .zip(values)
        .fold(LinExpr::zero(), |sum, (selector, value)| {
            sum.add(&selector.scale(flat_const(*value as u128)))
        })
}

fn payout_boundary(b: &mut FieldR1csBuilder, height: &LinExpr, native_height: u64) -> LinExpr {
    let quotient = native_height / TARGET_BLOCKS_PER_DAY;
    let remainder = native_height % TARGET_BLOCKS_PER_DAY;
    let quotient = alloc_block(b, Block128::from(quotient as u128));
    let quotient_bits = range_check_bits(b, &quotient, PAYOUT_QUOTIENT_BITS);
    let remainder = alloc_block(b, Block128::from(remainder as u128));
    let remainder_bits = range_check_bits(b, &remainder, PAYOUT_REMAINDER_BITS);
    let divisor = const_block(Block128::from(TARGET_BLOCKS_PER_DAY as u128));
    let divisor_bits = range_check_bits(b, &divisor, PAYOUT_REMAINDER_BITS);
    pin_lt_strict(b, &remainder_bits, &divisor_bits);

    let terms = [
        shifted_integer_from_bits(&quotient_bits, 12),
        shifted_integer_from_bits(&quotient_bits, 7),
        shifted_integer_from_bits(&quotient_bits, 6),
        shifted_integer_from_bits(&quotient_bits, 5),
    ];
    let mut product = terms[0].clone();
    for term in &terms[1..] {
        product = integer_add_no_overflow(b, &product, term, HEIGHT_BITS);
    }
    let recomposed = integer_add_no_overflow(b, &product, &remainder, HEIGHT_BITS);
    pin_eq(b, height, &recomposed);

    remainder_bits
        .iter()
        .fold(LinExpr::constant(F128::ONE), |zero, &bit| {
            mul(b, &zero, &LinExpr::from_wire(bit).add_const(F128::ONE))
        })
}

/// Bind the exact miner share and stateless daily development payout.
pub fn bind_development_allocation(
    b: &mut FieldR1csBuilder,
    child_height: &LinExpr,
    child_depth: &StateDepthTrace,
    payout_raw_amount: &LinExpr,
) -> DevelopmentAllocationTrace {
    use noid_core::hardware::flat_to_tower_u128;

    let flat = child_height.eval(b.values());
    let tower = flat_to_tower_u128((flat.lo as u128) | ((flat.hi as u128) << 64));
    let native_height = u64::try_from(tower).expect("child height fits u64");
    let height_wires = range_check_bits(b, child_height, HEIGHT_BITS);
    let height_bits = height_wires
        .iter()
        .copied()
        .map(LinExpr::from_wire)
        .collect::<Vec<_>>();

    let below_end = less_than_bits(
        b,
        &height_bits,
        &constant_bits(DEVELOPMENT_ALLOCATION_END_HEIGHT + 1, HEIGHT_BITS),
    );
    let height_is_zero = height_bits
        .iter()
        .fold(LinExpr::constant(F128::ONE), |zero, bit| {
            mul(b, &zero, &bit.add_const(F128::ONE))
        });
    let active = mul(b, &below_end, &height_is_zero.add_const(F128::ONE));
    let interval_boundary = payout_boundary(b, child_height, native_height);
    let payout_due = mul(b, &active, &interval_boundary);

    let rewards = (MIN_EXACT_STATE_DEPTH..=MAX_EXACT_STATE_DEPTH)
        .map(|depth| noid_chain::consensus::emission::block_reward(depth as u32))
        .collect::<Vec<_>>();
    let shares = rewards.iter().map(|reward| reward / 20).collect::<Vec<_>>();
    let daily_payouts = shares
        .iter()
        .map(|share| {
            share
                .checked_mul(TARGET_BLOCKS_PER_DAY)
                .expect("development payout fits u64")
        })
        .collect::<Vec<_>>();
    let miner_active = rewards
        .iter()
        .zip(&shares)
        .map(|(reward, share)| reward - 2 * share)
        .collect::<Vec<_>>();
    let full_subsidy = selected_depth_constant(child_depth, &rewards);
    let share_each = selected_depth_constant(child_depth, &shares);
    let daily_payout_each = selected_depth_constant(child_depth, &daily_payouts);
    let active_miner = selected_depth_constant(child_depth, &miner_active);
    let miner_subsidy = full_subsidy.add(&mul(b, &active, &full_subsidy.add(&active_miner)));

    let current_share = mul(b, &active, &share_each);
    let expected_payout = mul(b, &payout_due, &daily_payout_each);
    // Suffix slot zero is a user body off payout heights and the payout body
    // on a boundary. Only the schedule-selected amount is monetary here.
    let selected_payout = mul(b, &payout_due, payout_raw_amount);
    pin_eq(b, &selected_payout, &expected_payout);

    let native_depth = {
        let flat = child_depth.value.eval(b.values());
        let tower = flat_to_tower_u128((flat.lo as u128) | ((flat.hi as u128) << 64));
        u32::try_from(tower).expect("state depth fits u32")
    };
    let native =
        development_allocation(native_height, native_depth).expect("honest development schedule");
    let native_payout = native.payout_each.unwrap_or(0);
    debug_assert_eq!(
        selected_payout.eval(b.values()),
        alloc_block_value(native_payout)
    );

    DevelopmentAllocationTrace {
        height_bits: height_wires
            .try_into()
            .expect("child height range check has 64 bits"),
        active,
        payout_due,
        share_each: current_share,
        miner_subsidy,
        payout_each: expected_payout,
    }
}

fn alloc_block_value(value: u64) -> F128 {
    use noid_core::hardware::tower_to_flat_u128;
    let flat = tower_to_flat_u128(value as u128);
    F128 {
        lo: flat as u64,
        hi: (flat >> 64) as u64,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy)]
    struct CaseWires {
        payout: Wire,
    }

    fn case(
        height: u64,
        depth: u32,
    ) -> (
        noid_ivc_core::field_r1cs::FieldR1cs,
        Vec<F128>,
        DevelopmentAllocationTrace,
        CaseWires,
    ) {
        let native = development_allocation(height, depth).unwrap();
        let mut builder = FieldR1csBuilder::new();
        let height = alloc_block(&mut builder, Block128::from(height as u128));
        let depth_value = alloc_block(&mut builder, Block128::from(depth as u128));
        let depth = StateDepthTrace::bind(&mut builder, &depth_value);
        let payout_wire = builder.alloc_f128(alloc_block_value(native.payout_each.unwrap_or(0)));
        let payout = LinExpr::from_wire(payout_wire);
        let trace = bind_development_allocation(&mut builder, &height, &depth, &payout);
        let (matrix, witness) = builder.build();
        (
            matrix,
            witness,
            trace,
            CaseWires {
                payout: payout_wire,
            },
        )
    }

    #[test]
    fn exact_edges_match_native_schedule() {
        for height in [
            1,
            TARGET_BLOCKS_PER_DAY - 1,
            TARGET_BLOCKS_PER_DAY,
            TARGET_BLOCKS_PER_DAY + 1,
            DEVELOPMENT_ALLOCATION_END_HEIGHT,
            DEVELOPMENT_ALLOCATION_END_HEIGHT + 1,
        ] {
            let native = development_allocation(height, 24).unwrap();
            let (matrix, witness, trace, _) = case(height, 24);
            assert!(matrix.satisfies(&witness), "height {height}");
            assert_eq!(
                trace.miner_subsidy.eval(&witness),
                alloc_block_value(native.miner_subsidy),
                "miner subsidy at height {height}"
            );
            assert_eq!(
                trace.payout_each.eval(&witness),
                alloc_block_value(native.payout_each.unwrap_or(0)),
                "payout at height {height}"
            );
        }
    }

    #[test]
    fn scheduled_payout_amount_is_load_bearing() {
        let (due, witness, _, wires) = case(TARGET_BLOCKS_PER_DAY, 24);
        let mut bad = witness;
        bad[wires.payout.0 as usize] += F128::ONE;
        assert!(
            !due.satisfies(&bad),
            "payout-height amount mutation was accepted"
        );
    }

    #[test]
    fn expansion_day_uses_the_current_lower_reward_tier() {
        let (matrix, witness, trace, _) = case(TARGET_BLOCKS_PER_DAY, 25);
        assert!(matrix.satisfies(&witness));
        let native = development_allocation(TARGET_BLOCKS_PER_DAY, 25).unwrap();
        assert_eq!(
            trace.payout_each.eval(&witness),
            alloc_block_value(native.payout_each.unwrap())
        );
    }
}
