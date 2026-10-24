// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Exact in-circuit stateless development-allocation schedule.

use noid_chain::consensus::development_allocation::{
    development_allocation_end_height_with_schedule, development_allocation_with_schedule,
    TARGET_BLOCKS_PER_DAY,
};
use noid_chain::consensus::emission::{V2_REWARDS_MICRONOID, V2_REWARD_INTERVAL_BLOCKS};
use noid_chain::consensus::forks::{ForkSchedule, V2Activation};
use noid_core::Block128;

use super::exact_state::{StateDepthTrace, MAX_EXACT_STATE_DEPTH, MIN_EXACT_STATE_DEPTH};
use super::{
    alloc_block, const_block, flat_const, integer_add_no_overflow, mul, pin_eq, pin_lt_strict,
    range_check_bits, FieldR1csBuilder, LinExpr, Wire, F128,
};

const HEIGHT_BITS: usize = 64;
// Both daily boundaries and the final height account for the target interval.
// Shifted terms multiply by the constant divisor in ordinary integer
// arithmetic; field multiplication would give the wrong monetary result.

pub struct DevelopmentAllocationTrace {
    /// Canonical range-check bits of the accepted child height. Consumers
    /// such as the v2 timed object policy reuse these exact wires.
    pub height_bits: [Wire; HEIGHT_BITS],
    /// Authenticated v2 activation bit, also used by contract admission in the
    /// local fork relation. It is not a witness-selected protocol version.
    pub v2_active: LinExpr,
    pub active: LinExpr,
    pub payout_due: LinExpr,
    pub share_each: LinExpr,
    pub miner_subsidy: LinExpr,
    pub payout_each: LinExpr,
}

/// Reserve the schedule outputs used by earlier slots, then bind every one
/// after the aligned selected-region allocation. The fork schedule otherwise
/// pushes that allocation across an entire 8,192-row boundary. The legacy
/// profile keeps its original ordering and matrix.
#[must_use = "finish the allocation binding before completing the block relation"]
pub(crate) struct PreparedDevelopmentAllocation<'a> {
    trace: DevelopmentAllocationTrace,
    deferred: Option<(&'a LinExpr, &'a StateDepthTrace, &'a LinExpr, ForkSchedule)>,
}

impl<'a> PreparedDevelopmentAllocation<'a> {
    pub(crate) fn legacy(
        b: &mut FieldR1csBuilder,
        height: &'a LinExpr,
        depth: &'a StateDepthTrace,
        payout_raw_amount: &'a LinExpr,
    ) -> Self {
        let old = super::development_allocation::bind_development_allocation(
            b,
            height,
            depth,
            payout_raw_amount,
        );
        Self {
            trace: DevelopmentAllocationTrace {
                height_bits: old.height_bits,
                v2_active: LinExpr::zero(),
                active: old.active,
                payout_due: old.payout_due,
                share_each: old.share_each,
                miner_subsidy: old.miner_subsidy,
                payout_each: old.payout_each,
            },
            deferred: None,
        }
    }

    pub(crate) fn new(
        b: &mut FieldR1csBuilder,
        height: &'a LinExpr,
        depth: &'a StateDepthTrace,
        payout_raw_amount: &'a LinExpr,
        schedule: ForkSchedule,
    ) -> Self {
        assert!(schedule.v2().is_some());
        let tower = |expr: &LinExpr| {
            let flat = expr.eval(b.values());
            noid_core::hardware::flat_to_tower_u128((flat.lo as u128) | ((flat.hi as u128) << 64))
        };
        let native_height = u64::try_from(tower(height)).expect("child height fits u64");
        let native_depth = u32::try_from(tower(&depth.value)).expect("child depth fits u32");
        let native = development_allocation_with_schedule(native_height, native_depth, schedule)
            .expect("honest schedule");
        let height_bits = range_check_bits(b, height, HEIGHT_BITS).try_into().unwrap();
        let trace = DevelopmentAllocationTrace {
            height_bits,
            v2_active: alloc_block(
                b,
                Block128::from(u64::from(native_height >= schedule.v2().unwrap().height())),
            ),
            active: alloc_block(b, Block128::from(u64::from(native.active))),
            payout_due: alloc_block(b, Block128::from(u64::from(native.payout_due))),
            share_each: alloc_block(
                b,
                Block128::from(if native.active { native.share_each } else { 0 }),
            ),
            miner_subsidy: alloc_block(b, Block128::from(native.miner_subsidy)),
            payout_each: alloc_block(b, Block128::from(native.payout_each.unwrap_or(0))),
        };
        Self {
            trace,
            deferred: Some((height, depth, payout_raw_amount, schedule)),
        }
    }

    pub(crate) fn trace(&self) -> &DevelopmentAllocationTrace {
        &self.trace
    }

    pub(crate) fn finish(self, b: &mut FieldR1csBuilder) {
        let Some((height, depth, payout_raw, schedule)) = self.deferred else {
            return;
        };
        let bound =
            bind_development_allocation_with_schedule(b, height, depth, payout_raw, schedule.v2());
        for (reserved, actual) in [
            (&self.trace.v2_active, &bound.v2_active),
            (&self.trace.active, &bound.active),
            (&self.trace.payout_due, &bound.payout_due),
            (&self.trace.share_each, &bound.share_each),
            (&self.trace.miner_subsidy, &bound.miner_subsidy),
            (&self.trace.payout_each, &bound.payout_each),
        ] {
            pin_eq(b, reserved, actual);
        }
        // Both decompositions bind the same authenticated height. Keep the
        // original early bits for the contract policy; no detached height is
        // introduced by delaying the schedule arithmetic.
    }
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

/// One-hot annual reward epochs derived only from the authenticated height.
/// Comparisons use fixed constants, so neither the epoch nor matrix shape
/// is chosen by the witness. Unreachable thresholds above u64::MAX stay off.
fn reward_epoch_selectors(
    b: &mut FieldR1csBuilder,
    height_bits: &[LinExpr],
    activation: Option<V2Activation>,
) -> Vec<LinExpr> {
    let mut started = vec![LinExpr::constant(F128::ONE)];
    for epoch in 1..V2_REWARDS_MICRONOID.len() {
        let threshold = activation.and_then(|at| {
            (epoch as u64)
                .checked_mul(V2_REWARD_INTERVAL_BLOCKS)
                .and_then(|elapsed| at.height().checked_add(elapsed))
        });
        started.push(match threshold {
            Some(height) => less_than_bits(b, height_bits, &constant_bits(height, HEIGHT_BITS))
                .add_const(F128::ONE),
            None => LinExpr::zero(),
        });
    }
    started.push(LinExpr::zero());
    // In characteristic two, XOR of monotone adjacent flags is their
    // disjoint interval selector. v2_active separately excludes old blocks.
    started
        .windows(2)
        .map(|pair| pair[0].add(&pair[1]))
        .collect()
}

fn payout_boundary_for(
    b: &mut FieldR1csBuilder,
    height: &LinExpr,
    native_height: u64,
    interval: u64,
) -> LinExpr {
    assert!(interval > 0);
    let shifts: Vec<usize> = (0..64)
        .rev()
        .filter(|shift| interval >> shift & 1 != 0)
        .collect();
    let remainder_bits_len = (64 - interval.leading_zeros()) as usize;
    let quotient = native_height / interval;
    let remainder = native_height % interval;
    let quotient = alloc_block(b, Block128::from(quotient as u128));
    let quotient_bits = range_check_bits(b, &quotient, HEIGHT_BITS - shifts[0]);
    let remainder = alloc_block(b, Block128::from(remainder as u128));
    let remainder_bits = range_check_bits(b, &remainder, remainder_bits_len);
    let divisor = const_block(Block128::from(interval as u128));
    let divisor_bits = range_check_bits(b, &divisor, remainder_bits_len);
    pin_lt_strict(b, &remainder_bits, &divisor_bits);

    let terms: Vec<_> = shifts
        .iter()
        .map(|&shift| shifted_integer_from_bits(&quotient_bits, shift))
        .collect();
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

fn equals_constant(b: &mut FieldR1csBuilder, bits: &[LinExpr], value: u64) -> LinExpr {
    bits.iter()
        .enumerate()
        .fold(LinExpr::constant(F128::ONE), |equal, (index, bit)| {
            let matching = if value >> index & 1 == 1 {
                bit.clone()
            } else {
                bit.add_const(F128::ONE)
            };
            mul(b, &equal, &matching)
        })
}

/// Disjoint payout selectors with fixed block counts. The daily and final
/// intervals are constants of the frozen schedule, never chosen by a
/// prover. The output is independent of the occupied transaction positions.
fn payout_rules(
    b: &mut FieldR1csBuilder,
    height: &LinExpr,
    bits: &[LinExpr],
    native_height: u64,
    activation: Option<V2Activation>,
) -> (LinExpr, Vec<(LinExpr, u64)>) {
    let Some(activation) = activation else {
        let due = payout_boundary_for(b, height, native_height, TARGET_BLOCKS_PER_DAY);
        return (
            LinExpr::constant(F128::ZERO),
            vec![(due, TARGET_BLOCKS_PER_DAY)],
        );
    };
    let at = activation.height();
    assert_eq!(86_400 % activation.block_time(), 0);
    let interval = 86_400 / activation.block_time();
    let before = less_than_bits(b, bits, &constant_bits(at, HEIGHT_BITS));
    let after = before.add_const(F128::ONE);
    let old_boundary = payout_boundary_for(b, height, native_height, TARGET_BLOCKS_PER_DAY);
    let old_due = mul(b, &before, &old_boundary);
    // H is accrual block one, matching its new-rule target interval.
    let elapsed_native = native_height.saturating_sub(at - 1);
    let elapsed = alloc_block(b, Block128::from(elapsed_native));
    let selected_height = mul(b, &after, height);
    let origin = after.scale(flat_const((at - 1) as u128));
    let recomposed = integer_add_no_overflow(b, &elapsed, &origin, HEIGHT_BITS);
    pin_eq(b, &selected_height, &recomposed);
    let boundary = payout_boundary_for(b, &elapsed, elapsed_native, interval);
    let first = equals_constant(b, bits, at);
    let regular = mul(b, &after, &first.add_const(F128::ONE));
    let regular = mul(b, &regular, &boundary);
    let mut rules = vec![(old_due, TARGET_BLOCKS_PER_DAY), (regular, interval)];
    let schedule = ForkSchedule::new(Some(0), Some(activation)).expect("checked schedule");
    let end = development_allocation_end_height_with_schedule(schedule);
    let final_blocks = end.saturating_sub(at - 1) % interval;
    if end > at && final_blocks != 0 {
        rules.push((equals_constant(b, bits, end), final_blocks));
    }
    (after, rules)
}

fn bind_development_allocation_with_schedule(
    b: &mut FieldR1csBuilder,
    child_height: &LinExpr,
    child_depth: &StateDepthTrace,
    payout_raw_amount: &LinExpr,
    activation: Option<V2Activation>,
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

    let schedule = ForkSchedule::new(Some(0), activation).expect("checked schedule");
    let end = development_allocation_end_height_with_schedule(schedule);
    let below_end = less_than_bits(b, &height_bits, &constant_bits(end + 1, HEIGHT_BITS));
    let height_is_zero = height_bits
        .iter()
        .fold(LinExpr::constant(F128::ONE), |zero, bit| {
            mul(b, &zero, &bit.add_const(F128::ONE))
        });
    let active = mul(b, &below_end, &height_is_zero.add_const(F128::ONE));
    let (v2_active, payout_rules) =
        payout_rules(b, child_height, &height_bits, native_height, activation);
    let interval_boundary = payout_rules
        .iter()
        .fold(LinExpr::zero(), |sum, (selector, _)| sum.add(selector));
    let payout_due = mul(b, &active, &interval_boundary);

    let legacy_rewards = (MIN_EXACT_STATE_DEPTH..=MAX_EXACT_STATE_DEPTH)
        .map(|depth| noid_chain::consensus::emission::block_reward(depth as u32))
        .collect::<Vec<_>>();
    let reward_epochs = reward_epoch_selectors(b, &height_bits, activation);
    // All products are computed on fixed integer tables, then selected by
    // legacy depth or v2 elapsed height. No integer amount is multiplied in F128.
    let selected_amount = |b: &mut FieldR1csBuilder, amount: &dyn Fn(u64) -> u64| {
        let old_values = legacy_rewards
            .iter()
            .copied()
            .map(amount)
            .collect::<Vec<_>>();
        let old = selected_depth_constant(child_depth, &old_values);
        let new = reward_epochs
            .iter()
            .zip(V2_REWARDS_MICRONOID)
            .fold(LinExpr::zero(), |sum, (selector, reward)| {
                sum.add(&selector.scale(flat_const(amount(reward) as u128)))
            });
        old.add(&mul(b, &v2_active, &old.add(&new)))
    };
    let full_subsidy = selected_amount(b, &|reward| reward);
    let share_each = selected_amount(b, &|reward| reward / 20);
    let fork_schedule = activation.is_some();
    let selected_payout_each = if fork_schedule {
        payout_rules
            .iter()
            .fold(LinExpr::zero(), |sum, (selector, blocks)| {
                let amount = selected_amount(b, &|reward| {
                    (reward / 20).checked_mul(*blocks).expect("payout fits u64")
                });
                sum.add(&mul(b, selector, &amount))
            })
    } else {
        selected_amount(b, &|reward| {
            (reward / 20)
                .checked_mul(TARGET_BLOCKS_PER_DAY)
                .expect("payout fits u64")
        })
    };
    let active_miner = selected_amount(b, &|reward| reward - 2 * (reward / 20));
    let miner_subsidy = full_subsidy.add(&mul(b, &active, &full_subsidy.add(&active_miner)));

    let current_share = mul(b, &active, &share_each);
    let expected_payout = mul(
        b,
        if fork_schedule { &active } else { &payout_due },
        &selected_payout_each,
    );
    // Suffix slot zero is a user body off payout heights and the payout body
    // on a boundary. Only the schedule-selected amount is monetary here.
    let selected_payout = mul(b, &payout_due, payout_raw_amount);
    pin_eq(b, &selected_payout, &expected_payout);

    let native_depth = {
        let flat = child_depth.value.eval(b.values());
        let tower = flat_to_tower_u128((flat.lo as u128) | ((flat.hi as u128) << 64));
        u32::try_from(tower).expect("state depth fits u32")
    };
    let native_payout = development_allocation_with_schedule(native_height, native_depth, schedule)
        .expect("checked candidate schedule")
        .payout_each
        .unwrap_or(0);
    debug_assert_eq!(
        selected_payout.eval(b.values()),
        alloc_block_value(native_payout)
    );

    DevelopmentAllocationTrace {
        height_bits: height_wires
            .try_into()
            .expect("child height range check has 64 bits"),
        v2_active,
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
    use noid_chain::consensus::development_allocation::DEVELOPMENT_ALLOCATION_END_HEIGHT;

    #[test]
    fn explicit_schedule_matches_native_boundaries_and_rejects_changed_height() {
        for interval in [20, 30, 40] {
            let period = 86_400 / interval;
            for activation in [
                1,
                10,
                4_320,
                219_177,
                DEVELOPMENT_ALLOCATION_END_HEIGHT,
                u64::MAX - V2_REWARD_INTERVAL_BLOCKS,
                u64::MAX,
            ] {
                let at = V2Activation::new(activation, interval).unwrap();
                let schedule = ForkSchedule::new(Some(0), Some(at)).unwrap();
                let end = development_allocation_end_height_with_schedule(schedule);
                let mut digest = None;
                for height in [
                    activation - 1,
                    activation,
                    activation.saturating_add(1),
                    activation.saturating_add(period - 1),
                    activation.saturating_add(period),
                    end,
                    end + 1,
                    DEVELOPMENT_ALLOCATION_END_HEIGHT,
                    DEVELOPMENT_ALLOCATION_END_HEIGHT + 1,
                    u64::MAX,
                ] {
                    let native =
                        development_allocation_with_schedule(height, 24, schedule).unwrap();
                    let mut b = FieldR1csBuilder::new();
                    let h = b.alloc_f128(alloc_block_value(height));
                    let h_expr = LinExpr::from_wire(h);
                    let depth_value = alloc_block(&mut b, Block128(24));
                    let depth = StateDepthTrace::bind(&mut b, &depth_value);
                    let amount =
                        alloc_block(&mut b, Block128(native.payout_each.unwrap_or(0) as u128));
                    let prepared = PreparedDevelopmentAllocation::new(
                        &mut b, &h_expr, &depth, &amount, schedule,
                    );
                    let trace = prepared.trace();
                    let reserved = [
                        &trace.v2_active,
                        &trace.active,
                        &trace.payout_due,
                        &trace.share_each,
                        &trace.miner_subsidy,
                        &trace.payout_each,
                    ]
                    .map(|value| {
                        assert_eq!(value.terms.len(), 1);
                        value.terms[0].0 as usize
                    });
                    assert_eq!(
                        trace.payout_each.eval(b.values()),
                        alloc_block_value(native.payout_each.unwrap_or(0))
                    );
                    assert_eq!(
                        trace.miner_subsidy.eval(b.values()),
                        alloc_block_value(native.miner_subsidy)
                    );
                    prepared.finish(&mut b);
                    let (matrix, mut witness) = b.build();
                    assert!(
                        matrix.satisfies(&witness),
                        "interval={interval}, activation={activation}, height={height}"
                    );
                    let actual = matrix.structural_statement_digest();
                    assert!(digest.is_none_or(|expected| expected == actual));
                    digest = Some(actual);
                    for output in reserved {
                        witness[output] += F128::ONE;
                        assert!(
                            !matrix.satisfies(&witness),
                            "unbound schedule output {output}"
                        );
                        witness[output] += F128::ONE;
                    }
                    witness[h.0 as usize] += F128::ONE;
                    assert!(!matrix.satisfies(&witness));
                }
            }
        }
    }

    #[test]
    fn every_state_level_matches_at_fork_annual_daily_and_final_boundaries() {
        let h = noid_chain::consensus::params::MAINNET_V2_ACTIVATION_HEIGHT;
        let at = V2Activation::new(h, 30).unwrap();
        let schedule = ForkSchedule::new(Some(95_125), Some(at)).unwrap();
        let end = development_allocation_end_height_with_schedule(schedule);
        let mut digest = None;
        let mut heights = vec![h - 1, h, h + 2878, h + 2879, end, end + 1, u64::MAX];
        for epoch in 1..V2_REWARDS_MICRONOID.len() {
            let threshold = h + epoch as u64 * V2_REWARD_INTERVAL_BLOCKS;
            heights.extend([threshold - 1, threshold, threshold + 1, threshold + 2879]);
        }
        for level in 24..=32 {
            for &height in &heights {
                let native = development_allocation_with_schedule(height, level, schedule).unwrap();
                let mut b = FieldR1csBuilder::new();
                let height = alloc_block(&mut b, Block128::from(height));
                let depth_value = alloc_block(&mut b, Block128::from(u64::from(level)));
                let depth = StateDepthTrace::bind(&mut b, &depth_value);
                let amount = alloc_block(&mut b, Block128::from(native.payout_each.unwrap_or(0)));
                let prepared =
                    PreparedDevelopmentAllocation::new(&mut b, &height, &depth, &amount, schedule);
                let reward_wire = prepared.trace().miner_subsidy.terms[0].0 as usize;
                prepared.finish(&mut b);
                let (matrix, mut witness) = b.build();
                assert!(matrix.satisfies(&witness), "level={level}");
                let actual = matrix.structural_statement_digest();
                assert!(digest.is_none_or(|expected| expected == actual));
                digest = Some(actual);
                // A State-selected reward, another year or any other
                // subsidy cannot replace the height-selected amount.
                for wrong in V2_REWARDS_MICRONOID {
                    if wrong != native.miner_subsidy {
                        let original = witness[reward_wire];
                        witness[reward_wire] = alloc_block_value(wrong);
                        assert!(!matrix.satisfies(&witness), "level={level}, wrong={wrong}");
                        witness[reward_wire] = original;
                    }
                }
            }
        }
    }
}
