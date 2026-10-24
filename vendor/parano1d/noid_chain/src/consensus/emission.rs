// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Height-selected block reward schedules. The table below is the legacy rule;
//! v2 advances through [`V2_REWARDS_MICRONOID`] by elapsed block height,
//! starting at its activation block. State size does not select a v2 reward.
//!
//! Before v2, reward halves with every state expansion (`log_slots += 1`),
//! floored at 1 NOID.
//!
//! ```text
//! log_slots | expansion | reward
//! ----------|-----------|-------
//!    24      |     0     | 50.000000 NOID  (genesis)
//!    25      |     1     | 25.000000 NOID
//!    26      |     2     | 12.500000 NOID
//!    27      |     3     |  6.250000 NOID
//!    28      |     4     |  3.125000 NOID
//!    29      |     5     |  1.562500 NOID
//!    30+     |     6+    |  1.000000 NOID  (floor, forever)
//! ```
//!
//! The v2 height schedule does not change occupancy-sensitive State-growth
//! fees or their deterministic burn. Consolidation still avoids charges for
//! adding live slots; other applicable transaction fees remain payable.

use crate::consensus::fees::claimable_fee_for_tx_body;
use crate::consensus::params::{
    BASE_REWARD_MICRONOID, FLOOR_REWARD_MICRONOID, LOG_SLOTS_GENESIS, MICRONOID_PER_NOID,
};
use noid_tx::types::TxBody;

/// One nominal 365-day year at the v2 target of 30 seconds per block.
/// The activation block has elapsed height zero; the first reduction occurs
/// exactly this many blocks after activation, independent of State size.
pub const V2_REWARD_INTERVAL_BLOCKS: u64 = 1_051_200;

/// Exact gross subsidy for successive v2 height epochs, before allocation.
/// These decimal amounts are consensus constants, not a floating-point formula.
pub const V2_REWARDS_MICRONOID: [u64; 9] = [
    16_000_000, 11_300_000, 8_000_000, 5_650_000, 4_000_000, 2_830_000, 2_000_000, 1_410_000,
    1_000_000,
];

pub fn v2_block_reward_at_elapsed(elapsed_blocks: u64) -> u64 {
    let epoch = (elapsed_blocks / V2_REWARD_INTERVAL_BLOCKS)
        .min((V2_REWARDS_MICRONOID.len() - 1) as u64) as usize;
    V2_REWARDS_MICRONOID[epoch]
}

pub fn block_reward_with_schedule(
    height: u64,
    log_slots: u32,
    schedule: super::forks::ForkSchedule,
) -> u64 {
    match schedule.v2() {
        Some(activation) if height >= activation.height() => {
            v2_block_reward_at_elapsed(height - activation.height())
        }
        _ => block_reward(log_slots),
    }
}

pub fn block_reward_at_height(height: u64, log_slots: u32) -> u64 {
    block_reward_with_schedule(height, log_slots, super::forks::ACTIVE_SCHEDULE)
}

/// Compute the legacy block reward in μNOID for the given `log_slots` value.
/// Frozen legacy relations retain this function; network callers use
/// [`block_reward_at_height`].
///
/// `log_slots` is the current state capacity exponent from the block header.
/// Halves once per state expansion, never below `FLOOR_REWARD_MICRONOID`.
///
/// # Examples
///
/// ```
/// use noid_chain::consensus::emission::block_reward;
/// assert_eq!(block_reward(24), 50_000_000); // 50 NOID at genesis
/// assert_eq!(block_reward(25), 25_000_000); // 25 NOID after first expansion
/// assert_eq!(block_reward(30), 1_000_000);  // 1 NOID floor
/// assert_eq!(block_reward(32), 1_000_000);  // 1 NOID still
/// ```
pub fn block_reward(log_slots: u32) -> u64 {
    let expansions = log_slots.saturating_sub(LOG_SLOTS_GENESIS);
    BASE_REWARD_MICRONOID
        .checked_shr(expansions)
        .unwrap_or(0)
        .max(FLOOR_REWARD_MICRONOID)
}

/// Sum all gross transaction fees (non-coinbase) in μNOID.
///
/// A block can contain 255 `u64` fees, so aggregation uses `u128`; consensus
/// predicates never silently saturate a monetary total. This is accounting
/// data, not a coinbase ceiling: deterministic state-growth burn must first be
/// removed via [`claimable_fee_for_tx_body`].
pub fn total_fees(txs: &[TxBody]) -> u128 {
    txs.iter()
        .filter(|tx| !tx.is_coinbase)
        .map(|tx| u128::from(tx.fee))
        .sum()
}

/// Maximum value the coinbase output is permitted to carry (μNOID).
///
/// Only miner-claimable fees are included. The deterministic state-growth
/// component is burned and can never be recovered through coinbase.
pub fn max_coinbase_value(
    child_height: u64,
    child_log_slots: u32,
    parent_active_slot_count: u64,
    parent_log_slots: u32,
    non_coinbase_txs: &[TxBody],
) -> u128 {
    let claimable_fee_sum: u128 = non_coinbase_txs
        .iter()
        .filter(|tx| !tx.is_coinbase)
        .map(|tx| {
            u128::from(claimable_fee_for_tx_body(
                tx,
                parent_active_slot_count,
                parent_log_slots,
            ))
        })
        .sum();
    max_coinbase_value_from_claimable_fee_sum(child_height, child_log_slots, claimable_fee_sum)
}

/// Same as [`max_coinbase_value`] but accepts an already checked sum of
/// miner-claimable fees (paid fee minus deterministic burn).
///
/// Used by `validate_block_consensus` to avoid cloning all non-coinbase
/// bodies just to repeat fee accounting.
#[inline]
pub fn max_coinbase_value_from_claimable_fee_sum(
    child_height: u64,
    child_log_slots: u32,
    claimable_fee_sum: u128,
) -> u128 {
    max_coinbase_value_from_claimable_fee_sum_with_schedule(
        child_height,
        child_log_slots,
        claimable_fee_sum,
        super::forks::ACTIVE_SCHEDULE,
    )
    .expect("release emission and daily intervals are exact")
}

pub fn max_coinbase_value_from_claimable_fee_sum_with_schedule(
    child_height: u64,
    child_log_slots: u32,
    claimable_fee_sum: u128,
    schedule: super::forks::ForkSchedule,
) -> Result<u128, super::development_allocation::DevelopmentAllocationError> {
    let allocation = super::development_allocation::development_allocation_with_schedule(
        child_height,
        child_log_slots,
        schedule,
    )?;
    Ok(u128::from(allocation.miner_subsidy) + claimable_fee_sum)
}

/// Format a μNOID amount as a human-readable string (not consensus-critical).
pub fn format_noid(micronoid: u64) -> String {
    let whole = micronoid / MICRONOID_PER_NOID;
    let frac = micronoid % MICRONOID_PER_NOID;
    format!("{}.{:06} NOID", whole, frac)
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::primitives::Address;
    use noid_tx::{output_bitmap_bit, TxBody, TxInput, TxOutput, TX_INPUTS, TX_OUTPUTS};

    fn fee_body(fee: u64, coinbase: bool) -> TxBody {
        TxBody {
            epoch_anchor: [1u8; 32],
            fee: if coinbase { 0 } else { fee },
            input_owner: Address([0u8; 32]),
            inputs: [TxInput::dummy(); TX_INPUTS],
            outputs: [TxOutput::dummy(); TX_OUTPUTS],
            validity_bitmap: 0,
            is_coinbase: coinbase,
        }
    }

    #[test]
    fn reward_halves_with_expansion_and_has_floor() {
        assert_eq!(block_reward(LOG_SLOTS_GENESIS), BASE_REWARD_MICRONOID);
        assert_eq!(
            block_reward(LOG_SLOTS_GENESIS + 1),
            BASE_REWARD_MICRONOID / 2
        );
        assert_eq!(
            block_reward(LOG_SLOTS_GENESIS + 100),
            FLOOR_REWARD_MICRONOID
        );
    }

    #[test]
    fn v2_rewards_advance_by_elapsed_height_independently_of_state() {
        use crate::consensus::forks::{ForkSchedule, V2Activation};
        let expected = [
            16_000_000, 11_300_000, 8_000_000, 5_650_000, 4_000_000, 2_830_000, 2_000_000,
            1_410_000, 1_000_000,
        ];
        assert_eq!(V2_REWARD_INTERVAL_BLOCKS, 365 * 24 * 60 * 60 / 30);
        for activation in [10, super::super::params::MAINNET_V2_ACTIVATION_HEIGHT] {
            let schedule = ForkSchedule::new(Some(5), V2Activation::new(activation, 30)).unwrap();
            for level in 24..=32 {
                for height in [0, 4, 5, activation - 1] {
                    assert_eq!(
                        block_reward_with_schedule(height, level, schedule),
                        block_reward(level)
                    );
                }
                for (epoch, reward) in expected.into_iter().enumerate() {
                    let threshold = activation + epoch as u64 * V2_REWARD_INTERVAL_BLOCKS;
                    for height in [
                        threshold,
                        threshold + 1,
                        threshold + V2_REWARD_INTERVAL_BLOCKS - 1,
                    ] {
                        assert_eq!(block_reward_with_schedule(height, level, schedule), reward);
                    }
                    if epoch > 0 {
                        assert_eq!(
                            block_reward_with_schedule(threshold - 1, level, schedule),
                            expected[epoch - 1]
                        );
                    }
                }
                assert_eq!(
                    block_reward_with_schedule(u64::MAX, level, schedule),
                    1_000_000
                );
            }
        }
        assert_eq!(v2_block_reward_at_elapsed(u64::MAX), 1_000_000);
    }

    #[test]
    fn reward_clock_never_wraps_at_the_height_limit() {
        use crate::consensus::forks::{ForkSchedule, V2Activation};
        for activation in [u64::MAX, u64::MAX - V2_REWARD_INTERVAL_BLOCKS] {
            let schedule = ForkSchedule::new(Some(5), V2Activation::new(activation, 30)).unwrap();
            assert_eq!(
                block_reward_with_schedule(activation - 1, 25, schedule),
                25_000_000
            );
            assert_eq!(
                block_reward_with_schedule(activation, 32, schedule),
                16_000_000
            );
            assert_eq!(
                block_reward_with_schedule(u64::MAX, 24, schedule),
                if activation == u64::MAX {
                    16_000_000
                } else {
                    11_300_000
                }
            );
        }
        let legacy = ForkSchedule::new(Some(5), None).unwrap();
        for level in 24..=32 {
            assert_eq!(
                block_reward_with_schedule(u64::MAX, level, legacy),
                block_reward(level)
            );
        }
    }

    #[test]
    fn total_fees_excludes_coinbase_without_u64_saturation() {
        assert_eq!(
            total_fees(&[fee_body(7, false), fee_body(0, true), fee_body(9, false),]),
            16
        );
        assert_eq!(
            total_fees(&[fee_body(u64::MAX, false), fee_body(1, false)]),
            u128::from(u64::MAX) + 1
        );
    }

    #[test]
    fn coinbase_ceiling_excludes_state_growth_burn() {
        let mut tx = fee_body(9_000, false);
        tx.inputs[0].slot_index = 1;
        tx.outputs[0].slot_index = 2;
        tx.outputs[1].slot_index = 3;
        tx.validity_bitmap = 1 | output_bitmap_bit(0) | output_bitmap_bit(1);
        let ceiling = max_coinbase_value(1, LOG_SLOTS_GENESIS, 0, LOG_SLOTS_GENESIS, &[tx]);
        assert_eq!(
            ceiling,
            u128::from(
                crate::consensus::development_allocation::miner_subsidy(1, LOG_SLOTS_GENESIS,)
                    + 6_500,
            )
        );
        assert_eq!(
            ceiling,
            max_coinbase_value_from_claimable_fee_sum(1, LOG_SLOTS_GENESIS, 6_500)
        );
    }
}
