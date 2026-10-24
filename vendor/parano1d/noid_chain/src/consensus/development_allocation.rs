// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Deterministic launch-period development allocation.
//!
//! For the first three target-time years after genesis, miners receive 90% of
//! each block subsidy. O(1) Network Fund and ParanO(1)d Lab each receive one
//! mandatory daily payout calculated from the reward tier active in the payout
//! block. A state expansion during that day can therefore make the effective
//! fund share smaller than 5%; the difference is never issued. Fees remain
//! entirely miner-claimable after the existing state-growth burn.

use noid_poseidon2b::primitives::Address;

use super::emission::{block_reward, block_reward_with_schedule};
use super::forks::{ForkSchedule, ACTIVE_SCHEDULE};
use super::params::BLOCK_TIME;

/// Target blocks in one wall-clock day at the consensus block interval.
pub const TARGET_BLOCKS_PER_DAY: u64 = 24 * 60 * 60 / BLOCK_TIME;

const _: () = assert!(
    (24_u64 * 60 * 60).is_multiple_of(BLOCK_TIME),
    "BLOCK_TIME must divide one day exactly"
);

/// Three 365-day target-time years, excluding built-in genesis height zero.
pub const DEVELOPMENT_ALLOCATION_END_HEIGHT: u64 = TARGET_BLOCKS_PER_DAY * 365 * 3;

/// The duration is shared by both intervals; the v2 fork does not restart it.
pub const DEVELOPMENT_ALLOCATION_DURATION_SECONDS: u64 = 86_400 * 365 * 3;

/// Number of mandatory daily payouts over the allocation period.
pub const DEVELOPMENT_ALLOCATION_PAYOUTS: u64 =
    DEVELOPMENT_ALLOCATION_END_HEIGHT / TARGET_BLOCKS_PER_DAY;

/// One maximum fund share is one twentieth (5%) of the block subsidy.
pub const DEVELOPMENT_SHARE_DENOMINATOR: u64 = 20;

/// O(1) Network Fund recipient.
pub const O1_NETWORK_FUND_ADDRESS: Address = Address([
    0x1c, 0x5b, 0x23, 0x74, 0x54, 0xad, 0xab, 0xeb, 0x0e, 0x95, 0x37, 0xb5, 0x87, 0x02, 0xd7, 0xfe,
    0x8c, 0x0e, 0x63, 0x30, 0xc3, 0x0b, 0x58, 0xee, 0x9b, 0x3f, 0x19, 0x8a, 0x3b, 0x46, 0xf6, 0x78,
]);

/// ParanO(1)d Lab recipient.
pub const PARANO1D_LAB_ADDRESS: Address = Address([
    0x36, 0x24, 0xd0, 0xc7, 0x8d, 0x0d, 0x20, 0x87, 0x61, 0x93, 0xdc, 0xbf, 0xc2, 0xc2, 0x91, 0xe5,
    0x52, 0x6a, 0x6e, 0x37, 0x08, 0x38, 0xc4, 0x3f, 0x99, 0xda, 0x82, 0x35, 0x6c, 0x63, 0x2b, 0x40,
]);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DevelopmentAllocation {
    /// The block subsidy is still inside the three-year allocation period.
    pub active: bool,
    /// The block must carry the mandatory two-output daily payout.
    pub payout_due: bool,
    /// Five percent of the reward tier active in this block.
    pub share_each: u64,
    /// Exact amount of each daily payout output.
    pub payout_each: Option<u64>,
    /// Maximum subsidy component claimable by the primary coinbase.
    pub miner_subsidy: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DevelopmentAllocationError {
    InexactRewardShare,
    PayoutOverflow,
    InexactInterval,
}

impl core::fmt::Display for DevelopmentAllocationError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for DevelopmentAllocationError {}

/// Last eligible height after accounting for every target interval from
/// genesis. The fork block contributes a new-rule interval. A fork after the
/// legacy period has expired cannot restart it. An incomplete final interval
/// is not counted, so the horizon never exceeds the original target duration.
pub const fn development_allocation_end_height_with_schedule(schedule: ForkSchedule) -> u64 {
    let Some(at) = schedule.v2() else {
        return DEVELOPMENT_ALLOCATION_END_HEIGHT;
    };
    if at.height() > DEVELOPMENT_ALLOCATION_END_HEIGHT {
        return DEVELOPMENT_ALLOCATION_END_HEIGHT;
    }
    let legacy_blocks = at.height() - 1;
    let remaining = DEVELOPMENT_ALLOCATION_DURATION_SECONDS - legacy_blocks * BLOCK_TIME;
    legacy_blocks + remaining / at.block_time()
}

/// Complete allocation with explicit consensus timing and emission rules.
/// The old incomplete day is discarded at the fork. H is the first block of
/// the new accrual period; no payout occurs in H itself, and the first complete
/// 30-second day ends at H+2879. The final eligible block pays any partial day.
pub fn development_allocation_with_schedule(
    height: u64,
    log_slots: u32,
    schedule: ForkSchedule,
) -> Result<DevelopmentAllocation, DevelopmentAllocationError> {
    let Some(at) = schedule.v2().filter(|at| height >= at.height()) else {
        return development_allocation(height, log_slots);
    };
    if 86_400 % at.block_time() != 0 {
        return Err(DevelopmentAllocationError::InexactInterval);
    }
    let subsidy = block_reward_with_schedule(height, log_slots, schedule);
    let end_height = development_allocation_end_height_with_schedule(schedule);
    if height > end_height {
        return Ok(DevelopmentAllocation {
            active: false,
            payout_due: false,
            share_each: 0,
            payout_each: None,
            miner_subsidy: subsidy,
        });
    }
    let share_each = development_share_each(subsidy)?;
    let interval = 86_400 / at.block_time();
    let elapsed = height - (at.height() - 1);
    let count = if height == at.height() {
        None
    } else if elapsed.is_multiple_of(interval) {
        Some(interval)
    } else if height == end_height {
        Some(elapsed % interval)
    } else {
        None
    };
    let payout_each = count
        .map(|count| {
            share_each
                .checked_mul(count)
                .ok_or(DevelopmentAllocationError::PayoutOverflow)
        })
        .transpose()?;
    Ok(DevelopmentAllocation {
        active: true,
        payout_due: count.is_some(),
        share_each,
        payout_each,
        miner_subsidy: subsidy - 2 * share_each,
    })
}

pub fn development_allocation_at_height(
    height: u64,
    log_slots: u32,
) -> Result<DevelopmentAllocation, DevelopmentAllocationError> {
    development_allocation_with_schedule(height, log_slots, ACTIVE_SCHEDULE)
}

pub fn miner_subsidy_at_height(height: u64, log_slots: u32) -> u64 {
    development_allocation_at_height(height, log_slots)
        .expect("release emission and daily intervals are exact")
        .miner_subsidy
}

pub fn development_payout_due_at_height(height: u64) -> bool {
    development_allocation_at_height(height, super::params::LOG_SLOTS_GENESIS)
        .expect("release emission and daily intervals are exact")
        .payout_due
}

#[inline]
pub const fn development_allocation_active(height: u64) -> bool {
    height > 0 && height <= DEVELOPMENT_ALLOCATION_END_HEIGHT
}

#[inline]
pub const fn development_payout_due(height: u64) -> bool {
    development_allocation_active(height) && height.is_multiple_of(TARGET_BLOCKS_PER_DAY)
}

/// Exact five-percent share of one subsidy.
pub fn development_share_each(subsidy: u64) -> Result<u64, DevelopmentAllocationError> {
    if !subsidy.is_multiple_of(DEVELOPMENT_SHARE_DENOMINATOR) {
        return Err(DevelopmentAllocationError::InexactRewardShare);
    }
    Ok(subsidy / DEVELOPMENT_SHARE_DENOMINATOR)
}

/// Legacy subsidy component; frozen legacy relations keep this exact rule.
#[inline]
pub fn miner_subsidy(height: u64, log_slots: u32) -> u64 {
    let subsidy = block_reward(log_slots);
    if development_allocation_active(height) {
        let share = development_share_each(subsidy)
            .expect("the fixed emission schedule is exactly divisible by twenty");
        subsidy - 2 * share
    } else {
        subsidy
    }
}

/// Compute the legacy stateless allocation for one child block.
/// Network callers use [`development_allocation_at_height`].
///
/// Every daily payout uses the reward tier active in that payout block for the
/// whole target-time day. Because state depth and reward are monotone, this can
/// only leave part of the maximum development share unissued; it can never
/// create additional issuance.
pub fn development_allocation(
    child_height: u64,
    child_log_slots: u32,
) -> Result<DevelopmentAllocation, DevelopmentAllocationError> {
    let subsidy = block_reward(child_log_slots);
    if !development_allocation_active(child_height) {
        return Ok(DevelopmentAllocation {
            active: false,
            payout_due: false,
            share_each: 0,
            payout_each: None,
            miner_subsidy: subsidy,
        });
    }

    let share_each = development_share_each(subsidy)?;
    let payout_due = development_payout_due(child_height);
    let payout_each = if payout_due {
        Some(
            share_each
                .checked_mul(TARGET_BLOCKS_PER_DAY)
                .ok_or(DevelopmentAllocationError::PayoutOverflow)?,
        )
    } else {
        None
    };

    Ok(DevelopmentAllocation {
        active: true,
        payout_due,
        share_each,
        payout_each,
        miner_subsidy: subsidy - 2 * share_each,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consensus::forks::V2Activation;
    use crate::consensus::params::{LOG_SLOTS_GENESIS, LOG_SLOTS_MAX};

    #[test]
    fn mainnet_fund_addresses_are_canonical() {
        assert_eq!(
            O1_NETWORK_FUND_ADDRESS.to_bech32(),
            "o1r3djxaz54k47kr54x76cwqkhl6xqucescv943m5m8uvc5w6x7euqct3h07"
        );
        assert_eq!(
            PARANO1D_LAB_ADDRESS.to_bech32(),
            "o1xcjdp3udp5sgwcvnmjlu9s53u4fx5m3hpquvg0uem2pr2mrr9dqq38jple"
        );
    }

    #[test]
    fn schedule_edges_are_exact() {
        assert!(!development_allocation_active(0));
        assert!(development_allocation_active(1));
        assert!(!development_payout_due(TARGET_BLOCKS_PER_DAY - 1));
        assert!(development_payout_due(TARGET_BLOCKS_PER_DAY));
        assert!(!development_payout_due(TARGET_BLOCKS_PER_DAY + 1));
        assert!(development_allocation_active(
            DEVELOPMENT_ALLOCATION_END_HEIGHT
        ));
        assert!(development_payout_due(DEVELOPMENT_ALLOCATION_END_HEIGHT));
        assert!(!development_allocation_active(
            DEVELOPMENT_ALLOCATION_END_HEIGHT + 1
        ));
        assert_eq!(DEVELOPMENT_ALLOCATION_PAYOUTS, 1_095);
    }

    #[test]
    fn every_reward_tier_reserves_at_most_ninety_five_five() {
        for depth in LOG_SLOTS_GENESIS..=LOG_SLOTS_MAX {
            let subsidy = block_reward(depth);
            let share = development_share_each(subsidy).unwrap();
            let allocation = development_allocation(1, depth).unwrap();
            assert_eq!(allocation.share_each, share);
            assert_eq!(allocation.miner_subsidy + 2 * share, subsidy);
        }
    }

    #[test]
    fn daily_payout_uses_the_payout_blocks_reward_tier() {
        for depth in LOG_SLOTS_GENESIS..=LOG_SLOTS_MAX {
            let share = development_share_each(block_reward(depth)).unwrap();
            let allocation = development_allocation(TARGET_BLOCKS_PER_DAY, depth).unwrap();
            assert_eq!(allocation.payout_each, Some(share * TARGET_BLOCKS_PER_DAY));
        }
    }

    #[test]
    fn expansion_day_conservatively_uses_the_lower_reward() {
        let old_share = development_share_each(block_reward(LOG_SLOTS_GENESIS)).unwrap();
        let new_share = development_share_each(block_reward(LOG_SLOTS_GENESIS + 1)).unwrap();
        let allocation =
            development_allocation(TARGET_BLOCKS_PER_DAY, LOG_SLOTS_GENESIS + 1).unwrap();
        assert_eq!(
            allocation.payout_each,
            Some(new_share * TARGET_BLOCKS_PER_DAY)
        );
        assert!(new_share < old_share);
    }

    #[test]
    fn final_payout_is_followed_by_full_miner_reward() {
        let final_allocation =
            development_allocation(DEVELOPMENT_ALLOCATION_END_HEIGHT, LOG_SLOTS_GENESIS).unwrap();
        assert!(final_allocation.payout_due);
        assert!(final_allocation.payout_each.is_some());

        let post = development_allocation(DEVELOPMENT_ALLOCATION_END_HEIGHT + 1, LOG_SLOTS_GENESIS)
            .unwrap();
        assert!(!post.active);
        assert!(!post.payout_due);
        assert_eq!(post.payout_each, None);
        assert_eq!(post.miner_subsidy, block_reward(LOG_SLOTS_GENESIS));
    }

    #[test]
    fn scheduled_mainnet_horizon_and_daily_boundaries_are_exact() {
        let h = super::super::params::MAINNET_V2_ACTIVATION_HEIGHT;
        let schedule = ForkSchedule::new(Some(95_125), V2Activation::new(h, 30)).unwrap();
        let end = development_allocation_end_height_with_schedule(schedule);
        assert_eq!(end, 3_223_778);
        assert_eq!(schedule.ideal_elapsed(0, end), 94_607_980);
        assert_eq!(schedule.ideal_elapsed(0, end + 1), 94_608_010);
        for height in [0, 1, 95_124, 95_125, 207_360, h - 1] {
            for depth in 24..=32 {
                assert_eq!(
                    development_allocation_with_schedule(height, depth, schedule),
                    development_allocation(height, depth)
                );
            }
        }
        let at = |height| development_allocation_with_schedule(height, 24, schedule).unwrap();
        assert_eq!(at(h).miner_subsidy, 14_400_000);
        assert_eq!(at(h).share_each, 800_000);
        for height in [h, h + 1, h + 2878, h + 2880, end - 1, end + 1] {
            assert_eq!(at(height).payout_each, None, "height={height}");
        }
        assert_eq!(at(h + 2879).payout_each, Some(2_304_000_000));
        assert_eq!(at(h + 2 * 2880 - 1).payout_each, Some(2_304_000_000));
        assert_eq!(at(end).payout_each, Some(762 * 400_000));
        assert_eq!(at(end + 1).miner_subsidy, 8_000_000);
        assert!(!at(end + 1).active);
        // Every new-rule interval is counted exactly once. The old partial
        // day is not folded into the first new daily record.
        let issued: u128 = (h..=end)
            .map(|height| u128::from(at(height).payout_each.unwrap_or(0)))
            .sum();
        let year = super::super::emission::V2_REWARD_INTERVAL_BLOCKS;
        assert_eq!(
            issued,
            u128::from(year) * (800_000 + 565_000) + u128::from(end - h + 1 - 2 * year) * 400_000
        );
    }

    #[test]
    fn fork_on_legacy_payout_height_discards_the_partial_period() {
        let h = 4320;
        let schedule = ForkSchedule::new(Some(5), V2Activation::new(h, 30)).unwrap();
        assert!(development_allocation(h, 24).unwrap().payout_due);
        for depth in 24..=32 {
            let at =
                |height| development_allocation_with_schedule(height, depth, schedule).unwrap();
            assert!(!at(h).payout_due);
            assert_eq!(at(h).payout_each, None);
            let reward = block_reward_with_schedule(h, depth, schedule);
            assert_eq!(at(h).miner_subsidy + 2 * at(h).share_each, reward);
            assert_eq!(at(h + 2879).payout_each, Some((reward / 20) * 2880));
        }
    }

    #[test]
    fn annual_reductions_start_a_new_daily_period_without_losing_accrual() {
        use super::super::emission::{V2_REWARDS_MICRONOID, V2_REWARD_INTERVAL_BLOCKS};
        let h = super::super::params::MAINNET_V2_ACTIVATION_HEIGHT;
        let schedule = ForkSchedule::new(Some(95_125), V2Activation::new(h, 30)).unwrap();
        for epoch in 1..=2 {
            let threshold = h + epoch as u64 * V2_REWARD_INTERVAL_BLOCKS;
            for depth in 24..=32 {
                let at =
                    |height| development_allocation_with_schedule(height, depth, schedule).unwrap();
                let old_share = V2_REWARDS_MICRONOID[epoch - 1] / 20;
                let new_reward = V2_REWARDS_MICRONOID[epoch];
                let new_share = new_reward / 20;
                assert_eq!(at(threshold - 1).payout_each, Some(2880 * old_share));
                assert_eq!(at(threshold).payout_each, None);
                assert_eq!(at(threshold).share_each, new_share);
                assert_eq!(at(threshold).miner_subsidy + 2 * new_share, new_reward);
                assert_eq!(at(threshold + 2879).payout_each, Some(2880 * new_share));
            }
        }
    }

    #[test]
    fn interval_changes_never_restart_or_extend_the_target_duration() {
        for interval in [1, 20, 30, 40, 86_400] {
            for h in [
                1,
                10,
                4320,
                219_177,
                DEVELOPMENT_ALLOCATION_END_HEIGHT - 1,
                DEVELOPMENT_ALLOCATION_END_HEIGHT,
                DEVELOPMENT_ALLOCATION_END_HEIGHT + 1,
                u64::MAX,
            ] {
                let schedule = ForkSchedule::new(Some(0), V2Activation::new(h, interval)).unwrap();
                let end = development_allocation_end_height_with_schedule(schedule);
                assert!(
                    schedule.ideal_elapsed(0, end)
                        <= u128::from(DEVELOPMENT_ALLOCATION_DURATION_SECONDS)
                );
                assert!(
                    schedule.ideal_elapsed(0, end + 1)
                        > u128::from(DEVELOPMENT_ALLOCATION_DURATION_SECONDS)
                );
                for height in [h, h.saturating_add(1), end, end + 1, u64::MAX] {
                    let allocation =
                        development_allocation_with_schedule(height, 24, schedule).unwrap();
                    assert_eq!(allocation.active, height > 0 && height <= end);
                    if height == h {
                        assert!(!allocation.payout_due);
                    }
                    if !allocation.active {
                        assert!(!allocation.payout_due);
                        assert_eq!(allocation.payout_each, None);
                        assert_eq!(allocation.share_each, 0);
                    }
                }
            }
        }
        let inexact = ForkSchedule::new(Some(5), V2Activation::new(10, 37)).unwrap();
        assert_eq!(
            development_allocation_with_schedule(10, 24, inexact),
            Err(DevelopmentAllocationError::InexactInterval)
        );
    }
}
