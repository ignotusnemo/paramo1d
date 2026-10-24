// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Candidate-height rule selection. A schedule neither authenticates a proof
//! bank nor selects its capacity. Isolated callers may supply a local schedule.

use super::params::{BLOCK_TIME, V1_1_ACTIVATION_HEIGHT, V2_ACTIVATION_HEIGHT, V2_BLOCK_TIME};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProtocolVersion {
    V1,
    V1_1,
    V2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V2Activation {
    height: u64,
    block_time: u64,
}

impl V2Activation {
    /// V2 begins with a successor to an authenticated legacy block.
    pub const fn new(height: u64, block_time: u64) -> Option<Self> {
        if height == 0 || block_time == 0 {
            None
        } else {
            Some(Self { height, block_time })
        }
    }

    pub const fn height(self) -> u64 {
        self.height
    }

    pub const fn block_time(self) -> u64 {
        self.block_time
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForkSchedule {
    v1_1: Option<u64>,
    v2: Option<V2Activation>,
}

impl ForkSchedule {
    pub const fn new(v1_1: Option<u64>, v2: Option<V2Activation>) -> Option<Self> {
        match (v1_1, v2) {
            (Some(first), Some(second)) if second.height >= first => Some(Self { v1_1, v2 }),
            (_, None) => Some(Self { v1_1, v2 }),
            _ => None,
        }
    }

    pub const fn v1_1_height(self) -> Option<u64> {
        self.v1_1
    }

    pub const fn v2(self) -> Option<V2Activation> {
        self.v2
    }

    /// Re-evaluate for each candidate, including when a reorg crosses a fork.
    pub const fn version(self, height: u64) -> ProtocolVersion {
        if matches!(self.v2, Some(at) if height >= at.height) {
            ProtocolVersion::V2
        } else if matches!(self.v1_1, Some(at) if height >= at) {
            ProtocolVersion::V1_1
        } else {
            ProtocolVersion::V1
        }
    }

    pub const fn block_time(self, height: u64) -> u64 {
        match self.v2 {
            Some(at) if height >= at.height => at.block_time,
            _ => BLOCK_TIME,
        }
    }

    /// Target elapsed seconds for (anchor, child], counting the fork block's
    /// interval under the new rules. This remains exact for all u64 heights.
    /// The ASERT caller must choose its versioned arithmetic separately.
    pub const fn ideal_elapsed(self, anchor: u64, child: u64) -> u128 {
        let count = child.saturating_sub(anchor);
        match self.v2 {
            Some(at) if child >= at.height => {
                let last_old = at.height - 1;
                let start = if anchor > last_old { anchor } else { last_old };
                let new_count = child.saturating_sub(start);
                (count - new_count) as u128 * BLOCK_TIME as u128
                    + new_count as u128 * at.block_time as u128
            }
            _ => count as u128 * BLOCK_TIME as u128,
        }
    }
}

/// Preserve the existing v1.1 activation and add the scheduled v2 successor.
pub const ACTIVE_SCHEDULE: ForkSchedule = ForkSchedule {
    v1_1: V1_1_ACTIVATION_HEIGHT,
    v2: match V2_ACTIVATION_HEIGHT {
        Some(height) => V2Activation::new(height, V2_BLOCK_TIME),
        None => None,
    },
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn candidate_height_selects_both_forks_and_reverses_on_reorg() {
        let schedule = ForkSchedule::new(Some(5), V2Activation::new(10, 30)).unwrap();
        for (height, version) in [
            (0, ProtocolVersion::V1),
            (4, ProtocolVersion::V1),
            (5, ProtocolVersion::V1_1),
            (9, ProtocolVersion::V1_1),
            (10, ProtocolVersion::V2),
            (11, ProtocolVersion::V2),
            (9, ProtocolVersion::V1_1),
            (4, ProtocolVersion::V1),
        ] {
            assert_eq!(schedule.version(height), version);
        }
    }

    #[test]
    fn active_schedule_preserves_legacy_rules_and_selects_v2_at_its_height() {
        assert_eq!(
            ACTIVE_SCHEDULE.v2().map(V2Activation::height),
            V2_ACTIVATION_HEIGHT
        );
        let activation = V1_1_ACTIVATION_HEIGHT.unwrap();
        for height in [0, activation - 1, activation, activation + 1, u64::MAX] {
            assert_eq!(
                ACTIVE_SCHEDULE.version(height) != ProtocolVersion::V1,
                super::super::params::v1_1_active_with(height, V1_1_ACTIVATION_HEIGHT)
            );
            assert_eq!(
                ACTIVE_SCHEDULE.block_time(height),
                if matches!(V2_ACTIVATION_HEIGHT, Some(at) if height >= at) {
                    V2_BLOCK_TIME
                } else {
                    BLOCK_TIME
                }
            );
        }
        if let Some(at) = ACTIVE_SCHEDULE.v2() {
            assert_eq!(
                ACTIVE_SCHEDULE.version(at.height() - 1),
                ProtocolVersion::V1_1
            );
            assert_eq!(ACTIVE_SCHEDULE.version(at.height()), ProtocolVersion::V2);
            assert_eq!(
                ACTIVE_SCHEDULE.ideal_elapsed(at.height() - 2, at.height()),
                50
            );
        }
    }

    #[test]
    fn invalid_upgrade_order_genesis_and_zero_interval_reject() {
        assert!(V2Activation::new(0, 30).is_none());
        assert!(V2Activation::new(10, 0).is_none());
        assert!(ForkSchedule::new(None, V2Activation::new(10, 30)).is_none());
        assert!(ForkSchedule::new(Some(11), V2Activation::new(10, 30)).is_none());
        assert!(ForkSchedule::new(Some(10), V2Activation::new(10, 30)).is_some());
        assert!(ForkSchedule::new(None, None).is_some());
    }

    #[test]
    fn mixed_intervals_match_an_independent_per_height_sum() {
        for interval in [27, 30, 37] {
            let schedule = ForkSchedule::new(Some(5), V2Activation::new(10, interval)).unwrap();
            for anchor in 0..15 {
                for child in 0..20 {
                    let expected: u128 = ((anchor + 1)..=child)
                        .map(|h| if h < 10 { 20 } else { interval } as u128)
                        .sum();
                    assert_eq!(schedule.ideal_elapsed(anchor, child), expected);
                }
            }
            assert_eq!(
                schedule.ideal_elapsed(0, u64::MAX),
                9 * 20 + (u64::MAX as u128 - 9) * interval as u128
            );
        }
        let schedule = ForkSchedule::new(Some(0), V2Activation::new(1, u64::MAX)).unwrap();
        assert_eq!(
            schedule.ideal_elapsed(0, u64::MAX),
            (u64::MAX as u128).pow(2)
        );
    }
}
