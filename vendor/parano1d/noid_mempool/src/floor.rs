// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Dynamic fee floor: tracks recent admitted-tx fees and raises the minimum.
//!
//! The floor is computed from recent admitted fees:
//!   `floor = max(MIN_FEE_BASE, median(last N fees) × 0.9)`
//!
//! Before v1.1 this floor applies at any occupancy and resets on emptying.
//! From v1.1 it applies only after count or retained bytes reach 80% of their
//! existing limit. Both must fall strictly below 50% to reset the floor.

use std::collections::VecDeque;

use noid_chain::consensus::params::MIN_FEE_BASE;

/// Tracks recently admitted fees and computes the dynamic floor.
pub struct FeeFloor {
    /// Ring buffer of the last `capacity` admitted fees.
    recent: VecDeque<u64>,
    /// Maximum entries before oldest is dropped.
    capacity: usize,
    /// Current computed floor (cached, updated on each push).
    current: u64,
    /// None preserves legacy policy; Some holds the v1.1 pressure latch.
    pressure_active: Option<bool>,
}

impl FeeFloor {
    pub fn new(window_size: usize) -> Self {
        Self {
            recent: VecDeque::with_capacity(window_size),
            capacity: window_size.max(1),
            current: MIN_FEE_BASE,
            pressure_active: None,
        }
    }

    /// Record a newly admitted transaction's fee and recompute the floor.
    pub fn record(&mut self, fee: u64) {
        if self.recent.len() >= self.capacity {
            self.recent.pop_front();
        }
        self.recent.push_back(fee);
        self.current = self.compute();
    }

    /// Return the current dynamic fee floor (μNOID).
    #[inline]
    pub fn current(&self) -> u64 {
        if self.pressure_active == Some(false) {
            MIN_FEE_BASE
        } else {
            self.current
        }
    }

    /// Refresh local policy from already-maintained counters, without scanning
    /// entries. The caller holds the same lock used for admission and quotes.
    pub(crate) fn update_pressure(
        &mut self,
        v1_1_active: bool,
        count: usize,
        max_count: usize,
        bytes: usize,
        max_bytes: usize,
    ) {
        if !v1_1_active {
            self.pressure_active = None;
            if count == 0 {
                self.reset();
            }
            return;
        }

        // Crossing activation starts unlatched; legacy high fees alone cannot
        // enable the new policy while occupancy is in the 50%-80% band.
        self.pressure_active.get_or_insert(false);
        // Widen before multiplication so exact integer boundaries cannot wrap.
        if count == 0
            || ((count as u128) * 2 < max_count as u128 && (bytes as u128) * 2 < max_bytes as u128)
        {
            self.reset();
        } else if (count as u128) * 5 >= (max_count as u128) * 4
            || (bytes as u128) * 5 >= (max_bytes as u128) * 4
        {
            self.pressure_active = Some(true);
        }
    }

    /// Forget prior fees after an empty pool or a v1.1 low-water reset.
    ///
    /// A historical admission must not leave an idle node enforcing a higher
    /// relay policy forever. Once no transaction remains, there is no live
    /// congestion signal and the next admission starts from the base floor.
    pub fn reset(&mut self) {
        self.recent.clear();
        self.current = MIN_FEE_BASE;
        if let Some(active) = &mut self.pressure_active {
            *active = false;
        }
    }

    fn compute(&self) -> u64 {
        if self.recent.is_empty() {
            return MIN_FEE_BASE;
        }
        let median =
            noid_chain::consensus::median_u64(&self.recent.iter().copied().collect::<Vec<_>>());
        // Floor = 90% of median, never below MIN_FEE_BASE.
        let floor_90 = median.saturating_mul(9) / 10;
        floor_90.max(MIN_FEE_BASE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn floor_starts_at_min_fee() {
        let f = FeeFloor::new(50);
        assert_eq!(f.current(), MIN_FEE_BASE);
    }

    #[test]
    fn floor_rises_with_high_fees() {
        let mut f = FeeFloor::new(10);
        for _ in 0..10 {
            f.record(100_000); // 0.1 NOID
        }
        assert!(f.current() > MIN_FEE_BASE, "floor must rise above minimum");
    }

    #[test]
    fn floor_never_below_min_fee() {
        let mut f = FeeFloor::new(10);
        for _ in 0..10 {
            f.record(0);
        }
        assert_eq!(f.current(), MIN_FEE_BASE);
    }

    #[test]
    fn floor_window_is_bounded() {
        let mut f = FeeFloor::new(3);
        f.record(1_000_000);
        f.record(1_000_000);
        f.record(1_000_000);
        let high = f.current();
        // Push many low fees to displace high ones.
        for _ in 0..10 {
            f.record(MIN_FEE_BASE);
        }
        assert!(f.current() < high, "old high fees should be replaced");
    }

    #[test]
    fn floor_resets_after_congestion_clears() {
        let mut f = FeeFloor::new(10);
        f.record(100_000);
        assert!(f.current() > MIN_FEE_BASE);

        f.reset();

        assert_eq!(f.current(), MIN_FEE_BASE);
        f.record(MIN_FEE_BASE);
        assert_eq!(f.current(), MIN_FEE_BASE);
    }

    #[test]
    fn v1_1_suppresses_expensive_admissions_until_pressure_reaches_eighty_percent() {
        let mut floor = FeeFloor::new(50);
        floor.update_pressure(true, 0, 10, 0, 100);
        for count in 1..=7 {
            floor.record(100_000);
            floor.update_pressure(true, count, 10, 0, 100);
            assert_eq!(floor.current(), MIN_FEE_BASE);
        }
        floor.record(100_000);
        floor.update_pressure(true, 8, 10, 0, 100);
        assert_eq!(floor.current(), 90_000);
    }

    #[test]
    fn either_pressure_dimension_enables_at_the_exact_integer_boundary() {
        for limit in [1usize, 2, 3, 5, 7, 10, 1024, 384 * 1024 * 1024, usize::MAX] {
            let high = limit - limit / 5; // ceil(4 * limit / 5), without overflow.
            for count_dimension in [false, true] {
                let mut floor = FeeFloor::new(50);
                let update = |floor: &mut FeeFloor, used| {
                    if count_dimension {
                        floor.update_pressure(true, used, limit, 0, usize::MAX);
                    } else {
                        floor.update_pressure(true, 1, usize::MAX, used, limit);
                    }
                };
                floor.record(100_000);
                update(&mut floor, high - 1);
                assert_eq!(floor.current(), MIN_FEE_BASE, "limit={limit}");
                floor.record(100_000);
                update(&mut floor, high);
                assert_eq!(floor.current(), 90_000, "limit={limit}");
            }
        }
    }

    #[test]
    fn hysteresis_requires_both_dimensions_strictly_below_half() {
        let mut floor = FeeFloor::new(50);
        floor.record(100_000);
        floor.update_pressure(true, 8, 10, 0, 100);
        for (count, bytes) in [(7, 0), (5, 0), (4, 50), (1, 79)] {
            floor.update_pressure(true, count, 10, bytes, 100);
            assert_eq!(floor.current(), 90_000);
        }
        floor.update_pressure(true, 4, 10, 49, 100);
        assert_eq!(floor.current(), MIN_FEE_BASE);
        assert!(
            floor.recent.is_empty(),
            "low-water reset must discard old fees"
        );

        floor.record(20_000);
        floor.update_pressure(true, 7, 10, 79, 100);
        assert_eq!(floor.current(), MIN_FEE_BASE);
        floor.update_pressure(true, 7, 10, 80, 100);
        assert_eq!(floor.current(), 18_000, "old high fees must not return");
    }

    #[test]
    fn half_boundary_is_exact_for_odd_and_large_limits() {
        for limit in [1usize, 3, 5, 7, 1025, usize::MAX] {
            let half_ceil = limit.div_ceil(2);
            let mut floor = FeeFloor::new(50);
            floor.record(100_000);
            floor.update_pressure(true, limit, limit, 0, usize::MAX);
            floor.update_pressure(true, half_ceil, limit, 0, usize::MAX);
            assert_eq!(floor.current(), 90_000);
            floor.update_pressure(true, half_ceil - 1, limit, 0, usize::MAX);
            assert_eq!(floor.current(), MIN_FEE_BASE);
        }
    }

    #[test]
    fn activation_reorg_and_recross_do_not_inherit_the_wrong_policy_latch() {
        let mut floor = FeeFloor::new(50);
        floor.record(100_000);
        floor.update_pressure(false, 6, 10, 0, 100);
        assert_eq!(floor.current(), 90_000);
        floor.update_pressure(true, 6, 10, 0, 100);
        assert_eq!(floor.current(), MIN_FEE_BASE);
        floor.update_pressure(true, 8, 10, 0, 100);
        assert_eq!(floor.current(), 90_000);
        floor.update_pressure(false, 6, 10, 0, 100);
        assert_eq!(floor.current(), 90_000);
        floor.update_pressure(true, 6, 10, 0, 100);
        assert_eq!(floor.current(), MIN_FEE_BASE);
        floor.update_pressure(true, 8, 10, 0, 100);
        assert_eq!(floor.current(), 90_000);
        floor.update_pressure(true, 0, 10, 0, 100);
        assert_eq!(floor.current(), MIN_FEE_BASE);
        assert!(floor.recent.is_empty());
    }

    #[test]
    fn legacy_partial_drain_is_unchanged_and_zero_limits_do_not_panic() {
        let mut floor = FeeFloor::new(50);
        floor.record(100_000);
        floor.update_pressure(false, 1, 10, 0, 100);
        assert_eq!(floor.current(), 90_000);
        floor.update_pressure(false, 0, 10, 0, 100);
        assert_eq!(floor.current(), MIN_FEE_BASE);
        floor.record(100_000);
        floor.update_pressure(true, 0, 0, 0, 0);
        assert_eq!(floor.current(), MIN_FEE_BASE);
    }
}
