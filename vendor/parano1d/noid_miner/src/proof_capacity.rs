// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Two-class miner capacity controller.
//!
//! A proof class has essentially fixed work regardless of how many of its
//! physical page slots are live. Capacity decisions therefore use complete
//! B25/B255 preparation timings, never `milliseconds / populated pages`.

use std::time::Duration;

use noid_chain::consensus::paged_spend::BlockProofClass;

const EWMA_PREVIOUS_WEIGHT: f64 = 0.75;

/// Miner-local capacity evidence for the two launch proof classes.
///
/// Every session starts at B25. The first completed ordinary B25 preparation
/// determines its capacity ceiling for that session, predicting B255 cost from
/// the `m22 -> m24` expansion. Later timings remain telemetry only. Template
/// construction independently caps this ceiling at B25 before activation.
#[derive(Clone, Debug, Default)]
pub struct AdaptiveProofCapacity {
    b255_allowed: Option<bool>,
    b25_prepare_ms_ewma: Option<f64>,
    b255_prepare_ms_ewma: Option<f64>,
}

impl AdaptiveProofCapacity {
    /// Effective page-position budget for the next template: 25 or 255.
    /// A mandatory system payout consumes one position inside that budget.
    pub fn page_limit(&self) -> usize {
        // Local acceptance fixtures must be able to exercise B255 even on a
        // machine which correctly elects B25 in normal operation. This branch
        // is compiled away in the public-network profile. It changes only the
        // producer's chosen page budget, never block admission or proof rules.
        if noid_chain::consensus::params::ISOLATED_V1_1_TESTNET
            && std::env::var("NOID_ISOLATED_FORCE_B255").as_deref() == Ok("1")
        {
            return BlockProofClass::B255.page_capacity();
        }
        if self.b255_allowed == Some(true) {
            BlockProofClass::B255.page_capacity()
        } else {
            BlockProofClass::B25.page_capacity()
        }
    }

    /// Record one complete nonce-independent HistoryStep preparation.
    pub fn observe_preparation(&mut self, class: BlockProofClass, elapsed: Duration) {
        if class == BlockProofClass::B25 && self.b255_allowed.is_none() {
            self.b255_allowed = Some(
                elapsed
                    .checked_mul(class_work_ratio())
                    .is_some_and(|predicted| predicted <= target_prepare_time()),
            );
        }
        let sample_ms = elapsed.as_secs_f64() * 1_000.0;
        let ewma = match class {
            BlockProofClass::B25 => &mut self.b25_prepare_ms_ewma,
            BlockProofClass::B255 => &mut self.b255_prepare_ms_ewma,
        };
        *ewma = Some(match *ewma {
            Some(previous) => {
                previous * EWMA_PREVIOUS_WEIGHT + sample_ms * (1.0 - EWMA_PREVIOUS_WEIGHT)
            }
            None => sample_ms,
        });
    }

    /// Current complete-class preparation EWMA in milliseconds.
    pub fn prepare_ms_ewma(&self, class: BlockProofClass) -> Option<f64> {
        match class {
            BlockProofClass::B25 => self.b25_prepare_ms_ewma,
            BlockProofClass::B255 => self.b255_prepare_ms_ewma,
        }
    }
}

#[inline]
fn target_prepare_time() -> Duration {
    Duration::from_secs(noid_chain::consensus::params::BLOCK_TIME)
}

#[inline]
fn class_work_ratio() -> u32 {
    let delta = BlockProofClass::B255.outer_m() - BlockProofClass::B25.outer_m();
    1u32 << delta
}

#[cfg(test)]
mod tests {
    use super::*;

    fn millis(value: u64) -> Duration {
        Duration::from_millis(value)
    }

    #[test]
    fn starts_at_b25_and_has_no_intermediate_limits() {
        let mut capacity = AdaptiveProofCapacity::default();
        assert_eq!(capacity.page_limit(), 25);

        let predicted_b255_boundary =
            (target_prepare_time() / class_work_ratio()).as_millis() as u64;
        capacity.observe_preparation(BlockProofClass::B25, millis(predicted_b255_boundary + 1));
        assert_eq!(capacity.page_limit(), 25);

        let mut exact_boundary = AdaptiveProofCapacity::default();
        exact_boundary.observe_preparation(BlockProofClass::B25, millis(predicted_b255_boundary));
        assert_eq!(exact_boundary.page_limit(), 255);
        assert!(matches!(capacity.page_limit(), 25 | 255));
    }

    #[test]
    fn first_fast_b25_keeps_permission_despite_later_slow_samples() {
        let mut capacity = AdaptiveProofCapacity::default();
        capacity.observe_preparation(BlockProofClass::B25, millis(3_000));
        assert_eq!(capacity.page_limit(), 255);

        capacity.observe_preparation(BlockProofClass::B255, millis(60_000));
        assert_eq!(capacity.page_limit(), 255);

        // Neither class's telemetry changes the first-sample decision.
        capacity.observe_preparation(BlockProofClass::B25, millis(20_000));
        assert_eq!(capacity.page_limit(), 255);
        assert_eq!(
            capacity.prepare_ms_ewma(BlockProofClass::B255),
            Some(60_000.0)
        );
    }

    #[test]
    fn first_slow_b25_keeps_small_ceiling_despite_later_fast_samples() {
        let mut capacity = AdaptiveProofCapacity::default();
        capacity.observe_preparation(BlockProofClass::B25, millis(5_001));
        assert_eq!(capacity.page_limit(), 25);

        capacity.observe_preparation(BlockProofClass::B255, millis(1_000));
        capacity.observe_preparation(BlockProofClass::B25, millis(1_000));
        assert_eq!(capacity.page_limit(), 25);
    }

    #[test]
    fn only_completed_b25_observations_qualify_and_restart_forgets_them() {
        let mut capacity = AdaptiveProofCapacity::default();
        capacity.observe_preparation(BlockProofClass::B255, millis(1_000));
        assert_eq!(capacity.page_limit(), 25);
        assert_eq!(capacity.b255_allowed, None);

        capacity.observe_preparation(BlockProofClass::B25, millis(4_999));
        assert_eq!(capacity.page_limit(), 255);
        assert_eq!(AdaptiveProofCapacity::default().page_limit(), 25);
    }

    #[test]
    fn permission_boundary_uses_full_duration_without_rounding_or_overflow() {
        assert_eq!(class_work_ratio(), 4);
        assert_eq!(target_prepare_time(), Duration::from_secs(20));
        let boundary = target_prepare_time() / class_work_ratio();
        for (elapsed, allowed) in [
            (boundary - Duration::from_nanos(1), true),
            (boundary, true),
            (boundary + Duration::from_nanos(1), false),
            (Duration::MAX, false),
        ] {
            let mut capacity = AdaptiveProofCapacity::default();
            capacity.observe_preparation(BlockProofClass::B25, elapsed);
            assert_eq!(capacity.b255_allowed, Some(allowed), "{elapsed:?}");
        }
    }
}
