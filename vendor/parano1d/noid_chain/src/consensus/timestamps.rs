// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Timestamp validation rules.
//!
//! A block's timestamp must satisfy two constraints:
//!
//! 1. **Median-time-past (MTP)**: `timestamp > median(last 11 block timestamps)`.
//!    Prevents miners from moving the clock backwards.
//!
//! 2. **Future drift cap**: `timestamp <= local_time + MAX_FUTURE_DRIFT`.
//!    Prevents miners from claiming far-future timestamps to game difficulty.

use crate::consensus::params::{MAX_FUTURE_DRIFT, MEDIAN_TIME_BLOCKS};
use crate::consensus::ConsensusError;

/// Validate the timestamp of a new block.
///
/// # Arguments
///
/// * `block_ts`        — The timestamp from the candidate block header (Unix seconds).
/// * `prev_timestamps` — Timestamps of the `N` most recent ancestor blocks,
///   ordered oldest-first (index 0 = oldest). Up to
///   `MEDIAN_TIME_BLOCKS = 11` entries; fewer at genesis.
/// * `local_time`      — Current wall-clock time at the validating node (Unix seconds).
pub fn validate_timestamp(
    block_ts: u64,
    prev_timestamps: &[u64],
    local_time: u64,
) -> Result<(), ConsensusError> {
    validate_median_time_past(block_ts, prev_timestamps)?;
    validate_future_drift(block_ts, local_time)?;
    Ok(())
}

/// Validate only the timeless consensus timestamp rule.
///
/// This is the timestamp predicate that can be proven for historical recursive
/// checkpoints. It deliberately excludes the local wall-clock future-drift
/// admission policy.
pub fn validate_median_time_past(
    block_ts: u64,
    prev_timestamps: &[u64],
) -> Result<(), ConsensusError> {
    let mtp = median_time_past(prev_timestamps);
    if block_ts <= mtp {
        return Err(ConsensusError::BadTimestamp);
    }
    Ok(())
}

/// Validate the local node admission policy for far-future timestamps.
pub fn validate_future_drift(block_ts: u64, local_time: u64) -> Result<(), ConsensusError> {
    if block_ts > local_time.saturating_add(MAX_FUTURE_DRIFT) {
        return Err(ConsensusError::BadTimestamp);
    }
    Ok(())
}

/// Compute the median-time-past from up to `MEDIAN_TIME_BLOCKS` recent timestamps.
///
/// Returns 0 if no previous timestamps are provided (genesis edge case).
pub fn median_time_past(prev_timestamps: &[u64]) -> u64 {
    if prev_timestamps.is_empty() {
        return 0;
    }
    let count = prev_timestamps.len().min(MEDIAN_TIME_BLOCKS);
    let mut recent: Vec<u64> = prev_timestamps[prev_timestamps.len() - count..].to_vec();
    recent.sort_unstable();
    recent[count / 2]
}

/// Compute the median of a slice of `u64` values.
///
/// Used by bounded rolling policies that need an integer upper median.
///
/// Returns `0` for an empty slice (matches the behaviour of `median_time_past`).
pub fn median_u64(values: &[u64]) -> u64 {
    if values.is_empty() {
        return 0;
    }
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    sorted[sorted.len() / 2]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consensus::params::BLOCK_TIME;

    fn timestamps(n: usize) -> Vec<u64> {
        (0..n as u64).map(|i| 1_000_000 + i * BLOCK_TIME).collect()
    }

    #[test]
    fn valid_timestamp_accepts() {
        let prev = timestamps(11);
        let mtp = median_time_past(&prev);
        let local = prev.last().copied().unwrap() + BLOCK_TIME;
        assert!(validate_timestamp(mtp + 1, &prev, local).is_ok());
    }

    #[test]
    fn timestamp_equal_to_mtp_rejects() {
        let prev = timestamps(11);
        let mtp = median_time_past(&prev);
        let local = mtp + BLOCK_TIME * 100;
        assert_eq!(
            validate_timestamp(mtp, &prev, local),
            Err(ConsensusError::BadTimestamp)
        );
    }

    #[test]
    fn timestamp_below_mtp_rejects() {
        let prev = timestamps(11);
        let mtp = median_time_past(&prev);
        let local = mtp + BLOCK_TIME * 100;
        assert_eq!(
            validate_timestamp(mtp - 1, &prev, local),
            Err(ConsensusError::BadTimestamp)
        );
    }

    #[test]
    fn future_drift_exactly_at_limit_accepts() {
        let prev = timestamps(5);
        let local = 2_000_000u64;
        let ts = local + MAX_FUTURE_DRIFT;
        assert!(validate_timestamp(ts, &prev, local).is_ok());
    }

    #[test]
    fn future_drift_one_over_limit_rejects() {
        let prev = timestamps(5);
        let local = 2_000_000u64;
        let ts = local + MAX_FUTURE_DRIFT + 1;
        assert_eq!(
            validate_timestamp(ts, &prev, local),
            Err(ConsensusError::BadTimestamp)
        );
    }

    #[test]
    fn median_of_11_sorted_picks_middle() {
        // Median of 11 elements = element at index 5 (0-based).
        let ts: Vec<u64> = (0..11).map(|i| 100 + i * 60).collect();
        let mtp = median_time_past(&ts);
        assert_eq!(mtp, ts[5]);
    }

    #[test]
    fn median_of_fewer_than_11() {
        let ts = vec![100u64, 200, 300, 400, 500];
        let mtp = median_time_past(&ts);
        assert_eq!(mtp, 300); // median of 5 = index 2
    }

    #[test]
    fn genesis_empty_timestamps() {
        // Genesis block has no previous timestamps.
        let mtp = median_time_past(&[]);
        assert_eq!(mtp, 0);
        // Any positive timestamp > 0 should be valid at genesis.
        assert!(validate_timestamp(1, &[], 1_000_000).is_ok());
    }

    #[test]
    fn median_u64_empty_returns_zero() {
        assert_eq!(median_u64(&[]), 0);
    }

    #[test]
    fn median_u64_odd_count() {
        assert_eq!(median_u64(&[10, 30, 20]), 20);
    }

    #[test]
    fn median_u64_even_count_upper_middle() {
        // With even count, picks the upper-middle element (index len/2).
        assert_eq!(median_u64(&[10, 20, 30, 40]), 30);
    }

    #[test]
    fn median_u64_single_element() {
        assert_eq!(median_u64(&[42]), 42);
    }

    #[test]
    fn median_u64_all_same() {
        assert_eq!(median_u64(&[7, 7, 7, 7, 7]), 7);
    }

    #[test]
    fn median_u64_large_values() {
        assert_eq!(median_u64(&[u64::MAX, 0, u64::MAX / 2]), u64::MAX / 2);
    }

    #[test]
    fn uses_only_last_11_timestamps() {
        // Provide 20 timestamps; only last 11 matter for MTP.
        let ts: Vec<u64> = (0..20u64).map(|i| 1000 + i * 60).collect();
        let mtp_20 = median_time_past(&ts);
        let last_11: Vec<u64> = ts[9..].to_vec();
        let mtp_11 = median_time_past(&last_11);
        assert_eq!(mtp_20, mtp_11);
    }
}
