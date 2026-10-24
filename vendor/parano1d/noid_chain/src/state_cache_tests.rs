// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

use super::*;
use std::time::Instant;

fn assert_streamed_root(state: &ChainState) {
    let mut reference = ExactSegmentRootCache::empty(state.state.log_slots());
    for id in state.state.active_segment_ids() {
        assert!(!state.state.is_evicted(id));
        reference.set_segment_root(
            id,
            exact_segment_root_from_columns(
                state.state.effective_log_segment_size(),
                state.state.try_get_segment_columns(id).unwrap(),
            ),
        );
    }
    assert_eq!(state.cached_state_root(), reference.root());
}

#[test]
fn incremental_roots_frontiers_and_previews_match_uncached_reference() {
    let slots: Vec<_> = (0..256u32)
        .filter(|i| i % 3 != 0)
        .map(|i| (i, benchmark_slot(u64::from(i) + 1)))
        .collect();
    let mut cached = ChainState::from_sparse_utxos(8, &slots, 100_000).unwrap();
    let mut reference = cached.clone();
    reference.state.set_exact_cache_budget(0);
    let mut rng = 0x826fc428abu64;
    for round in 0..32u64 {
        let updates: Vec<_> = (0..9)
            .map(|i| {
                rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1);
                (
                    (rng >> 32) as u32 % 256,
                    if i % 3 == 0 {
                        SlotValue::EMPTY
                    } else {
                        benchmark_slot(500 + round * 10 + i)
                    },
                )
            })
            .collect();
        let before = cached.cached_state_root();
        let predicted = cached
            .exact_utxo_root_after_slot_updates(8, &updates)
            .unwrap();
        assert_eq!(
            predicted,
            reference
                .exact_utxo_root_after_slot_updates(8, &updates)
                .unwrap()
        );
        assert_eq!(cached.cached_state_root(), before);
        cached.state.apply_delta_unrooted(&updates).unwrap();
        reference.state.apply_delta_unrooted(&updates).unwrap();
        assert_eq!(cached.try_state_root().unwrap(), predicted);
        assert_eq!(reference.try_state_root().unwrap(), predicted);
        let mut touched: Vec<_> = updates.iter().map(|&(index, _)| index).collect();
        touched.sort_unstable();
        touched.dedup();
        assert_eq!(
            cached.exact_frontier_siblings(&touched, 8).unwrap(),
            reference.exact_frontier_siblings(&touched, 8).unwrap()
        );
        assert_streamed_root(&cached);
    }
    let before = cached.cached_state_root();
    assert!(cached
        .exact_utxo_root_after_slot_updates(8, &[(256, benchmark_slot(1))])
        .is_err());
    assert_eq!(cached.cached_state_root(), before);
}

#[test]
fn cloned_trees_are_isolated_and_empty_segments_release_the_cache() {
    let mut state =
        ChainState::from_sparse_utxos(8, &[(7, benchmark_slot(1)), (200, benchmark_slot(2))], 100)
            .unwrap();
    let original = state.clone();
    assert!(state.state.exact_cache_bytes() > 0);
    state
        .state
        .apply_delta_unrooted(&[(7, benchmark_slot(3))])
        .unwrap();
    state.try_state_root().unwrap();
    assert_ne!(state.cached_state_root(), original.cached_state_root());
    assert_streamed_root(&state);
    assert_streamed_root(&original);
    state
        .state
        .apply_delta_unrooted(&[(7, SlotValue::EMPTY), (200, SlotValue::EMPTY)])
        .unwrap();
    assert_eq!(state.try_state_root().unwrap(), zero_slot_roots(8)[8]);
    assert_eq!(state.state.exact_cache_bytes(), 0);
    assert_eq!(state.state.materialized_segment_ids().count(), 0);
    state
        .state
        .apply_delta_unrooted(&[(7, benchmark_slot(4))])
        .unwrap();
    state.try_state_root().unwrap();
    assert_streamed_root(&state);
    assert_streamed_root(&original);
}

#[test]
fn cache_survives_geometry_changes_without_reusing_old_subtree_shapes() {
    let mut state = ChainState::from_sparse_utxos(8, &[(7, benchmark_slot(1))], 100).unwrap();
    let original = state.cached_state_root();
    let expected = state
        .exact_utxo_root_after_slot_updates(9, &[(300, benchmark_slot(2))])
        .unwrap();
    state.expand_one();
    assert_eq!(state.state.exact_cache_bytes(), 0);
    state
        .state
        .apply_delta_unrooted(&[(300, benchmark_slot(2))])
        .unwrap();
    assert_eq!(state.try_state_root().unwrap(), expected);
    assert_streamed_root(&state);
    assert!(state.state.shrink_to_log_slots(8).is_err());
    state
        .state
        .apply_delta_unrooted(&[(300, SlotValue::EMPTY)])
        .unwrap();
    state.state.shrink_to_log_slots(8).unwrap();
    assert_eq!(state.try_state_root().unwrap(), original);
    assert_streamed_root(&state);

    let mut large = ChainState::from_sparse_utxos(16, &[(7, benchmark_slot(1))], 100).unwrap();
    let parent = large.cached_state_root();
    let resident_bytes = large.state.exact_cache_bytes();
    let expected = large
        .exact_utxo_root_after_slot_updates(17, &[(65_540, benchmark_slot(2))])
        .unwrap();
    large.expand_exact_metadata_for_replay().unwrap();
    large
        .state
        .apply_delta_unrooted(&[(65_540, benchmark_slot(2))])
        .unwrap();
    assert_eq!(large.try_state_root().unwrap(), expected);
    assert_streamed_root(&large);
    large
        .state
        .apply_delta_unrooted(&[(65_540, SlotValue::EMPTY)])
        .unwrap();
    large.state.shrink_exact_metadata_to_log_slots(16).unwrap();
    assert_eq!(large.try_state_root().unwrap(), parent);
    assert_eq!(large.state.exact_cache_bytes(), resident_bytes);
    assert_streamed_root(&large);
}

#[test]
fn bounded_cache_evicts_across_many_segments_and_authenticates_reload() {
    const BUDGET: usize = 15 * 1024 * 1024; // Two production-size entries.
    let slots: Vec<_> = (0..12u32)
        .map(|id| ((id << 16) | 7, benchmark_slot(u64::from(id) + 1)))
        .collect();
    let mut state = ChainState::from_sparse_utxos(20, &slots, 1000).unwrap();
    state.state.set_exact_cache_budget(BUDGET);
    let mut durable: BTreeMap<_, _> = (0..12u16)
        .map(|id| (id, state.state.try_get_segment_columns(id).unwrap().clone()))
        .collect();
    state.state.clear_dirty();
    state.state.evict_all_persisted_segments();
    let mut reference = ExactSegmentRootCache::empty(20);
    for (&id, columns) in &durable {
        reference.set_segment_root(id, exact_segment_root_from_columns(16, columns));
    }
    for round in 0..36 {
        let id = (round % 12) as u16;
        state
            .restore_evicted_segment(id, durable[&id].clone())
            .unwrap();
        state
            .state
            .apply_delta_unrooted(&[(
                (u32::from(id) << 16) | 7,
                benchmark_slot(100 + round as u64),
            )])
            .unwrap();
        state.try_state_root().unwrap();
        let columns = state.state.try_get_segment_columns(id).unwrap().clone();
        reference.set_segment_root(id, exact_segment_root_from_columns(16, &columns));
        durable.insert(id, columns);
        state.state.clear_dirty();
        state.state.evict_cold_persisted_segments();
        assert_eq!(state.cached_state_root(), reference.root());
        assert!(state.state.exact_cache_bytes() <= BUDGET);
        assert!(state.state.materialized_segment_ids().count() <= 2);
        assert!(!state.state.is_evicted(id));
    }
    let root = state.cached_state_root();
    assert!(state.state.is_evicted(0));
    let bytes = state.state.exact_cache_bytes();
    let mut damaged = durable[&0].clone();
    damaged.values[7] = noid_core::Block128::from(999u64);
    assert!(matches!(
        state.restore_evicted_segment(0, damaged),
        Err(ExactStateReadError::SegmentRootMismatch { seg_id: 0 })
    ));
    let mut truncated = durable[&0].clone();
    truncated.owners_hi.pop();
    assert!(state.restore_evicted_segment(0, truncated).is_err());
    assert!(state.state.is_evicted(0));
    assert_eq!(state.state.exact_cache_bytes(), bytes);
    assert_eq!(state.cached_state_root(), root);
    state
        .restore_evicted_segment(0, durable[&0].clone())
        .unwrap();
    let snapshot = state.durable_metadata_clone().unwrap();
    assert_eq!(snapshot.state.exact_cache_bytes(), 0);
    assert_eq!(snapshot.state.materialized_segment_ids().count(), 0);
    assert_eq!(snapshot.cached_state_root(), root);
}

/// Run in release mode with a fixed CPU affinity. Includes authenticated cold
/// loads and exact root updates, but not disk I/O, proof verification or PoW.
#[test]
#[ignore = "manual state-cache performance measurement"]
fn bench_exact_state_cache_cycles() {
    for (name, segments, live_per_segment, touched, rounds, changes) in [
        ("dense_one", 1usize, 57_000usize, 1usize, 6usize, 2usize),
        ("dense_25", 1, 57_000, 1, 6, 50),
        ("distributed_eight", 8, 7_125, 8, 4, 2),
        ("distributed_sixteen", 16, 3_562, 16, 4, 2),
        ("churn_thirty_two", 32, 128, 1, 40, 2),
    ] {
        let slots: Vec<_> = (0..segments)
            .flat_map(|segment| {
                (0..live_per_segment).map(move |local| {
                    let index = ((segment as u32) << LOG_SEGMENT_SIZE) | local as u32;
                    (index, benchmark_slot(u64::from(index) + 1))
                })
            })
            .collect();
        let mut state = ChainState::from_sparse_utxos(24, &slots, u32::MAX as u64).unwrap();
        let mut durable: BTreeMap<_, _> = (0..segments)
            .map(|id| {
                (
                    id as u16,
                    state
                        .state
                        .try_get_segment_columns(id as u16)
                        .unwrap()
                        .clone(),
                )
            })
            .collect();
        state.state.clear_dirty();
        state.state.evict_all_persisted_segments();
        let mut loads = Vec::new();
        let mut updates = Vec::new();
        for round in 0..rounds {
            let ids: Vec<_> = (0..touched)
                .map(|offset| ((round * touched + offset) % segments) as u16)
                .collect();
            let started = Instant::now();
            for &id in &ids {
                if state.state.is_evicted(id) {
                    state
                        .restore_evicted_segment(id, durable[&id].clone())
                        .unwrap();
                }
            }
            loads.push(started.elapsed().as_secs_f64() * 1000.0);
            let deltas: Vec<_> = ids
                .iter()
                .flat_map(|&id| {
                    (0..changes).map(move |local| {
                        let index = (u32::from(id) << LOG_SEGMENT_SIZE) | local as u32;
                        (
                            index,
                            benchmark_slot((round as u64 + 2) * 10_000_000 + u64::from(index)),
                        )
                    })
                })
                .collect();
            let started = Instant::now();
            state.state.apply_delta_unrooted(&deltas).unwrap();
            state.try_state_root().unwrap();
            updates.push(started.elapsed().as_secs_f64() * 1000.0);
            for id in ids {
                durable.insert(id, state.state.try_get_segment_columns(id).unwrap().clone());
            }
            state.state.clear_dirty();
            benchmark_commit_boundary(&mut state);
        }
        let mut reference = ExactSegmentRootCache::empty(24);
        for (&id, columns) in &durable {
            reference.set_segment_root(
                id,
                exact_segment_root_from_columns(LOG_SEGMENT_SIZE, columns),
            );
        }
        assert_eq!(state.cached_state_root(), reference.root());
        let root: String = reference
            .root()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        println!("STATE_CACHE_BENCH name={name} rounds={rounds} load_ms={loads:?} update_ms={updates:?} root={root}");
    }
}

fn benchmark_slot(id: u64) -> SlotValue {
    SlotValue::with_owner_fields(
        10,
        id,
        [
            noid_core::Block128::from(3u64),
            noid_core::Block128::from(5u64),
        ],
    )
}

fn benchmark_commit_boundary(state: &mut ChainState) {
    state.state.evict_cold_persisted_segments();
}
