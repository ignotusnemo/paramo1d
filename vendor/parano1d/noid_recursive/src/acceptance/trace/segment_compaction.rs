// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Fixed-shape compaction of local exact-state updates into segment updates.
//!
//! The action compactor supplies a slot-sorted live prefix and the already
//! constrained highest-differing-bit metadata for every adjacent pair.  This
//! gadget uses that metadata to prove the local-root chain inside each
//! 2^16-leaf segment, carries the first root of the segment to its last action,
//! and routes the resulting tuples through one shared Beneš network. The
//! boolean liveness tag and 16-bit segment id use one injective 17-bit key, so
//! four arbitrary root fields need only one additional routing lane. No
//! semantic lane has an independently chosen permutation.

use noid_ivc_core::field_circuit::Wire;

use super::action_compaction::strict_less_bits;
use super::action_surface::ActionRowTrace;
use super::paired_merkle_update::PAIRED_UPDATE_DEPTH;
use super::permutation_network::route_permutation_network;
use super::{flat_const, mul, pin_eq, pin_zero, range_check_bits, FieldR1csBuilder, LinExpr, F128};

const SLOT_BITS: usize = 32;
const SEGMENT_BITS: usize = SLOT_BITS - PAIRED_UPDATE_DEPTH;
const SEGMENT_KEY_BITS: usize = SEGMENT_BITS + 1;

/// One upper-tree update selected from the last touched leaf in a segment.
#[derive(Clone, Debug)]
pub struct SegmentUpdateTrace {
    pub live: LinExpr,
    pub segment_id: LinExpr,
    pub root_before: [LinExpr; 2],
    pub root_after: [LinExpr; 2],
}

#[derive(Clone, Debug)]
struct SegmentRouteTrace {
    key: LinExpr,
    root_before: [LinExpr; 2],
    root_after: [LinExpr; 2],
}

/// Strictly segment-id-sorted live-prefix handoff to the upper paired walk.
pub struct CompactedSegmentTrace {
    pub rows: Vec<SegmentUpdateTrace>,
    /// Already-constrained 16-bit little-endian segment ids aligned with
    /// `rows`; upper paired walks reuse these direction bits directly.
    pub segment_id_bits: Vec<Vec<Wire>>,
    pub source_rows: usize,
    pub sort_rows: usize,
    /// Rows allocated by the one five-lane Beneš network alone.
    pub network_rows: usize,
}

/// Derive and compact one upper update per touched 2^16-leaf segment.
///
/// `local_roots_before[i]` and `local_roots_after[i]` are the endpoints of the
/// paired 16-level walk for `actions[i]`.  Whenever two adjacent live actions
/// share a segment, the former after-root is constrained equal to the latter
/// before-root.  The returned tuple for that segment contains the first
/// before-root and the last after-root.
pub fn compact_segment_updates(
    b: &mut FieldR1csBuilder,
    actions: &[ActionRowTrace],
    slot_bits: &[Vec<Wire>],
    adjacent_msb_one_hot: &[Vec<LinExpr>],
    adjacent_both_live: &[LinExpr],
    local_roots_before: &[[LinExpr; 2]],
    local_roots_after: &[[LinExpr; 2]],
    max_segments: usize,
) -> CompactedSegmentTrace {
    assert!(!actions.is_empty());
    assert_eq!(actions.len(), slot_bits.len());
    assert_eq!(actions.len(), local_roots_before.len());
    assert_eq!(actions.len(), local_roots_after.len());
    assert_eq!(adjacent_msb_one_hot.len(), actions.len() - 1);
    assert_eq!(adjacent_both_live.len(), actions.len() - 1);
    assert!(slot_bits.iter().all(|bits| bits.len() == SLOT_BITS));
    assert!(adjacent_msb_one_hot
        .iter()
        .all(|one_hot| one_hot.len() == SLOT_BITS));
    assert!((1..=actions.len()).contains(&max_segments));

    // `same_next[i] = 1` exactly when two adjacent live sorted slots differ
    // only below bit 16.  The one-hot is already proven by the action-order
    // comparator; multiplying by its existing both-live gate suppresses the
    // live/dead boundary.
    let same_next: Vec<LinExpr> = adjacent_msb_one_hot
        .iter()
        .zip(adjacent_both_live)
        .map(|(highest, both_live)| {
            let local_difference = highest[..PAIRED_UPDATE_DEPTH]
                .iter()
                .fold(LinExpr::zero(), |sum, bit| sum.add(bit));
            mul(b, both_live, &local_difference)
        })
        .collect();

    for index in 0..same_next.len() {
        for lane in 0..2 {
            let discontinuity =
                local_roots_after[index][lane].add(&local_roots_before[index + 1][lane]);
            let gated_discontinuity = mul(b, &same_next[index], &discontinuity);
            pin_zero(b, &gated_discontinuity);
        }
    }

    // Carry the first before-root of each segment to every subsequent action
    // in that segment.  This is a selector recurrence, not host control flow.
    let mut first_before = local_roots_before[0].clone();
    let mut candidates = Vec::with_capacity(actions.len());
    for index in 0..actions.len() {
        if index > 0 {
            let same_previous = &same_next[index - 1];
            first_before = std::array::from_fn(|lane| {
                let delta = first_before[lane].add(&local_roots_before[index][lane]);
                local_roots_before[index][lane].add(&mul(b, same_previous, &delta))
            });
        }

        let next_same = same_next.get(index).cloned().unwrap_or_else(LinExpr::zero);
        let is_last = mul(b, &actions[index].live, &next_same.add_const(F128::ONE));
        let segment_id = slot_bits[index][PAIRED_UPDATE_DEPTH..]
            .iter()
            .enumerate()
            .fold(LinExpr::zero(), |sum, (bit, &wire)| {
                sum.add(&LinExpr::from_wire(wire).scale(flat_const(1u128 << bit)))
            });
        let select = |b: &mut FieldR1csBuilder, value: &LinExpr| mul(b, &is_last, value);
        candidates.push(SegmentUpdateTrace {
            live: is_last.clone(),
            segment_id: select(b, &segment_id),
            root_before: std::array::from_fn(|lane| select(b, &first_before[lane])),
            root_after: std::array::from_fn(|lane| select(b, &local_roots_after[index][lane])),
        });
    }

    let source_rows = candidates.len();
    let sort_rows = source_rows.next_power_of_two();
    candidates.resize_with(sort_rows, zero_segment_update);

    // Host routing only supplies a satisfying switch witness.  The shared
    // switch bits prove that all five semantic lanes take the same route. The
    // key is `segment_id + live * 2^16` in tower bits; because `segment_id` is
    // already derived from 16 constrained slot bits, this is an exact,
    // challenge-free injection of `(live, segment_id)` into one field lane.
    let mut output_inputs: Vec<usize> = (0..sort_rows).collect();
    output_inputs.sort_by_key(|&input| {
        let row = &candidates[input];
        let live = native_bool(&row.live, b);
        let id = if live {
            native_tower_u128(&row.segment_id, b)
        } else {
            0
        };
        (u8::from(!live), id, input)
    });
    let mut permutation = vec![usize::MAX; sort_rows];
    for (output, input) in output_inputs.into_iter().enumerate() {
        permutation[input] = output;
    }
    let network_start = b.num_wires();
    let routed = route_permutation_network(
        b,
        candidates.into_iter().map(segment_route_lanes).collect(),
        &permutation,
    )
    .into_iter()
    .map(segment_route_from_lanes)
    .collect::<Vec<_>>();
    let network_rows = b.num_wires() - network_start;

    for row in &routed[max_segments..] {
        // Every live key has tower bit 16 set and therefore cannot be zero,
        // including segment zero. This is the exact algebraic segment cap.
        pin_zero(b, &row.key);
    }

    let mut rows = Vec::with_capacity(max_segments);
    let mut id_bits = Vec::with_capacity(max_segments);
    for routed in routed.into_iter().take(max_segments) {
        let bits = range_check_bits(b, &routed.key, SEGMENT_KEY_BITS);
        let live = LinExpr::from_wire(bits[SEGMENT_BITS]);
        let segment_id = bits[..SEGMENT_BITS]
            .iter()
            .enumerate()
            .fold(LinExpr::zero(), |sum, (bit, &wire)| {
                sum.add(&LinExpr::from_wire(wire).scale(flat_const(1u128 << bit)))
            });
        id_bits.push(bits[..SEGMENT_BITS].to_vec());
        rows.push(SegmentUpdateTrace {
            live,
            segment_id,
            root_before: routed.root_before,
            root_after: routed.root_after,
        });
    }

    for pair in rows.windows(2) {
        let dead_then_live = mul(b, &pair[1].live, &pair[0].live.add_const(F128::ONE));
        pin_zero(b, &dead_then_live);
    }

    for (pair, bits) in rows.windows(2).zip(id_bits.windows(2)) {
        let both_live = mul(b, &pair[0].live, &pair[1].live);
        let (strictly_less, _) = strict_less_bits(b, &bits[0], &bits[1]);
        let violation = mul(b, &both_live, &strictly_less.add_const(F128::ONE));
        pin_zero(b, &violation);
    }

    CompactedSegmentTrace {
        rows,
        segment_id_bits: id_bits,
        source_rows,
        sort_rows,
        network_rows,
    }
}

/// Bind compacted segment tuples to upper paired-walk entries and chain the
/// resulting global roots from the parent to the child endpoint.
///
/// Entry equality is unconditional, so dead suffix rows force the upper
/// walk's old/new entries to the compactor's canonical zero tuple. Global
/// root continuity is gated by the proven live prefix; dead ghost paths are
/// therefore disconnected from the accepted transition.
pub fn bind_segment_upper_chain(
    b: &mut FieldR1csBuilder,
    segments: &CompactedSegmentTrace,
    upper_old_entries: &[[LinExpr; 2]],
    upper_new_entries: &[[LinExpr; 2]],
    upper_roots_before: &[[LinExpr; 2]],
    upper_roots_after: &[[LinExpr; 2]],
    parent_root: &[LinExpr; 2],
    child_root: &[LinExpr; 2],
) {
    let capacity = segments.rows.len();
    assert_eq!(upper_old_entries.len(), capacity);
    assert_eq!(upper_new_entries.len(), capacity);
    assert_eq!(upper_roots_before.len(), capacity);
    assert_eq!(upper_roots_after.len(), capacity);

    let mut rolling = parent_root.clone();
    for index in 0..capacity {
        let row = &segments.rows[index];
        for lane in 0..2 {
            pin_eq(b, &row.root_before[lane], &upper_old_entries[index][lane]);
            pin_eq(b, &row.root_after[lane], &upper_new_entries[index][lane]);

            let discontinuity = rolling[lane].add(&upper_roots_before[index][lane]);
            let gated_discontinuity = mul(b, &row.live, &discontinuity);
            pin_zero(b, &gated_discontinuity);

            let delta = rolling[lane].add(&upper_roots_after[index][lane]);
            rolling[lane] = rolling[lane].add(&mul(b, &row.live, &delta));
        }
    }
    for lane in 0..2 {
        pin_eq(b, &rolling[lane], &child_root[lane]);
    }
}

fn zero_segment_update() -> SegmentUpdateTrace {
    SegmentUpdateTrace {
        live: LinExpr::zero(),
        segment_id: LinExpr::zero(),
        root_before: [LinExpr::zero(), LinExpr::zero()],
        root_after: [LinExpr::zero(), LinExpr::zero()],
    }
}

fn segment_route_lanes(row: SegmentUpdateTrace) -> Vec<LinExpr> {
    let key = row
        .segment_id
        .add(&row.live.scale(flat_const(1u128 << SEGMENT_BITS)));
    vec![
        key,
        row.root_before[0].clone(),
        row.root_before[1].clone(),
        row.root_after[0].clone(),
        row.root_after[1].clone(),
    ]
}

fn segment_route_from_lanes(mut lanes: Vec<LinExpr>) -> SegmentRouteTrace {
    assert_eq!(lanes.len(), 5);
    let after1 = lanes.pop().unwrap();
    let after0 = lanes.pop().unwrap();
    let before1 = lanes.pop().unwrap();
    let before0 = lanes.pop().unwrap();
    let key = lanes.pop().unwrap();
    SegmentRouteTrace {
        key,
        root_before: [before0, before1],
        root_after: [after0, after1],
    }
}

fn native_bool(expr: &LinExpr, b: &FieldR1csBuilder) -> bool {
    match expr.eval(b.values()) {
        F128::ZERO => false,
        F128::ONE => true,
        value => panic!("non-boolean segment selector in native witness: {value:?}"),
    }
}

fn native_tower_u128(expr: &LinExpr, b: &FieldR1csBuilder) -> u128 {
    let flat = expr.eval(b.values());
    let raw = u128::from(flat.lo) | (u128::from(flat.hi) << 64);
    noid_core::hardware::flat_to_tower_u128(raw)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::trace::action_compaction::compact_action_rows;
    use crate::acceptance::trace::action_surface::ActionRowTrace;
    use crate::acceptance::trace::{alloc_block, flat_of};
    use noid_core::Block128;

    fn action(b: &mut FieldR1csBuilder, slot: u32, live: bool) -> ActionRowTrace {
        ActionRowTrace {
            live: LinExpr::from_wire(b.alloc_bool(live)),
            slot_index: alloc_block(b, Block128::from(slot as u128)),
            value: LinExpr::zero(),
            owner: [LinExpr::zero(), LinExpr::zero()],
            is_mint: LinExpr::zero(),
        }
    }

    fn roots(
        b: &mut FieldR1csBuilder,
        pairs: &[([u128; 2], [u128; 2])],
        capacity: usize,
    ) -> (Vec<[LinExpr; 2]>, Vec<[LinExpr; 2]>) {
        let mut before = Vec::with_capacity(capacity);
        let mut after = Vec::with_capacity(capacity);
        for index in 0..capacity {
            let (old, new) = pairs.get(index).copied().unwrap_or(([0, 0], [0, 0]));
            before.push(std::array::from_fn(|lane| {
                alloc_block(b, Block128::from(old[lane]))
            }));
            after.push(std::array::from_fn(|lane| {
                alloc_block(b, Block128::from(new[lane]))
            }));
        }
        (before, after)
    }

    fn eval_pair(pair: &[LinExpr; 2], b: &FieldR1csBuilder) -> [F128; 2] {
        [pair[0].eval(b.values()), pair[1].eval(b.values())]
    }

    fn build_case(
        slots: &[(u32, bool)],
        pairs: &[([u128; 2], [u128; 2])],
        max_segments: usize,
    ) -> (
        noid_ivc_core::field_r1cs::FieldR1cs,
        Vec<F128>,
        Vec<(F128, [F128; 2], [F128; 2])>,
        usize,
    ) {
        let mut b = FieldR1csBuilder::new();
        let actions = slots
            .iter()
            .map(|&(slot, live)| action(&mut b, slot, live))
            .collect::<Vec<_>>();
        let compacted = compact_action_rows(&mut b, &actions, actions.len());
        let (before, after) = roots(&mut b, pairs, actions.len());
        let segments = compact_segment_updates(
            &mut b,
            &compacted.rows,
            &compacted.slot_bits,
            &compacted.adjacent_msb_one_hot,
            &compacted.adjacent_both_live,
            &before,
            &after,
            max_segments,
        );
        let values = segments
            .rows
            .iter()
            .map(|row| {
                (
                    row.segment_id.eval(b.values()),
                    eval_pair(&row.root_before, &b),
                    eval_pair(&row.root_after, &b),
                )
            })
            .collect();
        let network_rows = segments.network_rows;
        let (r1cs, witness) = b.build();
        (r1cs, witness, values, network_rows)
    }

    fn alloc_pair(b: &mut FieldR1csBuilder, value: [u128; 2]) -> [LinExpr; 2] {
        std::array::from_fn(|lane| alloc_block(b, Block128::from(value[lane])))
    }

    fn upper_chain_case(
        break_entry: bool,
        break_chain: bool,
    ) -> (noid_ivc_core::field_r1cs::FieldR1cs, Vec<F128>) {
        let mut b = FieldR1csBuilder::new();
        let actions = vec![
            action(&mut b, 0x0001_0001, true),
            action(&mut b, 0x0002_0001, true),
            action(&mut b, 0, false),
            action(&mut b, 0, false),
        ];
        let compacted = compact_action_rows(&mut b, &actions, actions.len());
        let (local_before, local_after) = roots(
            &mut b,
            &[([10, 11], [20, 21]), ([30, 31], [40, 41])],
            actions.len(),
        );
        let segments = compact_segment_updates(
            &mut b,
            &compacted.rows,
            &compacted.slot_bits,
            &compacted.adjacent_msb_one_hot,
            &compacted.adjacent_both_live,
            &local_before,
            &local_after,
            actions.len(),
        );

        let mut upper_old = vec![
            alloc_pair(&mut b, [10, 11]),
            alloc_pair(&mut b, [30, 31]),
            alloc_pair(&mut b, [0, 0]),
            alloc_pair(&mut b, [0, 0]),
        ];
        if break_entry {
            upper_old[1] = alloc_pair(&mut b, [99, 31]);
        }
        let upper_new = vec![
            alloc_pair(&mut b, [20, 21]),
            alloc_pair(&mut b, [40, 41]),
            alloc_pair(&mut b, [0, 0]),
            alloc_pair(&mut b, [0, 0]),
        ];
        let upper_before = vec![
            alloc_pair(&mut b, [100, 101]),
            alloc_pair(&mut b, if break_chain { [999, 201] } else { [200, 201] }),
            alloc_pair(&mut b, [0, 0]),
            alloc_pair(&mut b, [0, 0]),
        ];
        let upper_after = vec![
            alloc_pair(&mut b, [200, 201]),
            alloc_pair(&mut b, [300, 301]),
            alloc_pair(&mut b, [0, 0]),
            alloc_pair(&mut b, [0, 0]),
        ];
        let parent = alloc_pair(&mut b, [100, 101]);
        let child = alloc_pair(&mut b, [300, 301]);
        bind_segment_upper_chain(
            &mut b,
            &segments,
            &upper_old,
            &upper_new,
            &upper_before,
            &upper_after,
            &parent,
            &child,
        );
        b.build()
    }

    #[test]
    fn derives_one_whole_tuple_per_segment() {
        let (r1cs, witness, rows, _) = build_case(
            &[
                (0x0001_0001, true),
                (0x0001_0003, true),
                (0x0004_0002, true),
                (0, false),
            ],
            &[
                ([10, 11], [20, 21]),
                ([20, 21], [30, 31]),
                ([40, 41], [50, 51]),
            ],
            4,
        );
        assert!(r1cs.satisfies(&witness));
        assert_eq!(rows[0].0, flat_of(Block128::from(1u128)));
        assert_eq!(
            rows[0].1,
            [
                flat_of(Block128::from(10u128)),
                flat_of(Block128::from(11u128)),
            ]
        );
        assert_eq!(
            rows[0].2,
            [
                flat_of(Block128::from(30u128)),
                flat_of(Block128::from(31u128)),
            ]
        );
        assert_eq!(rows[1].0, flat_of(Block128::from(4u128)));
        assert_eq!(
            rows[1].1,
            [
                flat_of(Block128::from(40u128)),
                flat_of(Block128::from(41u128)),
            ]
        );
        assert_eq!(
            rows[1].2,
            [
                flat_of(Block128::from(50u128)),
                flat_of(Block128::from(51u128)),
            ]
        );
        assert_eq!(rows[2], (F128::ZERO, [F128::ZERO; 2], [F128::ZERO; 2]));
    }

    #[test]
    fn rejects_a_broken_local_chain() {
        let (r1cs, witness, _, _) = build_case(
            &[(0x0001_0001, true), (0x0001_0003, true)],
            &[([10, 11], [20, 21]), ([99, 21], [30, 31])],
            2,
        );
        assert!(!r1cs.satisfies(&witness));
    }

    #[test]
    fn upper_entries_and_global_roots_chain_end_to_end() {
        let (r1cs, witness) = upper_chain_case(false, false);
        assert!(r1cs.satisfies(&witness));
    }

    #[test]
    fn rejects_a_mismatched_upper_entry_or_global_chain() {
        for (break_entry, break_chain) in [(true, false), (false, true)] {
            let (r1cs, witness) = upper_chain_case(break_entry, break_chain);
            assert!(!r1cs.satisfies(&witness));
        }
    }

    #[test]
    fn segment_cap_is_algebraic() {
        let (r1cs, witness, _, _) = build_case(
            &[(0x0000_0001, true), (0x0001_0001, true)],
            &[([10, 11], [20, 21]), ([30, 31], [40, 41])],
            1,
        );
        assert!(!r1cs.satisfies(&witness));
    }

    #[test]
    fn topology_and_occupancy_do_not_change_the_matrix() {
        let (left, left_witness, _, _) = build_case(
            &[
                (0x0001_0001, true),
                (0x0001_0003, true),
                (0x0004_0002, true),
                (0, false),
            ],
            &[
                ([10, 11], [20, 21]),
                ([20, 21], [30, 31]),
                ([40, 41], [50, 51]),
            ],
            4,
        );
        let (right, right_witness, _, _) = build_case(
            &[
                (0x0002_0100, true),
                (0x0005_0200, true),
                (0, false),
                (0, false),
            ],
            &[([60, 61], [70, 71]), ([80, 81], [90, 91])],
            4,
        );
        assert!(left.satisfies(&left_witness));
        assert!(right.satisfies(&right_witness));
        assert_eq!(left.useful_rows, right.useful_rows);
        assert_eq!(left.statement_digest(), right.statement_digest());
    }

    #[test]
    fn b255_uses_one_five_lane_2048_row_network() {
        const ACTIONS: usize = 1_531;
        let mut b = FieldR1csBuilder::new();
        let actions = (0..ACTIONS)
            .map(|slot| action(&mut b, slot as u32, true))
            .collect::<Vec<_>>();
        let compacted = compact_action_rows(&mut b, &actions, ACTIONS);
        // Allocate even zero-valued endpoints as wires: production endpoints
        // are committed-column claims, and constant-folding them here would
        // undercount the class-fixed five-lane network.
        let zero_roots = (0..ACTIONS)
            .map(|_| {
                [
                    alloc_block(&mut b, Block128::from(0u128)),
                    alloc_block(&mut b, Block128::from(0u128)),
                ]
            })
            .collect::<Vec<_>>();
        let segments = compact_segment_updates(
            &mut b,
            &compacted.rows,
            &compacted.slot_bits,
            &compacted.adjacent_msb_one_hot,
            &compacted.adjacent_both_live,
            &zero_roots,
            &zero_roots,
            256,
        );
        assert_eq!(segments.sort_rows, 2_048);
        assert_eq!(segments.network_rows, 117_484);
        let (r1cs, witness) = b.build();
        assert!(r1cs.satisfies(&witness));
    }
}
