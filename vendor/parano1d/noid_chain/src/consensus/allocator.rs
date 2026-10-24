// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Native slot allocator for wallet hint generation.
//!
//! Uses splitmix64 seeded from `alloc_counter` to produce candidate free slot
//! indices. Hints are **non-authoritative** — miners verify slot emptiness via
//! the exact state transition proof. Two wallets may receive the same hint;
//! conflicts are resolved at block inclusion time.
//!
//! splitmix64 is chosen over LCG because it is bijective and all output bits
//! are equally well-distributed. With `idx = splitmix64(counter) mod 2^k`,
//! even the low-order bits (used for slot masking) are fully mixed.
//! Reference: https://prng.di.unimi.it/splitmix64.c

/// splitmix64 — standard 64-bit non-cryptographic bijective mixer.
///
/// State advances by the Weyl sequence constant 0x9e3779b97f4a7c15;
/// the output is mixed through two multiply-xorshift rounds.
/// Every input maps to a unique output (bijection over u64).
#[inline]
pub fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

/// Zone capacity: number of consecutive slots allocated within one segment.
/// Must equal 2^LOG_SEGMENT_SIZE so that one zone == one raw state segment.
///
/// # Rationale for zone-based allocation
///
/// Naive uniform splitmix64 would send each new UTXO to a DIFFERENT segment,
/// materialising all 256 segments (768 MB) after just 256 blocks (~1.4 hours
/// at the production 20s/block target). With zone-based allocation, sequential slots within
/// one zone land in the SAME segment, so memory grows as:
///
///   ceil(alloc_counter / ZONE_CAPACITY) segments × 3 MB
///
/// rather than min(alloc_counter, 256) segments × 3 MB.
///
/// # Slot conflict mitigation
///
/// Multiple wallets on DIFFERENT nodes can receive the same slot hint if their
/// nodes have the same `alloc_counter`. To mitigate:
/// 1. Nodes over-generate hints (e.g. 256) and return them shuffled by
///    `splitmix64(tip_hash)` — different tip hashes = different orderings.
/// 2. Wallets should request multiple hints and try alternates on conflict.
/// 3. The WITHIN-ZONE offset is sequential, so two nodes at different heights
///    will naturally give different hints even in the same zone.
pub const ZONE_CAPACITY: u64 = 1 << 16; // = 2^LOG_SEGMENT_SIZE = 65536

/// Bijective zone permutation for `num_zones = 2^k`.
///
/// An odd multiplier is invertible modulo `2^k`, so
/// `zone_id ↦ zone_id * mul + add (mod 2^k)` visits every segment exactly once
/// per cycle. This avoids the collision-heavy `splitmix64(zone_id) % num_zones`
/// mapping while keeping allocation deterministic and cheap.
#[inline]
pub fn permute_zone(zone_id: u64, num_zones: u64, seed: u64) -> u64 {
    debug_assert!(num_zones.is_power_of_two());
    let mask = num_zones - 1;
    let mut s = seed ^ 0xD1B5_4A32_D192_ED03;
    let mul = splitmix64(&mut s) | 1; // odd => invertible modulo 2^k
    let add = splitmix64(&mut s);
    zone_id.wrapping_mul(mul).wrapping_add(add) & mask
}

/// Generate `count` candidate free slot indices from an `alloc_counter` seed.
///
/// ## Zone-based strategy
///
/// Consecutive `alloc_counter` values within the same zone (block of
/// `ZONE_CAPACITY` increments) map to the SAME randomly-chosen segment,
/// filling it sequentially. A new zone starts a new randomly-chosen segment.
///
/// This bounds memory to `ceil(alloc_counter / ZONE_CAPACITY) × segment_size`
/// instead of `min(alloc_counter, num_segments) × segment_size`.
///
/// The caller is responsible for checking actual slot occupancy and may
/// advance `alloc_counter` further if a candidate slot is occupied.
pub fn generate_slot_hints(alloc_counter: u64, log_slots: u32, count: usize) -> Vec<u32> {
    debug_assert!(log_slots <= 32, "log_slots must fit in u32 slot index");

    let num_slots: u64 = 1 << log_slots;

    // Zone-based allocation requires at least 2 zones (log_slots > LOG_SEGMENT_SIZE = 16).
    // For small test states (log_slots <= 16), fall back to simple uniform splitmix64.
    if num_slots <= ZONE_CAPACITY {
        // Monolithic or smaller-than-zone state: simple uniform distribution.
        let mask = num_slots - 1;
        let mut state = alloc_counter;
        let mut hints = Vec::with_capacity(count);
        while hints.len() < count {
            let raw = splitmix64(&mut state);
            hints.push((raw & mask) as u32);
        }
        return hints;
    }

    // Zone-based allocation for production (log_slots > 16).
    // Consecutive alloc_counter values within the same ZONE land in the SAME
    // segment, so memory grows O(zones) = O(alloc_counter / ZONE_CAPACITY)
    // rather than O(min(alloc_counter, num_segments)).
    let zone_mask: u64 = ZONE_CAPACITY - 1;
    let num_zones: u64 = num_slots / ZONE_CAPACITY; // = 2^(log_slots - 16) = 256 at genesis
    let perm_seed = 0xA076_1D64_78BD_642F ^ ((log_slots as u64) << 32);

    let mut hints = Vec::with_capacity(count);
    let mut counter = alloc_counter;

    while hints.len() < count {
        let zone_id = counter / ZONE_CAPACITY;
        let zone_offset = counter & zone_mask;

        // Map zone_id to a permuted segment index. Because num_zones is a
        // power of two, this is a real permutation (no modulo collisions).
        let zone_seg = permute_zone(zone_id, num_zones, perm_seed);
        let zone_start = zone_seg * ZONE_CAPACITY;
        let slot = (zone_start + zone_offset) as u32;

        hints.push(slot);
        counter += 1;
    }
    hints
}

/// Generate a deterministic, duplicate-free probe order over state segments.
///
/// The first entry is the segment selected by the allocator's current zone.
/// Later entries advance through successive zones. Since [`permute_zone`] is
/// bijective modulo the power-of-two segment count, a full probe visits every
/// segment exactly once. This is the bounded escape path when the current zone
/// is full after long-lived churn or a `log_slots` expansion.
///
/// Slot hints remain non-authoritative. Callers use compact live counts to skip
/// full segments and verify the selected raw slot before minting.
pub fn generate_zone_segment_hints(alloc_counter: u64, log_slots: u32, count: usize) -> Vec<u16> {
    debug_assert!(log_slots <= 32, "log_slots must fit in u32 slot index");
    if count == 0 {
        return Vec::new();
    }
    if log_slots <= 16 {
        return vec![0];
    }

    let num_zones = 1u64 << (log_slots - 16);
    let limit = count.min(num_zones as usize);
    let first_zone = alloc_counter / ZONE_CAPACITY;
    let perm_seed = 0xA076_1D64_78BD_642F ^ ((log_slots as u64) << 32);
    (0..limit)
        .map(|offset| {
            let segment =
                permute_zone(first_zone.wrapping_add(offset as u64), num_zones, perm_seed);
            u16::try_from(segment).expect("log_slots <= 32 implies a u16 segment id")
        })
        .collect()
}

/// Deduplicate slot hints and remove any slots already in `reserved`.
///
/// Preserves generation order. O(n log n).
pub fn deduplicate_hints(hints: Vec<u32>, reserved: &[u32]) -> Vec<u32> {
    let mut seen = std::collections::HashSet::new();
    for &r in reserved {
        seen.insert(r);
    }
    hints.into_iter().filter(|s| seen.insert(*s)).collect()
}

/// Compute the `alloc_counter` increment for a block that creates `n_outputs`
/// new outputs (including coinbase). The counter increments by 1 per mint.
pub fn alloc_counter_increment(n_outputs: u64) -> u64 {
    n_outputs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn splitmix64_advances() {
        let mut s = 42u64;
        let a = splitmix64(&mut s);
        let b = splitmix64(&mut s);
        assert_ne!(a, b);
        assert_ne!(a, 42);
    }

    #[test]
    fn splitmix64_deterministic() {
        let mut s1 = 1234u64;
        let mut s2 = 1234u64;
        for _ in 0..100 {
            assert_eq!(splitmix64(&mut s1), splitmix64(&mut s2));
        }
    }

    #[test]
    fn splitmix64_bijective_on_small_sample() {
        // Check no collisions over 65536 consecutive inputs.
        let mut outputs = std::collections::HashSet::new();
        let mut s = 0u64;
        for _ in 0..65536 {
            let v = splitmix64(&mut s);
            assert!(outputs.insert(v), "collision detected");
        }
    }

    #[test]
    fn generate_correct_count() {
        let hints = generate_slot_hints(0, 24, 10);
        assert_eq!(hints.len(), 10);
    }

    #[test]
    fn slots_within_range() {
        let log_slots = 24;
        let cap = 1u64 << log_slots;
        let hints = generate_slot_hints(999, log_slots, 1000);
        for &h in &hints {
            assert!((h as u64) < cap, "slot {h} exceeds capacity {cap}");
        }
    }

    #[test]
    fn different_counters_different_hints() {
        let a = generate_slot_hints(0, 24, 5);
        let b = generate_slot_hints(1, 24, 5);
        assert_ne!(a, b);
    }

    #[test]
    fn deduplication_removes_reserved() {
        let hints = vec![1u32, 2, 3, 4, 5];
        let reserved = vec![2u32, 4];
        let result = deduplicate_hints(hints, &reserved);
        assert!(!result.contains(&2));
        assert!(!result.contains(&4));
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn deduplication_removes_duplicates_within_hints() {
        let hints = vec![1u32, 1, 2, 2, 3];
        let result = deduplicate_hints(hints, &[]);
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn genesis_counter_starts_at_zero() {
        let hints_a = generate_slot_hints(0, 24, 3);
        let hints_b = generate_slot_hints(0, 24, 3);
        assert_eq!(hints_a, hints_b);
    }

    /// Verify zone-based allocation: first ZONE_CAPACITY slots all land in the
    /// SAME segment (zone 0), and zone 1 lands in a DIFFERENT segment.
    #[test]
    fn zone_based_same_segment_within_zone() {
        let log_slots = 24u32;
        let seg_size = 1u32 << 16; // LOG_SEGMENT_SIZE

        // All hints within zone 0 (counter 0..ZONE_CAPACITY-1) must be in the same segment.
        let hints_zone0_start = generate_slot_hints(0, log_slots, 10);
        let hints_zone0_end = generate_slot_hints(ZONE_CAPACITY - 10, log_slots, 10);
        let seg_z0_start = hints_zone0_start[0] / seg_size;
        for &h in &hints_zone0_start {
            assert_eq!(
                h / seg_size,
                seg_z0_start,
                "zone 0 start spread across segments"
            );
        }
        for &h in &hints_zone0_end {
            assert_eq!(
                h / seg_size,
                seg_z0_start,
                "zone 0 end in different segment"
            );
        }

        // Zone 1 must be in a DIFFERENT (random) segment.
        let hints_zone1 = generate_slot_hints(ZONE_CAPACITY, log_slots, 10);
        let seg_z1 = hints_zone1[0] / seg_size;
        for &h in &hints_zone1 {
            assert_eq!(h / seg_size, seg_z1, "zone 1 spread across segments");
        }
        assert_ne!(
            seg_z0_start, seg_z1,
            "zone 0 and zone 1 should be in different segments"
        );
    }

    /// Memory growth is O(zone_count) not O(unique_slots).
    #[test]
    fn memory_growth_proportional_to_zones() {
        let log_slots = 24u32;
        let seg_size = 1u32 << 16;

        // Generate 256 slots (one per block at genesis).
        let hints = generate_slot_hints(0, log_slots, 256);
        let segments: std::collections::HashSet<u32> =
            hints.iter().map(|&h| h / seg_size).collect();
        // ALL 256 hints must be in the SAME segment (zone 0).
        assert_eq!(
            segments.len(),
            1,
            "256 consecutive slots should be in 1 segment, got {}",
            segments.len()
        );

        // After ZONE_CAPACITY blocks, we move to zone 1 (1 new segment).
        let hints2 = generate_slot_hints(ZONE_CAPACITY, log_slots, 256);
        let segs2: std::collections::HashSet<u32> = hints2.iter().map(|&h| h / seg_size).collect();
        assert_eq!(segs2.len(), 1, "zone 1: 256 slots should be in 1 segment");
        assert!(
            segments.is_disjoint(&segs2),
            "zone 0 and zone 1 should use different segments"
        );
    }

    #[test]
    fn zone_permutation_covers_all_segments_once() {
        let log_slots = 24u32;
        let num_zones = 1u64 << (log_slots - 16);
        let seed = 0xA076_1D64_78BD_642F ^ ((log_slots as u64) << 32);
        let mut seen = std::collections::HashSet::new();
        for zone in 0..num_zones {
            let seg = permute_zone(zone, num_zones, seed);
            assert!(seen.insert(seg), "duplicate segment {seg} for zone {zone}");
        }
        assert_eq!(seen.len() as u64, num_zones);
    }

    #[test]
    fn zone_segment_probe_visits_each_segment_once() {
        for log_slots in [17u32, 24, 25, 32] {
            let segment_count = 1usize << (log_slots - 16);
            let hints = generate_zone_segment_hints(
                193 * ZONE_CAPACITY + 17,
                log_slots,
                segment_count + 10,
            );
            assert_eq!(hints.len(), segment_count);
            let unique = hints
                .iter()
                .copied()
                .collect::<std::collections::HashSet<_>>();
            assert_eq!(unique.len(), segment_count);
            assert!(hints
                .iter()
                .all(|segment| usize::from(*segment) < segment_count));
        }
    }

    #[test]
    fn zone_segment_probe_escapes_a_full_primary_after_expansion() {
        let old_log_slots = 24u32;
        let old_segment_count = 1usize << (old_log_slots - 16);
        let old_seed = 0xA076_1D64_78BD_642F ^ ((old_log_slots as u64) << 32);
        let old_filled = (0..192u64)
            .map(|zone| permute_zone(zone, old_segment_count as u64, old_seed) as u16)
            .collect::<std::collections::HashSet<_>>();

        // At the expanded depth, zones 194 and 195 deterministically land in
        // old full segments. The probe must still reach a free segment rather
        // than treating one exhausted 65,536-slot zone as global exhaustion.
        let hints = generate_zone_segment_hints(194 * ZONE_CAPACITY, 25, 512);
        assert!(old_filled.contains(&hints[0]));
        assert!(hints.iter().any(|segment| !old_filled.contains(segment)));
    }

    #[test]
    fn low_bits_uniformly_distributed() {
        // Verify that the bottom k bits of splitmix64 outputs are well-distributed.
        // With LCG, bottom bits have shorter period. With splitmix64 they should not.
        let mask = (1u64 << 24) - 1;
        let mut state = 0u64;
        let n = 100_000usize;
        let buckets = 256usize;
        let mut counts = vec![0usize; buckets];
        for _ in 0..n {
            let v = splitmix64(&mut state) & mask;
            counts[(v % buckets as u64) as usize] += 1;
        }
        let expected = n / buckets;
        for &c in &counts {
            // Allow ±20% deviation from uniform.
            assert!(
                c > expected * 80 / 100 && c < expected * 120 / 100,
                "bucket count {} deviates too far from expected {}",
                c,
                expected
            );
        }
    }
}
