//! Flat-basis replay of the capsule-PCS query-leaf sponge.
//!
//! Each capsule query opens a 16-symbol coset leaf whose hash is a rate-2
//! FLAT Poseidon2b sponge on the `TAG_CAPSLEAF` capacity IV: one meta block
//! `[msg_log, leaf_index]`, then the 16 coset symbols over eight further
//! blocks — nine permutations total, NO padding flush (the schedule is
//! fixed-length and block-aligned; domain separation is the dedicated tag).
//! The digest is the two rate lanes after the last permutation.
//!
//! Unlike the legacy tower leaf hashes (replayed flat via φ at every
//! boundary), the capsule sponge is flat-native: the capacity IV and the
//! meta lanes are RAW flat words (`u128` little-endian bytes reinterpreted
//! as flat lanes), and only the coset symbols cross the tower→flat boundary
//! (the native hasher absorbs `tower_to_flat(sym)`, so the committed symbol
//! cells hold φ(sym) — the same convention as every other leaf family's
//! symbol lanes).
//!
//! The tile is a strict generalization of the exact-state sponge leaf
//! (distance-1 duplex carry) to nine slots: slot 0 absorbs the meta block
//! on the IV capacity, slots 1..=8 feed the previous slot's full output
//! state forward and absorb two symbols each, slots 9..15 of the 16-slot
//! stride are ghost permutations (`raw = 0`). `IN0/IN1` are read PLAINLY by
//! the substitution — they are zero at ghost slots and the assembly pins the
//! slot-0 meta cells (msg_log to the class constant, leaf_index to the query
//! position bits).

use crate::deep_chain::leaf_hash::SourceLeafColumns;
use crate::deep_chain::relations::{ColRef, FixedPattern, RelationTerm};
use crate::deep_chain::source_tree::{mds_weights_pub, permute_flat_state, run_perm};
use crate::field::F128;
use noid_poseidon2b::native::domain::{TAG_CAPS256, TAG_CAPSLEAF, TAG_CAPSMIX, capacity_iv_flat};
use noid_poseidon2b::native::permutation::STATE_SIZE;

/// Symbols per capsule leaf — mirrors
/// `noid_fri_binius::capsule::CAPSULE_LEAF_SYMBOLS`. Kept in sync with the
/// native constant; a mismatch only yields honest-rejected proofs.
pub const CAPSULE_LEAF_SYMBOLS: usize = 16;

/// Active permutation slots per capsule leaf: 1 meta block + 8 symbol blocks.
pub const CAPSULE_LEAF_SLOTS: usize = 1 + CAPSULE_LEAF_SYMBOLS / 2;
/// Tile stride (the fixed-pattern period).
pub const CAPSULE_LEAF_STRIDE: usize = 16;
/// The slot holding a leaf's digest (the last permutation's `C0/C1`),
/// relative to the leaf's tile base.
pub const CAPSULE_LEAF_DIGEST_SLOT: usize = CAPSULE_LEAF_SLOTS - 1;

/// A raw flat lane: the `u128`'s little-endian bytes reinterpreted as a flat
/// F128 word (NO basis change). This is how the flat sponge absorbs metadata
/// and how flat digests read back as lanes — contrast `flat_lane` (= φ of a
/// tower word), which only the coset symbols go through.
#[inline]
pub fn raw_flat_lane(v: u128) -> F128 {
    F128 {
        lo: v as u64,
        hi: (v >> 64) as u64,
    }
}

/// The flat capacity IV for the capsule leaf sponge (`TAG_CAPSLEAF`), as raw
/// flat lanes (the flat sponge seeds its capacity with these words directly).
pub fn capsule_leaf_iv_flat() -> [F128; 2] {
    let iv = capacity_iv_flat(TAG_CAPSLEAF);
    [raw_flat_lane(iv[0]), raw_flat_lane(iv[1])]
}

/// Flat replay of the native capsule leaf hash: nine chained permutations,
/// no padding flush.
///
/// ```text
///   s = permute([msg_log, leaf_index, iv0, iv1])          // meta block
///   for k in 0..8: s = permute([s0 + sym[2k], s1 + sym[2k+1], s2, s3])
///   digest = (s0, s1)
/// ```
///
/// `syms` are the 16 coset symbols already as flat lanes (φ applied at the
/// boundary); `msg_log`/`leaf_index` enter as raw flat words. Matches the
/// native flat-sponge `capsule_leaf_hash` lane-for-lane.
pub fn flat_capsule_leaf_hash(msg_log: usize, leaf_index: usize, syms: &[F128]) -> [F128; 2] {
    assert_eq!(
        syms.len(),
        CAPSULE_LEAF_SYMBOLS,
        "capsule leaf symbol count"
    );
    let iv = capsule_leaf_iv_flat();
    let mut s = permute_flat_state([
        raw_flat_lane(msg_log as u128),
        raw_flat_lane(leaf_index as u128),
        iv[0],
        iv[1],
    ]);
    for k in 0..CAPSULE_LEAF_SYMBOLS / 2 {
        s = permute_flat_state([s[0] + syms[2 * k], s[1] + syms[2 * k + 1], s[2], s[3]]);
    }
    [s[0], s[1]]
}

/// One capsule leaf's replay inputs: the class-fixed message log-size, the
/// query's leaf index, and the 16 queried coset symbols as flat lanes.
#[derive(Clone, Debug)]
pub struct CapsuleLeafData {
    pub msg_log: usize,
    pub leaf_index: usize,
    pub syms: [F128; CAPSULE_LEAF_SYMBOLS],
}

/// Fill the region columns for `leaves.len()` capsule-leaf sponge chains
/// tiled at stride [`CAPSULE_LEAF_STRIDE`] (leaf `t` at slots `16t..16t+9`).
/// `w_log` must cover the tiles. Any tile past `leaves.len()` is a CANONICAL
/// GHOST capsule leaf (`msg_log = leaf_index = 0`, all-zero symbols) — a
/// real nine-permutation run, because the periodic fixed patterns fire in
/// every tile and must be satisfied by a real sponge chain; slots 9..15 of
/// every tile are plain ghost permutations (`raw = 0`). Returns the columns
/// and each REAL leaf's digest (`C0/C1` at its slot `16t + 8`); leaf `t`'s
/// digest matches [`flat_capsule_leaf_hash`] (hence the native flat-sponge
/// `capsule_leaf_hash` lane-for-lane).
///
/// Reuses the [`SourceLeafColumns`] layout: `IN0/IN1` are the two rate-absorb
/// lanes at each slot (`[msg_log, leaf_index]` at the tile's slot 0, the
/// symbol pairs at slots 1..=8, zero elsewhere); `c/s0/s_out` are every
/// slot's permutation.
pub fn build_capsule_leaf_columns(
    leaves: &[CapsuleLeafData],
    w_log: usize,
) -> (SourceLeafColumns, Vec<[F128; 2]>) {
    let w = 1usize << w_log;
    assert_eq!(
        w % CAPSULE_LEAF_STRIDE,
        0,
        "domain not a multiple of the tile"
    );
    let num_tiles = w / CAPSULE_LEAF_STRIDE;
    assert!(leaves.len() <= num_tiles, "more leaves than tiles");
    let iv = capsule_leaf_iv_flat();
    let ghost = CapsuleLeafData {
        msg_log: 0,
        leaf_index: 0,
        syms: [F128::ZERO; CAPSULE_LEAF_SYMBOLS],
    };

    let mut c: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut s0: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut s_out: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut in_: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; w]);

    let mut store = |slot: usize,
                     s0v: [F128; STATE_SIZE],
                     outv: [F128; STATE_SIZE],
                     c: &mut [Vec<F128>; STATE_SIZE]| {
        for j in 0..STATE_SIZE {
            s0[j][slot] = s0v[j];
            s_out[j][slot] = outv[j];
            c[j][slot] = outv[j];
        }
    };

    // Ghost default (raw = 0), one perm broadcast; the 9 active slots of each
    // tile are overwritten below, slots 9..15 keep the ghost run.
    let (ghost_s0, ghost_out) = run_perm([F128::ZERO; STATE_SIZE]);
    for slot in 0..w {
        store(slot, ghost_s0, ghost_out, &mut c);
    }

    let mut digests = Vec::with_capacity(leaves.len());
    for t in 0..num_tiles {
        let leaf = leaves.get(t).unwrap_or(&ghost);
        let base = CAPSULE_LEAF_STRIDE * t;
        // Meta block on the IV capacity.
        let meta = [
            raw_flat_lane(leaf.msg_log as u128),
            raw_flat_lane(leaf.leaf_index as u128),
        ];
        let (a, b) = run_perm([meta[0], meta[1], iv[0], iv[1]]);
        store(base, a, b, &mut c);
        in_[0][base] = meta[0];
        in_[1][base] = meta[1];
        // Symbol blocks: feed the previous slot's full output state forward.
        for k in 0..CAPSULE_LEAF_SYMBOLS / 2 {
            let slot = base + 1 + k;
            let prev: [F128; STATE_SIZE] = std::array::from_fn(|j| c[j][slot - 1]);
            let (sa, sb) = [leaf.syms[2 * k], leaf.syms[2 * k + 1]].into();
            let (a, b) = run_perm([prev[0] + sa, prev[1] + sb, prev[2], prev[3]]);
            store(slot, a, b, &mut c);
            in_[0][slot] = sa;
            in_[1][slot] = sb;
        }
        if t < leaves.len() {
            let d = base + CAPSULE_LEAF_DIGEST_SLOT;
            digests.push([c[0][d], c[1][d]]);
        }
    }

    let digest = digests.first().copied().unwrap_or([F128::ZERO; 2]);
    (
        SourceLeafColumns {
            c,
            s0,
            s_out,
            in_,
            digest,
        },
        digests,
    )
}

/// Fixed C1 leaf types used by the wide authorization PCS.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum C1CapsuleLeafKind {
    /// Eight base-field bank cells interleaved with eight wide companion
    /// cells: 24 base-field lanes, 12 permutations.
    MixedSource,
    /// Sixteen wide mid-codeword cells: 32 base-field lanes, 16 permutations.
    WideMid,
}

pub const C1_CAPSULE_SOURCE_LANES: usize = 24;
pub const C1_CAPSULE_SOURCE_SLOTS: usize = C1_CAPSULE_SOURCE_LANES / 2;
pub const C1_CAPSULE_SOURCE_DIGEST_SLOT: usize = C1_CAPSULE_SOURCE_SLOTS - 1;
pub const C1_CAPSULE_MID_LANES: usize = 32;
pub const C1_CAPSULE_MID_SLOTS: usize = C1_CAPSULE_MID_LANES / 2;
pub const C1_CAPSULE_MID_DIGEST_SLOT: usize = C1_CAPSULE_MID_SLOTS - 1;
pub const C1_CAPSULE_LEAF_STRIDE: usize = 16;

impl C1CapsuleLeafKind {
    pub const fn lane_count(self) -> usize {
        match self {
            Self::MixedSource => C1_CAPSULE_SOURCE_LANES,
            Self::WideMid => C1_CAPSULE_MID_LANES,
        }
    }

    pub const fn active_slots(self) -> usize {
        self.lane_count() / 2
    }
}

fn c1_capsule_leaf_iv_flat(kind: C1CapsuleLeafKind) -> [F128; 2] {
    let tag = match kind {
        C1CapsuleLeafKind::MixedSource => TAG_CAPSMIX,
        C1CapsuleLeafKind::WideMid => TAG_CAPS256,
    };
    let iv = capacity_iv_flat(tag);
    [raw_flat_lane(iv[0]), raw_flat_lane(iv[1])]
}

/// One metadata-free C1 leaf. The dedicated tag fixes `lanes.len()` and the
/// ordered Merkle path binds its position.
#[derive(Clone, Debug)]
pub struct C1CapsuleLeafData {
    pub lanes: Vec<F128>,
}

/// Scalar replay of the native C1 fixed-shape leaf sponge.
pub fn flat_c1_capsule_leaf_hash(kind: C1CapsuleLeafKind, lanes: &[F128]) -> [F128; 2] {
    assert_eq!(lanes.len(), kind.lane_count(), "C1 capsule leaf lane count");
    let iv = c1_capsule_leaf_iv_flat(kind);
    let mut state = [F128::ZERO; STATE_SIZE];
    for (slot, pair) in lanes.chunks_exact(2).enumerate() {
        let raw = if slot == 0 {
            [pair[0], pair[1], iv[0], iv[1]]
        } else {
            [state[0] + pair[0], state[1] + pair[1], state[2], state[3]]
        };
        state = permute_flat_state(raw);
    }
    [state[0], state[1]]
}

/// Build metadata-free C1 leaf columns at a common 16-slot stride. Source
/// tiles leave slots 12..15 available to another explicitly disjoint family;
/// mid tiles consume all sixteen slots.
pub fn build_c1_capsule_leaf_columns(
    leaves: &[C1CapsuleLeafData],
    kind: C1CapsuleLeafKind,
    w_log: usize,
) -> (SourceLeafColumns, Vec<[F128; 2]>) {
    let w = 1usize << w_log;
    assert_eq!(w % C1_CAPSULE_LEAF_STRIDE, 0, "C1 leaf domain stride");
    let num_tiles = w / C1_CAPSULE_LEAF_STRIDE;
    assert!(leaves.len() <= num_tiles, "more C1 leaves than tiles");
    assert!(
        leaves
            .iter()
            .all(|leaf| leaf.lanes.len() == kind.lane_count()),
        "C1 leaf shape mismatch"
    );
    let iv = c1_capsule_leaf_iv_flat(kind);
    let zero_lanes = vec![F128::ZERO; kind.lane_count()];

    let mut c: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut s0: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut s_out: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut in_: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; w]);

    let (ghost_s0, ghost_out) = run_perm([F128::ZERO; STATE_SIZE]);
    for slot in 0..w {
        for lane in 0..STATE_SIZE {
            s0[lane][slot] = ghost_s0[lane];
            s_out[lane][slot] = ghost_out[lane];
            c[lane][slot] = ghost_out[lane];
        }
    }

    let mut digests = Vec::with_capacity(leaves.len());
    for tile in 0..num_tiles {
        let lanes = leaves
            .get(tile)
            .map_or(zero_lanes.as_slice(), |leaf| leaf.lanes.as_slice());
        let base = tile * C1_CAPSULE_LEAF_STRIDE;
        let mut previous = [F128::ZERO; STATE_SIZE];
        for (local_slot, pair) in lanes.chunks_exact(2).enumerate() {
            let slot = base + local_slot;
            let raw = if local_slot == 0 {
                [pair[0], pair[1], iv[0], iv[1]]
            } else {
                [
                    previous[0] + pair[0],
                    previous[1] + pair[1],
                    previous[2],
                    previous[3],
                ]
            };
            let (state_in, state_out) = run_perm(raw);
            for lane in 0..STATE_SIZE {
                s0[lane][slot] = state_in[lane];
                s_out[lane][slot] = state_out[lane];
                c[lane][slot] = state_out[lane];
            }
            in_[0][slot] = pair[0];
            in_[1][slot] = pair[1];
            previous = state_out;
        }
        if tile < leaves.len() {
            let digest_slot = base + kind.active_slots() - 1;
            digests.push([c[0][digest_slot], c[1][digest_slot]]);
        }
    }

    let digest = digests.first().copied().unwrap_or([F128::ZERO; 2]);
    (
        SourceLeafColumns {
            c,
            s0,
            s_out,
            in_,
            digest,
        },
        digests,
    )
}

/// Periodic carry and IV patterns for one C1 leaf kind.
pub fn c1_capsule_leaf_fixed_patterns(kind: C1CapsuleLeafKind) -> Vec<FixedPattern> {
    let low_log = C1_CAPSULE_LEAF_STRIDE.trailing_zeros() as usize;
    let mut carry = vec![F128::ZERO; C1_CAPSULE_LEAF_STRIDE];
    let mut iv0 = vec![F128::ZERO; C1_CAPSULE_LEAF_STRIDE];
    let mut iv1 = vec![F128::ZERO; C1_CAPSULE_LEAF_STRIDE];
    let iv = c1_capsule_leaf_iv_flat(kind);
    iv0[0] = iv[0];
    iv1[0] = iv[1];
    for slot in 1..kind.active_slots() {
        carry[slot] = F128::ONE;
    }
    vec![
        FixedPattern::new(low_log, carry),
        FixedPattern::new(low_log, iv0),
        FixedPattern::new(low_log, iv1),
    ]
}

/// Column/pattern indices of one capsule-leaf sponge family. Committed column
/// order `IN0, IN1, C0..C3`; pattern order `CARRY, IV0, IV1`.
#[derive(Clone, Copy, Debug)]
pub struct CapsuleLeafRefs {
    pub in_: [usize; 2],
    pub c: [usize; STATE_SIZE],
    pub carry: usize,
    pub iv: [usize; 2],
}

pub fn capsule_leaf_refs(col_base: usize, fixed_base: usize) -> CapsuleLeafRefs {
    CapsuleLeafRefs {
        in_: [col_base, col_base + 1],
        c: std::array::from_fn(|i| col_base + 2 + i),
        carry: fixed_base,
        iv: [fixed_base + 1, fixed_base + 2],
    }
}

/// The schedule patterns over one [`CAPSULE_LEAF_STRIDE`]-slot period.
/// `CARRY` marks the chained slots 1..=8 (the duplex feed-forward); `IV0/IV1`
/// carry the sponge capacity IV at slot 0 only. No absorb selector is needed:
/// `IN0/IN1` are read plainly (zero at ghost slots by construction). One
/// period tiles per leaf, so the verifier's pattern cost is query-count
/// independent.
pub fn capsule_leaf_fixed_patterns(iv_flat: [F128; 2]) -> Vec<FixedPattern> {
    let low_log = CAPSULE_LEAF_STRIDE.trailing_zeros() as usize;
    let mut carry = vec![F128::ZERO; CAPSULE_LEAF_STRIDE];
    let mut iv0 = vec![F128::ZERO; CAPSULE_LEAF_STRIDE];
    let mut iv1 = vec![F128::ZERO; CAPSULE_LEAF_STRIDE];
    iv0[0] = iv_flat[0];
    iv1[0] = iv_flat[1];
    for slot in 1..CAPSULE_LEAF_SLOTS {
        carry[slot] = F128::ONE;
    }
    vec![
        FixedPattern::new(low_log, carry),
        FixedPattern::new(low_log, iv0),
        FixedPattern::new(low_log, iv1),
    ]
}

/// Wiring substitution `Σ_j m_j·raw_j(w)` for the α-batched walk terminal.
/// The carry is uniformly one slot back (each symbol block feeds off the
/// previous permutation's full output):
///
/// ```text
///   raw_0 = IN0      + CARRY·C0(w−1)
///   raw_1 = IN1      + CARRY·C1(w−1)
///   raw_2 = IV0_pat  + CARRY·C2(w−1)
///   raw_3 = IV1_pat  + CARRY·C3(w−1)
/// ```
///
/// At slot 0 `CARRY = 0`: `raw = [msg_log, leaf_index, iv0, iv1]` (the fresh
/// sponge absorb on the IV capacity). At slots 1..=8 the IV patterns are
/// zero: `raw = [sym_a + C0(w−1), sym_b + C1(w−1), C2(w−1), C3(w−1)]` (the
/// duplex feed-forward absorbing two symbols). At ghost slots every term is
/// zero: `raw = 0`.
pub fn capsule_leaf_substitution_terms(refs: &CapsuleLeafRefs, alpha: F128) -> Vec<RelationTerm> {
    let m = mds_weights_pub(alpha);
    let mut terms = Vec::new();
    // Rate lanes 0/1: the absorbed block read plainly + the carry-gated feed.
    for i in 0..2 {
        terms.push(RelationTerm {
            coeff: m[i],
            factors: vec![ColRef::Committed(refs.in_[i])],
        });
        terms.push(RelationTerm {
            coeff: m[i],
            factors: vec![ColRef::Fixed(refs.carry), ColRef::CommittedShift(refs.c[i])],
        });
    }
    // Capacity lanes 2/3: the slot-0 IV pattern + the carry-gated feed.
    for j in 2..STATE_SIZE {
        terms.push(RelationTerm {
            coeff: m[j],
            factors: vec![ColRef::Fixed(refs.iv[j - 2])],
        });
        terms.push(RelationTerm {
            coeff: m[j],
            factors: vec![ColRef::Fixed(refs.carry), ColRef::CommittedShift(refs.c[j])],
        });
    }
    terms
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::Poseidon2bFlatSponge;

    fn next_f128(seed: &mut u64) -> F128 {
        *seed = seed.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = *seed;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z ^= z >> 31;
        F128 {
            lo: z,
            hi: z.rotate_left(23),
        }
    }

    /// The native flat sponge over the leaf schedule, digest as raw flat
    /// lanes — the oracle the family replays.
    fn native_leaf_digest(msg_log: usize, leaf_index: usize, syms: &[F128]) -> [F128; 2] {
        let mut sponge = Poseidon2bFlatSponge::with_tag(TAG_CAPSLEAF);
        sponge.update(&(msg_log as u128).to_le_bytes());
        sponge.update(&(leaf_index as u128).to_le_bytes());
        for s in syms {
            let v = ((s.hi as u128) << 64) | s.lo as u128;
            sponge.update(&v.to_le_bytes());
        }
        let d = sponge.finalize_no_pad();
        [
            raw_flat_lane(u128::from_le_bytes(d[..16].try_into().unwrap())),
            raw_flat_lane(u128::from_le_bytes(d[16..].try_into().unwrap())),
        ]
    }

    fn native_c1_digest(kind: C1CapsuleLeafKind, lanes: &[F128]) -> [F128; 2] {
        let tag = match kind {
            C1CapsuleLeafKind::MixedSource => TAG_CAPSMIX,
            C1CapsuleLeafKind::WideMid => TAG_CAPS256,
        };
        let mut sponge = Poseidon2bFlatSponge::with_tag(tag);
        for lane in lanes {
            let value = ((lane.hi as u128) << 64) | lane.lo as u128;
            sponge.update(&value.to_le_bytes());
        }
        let digest = sponge.finalize_no_pad();
        [
            raw_flat_lane(u128::from_le_bytes(digest[..16].try_into().unwrap())),
            raw_flat_lane(u128::from_le_bytes(digest[16..].try_into().unwrap())),
        ]
    }

    /// Column replay == the native flat sponge (both the scalar replay and
    /// the tiled columns), including a ghost tile past the real leaves.
    #[test]
    fn capsule_leaf_columns_match_native_sponge() {
        let mut seed = 0xCA95u64;
        let leaves: Vec<CapsuleLeafData> = (0..3)
            .map(|t| CapsuleLeafData {
                msg_log: 9,
                leaf_index: 5 * t + 1,
                syms: std::array::from_fn(|_| next_f128(&mut seed)),
            })
            .collect();
        let w_log = 6; // 4 tiles of 16 slots: 3 real + 1 ghost
        let (cols, digests) = build_capsule_leaf_columns(&leaves, w_log);
        assert_eq!(digests.len(), leaves.len());
        for (t, leaf) in leaves.iter().enumerate() {
            let native = native_leaf_digest(leaf.msg_log, leaf.leaf_index, &leaf.syms);
            assert_eq!(digests[t], native, "tile {t} digest vs native sponge");
            assert_eq!(
                flat_capsule_leaf_hash(leaf.msg_log, leaf.leaf_index, &leaf.syms),
                native,
                "scalar replay vs native sponge"
            );
            let d = CAPSULE_LEAF_STRIDE * t + CAPSULE_LEAF_DIGEST_SLOT;
            assert_eq!([cols.c[0][d], cols.c[1][d]], native, "column digest slot");
        }
        // The ghost tile is the canonical all-zero leaf, a real sponge run.
        let ghost_native = native_leaf_digest(0, 0, &[F128::ZERO; CAPSULE_LEAF_SYMBOLS]);
        let gd = CAPSULE_LEAF_STRIDE * 3 + CAPSULE_LEAF_DIGEST_SLOT;
        assert_eq!(
            [cols.c[0][gd], cols.c[1][gd]],
            ghost_native,
            "ghost tile digest"
        );
    }

    #[test]
    fn c1_fixed_shape_columns_match_native_sponges() {
        let mut seed = 0xC1A5_5EEDu64;
        for kind in [C1CapsuleLeafKind::MixedSource, C1CapsuleLeafKind::WideMid] {
            let leaves = (0..3)
                .map(|_| C1CapsuleLeafData {
                    lanes: (0..kind.lane_count())
                        .map(|_| next_f128(&mut seed))
                        .collect(),
                })
                .collect::<Vec<_>>();
            let (columns, digests) = build_c1_capsule_leaf_columns(&leaves, kind, 6);
            for (tile, leaf) in leaves.iter().enumerate() {
                let native = native_c1_digest(kind, &leaf.lanes);
                assert_eq!(flat_c1_capsule_leaf_hash(kind, &leaf.lanes), native);
                assert_eq!(digests[tile], native);
                let digest_slot = tile * C1_CAPSULE_LEAF_STRIDE + kind.active_slots() - 1;
                assert_eq!(
                    [columns.c[0][digest_slot], columns.c[1][digest_slot]],
                    native
                );
            }
            if kind == C1CapsuleLeafKind::MixedSource {
                for tile in 0..4 {
                    for slot in C1_CAPSULE_SOURCE_SLOTS..C1_CAPSULE_LEAF_STRIDE {
                        let physical = tile * C1_CAPSULE_LEAF_STRIDE + slot;
                        assert_eq!(columns.in_[0][physical], F128::ZERO);
                        assert_eq!(columns.in_[1][physical], F128::ZERO);
                    }
                }
            }
        }
    }
}
