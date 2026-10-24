// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Shared PCS trace primitives used by the region wallet-PCS discharge:
//!
//! - [`packed_capsule_queries_from_seeds_with_bits`] — the production capsule
//!   query rule on PRE-SQUEEZED seed wires (the region path reads them from
//!   walk-C carry cells). Every seed decomposes into all 128 tower bits
//!   (booleanity-pinned, φ-weighted sum pinned to the wire); the concatenated
//!   stream is split into independent query positions. The older one-position
//!   [`compact_queries_from_squeezes_with_bits`] primitive remains for grind
//!   and focused trace uses.
//! - [`forward_ntt_trace`] — the additive-NTT butterfly network with
//!   constant basis twiddles: F128-linear, pure `LinExpr` algebra
//!   (0 constraints). The capsule-rate encode twin is built on it.
//! - [`mle_evaluate_small_trace`] — the highest-variable MLE fold loop
//!   (`2^n − 1` multiplications) for small tables.

use noid_core::hardware::flat_to_tower_u128;
use noid_core::Block128;
use noid_fri_binius::capsule::{
    capsule_query_bit_location, CAPSULE_NUM_QUERIES, CAPSULE_QUERY_SEED_BITS,
};

use super::{flat_const, mul, pin_zero, FieldR1csBuilder, LinExpr};

/// The native TOWER value of a trace expression (fixture/bookkeeping only —
/// never a constraint).
pub fn expr_tower_value(b: &FieldR1csBuilder, e: &LinExpr) -> Block128 {
    let f = e.eval(b.values());
    let flat = (f.lo as u128) | ((f.hi as u128) << 64);
    Block128(flat_to_tower_u128(flat))
}

/// The query-index rule driven from PRE-SQUEEZED challenge wires.
/// `squeezes.len()` must be the already-clamped query count (exactly the
/// channel schedule's `Squeeze(query_count)` op — every squeeze becomes one
/// query). Position derivation is byte-identical to the native
/// `e.0 & ((1 << log_max_len) − 1)` rule.
pub fn compact_queries_from_squeezes_with_bits(
    b: &mut FieldR1csBuilder,
    squeezes: &[LinExpr],
    log_max_len: usize,
) -> (Vec<usize>, Vec<Vec<LinExpr>>) {
    assert!(log_max_len < usize::BITS as usize);
    let mut indices = Vec::with_capacity(squeezes.len());
    let mut all_bits = Vec::with_capacity(squeezes.len());
    for e in squeezes {
        let (idx, bits) = decompose_query_squeeze(b, e, log_max_len);
        indices.push(idx);
        all_bits.push(bits);
    }
    (indices, all_bits)
}

/// Packed capsule query rule on pre-squeezed seed wires.
///
/// Every seed is fully decomposed and rebound to its channel wire once. The
/// resulting 128-bit streams are concatenated LSB-first and split into
/// `CAPSULE_NUM_QUERIES` consecutive `log_max_len`-bit positions using the
/// protocol-owned mapping helpers. Thus release OwnerAuth pays seven complete
/// decompositions for 64 independent 14-bit queries instead of discarding 114
/// bits from each of 64 squeezes.
pub fn packed_capsule_queries_from_seeds_with_bits(
    b: &mut FieldR1csBuilder,
    seeds: &[LinExpr],
    log_max_len: usize,
) -> (Vec<usize>, Vec<Vec<LinExpr>>) {
    packed_capsule_queries_from_seeds_with_bound_bits(b, seeds, log_max_len, None)
}

/// Packed capsule query rule with an optional committed-cell carrier for
/// selected query bits.
///
/// `bound_query_bits[q][i] = Some(cell)` makes the seed recomposition consume
/// that expression directly instead of allocating a duplicate boolean wire.
/// The caller MUST separately prove every supplied expression boolean. The
/// recomposition still binds it exactly to the transcript seed, so this only
/// removes duplicate storage/pointwise equality rows; it does not weaken the
/// query derivation.
///
/// The active capsule's cfg-selected [`CAPSULE_NUM_QUERIES`] is authoritative;
/// the optional carrier matrix cannot change verifier shape. Fixed-count
/// protocol candidates use
/// [`packed_queries_from_seeds_with_bound_bits_for_count`] explicitly.
pub fn packed_capsule_queries_from_seeds_with_bound_bits(
    b: &mut FieldR1csBuilder,
    seeds: &[LinExpr],
    log_max_len: usize,
    bound_query_bits: Option<&[Vec<Option<LinExpr>>]>,
) -> (Vec<usize>, Vec<Vec<LinExpr>>) {
    packed_queries_from_seeds_with_bound_bits_for_count(
        b,
        seeds,
        CAPSULE_NUM_QUERIES,
        log_max_len,
        bound_query_bits,
    )
}

/// Explicit-count packed query binding for disconnected, fixed-shape protocol
/// candidates.
///
/// Unlike [`packed_capsule_queries_from_seeds_with_bound_bits`], this helper
/// does not inherit the active capsule's debug/release query-count cfg. The
/// caller must pass a protocol constant and the optional carrier matrix must
/// have exactly that many rows; witness data cannot choose the count.
pub fn packed_queries_from_seeds_with_bound_bits_for_count(
    b: &mut FieldR1csBuilder,
    seeds: &[LinExpr],
    query_count: usize,
    log_max_len: usize,
    bound_query_bits: Option<&[Vec<Option<LinExpr>>]>,
) -> (Vec<usize>, Vec<Vec<LinExpr>>) {
    assert!(log_max_len > 0, "capsule query width must be non-zero");
    assert!(
        log_max_len <= usize::BITS as usize,
        "capsule query width exceeds usize"
    );
    assert!(query_count > 0, "packed capsule query count");
    let packed_seed_count = query_count
        .checked_mul(log_max_len)
        .expect("packed capsule query bit count")
        .div_ceil(CAPSULE_QUERY_SEED_BITS);
    assert_eq!(
        seeds.len(),
        packed_seed_count,
        "packed capsule query seed count"
    );
    if let Some(bound) = bound_query_bits {
        assert_eq!(bound.len(), query_count, "bound query count");
        assert!(
            bound.iter().all(|query| query.len() == log_max_len),
            "bound query bit width"
        );
    }
    let native_seeds = seeds
        .iter()
        .map(|seed| expr_tower_value(b, seed))
        .collect::<Vec<_>>();
    let indices = (0..query_count)
        .map(|query| {
            (0..log_max_len).fold(0usize, |index, query_bit| {
                let (seed, bit) = capsule_query_bit_location(query, query_bit, log_max_len);
                index | ((((native_seeds[seed].0 >> bit) & 1) as usize) << query_bit)
            })
        })
        .collect::<Vec<_>>();

    let mut carried_seed_bits = vec![vec![None; CAPSULE_QUERY_SEED_BITS]; seeds.len()];
    if let Some(bound) = bound_query_bits {
        for (query, query_bits) in bound.iter().enumerate() {
            for (query_bit, carried) in query_bits.iter().enumerate() {
                let Some(carried) = carried else { continue };
                let (seed, bit) = capsule_query_bit_location(query, query_bit, log_max_len);
                assert!(
                    carried_seed_bits[seed][bit].is_none(),
                    "two carriers assigned to seed {seed} bit {bit}"
                );
                carried_seed_bits[seed][bit] = Some(carried.clone());
            }
        }
    }

    let seed_bits = seeds
        .iter()
        .enumerate()
        .map(|(seed_index, seed)| {
            decompose_squeeze_bits_with_carriers(b, seed, &carried_seed_bits[seed_index]).1
        })
        .collect::<Vec<_>>();
    let all_bits = (0..query_count)
        .map(|query| {
            (0..log_max_len)
                .map(|query_bit| {
                    let (seed, bit) = capsule_query_bit_location(query, query_bit, log_max_len);
                    seed_bits[seed][bit].clone()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    debug_assert!(seed_bits
        .iter()
        .all(|bits| bits.len() == CAPSULE_QUERY_SEED_BITS));

    for (query, bits) in all_bits.iter().enumerate() {
        let reconstructed = bits.iter().enumerate().fold(0usize, |acc, (bit, wire)| {
            acc | (usize::from(wire.eval(b.values()) != noid_ivc_core::field::F128::ZERO) << bit)
        });
        assert_eq!(reconstructed, indices[query], "packed query {query}");
    }
    (indices, all_bits)
}

/// Decompose one squeezed challenge wire `e` into its query index (low
/// `log_max_len` bits of the tower value) and the low `log_max_len` position
/// bits as witness wires (LSB first). Decomposes ALL 128 bits into booleans
/// (not just the high bits past the mask): baking the low position bits as
/// `add_const` constants would put the query position into the pinning row's
/// constant term and drift the matrix across blocks. `pin_zero(sum + e)` binds
/// the decomposition to the squeeze; booleanity pins each bit.
fn decompose_query_squeeze(
    b: &mut FieldR1csBuilder,
    e: &LinExpr,
    log_max_len: usize,
) -> (usize, Vec<LinExpr>) {
    let bit_mask = ((1u128 << log_max_len) - 1) as u128;
    let (tower, all_bits) = decompose_squeeze_bits(b, e);
    let idx = (tower & bit_mask) as usize;
    (idx, all_bits[..log_max_len].to_vec())
}

/// Fully decompose one tower-basis field wire and constrain its exact
/// recomposition. The returned bits are LSB-first in the native `Block128`
/// representation used by the capsule query sampler.
fn decompose_squeeze_bits(b: &mut FieldR1csBuilder, e: &LinExpr) -> (u128, Vec<LinExpr>) {
    let empty = vec![None; CAPSULE_QUERY_SEED_BITS];
    decompose_squeeze_bits_with_carriers(b, e, &empty)
}

/// Fully decompose one seed while reusing caller-provided, separately
/// booleanity-proven expressions at selected bit positions.
fn decompose_squeeze_bits_with_carriers(
    b: &mut FieldR1csBuilder,
    e: &LinExpr,
    carriers: &[Option<LinExpr>],
) -> (u128, Vec<LinExpr>) {
    assert_eq!(carriers.len(), CAPSULE_QUERY_SEED_BITS);
    let tower = expr_tower_value(b, e).0;
    let mut sum = LinExpr::zero();
    let mut bits = Vec::with_capacity(CAPSULE_QUERY_SEED_BITS);
    for i in 0..CAPSULE_QUERY_SEED_BITS {
        let bit = carriers[i]
            .clone()
            .unwrap_or_else(|| LinExpr::from_wire(b.alloc_bool((tower >> i) & 1 == 1)));
        sum = sum.add(&bit.scale(flat_const(1u128 << i)));
        bits.push(bit);
    }
    pin_zero(b, &sum.add(e));
    (tower, bits)
}

/// Trace twin of `noid_core::ntt::forward_ntt` over expressions. The
/// butterflies are affine with constant basis twiddles — 0 constraints.
pub fn forward_ntt_trace(coeffs: &[LinExpr], basis: &[Block128]) -> Vec<LinExpr> {
    let n = coeffs.len();
    assert!(n.is_power_of_two());
    assert_eq!(basis.len(), n.trailing_zeros() as usize);
    let mut evals = coeffs.to_vec();
    let mut len = 1usize;
    for &bb in basis.iter() {
        let b_flat = flat_const(bb.0);
        for start in (0..n).step_by(2 * len) {
            for i in start..start + len {
                let u = evals[i].clone();
                let v = evals[i + len].clone();
                let sum = u.add(&v);
                evals[i] = sum.clone();
                evals[i + len] = sum.scale(b_flat).add(&v);
            }
        }
        len *= 2;
    }
    evals
}

/// Trace twin of the highest-variable MLE fold loop for small tables
/// (`2^n − 1` multiplications).
pub fn mle_evaluate_small_trace(
    b: &mut FieldR1csBuilder,
    evals: &[LinExpr],
    point: &[LinExpr],
) -> LinExpr {
    if point.is_empty() {
        return evals[0].clone();
    }
    let mut buf = evals.to_vec();
    for r in point.iter().rev() {
        let half = buf.len() / 2;
        for i in 0..half {
            let diff = buf[i].add(&buf[i + half]);
            buf[i] = buf[i].add(&mul(b, r, &diff));
        }
        buf.truncate(half);
    }
    buf[0].clone()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::super::alloc_blocks;
    use super::super::test_support::assert_expr_is;
    use super::*;
    use noid_core::AdditiveNTT;
    use noid_fri_binius::capsule::{capsule_queries_from_seeds, capsule_query_seed_count};

    struct Rng(u128);
    impl Rng {
        fn next_u128(&mut self) -> u128 {
            self.0 = self
                .0
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add(0xB5AD_4ECE_DA1C_E2A9);
            self.0
        }
        fn next_block(&mut self) -> Block128 {
            Block128::from(self.next_u128())
        }
    }

    /// The pre-squeezed query decomposition reproduces the native
    /// `e.0 & mask` index rule, its 128-bit recomposition pins to the wire,
    /// and the returned low bits equal the index's binary digits.
    #[test]
    fn queries_from_squeezes_match_native_mask_rule() {
        let mut rng = Rng(0x9E37);
        let log_max_len = 14usize;
        let squeezed: Vec<Block128> = (0..8).map(|_| rng.next_block()).collect();
        let mut b = FieldR1csBuilder::new();
        let wires = alloc_blocks(&mut b, &squeezed);
        let (indices, bits) = compact_queries_from_squeezes_with_bits(&mut b, &wires, log_max_len);
        for (q, e) in squeezed.iter().enumerate() {
            let native = (e.0 & ((1u128 << log_max_len) - 1)) as usize;
            assert_eq!(indices[q], native, "query {q} index");
            for (i, bit) in bits[q].iter().enumerate() {
                let v = bit.eval(b.values());
                let expect = (native >> i) & 1 == 1;
                assert_eq!(
                    v != noid_ivc_core::field::F128::ZERO,
                    expect,
                    "query {q} bit {i}"
                );
            }
        }
        let (r1cs, z) = b.build();
        assert!(r1cs.satisfies(&z), "honest decomposition satisfies");
    }

    #[test]
    fn packed_capsule_seed_bits_match_native_query_mapping() {
        let log_max_len = 9 + noid_fri_binius::capsule::CAPSULE_LOG_RATE;
        let native = (0..capsule_query_seed_count(log_max_len))
            .map(|seed| {
                Block128::from(
                    (0x9E37_79B9_7F4A_7C15u128.wrapping_mul(seed as u128 + 1))
                        ^ ((seed as u128 + 0xA5) << 79),
                )
            })
            .collect::<Vec<_>>();
        let expected = capsule_queries_from_seeds(&native, log_max_len);
        let mut b = FieldR1csBuilder::new();
        let seeds = alloc_blocks(&mut b, &native);
        let before = b.num_wires();
        let (indices, bits) =
            packed_capsule_queries_from_seeds_with_bits(&mut b, &seeds, log_max_len);
        assert_eq!(indices, expected);
        assert_eq!(bits.len(), CAPSULE_NUM_QUERIES);
        assert!(bits.iter().all(|query| query.len() == log_max_len));
        assert_eq!(
            b.num_wires() - before,
            capsule_query_seed_count(log_max_len) * (CAPSULE_QUERY_SEED_BITS + 1),
            "one full decomposition and recomposition pin per seed"
        );
        let first_bit_wire = bits[0][0].terms[0].0 as usize;
        let (r1cs, witness) = b.build();
        assert!(r1cs.satisfies(&witness));
        let mut bad = witness.clone();
        bad[first_bit_wire] += noid_ivc_core::field::F128::ONE;
        assert!(
            !r1cs.satisfies(&bad),
            "query bit must remain bound to its seed wire"
        );

        let alternate = native
            .iter()
            .enumerate()
            .map(|(i, seed)| Block128::from(seed.0 ^ ((i as u128 + 1) << 37) ^ 1))
            .collect::<Vec<_>>();
        let mut b2 = FieldR1csBuilder::new();
        let seeds2 = alloc_blocks(&mut b2, &alternate);
        let _ = packed_capsule_queries_from_seeds_with_bits(&mut b2, &seeds2, log_max_len);
        let (r1cs2, witness2) = b2.build();
        assert!(r1cs2.satisfies(&witness2));
        assert_eq!(
            r1cs.statement_digest(),
            r1cs2.statement_digest(),
            "packed query mapping must be content-invariant"
        );
    }

    #[test]
    fn packed_capsule_seed_bits_reuse_separately_boolean_carriers() {
        let log_max_len = 9 + noid_fri_binius::capsule::CAPSULE_LOG_RATE;
        let native = (0..capsule_query_seed_count(log_max_len))
            .map(|seed| Block128::from(0xD15C_A11Eu128.rotate_left(seed as u32 * 7)))
            .collect::<Vec<_>>();
        let expected = capsule_queries_from_seeds(&native, log_max_len);
        let mut b = FieldR1csBuilder::new();
        let seeds = alloc_blocks(&mut b, &native);
        let mut bound = vec![vec![None; log_max_len]; CAPSULE_NUM_QUERIES];
        for bit in 0..log_max_len {
            bound[0][bit] = Some(LinExpr::from_wire(
                b.alloc_bool((expected[0] >> bit) & 1 == 1),
            ));
        }
        let before = b.num_wires();
        let (indices, bits) = packed_capsule_queries_from_seeds_with_bound_bits(
            &mut b,
            &seeds,
            log_max_len,
            Some(&bound),
        );
        assert_eq!(indices, expected);
        assert_eq!(
            bits[0],
            bound[0]
                .iter()
                .cloned()
                .map(Option::unwrap)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            b.num_wires() - before,
            capsule_query_seed_count(log_max_len) * (CAPSULE_QUERY_SEED_BITS + 1) - log_max_len,
            "each carried bit removes one duplicate boolean wire"
        );
        let (r1cs, witness) = b.build();
        assert!(r1cs.satisfies(&witness));
    }

    /// The NTT twin reproduces `AdditiveNTT::forward_transform` for a
    /// shifted-basis window (the capsule-encode window form).
    #[test]
    fn forward_ntt_trace_matches_native_window() {
        let log_n = 4usize;
        let mut rng = Rng(7);
        let msg: Vec<Block128> = (0..1usize << log_n).map(|_| rng.next_block()).collect();
        let ntt = AdditiveNTT::<Block128>::new(log_n + 5);
        for round in [0u32, 3, 17] {
            let mut native = msg.clone();
            ntt.forward_transform(&mut native, round, 0);
            let mut b = FieldR1csBuilder::new();
            let msg_e = alloc_blocks(&mut b, &msg);
            let basis: Vec<Block128> = (round as usize..round as usize + log_n)
                .map(|i| Block128::from(1u128 << i))
                .collect();
            let enc = forward_ntt_trace(&msg_e, &basis);
            for (e, nv) in enc.iter().zip(native.iter()) {
                assert_expr_is(&b, e, *nv, "window symbol");
            }
        }
    }

    #[test]
    fn mle_evaluate_small_trace_matches_native() {
        let mut rng = Rng(31);
        for n in [0usize, 1, 3, 5] {
            let evals: Vec<Block128> = (0..1usize << n).map(|_| rng.next_block()).collect();
            let point: Vec<Block128> = (0..n).map(|_| rng.next_block()).collect();
            let mut buf = evals.clone();
            for &r in point.iter().rev() {
                let half = buf.len() / 2;
                for i in 0..half {
                    buf[i] = buf[i] + r * (buf[i] + buf[i + half]);
                }
                buf.truncate(half);
            }
            let native = buf[0];

            let mut b = FieldR1csBuilder::new();
            let evals_e = alloc_blocks(&mut b, &evals);
            let point_e = alloc_blocks(&mut b, &point);
            let got = mle_evaluate_small_trace(&mut b, &evals_e, &point_e);
            assert_expr_is(&b, &got, native, "mle_evaluate_small");
            let (r1cs, z) = b.build();
            assert!(r1cs.satisfies(&z));
        }
    }
}
