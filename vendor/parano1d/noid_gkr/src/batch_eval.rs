// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

#![allow(clippy::needless_range_loop)]

//! Batch-evaluation sumcheck.
//!
//! Reduces `M` MLE-evaluation claims `(r_i, v_i)` on a **single**
//! multilinear polynomial `B` of length `2^n` to one point-value pair
//! `(r_B, v_B)` via a standard RLC + degree-2 sumcheck:
//!
//! ```text
//!   V := Σ_i α_i · v_i  with  α_i ← channel.squeeze()
//!   W(x) := Σ_i α_i · eq(r_i, x)
//!   H(x) := W(x) · B(x)
//!
//!   V == Σ_x H(x)   (by linearity of eq)
//!
//!   sumcheck H over n variables → (r_B, claim_B)
//!   verifier checks  claim_B == W(r_B) · v_B_claimed
//! ```
//!
//! Soundness: W(r_B) is recomputed by the verifier as
//! `Σ_i α_i · eq(r_i, r_B)`. `v_B = B(r_B)` is the reduced claim that
//! the caller discharges through either native differential checks or the
//! composed recursive batch relation.
//!
//! Why a fresh primitive rather than the old per-slot degree-3 product
//! sumcheck: the per-slot prover folded in an extra `eq(r, x)` factor
//! (degree 3 per variable). Here the outer eq has been absorbed into
//! `W`, so `H = W · B` is degree 2 per variable, one less round
//! polynomial coefficient per round.

use std::sync::OnceLock;

use noid_core::mle::eq::eq_ind;

use noid_core::transcript::FiatShamir;
use noid_core::{Block128, TowerField};
use rayon::prelude::*;
use zeroize::Zeroize;

/// Inverse Lagrange denominators at `{0,1,2}`. Cached so per-round
/// `evaluate` is invert-free in the hot path.
fn denom_inv_3() -> &'static [Block128; 3] {
    static CACHE: OnceLock<[Block128; 3]> = OnceLock::new();
    CACHE.get_or_init(|| {
        let mut out = [Block128::ZERO; 3];
        for k in 0..3 {
            let xk = Block128::from(k as u128);
            let mut d = Block128::ONE;
            for j in 0..3 {
                if j == k {
                    continue;
                }
                d *= xk + Block128::from(j as u128);
            }
            out[k] = d.invert();
        }
        out
    })
}

const PAR_THRESHOLD: usize = 64;

/// One round of the degree-2 batch-eval sumcheck, stored COMPRESSED as its
/// evaluations at `X = 1, 2`. The evaluation at 0 is derivable from the
/// running claim — `p(0) + p(1) = claim` in characteristic 2 — so shipping
/// or absorbing it bound nothing, and reconstructing it makes the
/// per-round sum check true by construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BatchEvalRound {
    pub evals_at_1_2: [Block128; 2],
}

impl BatchEvalRound {
    /// Reconstruct `p(0)` from the running claim: `p(0) = claim + p(1)`.
    #[inline]
    pub fn eval_at_0(&self, claim: Block128) -> Block128 {
        claim + self.evals_at_1_2[0]
    }

    /// Lagrange-interpolate at `r`, reconstructing `p(0)` from the claim.
    pub fn evaluate(&self, claim: Block128, r: Block128) -> Block128 {
        let evals = [
            self.eval_at_0(claim),
            self.evals_at_1_2[0],
            self.evals_at_1_2[1],
        ];
        lagrange_at_0_1_2(&evals, r)
    }
}

/// Lagrange evaluation at a single point from evals at `{0,1,2}`. Uses
/// the cached denominator inverses in `denom_inv_3()` so the hot path
/// is invert-free.
#[inline]
pub fn lagrange_at_0_1_2(evals: &[Block128; 3], r: Block128) -> Block128 {
    let denom_inv = denom_inv_3();
    let r0 = r + Block128::from(0u128);
    let r1 = r + Block128::from(1u128);
    let r2 = r + Block128::from(2u128);
    let n0 = r1 * r2;
    let n1 = r0 * r2;
    let n2 = r0 * r1;
    evals[0] * n0 * denom_inv[0] + evals[1] * n1 * denom_inv[1] + evals[2] * n2 * denom_inv[2]
}

/// One `(r, v)` MLE-evaluation claim on the shared target MLE `B`.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct EvalClaim {
    pub point: Vec<Block128>,
    pub value: Block128,
}

/// Proof object: one round poly per sumcheck variable plus the final
/// reduced `(r_B, v_B)` is derived by the verifier from the transcript
/// and the last round's final claim, so only the round polys and the
/// prover's `b_final` need to ship.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BatchEvalProof {
    pub rounds: Vec<BatchEvalRound>,
    /// `b_final = B(r_B)`. Verifier cross-checks against
    /// `final_claim / W(r_B)`; caller discharges this against the
    /// committed `B`.
    pub b_final: Block128,
}

impl BatchEvalProof {
    /// Raw field-element byte size: `rounds.len() * 3` degree-2 round
    /// evals plus `b_final`, 16 bytes each.
    pub fn byte_len(&self) -> usize {
        self.rounds.len() * 2 * 16 + 16
    }
}

/// Multi-column batch-evaluation sumcheck.
///
/// Reduces claim sets over several committed MLE columns to one shared terminal
/// point and one final value per column. This is used by Auth Capsule to close
/// `state`, `s_in`, and `s_out` with one sumcheck and one PCS opening instead
/// of three independent openings.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MultiBatchEvalProof {
    pub rounds: Vec<BatchEvalRound>,
    pub b_finals: Vec<Block128>,
}

impl MultiBatchEvalProof {
    /// Raw field-element byte size: `rounds.len() * 3` degree-2 round evals
    /// plus one terminal column value per batched column.
    pub fn byte_len(&self) -> usize {
        self.rounds.len() * 2 * 16 + self.b_finals.len() * 16
    }
}

/// Output of a successful verify.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BatchEvalReduction {
    /// `r_B` — the sumcheck's terminal point, in variable order.
    pub point: Vec<Block128>,
    /// `v_B = B(r_B)` as claimed by the prover and telescope-consistent.
    pub value: Block128,
}

/// One term in a public linear relation over a committed MLE.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearEvalTerm {
    pub point: Vec<Block128>,
    pub coeff: Block128,
}

/// Public linear relation:
///
/// ```text
/// Σ_j coeff_j * B(point_j) == value
/// ```
///
/// The proof reduces many such relations to one terminal claim on `B`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearEvalClaim {
    pub terms: Vec<LinearEvalTerm>,
    pub value: Block128,
}

/// Sumcheck proof for a set of linear relations over one committed MLE.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LinearEvalProof {
    pub rounds: Vec<BatchEvalRound>,
    pub b_final: Block128,
}

impl LinearEvalProof {
    pub fn byte_len(&self) -> usize {
        self.rounds.len() * 2 * 16 + 16
    }
}

enum LinearEvalBinding {
    Explicit,
    Prebound { relation_tag: u128 },
}

/// Flat-basis fold: folds a `Vec<u128>` table in place using `clmul_gcm` (~4 ns/mul).
/// ~7x faster than the tower-basis `fold_highest_var_par`.
fn fold_flat(tbl: &mut Vec<u128>, r_flat: u128) {
    fold_flat_inner(tbl, r_flat, false);
}

/// Same fold, but wipes the discarded high half before truncating. Use this for
/// secret-derived target tables: `Vec::truncate` alone would leave stale `u128`
/// limbs in the allocation backing store.
fn fold_flat_zeroing_truncated(tbl: &mut Vec<u128>, r_flat: u128) {
    fold_flat_inner(tbl, r_flat, true);
}

fn fold_flat_inner(tbl: &mut Vec<u128>, r_flat: u128, zeroize_truncated: bool) {
    use noid_core::hardware::clmul_gcm;
    let half = tbl.len() / 2;
    if half >= 1024 {
        let (lo, hi) = tbl.split_at_mut(half);
        lo.par_iter_mut().zip(hi.par_iter()).for_each(|(l, &h)| {
            *l ^= clmul_gcm(r_flat, *l ^ h);
        });
    } else {
        for j in 0..half {
            tbl[j] ^= clmul_gcm(r_flat, tbl[j] ^ tbl[j + half]);
        }
    }
    if zeroize_truncated {
        tbl[half..].zeroize();
    }
    tbl.truncate(half);
}

/// Build `W(x)` table in flat (GCM) basis using clmul_gcm — ~7x faster
/// than the tower-basis version.
fn build_w_table_flat(claims: &[EvalClaim], alphas: &[Block128], n: usize) -> Vec<u128> {
    use noid_core::hardware::{clmul_gcm, tower_to_flat_u128};
    debug_assert_eq!(claims.len(), alphas.len());
    let len = 1usize << n;

    let mut out = vec![0u128; len];
    let mut dense_claims = Vec::new();
    let mut dense_alphas = Vec::new();
    for (claim, &alpha) in claims.iter().zip(alphas.iter()) {
        if let Some(index) = boolean_point_index(&claim.point) {
            out[index] ^= tower_to_flat_u128(alpha.0);
        } else {
            dense_claims.push(claim);
            dense_alphas.push(alpha);
        }
    }

    if dense_claims.is_empty() {
        return out;
    }

    let dense = dense_claims
        .par_iter()
        .zip(dense_alphas.par_iter())
        .map(|(claim, &alpha)| {
            let alpha_flat = tower_to_flat_u128(alpha.0);
            let point_flat: Vec<u128> = claim
                .point
                .iter()
                .map(|v| tower_to_flat_u128(v.0))
                .collect();
            let mut eq: Vec<u128> = Vec::with_capacity(len);
            eq.push(alpha_flat);
            for &r_flat in &point_flat {
                let cur = eq.len();
                for j in 0..cur {
                    let prod = clmul_gcm(eq[j], r_flat);
                    eq[j] ^= prod; // subtraction = addition in char 2
                    eq.push(prod);
                }
            }
            debug_assert_eq!(eq.len(), len);
            eq
        })
        .reduce(
            || vec![0u128; len],
            |mut a, b| {
                a.iter_mut().zip(b.iter()).for_each(|(ai, bi)| *ai ^= bi);
                a
            },
        );
    out.iter_mut()
        .zip(dense.iter())
        .for_each(|(out_i, dense_i)| *out_i ^= *dense_i);
    out
}

fn build_linear_w_table_flat(
    claims: &[LinearEvalClaim],
    alphas: &[Block128],
    n: usize,
) -> Vec<u128> {
    use noid_core::hardware::{clmul_gcm, tower_to_flat_u128};
    debug_assert_eq!(claims.len(), alphas.len());
    let len = 1usize << n;

    let mut out = vec![0u128; len];
    let mut dense_terms = Vec::<(&LinearEvalTerm, Block128)>::new();

    for (claim, &alpha) in claims.iter().zip(alphas.iter()) {
        for term in &claim.terms {
            let weighted = alpha * term.coeff;
            if let Some(index) = boolean_point_index(&term.point) {
                out[index] ^= tower_to_flat_u128(weighted.0);
            } else {
                dense_terms.push((term, weighted));
            }
        }
    }

    if dense_terms.is_empty() {
        return out;
    }

    let dense = dense_terms
        .par_iter()
        .map(|(term, weighted)| {
            let weighted_flat = tower_to_flat_u128(weighted.0);
            let point_flat: Vec<u128> =
                term.point.iter().map(|v| tower_to_flat_u128(v.0)).collect();
            let mut eq: Vec<u128> = Vec::with_capacity(len);
            eq.push(weighted_flat);
            for &r_flat in &point_flat {
                let cur = eq.len();
                for j in 0..cur {
                    let prod = clmul_gcm(eq[j], r_flat);
                    eq[j] ^= prod;
                    eq.push(prod);
                }
            }
            debug_assert_eq!(eq.len(), len);
            eq
        })
        .reduce(
            || vec![0u128; len],
            |mut a, b| {
                a.iter_mut().zip(b.iter()).for_each(|(ai, bi)| *ai ^= bi);
                a
            },
        );
    out.iter_mut()
        .zip(dense.iter())
        .for_each(|(out_i, dense_i)| *out_i ^= *dense_i);
    out
}

fn boolean_point_index(point: &[Block128]) -> Option<usize> {
    let mut index = 0usize;
    for (bit, value) in point.iter().enumerate() {
        if *value == Block128::ONE {
            index |= 1usize << bit;
        } else if *value != Block128::ZERO {
            return None;
        }
    }
    Some(index)
}

/// Flat-basis round polynomial evaluation. Uses clmul_gcm (~4 ns/mul) vs
/// Block128 mul (~30 ns). Returns evaluations at X=0,1,2 as u128 (flat basis).
fn eval_round_flat(w: &[u128], b: &[u128], half: usize) -> [u128; 3] {
    use noid_core::hardware::clmul_gcm;
    let f2_flat = noid_core::hardware::tower_to_flat_u128(noid_core::Block128::from(2u128).0);
    let per_entry = |j: usize| -> [u128; 3] {
        let w_lo = w[j];
        let w_hi = w[j + half];
        let b_lo = b[j];
        let b_hi = b[j + half];
        let dw = w_lo ^ w_hi;
        let db = b_lo ^ b_hi;
        let w2 = w_lo ^ clmul_gcm(f2_flat, dw);
        let b2 = b_lo ^ clmul_gcm(f2_flat, db);
        [
            clmul_gcm(w_lo, b_lo),
            clmul_gcm(w_hi, b_hi),
            clmul_gcm(w2, b2),
        ]
    };
    if half >= PAR_THRESHOLD {
        (0..half).into_par_iter().map(per_entry).reduce(
            || [0u128; 3],
            |a, b| [a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2]],
        )
    } else {
        let mut acc = [0u128; 3];
        for j in 0..half {
            let p = per_entry(j);
            acc[0] ^= p[0];
            acc[1] ^= p[1];
            acc[2] ^= p[2];
        }
        acc
    }
}

/// Evaluate `W(r) = Σ_i α_i · eq(r_i, r)` without materialising the table.
fn evaluate_w_at(claims: &[EvalClaim], alphas: &[Block128], r: &[Block128]) -> Block128 {
    debug_assert_eq!(claims.len(), alphas.len());
    let mut acc = Block128::ZERO;
    for (claim, &alpha) in claims.iter().zip(alphas.iter()) {
        debug_assert_eq!(claim.point.len(), r.len());
        acc += alpha * eq_ind(&claim.point, r);
    }
    acc
}

fn linear_claim_w_contribution(
    claim: &LinearEvalClaim,
    alpha: Block128,
    r: &[Block128],
) -> Block128 {
    let mut acc = Block128::ZERO;
    for term in &claim.terms {
        debug_assert_eq!(term.point.len(), r.len());
        let eq = if let Some(index) = boolean_point_index(&term.point) {
            eq_at_boolean_index(index, term.point.len(), r)
        } else {
            eq_ind(&term.point, r)
        };
        acc += alpha * term.coeff * eq;
    }
    acc
}

/// Claim-count threshold above which the public w(r) evaluation fans out to
/// rayon. Field addition is XOR, so the parallel reduction is bit-exact.
const LINEAR_W_PAR_THRESHOLD: usize = 1024;

fn evaluate_linear_w_at(
    claims: &[LinearEvalClaim],
    alphas: &[Block128],
    r: &[Block128],
) -> Block128 {
    debug_assert_eq!(claims.len(), alphas.len());
    if claims.len() >= LINEAR_W_PAR_THRESHOLD {
        return claims
            .par_iter()
            .zip(alphas.par_iter())
            .map(|(claim, &alpha)| linear_claim_w_contribution(claim, alpha, r))
            .reduce(|| Block128::ZERO, |a, b| a + b);
    }
    let mut acc = Block128::ZERO;
    for (claim, &alpha) in claims.iter().zip(alphas.iter()) {
        acc += linear_claim_w_contribution(claim, alpha, r);
    }
    acc
}

fn eq_at_boolean_index(index: usize, n: usize, r: &[Block128]) -> Block128 {
    debug_assert_eq!(r.len(), n);
    let mut acc = Block128::ONE;
    for (bit, &coord) in r.iter().enumerate().take(n) {
        if (index >> bit) & 1 == 1 {
            acc *= coord;
        } else {
            acc *= Block128::ONE + coord;
        }
    }
    acc
}

/// Base-64 digits of `m − 1` (≥ 1) — the number of squeezed challenge
/// LEVELS the multi-level RLC below uses for an `m`-claim batch. Shared by
/// the native helper, the trace twin and the channel schedule extractors so
/// every transcript agrees on the squeeze count by construction.
pub fn rlc_levels(m: usize) -> usize {
    let mut levels = 1usize;
    let mut top = m.saturating_sub(1) / RLC_LEVEL_BASE;
    while top > 0 {
        levels += 1;
        top /= RLC_LEVEL_BASE;
    }
    levels
}

/// Per-level digit base of the multi-level RLC (digit degree ≤ 63).
pub const RLC_LEVEL_BASE: usize = 64;

/// MULTI-LEVEL RLC batching weights for `m` claims: with `L = rlc_levels(m)`
/// challenges `c_0, …, c_{L−1}` squeezed in order,
/// `weight[i] = Π_j c_j^{digit_j(i)}` over the base-64 digits of `i`.
/// For `m ≤ 64` this is exactly the single-α power ladder
/// `(1, α, α², …, α^{m−1})` — one squeeze, transcripts unchanged.
///
/// Soundness: a nonzero claim-error vector `e` survives the batch only if
/// the multivariate polynomial `Σ eᵢ·Π_j x_j^{digit_j(i)}` vanishes at the
/// random `(c_0, …, c_{L−1})`; by Schwartz–Zippel that happens with
/// probability ≤ (Σ_j d_j)/2^128 where every per-level degree `d_j ≤ 63`.
/// Largest batch in the protocol (the batched Merkle path chains ≈ 2^17
/// claims at the 255-tx max shape) takes L = 3 levels ⇒ error ≤ 189/2^128
/// ≈ 2^-120.4 — the ≥ 120-bit batching term the §7.1 ledger budgets (the
/// old single-α rule bottomed at ≈ 2^-111 there). Small batches keep the
/// squeeze diet: one FS permutation per batch, not per claim.
///
/// The prover and the verifier derive the weights through this same helper,
/// so the channel stays in lockstep by construction.
pub(crate) fn squeeze_alphas<T: FiatShamir<Block128>>(channel: &mut T, m: usize) -> Vec<Block128> {
    if m == 0 {
        return Vec::new();
    }
    let levels = rlc_levels(m);
    let cs: Vec<Block128> = (0..levels).map(|_| channel.squeeze()).collect();
    if levels == 1 {
        // The single-α power ladder (byte-identical to the pre-upgrade rule).
        let mut alphas = Vec::with_capacity(m);
        let mut acc = Block128::ONE;
        for _ in 0..m {
            alphas.push(acc);
            acc *= cs[0];
        }
        return alphas;
    }
    // Per-level power tables over the digit range each level takes, then
    // the digit products (level 0 rolls fastest).
    let mut tables: Vec<Vec<Block128>> = Vec::with_capacity(levels);
    for (j, c) in cs.iter().enumerate() {
        let digits = RLC_LEVEL_BASE.min((m - 1) / RLC_LEVEL_BASE.pow(j as u32) + 1);
        let mut table = Vec::with_capacity(digits);
        let mut acc = Block128::ONE;
        for _ in 0..digits {
            table.push(acc);
            acc *= *c;
        }
        tables.push(table);
    }
    (0..m)
        .map(|i| {
            let mut w = tables[0][i % RLC_LEVEL_BASE];
            let mut x = i / RLC_LEVEL_BASE;
            for table in &tables[1..] {
                w *= table[x % RLC_LEVEL_BASE];
                x /= RLC_LEVEL_BASE;
            }
            w
        })
        .collect()
}

/// Bind the batched claims to the channel so `α_i` are tied to the exact
/// claim set. PREBOUND schedule: only each claim's point LENGTH and VALUE
/// are absorbed, never the point coordinates. Sound because every closure
/// in the protocol batches claims whose points are the channel's OWN
/// squeezed challenge vectors (unified/shift reduction points, chain and
/// boundary points) — already determined by the transcript state at entry;
/// re-absorbing them bound nothing and cost `~(2 + num_vars)` lanes per
/// point. Values must stay absorbed: sub-reduction `b_final`s enter the
/// transcript only here. A future caller whose points are NOT
/// transcript-determined must absorb them explicitly first (see
/// [`absorb_point`] / the dense linear-claim schedule).
fn absorb_claims<T: FiatShamir<Block128>>(channel: &mut T, claims: &[EvalClaim]) {
    for c in claims {
        channel.absorb(Block128::from(c.point.len() as u128));
        channel.absorb(c.value);
    }
}

fn absorb_point<T: FiatShamir<Block128>>(channel: &mut T, point: &[Block128]) {
    if let Some(index) = boolean_point_index(point) {
        channel.absorb(Block128::from(CLAIM_POINT_BOOL_TAG));
        channel.absorb(Block128::from(point.len() as u128));
        channel.absorb(Block128::from(index as u128));
    } else {
        channel.absorb(Block128::from(CLAIM_POINT_DENSE_TAG));
        channel.absorb(Block128::from(point.len() as u128));
        for e in point {
            channel.absorb(*e);
        }
    }
}

fn absorb_linear_claims<T: FiatShamir<Block128>>(channel: &mut T, claims: &[LinearEvalClaim]) {
    channel.absorb(Block128::from(LINEAR_EVAL_TAG));
    channel.absorb(Block128::from(claims.len() as u128));
    for claim in claims {
        channel.absorb(Block128::from(claim.terms.len() as u128));
        for term in &claim.terms {
            channel.absorb(term.coeff);
            absorb_point(channel, &term.point);
        }
        channel.absorb(claim.value);
    }
}

fn absorb_linear_claims_prebound<T: FiatShamir<Block128>>(
    channel: &mut T,
    relation_tag: u128,
    n: usize,
    claims: &[LinearEvalClaim],
) {
    let total_terms: usize = claims.iter().map(|claim| claim.terms.len()).sum();
    channel.absorb(Block128::from(LINEAR_EVAL_PREBOUND_TAG));
    channel.absorb(Block128::from(relation_tag));
    channel.absorb(Block128::from(n as u128));
    channel.absorb(Block128::from(claims.len() as u128));
    channel.absorb(Block128::from(total_terms as u128));
}

fn absorb_linear_binding<T: FiatShamir<Block128>>(
    channel: &mut T,
    binding: &LinearEvalBinding,
    n: usize,
    claims: &[LinearEvalClaim],
) {
    match *binding {
        LinearEvalBinding::Explicit => absorb_linear_claims(channel, claims),
        LinearEvalBinding::Prebound { relation_tag } => {
            absorb_linear_claims_prebound(channel, relation_tag, n, claims)
        }
    }
}

// Public: the in-circuit trace transliterations (`noid_recursive::acceptance::trace`)
// absorb these same tags; referencing one definition keeps native and trace
// in lockstep by construction; change both together.
pub const MULTI_BATCH_EVAL_PREBOUND_TAG: u128 = 0xA07D_6B12_BA7C_0002;
pub const CLAIM_POINT_BOOL_TAG: u128 = 0xA07D_6B12_C1A1_0001;
pub const CLAIM_POINT_DENSE_TAG: u128 = 0xA07D_6B12_C1A1_0002;
pub const LINEAR_EVAL_TAG: u128 = 0xA07D_6B12_11EA_0001;
pub const LINEAR_EVAL_PREBOUND_TAG: u128 = 0xA07D_6B12_11EA_0002;

/// Multi-column claim binding, prebound schedule (see [`absorb_claims`]).
fn absorb_multi_claims<T: FiatShamir<Block128>>(
    channel: &mut T,
    claims_by_column: &[&[EvalClaim]],
) {
    channel.absorb(Block128::from(MULTI_BATCH_EVAL_PREBOUND_TAG));
    channel.absorb(Block128::from(claims_by_column.len() as u128));
    for (col_idx, claims) in claims_by_column.iter().enumerate() {
        channel.absorb(Block128::from(col_idx as u128));
        channel.absorb(Block128::from(claims.len() as u128));
        absorb_claims(channel, claims);
    }
}

fn squeeze_alphas_by_column<T: FiatShamir<Block128>>(
    channel: &mut T,
    claims_by_column: &[&[EvalClaim]],
) -> Vec<Vec<Block128>> {
    claims_by_column
        .iter()
        .map(|claims| squeeze_alphas(channel, claims.len()))
        .collect()
}

fn initial_multi_claim(
    claims_by_column: &[&[EvalClaim]],
    alphas_by_column: &[Vec<Block128>],
) -> Block128 {
    let mut claim = Block128::ZERO;
    for (claims, alphas) in claims_by_column.iter().zip(alphas_by_column.iter()) {
        for (c, &a) in claims.iter().zip(alphas.iter()) {
            claim += a * c.value;
        }
    }
    claim
}

fn initial_linear_claim(claims: &[LinearEvalClaim], alphas: &[Block128]) -> Block128 {
    if claims.len() >= LINEAR_W_PAR_THRESHOLD {
        return claims
            .par_iter()
            .zip(alphas.par_iter())
            .map(|(claim, &alpha)| alpha * claim.value)
            .reduce(|| Block128::ZERO, |a, b| a + b);
    }
    claims
        .iter()
        .zip(alphas.iter())
        .map(|(claim, &alpha)| alpha * claim.value)
        .fold(Block128::ZERO, |a, b| a + b)
}

/// Honest prover.
///
/// `b`: length-`2^n` table of the target MLE. Must be the same table
/// whose claims are being discharged.
/// `claims`: the M `(r_i, v_i)` claims.
/// `channel`: shared Fiat-Shamir channel.
///
/// Returns the proof and the `(r_B, v_B)` reduction so callers can
/// feed it into the next protocol layer.
pub fn prove_batch_eval<T: FiatShamir<Block128>>(
    b: &[Block128],
    claims: &[EvalClaim],
    channel: &mut T,
) -> (BatchEvalProof, BatchEvalReduction) {
    let n = b.len().trailing_zeros() as usize;
    assert_eq!(b.len(), 1 << n);
    assert!(!claims.is_empty());
    for c in claims {
        assert_eq!(c.point.len(), n);
    }

    absorb_claims(channel, claims);
    let alphas = squeeze_alphas(channel, claims.len());

    // Convert w and b to flat (GCM) basis for ~7x faster arithmetic.
    let mut w_flat = build_w_table_flat(claims, &alphas, n);
    let mut b_flat: Vec<u128> = {
        use noid_core::hardware::tower_to_flat_u128;
        use rayon::prelude::*;
        if b.len() >= 4096 {
            b.par_iter().map(|v| tower_to_flat_u128(v.0)).collect()
        } else {
            b.iter().map(|v| tower_to_flat_u128(v.0)).collect()
        }
    };

    // Initial claim: V = Σ α_i · v_i.
    let mut claim = Block128::ZERO;
    for (c, &a) in claims.iter().zip(alphas.iter()) {
        claim += a * c.value;
    }

    let mut rounds = Vec::with_capacity(n);
    let mut challenges = Vec::with_capacity(n);

    for _round in 0..n {
        let half = w_flat.len() / 2;
        // Evaluate round polynomial in flat basis, convert to tower for transcript.
        let evals_flat = eval_round_flat(&w_flat, &b_flat, half);
        let evals: [Block128; 3] =
            evals_flat.map(|v| Block128::from(noid_core::hardware::flat_to_tower_u128(v)));
        debug_assert_eq!(evals[0] + evals[1], claim);
        let re = BatchEvalRound {
            evals_at_1_2: [evals[1], evals[2]],
        };

        for e in &re.evals_at_1_2 {
            channel.absorb(*e);
        }
        let r_i = channel.squeeze();
        let r_i_flat = noid_core::hardware::tower_to_flat_u128(r_i.0);

        claim = re.evaluate(claim, r_i);
        fold_flat(&mut w_flat, r_i_flat);
        fold_flat_zeroing_truncated(&mut b_flat, r_i_flat);

        rounds.push(re);
        challenges.push(r_i);
    }

    debug_assert_eq!(w_flat.len(), 1);
    debug_assert_eq!(b_flat.len(), 1);
    let b_final = Block128::from(noid_core::hardware::flat_to_tower_u128(b_flat[0]));
    let w_final = Block128::from(noid_core::hardware::flat_to_tower_u128(w_flat[0]));
    debug_assert_eq!(claim, w_final * b_final);
    w_flat.zeroize();
    b_flat.zeroize();

    challenges.reverse();

    let proof = BatchEvalProof { rounds, b_final };
    let reduction = BatchEvalReduction {
        point: challenges.clone(),
        value: b_final,
    };
    (proof, reduction)
}

/// Honest verifier. Returns `Some(reduction)` on accept, `None` on
/// reject. The caller is responsible for discharging
/// `reduction.value == B(reduction.point)` against the commitment to
/// `B`.
pub fn verify_batch_eval<T: FiatShamir<Block128>>(
    proof: &BatchEvalProof,
    claims: &[EvalClaim],
    n: usize,
    channel: &mut T,
) -> Option<BatchEvalReduction> {
    if claims.is_empty() {
        return None;
    }
    for c in claims {
        if c.point.len() != n {
            return None;
        }
    }
    if proof.rounds.len() != n {
        return None;
    }

    absorb_claims(channel, claims);
    let alphas = squeeze_alphas(channel, claims.len());

    let mut claim = Block128::ZERO;
    for (c, &a) in claims.iter().zip(alphas.iter()) {
        claim += a * c.value;
    }

    let mut challenges = Vec::with_capacity(n);
    for re in &proof.rounds {
        for e in &re.evals_at_1_2 {
            channel.absorb(*e);
        }
        let r_i = channel.squeeze();
        claim = re.evaluate(claim, r_i);
        challenges.push(r_i);
    }
    challenges.reverse();

    // Final check: claim == W(r_B) · b_final.
    let w_at = evaluate_w_at(claims, &alphas, &challenges);
    if claim != w_at * proof.b_final {
        return None;
    }

    Some(BatchEvalReduction {
        point: challenges,
        value: proof.b_final,
    })
}

/// Honest prover for public linear relations over one committed MLE.
pub fn prove_linear_eval<T: FiatShamir<Block128>>(
    b: &[Block128],
    claims: &[LinearEvalClaim],
    channel: &mut T,
) -> (LinearEvalProof, BatchEvalReduction) {
    prove_linear_eval_inner(b, claims, channel, LinearEvalBinding::Explicit)
}

/// Honest prover for public linear relations whose full constraint set is
/// deterministically derived from already-absorbed public statement data.
///
/// This mode is for large relations such as Merkle path-chain continuity where
/// serializing every Boolean point into the Fiat-Shamir channel would dominate
/// verification. The caller must ensure the public statement defining `claims`
/// was absorbed before this call, and must use a unique `relation_tag`.
pub fn prove_linear_eval_prebound<T: FiatShamir<Block128>>(
    b: &[Block128],
    claims: &[LinearEvalClaim],
    relation_tag: u128,
    channel: &mut T,
) -> (LinearEvalProof, BatchEvalReduction) {
    prove_linear_eval_inner(
        b,
        claims,
        channel,
        LinearEvalBinding::Prebound { relation_tag },
    )
}

fn prove_linear_eval_inner<T: FiatShamir<Block128>>(
    b: &[Block128],
    claims: &[LinearEvalClaim],
    channel: &mut T,
    binding: LinearEvalBinding,
) -> (LinearEvalProof, BatchEvalReduction) {
    let n = b.len().trailing_zeros() as usize;
    assert_eq!(b.len(), 1 << n);
    assert!(!claims.is_empty());
    for claim in claims {
        assert!(!claim.terms.is_empty());
        for term in &claim.terms {
            assert_eq!(term.point.len(), n);
        }
    }

    absorb_linear_binding(channel, &binding, n, claims);
    let alphas = squeeze_alphas(channel, claims.len());
    let mut claim = initial_linear_claim(claims, &alphas);
    let mut w_flat = build_linear_w_table_flat(claims, &alphas, n);
    let mut b_flat: Vec<u128> = {
        use noid_core::hardware::tower_to_flat_u128;
        if b.len() >= 4096 {
            b.par_iter().map(|v| tower_to_flat_u128(v.0)).collect()
        } else {
            b.iter().map(|v| tower_to_flat_u128(v.0)).collect()
        }
    };

    let mut rounds = Vec::with_capacity(n);
    let mut challenges = Vec::with_capacity(n);

    for _round in 0..n {
        let half = w_flat.len() / 2;
        let evals_flat = eval_round_flat(&w_flat, &b_flat, half);
        let evals: [Block128; 3] =
            evals_flat.map(|v| Block128::from(noid_core::hardware::flat_to_tower_u128(v)));
        debug_assert_eq!(evals[0] + evals[1], claim);
        let re = BatchEvalRound {
            evals_at_1_2: [evals[1], evals[2]],
        };

        for e in &re.evals_at_1_2 {
            channel.absorb(*e);
        }
        let r_i = channel.squeeze();
        let r_i_flat = noid_core::hardware::tower_to_flat_u128(r_i.0);

        claim = re.evaluate(claim, r_i);
        fold_flat(&mut w_flat, r_i_flat);
        fold_flat_zeroing_truncated(&mut b_flat, r_i_flat);

        rounds.push(re);
        challenges.push(r_i);
    }

    debug_assert_eq!(w_flat.len(), 1);
    debug_assert_eq!(b_flat.len(), 1);
    let b_final = Block128::from(noid_core::hardware::flat_to_tower_u128(b_flat[0]));
    let w_final = Block128::from(noid_core::hardware::flat_to_tower_u128(w_flat[0]));
    debug_assert_eq!(claim, w_final * b_final);
    w_flat.zeroize();
    b_flat.zeroize();

    challenges.reverse();
    let proof = LinearEvalProof { rounds, b_final };
    let reduction = BatchEvalReduction {
        point: challenges,
        value: b_final,
    };
    (proof, reduction)
}

/// Verifier for [`prove_linear_eval`].
pub fn verify_linear_eval<T: FiatShamir<Block128>>(
    proof: &LinearEvalProof,
    claims: &[LinearEvalClaim],
    n: usize,
    channel: &mut T,
) -> Option<BatchEvalReduction> {
    verify_linear_eval_inner(proof, claims, n, channel, LinearEvalBinding::Explicit)
}

/// Verifier for [`prove_linear_eval_prebound`].
pub fn verify_linear_eval_prebound<T: FiatShamir<Block128>>(
    proof: &LinearEvalProof,
    claims: &[LinearEvalClaim],
    n: usize,
    relation_tag: u128,
    channel: &mut T,
) -> Option<BatchEvalReduction> {
    verify_linear_eval_inner(
        proof,
        claims,
        n,
        channel,
        LinearEvalBinding::Prebound { relation_tag },
    )
}

fn verify_linear_eval_inner<T: FiatShamir<Block128>>(
    proof: &LinearEvalProof,
    claims: &[LinearEvalClaim],
    n: usize,
    channel: &mut T,
    binding: LinearEvalBinding,
) -> Option<BatchEvalReduction> {
    if claims.is_empty() || proof.rounds.len() != n {
        return None;
    }
    for claim in claims {
        if claim.terms.is_empty() {
            return None;
        }
        for term in &claim.terms {
            if term.point.len() != n {
                return None;
            }
        }
    }

    absorb_linear_binding(channel, &binding, n, claims);
    let alphas = squeeze_alphas(channel, claims.len());
    let mut claim = initial_linear_claim(claims, &alphas);

    let mut challenges = Vec::with_capacity(n);
    for re in &proof.rounds {
        for e in &re.evals_at_1_2 {
            channel.absorb(*e);
        }
        let r_i = channel.squeeze();
        claim = re.evaluate(claim, r_i);
        challenges.push(r_i);
    }
    challenges.reverse();

    let w_at = evaluate_linear_w_at(claims, &alphas, &challenges);
    if claim != w_at * proof.b_final {
        return None;
    }

    Some(BatchEvalReduction {
        point: challenges,
        value: proof.b_final,
    })
}

/// Honest prover for multiple target MLE columns with a shared terminal point.
pub fn prove_multi_batch_eval<T: FiatShamir<Block128>>(
    columns: &[&[Block128]],
    claims_by_column: &[&[EvalClaim]],
    channel: &mut T,
) -> (MultiBatchEvalProof, Vec<BatchEvalReduction>) {
    assert!(!columns.is_empty());
    assert_eq!(columns.len(), claims_by_column.len());
    let n = columns[0].len().trailing_zeros() as usize;
    assert_eq!(columns[0].len(), 1 << n);
    for b in columns {
        assert_eq!(b.len(), 1 << n);
    }
    for claims in claims_by_column {
        assert!(!claims.is_empty());
        for c in *claims {
            assert_eq!(c.point.len(), n);
        }
    }

    absorb_multi_claims(channel, claims_by_column);
    let alphas_by_column = squeeze_alphas_by_column(channel, claims_by_column);

    let mut w_tables: Vec<Vec<u128>> = claims_by_column
        .iter()
        .zip(alphas_by_column.iter())
        .map(|(claims, alphas)| build_w_table_flat(claims, alphas, n))
        .collect();
    let mut b_tables: Vec<Vec<u128>> = columns
        .iter()
        .map(|b| {
            use noid_core::hardware::tower_to_flat_u128;
            if b.len() >= 4096 {
                b.par_iter().map(|v| tower_to_flat_u128(v.0)).collect()
            } else {
                b.iter().map(|v| tower_to_flat_u128(v.0)).collect()
            }
        })
        .collect();

    let mut claim = initial_multi_claim(claims_by_column, &alphas_by_column);
    let mut rounds = Vec::with_capacity(n);
    let mut challenges = Vec::with_capacity(n);

    for _round in 0..n {
        let half = b_tables[0].len() / 2;
        let mut evals_flat = [0u128; 3];
        for (w, b) in w_tables.iter().zip(b_tables.iter()) {
            debug_assert_eq!(w.len(), b.len());
            let e = eval_round_flat(w, b, half);
            evals_flat[0] ^= e[0];
            evals_flat[1] ^= e[1];
            evals_flat[2] ^= e[2];
        }
        let evals: [Block128; 3] =
            evals_flat.map(|v| Block128::from(noid_core::hardware::flat_to_tower_u128(v)));
        debug_assert_eq!(evals[0] + evals[1], claim);
        let re = BatchEvalRound {
            evals_at_1_2: [evals[1], evals[2]],
        };

        for e in &re.evals_at_1_2 {
            channel.absorb(*e);
        }
        let r_i = channel.squeeze();
        let r_i_flat = noid_core::hardware::tower_to_flat_u128(r_i.0);

        claim = re.evaluate(claim, r_i);
        for w in &mut w_tables {
            fold_flat(w, r_i_flat);
        }
        for b in &mut b_tables {
            fold_flat_zeroing_truncated(b, r_i_flat);
        }

        rounds.push(re);
        challenges.push(r_i);
    }

    debug_assert!(w_tables.iter().all(|w| w.len() == 1));
    debug_assert!(b_tables.iter().all(|b| b.len() == 1));
    let b_finals: Vec<Block128> = b_tables
        .iter()
        .map(|b| Block128::from(noid_core::hardware::flat_to_tower_u128(b[0])))
        .collect();
    let w_finals: Vec<Block128> = w_tables
        .iter()
        .map(|w| Block128::from(noid_core::hardware::flat_to_tower_u128(w[0])))
        .collect();
    let final_claim = w_finals
        .iter()
        .zip(b_finals.iter())
        .map(|(&w, &b)| w * b)
        .fold(Block128::ZERO, |a, b| a + b);
    debug_assert_eq!(claim, final_claim);
    b_tables.zeroize();

    challenges.reverse();
    let reductions = b_finals
        .iter()
        .map(|&value| BatchEvalReduction {
            point: challenges.clone(),
            value,
        })
        .collect();
    let proof = MultiBatchEvalProof { rounds, b_finals };
    (proof, reductions)
}

/// Verifier for `prove_multi_batch_eval`.
pub fn verify_multi_batch_eval<T: FiatShamir<Block128>>(
    proof: &MultiBatchEvalProof,
    claims_by_column: &[&[EvalClaim]],
    n: usize,
    channel: &mut T,
) -> Option<Vec<BatchEvalReduction>> {
    if claims_by_column.is_empty() || proof.b_finals.len() != claims_by_column.len() {
        return None;
    }
    for claims in claims_by_column {
        if claims.is_empty() {
            return None;
        }
        for c in *claims {
            if c.point.len() != n {
                return None;
            }
        }
    }
    if proof.rounds.len() != n {
        return None;
    }

    absorb_multi_claims(channel, claims_by_column);
    let alphas_by_column = squeeze_alphas_by_column(channel, claims_by_column);
    let mut claim = initial_multi_claim(claims_by_column, &alphas_by_column);

    let mut challenges = Vec::with_capacity(n);
    for re in &proof.rounds {
        for e in &re.evals_at_1_2 {
            channel.absorb(*e);
        }
        let r_i = channel.squeeze();
        claim = re.evaluate(claim, r_i);
        challenges.push(r_i);
    }
    challenges.reverse();

    let final_claim = claims_by_column
        .iter()
        .zip(alphas_by_column.iter())
        .zip(proof.b_finals.iter())
        .map(|((claims, alphas), &b_final)| evaluate_w_at(claims, alphas, &challenges) * b_final)
        .fold(Block128::ZERO, |a, b| a + b);
    if claim != final_claim {
        return None;
    }

    Some(
        proof
            .b_finals
            .iter()
            .map(|&value| BatchEvalReduction {
                point: challenges.clone(),
                value,
            })
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_core::mle::evaluate::evaluate_slice;
    use noid_poseidon2b::channel::Poseidon2bChannel;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    fn rand_vec(rng: &mut StdRng, n: usize) -> Vec<Block128> {
        (0..n).map(|_| Block128::from(rng.gen::<u128>())).collect()
    }

    fn fresh_channel(seed: u64) -> Poseidon2bChannel {
        let mut ch = Poseidon2bChannel::new();
        ch.absorb(Block128::from(seed as u128));
        ch
    }

    #[test]
    fn honest_roundtrip_single_claim() {
        let mut rng = StdRng::seed_from_u64(1);
        let n = 5;
        let b = rand_vec(&mut rng, 1 << n);
        let r0 = rand_vec(&mut rng, n);
        let v0 = evaluate_slice(&b, &r0);
        let claims = vec![EvalClaim {
            point: r0,
            value: v0,
        }];

        let mut cp = fresh_channel(7);
        let (proof, red_p) = prove_batch_eval(&b, &claims, &mut cp);

        let mut cv = fresh_channel(7);
        let red_v = verify_batch_eval(&proof, &claims, n, &mut cv).unwrap();
        assert_eq!(red_p, red_v);
        assert_eq!(red_v.value, evaluate_slice(&b, &red_v.point));
    }

    #[test]
    fn honest_roundtrip_many_claims() {
        let mut rng = StdRng::seed_from_u64(2);
        let n = 6;
        let b = rand_vec(&mut rng, 1 << n);
        let m = 17;
        let claims: Vec<EvalClaim> = (0..m)
            .map(|_| {
                let r = rand_vec(&mut rng, n);
                let v = evaluate_slice(&b, &r);
                EvalClaim { point: r, value: v }
            })
            .collect();

        let mut cp = fresh_channel(13);
        let (proof, red_p) = prove_batch_eval(&b, &claims, &mut cp);

        let mut cv = fresh_channel(13);
        let red_v = verify_batch_eval(&proof, &claims, n, &mut cv).unwrap();
        assert_eq!(red_p, red_v);
        assert_eq!(red_v.value, evaluate_slice(&b, &red_v.point));
    }

    #[test]
    fn honest_multi_column_roundtrip() {
        let mut rng = StdRng::seed_from_u64(33);
        let n = 6;
        let columns: Vec<Vec<Block128>> = (0..3).map(|_| rand_vec(&mut rng, 1 << n)).collect();
        let mut claims_by_column: Vec<Vec<EvalClaim>> = Vec::new();
        for (col_idx, b) in columns.iter().enumerate() {
            let m = col_idx + 2;
            let claims: Vec<EvalClaim> = (0..m)
                .map(|_| {
                    let r = rand_vec(&mut rng, n);
                    let v = evaluate_slice(b, &r);
                    EvalClaim { point: r, value: v }
                })
                .collect();
            claims_by_column.push(claims);
        }
        let column_refs: Vec<&[Block128]> = columns.iter().map(Vec::as_slice).collect();
        let claim_refs: Vec<&[EvalClaim]> = claims_by_column.iter().map(Vec::as_slice).collect();

        let mut cp = fresh_channel(77);
        let (proof, red_p) = prove_multi_batch_eval(&column_refs, &claim_refs, &mut cp);

        let mut cv = fresh_channel(77);
        let red_v = verify_multi_batch_eval(&proof, &claim_refs, n, &mut cv).unwrap();
        assert_eq!(red_p, red_v);
        assert_eq!(red_v.len(), columns.len());
        for (col, red) in columns.iter().zip(red_v.iter()) {
            assert_eq!(red.value, evaluate_slice(col, &red.point));
        }
        assert!(red_v.windows(2).all(|w| w[0].point == w[1].point));
    }

    #[test]
    fn honest_linear_eval_roundtrip() {
        let mut rng = StdRng::seed_from_u64(44);
        let n = 5;
        let b = rand_vec(&mut rng, 1 << n);
        let p0 = rand_vec(&mut rng, n);
        let p1 = rand_vec(&mut rng, n);
        let c0 = Block128::from(7u128);
        let c1 = Block128::from(11u128);
        let value = c0 * evaluate_slice(&b, &p0) + c1 * evaluate_slice(&b, &p1);
        let claims = vec![LinearEvalClaim {
            terms: vec![
                LinearEvalTerm {
                    point: p0,
                    coeff: c0,
                },
                LinearEvalTerm {
                    point: p1,
                    coeff: c1,
                },
            ],
            value,
        }];

        let mut cp = fresh_channel(101);
        let (proof, red_p) = prove_linear_eval(&b, &claims, &mut cp);
        let mut cv = fresh_channel(101);
        let red_v = verify_linear_eval(&proof, &claims, n, &mut cv).unwrap();

        assert_eq!(red_p, red_v);
        assert_eq!(red_v.value, evaluate_slice(&b, &red_v.point));
    }

    #[test]
    fn linear_eval_tampered_value_rejected() {
        let mut rng = StdRng::seed_from_u64(45);
        let n = 5;
        let b = rand_vec(&mut rng, 1 << n);
        let point = rand_vec(&mut rng, n);
        let claims = vec![LinearEvalClaim {
            terms: vec![LinearEvalTerm {
                point: point.clone(),
                coeff: Block128::ONE,
            }],
            value: evaluate_slice(&b, &point),
        }];

        let mut cp = fresh_channel(102);
        let (proof, _) = prove_linear_eval(&b, &claims, &mut cp);
        let mut bad_claims = claims.clone();
        bad_claims[0].value += Block128::ONE;

        let mut cv = fresh_channel(102);
        assert!(verify_linear_eval(&proof, &bad_claims, n, &mut cv).is_none());
    }

    #[test]
    fn prebound_linear_eval_relation_tag_is_binding() {
        let mut rng = StdRng::seed_from_u64(46);
        let n = 4;
        let b = rand_vec(&mut rng, 1 << n);
        let point = (0..n)
            .map(|bit| {
                if bit % 2 == 0 {
                    Block128::ONE
                } else {
                    Block128::ZERO
                }
            })
            .collect::<Vec<_>>();
        let claims = vec![LinearEvalClaim {
            terms: vec![LinearEvalTerm {
                point: point.clone(),
                coeff: Block128::ONE,
            }],
            value: evaluate_slice(&b, &point),
        }];

        let mut cp = fresh_channel(103);
        let (proof, red_p) = prove_linear_eval_prebound(&b, &claims, 0xAA55, &mut cp);
        let mut cv = fresh_channel(103);
        let red_v = verify_linear_eval_prebound(&proof, &claims, n, 0xAA55, &mut cv)
            .expect("matching relation tag accepts");
        assert_eq!(red_p, red_v);

        let mut cv_bad = fresh_channel(103);
        assert!(
            verify_linear_eval_prebound(&proof, &claims, n, 0xAA56, &mut cv_bad).is_none(),
            "changed relation tag must alter Fiat-Shamir challenges"
        );
    }

    #[test]
    fn tampered_multi_column_final_rejected() {
        let mut rng = StdRng::seed_from_u64(34);
        let n = 5;
        let columns: Vec<Vec<Block128>> = (0..3).map(|_| rand_vec(&mut rng, 1 << n)).collect();
        let claims_by_column: Vec<Vec<EvalClaim>> = columns
            .iter()
            .map(|b| {
                let r = rand_vec(&mut rng, n);
                let v = evaluate_slice(b, &r);
                vec![EvalClaim { point: r, value: v }]
            })
            .collect();
        let column_refs: Vec<&[Block128]> = columns.iter().map(Vec::as_slice).collect();
        let claim_refs: Vec<&[EvalClaim]> = claims_by_column.iter().map(Vec::as_slice).collect();

        let mut cp = fresh_channel(78);
        let (mut proof, _) = prove_multi_batch_eval(&column_refs, &claim_refs, &mut cp);
        proof.b_finals[1] += Block128::from(1u128);

        let mut cv = fresh_channel(78);
        assert!(verify_multi_batch_eval(&proof, &claim_refs, n, &mut cv).is_none());
    }

    #[test]
    fn forged_verifier_claim_rejected() {
        // Prover runs honestly. Verifier is handed a claim vector with
        // one tampered `value`; its initial running claim forks, so
        // round 0's telescope `e0+e1 == claim` fails immediately.
        let mut rng = StdRng::seed_from_u64(3);
        let n = 5;
        let b = rand_vec(&mut rng, 1 << n);
        let r0 = rand_vec(&mut rng, n);
        let good = evaluate_slice(&b, &r0);
        let honest_claims = vec![EvalClaim {
            point: r0.clone(),
            value: good,
        }];

        let mut cp = fresh_channel(9);
        let (proof, _) = prove_batch_eval(&b, &honest_claims, &mut cp);

        let bad_claims = vec![EvalClaim {
            point: r0,
            value: good + Block128::from(1u128),
        }];
        let mut cv = fresh_channel(9);
        assert!(verify_batch_eval(&proof, &bad_claims, n, &mut cv).is_none());
    }

    #[test]
    fn tampered_b_final_rejected() {
        let mut rng = StdRng::seed_from_u64(4);
        let n = 5;
        let b = rand_vec(&mut rng, 1 << n);
        let r0 = rand_vec(&mut rng, n);
        let v0 = evaluate_slice(&b, &r0);
        let claims = vec![EvalClaim {
            point: r0,
            value: v0,
        }];

        let mut cp = fresh_channel(17);
        let (mut proof, _) = prove_batch_eval(&b, &claims, &mut cp);
        proof.b_final += Block128::from(1u128);

        let mut cv = fresh_channel(17);
        assert!(verify_batch_eval(&proof, &claims, n, &mut cv).is_none());
    }

    #[test]
    fn determinism() {
        let mut rng = StdRng::seed_from_u64(5);
        let n = 5;
        let b = rand_vec(&mut rng, 1 << n);
        let r0 = rand_vec(&mut rng, n);
        let v0 = evaluate_slice(&b, &r0);
        let claims = vec![EvalClaim {
            point: r0,
            value: v0,
        }];

        let mut c1 = fresh_channel(21);
        let (p1, _) = prove_batch_eval(&b, &claims, &mut c1);
        let mut c2 = fresh_channel(21);
        let (p2, _) = prove_batch_eval(&b, &claims, &mut c2);
        assert_eq!(p1, p2);
    }

    /// The multi-level RLC weights are exactly the digit products
    /// `Π_j c_j^{digit_j(i)}` of the sequentially squeezed level
    /// challenges, one squeeze per level, and `m ≤ 64` stays the
    /// single-α power ladder.
    #[test]
    fn multi_level_rlc_weights_match_digit_products() {
        fn pow(c: Block128, e: usize) -> Block128 {
            let mut acc = Block128::ONE;
            for _ in 0..e {
                acc *= c;
            }
            acc
        }
        for m in [1usize, 3, 64, 65, 100, 4096, 4097, 70_000] {
            let levels = rlc_levels(m);
            assert_eq!(
                levels,
                match m {
                    0..=64 => 1,
                    65..=4096 => 2,
                    _ => 3,
                },
                "levels at m = {m}"
            );
            // Replay the squeezes on a lockstep channel to recover the
            // level challenges the helper drew.
            let mut ch = fresh_channel(33);
            let weights = squeeze_alphas(&mut ch, m);
            let mut ch2 = fresh_channel(33);
            let cs: Vec<Block128> = (0..levels).map(|_| ch2.squeeze()).collect();
            for (i, w) in weights.iter().enumerate() {
                let mut expect = Block128::ONE;
                let mut x = i;
                for c in &cs {
                    expect *= pow(*c, x % RLC_LEVEL_BASE);
                    x /= RLC_LEVEL_BASE;
                }
                assert_eq!(*w, expect, "weight {i} of m = {m}");
            }
            // Post-state lockstep: both channels drew the same squeezes.
            assert_eq!(ch.squeeze(), ch2.squeeze(), "channel lockstep at m = {m}");
        }
    }

    /// A > 64-claim batch (two RLC levels) roundtrips and rejects a
    /// tampered claim value — the level-1 weights carry real soundness
    /// (a mutant dropping the second level cannot verify).
    #[test]
    fn two_level_batch_roundtrip_and_rejects_tamper() {
        let mut rng = StdRng::seed_from_u64(77);
        let n = 8;
        let b = rand_vec(&mut rng, 1 << n);
        let claims: Vec<EvalClaim> = (0..100)
            .map(|_| {
                let point = rand_vec(&mut rng, n);
                let value = evaluate_slice(&b, &point);
                EvalClaim { point, value }
            })
            .collect();

        let mut cp = fresh_channel(41);
        let (proof, red) = prove_batch_eval(&b, &claims, &mut cp);
        let mut cv = fresh_channel(41);
        let got = verify_batch_eval(&proof, &claims, n, &mut cv).expect("two-level batch verifies");
        assert_eq!(got.point, red.point);
        assert_eq!(got.value, red.value);

        // Tamper with a claim in the SECOND chunk (index ≥ 64): only the
        // level-1 weight separates it from the first chunk's claims.
        let mut bad = claims.clone();
        bad[80].value += Block128::from(1u128);
        let mut cv2 = fresh_channel(41);
        assert!(verify_batch_eval(&proof, &bad, n, &mut cv2).is_none());
    }
}
