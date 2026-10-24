// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Trace twins of the shared batch-evaluation sumcheck verifiers
//! (`noid_gkr::batch_eval`): `verify_linear_eval_prebound` and
//! `verify_multi_batch_eval`. Transliterated line by line — every absorb,
//! squeeze and telescope check in native order.
//!
//! Type restrictions vs native (deliberate, shape-driven):
//! - Linear-eval claims carry **constant boolean points** (packed indices)
//!   and **constant coefficients** — every in-trace user of the linear path
//!   (spine chain relations, Merkle path chains) has structural points; the
//!   native `boolean_point_index` branch is then decided at build time.
//! - Multi-batch claims carry **dense expression points** (they are always
//!   sumcheck challenge vectors). The prebound claim binding absorbs only
//!   point lengths and values — the points are the channel's own squeezed
//!   reduction vectors, already transcript-determined — so the old
//!   dense-vs-boolean absorb divergence no longer exists.

use noid_core::{Block128, TowerField};
use noid_gkr::batch_eval::{
    BatchEvalRound, LinearEvalProof, MultiBatchEvalProof, CLAIM_POINT_BOOL_TAG,
    LINEAR_EVAL_PREBOUND_TAG, MULTI_BATCH_EVAL_PREBOUND_TAG,
};

use super::{
    alloc_block, eq_ind_trace, mul, pin_zero, BatchEvalReductionTrace, BooleanPointEqCache,
    FieldR1csBuilder, LinExpr, RawChannelTrace, F128,
};

// ---------------------------------------------------------------------------
// Proof / claim wire types
// ---------------------------------------------------------------------------

/// Trace twin of `BatchEvalRound` — degree-2 round stored COMPRESSED as its
/// evaluations at `{1, 2}`; the evaluation at 0 is reconstructed from the
/// running claim (`p(0) = claim + p(1)`, a free linear expression), which
/// makes the old per-round sum pin true by construction.
pub struct BatchEvalRoundTrace {
    pub evals_at_1_2: [LinExpr; 2],
}

impl BatchEvalRoundTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &BatchEvalRound) -> Self {
        Self {
            evals_at_1_2: std::array::from_fn(|i| alloc_block(b, native.evals_at_1_2[i])),
        }
    }

    /// Trace twin of `batch_eval::lagrange_at_0_1_2` on the reconstructed
    /// triple (6 multiplications).
    pub fn evaluate(&self, b: &mut FieldR1csBuilder, claim: &LinExpr, r: &LinExpr) -> LinExpr {
        let e0 = claim.add(&self.evals_at_1_2[0]);
        let denom_inv = denom_inv_3_flat();
        let r0 = r.clone();
        let r1 = r.add_const(super::flat_of(Block128::from(1u128)));
        let r2 = r.add_const(super::flat_of(Block128::from(2u128)));
        let n0 = mul(b, &r1, &r2);
        let n1 = mul(b, &r0, &r2);
        let n2 = mul(b, &r0, &r1);
        let t0 = mul(b, &e0, &n0).scale(denom_inv[0]);
        let t1 = mul(b, &self.evals_at_1_2[0], &n1).scale(denom_inv[1]);
        let t2 = mul(b, &self.evals_at_1_2[1], &n2).scale(denom_inv[2]);
        t0.add(&t1).add(&t2)
    }

    pub fn absorb_evals(&self, b: &mut FieldR1csBuilder, ch: &mut RawChannelTrace) {
        for e in &self.evals_at_1_2 {
            ch.absorb(b, e);
        }
    }
}

/// Flat images of the inverse Lagrange denominators at `{0,1,2}`
/// (`batch_eval::denom_inv_3`, recomputed here at build time).
fn denom_inv_3_flat() -> [F128; 3] {
    let mut out = [F128::ZERO; 3];
    for k in 0..3usize {
        let xk = Block128::from(k as u128);
        let mut d = Block128::ONE;
        for j in 0..3usize {
            if j == k {
                continue;
            }
            d *= xk + Block128::from(j as u128);
        }
        out[k] = super::flat_of(d.invert());
    }
    out
}

/// Trace twin of `LinearEvalProof`.
pub struct LinearEvalProofTrace {
    pub rounds: Vec<BatchEvalRoundTrace>,
    pub b_final: LinExpr,
}

impl LinearEvalProofTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &LinearEvalProof, n: usize) -> Self {
        assert_eq!(
            native.rounds.len(),
            n,
            "linear-eval proof off the trace shape"
        );
        Self {
            rounds: native
                .rounds
                .iter()
                .map(|r| BatchEvalRoundTrace::alloc(b, r))
                .collect(),
            b_final: alloc_block(b, native.b_final),
        }
    }
}

/// Trace twin of `MultiBatchEvalProof`.
pub struct MultiBatchEvalProofTrace {
    pub rounds: Vec<BatchEvalRoundTrace>,
    pub b_finals: Vec<LinExpr>,
}

impl MultiBatchEvalProofTrace {
    pub fn alloc(
        b: &mut FieldR1csBuilder,
        native: &MultiBatchEvalProof,
        n: usize,
        n_columns: usize,
    ) -> Self {
        assert_eq!(
            native.rounds.len(),
            n,
            "multi-batch proof off the trace shape"
        );
        assert_eq!(
            native.b_finals.len(),
            n_columns,
            "multi-batch proof off the trace shape"
        );
        Self {
            rounds: native
                .rounds
                .iter()
                .map(|r| BatchEvalRoundTrace::alloc(b, r))
                .collect(),
            b_finals: native.b_finals.iter().map(|&v| alloc_block(b, v)).collect(),
        }
    }
}

/// One `(point, value)` claim with a dense expression point — the trace twin
/// of `EvalClaim` as used by the multi-batch layer (points are challenge
/// vectors).
#[derive(Clone)]
pub struct EvalClaimTrace {
    pub point: Vec<LinExpr>,
    pub value: LinExpr,
}

/// One term of a public linear relation: constant boolean point (packed
/// index) and constant coefficient. Trace twin of `LinearEvalTerm` under the
/// structural-points restriction (module docs).
#[derive(Clone)]
pub struct LinearEvalTermTrace {
    /// Packed boolean point: bit `b` of `index` is coordinate `b`.
    pub index: usize,
    /// Flat-basis coefficient. Constant for direction-independent terms;
    /// an affine expression in statement selector bits (e.g. Merkle
    /// direction bits) where the claim shape is the union of data-dependent
    /// branches.
    pub coeff: LinExpr,
}

/// Trace twin of `LinearEvalClaim`: `Σ_j coeff_j · B(point_j) == value`.
#[derive(Clone)]
pub struct LinearEvalClaimTrace {
    pub terms: Vec<LinearEvalTermTrace>,
    pub value: LinExpr,
}

// ---------------------------------------------------------------------------
// Shared transcript pieces
// ---------------------------------------------------------------------------

/// Trace twin of `batch_eval::squeeze_alphas` — the MULTI-LEVEL RLC:
/// `rlc_levels(m)` squeezed challenges, `weight[i] = Π_j c_j^{digit_j(i)}`
/// over the base-64 digits of `i` (soundness note on the native fn). For
/// `m ≤ 64` this is the single-α power ladder (`m − 2` multiplications,
/// wire-identical to the pre-upgrade rule); larger batches cost the level
/// power tables plus `m·(levels−1)` digit-product multiplications.
pub fn squeeze_alphas_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    m: usize,
) -> Vec<LinExpr> {
    use noid_gkr::batch_eval::{rlc_levels, RLC_LEVEL_BASE};
    if m == 0 {
        return Vec::new();
    }
    let levels = rlc_levels(m);
    let cs: Vec<LinExpr> = (0..levels).map(|_| ch.squeeze(b)).collect();
    if levels == 1 {
        let mut alphas = Vec::with_capacity(m);
        let mut acc = LinExpr::constant(F128::ONE);
        for _ in 0..m {
            alphas.push(acc.clone());
            // `acc *= alpha` — the value pushed NEXT iteration; the final
            // multiply is skipped (native computes it and discards).
            if alphas.len() < m {
                acc = if alphas.len() == 1 {
                    cs[0].clone()
                } else {
                    mul(b, &acc, &cs[0])
                };
            }
        }
        return alphas;
    }
    let mut tables: Vec<Vec<LinExpr>> = Vec::with_capacity(levels);
    for (j, c) in cs.iter().enumerate() {
        let digits = RLC_LEVEL_BASE.min((m - 1) / RLC_LEVEL_BASE.pow(j as u32) + 1);
        let mut table = Vec::with_capacity(digits);
        let mut acc = LinExpr::constant(F128::ONE);
        for k in 0..digits {
            table.push(acc.clone());
            if k + 1 < digits {
                acc = if k == 0 { c.clone() } else { mul(b, &acc, c) };
            }
        }
        tables.push(table);
    }
    (0..m)
        .map(|i| {
            let mut w = tables[0][i % RLC_LEVEL_BASE].clone();
            let mut x = i / RLC_LEVEL_BASE;
            for table in &tables[1..] {
                let d = x % RLC_LEVEL_BASE;
                x /= RLC_LEVEL_BASE;
                if d > 0 {
                    w = mul(b, &w, &table[d]);
                }
            }
            w
        })
        .collect()
}

/// Trace twin of the native prebound claim binding: point LENGTH + VALUE
/// per claim, never the point coordinates (they are the channel's own
/// squeezed reduction points, already transcript-determined).
fn absorb_claims_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    claims: &[EvalClaimTrace],
) {
    for c in claims {
        ch.absorb_const_tower(b, c.point.len() as u128);
        ch.absorb(b, &c.value);
    }
}

// Compile-time reference so the boolean tag stays linked to the native
// definition even though the prebound absorb above never emits it.
#[allow(dead_code)]
const _BOOL_TAG_LINK: u128 = CLAIM_POINT_BOOL_TAG;

// ---------------------------------------------------------------------------
// verify_linear_eval_prebound
// ---------------------------------------------------------------------------

/// Trace twin of `batch_eval::verify_linear_eval_prebound`
/// (= `verify_linear_eval_inner` with the `Prebound { relation_tag }`
/// binding). Native `None` returns: shape → asserts; value checks → pins.
pub fn verify_linear_eval_prebound_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    proof: &LinearEvalProofTrace,
    claims: &[LinearEvalClaimTrace],
    n: usize,
    relation_tag: u128,
) -> BatchEvalReductionTrace {
    assert!(!claims.is_empty() && proof.rounds.len() == n);
    for claim in claims {
        assert!(!claim.terms.is_empty());
        for term in &claim.terms {
            assert!(term.index < (1usize << n));
        }
    }

    // absorb_linear_claims_prebound
    let total_terms: usize = claims.iter().map(|c| c.terms.len()).sum();
    ch.absorb_const_tower(b, LINEAR_EVAL_PREBOUND_TAG);
    ch.absorb_const_tower(b, relation_tag);
    ch.absorb_const_tower(b, n as u128);
    ch.absorb_const_tower(b, claims.len() as u128);
    ch.absorb_const_tower(b, total_terms as u128);

    let alphas = squeeze_alphas_trace(b, ch, claims.len());

    // initial_linear_claim: Σ α_i · value_i (α_0 = 1 — free).
    let mut claim = claims[0].value.clone();
    for (c, a) in claims.iter().zip(alphas.iter()).skip(1) {
        claim = claim.add(&mul(b, a, &c.value));
    }

    let mut challenges = Vec::with_capacity(n);
    for re in &proof.rounds {
        re.absorb_evals(b, ch);
        let r_i = ch.squeeze(b);
        claim = re.evaluate(b, &claim.clone(), &r_i);
        challenges.push(r_i);
    }
    challenges.reverse();

    // evaluate_linear_w_at over constant boolean points, shared through the
    // prefix cache; per-claim α weighting mirrors
    // `linear_claim_w_contribution` (α · coeff · eq).
    let mut eq_cache = BooleanPointEqCache::new(&challenges);
    let mut w_at = LinExpr::zero();
    for (c, a) in claims.iter().zip(alphas.iter()) {
        let mut inner = LinExpr::zero();
        for term in &c.terms {
            let eq = eq_cache.eq_at_index(b, term.index);
            if term.coeff.is_const() {
                inner = inner.add(&eq.scale(term.coeff.constant));
            } else {
                inner = inner.add(&mul(b, &eq, &term.coeff));
            }
        }
        // α_0 = 1: the first claim's contribution needs no multiplication.
        if a.is_const() && a.constant == F128::ONE {
            w_at = w_at.add(&inner);
        } else {
            w_at = w_at.add(&mul(b, a, &inner));
        }
    }

    // Final check: claim == W(r_B) · b_final.
    let rhs = mul(b, &w_at, &proof.b_final);
    pin_zero(b, &claim.add(&rhs));

    BatchEvalReductionTrace {
        point: challenges,
        value: proof.b_final.clone(),
    }
}

/// Trace twin of `BatchEvalProof` (single-column batch eval).
pub struct BatchEvalProofTrace {
    pub rounds: Vec<BatchEvalRoundTrace>,
    pub b_final: LinExpr,
}

impl BatchEvalProofTrace {
    pub fn alloc(
        b: &mut FieldR1csBuilder,
        native: &noid_gkr::batch_eval::BatchEvalProof,
        n: usize,
    ) -> Self {
        assert_eq!(
            native.rounds.len(),
            n,
            "batch-eval proof off the trace shape"
        );
        Self {
            rounds: native
                .rounds
                .iter()
                .map(|r| BatchEvalRoundTrace::alloc(b, r))
                .collect(),
            b_final: alloc_block(b, native.b_final),
        }
    }
}

/// Trace twin of `batch_eval::verify_batch_eval` (single column, dense
/// expression points).
pub fn verify_batch_eval_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    proof: &BatchEvalProofTrace,
    claims: &[EvalClaimTrace],
    n: usize,
) -> BatchEvalReductionTrace {
    assert!(!claims.is_empty());
    for c in claims {
        assert_eq!(c.point.len(), n);
    }
    assert_eq!(proof.rounds.len(), n);

    absorb_claims_trace(b, ch, claims);
    let alphas = squeeze_alphas_trace(b, ch, claims.len());

    let mut claim = claims[0].value.clone();
    for (c, a) in claims.iter().zip(alphas.iter()).skip(1) {
        claim = claim.add(&mul(b, a, &c.value));
    }

    let mut challenges = Vec::with_capacity(n);
    for re in &proof.rounds {
        re.absorb_evals(b, ch);
        let r_i = ch.squeeze(b);
        claim = re.evaluate(b, &claim.clone(), &r_i);
        challenges.push(r_i);
    }
    challenges.reverse();

    // claim == W(r_B) · b_final with W = Σ α_i · eq(r_i, r_B).
    let mut w_at = LinExpr::zero();
    for (c, a) in claims.iter().zip(alphas.iter()) {
        let eq = eq_ind_trace(b, &c.point, &challenges);
        if a.is_const() && a.constant == F128::ONE {
            w_at = w_at.add(&eq);
        } else {
            w_at = w_at.add(&mul(b, a, &eq));
        }
    }
    let rhs = mul(b, &w_at, &proof.b_final);
    pin_zero(b, &claim.add(&rhs));

    BatchEvalReductionTrace {
        point: challenges,
        value: proof.b_final.clone(),
    }
}

// ---------------------------------------------------------------------------
// verify_multi_batch_eval
// ---------------------------------------------------------------------------

/// Trace twin of `batch_eval::verify_multi_batch_eval`.
pub fn verify_multi_batch_eval_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    proof: &MultiBatchEvalProofTrace,
    claims_by_column: &[&[EvalClaimTrace]],
    n: usize,
) -> Vec<BatchEvalReductionTrace> {
    assert!(!claims_by_column.is_empty());
    assert_eq!(proof.b_finals.len(), claims_by_column.len());
    for claims in claims_by_column {
        assert!(!claims.is_empty());
        for c in *claims {
            assert_eq!(c.point.len(), n);
        }
    }
    assert_eq!(proof.rounds.len(), n);

    // absorb_multi_claims (prebound schedule)
    ch.absorb_const_tower(b, MULTI_BATCH_EVAL_PREBOUND_TAG);
    ch.absorb_const_tower(b, claims_by_column.len() as u128);
    for (col_idx, claims) in claims_by_column.iter().enumerate() {
        ch.absorb_const_tower(b, col_idx as u128);
        ch.absorb_const_tower(b, claims.len() as u128);
        absorb_claims_trace(b, ch, claims);
    }

    // squeeze_alphas_by_column
    let alphas_by_column: Vec<Vec<LinExpr>> = claims_by_column
        .iter()
        .map(|claims| squeeze_alphas_trace(b, ch, claims.len()))
        .collect();

    // initial_multi_claim
    let mut claim = LinExpr::zero();
    for (claims, alphas) in claims_by_column.iter().zip(alphas_by_column.iter()) {
        for (c, a) in claims.iter().zip(alphas.iter()) {
            if a.is_const() && a.constant == F128::ONE {
                claim = claim.add(&c.value);
            } else {
                claim = claim.add(&mul(b, a, &c.value));
            }
        }
    }

    let mut challenges = Vec::with_capacity(n);
    for re in &proof.rounds {
        re.absorb_evals(b, ch);
        let r_i = ch.squeeze(b);
        claim = re.evaluate(b, &claim.clone(), &r_i);
        challenges.push(r_i);
    }
    challenges.reverse();

    // final_claim = Σ_col W_col(r_B) · b_final_col, with
    // W_col = Σ_i α_i · eq(point_i, r_B) (`evaluate_w_at`).
    let mut final_claim = LinExpr::zero();
    for ((claims, alphas), b_final) in claims_by_column
        .iter()
        .zip(alphas_by_column.iter())
        .zip(proof.b_finals.iter())
    {
        let mut w_at = LinExpr::zero();
        for (c, a) in claims.iter().zip(alphas.iter()) {
            let eq = eq_ind_trace(b, &c.point, &challenges);
            if a.is_const() && a.constant == F128::ONE {
                w_at = w_at.add(&eq);
            } else {
                w_at = w_at.add(&mul(b, a, &eq));
            }
        }
        final_claim = final_claim.add(&mul(b, &w_at, b_final));
    }
    pin_zero(b, &claim.add(&final_claim));

    proof
        .b_finals
        .iter()
        .map(|value| BatchEvalReductionTrace {
            point: challenges.clone(),
            value: value.clone(),
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Tests — lockstep with the native verifiers on real proofs
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::super::flat_of;
    use super::super::test_support::{assert_expr_is, tower_value};
    use super::*;
    use noid_core::mle::evaluate::evaluate_slice;
    use noid_core::transcript::FiatShamir;
    use noid_gkr::batch_eval::{
        prove_linear_eval_prebound, prove_multi_batch_eval, verify_linear_eval_prebound,
        verify_multi_batch_eval, EvalClaim, LinearEvalClaim, LinearEvalTerm,
    };
    use noid_poseidon2b::channel::Poseidon2bChannel;

    fn rand_blocks(seed: u64, n: usize) -> Vec<Block128> {
        let mut s = seed as u128 | 1;
        (0..n)
            .map(|_| {
                s = s
                    .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    .wrapping_add(0xDEAD_BEEF);
                Block128::from(s)
            })
            .collect()
    }

    fn boolean_point(index: usize, n: usize) -> Vec<Block128> {
        (0..n)
            .map(|bit| {
                if (index >> bit) & 1 == 1 {
                    Block128::ONE
                } else {
                    Block128::ZERO
                }
            })
            .collect()
    }

    /// Linear-eval prebound: native prove → native verify AND trace verify;
    /// trace reduction == native reduction; trace R1CS satisfiable. A
    /// value-tampered proof keeps native and trace in agreement (both
    /// reject / unsat).
    #[test]
    fn linear_eval_prebound_trace_lockstep() {
        const TAG: u128 = 0xB001_u128;
        let n = 5usize;
        let table = rand_blocks(11, 1 << n);

        // Three public linear relations over boolean points.
        let mk_claims = |table: &[Block128]| -> Vec<LinearEvalClaim> {
            (0..3usize)
                .map(|k| {
                    let idx_a = (7 * k + 1) % (1 << n);
                    let idx_b = (13 * k + 4) % (1 << n);
                    let coeff_a = Block128::from(3 + k as u128);
                    let coeff_b = Block128::ONE;
                    let value = coeff_a * table[idx_a] + coeff_b * table[idx_b];
                    LinearEvalClaim {
                        terms: vec![
                            LinearEvalTerm {
                                point: boolean_point(idx_a, n),
                                coeff: coeff_a,
                            },
                            LinearEvalTerm {
                                point: boolean_point(idx_b, n),
                                coeff: coeff_b,
                            },
                        ],
                        value,
                    }
                })
                .collect()
        };
        let claims = mk_claims(&table);

        let mut ch_p = Poseidon2bChannel::new();
        ch_p.absorb(Block128::from(77u128));
        let (proof, red_native) = prove_linear_eval_prebound(&table, &claims, TAG, &mut ch_p);

        let mut ch_n = Poseidon2bChannel::new();
        ch_n.absorb(Block128::from(77u128));
        let red_check = verify_linear_eval_prebound(&proof, &claims, n, TAG, &mut ch_n)
            .expect("native accepts");
        assert_eq!(red_native, red_check);

        // Trace replay.
        let mut b = FieldR1csBuilder::new();
        let mut ch = RawChannelTrace::new();
        ch.absorb_const_tower(&mut b, 77);
        let proof_t = LinearEvalProofTrace::alloc(&mut b, &proof, n);
        let claims_t: Vec<LinearEvalClaimTrace> = claims
            .iter()
            .map(|c| LinearEvalClaimTrace {
                terms: c
                    .terms
                    .iter()
                    .map(|t| LinearEvalTermTrace {
                        index: t
                            .point
                            .iter()
                            .enumerate()
                            .map(|(i, v)| ((*v == Block128::ONE) as usize) << i)
                            .sum(),
                        coeff: LinExpr::constant(flat_of(t.coeff)),
                    })
                    .collect(),
                value: super::super::alloc_block(&mut b, c.value),
            })
            .collect();
        let red_t = verify_linear_eval_prebound_trace(&mut b, &mut ch, &proof_t, &claims_t, n, TAG);

        for (e, v) in red_t.point.iter().zip(red_native.point.iter()) {
            assert_expr_is(&b, e, *v, "reduction point");
        }
        assert_expr_is(&b, &red_t.value, red_native.value, "reduction value");
        assert_eq!(
            tower_value(&b, &red_t.value),
            evaluate_slice(&table, &red_native.point)
        );

        let (r1cs, z) = b.build();
        assert!(r1cs.satisfies(&z), "honest linear-eval trace unsatisfiable");
    }

    /// Multi-batch: lockstep on a real 3-column proof + unsat on a tampered
    /// b_final (the same mutation the native test uses).
    #[test]
    fn multi_batch_eval_trace_lockstep_and_tamper() {
        let n = 5usize;
        let columns: Vec<Vec<Block128>> = (0..3).map(|k| rand_blocks(100 + k, 1 << n)).collect();
        let claims_by_column: Vec<Vec<EvalClaim>> = columns
            .iter()
            .enumerate()
            .map(|(k, col)| {
                (0..(k + 1))
                    .map(|j| {
                        let point = rand_blocks(200 + (k * 7 + j) as u64, n);
                        let value = evaluate_slice(col, &point);
                        EvalClaim { point, value }
                    })
                    .collect()
            })
            .collect();
        let column_refs: Vec<&[Block128]> = columns.iter().map(Vec::as_slice).collect();
        let claim_refs: Vec<&[EvalClaim]> = claims_by_column.iter().map(Vec::as_slice).collect();

        let mut ch_p = Poseidon2bChannel::new();
        let (proof, red_native) = prove_multi_batch_eval(&column_refs, &claim_refs, &mut ch_p);
        let mut ch_n = Poseidon2bChannel::new();
        let red_check =
            verify_multi_batch_eval(&proof, &claim_refs, n, &mut ch_n).expect("native accepts");
        assert_eq!(red_native, red_check);

        let build_trace =
            |proof: &MultiBatchEvalProof| -> (FieldR1csBuilder, Vec<BatchEvalReductionTrace>) {
                let mut b = FieldR1csBuilder::new();
                let mut ch = RawChannelTrace::new();
                let proof_t = MultiBatchEvalProofTrace::alloc(&mut b, proof, n, 3);
                let claims_t: Vec<Vec<EvalClaimTrace>> = claims_by_column
                    .iter()
                    .map(|claims| {
                        claims
                            .iter()
                            .map(|c| EvalClaimTrace {
                                point: super::super::alloc_blocks(&mut b, &c.point),
                                value: super::super::alloc_block(&mut b, c.value),
                            })
                            .collect()
                    })
                    .collect();
                let refs: Vec<&[EvalClaimTrace]> = claims_t.iter().map(Vec::as_slice).collect();
                let reds = verify_multi_batch_eval_trace(&mut b, &mut ch, &proof_t, &refs, n);
                (b, reds)
            };

        let (b, reds) = build_trace(&proof);
        assert_eq!(reds.len(), red_native.len());
        for (rt, rn) in reds.iter().zip(red_native.iter()) {
            for (e, v) in rt.point.iter().zip(rn.point.iter()) {
                assert_expr_is(&b, e, *v, "multi reduction point");
            }
            assert_expr_is(&b, &rt.value, rn.value, "multi reduction value");
        }
        let (r1cs, z) = b.build();
        assert!(r1cs.satisfies(&z), "honest multi-batch trace unsatisfiable");

        // Tamper: native rejects, trace unsat.
        let mut bad = proof.clone();
        bad.b_finals[1] += Block128::ONE;
        let mut ch_bad = Poseidon2bChannel::new();
        assert!(verify_multi_batch_eval(&bad, &claim_refs, n, &mut ch_bad).is_none());
        let (b_bad, _) = build_trace(&bad);
        let (r1cs_bad, z_bad) = b_bad.build();
        assert!(
            !r1cs_bad.satisfies(&z_bad),
            "tampered multi-batch trace satisfiable"
        );
    }
}
