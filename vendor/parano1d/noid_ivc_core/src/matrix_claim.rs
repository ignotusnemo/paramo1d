//! Deferred matrix-consistency claims for the self-verification chain.
//!
//! The lincheck verifier's final consistency is a bilinear evaluation of
//! the CONSTANT instance matrices:
//!
//! ```text
//!   final = Σ_{r,c} (α·A + B)[r,c] · u[r] · v[c] + β·v[const_pin]
//!   u[r]  = λ(z_skip)[r mod 64] · eq(x_inner_rest)[r div 64]
//!   v[c]  = z_partial[c mod 64] · eq(r_inner_rest)[c div 64]
//! ```
//!
//! A trace that replays a verifier of ITS OWN proof class cannot bake
//! those matrices as constants (the matrix would have to contain its own
//! description). This module removes the matrices from the trace
//! entirely: the α-batched bilinear form becomes a CLAIM about the
//! stacked matrix `M̂ = [A; B]` (one extra top row bit `b`, with the α
//! weight moved into the multilinear factor `ŵ(b) = α + b·(α+1)`), and
//! each chain link FOLDS its fresh structured claim with the incoming
//! accumulated claim into one plain MLE claim `M̂~(point) = value`,
//! carried in the link's public IO. Only the DECIDER ever touches the
//! matrix: one native `M̂~` evaluation against the final accumulator.
//!
//! The fold is two dense product sumchecks (domain split, everything
//! O(nnz + 2^{k_log}) for the prover, O(k_log) rounds for the verifier):
//!
//! - Phase 1 over `y = (r, b)`:
//!   `t + γ·gate·w_in = Σ_y [ ŵu(y)·G_v(y) + γ·gate·eq(p_in^{rb}, y)·G_e(y) ]`
//!   with `G_v = M̂·v`, `G_e = M̂·eq(p_in^c, ·)` dense row images.
//! - Phase 2 over `c`, after batching the two derived G-claims with δ:
//!   `G_v~(ρ) + δ·gate·G_e~(ρ) = Σ_c H(c)·[v(c) + δ·gate·eq(p_in^c, c)]`
//!   with `H(c) = Σ_y eq(ρ, y)·M̂[y, c]`; its final value is exactly
//!   `M̂~(ρ ‖ σ)` — the outgoing accumulator claim.
//!
//! Claim point order: `point = [ρ_0..ρ_{k_log}] ‖ [σ_0..σ_{k_log−1}]`
//! where ρ covers the row bits LSB-first with the stack bit `b` LAST
//! (index `k_log`), and σ covers the column bits LSB-first.
//!
//! The genesis link has no incoming claim: `gate = 0` multiplies the
//! incoming weight out of BOTH phases, and the accumulator degenerates
//! to the fresh claim's reduction.

use crate::challenger::Challenger;
use crate::field::{F128, F256Unreduced};
use crate::field_r1cs::{
    CompactFieldR1cs, FieldR1cs, FieldR1csArtifactError, FieldR1csArtifactMatrix,
};
use crate::lincheck::build_eq_table;
use crate::proof::FieldShape;
use crate::zerocheck::multilinear::lagrange_weights_naive;
use noid_poseidon2b::native::poseidon2b_hash_byte_slices;
use rayon::prelude::*;

pub mod c1;
pub mod sparse_c1;

const MATRIX_CLAIM_REQUEST_DOMAIN: &[u8] = b"NOID/IVC/MATRIX-CLAIM-REQUEST/V1";

/// A plain accumulated claim `M̂~(point) = value` on the stacked matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixAccClaim {
    /// `2·k_log + 1` coordinates (see the module docs for the order).
    pub point: Vec<F128>,
    pub value: F128,
}

impl MatrixAccClaim {
    pub fn zero(k_log: usize) -> Self {
        Self {
            point: vec![F128::ZERO; 2 * k_log + 1],
            value: F128::ZERO,
        }
    }
}

/// The structured claim a deferred lincheck final emits: the transcript
/// ingredients that define `u`, `v`, the α weight and the claimed value
/// `t = Σ ŵ(b)·u[r]·v[c]·M̂[(r,b),c]`.
#[derive(Clone, Debug)]
pub struct FreshLincheckClaim {
    pub alpha: F128,
    pub z_skip: F128,
    pub x_inner_rest: Vec<F128>,
    pub r_inner_rest: Vec<F128>,
    pub z_partial: Vec<F128>,
    pub value: F128,
}

/// Authenticated evaluations produced by a matrix claim source in one pass.
///
/// The structural digest is deliberately returned alongside the values: a
/// caller must compare it with its canonical class registry before accepting
/// either optional evaluation.  Disk-backed implementations compute all
/// requested values from the exact row bytes fed into this digest, so a
/// matrix never needs to be materialized as a resident [`FieldR1cs`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthenticatedMatrixClaimEvaluations {
    structural_digest: [u8; 32],
    request_binding: [u8; 32],
    fresh_value: Option<F128>,
    accumulated_value: Option<F128>,
}

impl AuthenticatedMatrixClaimEvaluations {
    pub const fn structural_digest(&self) -> [u8; 32] {
        self.structural_digest
    }

    pub const fn fresh_value(&self) -> Option<F128> {
        self.fresh_value
    }

    pub const fn accumulated_value(&self) -> Option<F128> {
        self.accumulated_value
    }

    /// Prove that these values were evaluated for these exact claim objects,
    /// not replayed by an external evaluator implementation from another
    /// otherwise-valid call.
    pub fn is_bound_to(
        &self,
        fresh: Option<&FreshLincheckClaim>,
        accumulated: Option<&MatrixAccClaim>,
    ) -> bool {
        self.request_binding == matrix_claim_request_binding(fresh, accumulated)
    }

    pub(crate) fn new(
        structural_digest: [u8; 32],
        fresh: Option<&FreshLincheckClaim>,
        accumulated: Option<&MatrixAccClaim>,
        fresh_value: Option<F128>,
        accumulated_value: Option<F128>,
    ) -> Self {
        Self {
            structural_digest,
            request_binding: matrix_claim_request_binding(fresh, accumulated),
            fresh_value,
            accumulated_value,
        }
    }
}

fn matrix_claim_request_binding(
    fresh: Option<&FreshLincheckClaim>,
    accumulated: Option<&MatrixAccClaim>,
) -> [u8; 32] {
    fn push_field(bytes: &mut Vec<u8>, value: F128) {
        bytes.extend_from_slice(&value.lo.to_le_bytes());
        bytes.extend_from_slice(&value.hi.to_le_bytes());
    }

    fn push_fields(bytes: &mut Vec<u8>, values: &[F128]) {
        bytes.extend_from_slice(&(values.len() as u64).to_le_bytes());
        for &value in values {
            push_field(bytes, value);
        }
    }

    let fresh_fields = fresh.map_or(0, |claim| {
        4usize
            .saturating_add(claim.x_inner_rest.len())
            .saturating_add(claim.r_inner_rest.len())
            .saturating_add(claim.z_partial.len())
    });
    let accumulated_fields = accumulated.map_or(0, |claim| 1 + claim.point.len());
    let mut bytes = Vec::with_capacity(
        2 + 4 * 8
            + fresh_fields
                .saturating_add(accumulated_fields)
                .saturating_mul(16),
    );
    bytes.push(u8::from(fresh.is_some()));
    if let Some(claim) = fresh {
        push_field(&mut bytes, claim.alpha);
        push_field(&mut bytes, claim.z_skip);
        push_fields(&mut bytes, &claim.x_inner_rest);
        push_fields(&mut bytes, &claim.r_inner_rest);
        push_fields(&mut bytes, &claim.z_partial);
        push_field(&mut bytes, claim.value);
    }
    bytes.push(u8::from(accumulated.is_some()));
    if let Some(claim) = accumulated {
        push_fields(&mut bytes, &claim.point);
        push_field(&mut bytes, claim.value);
    }
    poseidon2b_hash_byte_slices(MATRIX_CLAIM_REQUEST_DOMAIN, &[&bytes])
}

/// Bounded matrix-evaluation boundary used by the terminal history decider.
///
/// At most one fresh and one accumulated claim are needed for a class at a
/// time.  Keeping that bound in the API lets an on-disk implementation scan
/// both canonical matrices once with fixed-size buffers.  Implementations
/// must either recompute `structural_digest` from the same rows used for the
/// evaluations, or retain a core-authenticated immutable byte backing whose
/// exact rows were structurally authenticated at construction. Cached or
/// externally supplied digest metadata alone is not valid authority here. The
/// success object has no public constructor: external adapters may delegate to
/// a core evaluator, but cannot manufacture a digest or claim value in safe
/// Rust.
pub trait MatrixClaimEvaluator {
    fn field_shape(&self) -> FieldShape;

    fn evaluate_matrix_claims(
        &mut self,
        fresh: Option<&FreshLincheckClaim>,
        accumulated: Option<&MatrixAccClaim>,
    ) -> Result<AuthenticatedMatrixClaimEvaluations, FieldR1csArtifactError>;
}

fn evaluate_field_r1cs_claims(
    matrix: &FieldR1cs,
    fresh: Option<&FreshLincheckClaim>,
    accumulated: Option<&MatrixAccClaim>,
    digest: [u8; 32],
) -> Result<AuthenticatedMatrixClaimEvaluations, FieldR1csArtifactError> {
    if let Some(claim) = fresh {
        let rest = matrix.k_log - matrix.k_skip;
        if claim.x_inner_rest.len() != rest || claim.r_inner_rest.len() != rest {
            return Err(FieldR1csArtifactError::MatrixClaimShape(
                "fresh inner-rest width",
            ));
        }
        if claim.z_partial.len() != 1usize << matrix.k_skip {
            return Err(FieldR1csArtifactError::MatrixClaimShape(
                "fresh partial window",
            ));
        }
    }
    if accumulated.is_some_and(|claim| claim.point.len() != 2 * matrix.k_log + 1) {
        return Err(FieldR1csArtifactError::MatrixClaimShape(
            "accumulated point width",
        ));
    }
    Ok(AuthenticatedMatrixClaimEvaluations::new(
        digest,
        fresh,
        accumulated,
        fresh.map(|claim| fresh_claim_value(matrix, claim)),
        accumulated.map(|claim| stacked_matrix_mle_eval(matrix, claim)),
    ))
}

impl MatrixClaimEvaluator for FieldR1cs {
    fn field_shape(&self) -> FieldShape {
        FieldShape::of(self)
    }

    fn evaluate_matrix_claims(
        &mut self,
        fresh: Option<&FreshLincheckClaim>,
        accumulated: Option<&MatrixAccClaim>,
    ) -> Result<AuthenticatedMatrixClaimEvaluations, FieldR1csArtifactError> {
        let digest = self.structural_statement_digest();
        evaluate_field_r1cs_claims(self, fresh, accumulated, digest)
    }
}

/// Proof wires of one accumulator fold: phase-1 rounds (`k_log + 1`),
/// the two derived G values, phase-2 rounds (`k_log`), and the final
/// matrix evaluation (= the outgoing claim value).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixFoldProof {
    /// Compressed degree-2 rounds `[c_0, c_2]`.
    pub phase1_rounds: Vec<[F128; 2]>,
    pub g_v: F128,
    pub g_e: F128,
    pub phase2_rounds: Vec<[F128; 2]>,
    pub final_matrix_eval: F128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MatrixFoldError {
    Shape,
    FinalMismatch,
}

impl std::fmt::Display for MatrixFoldError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MatrixFoldError::Shape => write!(f, "matrix fold proof shape mismatch"),
            MatrixFoldError::FinalMismatch => write!(f, "matrix fold final mismatch"),
        }
    }
}

/// eq(a, b) over two equal-length coordinate vectors.
pub fn eq_points(a: &[F128], b: &[F128]) -> F128 {
    assert_eq!(a.len(), b.len());
    let mut acc = F128::ONE;
    for (x, y) in a.iter().zip(b.iter()) {
        acc = acc * (*x * *y + (F128::ONE + *x) * (F128::ONE + *y));
    }
    acc
}

/// MLE of a small value vector (the λ / z_partial 64-slot windows) at a
/// point of `log2(len)` coordinates.
pub fn small_mle_eval(values: &[F128], point: &[F128]) -> F128 {
    assert_eq!(values.len(), 1usize << point.len());
    let eq = build_eq_table(point);
    let mut acc = F128::ZERO;
    for (v, e) in values.iter().zip(eq.iter()) {
        acc += *v * *e;
    }
    acc
}

/// `ŵ(x_b) = α + x_b·(α + 1)`: the multilinear α weight of the stack bit
/// (`ŵ(0) = α` selects A, `ŵ(1) = 1` selects B).
fn alpha_weight(alpha: F128, x_b: F128) -> F128 {
    alpha + x_b * (alpha + F128::ONE)
}

/// The u-side weight MLE at a row point (λ window on the low `k_skip`
/// coordinates, eq(x_inner_rest) on the rest, ŵ on the stack bit).
fn u_weight_eval(fresh: &FreshLincheckClaim, k_skip: usize, rho: &[F128]) -> F128 {
    let ell_log = k_skip;
    let lambda = lagrange_weights_naive(k_skip, fresh.z_skip);
    let lam = small_mle_eval(&lambda, &rho[..ell_log]);
    let e = eq_points(&fresh.x_inner_rest, &rho[ell_log..rho.len() - 1]);
    let w = alpha_weight(fresh.alpha, rho[rho.len() - 1]);
    lam * e * w
}

/// The v-side weight MLE at a column point.
fn v_weight_eval(fresh: &FreshLincheckClaim, k_skip: usize, sigma: &[F128]) -> F128 {
    let zp = small_mle_eval(&fresh.z_partial, &sigma[..k_skip]);
    let q = eq_points(&fresh.r_inner_rest, &sigma[k_skip..]);
    zp * q
}

fn absorb_fold_header<Ch: Challenger>(
    ch: &mut Ch,
    fresh: &FreshLincheckClaim,
    incoming: &MatrixAccClaim,
    gate: F128,
) {
    ch.observe_label(b"history-matrix-claim-fold-v0");
    ch.observe_f128(fresh.alpha);
    ch.observe_f128(fresh.z_skip);
    ch.observe_f128_slice(&fresh.x_inner_rest);
    ch.observe_f128_slice(&fresh.r_inner_rest);
    ch.observe_f128_slice(&fresh.z_partial);
    ch.observe_f128(fresh.value);
    ch.observe_f128_slice(&incoming.point);
    ch.observe_f128(incoming.value);
    ch.observe_f128(gate);
}

/// Fold one dense MLE table while rotating a caller-owned spare allocation.
///
/// The previous parallel path collected a fresh `Vec` for every table in
/// every large round. At m22 that is 52 allocator round trips in phase 1 and
/// 24 more in phase 2, repeatedly releasing/reacquiring buffers on the
/// memory-bandwidth critical path. The first large fold below allocates one
/// half-sized spare; subsequent folds rotate the just-consumed input
/// allocation into `spare`, so every later round writes into an already
/// allocated buffer.
///
/// Returning both vectors also keeps this entirely safe: while Rayon writes
/// the spare, the input is immutably borrowed and the two allocations cannot
/// alias.  Small tails stay in place, where allocator avoidance matters more
/// than parallelism.
fn fold_table_pairs_reusing(
    mut table: Vec<F128>,
    mut spare: Vec<F128>,
    r: F128,
) -> (Vec<F128>, Vec<F128>) {
    debug_assert!(table.len().is_power_of_two());
    let half = table.len() / 2;
    if half >= 1024 {
        if spare.len() < half {
            // This occurs only for the first large fold of the phase. Every
            // consumed input thereafter remains initialized and becomes the
            // next spare. Let Rayon's collector initialize this first output
            // directly, without a redundant zero-fill pass.
            let folded = (0..half)
                .into_par_iter()
                .map(|p| {
                    let a = table[2 * p];
                    let b = table[2 * p + 1];
                    a + r * (a + b)
                })
                .collect();
            return (folded, table);
        }
        spare.truncate(half);
        spare.par_iter_mut().enumerate().for_each(|(p, folded)| {
            let a = table[2 * p];
            let b = table[2 * p + 1];
            *folded = a + r * (a + b);
        });
        // Keep the consumed input initialized: the next fold can truncate and
        // overwrite it without a redundant zero-fill pass.
        (spare, table)
    } else {
        for p in 0..half {
            let a = table[2 * p];
            let b = table[2 * p + 1];
            table[p] = a + r * (a + b);
        }
        table.truncate(half);
        (table, spare)
    }
}

#[cfg(test)]
fn fold_table_pairs_reference(table: &mut Vec<F128>, r: F128) {
    let half = table.len() / 2;
    let folded = (0..half)
        .map(|p| {
            let a = table[2 * p];
            let b = table[2 * p + 1];
            a + r * (a + b)
        })
        .collect();
    *table = folded;
}

/// One degree-2 product-sumcheck round over two products, already in the
/// compressed wire basis `[c_0, c_2]`.
///
/// For one pair, the affine extensions are
/// `w(t) = w_0 + t·(w_0 + w_1)` and `g(t) = g_0 + t·(g_0 + g_1)`.  Their
/// product therefore contributes `w_0·g_0` to `c_0` and
/// `(w_0+w_1)·(g_0+g_1)` to `c_2`.  Computing those coefficients directly
/// avoids evaluating at 1 and 2 and then interpolating the values back into
/// the exact same wire.
fn round_coefficients_two_products(
    w1: &[F128],
    g1: &[F128],
    w2: &[F128],
    g2: &[F128],
) -> [F128; 2] {
    debug_assert_eq!(w1.len(), g1.len());
    debug_assert_eq!(w1.len(), w2.len());
    debug_assert_eq!(w1.len(), g2.len());
    let half = w1.len() / 2;
    let deferred = (0..half)
        .into_par_iter()
        .fold(
            || [F256Unreduced::ZERO; 2],
            |mut acc, p| {
                let pairs = [
                    (w1[2 * p], w1[2 * p + 1], g1[2 * p], g1[2 * p + 1]),
                    (w2[2 * p], w2[2 * p + 1], g2[2 * p], g2[2 * p + 1]),
                ];
                for (w0, w1v, g0, g1v) in pairs {
                    let wd = w0 + w1v;
                    let gd = g0 + g1v;
                    // Reduction is F2-linear. Accumulate the carry-less
                    // 256-bit products with XOR and reduce only the two final
                    // coefficients after Rayon has combined every shard.
                    acc[0] ^= w0.mul_unreduced(g0);
                    acc[1] ^= wd.mul_unreduced(gd);
                }
                acc
            },
        )
        .reduce(
            || [F256Unreduced::ZERO; 2],
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(b.iter()) {
                    *x ^= *y;
                }
                a
            },
        );
    deferred.map(F256Unreduced::reduce)
}

/// One-product twin used by phase 2.  Keeping this separate means the hot
/// path neither allocates nor scans two width-`k` all-zero tables merely to
/// feed the generic two-product kernel.
fn round_coefficients_one_product(w: &[F128], g: &[F128]) -> [F128; 2] {
    debug_assert_eq!(w.len(), g.len());
    let half = w.len() / 2;
    let deferred = (0..half)
        .into_par_iter()
        .fold(
            || [F256Unreduced::ZERO; 2],
            |mut acc, p| {
                let w0 = w[2 * p];
                let w1 = w[2 * p + 1];
                let g0 = g[2 * p];
                let g1 = g[2 * p + 1];
                acc[0] ^= w0.mul_unreduced(g0);
                acc[1] ^= (w0 + w1).mul_unreduced(g0 + g1);
                acc
            },
        )
        .reduce(
            || [F256Unreduced::ZERO; 2],
            |mut a, b| {
                a[0] ^= b[0];
                a[1] ^= b[1];
                a
            },
        );
    deferred.map(F256Unreduced::reduce)
}

/// Materialize `w += scale·e` and compute phase 2's first round coefficients
/// in the same dense pass.
///
/// `scale` is transcript-derived after phase 1, so the mix cannot happen any
/// earlier. Once it is known, however, scanning the newly mixed table again
/// just to form round zero is redundant. Unreduced XOR accumulation makes the
/// fused reduction byte-identical for every Rayon partitioning.
fn mix_and_round_coefficients_one_product(
    w: &mut [F128],
    e: &[F128],
    g: &[F128],
    scale: F128,
) -> [F128; 2] {
    debug_assert_eq!(w.len(), e.len());
    debug_assert_eq!(w.len(), g.len());
    debug_assert_eq!(w.len() % 2, 0);
    let deferred = w
        .par_chunks_exact_mut(2)
        .zip(e.par_chunks_exact(2))
        .zip(g.par_chunks_exact(2))
        .fold(
            || [F256Unreduced::ZERO; 2],
            |mut acc, ((w_pair, e_pair), g_pair)| {
                let w0 = w_pair[0] + scale * e_pair[0];
                let w1 = w_pair[1] + scale * e_pair[1];
                w_pair[0] = w0;
                w_pair[1] = w1;
                acc[0] ^= w0.mul_unreduced(g_pair[0]);
                acc[1] ^= (w0 + w1).mul_unreduced(g_pair[0] + g_pair[1]);
                acc
            },
        )
        .reduce(
            || [F256Unreduced::ZERO; 2],
            |mut a, b| {
                a[0] ^= b[0];
                a[1] ^= b[1];
                a
            },
        );
    deferred.map(F256Unreduced::reduce)
}

/// Previous three-evaluation implementation retained solely as an independent
/// test oracle for the direct coefficient kernels above.
#[cfg(test)]
fn round_evals_two_products_reference(
    w1: &[F128],
    g1: &[F128],
    w2: &[F128],
    g2: &[F128],
) -> [F128; 3] {
    let half = w1.len() / 2;
    let two = F128 { lo: 2, hi: 0 };
    (0..half)
        .into_par_iter()
        .fold(
            || [F128::ZERO; 3],
            |mut acc, p| {
                let pairs = [
                    (w1[2 * p], w1[2 * p + 1], g1[2 * p], g1[2 * p + 1]),
                    (w2[2 * p], w2[2 * p + 1], g2[2 * p], g2[2 * p + 1]),
                ];
                for (w0, w1v, g0, g1v) in pairs {
                    let wd = w0 + w1v;
                    let gd = g0 + g1v;
                    acc[0] += w0 * g0;
                    acc[1] += w1v * g1v;
                    let w2v = w0 + two * wd;
                    let g2v = g0 + two * gd;
                    acc[2] += w2v * g2v;
                }
                acc
            },
        )
        .reduce(
            || [F128::ZERO; 3],
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(b.iter()) {
                    *x += *y;
                }
                a
            },
        )
}

#[cfg(test)]
fn round_coefficients_two_products_reference(
    w1: &[F128],
    g1: &[F128],
    w2: &[F128],
    g2: &[F128],
) -> [F128; 2] {
    let evals = round_evals_two_products_reference(w1, g1, w2, g2);
    let two = F128 { lo: 2, hi: 0 };
    let c0 = evals[0];
    let s1 = evals[1] + c0;
    let s2 = evals[2] + c0;
    let det_inv = crate::deep_chain::f128_inv_pub(two * two + two);
    let c2 = (s2 + two * s1) * det_inv;
    [c0, c2]
}

/// Run one phase of the fold: a degree-2 sumcheck over two product terms
/// with compressed `[c_0, c_2]` round wires. Returns (rounds, point).
fn run_phase<Ch: Challenger>(
    mut claim: F128,
    mut w1: Vec<F128>,
    mut g1: Vec<F128>,
    mut w2: Vec<F128>,
    mut g2: Vec<F128>,
    ch: &mut Ch,
) -> (Vec<[F128; 2]>, Vec<F128>, F128, [F128; 4]) {
    let n_rounds = w1.len().trailing_zeros() as usize;
    let mut rounds = Vec::with_capacity(n_rounds);
    let mut point = Vec::with_capacity(n_rounds);
    // One rotating allocation serves all four tables and all rounds. Its
    // first allocation is only half a table, matching the old path's peak
    // scratch rather than reserving four ping-pong buffers up front.
    let mut spare = Vec::new();
    for _ in 0..n_rounds {
        let [c0, c2] = round_coefficients_two_products(&w1, &g1, &w2, &g2);
        // In characteristic two, P(0) + P(1) = c1 + c2.
        let c1 = claim + c2;
        let wire = [c0, c2];
        ch.observe_f128_slice(&wire);
        let r = ch.sample_f128();
        claim = (c2 * r + c1) * r + c0;
        rounds.push(wire);
        point.push(r);
        (w1, spare) = fold_table_pairs_reusing(w1, spare, r);
        (g1, spare) = fold_table_pairs_reusing(g1, spare, r);
        (w2, spare) = fold_table_pairs_reusing(w2, spare, r);
        (g2, spare) = fold_table_pairs_reusing(g2, spare, r);
    }
    (rounds, point, claim, [w1[0], g1[0], w2[0], g2[0]])
}

/// One-product phase with the same compressed wire and transcript schedule.
fn run_phase_one_product<Ch: Challenger>(
    mut claim: F128,
    mut w: Vec<F128>,
    mut g: Vec<F128>,
    mut first_round_coefficients: Option<[F128; 2]>,
    ch: &mut Ch,
) -> (Vec<[F128; 2]>, Vec<F128>, F128, [F128; 2]) {
    let n_rounds = w.len().trailing_zeros() as usize;
    let mut rounds = Vec::with_capacity(n_rounds);
    let mut point = Vec::with_capacity(n_rounds);
    let mut spare = Vec::new();
    for _ in 0..n_rounds {
        let [c0, c2] = first_round_coefficients
            .take()
            .unwrap_or_else(|| round_coefficients_one_product(&w, &g));
        let c1 = claim + c2;
        let wire = [c0, c2];
        ch.observe_f128_slice(&wire);
        let r = ch.sample_f128();
        claim = (c2 * r + c1) * r + c0;
        rounds.push(wire);
        point.push(r);
        (w, spare) = fold_table_pairs_reusing(w, spare, r);
        (g, spare) = fold_table_pairs_reusing(g, spare, r);
    }
    (rounds, point, claim, [w[0], g[0]])
}

/// Frozen pre-optimization phase implementation used to prove that the
/// direct-coefficient kernel and rotating buffers leave every transcript wire
/// and challenge byte-identical. Keep this independent (three evaluations,
/// interpolation, allocating folds) so the test cannot merely repeat the
/// production implementation's mistake.
#[cfg(test)]
fn run_phase_reference<Ch: Challenger>(
    mut claim: F128,
    mut w1: Vec<F128>,
    mut g1: Vec<F128>,
    mut w2: Vec<F128>,
    mut g2: Vec<F128>,
    ch: &mut Ch,
) -> (Vec<[F128; 2]>, Vec<F128>, F128, [F128; 4]) {
    let n_rounds = w1.len().trailing_zeros() as usize;
    let mut rounds = Vec::with_capacity(n_rounds);
    let mut point = Vec::with_capacity(n_rounds);
    let two = F128 { lo: 2, hi: 0 };
    let det_inv = crate::deep_chain::f128_inv_pub(two * two + two);
    for _ in 0..n_rounds {
        let evals = round_evals_two_products_reference(&w1, &g1, &w2, &g2);
        let c0 = evals[0];
        let s1 = evals[1] + c0;
        let s2 = evals[2] + c0;
        let c2 = (s2 + two * s1) * det_inv;
        let c1 = s1 + c2;
        debug_assert_eq!(evals[0] + evals[1], claim);
        let wire = [c0, c2];
        ch.observe_f128_slice(&wire);
        let r = ch.sample_f128();
        claim = (c2 * r + c1) * r + c0;
        rounds.push(wire);
        point.push(r);
        fold_table_pairs_reference(&mut w1, r);
        fold_table_pairs_reference(&mut g1, r);
        fold_table_pairs_reference(&mut w2, r);
        fold_table_pairs_reference(&mut g2, r);
    }
    (rounds, point, claim, [w1[0], g1[0], w2[0], g2[0]])
}

/// Equality tensor with an initial scalar already folded into every entry.
/// Starting from `scale` instead of one removes a separate width-sized pass.
fn build_eq_table_scaled(point: &[F128], scale: F128) -> Vec<F128> {
    let length = 1usize << point.len();
    if scale == F128::ZERO {
        return vec![F128::ZERO; length];
    }
    let mut out = Vec::with_capacity(length);
    out.push(scale);
    for (j, &r) in point.iter().enumerate() {
        let one_plus_r = F128::ONE + r;
        let len = 1usize << j;
        out.resize(2 * len, F128::ZERO);
        for i in 0..len {
            let value = out[i];
            out[i + len] = value * r;
            out[i] = value * one_plus_r;
        }
    }
    out
}

/// Stacked fresh-row weight `[α·(λ⊗eq), λ⊗eq]`.  The shared base
/// half is formed once, then copied verbatim to B while A receives its one
/// required `α` multiplication.
fn build_stacked_u_weights(
    k_log: usize,
    k_skip: usize,
    alpha: F128,
    lambda: &[F128],
    e_tensor: &[F128],
) -> Vec<F128> {
    let k = 1usize << k_log;
    let ell = 1usize << k_skip;
    assert_eq!(lambda.len(), ell);
    assert_eq!(e_tensor.len(), k >> k_skip);
    let mut weights = vec![F128::ZERO; 2 * k];
    let (weights_a, weights_b) = weights.split_at_mut(k);
    weights_a
        .par_chunks_mut(ell)
        .zip(weights_b.par_chunks_mut(ell))
        .zip(e_tensor.par_iter())
        .for_each(|((a_chunk, b_chunk), &e)| {
            for ((a_slot, b_slot), &lam) in a_chunk
                .iter_mut()
                .zip(b_chunk.iter_mut())
                .zip(lambda.iter())
            {
                let base = lam * e;
                *a_slot = base * alpha;
                *b_slot = base;
            }
        });
    weights
}

/// Native row source for the matrix-fold prover.
///
/// The compact variant walks the canonical planar streams authenticated by
/// [`CompactFieldR1cs::open`] directly.  Keeping the two representations
/// behind this private enum makes the transcript-producing implementation a
/// single source of truth: compact and resident CSR proofs cannot drift.
enum MatrixFoldRows<'a> {
    Resident(&'a FieldR1cs),
    Compact(&'a CompactFieldR1cs),
}

impl MatrixFoldRows<'_> {
    #[inline]
    fn storage_name(&self) -> &'static str {
        match self {
            Self::Resident(_) => "resident",
            Self::Compact(r1cs) => r1cs.storage_name(),
        }
    }

    #[inline]
    fn k_log(&self) -> usize {
        match self {
            Self::Resident(r1cs) => r1cs.k_log,
            Self::Compact(r1cs) => r1cs.shape().k_log,
        }
    }

    #[inline]
    fn k_skip(&self) -> usize {
        match self {
            Self::Resident(r1cs) => r1cs.k_skip,
            Self::Compact(r1cs) => r1cs.shape().k_skip,
        }
    }

    /// Fill the two stacked row images used by phase 1. Each compact group
    /// owns a disjoint 2048-row output window, so Rayon can decode straight
    /// into the final dense tables without a CSR or reduction buffers.
    fn fill_row_images(&self, v_table: &[F128], e_c: &[F128], g_v: &mut [F128], g_e: &mut [F128]) {
        let k = 1usize << self.k_log();
        debug_assert_eq!(g_v.len(), 2 * k);
        debug_assert_eq!(g_e.len(), 2 * k);
        match self {
            Self::Resident(r1cs) => {
                let halves = [(&r1cs.a_0, 0usize), (&r1cs.b_0, k)];
                for (matrix, offset) in halves {
                    g_v.par_iter_mut()
                        .zip(g_e.par_iter_mut())
                        .skip(offset)
                        .take(k)
                        .enumerate()
                        .for_each(|(row, (gv, ge))| {
                            if row < matrix.num_rows {
                                let mut gv_deferred = F256Unreduced::ZERO;
                                let mut ge_deferred = F256Unreduced::ZERO;
                                for (column, coefficient) in matrix.row(row) {
                                    gv_deferred ^=
                                        coefficient.mul_unreduced(v_table[column as usize]);
                                    ge_deferred ^= coefficient.mul_unreduced(e_c[column as usize]);
                                }
                                // Characteristic-two reduction is linear:
                                // one reduction per row is bit-identical to
                                // reducing and XORing every product.
                                *gv = gv_deferred.reduce();
                                *ge = ge_deferred.reduce();
                            }
                        });
                }
            }
            Self::Compact(r1cs) => {
                const GROUP_ROWS: usize = 2048;
                for (side, offset) in [
                    (FieldR1csArtifactMatrix::A, 0usize),
                    (FieldR1csArtifactMatrix::B, k),
                ] {
                    g_v[offset..offset + k]
                        .par_chunks_mut(GROUP_ROWS)
                        .zip(g_e[offset..offset + k].par_chunks_mut(GROUP_ROWS))
                        .enumerate()
                        .for_each(|(group, (gv_group, ge_group))| {
                            let mut current_row = None;
                            let mut gv_deferred = F256Unreduced::ZERO;
                            let mut ge_deferred = F256Unreduced::ZERO;
                            let visited = r1cs.for_each_matrix_group_entry(
                                side,
                                group,
                                |row, column, coefficient| {
                                    if current_row != Some(row) {
                                        if let Some(previous_row) = current_row {
                                            let local_row = previous_row - group * GROUP_ROWS;
                                            gv_group[local_row] = gv_deferred.reduce();
                                            ge_group[local_row] = ge_deferred.reduce();
                                        }
                                        current_row = Some(row);
                                        gv_deferred = F256Unreduced::ZERO;
                                        ge_deferred = F256Unreduced::ZERO;
                                    }
                                    let local_row = row - group * GROUP_ROWS;
                                    debug_assert!(local_row < gv_group.len());
                                    gv_deferred ^=
                                        coefficient.mul_unreduced(v_table[column as usize]);
                                    ge_deferred ^= coefficient.mul_unreduced(e_c[column as usize]);
                                },
                            );
                            assert!(visited, "enumerated compact matrix group exists");
                            if let Some(row) = current_row {
                                let local_row = row - group * GROUP_ROWS;
                                gv_group[local_row] = gv_deferred.reduce();
                                ge_group[local_row] = ge_deferred.reduce();
                            }
                        });
                }
            }
        }
    }

    /// Compute `H(c) = sum_y eq(rho,y) M[y,c]` for phase 2. Resident CSR keeps
    /// one private accumulator per A/B side. The compact production path
    /// parallelizes authenticated row groups into one char-2 accumulator, so
    /// m22 scratch is 64 MiB rather than two 64-MiB side tables.
    fn weighted_column_image(&self, eq_rho: &FactoredEqTable) -> Vec<F128> {
        let k = 1usize << self.k_log();
        match self {
            Self::Resident(r1cs) => {
                let parts: Vec<Vec<F128>> = [(&r1cs.a_0, 0usize), (&r1cs.b_0, k)]
                    .par_iter()
                    .map(|(matrix, offset)| {
                        let mut acc = vec![F128::ZERO; k];
                        for row in 0..matrix.num_rows {
                            let weight = eq_rho.value(*offset + row);
                            if weight == F128::ZERO {
                                continue;
                            }
                            for (column, coefficient) in matrix.row(row) {
                                acc[column as usize] += coefficient * weight;
                            }
                        }
                        acc
                    })
                    .collect();
                // Reuse one side accumulator as the final H table. Allocating
                // a third k-wide output here costs another 64 MiB at m22.
                let mut parts = parts.into_iter();
                let mut h = parts.next().expect("A-side matrix-fold accumulator");
                for part in parts {
                    h.par_iter_mut()
                        .zip(part.par_iter())
                        .for_each(|(slot, value)| *slot += *value);
                }
                h
            }
            Self::Compact(r1cs) => r1cs.stacked_weighted_column_image(&|row| eq_rho.value(row)),
        }
    }
}

/// Shared transcript-producing implementation for resident CSR and compact
/// authenticated artifacts.
fn prove_matrix_claim_fold_from_rows<Ch: Challenger>(
    rows: MatrixFoldRows<'_>,
    fresh: &FreshLincheckClaim,
    incoming: &MatrixAccClaim,
    gate: bool,
    ch: &mut Ch,
) -> (MatrixFoldProof, MatrixAccClaim) {
    let timing = std::env::var_os("NOIDH_MATRIX_FOLD_TIMING").is_some();
    let total_started = std::time::Instant::now();
    let storage = rows.storage_name();
    let k_log = rows.k_log();
    let k_skip = rows.k_skip();
    let k = 1usize << k_log;
    assert_eq!(fresh.x_inner_rest.len(), k_log - k_skip);
    assert_eq!(fresh.r_inner_rest.len(), k_log - k_skip);
    assert_eq!(fresh.z_partial.len(), 1usize << k_skip);
    assert_eq!(incoming.point.len(), 2 * k_log + 1);

    let gate_f = if gate { F128::ONE } else { F128::ZERO };
    absorb_fold_header(ch, fresh, incoming, gate_f);
    let gamma = ch.sample_f128();

    let (p_in_row, p_in_col) = incoming.point.split_at(k_log + 1);

    // Dense weight/value tables.
    // v(c) = z_partial[c mod 64]·eq(r_inner_rest)[c div 64].
    let tables_started = std::time::Instant::now();
    let q_tensor = build_eq_table(&fresh.r_inner_rest);
    let mut v_table = vec![F128::ZERO; k];
    v_table
        .par_chunks_mut(1 << k_skip)
        .zip(q_tensor.par_iter())
        .for_each(|(chunk, &q)| {
            for (slot, zp) in chunk.iter_mut().zip(fresh.z_partial.iter()) {
                *slot = *zp * q;
            }
        });
    drop(q_tensor);
    // e_c(c) = eq(p_in^c, c).
    let e_c = build_eq_table(p_in_col);
    let tables_ms = tables_started.elapsed().as_millis();

    // G_v, G_e: row images of M̂ against v and e_c. Row index y = r + b·k.
    let row_images_started = std::time::Instant::now();
    let mut g_v = vec![F128::ZERO; 2 * k];
    let mut g_e = vec![F128::ZERO; 2 * k];
    rows.fill_row_images(&v_table, &e_c, &mut g_v, &mut g_e);
    let row_images_ms = row_images_started.elapsed().as_millis();

    // Phase-1 weights over y = (r, b): ŵu and γ·gate·eq(p_in^{rb}).
    let phase1_weights_started = std::time::Instant::now();
    let lambda = lagrange_weights_naive(k_skip, fresh.z_skip);
    let e_tensor = build_eq_table(&fresh.x_inner_rest);
    let w_u = build_stacked_u_weights(k_log, k_skip, fresh.alpha, &lambda, &e_tensor);
    let gg = gamma * gate_f;
    let w_in_row = build_eq_table_scaled(p_in_row, gg);
    drop(lambda);
    drop(e_tensor);
    let phase1_weights_ms = phase1_weights_started.elapsed().as_millis();

    let target1 = fresh.value + gg * incoming.value;
    let phase1_started = std::time::Instant::now();
    let (phase1_rounds, rho, claim1, finals1) = run_phase(target1, w_u, g_v, w_in_row, g_e, ch);
    let phase1_ms = phase1_started.elapsed().as_millis();
    // finals1 = [ŵu~(ρ), G_v~(ρ), γ·gate·eq~(ρ), G_e~(ρ)].
    let g_v_val = finals1[1];
    let g_e_val = finals1[3];
    debug_assert_eq!(
        finals1[0] * g_v_val + finals1[2] * g_e_val,
        claim1,
        "phase-1 terminal mismatch"
    );
    ch.observe_f128(g_v_val);
    ch.observe_f128(g_e_val);
    let delta = ch.sample_f128();

    // H(c) = Σ_y eq(ρ, y)·M̂[y, c].
    // `rho` has k_log+1 coordinates, so its dense equality table would hold
    // 2k field elements (128 MiB at m22). Matrix rows are canonical and
    // row-major; retain two sqrt-sized factors and evaluate one weight per
    // nonempty row instead.
    let column_image_started = std::time::Instant::now();
    let eq_rho = FactoredEqTable::new(&rho);
    let h = rows.weighted_column_image(&eq_rho);
    drop(eq_rho);
    let column_image_ms = column_image_started.elapsed().as_millis();

    // Phase 2 over c: target = G_v~ + δ·gate·G_e~, weight = v + δ·gate·e_c.
    let phase2_mix_started = std::time::Instant::now();
    let dg = delta * gate_f;
    let mut w2 = v_table;
    let first_phase2_coefficients = mix_and_round_coefficients_one_product(&mut w2, &e_c, &h, dg);
    drop(e_c);
    let phase2_mix_ms = phase2_mix_started.elapsed().as_millis();
    let target2 = g_v_val + dg * g_e_val;
    let phase2_started = std::time::Instant::now();
    let (phase2_rounds, sigma, claim2, finals2) =
        run_phase_one_product(target2, w2, h, Some(first_phase2_coefficients), ch);
    let phase2_ms = phase2_started.elapsed().as_millis();
    let final_matrix_eval = finals2[1];
    debug_assert_eq!(
        finals2[0] * final_matrix_eval,
        claim2,
        "phase-2 terminal mismatch"
    );
    ch.observe_f128(final_matrix_eval);

    if timing {
        eprintln!(
            "[matrix-fold] storage={storage} k_log={k_log} gate={gate} tables={tables_ms}ms row-images={row_images_ms}ms phase1-weights={phase1_weights_ms}ms phase1={phase1_ms}ms column-image={column_image_ms}ms phase2-mix={phase2_mix_ms}ms phase2-round0=fused phase2={phase2_ms}ms total={}ms",
            total_started.elapsed().as_millis()
        );
    }

    let mut point = rho;
    point.extend(sigma);
    (
        MatrixFoldProof {
            phase1_rounds,
            g_v: g_v_val,
            g_e: g_e_val,
            phase2_rounds,
            final_matrix_eval,
        },
        MatrixAccClaim {
            point,
            value: final_matrix_eval,
        },
    )
}

/// Prove one accumulator fold from a resident CSR relation. `gate` is 1 to
/// include the incoming claim (regular links) or 0 to ignore it (genesis).
pub fn prove_matrix_claim_fold<Ch: Challenger>(
    r1cs: &FieldR1cs,
    fresh: &FreshLincheckClaim,
    incoming: &MatrixAccClaim,
    gate: bool,
    ch: &mut Ch,
) -> (MatrixFoldProof, MatrixAccClaim) {
    prove_matrix_claim_fold_from_rows(MatrixFoldRows::Resident(r1cs), fresh, incoming, gate, ch)
}

/// Transcript-identical matrix fold directly over an authenticated compact
/// artifact. No CSR arrays are decoded or retained.
pub fn prove_matrix_claim_fold_compact<Ch: Challenger>(
    r1cs: &CompactFieldR1cs,
    fresh: &FreshLincheckClaim,
    incoming: &MatrixAccClaim,
    gate: bool,
    ch: &mut Ch,
) -> (MatrixFoldProof, MatrixAccClaim) {
    prove_matrix_claim_fold_from_rows(MatrixFoldRows::Compact(r1cs), fresh, incoming, gate, ch)
}

/// Verify one accumulator fold (matrix-free: only claim data and the
/// proof wires). Returns the outgoing accumulated claim.
pub fn verify_matrix_claim_fold<Ch: Challenger>(
    k_log: usize,
    k_skip: usize,
    fresh: &FreshLincheckClaim,
    incoming: &MatrixAccClaim,
    gate: F128,
    proof: &MatrixFoldProof,
    ch: &mut Ch,
) -> Result<MatrixAccClaim, MatrixFoldError> {
    if fresh.x_inner_rest.len() != k_log - k_skip
        || fresh.r_inner_rest.len() != k_log - k_skip
        || fresh.z_partial.len() != 1usize << k_skip
        || incoming.point.len() != 2 * k_log + 1
        || proof.phase1_rounds.len() != k_log + 1
        || proof.phase2_rounds.len() != k_log
    {
        return Err(MatrixFoldError::Shape);
    }

    absorb_fold_header(ch, fresh, incoming, gate);
    let gamma = ch.sample_f128();
    let gg = gamma * gate;
    let (p_in_row, p_in_col) = incoming.point.split_at(k_log + 1);

    let mut claim = fresh.value + gg * incoming.value;
    let mut rho = Vec::with_capacity(k_log + 1);
    for wire in &proof.phase1_rounds {
        ch.observe_f128_slice(wire);
        let c1 = claim + wire[1];
        let r = ch.sample_f128();
        claim = (wire[1] * r + c1) * r + wire[0];
        rho.push(r);
    }
    // Terminal: ŵu~(ρ)·G_v + γ·gate·eq(p_in^{rb}, ρ)·G_e == claim.
    let wu = u_weight_eval(fresh, k_skip, &rho);
    let ein = eq_points(p_in_row, &rho);
    if wu * proof.g_v + gg * ein * proof.g_e != claim {
        return Err(MatrixFoldError::FinalMismatch);
    }
    ch.observe_f128(proof.g_v);
    ch.observe_f128(proof.g_e);
    let delta = ch.sample_f128();
    let dg = delta * gate;

    let mut claim = proof.g_v + dg * proof.g_e;
    let mut sigma = Vec::with_capacity(k_log);
    for wire in &proof.phase2_rounds {
        ch.observe_f128_slice(wire);
        let c1 = claim + wire[1];
        let r = ch.sample_f128();
        claim = (wire[1] * r + c1) * r + wire[0];
        sigma.push(r);
    }
    // Terminal: [ṽ(σ) + δ·gate·eq(p_in^c, σ)]·M̂~(ρ‖σ) == claim.
    let v = v_weight_eval(fresh, k_skip, &sigma);
    let ec = eq_points(p_in_col, &sigma);
    if (v + dg * ec) * proof.final_matrix_eval != claim {
        return Err(MatrixFoldError::FinalMismatch);
    }
    ch.observe_f128(proof.final_matrix_eval);

    let mut point = rho;
    point.extend(sigma);
    Ok(MatrixAccClaim {
        point,
        value: proof.final_matrix_eval,
    })
}

/// Exact tensor-factored eq table.
///
/// A dense table over `d` variables retains `2^d` field elements. Splitting
/// the low/high coordinates retains only `2^floor(d/2) + 2^ceil(d/2)` and
/// reconstructs an entry with one multiplication. Indexing remains LSB-first,
/// exactly matching [`build_eq_table`].
struct FactoredEqTable {
    low: Vec<F128>,
    high: Vec<F128>,
    low_bits: usize,
    low_mask: usize,
}

impl FactoredEqTable {
    fn new(point: &[F128]) -> Self {
        let low_bits = point.len() / 2;
        let low = build_eq_table(&point[..low_bits]);
        let high = build_eq_table(&point[low_bits..]);
        Self {
            low,
            high,
            low_bits,
            low_mask: (1usize << low_bits) - 1,
        }
    }

    #[inline(always)]
    fn value(&self, index: usize) -> F128 {
        self.low[index & self.low_mask] * self.high[index >> self.low_bits]
    }
}

/// The decider's native check of an accumulated claim: evaluate the
/// stacked matrix MLE `M̂~(point)` directly from the sparse rows.
///
/// Both row and column equality tensors are factored, so the retained scratch
/// is `O(2^(k_log/2))`, not `O(2^k_log)`. At production `k_log = 24`, four
/// 4096-element factors replace two 16,777,216-element dense tables.
pub fn stacked_matrix_mle_eval(r1cs: &FieldR1cs, claim: &MatrixAccClaim) -> F128 {
    let k_log = r1cs.k_log;
    assert_eq!(claim.point.len(), 2 * k_log + 1);
    let (p_row, p_col) = claim.point.split_at(k_log + 1);
    let x_b = p_row[k_log];
    let eq_row = FactoredEqTable::new(&p_row[..k_log]);
    let eq_col = FactoredEqTable::new(p_col);
    let halves = [
        (&r1cs.a_0, F128::ONE + x_b), // b = 0 side
        (&r1cs.b_0, x_b),             // b = 1 side
    ];
    halves
        .par_iter()
        .map(|(m, w_b)| {
            (0..m.num_rows)
                .into_par_iter()
                .map(|r| {
                    let mut acc = F128::ZERO;
                    for (c, kappa) in m.row(r) {
                        acc += kappa * eq_col.value(c as usize);
                    }
                    acc * eq_row.value(r)
                })
                .reduce(|| F128::ZERO, |a, b| a + b)
                * *w_b
        })
        .reduce(|| F128::ZERO, |a, b| a + b)
}

/// The fresh-claim value a deferred lincheck final should carry, computed
/// directly from the matrices (prover/test side; the trace never runs
/// this).
pub fn fresh_claim_value(r1cs: &FieldR1cs, fresh: &FreshLincheckClaim) -> F128 {
    let k_skip = r1cs.k_skip;
    let lambda = lagrange_weights_naive(k_skip, fresh.z_skip);
    let e_tensor = FactoredEqTable::new(&fresh.x_inner_rest);
    let q_tensor = FactoredEqTable::new(&fresh.r_inner_rest);
    let mask = (1usize << k_skip) - 1;
    let halves = [(&r1cs.a_0, fresh.alpha), (&r1cs.b_0, F128::ONE)];
    halves
        .par_iter()
        .map(|(m, w)| {
            (0..m.num_rows)
                .into_par_iter()
                .map(|r| {
                    let u = lambda[r & mask] * e_tensor.value(r >> k_skip);
                    let mut acc = F128::ZERO;
                    for (c, kappa) in m.row(r) {
                        let c = c as usize;
                        acc += kappa * fresh.z_partial[c & mask] * q_tensor.value(c >> k_skip);
                    }
                    acc * u
                })
                .reduce(|| F128::ZERO, |a, b| a + b)
                * *w
        })
        .reduce(|| F128::ZERO, |a, b| a + b)
}

struct CompactFreshClaimWeights<'a> {
    claim: &'a FreshLincheckClaim,
    lambda: Vec<F128>,
    row_tensor: FactoredEqTable,
    column_tensor: FactoredEqTable,
    k_skip: usize,
    mask: usize,
}

impl<'a> CompactFreshClaimWeights<'a> {
    fn new(claim: &'a FreshLincheckClaim, k_skip: usize) -> Self {
        Self {
            claim,
            lambda: lagrange_weights_naive(k_skip, claim.z_skip),
            row_tensor: FactoredEqTable::new(&claim.x_inner_rest),
            column_tensor: FactoredEqTable::new(&claim.r_inner_rest),
            k_skip,
            mask: (1usize << k_skip) - 1,
        }
    }

    #[inline(always)]
    fn row_weight(&self, row: usize) -> F128 {
        self.lambda[row & self.mask] * self.row_tensor.value(row >> self.k_skip)
    }

    #[inline(always)]
    fn column_weight(&self, column: usize) -> F128 {
        self.claim.z_partial[column & self.mask] * self.column_tensor.value(column >> self.k_skip)
    }
}

struct CompactAccumulatedClaimWeights {
    x_b: F128,
    row_tensor: FactoredEqTable,
    column_tensor: FactoredEqTable,
}

impl CompactAccumulatedClaimWeights {
    fn new(claim: &MatrixAccClaim, k_log: usize) -> Self {
        assert_eq!(claim.point.len(), 2 * k_log + 1);
        let (p_row, p_col) = claim.point.split_at(k_log + 1);
        Self {
            x_b: p_row[k_log],
            row_tensor: FactoredEqTable::new(&p_row[..k_log]),
            column_tensor: FactoredEqTable::new(p_col),
        }
    }
}

#[derive(Clone, Copy)]
struct CompactMatrixClaimTotals {
    fresh: F128,
    accumulated: F128,
    #[cfg(test)]
    group_scans: usize,
}

impl CompactMatrixClaimTotals {
    const fn zero() -> Self {
        Self {
            fresh: F128::ZERO,
            accumulated: F128::ZERO,
            #[cfg(test)]
            group_scans: 0,
        }
    }

    #[inline]
    fn combine(self, other: Self) -> Self {
        Self {
            fresh: self.fresh + other.fresh,
            accumulated: self.accumulated + other.accumulated,
            #[cfg(test)]
            group_scans: self.group_scans + other.group_scans,
        }
    }
}

struct CompactMatrixClaimValues {
    fresh: Option<F128>,
    accumulated: Option<F128>,
    #[cfg(test)]
    group_scans: usize,
}

/// Evaluate the bounded fresh/accumulated pair over authenticated compact
/// planar rows.  When both claims are present, every A/B group is decoded
/// exactly once and each visited coefficient contributes to both independent
/// sums.  Canonical row-major order also lets the two factored row weights be
/// cached until the row changes; column tensors remain factored and bounded.
fn compact_matrix_claim_values(
    r1cs: &CompactFieldR1cs,
    fresh: Option<&FreshLincheckClaim>,
    accumulated: Option<&MatrixAccClaim>,
) -> CompactMatrixClaimValues {
    let shape = r1cs.shape();
    let fresh_weights = fresh.map(|claim| CompactFreshClaimWeights::new(claim, shape.k_skip));
    let accumulated_weights =
        accumulated.map(|claim| CompactAccumulatedClaimWeights::new(claim, shape.k_log));

    if fresh_weights.is_none() && accumulated_weights.is_none() {
        return CompactMatrixClaimValues {
            fresh: None,
            accumulated: None,
            #[cfg(test)]
            group_scans: 0,
        };
    }

    let totals = [FieldR1csArtifactMatrix::A, FieldR1csArtifactMatrix::B]
        .par_iter()
        .map(|&side| {
            let mut side_totals = (0..r1cs.matrix_group_count(side))
                .into_par_iter()
                .map(|group| {
                    let mut totals = CompactMatrixClaimTotals::zero();
                    #[cfg(test)]
                    {
                        totals.group_scans = 1;
                    }
                    let mut cached_row = usize::MAX;
                    let mut fresh_row_weight = F128::ZERO;
                    let mut accumulated_row_weight = F128::ZERO;
                    let visited = r1cs.for_each_matrix_group_entry(
                        side,
                        group,
                        |row, column, coefficient| {
                            if row != cached_row {
                                cached_row = row;
                                if let Some(weights) = &fresh_weights {
                                    fresh_row_weight = weights.row_weight(row);
                                }
                                if let Some(weights) = &accumulated_weights {
                                    accumulated_row_weight = weights.row_tensor.value(row);
                                }
                            }

                            let column = column as usize;
                            if let Some(weights) = &fresh_weights {
                                totals.fresh +=
                                    coefficient * weights.column_weight(column) * fresh_row_weight;
                            }
                            if let Some(weights) = &accumulated_weights {
                                totals.accumulated += coefficient
                                    * weights.column_tensor.value(column)
                                    * accumulated_row_weight;
                            }
                        },
                    );
                    assert!(visited, "enumerated compact matrix group exists");
                    totals
                })
                .reduce(CompactMatrixClaimTotals::zero, |a, b| a.combine(b));

            if let Some(weights) = &fresh_weights {
                side_totals.fresh *= match side {
                    FieldR1csArtifactMatrix::A => weights.claim.alpha,
                    FieldR1csArtifactMatrix::B => F128::ONE,
                };
            }
            if let Some(weights) = &accumulated_weights {
                side_totals.accumulated *= match side {
                    FieldR1csArtifactMatrix::A => F128::ONE + weights.x_b,
                    FieldR1csArtifactMatrix::B => weights.x_b,
                };
            }
            side_totals
        })
        .reduce(CompactMatrixClaimTotals::zero, |a, b| a.combine(b));

    CompactMatrixClaimValues {
        fresh: fresh.map(|_| totals.fresh),
        accumulated: accumulated.map(|_| totals.accumulated),
        #[cfg(test)]
        group_scans: totals.group_scans,
    }
}

impl CompactFieldR1cs {
    /// Evaluate the terminal's bounded fresh/accumulated claim set against the
    /// exact immutable rows authenticated by [`CompactFieldR1cs::open`].
    ///
    /// Unlike the compatibility [`MatrixClaimEvaluator`] trait this operation
    /// needs only `&self`, so an `Arc<CompactFieldR1cs>` can serve concurrent
    /// terminal and proving lanes without cloning the artifact or introducing
    /// a mutex solely for trait mutability.
    pub fn evaluate_matrix_claims_authenticated(
        &self,
        fresh: Option<&FreshLincheckClaim>,
        accumulated: Option<&MatrixAccClaim>,
    ) -> Result<AuthenticatedMatrixClaimEvaluations, FieldR1csArtifactError> {
        let shape = self.shape();
        if let Some(claim) = fresh {
            let rest = shape.k_log - shape.k_skip;
            if claim.x_inner_rest.len() != rest || claim.r_inner_rest.len() != rest {
                return Err(FieldR1csArtifactError::MatrixClaimShape(
                    "fresh inner-rest width",
                ));
            }
            if claim.z_partial.len() != 1usize << shape.k_skip {
                return Err(FieldR1csArtifactError::MatrixClaimShape(
                    "fresh partial window",
                ));
            }
        }
        if accumulated.is_some_and(|claim| claim.point.len() != 2 * shape.k_log + 1) {
            return Err(FieldR1csArtifactError::MatrixClaimShape(
                "accumulated point width",
            ));
        }
        let values = compact_matrix_claim_values(self, fresh, accumulated);
        Ok(AuthenticatedMatrixClaimEvaluations::new(
            self.statement_digest(),
            fresh,
            accumulated,
            values.fresh,
            values.accumulated,
        ))
    }
}

impl MatrixClaimEvaluator for CompactFieldR1cs {
    fn field_shape(&self) -> FieldShape {
        self.shape()
    }

    fn evaluate_matrix_claims(
        &mut self,
        fresh: Option<&FreshLincheckClaim>,
        accumulated: Option<&MatrixAccClaim>,
    ) -> Result<AuthenticatedMatrixClaimEvaluations, FieldR1csArtifactError> {
        self.evaluate_matrix_claims_authenticated(fresh, accumulated)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::FsLaneChallenger;
    use crate::field_r1cs::{CompactFieldR1cs, SparseFieldMatrix};

    struct Rng(u64);
    impl Rng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            z ^ (z >> 31)
        }
        fn f128(&mut self) -> F128 {
            F128 {
                lo: self.next_u64(),
                hi: self.next_u64(),
            }
        }
    }

    #[test]
    fn direct_round_coefficients_match_three_evaluation_reference_in_serial_and_parallel() {
        let mut rng = Rng(0xC02F_F1C1_E17);
        let cases = [2usize, 32, 4096]
            .into_iter()
            .map(|length| {
                let random_table =
                    |rng: &mut Rng| (0..length).map(|_| rng.f128()).collect::<Vec<_>>();
                (
                    random_table(&mut rng),
                    random_table(&mut rng),
                    random_table(&mut rng),
                    random_table(&mut rng),
                )
            })
            .collect::<Vec<_>>();

        for threads in [1, 4] {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .expect("round-coefficient test pool");
            pool.install(|| {
                for (w1, g1, w2, g2) in &cases {
                    assert_eq!(
                        round_coefficients_two_products(w1, g1, w2, g2),
                        round_coefficients_two_products_reference(w1, g1, w2, g2),
                        "two-product coefficients with {threads} Rayon threads",
                    );

                    let zero = vec![F128::ZERO; w1.len()];
                    assert_eq!(
                        round_coefficients_one_product(w1, g1),
                        round_coefficients_two_products_reference(w1, g1, &zero, &zero),
                        "one-product coefficients with {threads} Rayon threads",
                    );
                }
            });
        }
    }

    #[test]
    fn rotating_fold_buffers_preserve_full_phase_transcript() {
        let mut rng = Rng(0xB0FF_EA11_0CA7_E);
        let cases = [128usize, 4096]
            .into_iter()
            .map(|length| {
                let random_table =
                    |rng: &mut Rng| (0..length).map(|_| rng.f128()).collect::<Vec<_>>();
                (
                    random_table(&mut rng),
                    random_table(&mut rng),
                    random_table(&mut rng),
                    random_table(&mut rng),
                )
            })
            .collect::<Vec<_>>();

        for threads in [1, 4] {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .expect("phase transcript test pool");
            pool.install(|| {
                for (w1, g1, w2, g2) in &cases {
                    let initial = round_evals_two_products_reference(w1, g1, w2, g2);
                    let claim = initial[0] + initial[1];

                    let mut reference_ch = FsLaneChallenger::new(b"fold-buffer-parity");
                    let reference = run_phase_reference(
                        claim,
                        w1.clone(),
                        g1.clone(),
                        w2.clone(),
                        g2.clone(),
                        &mut reference_ch,
                    );
                    let mut optimized_ch = FsLaneChallenger::new(b"fold-buffer-parity");
                    let optimized = run_phase(
                        claim,
                        w1.clone(),
                        g1.clone(),
                        w2.clone(),
                        g2.clone(),
                        &mut optimized_ch,
                    );
                    assert_eq!(
                        optimized, reference,
                        "two-product phase with {threads} Rayon threads"
                    );
                    assert_eq!(
                        optimized_ch.sample_f128(),
                        reference_ch.sample_f128(),
                        "two-product challenger tail with {threads} Rayon threads"
                    );

                    // Phase 2 is the same frozen two-product protocol with an
                    // all-zero second term. Compare the specialized one-term
                    // kernel against that exact legacy schedule as well.
                    let zero = vec![F128::ZERO; w1.len()];
                    let initial_one = round_evals_two_products_reference(w1, g1, &zero, &zero);
                    let claim_one = initial_one[0] + initial_one[1];
                    let mut reference_ch = FsLaneChallenger::new(b"fold-buffer-one-parity");
                    let reference = run_phase_reference(
                        claim_one,
                        w1.clone(),
                        g1.clone(),
                        zero.clone(),
                        zero,
                        &mut reference_ch,
                    );
                    let mut optimized_ch = FsLaneChallenger::new(b"fold-buffer-one-parity");
                    let optimized = run_phase_one_product(
                        claim_one,
                        w1.clone(),
                        g1.clone(),
                        None,
                        &mut optimized_ch,
                    );
                    assert_eq!(optimized.0, reference.0, "one-product round wires");
                    assert_eq!(optimized.1, reference.1, "one-product challenges");
                    assert_eq!(optimized.2, reference.2, "one-product final claim");
                    assert_eq!(
                        optimized.3,
                        [reference.3[0], reference.3[1]],
                        "one-product terminal values"
                    );
                    assert_eq!(
                        optimized_ch.sample_f128(),
                        reference_ch.sample_f128(),
                        "one-product challenger tail with {threads} Rayon threads"
                    );

                    let scale = F128 {
                        lo: 0xD31A_5E00_1234_5678,
                        hi: 0xA11C_EF01_89AB_CDEF,
                    };
                    let mut expected_mixed = w1.clone();
                    expected_mixed
                        .iter_mut()
                        .zip(w2.iter())
                        .for_each(|(w, e)| *w += scale * *e);
                    let zero = vec![F128::ZERO; w1.len()];
                    let initial =
                        round_evals_two_products_reference(&expected_mixed, g1, &zero, &zero);
                    let claim = initial[0] + initial[1];
                    let mut reference_ch = FsLaneChallenger::new(b"fold-mix-parity");
                    let reference = run_phase_reference(
                        claim,
                        expected_mixed.clone(),
                        g1.clone(),
                        zero.clone(),
                        zero,
                        &mut reference_ch,
                    );

                    let mut fused_mixed = w1.clone();
                    let first_coefficients =
                        mix_and_round_coefficients_one_product(&mut fused_mixed, w2, g1, scale);
                    assert_eq!(fused_mixed, expected_mixed, "fused phase-2 mix");
                    assert_eq!(
                        first_coefficients,
                        round_coefficients_one_product(&expected_mixed, g1),
                        "fused phase-2 round-zero coefficients"
                    );
                    let mut optimized_ch = FsLaneChallenger::new(b"fold-mix-parity");
                    let optimized = run_phase_one_product(
                        claim,
                        fused_mixed,
                        g1.clone(),
                        Some(first_coefficients),
                        &mut optimized_ch,
                    );
                    assert_eq!(optimized.0, reference.0, "fused phase-2 round wires");
                    assert_eq!(optimized.1, reference.1, "fused phase-2 challenges");
                    assert_eq!(optimized.2, reference.2, "fused phase-2 final claim");
                    assert_eq!(optimized.3, [reference.3[0], reference.3[1]]);
                    assert_eq!(
                        optimized_ch.sample_f128(),
                        reference_ch.sample_f128(),
                        "fused phase-2 challenger tail with {threads} Rayon threads"
                    );
                }
            });
        }
    }

    #[test]
    fn scaled_eq_table_is_byte_identical_to_the_previous_scale_pass() {
        let mut rng = Rng(0x5CA1_ED_E9);
        for dimensions in 0..=10 {
            let point = (0..dimensions).map(|_| rng.f128()).collect::<Vec<_>>();
            for scale in [F128::ZERO, F128::ONE, rng.f128()] {
                let mut expected = build_eq_table(&point);
                expected
                    .iter_mut()
                    .for_each(|value| *value = *value * scale);
                assert_eq!(build_eq_table_scaled(&point, scale), expected);
            }
        }
    }

    #[test]
    fn shared_stacked_u_base_matches_the_previous_per_half_formula() {
        let mut rng = Rng(0x57AC_CED0);
        let (k_log, k_skip) = (10usize, 3usize);
        let k = 1usize << k_log;
        let ell = 1usize << k_skip;
        let alpha = rng.f128();
        let lambda = (0..ell).map(|_| rng.f128()).collect::<Vec<_>>();
        let e_tensor = (0..k >> k_skip).map(|_| rng.f128()).collect::<Vec<_>>();
        let expected = (0..2 * k)
            .map(|index| {
                let row = index & (k - 1);
                let side_weight = if index < k { alpha } else { F128::ONE };
                lambda[row & (ell - 1)] * e_tensor[row >> k_skip] * side_weight
            })
            .collect::<Vec<_>>();

        for threads in [1, 4] {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .expect("stacked-weight test pool");
            let actual =
                pool.install(|| build_stacked_u_weights(k_log, k_skip, alpha, &lambda, &e_tensor));
            assert_eq!(actual, expected, "{threads} Rayon threads");
        }
    }

    fn random_instance(rng: &mut Rng, k_log: usize, nnz_per_row: usize) -> FieldR1cs {
        let k = 1usize << k_log;
        let mk = |rng: &mut Rng| {
            SparseFieldMatrix::from_rows(
                k,
                (0..k)
                    .map(|_| {
                        (0..nnz_per_row)
                            .map(|_| ((rng.next_u64() as usize % k) as u32, rng.f128()))
                            .collect()
                    })
                    .collect(),
            )
        };
        FieldR1cs {
            m: k_log,
            k_log,
            k_skip: 6,
            useful_rows: k,
            a_0: mk(rng),
            b_0: mk(rng),
            const_pin: Some(0),
            digest_cache: std::sync::OnceLock::new(),
            csc_cache: std::sync::OnceLock::new(),
        }
    }

    fn random_fresh(rng: &mut Rng, r1cs: &FieldR1cs) -> FreshLincheckClaim {
        let rest = r1cs.k_log - r1cs.k_skip;
        let mut fresh = FreshLincheckClaim {
            alpha: rng.f128(),
            z_skip: rng.f128(),
            x_inner_rest: (0..rest).map(|_| rng.f128()).collect(),
            r_inner_rest: (0..rest).map(|_| rng.f128()).collect(),
            z_partial: (0..1 << r1cs.k_skip).map(|_| rng.f128()).collect(),
            value: F128::ZERO,
        };
        fresh.value = fresh_claim_value(r1cs, &fresh);
        fresh
    }

    fn random_true_acc(rng: &mut Rng, r1cs: &FieldR1cs) -> MatrixAccClaim {
        let mut acc = MatrixAccClaim {
            point: (0..2 * r1cs.k_log + 1).map(|_| rng.f128()).collect(),
            value: F128::ZERO,
        };
        acc.value = stacked_matrix_mle_eval(r1cs, &acc);
        acc
    }

    fn stacked_matrix_mle_eval_dense_reference(r1cs: &FieldR1cs, claim: &MatrixAccClaim) -> F128 {
        let k_log = r1cs.k_log;
        let (p_row, p_col) = claim.point.split_at(k_log + 1);
        let x_b = p_row[k_log];
        let eq_row = build_eq_table(&p_row[..k_log]);
        let eq_col = build_eq_table(p_col);
        let mut total = F128::ZERO;
        for (matrix, weight) in [(&r1cs.a_0, F128::ONE + x_b), (&r1cs.b_0, x_b)] {
            let mut half = F128::ZERO;
            for r in 0..matrix.num_rows {
                let mut row = F128::ZERO;
                for (c, kappa) in matrix.row(r) {
                    row += kappa * eq_col[c as usize];
                }
                half += row * eq_row[r];
            }
            total += half * weight;
        }
        total
    }

    fn fresh_claim_value_dense_reference(r1cs: &FieldR1cs, fresh: &FreshLincheckClaim) -> F128 {
        let lambda = lagrange_weights_naive(r1cs.k_skip, fresh.z_skip);
        let e_tensor = build_eq_table(&fresh.x_inner_rest);
        let q_tensor = build_eq_table(&fresh.r_inner_rest);
        let mask = (1usize << r1cs.k_skip) - 1;
        let mut total = F128::ZERO;
        for (matrix, weight) in [(&r1cs.a_0, fresh.alpha), (&r1cs.b_0, F128::ONE)] {
            let mut half = F128::ZERO;
            for r in 0..matrix.num_rows {
                let u = lambda[r & mask] * e_tensor[r >> r1cs.k_skip];
                let mut row = F128::ZERO;
                for (c, kappa) in matrix.row(r) {
                    let c = c as usize;
                    row += kappa * fresh.z_partial[c & mask] * q_tensor[c >> r1cs.k_skip];
                }
                half += row * u;
            }
            total += half * weight;
        }
        total
    }

    #[test]
    fn factored_eq_lookup_and_matrix_evaluators_match_dense_reference() {
        let mut rng = Rng(0xFAC7_0E0D);
        for dimensions in 0..=12 {
            let point = (0..dimensions).map(|_| rng.f128()).collect::<Vec<_>>();
            let dense = build_eq_table(&point);
            let factored = FactoredEqTable::new(&point);
            for (index, expected) in dense.into_iter().enumerate() {
                assert_eq!(factored.value(index), expected);
            }
        }

        for k_log in 6..=10 {
            let r1cs = random_instance(&mut rng, k_log, 3);
            let claim = MatrixAccClaim {
                point: (0..2 * k_log + 1).map(|_| rng.f128()).collect(),
                value: F128::ZERO,
            };
            assert_eq!(
                stacked_matrix_mle_eval(&r1cs, &claim),
                stacked_matrix_mle_eval_dense_reference(&r1cs, &claim),
                "factored accumulated claim at k_log={k_log}"
            );

            let fresh = random_fresh(&mut rng, &r1cs);
            assert_eq!(
                fresh_claim_value(&r1cs, &fresh),
                fresh_claim_value_dense_reference(&r1cs, &fresh),
                "factored fresh claim at k_log={k_log}"
            );
        }
    }

    #[test]
    fn authenticated_evaluation_cannot_be_replayed_for_another_claim() {
        let mut rng = Rng(0xB1AD_1A6);
        let mut r1cs = random_instance(&mut rng, 7, 2);
        let first = random_true_acc(&mut rng, &r1cs);
        let evaluated = r1cs
            .evaluate_matrix_claims(None, Some(&first))
            .expect("first claim evaluates");
        assert!(evaluated.is_bound_to(None, Some(&first)));

        let mut second = first.clone();
        second.point[0] += F128::ONE;
        second.value = stacked_matrix_mle_eval(&r1cs, &second);
        assert!(!evaluated.is_bound_to(None, Some(&second)));

        let second_evaluation = r1cs
            .evaluate_matrix_claims(None, Some(&second))
            .expect("second claim evaluates");
        assert!(second_evaluation.is_bound_to(None, Some(&second)));
        assert!(!second_evaluation.is_bound_to(None, Some(&first)));
    }

    #[test]
    fn compact_artifact_all_optional_evaluations_match_csr_in_one_scan() {
        let mut rng = Rng(0xC04A_C7E0);
        let mut resident = random_instance(&mut rng, 9, 4);
        let shape = FieldShape::of(&resident);
        let digest = resident.structural_statement_digest();
        let mut artifact = Vec::new();
        resident
            .write_artifact(&mut artifact)
            .expect("resident fixture has a canonical artifact");
        let compact = CompactFieldR1cs::open(artifact.clone().into_boxed_slice(), shape, digest)
            .expect("canonical artifact authenticates as compact");
        let packed = CompactFieldR1cs::open_packed(artifact.into_boxed_slice(), shape, digest)
            .expect("canonical artifact authenticates as startup-packed");

        let fresh = random_fresh(&mut rng, &resident);
        let accumulated = random_true_acc(&mut rng, &resident);
        let expected_group_scans = compact.matrix_group_count(FieldR1csArtifactMatrix::A)
            + compact.matrix_group_count(FieldR1csArtifactMatrix::B);

        for request_fresh in [false, true] {
            for request_accumulated in [false, true] {
                let fresh = request_fresh.then_some(&fresh);
                let accumulated = request_accumulated.then_some(&accumulated);
                let expected = resident
                    .evaluate_matrix_claims(fresh, accumulated)
                    .expect("resident claims evaluate");
                let actual = compact
                    .evaluate_matrix_claims_authenticated(fresh, accumulated)
                    .expect("compact claims evaluate");
                assert_eq!(actual, expected);
                assert!(actual.is_bound_to(fresh, accumulated));
                let packed_actual = packed
                    .evaluate_matrix_claims_authenticated(fresh, accumulated)
                    .expect("packed claims evaluate");
                assert_eq!(packed_actual, expected);
                assert!(packed_actual.is_bound_to(fresh, accumulated));

                let values = compact_matrix_claim_values(&compact, fresh, accumulated);
                assert_eq!(values.fresh, expected.fresh_value());
                assert_eq!(values.accumulated, expected.accumulated_value());
                assert_eq!(
                    values.group_scans,
                    if request_fresh || request_accumulated {
                        expected_group_scans
                    } else {
                        0
                    },
                    "fresh={request_fresh}, accumulated={request_accumulated}",
                );
            }
        }
    }

    #[test]
    fn compact_matrix_fold_is_transcript_identical_to_csr() {
        let mut rng = Rng(0xC04A_F01D);
        let resident = random_instance(&mut rng, 9, 4);
        let shape = FieldShape::of(&resident);
        let digest = resident.structural_statement_digest();
        let mut artifact = Vec::new();
        resident
            .write_artifact(&mut artifact)
            .expect("resident fixture has a canonical artifact");
        let compact = CompactFieldR1cs::open(artifact.clone().into_boxed_slice(), shape, digest)
            .expect("canonical artifact authenticates as compact");
        let packed = CompactFieldR1cs::open_packed(artifact.into_boxed_slice(), shape, digest)
            .expect("canonical artifact authenticates as startup-packed");
        let fresh = random_fresh(&mut rng, &resident);
        let incoming = random_true_acc(&mut rng, &resident);

        for gate in [false, true] {
            let mut resident_challenger = FsLaneChallenger::new(b"compact-fold-parity");
            let resident_fold = prove_matrix_claim_fold(
                &resident,
                &fresh,
                &incoming,
                gate,
                &mut resident_challenger,
            );
            let mut compact_challenger = FsLaneChallenger::new(b"compact-fold-parity");
            let compact_fold = prove_matrix_claim_fold_compact(
                &compact,
                &fresh,
                &incoming,
                gate,
                &mut compact_challenger,
            );
            assert_eq!(compact_fold, resident_fold, "gate={gate}");
            let mut packed_challenger = FsLaneChallenger::new(b"compact-fold-parity");
            let packed_fold = prove_matrix_claim_fold_compact(
                &packed,
                &fresh,
                &incoming,
                gate,
                &mut packed_challenger,
            );
            assert_eq!(packed_fold, resident_fold, "packed gate={gate}");
            assert_eq!(
                packed_challenger.sample_f128(),
                compact_challenger.sample_f128(),
                "packed challenger tail gate={gate}",
            );
        }
    }

    /// Honest fold roundtrip: chained accumulators stay TRUE against the
    /// matrix (decider check), with and without the genesis gate.
    #[test]
    fn fold_roundtrip_chained() {
        let mut rng = Rng(0xACC0);
        let r1cs = random_instance(&mut rng, 8, 3);

        // Genesis: gate = 0, incoming ignored (junk lanes).
        let fresh0 = random_fresh(&mut rng, &r1cs);
        let junk = MatrixAccClaim {
            point: (0..17).map(|_| rng.f128()).collect(),
            value: rng.f128(),
        };
        let mut ch_p = FsLaneChallenger::new(b"fold-test");
        let (proof0, acc0) = prove_matrix_claim_fold(&r1cs, &fresh0, &junk, false, &mut ch_p);
        let mut ch_v = FsLaneChallenger::new(b"fold-test");
        let acc0_v = verify_matrix_claim_fold(8, 6, &fresh0, &junk, F128::ZERO, &proof0, &mut ch_v)
            .expect("genesis fold verifies");
        assert_eq!(acc0, acc0_v);
        assert_eq!(
            stacked_matrix_mle_eval(&r1cs, &acc0),
            acc0.value,
            "genesis accumulator claim is true"
        );

        // Link 1: fold a fresh claim with acc0.
        let fresh1 = random_fresh(&mut rng, &r1cs);
        let (proof1, acc1) = prove_matrix_claim_fold(&r1cs, &fresh1, &acc0, true, &mut ch_p);
        let acc1_v = verify_matrix_claim_fold(8, 6, &fresh1, &acc0, F128::ONE, &proof1, &mut ch_v)
            .expect("link fold verifies");
        assert_eq!(acc1, acc1_v);
        assert_eq!(
            stacked_matrix_mle_eval(&r1cs, &acc1),
            acc1.value,
            "chained accumulator claim is true"
        );
        assert_eq!(ch_p.sample_f128(), ch_v.sample_f128(), "lockstep");
    }

    /// A false fresh claim or a false incoming claim cannot yield a
    /// verifier-accepted TRUE accumulator: the compressed rounds thread
    /// the (false) target through the verifier's `c_1` reconstruction, so
    /// the run is rejected — or, if some mutation slips it through, the
    /// accumulated claim is false against the matrix and the decider's
    /// evaluation catches it. A gated-off (genesis) incoming claim is
    /// excused by construction.
    #[test]
    fn false_claims_rejected_or_poison_the_accumulator() {
        let mut rng = Rng(0xACC1);
        let r1cs = random_instance(&mut rng, 8, 3);

        let caught = |r1cs: &FieldR1cs,
                      fresh: &FreshLincheckClaim,
                      acc_in: &MatrixAccClaim,
                      gate: bool,
                      proof: &MatrixFoldProof| {
            let mut ch = FsLaneChallenger::new(b"fold-false-v");
            let gate_f = if gate { F128::ONE } else { F128::ZERO };
            match verify_matrix_claim_fold(8, 6, fresh, acc_in, gate_f, proof, &mut ch) {
                Err(_) => true,
                Ok(acc) => stacked_matrix_mle_eval(r1cs, &acc) != acc.value,
            }
        };

        // False fresh value.
        let mut fresh = random_fresh(&mut rng, &r1cs);
        fresh.value += F128::ONE;
        let acc_in = random_true_acc(&mut rng, &r1cs);
        let mut ch = FsLaneChallenger::new(b"fold-false-v");
        if let Some((proof, _)) = crate::catch_expected_prover_rejection(|| {
            prove_matrix_claim_fold(&r1cs, &fresh, &acc_in, true, &mut ch)
        }) {
            assert!(
                caught(&r1cs, &fresh, &acc_in, true, &proof),
                "false fresh claim accepted with a true accumulator"
            );
        }

        // False incoming value under an honest fresh claim.
        let fresh = random_fresh(&mut rng, &r1cs);
        let mut acc_bad = random_true_acc(&mut rng, &r1cs);
        acc_bad.value += F128::ONE;
        let mut ch = FsLaneChallenger::new(b"fold-false-v");
        if let Some((proof, _)) = crate::catch_expected_prover_rejection(|| {
            prove_matrix_claim_fold(&r1cs, &fresh, &acc_bad, true, &mut ch)
        }) {
            assert!(
                caught(&r1cs, &fresh, &acc_bad, true, &proof),
                "false incoming claim accepted with a true accumulator"
            );
        }

        // The same false incoming with gate = 0 is EXCUSED (genesis): the
        // verifier accepts and the accumulator is TRUE.
        let mut ch_p = FsLaneChallenger::new(b"fold-false-g");
        let (proof, acc) = prove_matrix_claim_fold(&r1cs, &fresh, &acc_bad, false, &mut ch_p);
        let mut ch_v = FsLaneChallenger::new(b"fold-false-g");
        let acc_v = verify_matrix_claim_fold(8, 6, &fresh, &acc_bad, F128::ZERO, &proof, &mut ch_v)
            .expect("gated-off incoming verifies");
        assert_eq!(acc, acc_v);
        assert_eq!(
            stacked_matrix_mle_eval(&r1cs, &acc),
            acc.value,
            "gated-off incoming must not affect the accumulator"
        );
    }

    /// Proof-wire mutations: every mutated wire is rejected outright or
    /// lands on a false accumulator.
    #[test]
    fn fold_wire_mutations() {
        let mut rng = Rng(0xACC2);
        let r1cs = random_instance(&mut rng, 7, 3);
        let fresh = random_fresh(&mut rng, &r1cs);
        let acc_in = random_true_acc(&mut rng, &r1cs);
        let mut ch = FsLaneChallenger::new(b"fold-mut");
        let (proof, _) = prove_matrix_claim_fold(&r1cs, &fresh, &acc_in, true, &mut ch);

        let check = |bad: &MatrixFoldProof| {
            let mut ch = FsLaneChallenger::new(b"fold-mut");
            match verify_matrix_claim_fold(7, 6, &fresh, &acc_in, F128::ONE, bad, &mut ch) {
                Err(_) => true,
                Ok(acc) => stacked_matrix_mle_eval(&r1cs, &acc) != acc.value,
            }
        };

        for i in 0..proof.phase1_rounds.len() {
            for j in 0..2 {
                let mut bad = proof.clone();
                bad.phase1_rounds[i][j] += F128::ONE;
                assert!(check(&bad), "phase1 round {i}/{j} survived");
            }
        }
        for i in 0..proof.phase2_rounds.len() {
            for j in 0..2 {
                let mut bad = proof.clone();
                bad.phase2_rounds[i][j] += F128::ONE;
                assert!(check(&bad), "phase2 round {i}/{j} survived");
            }
        }
        for field in 0..3 {
            let mut bad = proof.clone();
            match field {
                0 => bad.g_v += F128::ONE,
                1 => bad.g_e += F128::ONE,
                _ => bad.final_matrix_eval += F128::ONE,
            }
            assert!(check(&bad), "terminal wire {field} survived");
        }
    }
}
