//! Column relations for the deep-chain layer walk: the sumchecks that tie
//! the walk's endpoint columns to committed data.
//!
//! The walk (`super`) binds layers 1..=66 to each other but says nothing
//! about WHERE its layer-0 inputs come from or where its layer-66 outputs
//! go. Three relation shapes close the loop, all instances of ONE generic
//! sumcheck over products of column MLEs:
//!
//! - SELECTION (before the walk): `0 = Σ_w eq(ρ,x)·[O(w) + mask(w)·S_out(w)]`
//!   — exposed outputs and carry columns are lane selections of the output
//!   columns. Terminal claims: committed columns (discharged through the
//!   batched PCS opening via public-IO) and output-column claims that seed
//!   the walk as a start group.
//! - SUBSTITUTION (after the walk): the walk's terminal claim
//!   `Σ_e α_e·S_in,e~(σ)` is re-expressed through the chain wiring —
//!   `S_in = MDS_FULL·raw` with `raw` a selector-gated combination of
//!   shifted carry columns and absorb columns. Terminal claims: committed
//!   columns and SHIFTED committed columns.
//! - BOOLEANITY: `0 = Σ_w eq(ρ,w)·(b(w)² + b(w))` for witness selector
//!   columns.
//!
//! A SHIFTED-column claim `Σ_w eq(σ,w)·col(w−1) = v` is not a plain MLE
//! evaluation; [`prove_shift_discharge`] reduces it to one with a degree-2
//! sumcheck against the successor kernel `N(σ,w) = eq(σ, w+1)`, whose
//! closed form ([`shift_kernel_eval`]) both verifiers evaluate in O(n).
//!
//! Besides witness columns, terms may reference FIXED columns
//! ([`ColRef::Fixed`] / [`FixedPattern`]): protocol-constant selector or
//! constant-value columns that are periodic in the low `low_log` index
//! bits. Their MLE factorizes — `pat~(ρ) = table~(ρ[..low_log])` — so the
//! verifier evaluates them itself in O(2^low_log) and they never appear in
//! `final_values`. This is what keeps chain-schedule wiring (start/absorb/
//! pad selectors, IV and domain-tag constants) out of the committed
//! witness and independent of how many schedule copies tile the slot
//! domain.
//!
//! Round polynomials use the compressed wire form (`[c_0, c_2..c_d]`, the
//! linear coefficient reconstructed from the running claim).

use crate::challenger::Challenger;
use crate::field::F128;
use crate::lincheck::build_eq_table;
use rayon::prelude::*;

pub mod c1;

/// Maximum column factors per term (degree 4 with the eq prefix). Three
/// factors admit selector-gated products like `EVEN·D·SIB` without minting
/// combined selector columns — committed columns cost 2^w_log witness
/// cells each at attack scale, an extra round coefficient costs one wire.
pub const MAX_TERM_FACTORS: usize = 3;

/// Relation sumcheck degree: eq · (≤ [`MAX_TERM_FACTORS`] column factors).
pub const RELATION_DEGREE: usize = 1 + MAX_TERM_FACTORS;

/// A reference to one column of the relation instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ColRef {
    /// A committed column (region/carry/selector) — its terminal claim
    /// discharges through the batched PCS opening.
    Committed(usize),
    /// A committed column read at the PREDECESSOR slot (`col(w−1)`, zero at
    /// slot 0) — its terminal claim needs [`prove_shift_discharge`].
    CommittedShift(usize),
    /// A committed column read TWO slots back (`col(w−2)`, zero at slots
    /// 0/1) — the node-to-node digest carry of two-permutation compress
    /// chains. Discharged by [`prove_shift_discharge_pow2`] with
    /// `shift_log = 1`.
    CommittedShift2(usize),
    /// A committed column read at a strided, offset position:
    /// `col(2^stride_log · w + offset)`, `offset < 2^stride_log`. This is
    /// the fan-in-2 tree wiring — a level-`ℓ` node at slot `w` reads its
    /// two children at slots `2w` and `2w+1` of the level-`ℓ+1` column via
    /// `Window { stride_log: 1, offset: 0 }` and `{..offset: 1}`. The child
    /// column has `2^stride_log` times the relation's slot count. Unlike a
    /// shift, the low `stride_log` index bits are FIXED constants, so the
    /// terminal claim is a plain MLE evaluation of the child column at the
    /// re-indexed point [`window_discharge_point`] — no successor kernel,
    /// discharged directly at the PCS like a [`ColRef::Committed`].
    Window {
        col: usize,
        stride_log: usize,
        offset: usize,
    },
    /// An internal (uncommitted) column — its terminal claim must feed a
    /// walk claim group or another relation's target.
    Internal(usize),
    /// A protocol-constant column ([`FixedPattern`]) — the verifier
    /// evaluates its MLE itself; no terminal claim, no `final_values`
    /// entry.
    Fixed(usize),
}

/// A protocol-constant column, periodic in the low `low_log` index bits:
/// `col(w) = table[w mod 2^low_log]`. Its MLE at any point ρ (with
/// `ρ.len() ≥ low_log`) is `table~(ρ[..low_log])` — the high coordinates
/// integrate out because `Σ_hi eq(ρ_hi, hi) = 1`.
///
/// An optional HI-GATE restricts the pattern to one aligned dyadic region
/// of the slot domain: with `hi_gate = Some((first, bits))` the column is
/// `table[w mod 2^low_log]` where the index bits `first..first+bits.len()`
/// of `w` equal `bits`, and ZERO everywhere else. The MLE gains one linear
/// factor per gated coordinate (`ρ_j` or `1+ρ_j`), so evaluation stays
/// closed-form; coordinates in `low_log..first` still integrate out (the
/// pattern repeats across them inside the region). This is what lets slot
/// regions with DIFFERENT periods share one walk domain: each region's
/// selector/constant patterns vanish exactly on the other regions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedPattern {
    pub low_log: usize,
    pub table: Vec<F128>,
    /// `(first_coord, required bits for coords first..first+len)`; the gate
    /// must pin every coordinate up to the walk's `w_log` (a shorter gate
    /// would alias the region across the un-pinned high bits).
    pub hi_gate: Option<(usize, Vec<bool>)>,
}

impl FixedPattern {
    pub fn new(low_log: usize, table: Vec<F128>) -> Self {
        assert_eq!(table.len(), 1usize << low_log, "fixed pattern length");
        Self {
            low_log,
            table,
            hi_gate: None,
        }
    }

    /// Restrict the pattern to the dyadic region whose index bits
    /// `first..first+bits.len()` equal `bits` (little-endian). `first` must
    /// be ≥ `low_log` and `first + bits.len()` must equal the walk's
    /// `w_log` exactly.
    pub fn gated(mut self, first: usize, bits: Vec<bool>) -> Self {
        assert!(first >= self.low_log, "gate below the pattern period");
        assert!(!bits.is_empty(), "empty hi-gate");
        self.hi_gate = Some((first, bits));
        self
    }

    /// MLE evaluation at a point of ≥ `low_log` coordinates (gated patterns
    /// require the point arity to equal `first + bits.len()` exactly — the
    /// gate must pin every high coordinate).
    pub fn eval(&self, point: &[F128]) -> F128 {
        assert!(point.len() >= self.low_log, "fixed pattern point arity");
        let eq = build_eq_table(&point[..self.low_log]);
        let mut acc = F128::ZERO;
        for (v, e) in self.table.iter().zip(eq.iter()) {
            acc += *v * *e;
        }
        if let Some((first, bits)) = &self.hi_gate {
            assert_eq!(point.len(), first + bits.len(), "gated pattern point arity");
            for (j, bit) in bits.iter().enumerate() {
                let p = point[first + j];
                acc = acc * if *bit { p } else { F128::ONE + p };
            }
        }
        acc
    }

    /// The periodic extension over a `2^w_log`-slot domain (prover side);
    /// gated patterns are zero outside their region, and the domain must
    /// match the gate's span exactly.
    pub fn materialize(&self, w: usize) -> Vec<F128> {
        assert!(w >= self.table.len(), "domain below pattern period");
        let mask = self.table.len() - 1;
        match &self.hi_gate {
            None => (0..w).map(|i| self.table[i & mask]).collect(),
            Some((first, bits)) => {
                assert_eq!(w, 1usize << (first + bits.len()), "gated pattern domain");
                let mut gate_val = 0usize;
                for (j, bit) in bits.iter().enumerate() {
                    if *bit {
                        gate_val |= 1 << j;
                    }
                }
                (0..w)
                    .map(|i| {
                        if i >> first == gate_val {
                            self.table[i & mask]
                        } else {
                            F128::ZERO
                        }
                    })
                    .collect()
            }
        }
    }
}

/// One product term: `coeff · Π factors` (0..=[`MAX_TERM_FACTORS`]
/// factors; empty = constant).
#[derive(Clone, Debug)]
pub struct RelationTerm {
    pub coeff: F128,
    pub factors: Vec<ColRef>,
}

/// Proof wires of one relation sumcheck.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ColumnRelationProof {
    /// Per round: `[c_0, c_2, .., c_d]` (compressed wire form).
    pub rounds: Vec<[F128; RELATION_DEGREE]>,
    /// MLE evaluation at the derived point per DISTINCT CLAIMED ColRef
    /// (Fixed refs excluded — the verifier evaluates those itself), in
    /// first-occurrence order over the term list.
    pub final_values: Vec<F128>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelationError {
    Shape,
    FinalMismatch,
}

impl std::fmt::Display for RelationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RelationError::Shape => write!(f, "relation proof shape mismatch"),
            RelationError::FinalMismatch => write!(f, "relation final claim mismatch"),
        }
    }
}

/// Distinct ColRefs in first-occurrence order (Fixed included) — the
/// prover's working-table layout.
pub fn distinct_refs(terms: &[RelationTerm]) -> Vec<ColRef> {
    let mut out = Vec::new();
    for t in terms {
        assert!(
            t.factors.len() <= MAX_TERM_FACTORS,
            "term arity above degree budget"
        );
        for f in &t.factors {
            if !out.contains(f) {
                out.push(*f);
            }
        }
    }
    out
}

/// Distinct CLAIMED ColRefs (Fixed excluded) in first-occurrence order —
/// the layout of `final_values` and of the returned claims.
pub fn claimed_refs(terms: &[RelationTerm]) -> Vec<ColRef> {
    distinct_refs(terms)
        .into_iter()
        .filter(|r| !matches!(r, ColRef::Fixed(_)))
        .collect()
}

/// The point at which a [`ColRef::Window`] terminal claim reads its CHILD
/// column: the `offset`'s low `stride_log` bits (little-endian, `point[0]`
/// = LSB) prepended to the relation's derived `point`. The window value
/// `Σ_w eq(point,w)·col(2^stride_log·w + offset)` equals the plain MLE
/// `col~(window_discharge_point(offset, stride_log, point))` exactly (the
/// fixed low bits select the coset; the high coordinates are `point`), so
/// the caller discharges it directly as a PCS opening — no shift kernel.
pub fn window_discharge_point(offset: usize, stride_log: usize, point: &[F128]) -> Vec<F128> {
    debug_assert!(
        offset < (1usize << stride_log),
        "window offset outside stride"
    );
    let mut out = Vec::with_capacity(stride_log + point.len());
    for j in 0..stride_log {
        out.push(if (offset >> j) & 1 == 1 {
            F128::ONE
        } else {
            F128::ZERO
        });
    }
    out.extend_from_slice(point);
    out
}

/// The columns backing a relation instance, prover side. `fixed` is also
/// consumed by the verifier (protocol constants, not witness).
pub struct RelationColumns<'a> {
    pub committed: &'a [&'a [F128]],
    pub internal: &'a [&'a [F128]],
    pub fixed: &'a [FixedPattern],
}

impl RelationColumns<'_> {
    fn resolve(&self, r: ColRef, w: usize) -> Vec<F128> {
        match r {
            ColRef::Committed(i) => self.committed[i].to_vec(),
            ColRef::Internal(i) => self.internal[i].to_vec(),
            ColRef::CommittedShift(i) => {
                let col = self.committed[i];
                let mut shifted = vec![F128::ZERO; w];
                shifted[1..].copy_from_slice(&col[..w - 1]);
                shifted
            }
            ColRef::CommittedShift2(i) => {
                let col = self.committed[i];
                let mut shifted = vec![F128::ZERO; w];
                shifted[2..].copy_from_slice(&col[..w - 2]);
                shifted
            }
            ColRef::Window {
                col,
                stride_log,
                offset,
            } => {
                let child = self.committed[col];
                let stride = 1usize << stride_log;
                assert!(offset < stride, "window offset outside stride");
                assert_eq!(child.len(), w << stride_log, "window child length");
                (0..w).map(|i| child[(i << stride_log) + offset]).collect()
            }
            ColRef::Fixed(i) => self.fixed[i].materialize(w),
        }
    }
}

fn absorb_relation_header<Ch: Challenger>(
    challenger: &mut Ch,
    target: F128,
    eq_point: &[F128],
    terms: &[RelationTerm],
) {
    challenger.observe_label(b"history-deep-chain-relation-v0");
    challenger.observe_f128(target);
    challenger.observe_f128_slice(eq_point);
    // Bind the relation structure: counts plus each term's coefficient and
    // factor encoding (kind, index).
    let lane = |a: u64, b: u64| F128 { lo: a, hi: b };
    let mut lanes = vec![lane(terms.len() as u64, 0)];
    for t in terms {
        lanes.push(t.coeff);
        lanes.push(lane(t.factors.len() as u64, 0));
        for f in &t.factors {
            match f {
                ColRef::Committed(i) => lanes.push(lane(0, *i as u64)),
                ColRef::CommittedShift(i) => lanes.push(lane(1, *i as u64)),
                ColRef::Internal(i) => lanes.push(lane(2, *i as u64)),
                // Fixed pattern CONTENT is a protocol constant on both
                // sides (like the term structure itself) — only the
                // reference is bound.
                ColRef::Fixed(i) => lanes.push(lane(3, *i as u64)),
                ColRef::CommittedShift2(i) => lanes.push(lane(4, *i as u64)),
                // Window carries three integers; bind the column reference
                // plus a second lane for the strided-offset layout.
                ColRef::Window {
                    col,
                    stride_log,
                    offset,
                } => {
                    lanes.push(lane(5, *col as u64));
                    lanes.push(lane(*stride_log as u64, *offset as u64));
                }
            }
        }
    }
    challenger.observe_f128_slice(&lanes);
}

#[inline]
fn f128_of_usize(t: usize) -> F128 {
    F128 {
        lo: t as u64,
        hi: 0,
    }
}

const RELATION_NODES: usize = RELATION_DEGREE + 1;

fn reconstruct_round(wire: &[F128; RELATION_DEGREE], claim: F128) -> [F128; RELATION_NODES] {
    // c_1 = claim + Σ_{i≥2} c_i (char 2).
    let mut c1 = claim;
    for &c in &wire[1..] {
        c1 += c;
    }
    let mut coeffs = [F128::ZERO; RELATION_NODES];
    coeffs[0] = wire[0];
    coeffs[1] = c1;
    coeffs[2..].copy_from_slice(&wire[1..]);
    coeffs
}

#[inline]
fn horner_round(coeffs: &[F128; RELATION_NODES], x: F128) -> F128 {
    let mut acc = coeffs[RELATION_NODES - 1];
    for &c in coeffs[..RELATION_NODES - 1].iter().rev() {
        acc = acc * x + c;
    }
    acc
}

/// Interpolate a degree-[`RELATION_DEGREE`] polynomial from evaluations at
/// the flat-basis nodes 0..=[`RELATION_DEGREE`] into monomial coefficients
/// (char-2 exact).
fn interpolate_round(evals: &[F128; RELATION_NODES]) -> [F128; RELATION_NODES] {
    static BASIS: std::sync::OnceLock<[[F128; RELATION_NODES]; RELATION_NODES]> =
        std::sync::OnceLock::new();
    let basis = BASIS.get_or_init(|| {
        let nodes: [F128; RELATION_NODES] = std::array::from_fn(f128_of_usize);
        std::array::from_fn(|i| {
            let mut poly = [F128::ZERO; RELATION_NODES];
            poly[0] = F128::ONE;
            let mut deg = 0usize;
            let mut denom = F128::ONE;
            for (j, &t_j) in nodes.iter().enumerate() {
                if j == i {
                    continue;
                }
                denom = denom * (nodes[i] + t_j);
                let mut next = [F128::ZERO; RELATION_NODES];
                for d in 0..=deg {
                    next[d + 1] += poly[d];
                    next[d] += poly[d] * t_j;
                }
                deg += 1;
                poly = next;
            }
            let inv = super::f128_inv_pub(denom);
            std::array::from_fn(|d| poly[d] * inv)
        })
    });
    let mut coeffs = [F128::ZERO; RELATION_NODES];
    for (i, &e) in evals.iter().enumerate() {
        for d in 0..RELATION_NODES {
            coeffs[d] += e * basis[i][d];
        }
    }
    coeffs
}

/// Prove `target = Σ_w eq(eq_point, w) · Σ_terms coeff · Π factors(w)`.
///
/// Returns the proof and the derived point with per-distinct-ref values —
/// the caller turns Committed refs into PCS opening claims, CommittedShift
/// refs into [`prove_shift_discharge`] runs, and Internal refs into walk
/// claim groups or downstream targets.
pub fn prove_column_relation<Ch: Challenger>(
    target: F128,
    eq_point: &[F128],
    terms: &[RelationTerm],
    columns: &RelationColumns<'_>,
    challenger: &mut Ch,
) -> (ColumnRelationProof, Vec<F128>, Vec<F128>) {
    let w_log = eq_point.len();
    let w = 1usize << w_log;
    let refs = distinct_refs(terms);
    let claimed = claimed_refs(terms);

    absorb_relation_header(challenger, target, eq_point, terms);

    // Materialize one working table per distinct ref plus the eq table.
    let mut tables: Vec<Vec<F128>> = refs
        .par_iter()
        .map(|&reference| columns.resolve(reference, w))
        .collect();
    for t in &tables {
        assert_eq!(t.len(), w, "column length mismatch");
    }
    let mut eq = build_eq_table(eq_point);
    // Folding used to allocate a fresh output Vec for every table in every
    // round.  Keep one alternate buffer per table instead: after the first
    // fold the two allocations simply swap roles for the remaining rounds.
    let mut table_scratch: Vec<Vec<F128>> = (0..tables.len()).map(|_| Vec::new()).collect();
    let mut eq_scratch = Vec::new();

    // Term factor indices into `refs`.
    let term_refs: Vec<(F128, Vec<usize>)> = terms
        .iter()
        .map(|t| {
            (
                t.coeff,
                t.factors
                    .iter()
                    .map(|f| refs.iter().position(|r| r == f).expect("distinct ref"))
                    .collect(),
            )
        })
        .collect();

    let mut claim = target;
    let mut rounds = Vec::with_capacity(w_log);
    let mut point = Vec::with_capacity(w_log);
    for _round in 0..w_log {
        let half = eq.len() / 2;
        // `bases` is only pair-local scratch.  Allocating it in the item
        // closure caused one heap allocation per Boolean pair (131071 of
        // them for a 2^17 relation), amplified by recording relations with
        // dozens of fixed refs.  Rayon fold state gives each worker one Vec
        // to clear and reuse while preserving the exact coefficient sums.
        let table_count = tables.len();
        let (evals, _) = (0..half)
            .into_par_iter()
            .fold(
                || {
                    (
                        [F128::ZERO; RELATION_NODES],
                        Vec::with_capacity(table_count),
                    )
                },
                |(mut acc, mut bases), p| {
                    let eq_base = eq[2 * p];
                    let eq_delta = eq[2 * p] + eq[2 * p + 1];
                    bases.clear();
                    bases.extend(tables.iter().map(|t| (t[2 * p], t[2 * p] + t[2 * p + 1])));
                    for (t, slot) in acc.iter_mut().enumerate() {
                        let t_f = f128_of_usize(t);
                        let eq_t = eq_base + t_f * eq_delta;
                        let mut sum = F128::ZERO;
                        for (coeff, fidx) in &term_refs {
                            let mut prod = *coeff;
                            for &fi in fidx {
                                let (b, d) = bases[fi];
                                prod = prod * (b + t_f * d);
                            }
                            sum += prod;
                        }
                        *slot += eq_t * sum;
                    }
                    (acc, bases)
                },
            )
            .reduce(
                || ([F128::ZERO; RELATION_NODES], Vec::new()),
                |(mut a, mut a_scratch), (b, b_scratch)| {
                    for (x, y) in a.iter_mut().zip(b.iter()) {
                        *x += *y;
                    }
                    if b_scratch.capacity() > a_scratch.capacity() {
                        a_scratch = b_scratch;
                    }
                    (a, a_scratch)
                },
            );
        let full = interpolate_round(&evals);
        debug_assert_eq!(
            full[0] + horner_round(&full, F128::ONE),
            claim,
            "relation prover-side round mismatch"
        );
        let mut wire = [F128::ZERO; RELATION_DEGREE];
        wire[0] = full[0];
        wire[1..].copy_from_slice(&full[2..]);
        challenger.observe_f128_slice(&wire);
        let r = challenger.sample_f128();
        claim = horner_round(&full, r);
        point.push(r);
        rounds.push(wire);
        // Every relation table folds at the same challenge and is otherwise
        // independent. One outer parallel pass avoids a Rayon barrier per
        // reference while retaining each indexed fold's exact order.
        rayon::join(
            || fold_table_reuse(&mut eq, &mut eq_scratch, r),
            || {
                tables
                    .par_iter_mut()
                    .zip(&mut table_scratch)
                    .for_each(|(table, scratch)| fold_table_reuse(table, scratch, r));
            },
        );
    }

    // Only claimed refs travel; Fixed values are verifier-computed.
    let final_values: Vec<F128> = refs
        .iter()
        .zip(tables.iter())
        .filter(|(r, _)| !matches!(r, ColRef::Fixed(_)))
        .map(|(_, t)| t[0])
        .collect();
    debug_assert_eq!(final_values.len(), claimed.len());
    challenger.observe_f128_slice(&final_values);
    debug_assert_eq!(
        {
            let mut sum = F128::ZERO;
            for (coeff, fidx) in &term_refs {
                let mut prod = *coeff;
                for &fi in fidx {
                    prod = prod * tables[fi][0];
                }
                sum += prod;
            }
            eq[0] * sum
        },
        claim,
        "relation prover-side final mismatch"
    );

    (
        ColumnRelationProof {
            rounds,
            final_values: final_values.clone(),
        },
        point,
        final_values,
    )
}

/// Verify a relation sumcheck; returns the derived point (the per-ref
/// values live in `proof.final_values`, ordered by [`claimed_refs`];
/// Fixed factors are evaluated from `fixed` in closed form).
pub fn verify_column_relation<Ch: Challenger>(
    w_log: usize,
    target: F128,
    eq_point: &[F128],
    terms: &[RelationTerm],
    fixed: &[FixedPattern],
    proof: &ColumnRelationProof,
    challenger: &mut Ch,
) -> Result<Vec<F128>, RelationError> {
    let claimed = claimed_refs(terms);
    if eq_point.len() != w_log
        || proof.rounds.len() != w_log
        || proof.final_values.len() != claimed.len()
    {
        return Err(RelationError::Shape);
    }

    absorb_relation_header(challenger, target, eq_point, terms);

    let mut claim = target;
    let mut point = Vec::with_capacity(w_log);
    for wire in &proof.rounds {
        challenger.observe_f128_slice(wire);
        let full = reconstruct_round(wire, claim);
        let r = challenger.sample_f128();
        claim = horner_round(&full, r);
        point.push(r);
    }
    challenger.observe_f128_slice(&proof.final_values);

    let mut sum = F128::ZERO;
    for t in terms {
        let mut prod = t.coeff;
        for f in &t.factors {
            prod = prod
                * match f {
                    ColRef::Fixed(i) => fixed[*i].eval(&point),
                    _ => {
                        let fi = claimed.iter().position(|r| r == f).expect("claimed ref");
                        proof.final_values[fi]
                    }
                };
        }
        sum += prod;
    }
    let eq = super::eq_eval_pub(eq_point, &point);
    if eq * sum != claim {
        return Err(RelationError::FinalMismatch);
    }
    Ok(point)
}

fn fold_table_reuse(table: &mut Vec<F128>, scratch: &mut Vec<F128>, r: F128) {
    let half = table.len() / 2;
    scratch.clear();
    scratch.par_extend((0..half).into_par_iter().map(|p| {
        let a = table[2 * p];
        let b = table[2 * p + 1];
        a + r * (a + b)
    }));
    std::mem::swap(table, scratch);
}

// ---------------------------------------------------------------------------
// Shift discharge
// ---------------------------------------------------------------------------

/// Closed form of the successor kernel
/// `N(ρ, σ) = Σ_w eq(ρ, w+1)·eq(σ, w)` (sum over non-overflowing w):
/// grouping by the carry length k of `w → w+1`,
///
/// ```text
///   N = Σ_{k<n} [Π_{i<k} σ_i(1+ρ_i)] · ρ_k(1+σ_k) · [Π_{i>k} (ρ_iσ_i + (1+ρ_i)(1+σ_i))]
/// ```
pub fn shift_kernel_eval(rho: &[F128], sigma: &[F128]) -> F128 {
    assert_eq!(rho.len(), sigma.len());
    let n = rho.len();
    // Suffix products of the matched factors.
    let mut suffix = vec![F128::ONE; n + 1];
    for i in (0..n).rev() {
        let matched = rho[i] * sigma[i] + (F128::ONE + rho[i]) * (F128::ONE + sigma[i]);
        suffix[i] = matched * suffix[i + 1];
    }
    let mut acc = F128::ZERO;
    let mut prefix = F128::ONE;
    for k in 0..n {
        acc += prefix * rho[k] * (F128::ONE + sigma[k]) * suffix[k + 1];
        prefix = prefix * sigma[k] * (F128::ONE + rho[k]);
    }
    acc
}

/// Closed form of the `2^shift_log`-step kernel
/// `N_s(ρ, σ) = Σ_w eq(ρ, w + 2^shift_log)·eq(σ, w)`: adding `2^k` leaves
/// the low `k` bits untouched and increments the high part by one, so the
/// kernel factors into matched low bits times the successor kernel on the
/// high coordinates.
pub fn shift_pow2_kernel_eval(shift_log: usize, rho: &[F128], sigma: &[F128]) -> F128 {
    assert_eq!(rho.len(), sigma.len());
    assert!(shift_log < rho.len(), "shift below the domain size");
    let mut acc = F128::ONE;
    for i in 0..shift_log {
        acc = acc * (rho[i] * sigma[i] + (F128::ONE + rho[i]) * (F128::ONE + sigma[i]));
    }
    acc * shift_kernel_eval(&rho[shift_log..], &sigma[shift_log..])
}

/// Proof wires of one shift discharge (degree-2 rounds `[c_0, c_2]` plus
/// the terminal plain MLE value).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ShiftDischargeProof {
    pub rounds: Vec<[F128; 2]>,
    pub final_value: F128,
}

/// Prove `target = Σ_w N(σ, w)·col(w)` — i.e. discharge a shifted-column
/// claim at σ into the plain claim `col~(derived point) = final_value`.
pub fn prove_shift_discharge<Ch: Challenger>(
    col: &[F128],
    sigma: &[F128],
    target: F128,
    challenger: &mut Ch,
) -> (ShiftDischargeProof, Vec<F128>) {
    prove_shift_discharge_pow2(col, sigma, target, 0, challenger)
}

/// Prove the `2^shift_log`-step variant: discharge
/// `Σ_w eq(σ,w)·col(w − 2^shift_log) = target` into a plain claim.
pub fn prove_shift_discharge_pow2<Ch: Challenger>(
    col: &[F128],
    sigma: &[F128],
    target: F128,
    shift_log: usize,
    challenger: &mut Ch,
) -> (ShiftDischargeProof, Vec<F128>) {
    let w = col.len();
    assert!(w.is_power_of_two());
    let w_log = w.trailing_zeros() as usize;
    assert_eq!(sigma.len(), w_log);
    let shift = 1usize << shift_log;
    assert!(shift < w);

    absorb_shift_header(challenger, target, sigma, shift_log);

    // N table: N[w] = eq(σ, w + shift), 0 at the top slots.
    let eq_sigma = build_eq_table(sigma);
    let mut n_table = vec![F128::ZERO; w];
    n_table[..w - shift].copy_from_slice(&eq_sigma[shift..]);
    let mut col_table = col.to_vec();
    let mut n_scratch = Vec::new();
    let mut col_scratch = Vec::new();

    let mut claim = target;
    let mut rounds = Vec::with_capacity(w_log);
    let mut point = Vec::with_capacity(w_log);
    for _round in 0..w_log {
        let half = n_table.len() / 2;
        let evals = (0..half)
            .into_par_iter()
            .fold(
                || [F128::ZERO; 3],
                |mut acc, p| {
                    let nb = n_table[2 * p];
                    let nd = n_table[2 * p] + n_table[2 * p + 1];
                    let cb = col_table[2 * p];
                    let cd = col_table[2 * p] + col_table[2 * p + 1];
                    for (t, slot) in acc.iter_mut().enumerate() {
                        let t_f = f128_of_usize(t);
                        *slot += (nb + t_f * nd) * (cb + t_f * cd);
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
            );
        let full = interpolate_deg2(&evals);
        // p(0) + p(1) = c_1 + c_2 must equal the running claim (char 2).
        debug_assert_eq!(full[1] + full[2], claim);
        let wire = [full[0], full[2]];
        challenger.observe_f128_slice(&wire);
        let r = challenger.sample_f128();
        claim = (full[2] * r + full[1]) * r + full[0];
        point.push(r);
        rounds.push(wire);
        rayon::join(
            || fold_table_reuse(&mut n_table, &mut n_scratch, r),
            || fold_table_reuse(&mut col_table, &mut col_scratch, r),
        );
    }

    let final_value = col_table[0];
    challenger.observe_f128(final_value);
    debug_assert_eq!(n_table[0] * final_value, claim);

    (
        ShiftDischargeProof {
            rounds,
            final_value,
        },
        point,
    )
}

fn absorb_shift_header<Ch: Challenger>(
    challenger: &mut Ch,
    target: F128,
    sigma: &[F128],
    shift_log: usize,
) {
    challenger.observe_label(b"history-deep-chain-shift-v0");
    challenger.observe_f128(F128 {
        lo: shift_log as u64,
        hi: 0,
    });
    challenger.observe_f128(target);
    challenger.observe_f128_slice(sigma);
}

/// Verify a shift discharge; returns the derived point (pair it with
/// `proof.final_value` as the plain committed-column claim).
pub fn verify_shift_discharge<Ch: Challenger>(
    w_log: usize,
    sigma: &[F128],
    target: F128,
    proof: &ShiftDischargeProof,
    challenger: &mut Ch,
) -> Result<Vec<F128>, RelationError> {
    verify_shift_discharge_pow2(w_log, sigma, target, 0, proof, challenger)
}

/// Verify the `2^shift_log`-step variant.
pub fn verify_shift_discharge_pow2<Ch: Challenger>(
    w_log: usize,
    sigma: &[F128],
    target: F128,
    shift_log: usize,
    proof: &ShiftDischargeProof,
    challenger: &mut Ch,
) -> Result<Vec<F128>, RelationError> {
    if sigma.len() != w_log || proof.rounds.len() != w_log || shift_log >= w_log {
        return Err(RelationError::Shape);
    }
    absorb_shift_header(challenger, target, sigma, shift_log);

    let mut claim = target;
    let mut point = Vec::with_capacity(w_log);
    for wire in &proof.rounds {
        challenger.observe_f128_slice(wire);
        // c_1 = claim + c_2 (char 2, degree 2).
        let c1 = claim + wire[1];
        let r = challenger.sample_f128();
        claim = (wire[1] * r + c1) * r + wire[0];
        point.push(r);
    }
    challenger.observe_f128(proof.final_value);

    if shift_pow2_kernel_eval(shift_log, sigma, &point) * proof.final_value != claim {
        return Err(RelationError::FinalMismatch);
    }
    Ok(point)
}

// ---------------------------------------------------------------------------
// Weighted-sum discharge (closed-form kernel)
// ---------------------------------------------------------------------------

/// Proof wires of one weighted-sum discharge (degree-2 rounds `[c_0, c_2]`
/// plus the terminal plain MLE value of the committed column).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WeightedSumProof {
    pub rounds: Vec<[F128; 2]>,
    pub final_value: F128,
}

/// Prove `target = Σ_i weights[i]·col[i]` as a product-of-two-multilinears
/// sumcheck, reducing it to a plain claim `col~(point) = final_value`. The
/// weight sequence is a CLOSED-FORM kernel (e.g. the additive-NTT encode
/// kernel times `eq(right, ·)`): the prover materializes it here, but the
/// verifier never does — it re-derives `weights~(point)` in O(n) from the
/// kernel's closed form (passed to [`verify_weighted_sum`]). This is the
/// source-binding reduction `codeword~(z) = Σ_i K_i(z)·eq(right,i)·H[i]`.
pub fn prove_weighted_sum<Ch: Challenger>(
    col: &[F128],
    weights: &[F128],
    target: F128,
    challenger: &mut Ch,
) -> (WeightedSumProof, Vec<F128>) {
    let w = col.len();
    assert_eq!(weights.len(), w, "weight length");
    assert!(w.is_power_of_two());
    let w_log = w.trailing_zeros() as usize;

    absorb_weighted_header(challenger, target);

    let mut wt = weights.to_vec();
    let mut col_t = col.to_vec();
    let mut wt_scratch = Vec::new();
    let mut col_scratch = Vec::new();
    let mut claim = target;
    let mut rounds = Vec::with_capacity(w_log);
    let mut point = Vec::with_capacity(w_log);
    for _round in 0..w_log {
        let half = wt.len() / 2;
        let evals = (0..half)
            .into_par_iter()
            .fold(
                || [F128::ZERO; 3],
                |mut acc, p| {
                    let wb = wt[2 * p];
                    let wd = wt[2 * p] + wt[2 * p + 1];
                    let cb = col_t[2 * p];
                    let cd = col_t[2 * p] + col_t[2 * p + 1];
                    for (t, slot) in acc.iter_mut().enumerate() {
                        let t_f = f128_of_usize(t);
                        *slot += (wb + t_f * wd) * (cb + t_f * cd);
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
            );
        let full = interpolate_deg2(&evals);
        debug_assert_eq!(full[1] + full[2], claim);
        let wire = [full[0], full[2]];
        challenger.observe_f128_slice(&wire);
        let r = challenger.sample_f128();
        claim = (full[2] * r + full[1]) * r + full[0];
        point.push(r);
        rounds.push(wire);
        rayon::join(
            || fold_table_reuse(&mut wt, &mut wt_scratch, r),
            || fold_table_reuse(&mut col_t, &mut col_scratch, r),
        );
    }
    let final_value = col_t[0];
    challenger.observe_f128(final_value);
    debug_assert_eq!(wt[0] * final_value, claim);
    (
        WeightedSumProof {
            rounds,
            final_value,
        },
        point,
    )
}

/// Verify a weighted-sum discharge; returns the derived point. `weight_eval`
/// computes `weights~(derived point)` from the kernel's CLOSED FORM (the
/// derived point is only known inside the sumcheck, so it is a callback):
/// the terminal check is `weights~(point)·final_value = claim`. Pair
/// `(point, final_value)` as the column's plain PCS opening claim.
pub fn verify_weighted_sum<Ch: Challenger, W: Fn(&[F128]) -> F128>(
    w_log: usize,
    weight_eval: W,
    target: F128,
    proof: &WeightedSumProof,
    challenger: &mut Ch,
) -> Result<Vec<F128>, RelationError> {
    if proof.rounds.len() != w_log {
        return Err(RelationError::Shape);
    }
    absorb_weighted_header(challenger, target);
    let mut claim = target;
    let mut point = Vec::with_capacity(w_log);
    for wire in &proof.rounds {
        challenger.observe_f128_slice(wire);
        let c1 = claim + wire[1];
        let r = challenger.sample_f128();
        claim = (wire[1] * r + c1) * r + wire[0];
        point.push(r);
    }
    challenger.observe_f128(proof.final_value);
    if weight_eval(&point) * proof.final_value != claim {
        return Err(RelationError::FinalMismatch);
    }
    Ok(point)
}

fn absorb_weighted_header<Ch: Challenger>(challenger: &mut Ch, target: F128) {
    challenger.observe_label(b"history-deep-chain-weighted-v0");
    challenger.observe_f128(target);
}

fn interpolate_deg2(evals: &[F128; 3]) -> [F128; 3] {
    // Nodes 0, 1, 2 (flat basis). c_0 = p(0). Solve the 2×2 system for
    // c_1, c_2 (char-2 exact): p(1) = c_0 + c_1 + c_2;
    // p(2) = c_0 + 2·c_1 + 4·c_2 with 2 = x, 4 = x² in the flat basis.
    static INV: std::sync::OnceLock<(F128, F128, F128)> = std::sync::OnceLock::new();
    let (two, four, inv_det) = *INV.get_or_init(|| {
        let two = f128_of_usize(2);
        let four = two * two;
        // det = 2·(4 + ... solve directly: from
        //   s1 = c_1 + c_2, s2 = 2c_1 + 4c_2:
        //   c_2 = (s2 + 2·s1) / (4 + 2), c_1 = s1 + c_2.
        let det = four + two;
        (two, four, super::f128_inv_pub(det))
    });
    let _ = four;
    let c0 = evals[0];
    let s1 = evals[1] + c0;
    let s2 = evals[2] + c0;
    let c2 = (s2 + two * s1) * inv_det;
    let c1 = s1 + c2;
    [c0, c1, c2]
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::{Challenger, FsLaneChallenger};

    /// Allocation-heavy implementation retained only as a byte-parity oracle
    /// for the optimized prover loop above.
    fn prove_column_relation_allocating_reference<Ch: Challenger>(
        target: F128,
        eq_point: &[F128],
        terms: &[RelationTerm],
        columns: &RelationColumns<'_>,
        challenger: &mut Ch,
    ) -> (ColumnRelationProof, Vec<F128>, Vec<F128>) {
        let w_log = eq_point.len();
        let w = 1usize << w_log;
        let refs = distinct_refs(terms);
        let claimed = claimed_refs(terms);

        absorb_relation_header(challenger, target, eq_point, terms);
        let mut tables: Vec<Vec<F128>> = refs
            .iter()
            .map(|&reference| columns.resolve(reference, w))
            .collect();
        let mut eq = build_eq_table(eq_point);
        let term_refs: Vec<(F128, Vec<usize>)> = terms
            .iter()
            .map(|term| {
                (
                    term.coeff,
                    term.factors
                        .iter()
                        .map(|factor| refs.iter().position(|r| r == factor).unwrap())
                        .collect(),
                )
            })
            .collect();

        let mut claim = target;
        let mut rounds = Vec::with_capacity(w_log);
        let mut point = Vec::with_capacity(w_log);
        for _round in 0..w_log {
            let half = eq.len() / 2;
            let evals = (0..half)
                .into_par_iter()
                .fold(
                    || [F128::ZERO; RELATION_NODES],
                    |mut acc, p| {
                        let eq_base = eq[2 * p];
                        let eq_delta = eq[2 * p] + eq[2 * p + 1];
                        let bases: Vec<(F128, F128)> = tables
                            .iter()
                            .map(|table| (table[2 * p], table[2 * p] + table[2 * p + 1]))
                            .collect();
                        for (t, slot) in acc.iter_mut().enumerate() {
                            let t_f = f128_of_usize(t);
                            let eq_t = eq_base + t_f * eq_delta;
                            let mut sum = F128::ZERO;
                            for (coeff, factors) in &term_refs {
                                let mut product = *coeff;
                                for &factor in factors {
                                    let (base, delta) = bases[factor];
                                    product *= base + t_f * delta;
                                }
                                sum += product;
                            }
                            *slot += eq_t * sum;
                        }
                        acc
                    },
                )
                .reduce(
                    || [F128::ZERO; RELATION_NODES],
                    |mut left, right| {
                        for (left, right) in left.iter_mut().zip(right) {
                            *left += right;
                        }
                        left
                    },
                );
            let full = interpolate_round(&evals);
            debug_assert_eq!(full[0] + horner_round(&full, F128::ONE), claim);
            let mut wire = [F128::ZERO; RELATION_DEGREE];
            wire[0] = full[0];
            wire[1..].copy_from_slice(&full[2..]);
            challenger.observe_f128_slice(&wire);
            let r = challenger.sample_f128();
            claim = horner_round(&full, r);
            point.push(r);
            rounds.push(wire);
            let fold_allocating = |table: &mut Vec<F128>| {
                let half = table.len() / 2;
                *table = (0..half)
                    .into_par_iter()
                    .map(|p| {
                        let a = table[2 * p];
                        let b = table[2 * p + 1];
                        a + r * (a + b)
                    })
                    .collect();
            };
            fold_allocating(&mut eq);
            for table in &mut tables {
                fold_allocating(table);
            }
        }

        let final_values: Vec<F128> = refs
            .iter()
            .zip(&tables)
            .filter(|(reference, _)| !matches!(reference, ColRef::Fixed(_)))
            .map(|(_, table)| table[0])
            .collect();
        debug_assert_eq!(final_values.len(), claimed.len());
        challenger.observe_f128_slice(&final_values);
        (
            ColumnRelationProof {
                rounds,
                final_values: final_values.clone(),
            },
            point,
            final_values,
        )
    }

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
        fn bit(&mut self) -> F128 {
            if self.next_u64() & 1 == 1 {
                F128::ONE
            } else {
                F128::ZERO
            }
        }
    }

    fn mle_eval(col: &[F128], point: &[F128]) -> F128 {
        let eq = build_eq_table(point);
        let mut acc = F128::ZERO;
        for (v, e) in col.iter().zip(eq.iter()) {
            acc += *v * *e;
        }
        acc
    }

    fn random_col(rng: &mut Rng, w: usize) -> Vec<F128> {
        (0..w).map(|_| rng.f128()).collect()
    }

    #[test]
    fn column_relation_reused_scratch_is_byte_identical() {
        // Mirror the recordings-C substitution shape: six committed columns,
        // nine disjoint seven-pattern sets, 94 terms and 69 distinct refs.
        let mut rng = Rng(0x5C4A_7C4);
        // The override turns this parity test into a narrow release microbench
        // without burdening the default test suite (for example, set it to
        // 14 to make allocator overhead visible).
        let w_log = std::env::var("NOID_RELATION_PARITY_W_LOG")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(8usize);
        assert!(w_log >= 8);
        let w = 1usize << w_log;
        let committed_owned: Vec<Vec<F128>> = (0..6).map(|_| random_col(&mut rng, w)).collect();
        let committed: Vec<&[F128]> = committed_owned.iter().map(Vec::as_slice).collect();

        let mut fixed = Vec::new();
        for set in 0..9usize {
            let gate_bits: Vec<bool> = (0..w_log - 4).map(|bit| (set >> bit) & 1 == 1).collect();
            for _pattern in 0..7 {
                fixed.push(
                    FixedPattern::new(4, random_col(&mut rng, 1 << 4)).gated(4, gate_bits.clone()),
                );
            }
        }
        let columns = RelationColumns {
            committed: &committed,
            internal: &[],
            fixed: &fixed,
        };

        let mut terms = Vec::new();
        for lane in 0..4 {
            terms.push(RelationTerm {
                coeff: rng.f128(),
                factors: vec![ColRef::CommittedShift(2 + lane)],
            });
        }
        for set in 0..9usize {
            let base = 7 * set;
            for lane in 0..4 {
                terms.push(RelationTerm {
                    coeff: rng.f128(),
                    factors: vec![ColRef::Fixed(base), ColRef::CommittedShift(2 + lane)],
                });
                if lane < 2 {
                    terms.push(RelationTerm {
                        coeff: rng.f128(),
                        factors: vec![ColRef::Fixed(base + 1 + lane), ColRef::Committed(lane)],
                    });
                }
                terms.push(RelationTerm {
                    coeff: rng.f128(),
                    factors: vec![ColRef::Fixed(base + 3 + lane)],
                });
            }
        }
        assert_eq!(terms.len(), 94);
        assert_eq!(distinct_refs(&terms).len(), 69);

        let eq_point: Vec<F128> = (0..w_log).map(|_| rng.f128()).collect();
        let eq = build_eq_table(&eq_point);
        let refs = distinct_refs(&terms);
        let resolved: Vec<Vec<F128>> = refs
            .iter()
            .map(|&reference| columns.resolve(reference, w))
            .collect();
        let mut target = F128::ZERO;
        for row in 0..w {
            let mut relation = F128::ZERO;
            for term in &terms {
                let mut product = term.coeff;
                for factor in &term.factors {
                    let index = refs
                        .iter()
                        .position(|reference| reference == factor)
                        .unwrap();
                    product *= resolved[index][row];
                }
                relation += product;
            }
            target += eq[row] * relation;
        }

        let mut reference_challenger = FsLaneChallenger::new(b"relation-scratch-parity");
        let reference_started = std::time::Instant::now();
        let reference = prove_column_relation_allocating_reference(
            target,
            &eq_point,
            &terms,
            &columns,
            &mut reference_challenger,
        );
        let reference_elapsed = reference_started.elapsed();
        let mut optimized_challenger = FsLaneChallenger::new(b"relation-scratch-parity");
        let optimized_started = std::time::Instant::now();
        let optimized = prove_column_relation(
            target,
            &eq_point,
            &terms,
            &columns,
            &mut optimized_challenger,
        );
        let optimized_elapsed = optimized_started.elapsed();
        if std::env::var_os("NOID_RELATION_PARITY_W_LOG").is_some() {
            eprintln!(
                "recording relation w_log={w_log}: allocating={reference_elapsed:?} reused={optimized_elapsed:?} speedup={:.2}x",
                reference_elapsed.as_secs_f64() / optimized_elapsed.as_secs_f64(),
            );
        }
        assert_eq!(optimized, reference);
        assert_eq!(
            optimized_challenger.sample_f128(),
            reference_challenger.sample_f128(),
            "post-proof Fiat-Shamir state",
        );

        let mut verifier = FsLaneChallenger::new(b"relation-scratch-parity");
        let verified_point = verify_column_relation(
            w_log,
            target,
            &eq_point,
            &terms,
            &fixed,
            &optimized.0,
            &mut verifier,
        )
        .expect("optimized proof verifies");
        assert_eq!(verified_point, optimized.1);
    }

    #[test]
    fn shift_kernel_matches_direct_sum() {
        let mut rng = Rng(0x511F7);
        for n in [1usize, 2, 4, 6] {
            let rho: Vec<F128> = (0..n).map(|_| rng.f128()).collect();
            let sigma: Vec<F128> = (0..n).map(|_| rng.f128()).collect();
            let eq_rho = build_eq_table(&rho);
            let eq_sigma = build_eq_table(&sigma);
            let mut direct = F128::ZERO;
            for w in 0..(1usize << n) - 1 {
                direct += eq_rho[w + 1] * eq_sigma[w];
            }
            assert_eq!(shift_kernel_eval(&rho, &sigma), direct, "n={n}");
        }
    }

    #[test]
    fn shift_pow2_kernel_and_roundtrip() {
        let mut rng = Rng(0x511F8);
        // Kernel closed form vs the direct double sum, shifts 2 and 4.
        for (shift_log, n) in [(1usize, 4usize), (1, 6), (2, 5)] {
            let shift = 1usize << shift_log;
            let rho: Vec<F128> = (0..n).map(|_| rng.f128()).collect();
            let sigma: Vec<F128> = (0..n).map(|_| rng.f128()).collect();
            let eq_rho = build_eq_table(&rho);
            let eq_sigma = build_eq_table(&sigma);
            let mut direct = F128::ZERO;
            for w in 0..(1usize << n) - shift {
                direct += eq_rho[w + shift] * eq_sigma[w];
            }
            assert_eq!(
                shift_pow2_kernel_eval(shift_log, &rho, &sigma),
                direct,
                "shift_log={shift_log} n={n}"
            );
        }

        // Discharge roundtrip at shift 2.
        let w_log = 5;
        let w = 1usize << w_log;
        let col = random_col(&mut rng, w);
        let sigma: Vec<F128> = (0..w_log).map(|_| rng.f128()).collect();
        let eq = build_eq_table(&sigma);
        let mut target = F128::ZERO;
        for i in 2..w {
            target += eq[i] * col[i - 2];
        }
        let mut ch_p = FsLaneChallenger::new(b"shift2-test");
        let (proof, point_p) = prove_shift_discharge_pow2(&col, &sigma, target, 1, &mut ch_p);
        let mut ch_v = FsLaneChallenger::new(b"shift2-test");
        let point_v = verify_shift_discharge_pow2(w_log, &sigma, target, 1, &proof, &mut ch_v)
            .expect("honest shift2 discharge");
        assert_eq!(point_p, point_v);
        assert_eq!(mle_eval(&col, &point_v), proof.final_value);

        // The shift amount is transcript-bound: verifying the same proof
        // as a 1-step discharge fails.
        let mut ch = FsLaneChallenger::new(b"shift2-test");
        assert!(verify_shift_discharge(w_log, &sigma, target, &proof, &mut ch).is_err());
    }

    #[test]
    fn shift_discharge_roundtrip_and_mutations() {
        let mut rng = Rng(0xD15C);
        let w_log = 5;
        let w = 1usize << w_log;
        let col = random_col(&mut rng, w);
        let sigma: Vec<F128> = (0..w_log).map(|_| rng.f128()).collect();
        // target = Σ_w eq(σ,w)·col(w−1)
        let eq = build_eq_table(&sigma);
        let mut target = F128::ZERO;
        for i in 1..w {
            target += eq[i] * col[i - 1];
        }

        let mut ch_p = FsLaneChallenger::new(b"shift-test");
        let (proof, point_p) = prove_shift_discharge(&col, &sigma, target, &mut ch_p);
        let mut ch_v = FsLaneChallenger::new(b"shift-test");
        let point_v = verify_shift_discharge(w_log, &sigma, target, &proof, &mut ch_v)
            .expect("honest shift discharge");
        assert_eq!(point_p, point_v);
        assert_eq!(mle_eval(&col, &point_v), proof.final_value);
        assert_eq!(ch_p.sample_f128(), ch_v.sample_f128());

        // Forged target rejected (kernel-vs-final check catches whp).
        let mut ch = FsLaneChallenger::new(b"shift-test");
        let bad = verify_shift_discharge(w_log, &sigma, target + F128::ONE, &proof, &mut ch);
        assert!(bad.is_err());

        // Any wire mutation rejected or lands on a false plain claim.
        for round in 0..w_log {
            for c in 0..2 {
                let mut bad = proof.clone();
                bad.rounds[round][c] += F128::ONE;
                let mut ch = FsLaneChallenger::new(b"shift-test");
                match verify_shift_discharge(w_log, &sigma, target, &bad, &mut ch) {
                    Err(_) => {}
                    Ok(pt) => assert_ne!(
                        mle_eval(&col, &pt),
                        bad.final_value,
                        "mutation {round}/{c} survived"
                    ),
                }
            }
        }
    }

    /// A wiring-shaped relation: two committed columns, one shifted carry,
    /// one witness selector, one internal column — the full generality the
    /// capsule wiring needs.
    #[test]
    fn column_relation_roundtrip_and_claims() {
        let mut rng = Rng(0xC01A);
        let w_log = 4;
        let w = 1usize << w_log;
        let carry = random_col(&mut rng, w);
        let absorb = random_col(&mut rng, w);
        let sel: Vec<F128> = (0..w).map(|_| rng.bit()).collect();
        let internal = random_col(&mut rng, w);
        let committed: Vec<&[F128]> = vec![&carry, &absorb, &sel];
        let internal_cols: Vec<&[F128]> = vec![&internal];
        let columns = RelationColumns {
            committed: &committed,
            internal: &internal_cols,
            fixed: &[],
        };

        // relation(w) = 3·sel(w)·carry(w−1) + 5·(absorb(w)) + 7·internal(w)
        let terms = vec![
            RelationTerm {
                coeff: f128_of_usize(3),
                factors: vec![ColRef::Committed(2), ColRef::CommittedShift(0)],
            },
            RelationTerm {
                coeff: f128_of_usize(5),
                factors: vec![ColRef::Committed(1)],
            },
            RelationTerm {
                coeff: f128_of_usize(7),
                factors: vec![ColRef::Internal(0)],
            },
        ];
        let eq_point: Vec<F128> = (0..w_log).map(|_| rng.f128()).collect();
        let eq = build_eq_table(&eq_point);
        let mut target = F128::ZERO;
        for i in 0..w {
            let shifted = if i == 0 { F128::ZERO } else { carry[i - 1] };
            let val = f128_of_usize(3) * sel[i] * shifted
                + f128_of_usize(5) * absorb[i]
                + f128_of_usize(7) * internal[i];
            target += eq[i] * val;
        }

        let mut ch_p = FsLaneChallenger::new(b"relation-test");
        let (proof, point_p, values_p) =
            prove_column_relation(target, &eq_point, &terms, &columns, &mut ch_p);
        let mut ch_v = FsLaneChallenger::new(b"relation-test");
        let point_v =
            verify_column_relation(w_log, target, &eq_point, &terms, &[], &proof, &mut ch_v)
                .expect("honest relation");
        assert_eq!(point_p, point_v);
        assert_eq!(values_p, proof.final_values);
        assert_eq!(ch_p.sample_f128(), ch_v.sample_f128());

        // Every terminal value is TRUE against its column.
        let refs = distinct_refs(&terms);
        for (r, v) in refs.iter().zip(proof.final_values.iter()) {
            let expected = match r {
                ColRef::Committed(2) => mle_eval(&sel, &point_v),
                ColRef::Committed(1) => mle_eval(&absorb, &point_v),
                ColRef::Internal(0) => mle_eval(&internal, &point_v),
                ColRef::CommittedShift(0) => {
                    let mut shifted = vec![F128::ZERO; w];
                    shifted[1..].copy_from_slice(&carry[..w - 1]);
                    mle_eval(&shifted, &point_v)
                }
                _ => unreachable!(),
            };
            assert_eq!(*v, expected, "terminal claim for {r:?}");
        }

        // Forged target and wire mutations rejected.
        let mut ch = FsLaneChallenger::new(b"relation-test");
        assert!(
            verify_column_relation(
                w_log,
                target + F128::ONE,
                &eq_point,
                &terms,
                &[],
                &proof,
                &mut ch
            )
            .is_err()
        );

        let mut survivors = Vec::new();
        for round in 0..w_log {
            for c in 0..RELATION_DEGREE {
                let mut bad = proof.clone();
                bad.rounds[round][c] += F128::ONE;
                let mut ch = FsLaneChallenger::new(b"relation-test");
                match verify_column_relation(w_log, target, &eq_point, &terms, &[], &bad, &mut ch) {
                    Err(_) => {}
                    Ok(pt) => {
                        // A surviving run must have shifted the derived point
                        // (fresh challenges) — its terminal claims must then
                        // be false against at least one true column.
                        let refs = distinct_refs(&terms);
                        let all_true =
                            refs.iter()
                                .zip(bad.final_values.iter())
                                .all(|(r, v)| match r {
                                    ColRef::Committed(1) => mle_eval(&absorb, &pt) == *v,
                                    ColRef::Committed(2) => mle_eval(&sel, &pt) == *v,
                                    ColRef::Internal(0) => mle_eval(&internal, &pt) == *v,
                                    ColRef::CommittedShift(0) => {
                                        let mut shifted = vec![F128::ZERO; w];
                                        shifted[1..].copy_from_slice(&carry[..w - 1]);
                                        mle_eval(&shifted, &pt) == *v
                                    }
                                    _ => unreachable!(),
                                });
                        if all_true {
                            survivors.push((round, c));
                        }
                    }
                }
            }
        }
        assert!(
            survivors.is_empty(),
            "relation mutation survivors: {survivors:?}"
        );
    }

    /// Weighted-sum discharge with a tensor-product closed-form weight (the
    /// shape of `K_i(z)·eq(right,i)` in the source binding): the sumcheck
    /// reduces `Σ_i w_i·col_i = target` to a plain `col~(point)` claim, and
    /// the terminal check uses `weights~(point)` from the closed form.
    #[test]
    fn weighted_sum_discharge_roundtrip_and_mutations() {
        let mut rng = Rng(0x8E19);
        let w_log = 5;
        let w = 1usize << w_log;
        let col = random_col(&mut rng, w);
        // A rank-1 tensor weight w_i = Π_l f_l(i_l) — the encode-kernel shape.
        let f0: Vec<F128> = (0..w_log).map(|_| rng.f128()).collect();
        let f1: Vec<F128> = (0..w_log).map(|_| rng.f128()).collect();
        let weights: Vec<F128> = (0..w)
            .map(|i| {
                let mut p = F128::ONE;
                for l in 0..w_log {
                    p = p * if (i >> l) & 1 == 1 { f1[l] } else { f0[l] };
                }
                p
            })
            .collect();
        // Closed-form MLE of the tensor weight at a point.
        let weight_eval = |pt: &[F128]| -> F128 {
            let mut p = F128::ONE;
            for l in 0..w_log {
                p = p * (f0[l] * (F128::ONE + pt[l]) + f1[l] * pt[l]);
            }
            p
        };
        let mut target = F128::ZERO;
        for i in 0..w {
            target += weights[i] * col[i];
        }

        let mut ch_p = FsLaneChallenger::new(b"wsum-test");
        let (proof, point_p) = prove_weighted_sum(&col, &weights, target, &mut ch_p);
        let mut ch_v = FsLaneChallenger::new(b"wsum-test");
        let point_v = verify_weighted_sum(w_log, weight_eval, target, &proof, &mut ch_v)
            .expect("honest weighted sum");
        assert_eq!(point_p, point_v);
        assert_eq!(mle_eval(&col, &point_v), proof.final_value);
        // The closed-form weight matches the materialized weight's MLE.
        assert_eq!(weight_eval(&point_v), mle_eval(&weights, &point_v));
        assert_eq!(ch_p.sample_f128(), ch_v.sample_f128());

        // Forged target rejected.
        let mut ch = FsLaneChallenger::new(b"wsum-test");
        assert!(
            verify_weighted_sum(w_log, weight_eval, target + F128::ONE, &proof, &mut ch).is_err()
        );

        // Wire mutations rejected or land on a false plain claim.
        for round in 0..w_log {
            for c in 0..2 {
                let mut bad = proof.clone();
                bad.rounds[round][c] += F128::ONE;
                let mut ch = FsLaneChallenger::new(b"wsum-test");
                match verify_weighted_sum(w_log, weight_eval, target, &bad, &mut ch) {
                    Err(_) => {}
                    Ok(pt) => assert_ne!(
                        mle_eval(&col, &pt),
                        bad.final_value,
                        "mutation {round}/{c} survived"
                    ),
                }
            }
        }
    }

    /// Windowed reads: fan-in-2 tree wiring. A parent-level relation reads
    /// its two children at slots `2w`/`2w+1` of a child column twice its
    /// length; each window's terminal value must equal a PLAIN MLE of the
    /// child at [`window_discharge_point`] (offset bit prepended), with no
    /// shift kernel. Roundtrip + terminal-claim correctness + the
    /// re-indexing identity + a mutation sweep.
    #[test]
    fn window_read_roundtrip_and_claims() {
        let mut rng = Rng(0x5177);
        let w_log = 4; // parent (relation) domain
        let stride_log = 1; // fan-in-2
        let w = 1usize << w_log;
        let child_len = w << stride_log; // 2^(w_log+stride_log)
        let child = random_col(&mut rng, child_len);
        let sel: Vec<F128> = (0..w).map(|_| rng.bit()).collect();
        let committed: Vec<&[F128]> = vec![&sel, &child];
        let columns = RelationColumns {
            committed: &committed,
            internal: &[],
            fixed: &[],
        };

        // relation(w) = sel(w)·child(2w) + 9·child(2w+1)
        let left = ColRef::Window {
            col: 1,
            stride_log,
            offset: 0,
        };
        let right = ColRef::Window {
            col: 1,
            stride_log,
            offset: 1,
        };
        let terms = vec![
            RelationTerm {
                coeff: F128::ONE,
                factors: vec![ColRef::Committed(0), left],
            },
            RelationTerm {
                coeff: f128_of_usize(9),
                factors: vec![right],
            },
        ];
        let eq_point: Vec<F128> = (0..w_log).map(|_| rng.f128()).collect();
        let eq = build_eq_table(&eq_point);
        let mut target = F128::ZERO;
        for i in 0..w {
            let c0 = child[i << stride_log];
            let c1 = child[(i << stride_log) + 1];
            target += eq[i] * (sel[i] * c0 + f128_of_usize(9) * c1);
        }

        let mut ch_p = FsLaneChallenger::new(b"window-test");
        let (proof, point_p, _) =
            prove_column_relation(target, &eq_point, &terms, &columns, &mut ch_p);
        let mut ch_v = FsLaneChallenger::new(b"window-test");
        let point_v =
            verify_column_relation(w_log, target, &eq_point, &terms, &[], &proof, &mut ch_v)
                .expect("honest window relation");
        assert_eq!(point_p, point_v);
        assert_eq!(ch_p.sample_f128(), ch_v.sample_f128());

        // Each terminal claim is a PLAIN MLE of the child at the re-indexed
        // point — offset bit prepended, no kernel. This is the whole point.
        for (r, v) in claimed_refs(&terms).iter().zip(proof.final_values.iter()) {
            let expected = match r {
                ColRef::Committed(0) => mle_eval(&sel, &point_v),
                ColRef::Window {
                    col: 1,
                    stride_log: s,
                    offset,
                } => {
                    let pt = window_discharge_point(*offset, *s, &point_v);
                    mle_eval(&child, &pt)
                }
                _ => unreachable!(),
            };
            assert_eq!(*v, expected, "terminal claim for {r:?}");
        }

        // The re-indexing identity in isolation: folding the windowed table
        // equals the plain child MLE at the prepended point, for BOTH cosets.
        for offset in 0..(1usize << stride_log) {
            let win: Vec<F128> = (0..w).map(|i| child[(i << stride_log) + offset]).collect();
            let pt = window_discharge_point(offset, stride_log, &point_v);
            assert_eq!(
                mle_eval(&win, &point_v),
                mle_eval(&child, &pt),
                "offset {offset}"
            );
        }

        // Forged target and every wire mutation rejected (or land on a false
        // terminal claim after a shifted derived point).
        let mut ch = FsLaneChallenger::new(b"window-test");
        assert!(
            verify_column_relation(
                w_log,
                target + F128::ONE,
                &eq_point,
                &terms,
                &[],
                &proof,
                &mut ch
            )
            .is_err()
        );

        let mut survivors = Vec::new();
        for round in 0..w_log {
            for c in 0..RELATION_DEGREE {
                let mut bad = proof.clone();
                bad.rounds[round][c] += F128::ONE;
                let mut ch = FsLaneChallenger::new(b"window-test");
                match verify_column_relation(w_log, target, &eq_point, &terms, &[], &bad, &mut ch) {
                    Err(_) => {}
                    Ok(pt) => {
                        let all_true = claimed_refs(&terms)
                            .iter()
                            .zip(bad.final_values.iter())
                            .all(|(r, v)| match r {
                                ColRef::Committed(0) => mle_eval(&sel, &pt) == *v,
                                ColRef::Window {
                                    col: 1,
                                    stride_log: s,
                                    offset,
                                } => {
                                    let q = window_discharge_point(*offset, *s, &pt);
                                    mle_eval(&child, &q) == *v
                                }
                                _ => unreachable!(),
                            });
                        if all_true {
                            survivors.push((round, c));
                        }
                    }
                }
            }
        }
        assert!(
            survivors.is_empty(),
            "window mutation survivors: {survivors:?}"
        );
    }

    /// Fixed patterns: a periodic selector gating a 3-factor term. The
    /// verifier evaluates the pattern itself; the folded prover table and
    /// the closed form must agree, and the roundtrip must hold on a domain
    /// LARGER than the pattern period (the tiling case).
    #[test]
    fn fixed_pattern_factors() {
        let mut rng = Rng(0xF17ED);
        let w_log = 5;
        let low_log = 3;
        let w = 1usize << w_log;
        let sel: Vec<F128> = (0..w).map(|_| rng.bit()).collect();
        let a = random_col(&mut rng, w);
        let b = random_col(&mut rng, w);
        // Period-8 pattern: 1 at slots ≡ 0, 3 (mod 8); constant 7 at slot 5.
        let mut table = vec![F128::ZERO; 1 << low_log];
        table[0] = F128::ONE;
        table[3] = F128::ONE;
        table[5] = f128_of_usize(7);
        let fixed = vec![FixedPattern::new(low_log, table.clone())];

        // relation(w) = pat·sel·a + pat·b + a  (a 3-factor term, a gated
        // single factor, and an ungated one).
        let terms = vec![
            RelationTerm {
                coeff: F128::ONE,
                factors: vec![ColRef::Fixed(0), ColRef::Committed(0), ColRef::Committed(1)],
            },
            RelationTerm {
                coeff: F128::ONE,
                factors: vec![ColRef::Fixed(0), ColRef::Committed(2)],
            },
            RelationTerm {
                coeff: F128::ONE,
                factors: vec![ColRef::Committed(1)],
            },
        ];
        let eq_point: Vec<F128> = (0..w_log).map(|_| rng.f128()).collect();
        let eq = build_eq_table(&eq_point);
        let mut target = F128::ZERO;
        for i in 0..w {
            let pat = table[i & ((1 << low_log) - 1)];
            target += eq[i] * (pat * sel[i] * a[i] + pat * b[i] + a[i]);
        }

        let committed: Vec<&[F128]> = vec![&sel, &a, &b];
        let columns = RelationColumns {
            committed: &committed,
            internal: &[],
            fixed: &fixed,
        };
        let mut ch_p = FsLaneChallenger::new(b"fixed-test");
        let (proof, point_p, _) =
            prove_column_relation(target, &eq_point, &terms, &columns, &mut ch_p);
        // Only the three committed refs are claimed.
        assert_eq!(proof.final_values.len(), 3);

        let mut ch_v = FsLaneChallenger::new(b"fixed-test");
        let point_v =
            verify_column_relation(w_log, target, &eq_point, &terms, &fixed, &proof, &mut ch_v)
                .expect("honest fixed-pattern relation");
        assert_eq!(point_p, point_v);
        assert_eq!(ch_p.sample_f128(), ch_v.sample_f128());

        // Closed-form eval == folded periodic table at the derived point.
        let materialized = fixed[0].materialize(w);
        assert_eq!(fixed[0].eval(&point_v), mle_eval(&materialized, &point_v));

        // Terminal claims true against the columns.
        for (r, v) in claimed_refs(&terms).iter().zip(proof.final_values.iter()) {
            let ColRef::Committed(c) = r else {
                unreachable!()
            };
            let col: &[F128] = committed[*c];
            assert_eq!(*v, mle_eval(col, &point_v));
        }

        // A verifier with a WRONG pattern rejects (or derives false claims).
        let mut bad_table = table.clone();
        bad_table[0] += F128::ONE;
        let bad_fixed = vec![FixedPattern::new(low_log, bad_table)];
        let mut ch = FsLaneChallenger::new(b"fixed-test");
        match verify_column_relation(
            w_log, target, &eq_point, &terms, &bad_fixed, &proof, &mut ch,
        ) {
            Err(_) => {}
            Ok(pt) => {
                let all_true = claimed_refs(&terms)
                    .iter()
                    .zip(proof.final_values.iter())
                    .all(|(r, v)| {
                        let ColRef::Committed(c) = r else {
                            unreachable!()
                        };
                        let col: &[F128] = committed[*c];
                        mle_eval(col, &pt) == *v
                    });
                assert!(!all_true, "wrong fixed pattern accepted");
            }
        }
    }

    /// Booleanity as a relation: `0 = Σ eq·(b² + b)` accepts boolean
    /// columns and rejects a non-boolean lane.
    #[test]
    fn booleanity_relation() {
        let mut rng = Rng(0xB001);
        let w_log = 4;
        let w = 1usize << w_log;
        let good: Vec<F128> = (0..w).map(|_| rng.bit()).collect();
        let terms = vec![
            RelationTerm {
                coeff: F128::ONE,
                factors: vec![ColRef::Committed(0), ColRef::Committed(0)],
            },
            RelationTerm {
                coeff: F128::ONE,
                factors: vec![ColRef::Committed(0)],
            },
        ];
        let eq_point: Vec<F128> = (0..w_log).map(|_| rng.f128()).collect();

        let committed: Vec<&[F128]> = vec![&good];
        let columns = RelationColumns {
            committed: &committed,
            internal: &[],
            fixed: &[],
        };
        let mut ch_p = FsLaneChallenger::new(b"bool-test");
        let (proof, _, _) =
            prove_column_relation(F128::ZERO, &eq_point, &terms, &columns, &mut ch_p);
        let mut ch_v = FsLaneChallenger::new(b"bool-test");
        let pt =
            verify_column_relation(w_log, F128::ZERO, &eq_point, &terms, &[], &proof, &mut ch_v)
                .expect("boolean column accepted");
        assert_eq!(proof.final_values[0], mle_eval(&good, &pt));

        // Non-boolean column: the honest prover's target over it is nonzero
        // whp, so proving "= 0" yields a rejected or false-claim run.
        let mut bad_col = good.clone();
        bad_col[3] = rng.f128();
        let committed: Vec<&[F128]> = vec![&bad_col];
        let columns = RelationColumns {
            committed: &committed,
            internal: &[],
            fixed: &[],
        };
        let mut ch_p = FsLaneChallenger::new(b"bool-test");
        let Some((proof, _, _)) = crate::catch_expected_prover_rejection(|| {
            prove_column_relation(F128::ZERO, &eq_point, &terms, &columns, &mut ch_p)
        }) else {
            return;
        };
        let mut ch_v = FsLaneChallenger::new(b"bool-test");
        match verify_column_relation(w_log, F128::ZERO, &eq_point, &terms, &[], &proof, &mut ch_v) {
            Err(_) => {}
            Ok(pt) => {
                assert_ne!(
                    proof.final_values[0],
                    mle_eval(&bad_col, &pt),
                    "non-boolean column produced a consistent zero-check"
                );
            }
        }
    }
}
