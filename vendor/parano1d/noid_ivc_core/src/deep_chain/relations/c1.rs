//! Genuine GF(2^256) column relations for the C1 sidecar profile.
//!
//! Committed columns remain over GF(2^128). Their multilinear evaluations,
//! relation coefficients, sumcheck messages, challenges, and terminal claims
//! are all in GF(2^256). This is the extension-field counterpart of the base
//! relation and shift protocols, with an independently domain-separated
//! transcript.

use crate::challenger::Challenger;
use crate::field::{F128, F256};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

use super::{
    ColRef, FixedPattern, MAX_TERM_FACTORS, RELATION_DEGREE, RelationColumns, RelationError,
};

const C1_RELATION_DOMAIN: &[u8] = b"history-deep-chain-relation-c1-v1";
const C1_SHIFT_DOMAIN: &[u8] = b"history-deep-chain-shift-c1-v1";
const RELATION_NODES: usize = RELATION_DEGREE + 1;

/// One extension-field product term.
#[derive(Clone, Debug)]
pub struct C1RelationTerm {
    pub coeff: F256,
    pub factors: Vec<ColRef>,
}

/// Proof wires of one genuine C1 relation sumcheck.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct C1ColumnRelationProof {
    pub rounds: Vec<[F256; RELATION_DEGREE]>,
    pub final_values: Vec<F256>,
}

/// Proof wires of one genuine C1 shift discharge.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct C1ShiftDischargeProof {
    pub rounds: Vec<[F256; 2]>,
    pub final_value: F256,
}

/// Distinct column references in first-occurrence order.
pub fn distinct_refs(terms: &[C1RelationTerm]) -> Vec<ColRef> {
    let mut references = Vec::new();
    for term in terms {
        assert!(
            term.factors.len() <= MAX_TERM_FACTORS,
            "term arity above degree budget"
        );
        for &factor in &term.factors {
            if !references.contains(&factor) {
                references.push(factor);
            }
        }
    }
    references
}

/// Distinct references that produce claims. Fixed patterns are evaluated by
/// the verifier and therefore have no proof-carried terminal value.
pub fn claimed_refs(terms: &[C1RelationTerm]) -> Vec<ColRef> {
    distinct_refs(terms)
        .into_iter()
        .filter(|reference| !matches!(reference, ColRef::Fixed(_)))
        .collect()
}

/// Re-index the terminal point of a window reference.
pub fn window_discharge_point(offset: usize, stride_log: usize, point: &[F256]) -> Vec<F256> {
    assert!(
        offset < (1usize << stride_log),
        "window offset outside stride"
    );
    let mut output = Vec::with_capacity(stride_log + point.len());
    for coordinate in 0..stride_log {
        output.push(if (offset >> coordinate) & 1 == 1 {
            F256::ONE
        } else {
            F256::ZERO
        });
    }
    output.extend_from_slice(point);
    output
}

#[inline]
fn base_constant(value: usize) -> F256 {
    F256::from_base(F128::new(value as u64, 0))
}

fn build_eq_table(point: &[F256]) -> Vec<F256> {
    let mut table = Vec::with_capacity(1usize << point.len());
    table.push(F256::ONE);
    for (coordinate, &challenge) in point.iter().enumerate() {
        let length = 1usize << coordinate;
        table.resize(2 * length, F256::ZERO);
        for index in 0..length {
            let value = table[index];
            let high = value * challenge;
            table[index] = value + high;
            table[index + length] = high;
        }
    }
    table
}

fn eq_eval(left: &[F256], right: &[F256]) -> F256 {
    assert_eq!(left.len(), right.len(), "equality point arity");
    left.iter()
        .zip(right)
        .fold(F256::ONE, |product, (&left, &right)| {
            product * (F256::ONE + left + right)
        })
}

fn fixed_eval(pattern: &FixedPattern, point: &[F256]) -> F256 {
    assert!(point.len() >= pattern.low_log, "fixed pattern point arity");
    let equality = build_eq_table(&point[..pattern.low_log]);
    let mut value = pattern
        .table
        .iter()
        .zip(&equality)
        .fold(F256::ZERO, |sum, (&entry, &weight)| {
            sum + weight.scale_base(entry)
        });
    if let Some((first, bits)) = &pattern.hi_gate {
        assert_eq!(point.len(), first + bits.len(), "gated pattern point arity");
        for (coordinate, bit) in bits.iter().enumerate() {
            let point_value = point[first + coordinate];
            value *= if *bit {
                point_value
            } else {
                F256::ONE + point_value
            };
        }
    }
    value
}

fn encode_reference(reference: ColRef, lanes: &mut Vec<F256>) {
    let lane = |low: usize, high: usize| F256::from_base(F128::new(low as u64, high as u64));
    match reference {
        ColRef::Committed(index) => lanes.push(lane(0, index)),
        ColRef::CommittedShift(index) => lanes.push(lane(1, index)),
        ColRef::Internal(index) => lanes.push(lane(2, index)),
        ColRef::Fixed(index) => lanes.push(lane(3, index)),
        ColRef::CommittedShift2(index) => lanes.push(lane(4, index)),
        ColRef::Window {
            col,
            stride_log,
            offset,
        } => {
            lanes.push(lane(5, col));
            lanes.push(lane(stride_log, offset));
        }
    }
}

fn absorb_relation_header<C: Challenger>(
    channel: &mut C,
    target: F256,
    eq_point: &[F256],
    terms: &[C1RelationTerm],
) {
    channel.observe_label(C1_RELATION_DOMAIN);
    channel.observe_f256(target);
    channel.observe_f256_slice(eq_point);
    let mut structure = vec![base_constant(terms.len())];
    for term in terms {
        structure.push(term.coeff);
        structure.push(base_constant(term.factors.len()));
        for &factor in &term.factors {
            encode_reference(factor, &mut structure);
        }
    }
    channel.observe_f256_slice(&structure);
}

fn relation_basis() -> &'static [[F128; RELATION_NODES]; RELATION_NODES] {
    static BASIS: std::sync::OnceLock<[[F128; RELATION_NODES]; RELATION_NODES]> =
        std::sync::OnceLock::new();
    BASIS.get_or_init(|| {
        let nodes: [F128; RELATION_NODES] = std::array::from_fn(|index| F128::new(index as u64, 0));
        std::array::from_fn(|index| {
            let mut polynomial = [F128::ZERO; RELATION_NODES];
            polynomial[0] = F128::ONE;
            let mut degree = 0usize;
            let mut denominator = F128::ONE;
            for (other, &node) in nodes.iter().enumerate() {
                if other == index {
                    continue;
                }
                denominator *= nodes[index] + node;
                let mut next = [F128::ZERO; RELATION_NODES];
                for coefficient in 0..=degree {
                    next[coefficient + 1] += polynomial[coefficient];
                    next[coefficient] += polynomial[coefficient] * node;
                }
                degree += 1;
                polynomial = next;
            }
            let inverse = crate::deep_chain::f128_inv_pub(denominator);
            std::array::from_fn(|coefficient| polynomial[coefficient] * inverse)
        })
    })
}

fn interpolate_round(evaluations: &[F256; RELATION_NODES]) -> [F256; RELATION_NODES] {
    let basis = relation_basis();
    let mut coefficients = [F256::ZERO; RELATION_NODES];
    for (node, &evaluation) in evaluations.iter().enumerate() {
        for coefficient in 0..RELATION_NODES {
            coefficients[coefficient] += evaluation.scale_base(basis[node][coefficient]);
        }
    }
    coefficients
}

fn reconstruct_round(wire: &[F256; RELATION_DEGREE], claim: F256) -> [F256; RELATION_NODES] {
    let mut linear = claim;
    for &coefficient in &wire[1..] {
        linear += coefficient;
    }
    let mut full = [F256::ZERO; RELATION_NODES];
    full[0] = wire[0];
    full[1] = linear;
    full[2..].copy_from_slice(&wire[1..]);
    full
}

fn horner(coefficients: &[F256; RELATION_NODES], point: F256) -> F256 {
    let mut value = coefficients[RELATION_NODES - 1];
    for &coefficient in coefficients[..RELATION_NODES - 1].iter().rev() {
        value = value * point + coefficient;
    }
    value
}

fn fold_table(table: &mut Vec<F256>, scratch: &mut Vec<F256>, challenge: F256) {
    let half = table.len() / 2;
    scratch.clear();
    scratch.par_extend((0..half).into_par_iter().map(|pair| {
        let low = table[2 * pair];
        low + challenge * (low + table[2 * pair + 1])
    }));
    std::mem::swap(table, scratch);
}

struct CompiledRelationGroup {
    factor: usize,
    terms: Vec<(F256, Vec<usize>)>,
}

/// Factor one high-frequency reference out of every monomial. Relation terms
/// are deliberately gate-heavy, so this removes many duplicate extension
/// multiplications while evaluating the identical polynomial.
struct CompiledRelation {
    constant: F256,
    groups: Vec<CompiledRelationGroup>,
}

impl CompiledRelation {
    fn new(indexed_terms: &[(F256, Vec<usize>)], reference_count: usize) -> Self {
        let mut frequencies = vec![0usize; reference_count];
        for (_, factors) in indexed_terms {
            for &factor in factors {
                frequencies[factor] += 1;
            }
        }
        let mut compiled = Self {
            constant: F256::ZERO,
            groups: Vec::new(),
        };
        for (coefficient, factors) in indexed_terms {
            if factors.is_empty() {
                compiled.constant += *coefficient;
                continue;
            }
            let mut pivot_position = 0usize;
            for position in 1..factors.len() {
                if frequencies[factors[position]] > frequencies[factors[pivot_position]] {
                    pivot_position = position;
                }
            }
            let pivot = factors[pivot_position];
            let mut remaining = Vec::with_capacity(factors.len() - 1);
            remaining.extend_from_slice(&factors[..pivot_position]);
            remaining.extend_from_slice(&factors[pivot_position + 1..]);
            match compiled
                .groups
                .iter_mut()
                .find(|group| group.factor == pivot)
            {
                Some(group) => group.terms.push((*coefficient, remaining)),
                None => compiled.groups.push(CompiledRelationGroup {
                    factor: pivot,
                    terms: vec![(*coefficient, remaining)],
                }),
            }
        }
        compiled
    }

    #[inline]
    fn evaluate_base(&self, values: &[F128]) -> F256 {
        self.groups.iter().fold(self.constant, |sum, group| {
            let inner = group
                .terms
                .iter()
                .fold(F256::ZERO, |inner, (coefficient, factors)| {
                    let product = factors.iter().fold(*coefficient, |product, &factor| {
                        product.scale_base(values[factor])
                    });
                    inner + product
                });
            sum + inner.scale_base(values[group.factor])
        })
    }

    #[inline]
    fn evaluate_wide(&self, values: &[F256]) -> F256 {
        self.groups.iter().fold(self.constant, |sum, group| {
            let inner = group
                .terms
                .iter()
                .fold(F256::ZERO, |inner, (coefficient, factors)| {
                    let product = factors
                        .iter()
                        .fold(*coefficient, |product, &factor| product * values[factor]);
                    inner + product
                });
            sum + values[group.factor] * inner
        })
    }
}

/// Prove one extension-field column relation over base-field columns.
pub fn prove_column_relation<C: Challenger>(
    target: F256,
    eq_point: &[F256],
    terms: &[C1RelationTerm],
    columns: &RelationColumns<'_>,
    channel: &mut C,
) -> (C1ColumnRelationProof, Vec<F256>, Vec<F256>) {
    let timing_started = std::time::Instant::now();
    let w_log = eq_point.len();
    let width = 1usize << w_log;
    let references = distinct_refs(terms);
    let claimed = claimed_refs(terms);
    absorb_relation_header(channel, target, eq_point, terms);

    let base_tables = references
        .par_iter()
        .map(|&reference| columns.resolve(reference, width))
        .collect::<Vec<_>>();
    let indexed_terms = terms
        .iter()
        .map(|term| {
            (
                term.coeff,
                term.factors
                    .iter()
                    .map(|factor| {
                        references
                            .iter()
                            .position(|reference| reference == factor)
                            .expect("distinct C1 relation reference")
                    })
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    let compiled_relation = CompiledRelation::new(&indexed_terms, references.len());

    let mut claim = target;
    let mut rounds = Vec::with_capacity(w_log);
    let mut point = Vec::with_capacity(w_log);
    let mut equality_prefix = F256::ONE;
    let (mut tables, mut equality) = if w_log == 0 {
        (
            base_tables
                .into_par_iter()
                .map(|table| table.into_iter().map(F256::from_base).collect())
                .collect(),
            vec![F256::ONE],
        )
    } else {
        // The committed columns stay in GF(2^128) through the first round.
        // Factoring the first equality coordinate leaves a half-size tail
        // table and avoids materializing any width-sized GF(2^256) column.
        let equality = build_eq_table(&eq_point[1..]);
        let table_count = base_tables.len();
        let nodes = std::array::from_fn::<_, RELATION_NODES, _>(|node| F128::new(node as u64, 0));
        let equality_factors = nodes.map(|node| F256::ONE + eq_point[0] + F256::from_base(node));
        let (evaluations, _, _) = (0..equality.len())
            .into_par_iter()
            .fold(
                || {
                    (
                        [F256::ZERO; RELATION_NODES],
                        Vec::with_capacity(table_count),
                        Vec::with_capacity(table_count),
                    )
                },
                |(mut accumulator, mut bases, mut values), pair| {
                    bases.clear();
                    bases.extend(base_tables.iter().map(|table| {
                        let base = table[2 * pair];
                        (base, base + table[2 * pair + 1])
                    }));
                    for (node_index, slot) in accumulator.iter_mut().enumerate() {
                        let node = nodes[node_index];
                        values.clear();
                        values.extend(bases.iter().map(|&(base, delta)| base + delta * node));
                        let sum = compiled_relation.evaluate_base(&values);
                        *slot += equality[pair] * equality_factors[node_index] * sum;
                    }
                    (accumulator, bases, values)
                },
            )
            .reduce(
                || ([F256::ZERO; RELATION_NODES], Vec::new(), Vec::new()),
                |(mut left, mut left_bases, mut left_values),
                 (right, right_bases, right_values)| {
                    for (left, right) in left.iter_mut().zip(right) {
                        *left += right;
                    }
                    if right_bases.capacity() > left_bases.capacity() {
                        left_bases = right_bases;
                    }
                    if right_values.capacity() > left_values.capacity() {
                        left_values = right_values;
                    }
                    (left, left_bases, left_values)
                },
            );
        let full = interpolate_round(&evaluations);
        debug_assert_eq!(full[0] + horner(&full, F256::ONE), claim);
        let mut wire = [F256::ZERO; RELATION_DEGREE];
        wire[0] = full[0];
        wire[1..].copy_from_slice(&full[2..]);
        channel.observe_f256_slice(&wire);
        let challenge = channel.sample_f256();
        claim = horner(&full, challenge);
        point.push(challenge);
        rounds.push(wire);
        equality_prefix = F256::ONE + eq_point[0] + challenge;
        let tables = base_tables
            .into_par_iter()
            .map(|table| {
                (0..table.len() / 2)
                    .into_par_iter()
                    .map(|pair| {
                        let low = table[2 * pair];
                        F256::from_base(low) + challenge.scale_base(low + table[2 * pair + 1])
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        (tables, equality)
    };
    let mut table_scratch = (0..tables.len()).map(|_| Vec::new()).collect::<Vec<_>>();
    let mut equality_scratch = Vec::new();

    for _ in 1..w_log {
        let half = equality.len() / 2;
        let table_count = tables.len();
        let (mut evaluations, _, _) = (0..half)
            .into_par_iter()
            .fold(
                || {
                    (
                        [F256::ZERO; RELATION_NODES],
                        Vec::with_capacity(table_count),
                        Vec::with_capacity(table_count),
                    )
                },
                |(mut accumulator, mut bases, mut values), pair| {
                    let eq_base = equality[2 * pair];
                    let eq_delta = eq_base + equality[2 * pair + 1];
                    bases.clear();
                    bases.extend(
                        tables
                            .iter()
                            .map(|table| (table[2 * pair], table[2 * pair] + table[2 * pair + 1])),
                    );
                    for (node, slot) in accumulator.iter_mut().enumerate() {
                        let node = F128::new(node as u64, 0);
                        let eq_at_node = eq_base + eq_delta.scale_base(node);
                        values.clear();
                        values.extend(
                            bases
                                .iter()
                                .map(|&(base, delta)| base + delta.scale_base(node)),
                        );
                        let sum = compiled_relation.evaluate_wide(&values);
                        *slot += eq_at_node * sum;
                    }
                    (accumulator, bases, values)
                },
            )
            .reduce(
                || ([F256::ZERO; RELATION_NODES], Vec::new(), Vec::new()),
                |(mut left, mut left_bases, mut left_values),
                 (right, right_bases, right_values)| {
                    for (left, right) in left.iter_mut().zip(right) {
                        *left += right;
                    }
                    if right_bases.capacity() > left_bases.capacity() {
                        left_bases = right_bases;
                    }
                    if right_values.capacity() > left_values.capacity() {
                        left_values = right_values;
                    }
                    (left, left_bases, left_values)
                },
            );
        for evaluation in &mut evaluations {
            *evaluation *= equality_prefix;
        }
        let full = interpolate_round(&evaluations);
        debug_assert_eq!(full[0] + horner(&full, F256::ONE), claim);
        let mut wire = [F256::ZERO; RELATION_DEGREE];
        wire[0] = full[0];
        wire[1..].copy_from_slice(&full[2..]);
        channel.observe_f256_slice(&wire);
        let challenge = channel.sample_f256();
        claim = horner(&full, challenge);
        point.push(challenge);
        rounds.push(wire);
        rayon::join(
            || fold_table(&mut equality, &mut equality_scratch, challenge),
            || {
                tables
                    .par_iter_mut()
                    .zip(&mut table_scratch)
                    .for_each(|(table, scratch)| fold_table(table, scratch, challenge));
            },
        );
    }

    let final_values = references
        .iter()
        .zip(&tables)
        .filter(|(reference, _)| !matches!(reference, ColRef::Fixed(_)))
        .map(|(_, table)| table[0])
        .collect::<Vec<_>>();
    debug_assert_eq!(final_values.len(), claimed.len());
    channel.observe_f256_slice(&final_values);
    debug_assert_eq!(
        equality_prefix
            * equality[0]
            * indexed_terms
                .iter()
                .fold(F256::ZERO, |sum, (coefficient, factors)| {
                    let product = factors
                        .iter()
                        .fold(*coefficient, |product, &factor| product * tables[factor][0]);
                    sum + product
                }),
        claim
    );
    if std::env::var_os("NOIDH_C1_RELATION_TIMING").is_some() {
        eprintln!(
            "[c1-relation] w_log={w_log} terms={} references={} elapsed_ms={:.1}",
            terms.len(),
            references.len(),
            timing_started.elapsed().as_secs_f64() * 1e3
        );
    }
    (
        C1ColumnRelationProof {
            rounds,
            final_values: final_values.clone(),
        },
        point,
        final_values,
    )
}

/// Verify one extension-field column relation.
pub fn verify_column_relation<C: Challenger>(
    w_log: usize,
    target: F256,
    eq_point: &[F256],
    terms: &[C1RelationTerm],
    fixed: &[FixedPattern],
    proof: &C1ColumnRelationProof,
    channel: &mut C,
) -> Result<Vec<F256>, RelationError> {
    let claimed = claimed_refs(terms);
    if eq_point.len() != w_log
        || proof.rounds.len() != w_log
        || proof.final_values.len() != claimed.len()
    {
        return Err(RelationError::Shape);
    }
    absorb_relation_header(channel, target, eq_point, terms);
    let mut claim = target;
    let mut point = Vec::with_capacity(w_log);
    for wire in &proof.rounds {
        channel.observe_f256_slice(wire);
        let full = reconstruct_round(wire, claim);
        let challenge = channel.sample_f256();
        claim = horner(&full, challenge);
        point.push(challenge);
    }
    channel.observe_f256_slice(&proof.final_values);

    let mut relation = F256::ZERO;
    for term in terms {
        let mut product = term.coeff;
        for factor in &term.factors {
            product *= match factor {
                ColRef::Fixed(index) => fixed_eval(&fixed[*index], &point),
                _ => {
                    let index = claimed
                        .iter()
                        .position(|reference| reference == factor)
                        .expect("claimed C1 relation reference");
                    proof.final_values[index]
                }
            };
        }
        relation += product;
    }
    if eq_eval(eq_point, &point) * relation != claim {
        return Err(RelationError::FinalMismatch);
    }
    Ok(point)
}

fn interpolate_degree_two(evaluations: &[F256; 3]) -> [F256; 3] {
    static CONSTANTS: std::sync::OnceLock<(F128, F128)> = std::sync::OnceLock::new();
    let (two, inverse_determinant) = *CONSTANTS.get_or_init(|| {
        let two = F128::new(2, 0);
        let four = two * two;
        (two, crate::deep_chain::f128_inv_pub(four + two))
    });
    let constant = evaluations[0];
    let sum_at_one = evaluations[1] + constant;
    let sum_at_two = evaluations[2] + constant;
    let quadratic = (sum_at_two + sum_at_one.scale_base(two)).scale_base(inverse_determinant);
    let linear = sum_at_one + quadratic;
    [constant, linear, quadratic]
}

fn absorb_shift_header<C: Challenger>(
    channel: &mut C,
    target: F256,
    point: &[F256],
    shift_log: usize,
) {
    channel.observe_label(C1_SHIFT_DOMAIN);
    channel.observe_f256(base_constant(shift_log));
    channel.observe_f256(target);
    channel.observe_f256_slice(point);
}

/// Evaluate the successor kernel over GF(2^256).
pub fn shift_kernel_eval(rho: &[F256], sigma: &[F256]) -> F256 {
    assert_eq!(rho.len(), sigma.len(), "shift point arity");
    let mut suffix = vec![F256::ONE; rho.len() + 1];
    for coordinate in (0..rho.len()).rev() {
        suffix[coordinate] =
            (F256::ONE + rho[coordinate] + sigma[coordinate]) * suffix[coordinate + 1];
    }
    let mut result = F256::ZERO;
    let mut prefix = F256::ONE;
    for coordinate in 0..rho.len() {
        result +=
            prefix * rho[coordinate] * (F256::ONE + sigma[coordinate]) * suffix[coordinate + 1];
        prefix *= sigma[coordinate] * (F256::ONE + rho[coordinate]);
    }
    result
}

/// Evaluate the power-of-two successor kernel over GF(2^256).
pub fn shift_pow2_kernel_eval(shift_log: usize, rho: &[F256], sigma: &[F256]) -> F256 {
    assert_eq!(rho.len(), sigma.len(), "shift point arity");
    assert!(shift_log < rho.len(), "shift below the domain size");
    let low_match = (0..shift_log).fold(F256::ONE, |product, coordinate| {
        product * (F256::ONE + rho[coordinate] + sigma[coordinate])
    });
    low_match * shift_kernel_eval(&rho[shift_log..], &sigma[shift_log..])
}

/// Prove a one-slot C1 shift discharge.
pub fn prove_shift_discharge<C: Challenger>(
    column: &[F128],
    sigma: &[F256],
    target: F256,
    channel: &mut C,
) -> (C1ShiftDischargeProof, Vec<F256>) {
    prove_shift_discharge_pow2(column, sigma, target, 0, channel)
}

/// Prove a power-of-two C1 shift discharge.
pub fn prove_shift_discharge_pow2<C: Challenger>(
    column: &[F128],
    sigma: &[F256],
    target: F256,
    shift_log: usize,
    channel: &mut C,
) -> (C1ShiftDischargeProof, Vec<F256>) {
    let timing_started = std::time::Instant::now();
    let width = column.len();
    assert!(width.is_power_of_two(), "shift column width");
    let w_log = width.trailing_zeros() as usize;
    assert_eq!(sigma.len(), w_log, "shift point arity");
    let shift = 1usize << shift_log;
    assert!(shift < width, "shift below the domain size");
    absorb_shift_header(channel, target, sigma, shift_log);

    let equality = build_eq_table(sigma);
    let mut kernel = vec![F256::ZERO; width];
    kernel[..width - shift].copy_from_slice(&equality[shift..]);
    let mut kernel_scratch = Vec::new();
    let mut claim = target;
    let mut rounds = Vec::with_capacity(w_log);
    let mut point = Vec::with_capacity(w_log);

    // The first round reads the committed column in GF(2^128). Only its
    // half-size fold is promoted into GF(2^256).
    let half = kernel.len() / 2;
    let evaluations = (0..half)
        .into_par_iter()
        .fold(
            || [F256::ZERO; 3],
            |mut accumulator, pair| {
                let kernel_base = kernel[2 * pair];
                let kernel_delta = kernel_base + kernel[2 * pair + 1];
                let column_base = column[2 * pair];
                let column_delta = column_base + column[2 * pair + 1];
                for (node, slot) in accumulator.iter_mut().enumerate() {
                    let node = F128::new(node as u64, 0);
                    *slot += (kernel_base + kernel_delta.scale_base(node))
                        .scale_base(column_base + column_delta * node);
                }
                accumulator
            },
        )
        .reduce(
            || [F256::ZERO; 3],
            |mut left, right| {
                for (left, right) in left.iter_mut().zip(right) {
                    *left += right;
                }
                left
            },
        );
    let full = interpolate_degree_two(&evaluations);
    debug_assert_eq!(full[1] + full[2], claim);
    let wire = [full[0], full[2]];
    channel.observe_f256_slice(&wire);
    let challenge = channel.sample_f256();
    claim = (full[2] * challenge + full[1]) * challenge + full[0];
    point.push(challenge);
    rounds.push(wire);
    let (_, mut column) = rayon::join(
        || fold_table(&mut kernel, &mut kernel_scratch, challenge),
        || {
            (0..column.len() / 2)
                .into_par_iter()
                .map(|pair| {
                    let low = column[2 * pair];
                    F256::from_base(low) + challenge.scale_base(low + column[2 * pair + 1])
                })
                .collect::<Vec<_>>()
        },
    );
    let mut column_scratch = Vec::new();

    for _ in 1..w_log {
        let half = kernel.len() / 2;
        let evaluations = (0..half)
            .into_par_iter()
            .fold(
                || [F256::ZERO; 3],
                |mut accumulator, pair| {
                    let kernel_base = kernel[2 * pair];
                    let kernel_delta = kernel_base + kernel[2 * pair + 1];
                    let column_base = column[2 * pair];
                    let column_delta = column_base + column[2 * pair + 1];
                    for (node, slot) in accumulator.iter_mut().enumerate() {
                        let node = F128::new(node as u64, 0);
                        *slot += (kernel_base + kernel_delta.scale_base(node))
                            * (column_base + column_delta.scale_base(node));
                    }
                    accumulator
                },
            )
            .reduce(
                || [F256::ZERO; 3],
                |mut left, right| {
                    for (left, right) in left.iter_mut().zip(right) {
                        *left += right;
                    }
                    left
                },
            );
        let full = interpolate_degree_two(&evaluations);
        debug_assert_eq!(full[1] + full[2], claim);
        let wire = [full[0], full[2]];
        channel.observe_f256_slice(&wire);
        let challenge = channel.sample_f256();
        claim = (full[2] * challenge + full[1]) * challenge + full[0];
        point.push(challenge);
        rounds.push(wire);
        rayon::join(
            || fold_table(&mut kernel, &mut kernel_scratch, challenge),
            || fold_table(&mut column, &mut column_scratch, challenge),
        );
    }
    let final_value = column[0];
    channel.observe_f256(final_value);
    debug_assert_eq!(kernel[0] * final_value, claim);
    if std::env::var_os("NOIDH_C1_RELATION_TIMING").is_some() {
        eprintln!(
            "[c1-shift] w_log={w_log} shift_log={shift_log} elapsed_ms={:.1}",
            timing_started.elapsed().as_secs_f64() * 1e3
        );
    }
    (
        C1ShiftDischargeProof {
            rounds,
            final_value,
        },
        point,
    )
}

/// Verify a one-slot C1 shift discharge.
pub fn verify_shift_discharge<C: Challenger>(
    w_log: usize,
    sigma: &[F256],
    target: F256,
    proof: &C1ShiftDischargeProof,
    channel: &mut C,
) -> Result<Vec<F256>, RelationError> {
    verify_shift_discharge_pow2(w_log, sigma, target, 0, proof, channel)
}

/// Verify a power-of-two C1 shift discharge.
pub fn verify_shift_discharge_pow2<C: Challenger>(
    w_log: usize,
    sigma: &[F256],
    target: F256,
    shift_log: usize,
    proof: &C1ShiftDischargeProof,
    channel: &mut C,
) -> Result<Vec<F256>, RelationError> {
    if sigma.len() != w_log || proof.rounds.len() != w_log || shift_log >= w_log {
        return Err(RelationError::Shape);
    }
    absorb_shift_header(channel, target, sigma, shift_log);
    let mut claim = target;
    let mut point = Vec::with_capacity(w_log);
    for wire in &proof.rounds {
        channel.observe_f256_slice(wire);
        let linear = claim + wire[1];
        let challenge = channel.sample_f256();
        claim = (wire[1] * challenge + linear) * challenge + wire[0];
        point.push(challenge);
    }
    channel.observe_f256(proof.final_value);
    if shift_pow2_kernel_eval(shift_log, sigma, &point) * proof.final_value != claim {
        return Err(RelationError::FinalMismatch);
    }
    Ok(point)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::{Challenger, FsLaneChallenger};

    struct Rng(u64);

    impl Rng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut value = self.0;
            value = (value ^ (value >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            value = (value ^ (value >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            value ^ (value >> 31)
        }

        fn f128(&mut self) -> F128 {
            F128::new(self.next_u64(), self.next_u64())
        }

        fn f256(&mut self) -> F256 {
            F256::new(self.f128(), self.f128())
        }
    }

    fn mle(column: &[F128], point: &[F256]) -> F256 {
        build_eq_table(point)
            .into_iter()
            .zip(column)
            .fold(F256::ZERO, |sum, (weight, &value)| {
                sum + weight.scale_base(value)
            })
    }

    #[test]
    fn c1_relation_and_shift_roundtrip_and_mutations() {
        let w_log = 4usize;
        let width = 1usize << w_log;
        let mut rng = Rng(0xC1_5E1A_7101);
        let committed_a = (0..width).map(|_| rng.f128()).collect::<Vec<_>>();
        let committed_b = (0..width).map(|_| rng.f128()).collect::<Vec<_>>();
        let internal = (0..width).map(|_| rng.f128()).collect::<Vec<_>>();
        let fixed = FixedPattern::new(
            2,
            vec![F128::ZERO, F128::ONE, F128::new(7, 0), F128::new(9, 0)],
        );
        let committed = vec![committed_a.as_slice(), committed_b.as_slice()];
        let internals = vec![internal.as_slice()];
        let fixed_patterns = vec![fixed];
        let columns = RelationColumns {
            committed: &committed,
            internal: &internals,
            fixed: &fixed_patterns,
        };
        let terms = vec![
            C1RelationTerm {
                coeff: rng.f256(),
                factors: vec![ColRef::Committed(0), ColRef::Internal(0)],
            },
            C1RelationTerm {
                coeff: rng.f256(),
                factors: vec![ColRef::CommittedShift(1), ColRef::Fixed(0)],
            },
        ];
        let eq_point = (0..w_log).map(|_| rng.f256()).collect::<Vec<_>>();
        let eq = build_eq_table(&eq_point);
        let fixed_column = fixed_patterns[0].materialize(width);
        let target = (0..width).fold(F256::ZERO, |sum, index| {
            let shifted = if index == 0 {
                F128::ZERO
            } else {
                committed_b[index - 1]
            };
            let relation = terms[0].coeff
                * F256::from_base(committed_a[index])
                * F256::from_base(internal[index])
                + terms[1].coeff * F256::from_base(shifted) * F256::from_base(fixed_column[index]);
            sum + eq[index] * relation
        });

        let mut prover = FsLaneChallenger::new_c1(b"c1-relation-roundtrip");
        let (proof, point, values) =
            prove_column_relation(target, &eq_point, &terms, &columns, &mut prover);
        let mut verifier = FsLaneChallenger::new_c1(b"c1-relation-roundtrip");
        let verified = verify_column_relation(
            w_log,
            target,
            &eq_point,
            &terms,
            &fixed_patterns,
            &proof,
            &mut verifier,
        )
        .unwrap();
        assert_eq!(point, verified);
        assert_eq!(prover.sample_f256(), verifier.sample_f256());
        let references = claimed_refs(&terms);
        for (reference, &value) in references.iter().zip(&values) {
            let expected = match reference {
                ColRef::Committed(0) => mle(&committed_a, &point),
                ColRef::Internal(0) => mle(&internal, &point),
                ColRef::CommittedShift(1) => {
                    let mut shifted = vec![F128::ZERO; width];
                    shifted[1..].copy_from_slice(&committed_b[..width - 1]);
                    mle(&shifted, &point)
                }
                _ => panic!("unexpected test reference"),
            };
            assert_eq!(value, expected);
        }

        let shifted_target = {
            let mut shifted = vec![F128::ZERO; width];
            shifted[1..].copy_from_slice(&committed_b[..width - 1]);
            mle(&shifted, &point)
        };
        let mut shift_prover = FsLaneChallenger::new_c1(b"c1-shift-roundtrip");
        let (shift_proof, shift_point) =
            prove_shift_discharge(&committed_b, &point, shifted_target, &mut shift_prover);
        let mut shift_verifier = FsLaneChallenger::new_c1(b"c1-shift-roundtrip");
        let verified_shift = verify_shift_discharge(
            w_log,
            &point,
            shifted_target,
            &shift_proof,
            &mut shift_verifier,
        )
        .unwrap();
        assert_eq!(shift_point, verified_shift);
        assert_eq!(shift_proof.final_value, mle(&committed_b, &shift_point));
        assert_eq!(shift_prover.sample_f256(), shift_verifier.sample_f256());

        let mut bad_relation = proof.clone();
        bad_relation.rounds[1][2] += F256::ONE;
        let mut verifier = FsLaneChallenger::new_c1(b"c1-relation-roundtrip");
        assert!(
            verify_column_relation(
                w_log,
                target,
                &eq_point,
                &terms,
                &fixed_patterns,
                &bad_relation,
                &mut verifier,
            )
            .is_err()
        );

        let mut bad_shift = shift_proof.clone();
        bad_shift.final_value += F256::ONE;
        let mut verifier = FsLaneChallenger::new_c1(b"c1-shift-roundtrip");
        assert!(
            verify_shift_discharge(w_log, &point, shifted_target, &bad_shift, &mut verifier)
                .is_err()
        );
    }
}
