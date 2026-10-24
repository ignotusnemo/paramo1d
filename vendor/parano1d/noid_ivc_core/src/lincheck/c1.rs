//! C1 lincheck for the F128-valued History relation.
//!
//! Matrix coefficients and the committed witness stay in GF(2^128), while
//! the Fiat-Shamir points, sumcheck messages, partial witness values, and
//! output claim are represented in GF(2^256).

use super::{LincheckCircuit, SUMCHECK_PAR_THRESHOLD, VerifyError};
use crate::challenger::Challenger;
use crate::field::{F128, F256};
use crate::zerocheck::field_c1::{build_eq_table, lagrange_weights};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct C1QuirkyPoint {
    pub z_skip: F256,
    pub x_inner_rest: Vec<F256>,
    pub x_outer: Vec<F256>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct C1LincheckProof {
    pub rounds: Vec<(F256, F256)>,
    pub z_partial: Vec<F256>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct C1LincheckClaim {
    pub r_inner_skip: F256,
    pub r_inner_rest: Vec<F256>,
    pub w: F256,
}

#[must_use = "a locally-authored C1 lincheck capture must be consumed or deliberately dropped"]
pub struct C1LocallyAuthoredFreshLincheckCapture {
    fresh: crate::matrix_claim::c1::C1FreshLincheckClaim,
}

impl C1LocallyAuthoredFreshLincheckCapture {
    pub fn into_fresh_claim(self) -> crate::matrix_claim::c1::C1FreshLincheckClaim {
        self.fresh
    }
}

fn inner_product(left: &[F256], right: &[F256]) -> F256 {
    assert_eq!(left.len(), right.len());
    left.par_iter()
        .zip(right.par_iter())
        .map(|(&left, &right)| left * right)
        .reduce(|| F256::ZERO, |left, right| left + right)
}

fn round_eval(combination: &[F256], witness: &[F256]) -> (F256, F256) {
    let half = combination.len() / 2;
    assert_eq!(witness.len(), combination.len());
    let (combination_low, combination_high) = combination.split_at(half);
    let (witness_low, witness_high) = witness.split_at(half);
    if half < SUMCHECK_PAR_THRESHOLD {
        let mut at_one = F256::ZERO;
        let mut at_infinity = F256::ZERO;
        for index in 0..half {
            at_one += combination_high[index] * witness_high[index];
            at_infinity += (combination_high[index] + combination_low[index])
                * (witness_high[index] + witness_low[index]);
        }
        return (at_one, at_infinity);
    }
    (0..half)
        .into_par_iter()
        .map(|index| {
            (
                combination_high[index] * witness_high[index],
                (combination_high[index] + combination_low[index])
                    * (witness_high[index] + witness_low[index]),
            )
        })
        .reduce(
            || (F256::ZERO, F256::ZERO),
            |left, right| (left.0 + right.0, left.1 + right.1),
        )
}

fn bind_top(values: &mut Vec<F256>, challenge: F256) {
    let half = values.len() / 2;
    let (low, high) = values.split_at_mut(half);
    let high = &high[..half];
    if half < SUMCHECK_PAR_THRESHOLD {
        for index in 0..half {
            low[index] += challenge * (high[index] + low[index]);
        }
    } else {
        low.par_iter_mut()
            .zip(high.par_iter())
            .for_each(|(low, &high)| *low += challenge * (high + *low));
    }
    values.truncate(half);
}

fn bind_both_and_eval_next(
    combination: &mut Vec<F256>,
    witness: &mut Vec<F256>,
    challenge: F256,
) -> (F256, F256) {
    let length = combination.len();
    assert_eq!(witness.len(), length);
    let half = length / 2;
    let quarter = half / 2;
    assert!(quarter >= 1);

    let (combination_low, combination_high) = combination.split_at_mut(half);
    let (combination_q0, combination_q1) = combination_low.split_at_mut(quarter);
    let (combination_q2, combination_q3) = combination_high.split_at(quarter);
    let (witness_low, witness_high) = witness.split_at_mut(half);
    let (witness_q0, witness_q1) = witness_low.split_at_mut(quarter);
    let (witness_q2, witness_q3) = witness_high.split_at(quarter);

    let (at_one, at_infinity) = if quarter < SUMCHECK_PAR_THRESHOLD {
        let mut at_one = F256::ZERO;
        let mut at_infinity = F256::ZERO;
        for index in 0..quarter {
            let combination_low =
                combination_q0[index] + challenge * (combination_q2[index] + combination_q0[index]);
            let combination_high =
                combination_q1[index] + challenge * (combination_q3[index] + combination_q1[index]);
            let witness_low =
                witness_q0[index] + challenge * (witness_q2[index] + witness_q0[index]);
            let witness_high =
                witness_q1[index] + challenge * (witness_q3[index] + witness_q1[index]);
            combination_q0[index] = combination_low;
            combination_q1[index] = combination_high;
            witness_q0[index] = witness_low;
            witness_q1[index] = witness_high;
            at_one += combination_high * witness_high;
            at_infinity += (combination_high + combination_low) * (witness_high + witness_low);
        }
        (at_one, at_infinity)
    } else {
        combination_q0
            .par_iter_mut()
            .zip(combination_q1.par_iter_mut())
            .zip(combination_q2.par_iter())
            .zip(combination_q3.par_iter())
            .zip(witness_q0.par_iter_mut())
            .zip(witness_q1.par_iter_mut())
            .zip(witness_q2.par_iter())
            .zip(witness_q3.par_iter())
            .map(
                |(
                    (
                        (
                            (
                                (((combination_0, combination_1), combination_2), combination_3),
                                witness_0,
                            ),
                            witness_1,
                        ),
                        witness_2,
                    ),
                    witness_3,
                )| {
                    let combination_low =
                        *combination_0 + challenge * (*combination_2 + *combination_0);
                    let combination_high =
                        *combination_1 + challenge * (*combination_3 + *combination_1);
                    let witness_low = *witness_0 + challenge * (*witness_2 + *witness_0);
                    let witness_high = *witness_1 + challenge * (*witness_3 + *witness_1);
                    *combination_0 = combination_low;
                    *combination_1 = combination_high;
                    *witness_0 = witness_low;
                    *witness_1 = witness_high;
                    (
                        combination_high * witness_high,
                        (combination_high + combination_low) * (witness_high + witness_low),
                    )
                },
            )
            .reduce(
                || (F256::ZERO, F256::ZERO),
                |left, right| (left.0 + right.0, left.1 + right.1),
            )
    };
    combination.truncate(half);
    witness.truncate(half);
    (at_one, at_infinity)
}

#[allow(clippy::too_many_arguments)]
pub fn prove_field<Ch: Challenger>(
    witness: &[F128],
    m: usize,
    k_log: usize,
    k_skip: usize,
    useful_rows: usize,
    circuit: &dyn LincheckCircuit,
    point: &C1QuirkyPoint,
    challenger: &mut Ch,
) -> (C1LincheckProof, C1LincheckClaim) {
    let (proof, claim, capture) = prove_field_inner(
        witness,
        m,
        k_log,
        k_skip,
        useful_rows,
        circuit,
        point,
        None,
        challenger,
    );
    debug_assert!(capture.is_none());
    (proof, claim)
}

#[allow(clippy::too_many_arguments)]
pub fn prove_field_capturing_fresh<Ch: Challenger>(
    witness: &[F128],
    m: usize,
    k_log: usize,
    k_skip: usize,
    useful_rows: usize,
    circuit: &dyn LincheckCircuit,
    point: &C1QuirkyPoint,
    a_value: F256,
    b_value: F256,
    challenger: &mut Ch,
) -> (
    C1LincheckProof,
    C1LincheckClaim,
    C1LocallyAuthoredFreshLincheckCapture,
) {
    let (proof, claim, capture) = prove_field_inner(
        witness,
        m,
        k_log,
        k_skip,
        useful_rows,
        circuit,
        point,
        Some((a_value, b_value)),
        challenger,
    );
    (
        proof,
        claim,
        capture.expect("captured C1 lincheck path returns its claim"),
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_field_inner<Ch: Challenger>(
    witness: &[F128],
    m: usize,
    k_log: usize,
    k_skip: usize,
    useful_rows: usize,
    circuit: &dyn LincheckCircuit,
    point: &C1QuirkyPoint,
    capture_values: Option<(F256, F256)>,
    challenger: &mut Ch,
) -> (
    C1LincheckProof,
    C1LincheckClaim,
    Option<C1LocallyAuthoredFreshLincheckCapture>,
) {
    let width = 1usize << k_log;
    let outer_log = m - k_log;
    assert!(m >= k_log);
    assert!(k_skip <= k_log);
    assert!(useful_rows <= width);
    assert_eq!(witness.len(), 1usize << m);
    let inner_rest_len = k_log - k_skip;
    assert_eq!(circuit.n_cols(), width);
    assert_eq!(point.x_inner_rest.len(), inner_rest_len);
    assert_eq!(point.x_outer.len(), outer_log);

    challenger.observe_label(b"history-lincheck-c1");
    let alpha = challenger.sample_f256();
    let mut captured_running = capture_values.map(|(a, b)| alpha * a + b);
    let mut combination =
        circuit.fold_alpha_batched_quirky_c1(alpha, point.z_skip, &point.x_inner_rest, k_skip);
    let mut beta = None;
    if let Some(column) = circuit.const_pin_col() {
        let sampled = challenger.sample_f256();
        combination[column] += sampled;
        if let Some(running) = captured_running.as_mut() {
            *running += sampled;
        }
        beta = Some(sampled);
    }

    let outer_weights = build_eq_table(&point.x_outer);
    let mut folded_witness = vec![F256::ZERO; width];
    folded_witness[..useful_rows]
        .par_iter_mut()
        .enumerate()
        .for_each(|(inner, output)| {
            *output = outer_weights
                .iter()
                .enumerate()
                .fold(F256::ZERO, |sum, (outer, &weight)| {
                    sum + weight.scale_base(witness[inner + (outer << k_log)])
                });
        });

    let mut rounds = Vec::with_capacity(inner_rest_len);
    let mut sampled = Vec::with_capacity(inner_rest_len);
    if inner_rest_len > 0 {
        let (mut at_one, mut at_infinity) = round_eval(&combination, &folded_witness);
        for round in 0..inner_rest_len {
            challenger.observe_f256(at_one);
            challenger.observe_f256(at_infinity);
            let challenge = challenger.sample_f256();
            rounds.push((at_one, at_infinity));
            sampled.push(challenge);
            if let Some(running) = captured_running.as_mut() {
                let at_zero = *running + at_one;
                let linear = at_zero + at_one + at_infinity;
                *running = at_infinity * challenge * challenge + linear * challenge + at_zero;
            }
            if round + 1 < inner_rest_len {
                (at_one, at_infinity) =
                    bind_both_and_eval_next(&mut combination, &mut folded_witness, challenge);
            } else {
                bind_top(&mut combination, challenge);
                bind_top(&mut folded_witness, challenge);
            }
        }
    }

    let z_partial = folded_witness;
    challenger.observe_f256_slice(&z_partial);
    let r_inner_skip = challenger.sample_f256();
    let weights = lagrange_weights(k_skip, r_inner_skip, 0);
    let w = inner_product(&weights, &z_partial);
    sampled.reverse();

    let capture = captured_running.map(|mut value| {
        debug_assert_eq!(value, inner_product(&combination, &z_partial));
        if let (Some(beta), Some(column)) = (beta, circuit.const_pin_col()) {
            let rest = build_eq_table(&sampled);
            value += beta * z_partial[column & ((1usize << k_skip) - 1)] * rest[column >> k_skip];
        }
        C1LocallyAuthoredFreshLincheckCapture {
            fresh: crate::matrix_claim::c1::C1FreshLincheckClaim {
                alpha,
                z_skip: point.z_skip,
                x_inner_rest: point.x_inner_rest.clone(),
                r_inner_rest: sampled.clone(),
                z_partial: z_partial.clone(),
                value,
            },
        }
    });

    (
        C1LincheckProof { rounds, z_partial },
        C1LincheckClaim {
            r_inner_skip,
            r_inner_rest: sampled,
            w,
        },
        capture,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn verify<Ch: Challenger>(
    m: usize,
    k_log: usize,
    k_skip: usize,
    circuit: &dyn LincheckCircuit,
    point: &C1QuirkyPoint,
    a_value: F256,
    b_value: F256,
    proof: &C1LincheckProof,
    challenger: &mut Ch,
) -> Result<C1LincheckClaim, VerifyError> {
    let width = 1usize << k_log;
    let outer_log = m - k_log;
    if k_skip > k_log {
        return Err(VerifyError::KSkipExceedsKLog { k_skip, k_log });
    }
    let inner_rest_len = k_log - k_skip;
    let skip_size = 1usize << k_skip;
    if point.x_inner_rest.len() != inner_rest_len {
        return Err(VerifyError::BadInnerRestLength {
            which: "x_ab",
            expected: inner_rest_len,
            got: point.x_inner_rest.len(),
        });
    }
    if point.x_outer.len() != outer_log {
        return Err(VerifyError::BadOuterLength {
            which: "x_ab",
            expected: outer_log,
            got: point.x_outer.len(),
        });
    }
    if circuit.n_cols() != width {
        return Err(VerifyError::BadMatrixShape {
            which: "circuit",
            expected: width,
            got_rows: width,
            got_cols: circuit.n_cols(),
        });
    }
    if proof.rounds.len() != inner_rest_len {
        return Err(VerifyError::BadVectorLength {
            which: "rounds",
            expected: inner_rest_len,
            got: proof.rounds.len(),
        });
    }
    if proof.z_partial.len() != skip_size {
        return Err(VerifyError::BadVectorLength {
            which: "z_partial",
            expected: skip_size,
            got: proof.z_partial.len(),
        });
    }

    challenger.observe_label(b"history-lincheck-c1");
    let alpha = challenger.sample_f256();
    let mut combination =
        circuit.fold_alpha_batched_quirky_c1(alpha, point.z_skip, &point.x_inner_rest, k_skip);
    let mut target = alpha * a_value + b_value;
    if let Some(column) = circuit.const_pin_col() {
        let beta = challenger.sample_f256();
        combination[column] += beta;
        target += beta;
    }

    let mut running = target;
    let mut sampled = Vec::with_capacity(inner_rest_len);
    for &(at_one, at_infinity) in &proof.rounds {
        challenger.observe_f256(at_one);
        challenger.observe_f256(at_infinity);
        let challenge = challenger.sample_f256();
        let at_zero = running + at_one;
        let linear = at_zero + at_one + at_infinity;
        running = at_infinity * challenge * challenge + linear * challenge + at_zero;
        bind_top(&mut combination, challenge);
        sampled.push(challenge);
    }

    challenger.observe_f256_slice(&proof.z_partial);
    if running != inner_product(&combination, &proof.z_partial) {
        return Err(VerifyError::ConsistencyFailed {
            which: "sumcheck-final",
        });
    }
    let r_inner_skip = challenger.sample_f256();
    let weights = lagrange_weights(k_skip, r_inner_skip, 0);
    let w = inner_product(&weights, &proof.z_partial);
    sampled.reverse();
    Ok(C1LincheckClaim {
        r_inner_skip,
        r_inner_rest: sampled,
        w,
    })
}

#[allow(clippy::too_many_arguments)]
pub fn verify_deferred<Ch: Challenger>(
    m: usize,
    k_log: usize,
    k_skip: usize,
    const_pin: Option<usize>,
    point: &C1QuirkyPoint,
    a_value: F256,
    b_value: F256,
    proof: &C1LincheckProof,
    challenger: &mut Ch,
) -> Result<
    (
        C1LincheckClaim,
        crate::matrix_claim::c1::C1FreshLincheckClaim,
    ),
    VerifyError,
> {
    if k_skip > k_log {
        return Err(VerifyError::KSkipExceedsKLog { k_skip, k_log });
    }
    let inner_rest_len = k_log - k_skip;
    let skip_size = 1usize << k_skip;
    if point.x_inner_rest.len() != inner_rest_len {
        return Err(VerifyError::BadInnerRestLength {
            which: "x_ab",
            expected: inner_rest_len,
            got: point.x_inner_rest.len(),
        });
    }
    if point.x_outer.len() != m - k_log {
        return Err(VerifyError::BadOuterLength {
            which: "x_ab",
            expected: m - k_log,
            got: point.x_outer.len(),
        });
    }
    if proof.rounds.len() != inner_rest_len {
        return Err(VerifyError::BadVectorLength {
            which: "rounds",
            expected: inner_rest_len,
            got: proof.rounds.len(),
        });
    }
    if proof.z_partial.len() != skip_size {
        return Err(VerifyError::BadVectorLength {
            which: "z_partial",
            expected: skip_size,
            got: proof.z_partial.len(),
        });
    }

    challenger.observe_label(b"history-lincheck-c1");
    let alpha = challenger.sample_f256();
    let mut running = alpha * a_value + b_value;
    let beta = if const_pin.is_some() {
        let beta = challenger.sample_f256();
        running += beta;
        Some(beta)
    } else {
        None
    };
    let mut sampled = Vec::with_capacity(inner_rest_len);
    for &(at_one, at_infinity) in &proof.rounds {
        challenger.observe_f256(at_one);
        challenger.observe_f256(at_infinity);
        let challenge = challenger.sample_f256();
        let at_zero = running + at_one;
        let linear = at_zero + at_one + at_infinity;
        running = at_infinity * challenge * challenge + linear * challenge + at_zero;
        sampled.push(challenge);
    }
    challenger.observe_f256_slice(&proof.z_partial);
    sampled.reverse();

    let mut fresh_value = running;
    if let (Some(beta), Some(column)) = (beta, const_pin) {
        let weights = build_eq_table(&sampled);
        fresh_value += beta * proof.z_partial[column & (skip_size - 1)] * weights[column >> k_skip];
    }
    let fresh = crate::matrix_claim::c1::C1FreshLincheckClaim {
        alpha,
        z_skip: point.z_skip,
        x_inner_rest: point.x_inner_rest.clone(),
        r_inner_rest: sampled.clone(),
        z_partial: proof.z_partial.clone(),
        value: fresh_value,
    };

    let r_inner_skip = challenger.sample_f256();
    let weights = lagrange_weights(k_skip, r_inner_skip, 0);
    let w = inner_product(&weights, &proof.z_partial);
    Ok((
        C1LincheckClaim {
            r_inner_skip,
            r_inner_rest: sampled,
            w,
        },
        fresh,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::FsLaneChallenger;
    use crate::field_r1cs::{FieldRowCircuit, synthetic_satisfiable};

    fn direct_quirky_evaluation(values: &[F128], k_skip: usize, point: &C1QuirkyPoint) -> F256 {
        let skip = lagrange_weights(k_skip, point.z_skip, 0);
        let mut rest_point = point.x_inner_rest.clone();
        rest_point.extend_from_slice(&point.x_outer);
        let rest = build_eq_table(&rest_point);
        values
            .iter()
            .enumerate()
            .fold(F256::ZERO, |sum, (index, &value)| {
                sum + (skip[index & ((1usize << k_skip) - 1)] * rest[index >> k_skip])
                    .scale_base(value)
            })
    }

    #[test]
    fn c1_field_lincheck_roundtrip_and_direct_claim() {
        let m = 9;
        let k_log = 9;
        let k_skip = 6;
        let (relation, witness) = synthetic_satisfiable(m, k_log, 0xC1_11C);
        let a = relation.apply_a(&witness);
        let b = relation.apply_b(&witness);
        let point = C1QuirkyPoint {
            z_skip: F256::from_raw_challenge_lanes(F128::new(1, 2), F128::new(3, 4)),
            x_inner_rest: (0..k_log - k_skip)
                .map(|index| {
                    F256::from_raw_challenge_lanes(
                        F128::new(10 + index as u64, 20 + index as u64),
                        F128::new(30 + index as u64, 40 + index as u64),
                    )
                })
                .collect(),
            x_outer: Vec::new(),
        };
        let a_value = direct_quirky_evaluation(&a, k_skip, &point);
        let b_value = direct_quirky_evaluation(&b, k_skip, &point);

        let mut prover = FsLaneChallenger::new_c1(b"field-c1-lincheck-test");
        let (proof, prover_claim) = prove_field(
            &witness,
            m,
            k_log,
            k_skip,
            relation.useful_rows,
            &relation,
            &point,
            &mut prover,
        );
        let verifier_circuit =
            FieldRowCircuit::new(&relation.a_0, &relation.b_0, relation.const_pin);
        let mut verifier = FsLaneChallenger::new_c1(b"field-c1-lincheck-test");
        let verifier_claim = verify(
            m,
            k_log,
            k_skip,
            &verifier_circuit,
            &point,
            a_value,
            b_value,
            &proof,
            &mut verifier,
        )
        .expect("honest C1 lincheck");

        assert_eq!(prover_claim, verifier_claim);
        let output_point = C1QuirkyPoint {
            z_skip: prover_claim.r_inner_skip,
            x_inner_rest: prover_claim.r_inner_rest.clone(),
            x_outer: point.x_outer.clone(),
        };
        assert_eq!(
            direct_quirky_evaluation(&witness, k_skip, &output_point),
            prover_claim.w
        );
        assert!(
            prover_claim
                .r_inner_rest
                .iter()
                .all(|challenge| !challenge.hi.is_zero())
        );
        assert_eq!(prover.sample_f256(), verifier.sample_f256());
    }

    #[test]
    fn c1_field_lincheck_rejects_message_and_shape_mutations() {
        let m = 8;
        let k_log = 8;
        let k_skip = 6;
        let (relation, witness) = synthetic_satisfiable(m, k_log, 0xC1_BAD11C);
        let a = relation.apply_a(&witness);
        let b = relation.apply_b(&witness);
        let point = C1QuirkyPoint {
            z_skip: F256::from_raw_challenge_lanes(F128::new(1, 0), F128::new(2, 0)),
            x_inner_rest: vec![
                F256::from_raw_challenge_lanes(F128::new(3, 0), F128::new(4, 0));
                k_log - k_skip
            ],
            x_outer: Vec::new(),
        };
        let a_value = direct_quirky_evaluation(&a, k_skip, &point);
        let b_value = direct_quirky_evaluation(&b, k_skip, &point);
        let mut prover = FsLaneChallenger::new_c1(b"field-c1-lincheck-mutate");
        let (proof, _) = prove_field(
            &witness,
            m,
            k_log,
            k_skip,
            relation.useful_rows,
            &relation,
            &point,
            &mut prover,
        );
        let circuit = FieldRowCircuit::new(&relation.a_0, &relation.b_0, relation.const_pin);

        let mut message = proof.clone();
        message.rounds[0].0.hi.lo ^= 1;
        let mut verifier = FsLaneChallenger::new_c1(b"field-c1-lincheck-mutate");
        assert!(
            verify(
                m,
                k_log,
                k_skip,
                &circuit,
                &point,
                a_value,
                b_value,
                &message,
                &mut verifier,
            )
            .is_err()
        );

        let mut truncated = proof;
        truncated.z_partial.pop();
        let mut verifier = FsLaneChallenger::new_c1(b"field-c1-lincheck-mutate");
        assert!(matches!(
            verify(
                m,
                k_log,
                k_skip,
                &circuit,
                &point,
                a_value,
                b_value,
                &truncated,
                &mut verifier,
            ),
            Err(VerifyError::BadVectorLength { .. })
        ));
    }
}
