// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright (C) 2026 Paranoid Zero.

//! Cubic sumcheck and a binary product-tree reduction over C1. These helpers
//! only reduce claims; the caller must authenticate every returned leaf.
//! The caller also binds each input claim/target before entering a reduction.

use super::{Error, F256};
use crate::challenger::Challenger;
use crate::zerocheck::field_c1::build_eq_table;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct CubicProof {
    // Constant, quadratic and cubic coefficients. In characteristic two the
    // linear coefficient is target + quadratic + cubic.
    pub rounds: Vec<[F256; 3]>,
    pub values: [F256; 3],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ProductProof {
    // Root to leaves; layer j has j sumcheck rounds.
    pub layers: Vec<CubicProof>,
}

pub(super) fn eq(left: &[F256], right: &[F256]) -> F256 {
    assert_eq!(left.len(), right.len());
    left.iter()
        .zip(right)
        .fold(F256::ONE, |out, (&a, &b)| out * (F256::ONE + a + b))
}

pub(super) fn evaluate(mut values: Vec<F256>, point: &[F256]) -> F256 {
    assert_eq!(values.len(), 1usize << point.len());
    for &challenge in point {
        fold(&mut values, challenge);
    }
    values[0]
}

fn fold(values: &mut Vec<F256>, challenge: F256) {
    for i in 0..values.len() / 2 {
        values[i] = values[2 * i] + challenge * (values[2 * i] + values[2 * i + 1]);
    }
    values.truncate(values.len() / 2);
}

fn round_value([c0, c2, c3]: [F256; 3], target: F256, challenge: F256) -> F256 {
    let c1 = target + c2 + c3;
    c0 + challenge * (c1 + challenge * (c2 + challenge * c3))
}

pub(super) fn prove_cubic(
    tables: [Vec<F256>; 3],
    target: F256,
    channel: &mut impl Challenger,
) -> (CubicProof, Vec<F256>) {
    let length = tables[0].len();
    assert!(length.is_power_of_two());
    assert!(tables.iter().all(|table| table.len() == length));
    channel.observe_label(b"sparse-c1-cubic-v1");
    continue_cubic(tables, target, Vec::new(), Vec::new(), channel)
}

/// Stream the first round from authenticated sparse entries and materialize
/// only the three half-sized folded tables. Transcript and final claims are
/// byte-for-byte identical to `prove_cubic` on fully expanded input tables.
pub(super) fn prove_cubic_from_fn(
    length: usize,
    value: impl Fn(usize) -> [F256; 3],
    target: F256,
    channel: &mut impl Challenger,
) -> (CubicProof, Vec<F256>) {
    assert!(length.is_power_of_two());
    channel.observe_label(b"sparse-c1-cubic-v1");
    if length == 1 {
        let values = value(0);
        return continue_cubic(
            values.map(|v| vec![v]),
            target,
            Vec::new(),
            Vec::new(),
            channel,
        );
    }
    let message = cubic_round(length, &value);
    channel.observe_f256_slice(&message);
    let challenge = channel.sample_f256();
    let tables = std::array::from_fn(|column| {
        (0..length / 2)
            .map(|index| {
                let low = value(2 * index)[column];
                low + challenge * (low + value(2 * index + 1)[column])
            })
            .collect()
    });
    continue_cubic(
        tables,
        round_value(message, target, challenge),
        vec![message],
        vec![challenge],
        channel,
    )
}

fn cubic_round(length: usize, value: &impl Fn(usize) -> [F256; 3]) -> [F256; 3] {
    let mut message = [F256::ZERO; 3];
    for index in 0..length / 2 {
        let low = value(2 * index);
        let high = value(2 * index + 1);
        let [a, b, c] = low;
        let [da, db, dc] = std::array::from_fn(|j| low[j] + high[j]);
        let ab0 = a * b;
        let ab1 = a * db + da * b;
        let ab2 = da * db;
        message[0] += ab0 * c;
        message[1] += ab1 * dc + ab2 * c;
        message[2] += ab2 * dc;
    }
    message
}

fn continue_cubic(
    mut tables: [Vec<F256>; 3],
    mut target: F256,
    mut rounds: Vec<[F256; 3]>,
    mut point: Vec<F256>,
    channel: &mut impl Challenger,
) -> (CubicProof, Vec<F256>) {
    while tables[0].len() > 1 {
        let message = cubic_round(tables[0].len(), &|index| {
            std::array::from_fn(|j| tables[j][index])
        });
        channel.observe_f256_slice(&message);
        let challenge = channel.sample_f256();
        target = round_value(message, target, challenge);
        for table in &mut tables {
            fold(table, challenge);
        }
        rounds.push(message);
        point.push(challenge);
    }
    let values = tables.map(|table| table[0]);
    debug_assert_eq!(
        target,
        values[0] * values[1] * values[2],
        "prover-side final mismatch"
    );
    channel.observe_f256_slice(&values);
    (CubicProof { rounds, values }, point)
}

pub(super) fn verify_cubic(
    log_len: usize,
    mut target: F256,
    proof: &CubicProof,
    channel: &mut impl Challenger,
) -> Result<Vec<F256>, Error> {
    if proof.rounds.len() != log_len {
        return Err(Error::ProofShape);
    }
    channel.observe_label(b"sparse-c1-cubic-v1");
    let mut point = Vec::with_capacity(log_len);
    for &message in &proof.rounds {
        channel.observe_f256_slice(&message);
        let challenge = channel.sample_f256();
        target = round_value(message, target, challenge);
        point.push(challenge);
    }
    channel.observe_f256_slice(&proof.values);
    if target != proof.values[0] * proof.values[1] * proof.values[2] {
        return Err(Error::Algebra);
    }
    Ok(point)
}

pub(super) fn prove_product(
    leaves: Vec<F256>,
    channel: &mut impl Challenger,
) -> (ProductProof, Vec<F256>, F256) {
    assert!(leaves.len().is_power_of_two());
    channel.observe_label(b"sparse-c1-product-v1");
    let mut tree = vec![leaves];
    while tree.last().expect("leaves").len() > 1 {
        let layer = tree.last().expect("leaves");
        let next = layer
            .chunks_exact(2)
            .map(|pair| pair[0] * pair[1])
            .collect();
        tree.push(next);
    }
    let mut value = tree.pop().expect("root")[0];
    let mut point = Vec::new();
    let mut layers = Vec::with_capacity(tree.len());
    while let Some(child) = tree.pop() {
        let tables = [
            build_eq_table(&point),
            child.iter().step_by(2).copied().collect(),
            child.iter().skip(1).step_by(2).copied().collect(),
        ];
        drop(child);
        let (proof, next_point) = prove_cubic(tables, value, channel);
        let challenge = channel.sample_f256();
        value = proof.values[1] + challenge * (proof.values[1] + proof.values[2]);
        point = Vec::with_capacity(next_point.len() + 1);
        point.push(challenge);
        point.extend(next_point);
        layers.push(proof);
    }
    (ProductProof { layers }, point, value)
}

pub(super) fn verify_product(
    log_len: usize,
    mut value: F256,
    proof: &ProductProof,
    channel: &mut impl Challenger,
) -> Result<(Vec<F256>, F256), Error> {
    if proof.layers.len() != log_len
        || proof
            .layers
            .iter()
            .enumerate()
            .any(|(j, layer)| layer.rounds.len() != j)
    {
        return Err(Error::ProofShape);
    }
    channel.observe_label(b"sparse-c1-product-v1");
    let mut point = Vec::new();
    for (j, layer) in proof.layers.iter().enumerate() {
        let next = verify_cubic(j, value, layer, channel)?;
        if layer.values[0] != eq(&point, &next) {
            return Err(Error::Algebra);
        }
        let challenge = channel.sample_f256();
        value = layer.values[1] + challenge * (layer.values[1] + layer.values[2]);
        point = Vec::with_capacity(j + 1);
        point.push(challenge);
        point.extend(next);
    }
    Ok((point, value))
}
