// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Witness-routed rearrangeable permutation network.
//!
//! A recursive Beneš construction realizes any power-of-two permutation with
//! `N log2(N)` two-way switches. Every switch bit is boolean-constrained and
//! every payload lane passes through a conditional swap, so the output is
//! provably a permutation of the input. Callers separately constrain the
//! desired output order; the host-derived routing bits are only a satisfying
//! witness and are never trusted for soundness.

use std::collections::VecDeque;

use super::{mul, FieldR1csBuilder, LinExpr};

enum BenesConfig {
    Leaf,
    Switch(bool),
    Node {
        first: Vec<bool>,
        upper: Box<BenesConfig>,
        lower: Box<BenesConfig>,
        last: Vec<bool>,
    },
}

/// Route row `input` to `permutation[input]`.
///
/// Rows must have a common lane width and their count must be a power of two.
/// The matrix shape depends only on those dimensions, not on the permutation.
pub fn route_permutation_network(
    b: &mut FieldR1csBuilder,
    rows: Vec<Vec<LinExpr>>,
    permutation: &[usize],
) -> Vec<Vec<LinExpr>> {
    assert!(!rows.is_empty());
    assert!(rows.len().is_power_of_two());
    assert_eq!(rows.len(), permutation.len());
    let width = rows[0].len();
    assert!(width > 0);
    assert!(rows.iter().all(|row| row.len() == width));
    let config = route_config(permutation);
    apply_config(b, rows, &config)
}

fn route_config(permutation: &[usize]) -> BenesConfig {
    let n = permutation.len();
    assert!(n.is_power_of_two());
    let mut seen = vec![false; n];
    for &output in permutation {
        assert!(output < n, "permutation output out of range");
        assert!(!seen[output], "permutation output repeated");
        seen[output] = true;
    }
    if n == 1 {
        return BenesConfig::Leaf;
    }
    if n == 2 {
        return BenesConfig::Switch(permutation[0] == 1);
    }

    // Each input pair and output pair has degree two. Alternating a two-color
    // assignment around every cycle sends exactly one edge from each pair to
    // each recursive half-network.
    let half = n / 2;
    let mut input_edges = vec![[usize::MAX; 2]; half];
    let mut output_edges = vec![[usize::MAX; 2]; half];
    for input in 0..n {
        let input_pair = input / 2;
        input_edges[input_pair][input & 1] = input;
        let output = permutation[input];
        let output_pair = output / 2;
        output_edges[output_pair][output & 1] = input;
    }
    let mut colors = vec![None; n];
    for start in 0..n {
        if colors[start].is_some() {
            continue;
        }
        colors[start] = Some(false);
        let mut queue = VecDeque::from([start]);
        while let Some(edge) = queue.pop_front() {
            let color = colors[edge].expect("queued edge is colored");
            for adjacent in [input_edges[edge / 2], output_edges[permutation[edge] / 2]] {
                let other = if adjacent[0] == edge {
                    adjacent[1]
                } else {
                    adjacent[0]
                };
                match colors[other] {
                    Some(existing) => assert_ne!(existing, color, "routing cycle coloring"),
                    None => {
                        colors[other] = Some(!color);
                        queue.push_back(other);
                    }
                }
            }
        }
    }
    let colors: Vec<bool> = colors
        .into_iter()
        .map(|color| color.expect("every routing edge colored"))
        .collect();

    let first: Vec<bool> = (0..half).map(|pair| colors[2 * pair]).collect();
    let mut inverse = vec![usize::MAX; n];
    for (input, &output) in permutation.iter().enumerate() {
        inverse[output] = input;
    }
    let last: Vec<bool> = (0..half).map(|pair| colors[inverse[2 * pair]]).collect();

    let mut upper_perm = vec![usize::MAX; half];
    let mut lower_perm = vec![usize::MAX; half];
    for input in 0..n {
        let target = permutation[input] / 2;
        let sub = if colors[input] {
            &mut lower_perm
        } else {
            &mut upper_perm
        };
        let at = input / 2;
        assert_eq!(sub[at], usize::MAX, "one edge per input pair/color");
        sub[at] = target;
    }

    BenesConfig::Node {
        first,
        upper: Box::new(route_config(&upper_perm)),
        lower: Box::new(route_config(&lower_perm)),
        last,
    }
}

fn apply_config(
    b: &mut FieldR1csBuilder,
    rows: Vec<Vec<LinExpr>>,
    config: &BenesConfig,
) -> Vec<Vec<LinExpr>> {
    match config {
        BenesConfig::Leaf => {
            assert_eq!(rows.len(), 1);
            rows
        }
        BenesConfig::Switch(switch) => {
            assert_eq!(rows.len(), 2);
            let (left, right) = conditional_switch(b, &rows[0], &rows[1], *switch);
            vec![left, right]
        }
        BenesConfig::Node {
            first,
            upper,
            lower,
            last,
        } => {
            let half = rows.len() / 2;
            assert_eq!(first.len(), half);
            assert_eq!(last.len(), half);
            let mut upper_rows = Vec::with_capacity(half);
            let mut lower_rows = Vec::with_capacity(half);
            for (pair, switch) in rows.chunks_exact(2).zip(first.iter().copied()) {
                let (up, down) = conditional_switch(b, &pair[0], &pair[1], switch);
                upper_rows.push(up);
                lower_rows.push(down);
            }
            let upper_rows = apply_config(b, upper_rows, upper);
            let lower_rows = apply_config(b, lower_rows, lower);
            let mut output = Vec::with_capacity(rows.len());
            for ((up, down), switch) in upper_rows
                .into_iter()
                .zip(lower_rows)
                .zip(last.iter().copied())
            {
                let (even, odd) = conditional_switch(b, &up, &down, switch);
                output.push(even);
                output.push(odd);
            }
            output
        }
    }
}

fn conditional_switch(
    b: &mut FieldR1csBuilder,
    left: &[LinExpr],
    right: &[LinExpr],
    native_switch: bool,
) -> (Vec<LinExpr>, Vec<LinExpr>) {
    assert_eq!(left.len(), right.len());
    let switch = LinExpr::from_wire(b.alloc_bool(native_switch));
    left.iter()
        .zip(right)
        .map(|(a, c)| {
            let delta = a.add(c);
            let selected_delta = mul(b, &switch, &delta);
            (a.add(&selected_delta), c.add(&selected_delta))
        })
        .unzip()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::trace::{alloc_block, flat_of, F128};
    use noid_core::Block128;

    fn next_permutation(values: &mut [usize]) -> bool {
        let Some(pivot) = (0..values.len().saturating_sub(1))
            .rev()
            .find(|&i| values[i] < values[i + 1])
        else {
            return false;
        };
        let swap = (pivot + 1..values.len())
            .rev()
            .find(|&i| values[pivot] < values[i])
            .unwrap();
        values.swap(pivot, swap);
        values[pivot + 1..].reverse();
        true
    }

    fn build(
        permutation: &[usize],
    ) -> (noid_ivc_core::field_r1cs::FieldR1cs, Vec<F128>, Vec<F128>) {
        let mut b = FieldR1csBuilder::new();
        let rows: Vec<_> = (0..permutation.len())
            .map(|input| vec![alloc_block(&mut b, Block128::from(input as u128))])
            .collect();
        let output = route_permutation_network(&mut b, rows, permutation);
        let output_values = output.iter().map(|row| row[0].eval(b.values())).collect();
        let (r1cs, witness) = b.build();
        (r1cs, witness, output_values)
    }

    #[test]
    fn routes_every_four_row_permutation() {
        let mut permutation = vec![0, 1, 2, 3];
        loop {
            let (r1cs, witness, output) = build(&permutation);
            assert!(r1cs.satisfies(&witness), "permutation {permutation:?}");
            let mut inverse = vec![0usize; permutation.len()];
            for (input, &at) in permutation.iter().enumerate() {
                inverse[at] = input;
            }
            assert_eq!(
                output,
                inverse
                    .into_iter()
                    .map(|value| flat_of(Block128::from(value as u128)))
                    .collect::<Vec<_>>()
            );
            if !next_permutation(&mut permutation) {
                break;
            }
        }
    }

    #[test]
    fn routing_values_do_not_change_the_matrix() {
        let (identity, identity_witness, _) = build(&[0, 1, 2, 3, 4, 5, 6, 7]);
        let (reverse, reverse_witness, _) = build(&[7, 6, 5, 4, 3, 2, 1, 0]);
        assert!(identity.satisfies(&identity_witness));
        assert!(reverse.satisfies(&reverse_witness));
        assert_eq!(identity.statement_digest(), reverse.statement_digest());
        assert_eq!(identity.useful_rows, reverse.useful_rows);
        assert_eq!(flat_of(Block128::from(1u128)), F128::ONE);
    }
}
