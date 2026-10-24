// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

#![allow(clippy::needless_range_loop)]

//! Packing the layered Poseidon2b permutation witness as multilinear
//! extensions.
//!
//! A single permutation's witness has `N_ROWS = N_ROUNDS + 1 = 67`
//! rows and `STATE_SIZE = 4` lanes per row. We pack each column
//! (`state`, `sin`, `x2`, `x3`, `x4`, `sout`) as an MLE over 9
//! variables `(row, lane)` with the lane index in the low 2 bits and
//! the row index in the high 7 bits:
//!
//! ```text
//! idx = (row << 2) | lane,     idx ∈ 0..2^9
//! ```
//!
//! Inactive indices (row ≥ 67) are padded with `Block128::ZERO`.
//! `N_PERM_VARS = 9`. We hardcode this because it is deterministic
//! from the permutation parameters; the sumcheck below takes
//! `n_vars` as a runtime argument so it does not need to know.

use noid_core::Block128;
use noid_poseidon2b::native::permutation::{N_ROUNDS, STATE_SIZE};

use crate::layers::PermLayerWitness;

/// Number of MLE variables per column: `log2(N_ROWS_PADDED *
/// STATE_SIZE) = log2(128 * 4) = 9`. `N_ROWS_PADDED = 128` is the
/// smallest power of two ≥ `N_ROUNDS + 1 = 67`.
pub const N_ROWS_PADDED: usize = 128;
pub const N_PERM_VARS: usize = 9;
pub const N_PERM_CELLS: usize = 1 << N_PERM_VARS; // 512

// Compile-time invariants (hand-rolled const asserts).
const _: [(); 1] = [(); (N_ROWS_PADDED > N_ROUNDS) as usize];
const _: [(); 1] = [(); N_ROWS_PADDED.is_power_of_two() as usize];
const _: [(); 1] = [(); (STATE_SIZE == 4) as usize];
const _: [(); 1] = [(); (N_ROWS_PADDED * STATE_SIZE == N_PERM_CELLS) as usize];

/// Logical column of a `PermLayerWitness`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PermColumn {
    State,
    Sin,
    X2,
    X3,
    X4,
    Sout,
}

/// Pack one column of a layered permutation witness as an MLE over
/// `N_PERM_VARS = 9` variables. Index layout: `(row << 2) | lane`.
pub fn pack_column(witness: &PermLayerWitness, col: PermColumn) -> Vec<Block128> {
    let mut out = vec![Block128::from(0u128); N_PERM_CELLS];
    let rows = witness.state.len();
    debug_assert!(rows <= N_ROWS_PADDED);

    for row in 0..rows {
        for lane in 0..STATE_SIZE {
            let v = match col {
                PermColumn::State => witness.state[row][lane],
                PermColumn::Sin => witness.sin[row][lane],
                PermColumn::X2 => witness.x2[row][lane],
                PermColumn::X3 => witness.x3[row][lane],
                PermColumn::X4 => witness.x4[row][lane],
                PermColumn::Sout => witness.sout[row][lane],
            };
            out[(row << 2) | lane] = v;
        }
    }
    out
}

/// All six columns of a layered permutation witness as MLEs.
#[derive(Debug, Clone)]
pub struct PermMle {
    pub state: Vec<Block128>,
    pub sin: Vec<Block128>,
    pub x2: Vec<Block128>,
    pub x3: Vec<Block128>,
    pub x4: Vec<Block128>,
    pub sout: Vec<Block128>,
}

impl PermMle {
    /// Pack every column of `witness`.
    pub fn from_witness(witness: &PermLayerWitness) -> Self {
        Self {
            state: pack_column(witness, PermColumn::State),
            sin: pack_column(witness, PermColumn::Sin),
            x2: pack_column(witness, PermColumn::X2),
            x3: pack_column(witness, PermColumn::X3),
            x4: pack_column(witness, PermColumn::X4),
            sout: pack_column(witness, PermColumn::Sout),
        }
    }

    /// Get a column by its logical name.
    pub fn column(&self, col: PermColumn) -> &[Block128] {
        match col {
            PermColumn::State => &self.state,
            PermColumn::Sin => &self.sin,
            PermColumn::X2 => &self.x2,
            PermColumn::X3 => &self.x3,
            PermColumn::X4 => &self.x4,
            PermColumn::Sout => &self.sout,
        }
    }
}

/// Build the `(row, lane)` hypercube coordinate vector for an index.
/// Returns 9 Block128 coordinates, lanes first (low 2 bits), rows
/// after (high 7 bits). Useful for tests.
pub fn index_to_point(idx: usize) -> [Block128; N_PERM_VARS] {
    assert!(idx < N_PERM_CELLS);
    let mut out = [Block128::from(0u128); N_PERM_VARS];
    for i in 0..N_PERM_VARS {
        out[i] = if (idx >> i) & 1 == 1 {
            Block128::from(1u128)
        } else {
            Block128::from(0u128)
        };
    }
    out
}
