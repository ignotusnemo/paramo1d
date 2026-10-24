// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.
// Adapted from binius_poseidon2b circuit reference.

//! Native Poseidon2b permutation over GF(2^128).
//!
//! Parameters: state size t=4, x^7 S-box, 8 full rounds + 58 partial rounds.

use std::sync::OnceLock;

use noid_core::{
    hardware::{clmul_gcm, flat_to_tower_u128, square_flat_u128, tower_to_flat_u128},
    Block128,
};
use zeroize::Zeroize;

pub const STATE_SIZE: usize = 4;
pub const SBOX_EXPONENT: usize = 7;
pub const F_ROUNDS: usize = 8;
pub const P_ROUNDS: usize = 58;
pub const N_ROUNDS: usize = F_ROUNDS + P_ROUNDS;

/// Poseidon2b permutation over GF(2^128).
#[derive(Debug, Clone, Copy, Default)]
pub struct Poseidon2bPermutation;

impl Poseidon2bPermutation {
    /// Apply the full permutation to `state` in-place.
    pub fn permute_mut(&self, state: &mut [Block128; STATE_SIZE]) {
        let mut flat = [0u128; STATE_SIZE];
        for i in 0..STATE_SIZE {
            flat[i] = tower_to_flat_u128(state[i].0);
        }
        permute_flat_u128(&mut flat);
        for i in 0..STATE_SIZE {
            state[i] = Block128(flat_to_tower_u128(flat[i]));
        }
        flat.zeroize();
    }
}

/// The Poseidon2b permutation acting directly on a **flat (GCM) basis**
/// state, with no basis conversion at the boundaries.
///
/// [`Poseidon2bPermutation::permute_mut`] is exactly
/// `tower→flat → permute_flat_u128 → flat→tower`: the round schedule always
/// runs in the flat basis internally. Callers whose data already lives in
/// the flat basis (lane-oriented transcripts, the proof-core PCS Merkle
/// primitives) use this entry point and skip both conversions.
pub fn permute_flat_u128(flat: &mut [u128; STATE_SIZE]) {
    #[cfg(target_arch = "x86_64")]
    if crate::batch::avx2_vpclmul_runtime() {
        // SAFETY: gated on runtime AVX2+VPCLMULQDQ detection.
        return unsafe {
            crate::batch_avx2::permute_flat_single_u128(flat, crate::batch::kernel_tables())
        };
    }
    #[cfg(target_arch = "aarch64")]
    if crate::batch::pmull_runtime() {
        // SAFETY: gated on runtime/static PMULL detection.
        return unsafe {
            crate::batch_aarch64::permute_flat_single_u128(flat, crate::batch::kernel_tables())
        };
    }
    #[allow(unreachable_code)]
    let tables = flat_tables();

    // Initial MDS_FULL multiplication.
    apply_mds_full_flat(flat, tables);

    // Full and partial rounds, entirely in flat/GCM basis. This is
    // algebraically identical to the tower schedule but avoids a
    // tower<->flat conversion around every CLMUL multiplication.
    #[allow(clippy::needless_range_loop)]
    for r in 0..N_ROUNDS {
        if !(F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&r) {
            // Full round.
            for i in 0..STATE_SIZE {
                flat[i] ^= tables.rc[i][r];
                flat[i] = sbox_x7_flat_u128(flat[i]);
            }
            apply_mds_full_flat(flat, tables);
        } else {
            // Partial round.
            flat[0] ^= tables.rc[0][r];
            flat[0] = sbox_x7_flat_u128(flat[0]);
            apply_mds_partial_flat(flat, tables);
        }
    }
}

#[derive(Debug)]
struct FlatTables {
    rc: [[u128; N_ROUNDS]; STATE_SIZE],
    mds_full: [[u128; STATE_SIZE]; STATE_SIZE],
    mds_partial: [[u128; STATE_SIZE]; STATE_SIZE],
    mds_full_is_one: [[bool; STATE_SIZE]; STATE_SIZE],
    mds_partial_is_one: [[bool; STATE_SIZE]; STATE_SIZE],
}

fn flat_tables() -> &'static FlatTables {
    static TABLES: OnceLock<FlatTables> = OnceLock::new();
    TABLES.get_or_init(|| {
        let mut rc = [[0u128; N_ROUNDS]; STATE_SIZE];
        for i in 0..STATE_SIZE {
            for r in 0..N_ROUNDS {
                rc[i][r] = tower_to_flat_u128(ROUND_CONSTANTS[i][r]);
            }
        }

        let mut mds_full = [[0u128; STATE_SIZE]; STATE_SIZE];
        let mut mds_partial = [[0u128; STATE_SIZE]; STATE_SIZE];
        let mut mds_full_is_one = [[false; STATE_SIZE]; STATE_SIZE];
        let mut mds_partial_is_one = [[false; STATE_SIZE]; STATE_SIZE];
        for i in 0..STATE_SIZE {
            for j in 0..STATE_SIZE {
                mds_full[i][j] = tower_to_flat_u128(MDS_FULL[i][j]);
                mds_partial[i][j] = tower_to_flat_u128(MDS_PARTIAL[i][j]);
                mds_full_is_one[i][j] = MDS_FULL[i][j] == 1;
                mds_partial_is_one[i][j] = MDS_PARTIAL[i][j] == 1;
            }
        }

        FlatTables {
            rc,
            mds_full,
            mds_partial,
            mds_full_is_one,
            mds_partial_is_one,
        }
    })
}

#[inline(always)]
fn apply_mds_full_flat(state: &mut [u128; STATE_SIZE], tables: &FlatTables) {
    let mut input = *state;
    for (i, state_i) in state.iter_mut().enumerate() {
        let mut out = 0u128;
        for (j, input_j) in input.iter().enumerate() {
            if tables.mds_full_is_one[i][j] {
                out ^= *input_j;
            } else {
                out ^= clmul_gcm(*input_j, tables.mds_full[i][j]);
            }
        }
        *state_i = out;
    }
    input.zeroize();
}

#[inline(always)]
fn apply_mds_partial_flat(state: &mut [u128; STATE_SIZE], tables: &FlatTables) {
    let mut input = *state;
    for (i, state_i) in state.iter_mut().enumerate() {
        let mut out = 0u128;
        for (j, input_j) in input.iter().enumerate() {
            if tables.mds_partial_is_one[i][j] {
                out ^= *input_j;
            } else {
                out ^= clmul_gcm(*input_j, tables.mds_partial[i][j]);
            }
        }
        *state_i = out;
    }
    input.zeroize();
}

/// The x^7 S-box in GF(2^128).
/// x^7 = x * x^2 * x^4.
#[inline(always)]
pub fn sbox_x7(x: Block128) -> Block128 {
    let x_flat = tower_to_flat_u128(x.0);
    Block128(flat_to_tower_u128(sbox_x7_flat_u128(x_flat)))
}

#[inline(always)]
fn sbox_x7_flat_u128(x: u128) -> u128 {
    let x2 = square_flat_u128(x);
    let x4 = square_flat_u128(x2);
    let x6 = clmul_gcm(x, x2);
    clmul_gcm(x6, x4)
}

#[rustfmt::skip]
pub const ROUND_CONSTANTS: [[u128; N_ROUNDS]; STATE_SIZE] = [
    [0x0, 0x1, 0x0, 0x3, 0x7, 0x7, 0x6, 0x6, 0x2, 0x1, 0x7, 0x2, 0x2, 0x3, 0x3, 0x2, 0x6, 0x5, 0x7, 0x5, 0x0, 0x2, 0x2, 0x3, 0x1, 0x5, 0x2, 0x6, 0x1, 0x4, 0x1, 0x0, 0x3, 0x7, 0x2, 0x0, 0x1, 0x2, 0x4, 0x1, 0x0, 0x0, 0x2, 0x5, 0x7, 0x2, 0x0, 0x4, 0x1, 0x5, 0x5, 0x1, 0x2, 0x7, 0x3, 0x1, 0x0, 0x1, 0x3, 0x7, 0x1, 0x6, 0x1, 0x6, 0x6, 0x2, ],
    [0x3, 0x3, 0x0, 0x6, 0x7, 0x1, 0x1, 0x2, 0x7, 0x3, 0x7, 0x5, 0x7, 0x1, 0x7, 0x3, 0x6, 0x1, 0x7, 0x5, 0x5, 0x5, 0x7, 0x1, 0x6, 0x5, 0x1, 0x2, 0x6, 0x3, 0x5, 0x4, 0x4, 0x6, 0x3, 0x2, 0x3, 0x0, 0x4, 0x1, 0x0, 0x6, 0x1, 0x7, 0x6, 0x7, 0x1, 0x6, 0x4, 0x1, 0x4, 0x0, 0x4, 0x3, 0x4, 0x0, 0x3, 0x0, 0x0, 0x7, 0x3, 0x2, 0x3, 0x5, 0x0, 0x2, ],
    [0x6, 0x0, 0x5, 0x3, 0x2, 0x5, 0x6, 0x5, 0x6, 0x7, 0x2, 0x7, 0x6, 0x4, 0x1, 0x0, 0x6, 0x3, 0x2, 0x6, 0x2, 0x1, 0x5, 0x3, 0x1, 0x7, 0x7, 0x6, 0x7, 0x1, 0x1, 0x4, 0x4, 0x4, 0x6, 0x2, 0x5, 0x4, 0x0, 0x3, 0x1, 0x4, 0x1, 0x6, 0x1, 0x6, 0x7, 0x7, 0x6, 0x2, 0x7, 0x3, 0x3, 0x3, 0x0, 0x2, 0x6, 0x4, 0x0, 0x0, 0x0, 0x3, 0x1, 0x4, 0x1, 0x5, ],
    [0x7, 0x1, 0x1, 0x5, 0x1, 0x2, 0x2, 0x7, 0x5, 0x0, 0x5, 0x5, 0x1, 0x4, 0x6, 0x5, 0x2, 0x4, 0x0, 0x1, 0x0, 0x4, 0x6, 0x4, 0x3, 0x7, 0x3, 0x2, 0x4, 0x0, 0x1, 0x6, 0x3, 0x3, 0x2, 0x6, 0x3, 0x4, 0x6, 0x3, 0x2, 0x3, 0x5, 0x1, 0x1, 0x2, 0x4, 0x5, 0x5, 0x6, 0x0, 0x5, 0x5, 0x6, 0x4, 0x1, 0x2, 0x1, 0x5, 0x7, 0x1, 0x3, 0x1, 0x2, 0x2, 0x2, ],
];

#[rustfmt::skip]
pub const MDS_FULL: [[u128; STATE_SIZE]; STATE_SIZE] = [
    [0x5, 0x7, 0x1, 0x3],
    [0x4, 0x6, 0x1, 0x1],
    [0x1, 0x3, 0x5, 0x7],
    [0x1, 0x1, 0x4, 0x6],
];

#[rustfmt::skip]
pub const MDS_PARTIAL: [[u128; STATE_SIZE]; STATE_SIZE] = [
    [0x20, 0x00000001, 0x00000001, 0x00000001],
    [0x00000001, 0x2000, 0x00000001, 0x00000001],
    [0x00000001, 0x00000001, 0x200, 0x00000001],
    [0x00000001, 0x00000001, 0x00000001, 0x800],
];

#[cfg(test)]
mod tests {
    use super::*;
    use noid_core::TowerField;

    #[test]
    fn test_permutation_deterministic() {
        let perm = Poseidon2bPermutation;
        let mut state1 = [Block128::ONE, Block128::ZERO, Block128::ONE, Block128::ZERO];
        let mut state2 = state1;
        perm.permute_mut(&mut state1);
        perm.permute_mut(&mut state2);
        assert_eq!(state1, state2);
    }

    #[test]
    fn test_permutation_changes_state() {
        let perm = Poseidon2bPermutation;
        let mut state = [Block128::ONE, Block128::ZERO, Block128::ONE, Block128::ZERO];
        let original = state;
        perm.permute_mut(&mut state);
        assert_ne!(state, original);
    }

    #[test]
    fn test_sbox_x7_basic() {
        let x = Block128::from(2u8);
        let x7 = sbox_x7(x);
        let manual = tower_sbox_x7_reference(x);
        assert_eq!(x7, manual);
    }

    #[test]
    fn flat_permutation_matches_tower_reference() {
        let perm = Poseidon2bPermutation;
        let fixtures = [
            [
                Block128::ZERO,
                Block128::ZERO,
                Block128::ZERO,
                Block128::ZERO,
            ],
            [Block128::ONE, Block128::ZERO, Block128::ONE, Block128::ZERO],
            [
                Block128(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210),
                Block128(0xffff_0000_ffff_0000_aaaa_5555_aaaa_5555),
                Block128(0x1111_2222_3333_4444_5555_6666_7777_8888),
                Block128(0xdead_beef_cafe_babe_0123_4567_89ab_cdef),
            ],
        ];

        for mut actual in fixtures {
            let mut expected = actual;
            perm.permute_mut(&mut actual);
            permute_mut_tower_reference(&mut expected);
            assert_eq!(actual, expected);
        }
    }

    fn permute_mut_tower_reference(state: &mut [Block128; STATE_SIZE]) {
        apply_mds_full_tower_reference(state);
        for (r, _) in ROUND_CONSTANTS[0].iter().enumerate() {
            if !(F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&r) {
                for i in 0..STATE_SIZE {
                    state[i] += Block128::from(ROUND_CONSTANTS[i][r]);
                }
                for elem in state.iter_mut() {
                    *elem = tower_sbox_x7_reference(*elem);
                }
                apply_mds_full_tower_reference(state);
            } else {
                state[0] += Block128::from(ROUND_CONSTANTS[0][r]);
                state[0] = tower_sbox_x7_reference(state[0]);
                apply_mds_partial_tower_reference(state);
            }
        }
    }

    fn apply_mds_full_tower_reference(state: &mut [Block128; STATE_SIZE]) {
        let input = *state;
        for i in 0..STATE_SIZE {
            let mut out = Block128::ZERO;
            for j in 0..STATE_SIZE {
                if MDS_FULL[i][j] == 1 {
                    out += input[j];
                } else {
                    out += Block128::from(MDS_FULL[i][j]) * input[j];
                }
            }
            state[i] = out;
        }
    }

    fn apply_mds_partial_tower_reference(state: &mut [Block128; STATE_SIZE]) {
        let input = *state;
        for i in 0..STATE_SIZE {
            let mut out = Block128::ZERO;
            for j in 0..STATE_SIZE {
                if MDS_PARTIAL[i][j] == 1 {
                    out += input[j];
                } else {
                    out += Block128::from(MDS_PARTIAL[i][j]) * input[j];
                }
            }
            state[i] = out;
        }
    }

    fn tower_sbox_x7_reference(x: Block128) -> Block128 {
        let x2 = x * x;
        let x4 = x2 * x2;
        let x3 = x2 * x;
        x4 * x3
    }
}
