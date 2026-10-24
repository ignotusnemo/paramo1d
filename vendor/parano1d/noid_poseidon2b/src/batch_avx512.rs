// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! Four-lane register-domain Poseidon2b for AVX-512 + VPCLMULQDQ.
//!
//! A ZMM register holds two adjacent two-lane `PackedBlock128` groups. The
//! logical pack remains unchanged, making the AVX2 and AVX-512 paths byte-
//! and transcript-identical.

#![cfg(target_arch = "x86_64")]

use core::arch::x86_64::*;

use crate::batch::KernelTables;
use crate::native::permutation::{F_ROUNDS, N_ROUNDS, P_ROUNDS, STATE_SIZE};
use noid_core::packed::clmul_avx512::{broadcast_u128, mul_gcm_x4, square_gcm_x4};
use noid_core::packed::PackedBlock128;

#[inline]
#[target_feature(enable = "avx2,avx512f,avx512bw,vpclmulqdq")]
unsafe fn sbox_x7(x: __m512i) -> __m512i {
    let x2 = square_gcm_x4(x);
    let x4 = square_gcm_x4(x2);
    let x6 = mul_gcm_x4(x, x2);
    mul_gcm_x4(x6, x4)
}

#[inline]
#[target_feature(enable = "avx2,avx512f,avx512bw,vpclmulqdq")]
unsafe fn mds_full(state: &mut [__m512i; STATE_SIZE], tables: &KernelTables) {
    let [a, b, c, d] = *state;
    let two = broadcast_u128(tables.mds_full_two);
    let four = broadcast_u128(tables.mds_full_four);
    let a4 = mul_gcm_x4(a, four);
    let b2 = mul_gcm_x4(b, two);
    let b4 = mul_gcm_x4(b, four);
    let c4 = mul_gcm_x4(c, four);
    let d2 = mul_gcm_x4(d, two);
    let d4 = mul_gcm_x4(d, four);

    state[0] = _mm512_xor_si512(
        _mm512_xor_si512(_mm512_xor_si512(a4, a), _mm512_xor_si512(b4, b2)),
        _mm512_xor_si512(_mm512_xor_si512(b, c), _mm512_xor_si512(d2, d)),
    );
    state[1] = _mm512_xor_si512(
        _mm512_xor_si512(a4, _mm512_xor_si512(b4, b2)),
        _mm512_xor_si512(c, d),
    );
    state[2] = _mm512_xor_si512(
        _mm512_xor_si512(a, _mm512_xor_si512(b2, b)),
        _mm512_xor_si512(
            _mm512_xor_si512(c4, c),
            _mm512_xor_si512(d4, _mm512_xor_si512(d2, d)),
        ),
    );
    state[3] = _mm512_xor_si512(
        _mm512_xor_si512(a, b),
        _mm512_xor_si512(c4, _mm512_xor_si512(d4, d2)),
    );
}

#[inline]
#[target_feature(enable = "avx2,avx512f,avx512bw,vpclmulqdq")]
unsafe fn mds_partial(state: &mut [__m512i; STATE_SIZE], tables: &KernelTables) {
    let sum = _mm512_xor_si512(
        _mm512_xor_si512(state[0], state[1]),
        _mm512_xor_si512(state[2], state[3]),
    );
    for i in 0..STATE_SIZE {
        let diagonal = mul_gcm_x4(state[i], broadcast_u128(tables.mds_partial_diag[i]));
        state[i] = _mm512_xor_si512(diagonal, _mm512_xor_si512(sum, state[i]));
    }
}

#[inline]
#[target_feature(enable = "avx2,avx512f,avx512bw,vpclmulqdq")]
unsafe fn permute_groups<const GROUPS: usize>(
    states: &mut [[__m512i; STATE_SIZE]; GROUPS],
    tables: &KernelTables,
) {
    for state in states.iter_mut() {
        mds_full(state, tables);
    }
    for round in 0..N_ROUNDS {
        let full = !((F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&round));
        if full {
            for state in states.iter_mut() {
                for (word, constants) in state.iter_mut().zip(&tables.rc) {
                    *word = sbox_x7(_mm512_xor_si512(*word, broadcast_u128(constants[round])));
                }
            }
            for state in states.iter_mut() {
                mds_full(state, tables);
            }
        } else {
            let rc = broadcast_u128(tables.rc[0][round]);
            for state in states.iter_mut() {
                state[0] = sbox_x7(_mm512_xor_si512(state[0], rc));
            }
            for state in states.iter_mut() {
                mds_partial(state, tables);
            }
        }
    }
}

#[inline]
#[target_feature(enable = "avx2,avx512f,avx512bw,vpclmulqdq")]
unsafe fn join_packs(low: __m256i, high: __m256i) -> __m512i {
    _mm512_inserti64x4::<1>(_mm512_castsi256_si512(low), high)
}

#[inline]
#[target_feature(enable = "avx2,avx512f,avx512bw,vpclmulqdq")]
unsafe fn load_pair(
    low: &[PackedBlock128; STATE_SIZE],
    high: &[PackedBlock128; STATE_SIZE],
) -> [__m512i; STATE_SIZE] {
    std::array::from_fn(|i| {
        join_packs(
            _mm256_loadu_si256((&low[i] as *const PackedBlock128).cast()),
            _mm256_loadu_si256((&high[i] as *const PackedBlock128).cast()),
        )
    })
}

#[inline]
#[target_feature(enable = "avx2,avx512f,avx512bw,vpclmulqdq")]
unsafe fn store_pair(
    words: &[__m512i; STATE_SIZE],
    low: &mut [PackedBlock128; STATE_SIZE],
    high: &mut [PackedBlock128; STATE_SIZE],
) {
    for i in 0..STATE_SIZE {
        _mm256_storeu_si256(
            (&mut low[i] as *mut PackedBlock128).cast(),
            _mm512_castsi512_si256(words[i]),
        );
        _mm256_storeu_si256(
            (&mut high[i] as *mut PackedBlock128).cast(),
            _mm512_extracti64x4_epi64::<1>(words[i]),
        );
    }
}

/// Permute packed states four field elements per ZMM register.
#[target_feature(enable = "avx2,avx512f,avx512bw,vpclmulqdq")]
pub(crate) unsafe fn permute_flat_groups(
    states: &mut [[PackedBlock128; STATE_SIZE]],
    tables: &KernelTables,
) {
    const REGISTER_GROUPS: usize = 4;
    const PACKS_PER_CHUNK: usize = REGISTER_GROUPS * 2;

    unsafe {
        let mut chunks = states.chunks_exact_mut(PACKS_PER_CHUNK);
        for chunk in &mut chunks {
            let mut registers: [[__m512i; STATE_SIZE]; REGISTER_GROUPS] =
                std::array::from_fn(|group| load_pair(&chunk[2 * group], &chunk[2 * group + 1]));
            permute_groups(&mut registers, tables);
            for group in 0..REGISTER_GROUPS {
                let (before_high, at_high) = chunk.split_at_mut(2 * group + 1);
                store_pair(
                    &registers[group],
                    &mut before_high[2 * group],
                    &mut at_high[0],
                );
            }
        }

        let remainder = chunks.into_remainder();
        let pairs = remainder.len() / 2;
        for pair in 0..pairs {
            let (before_high, at_high) = remainder.split_at_mut(2 * pair + 1);
            let mut registers = [load_pair(&before_high[2 * pair], &at_high[0])];
            permute_groups(&mut registers, tables);
            store_pair(&registers[0], &mut before_high[2 * pair], &mut at_high[0]);
        }
        if remainder.len() % 2 == 1 {
            // The final single logical pack remains on the proven AVX2 path.
            crate::batch_avx2::permute_flat_one(remainder.last_mut().unwrap(), tables);
        }
    }
}

#[inline]
#[target_feature(enable = "avx2,avx512f,avx512bw,vpclmulqdq")]
unsafe fn load_four_u128(pointers: [*const u8; 4]) -> __m512i {
    let v0 = _mm_loadu_si128(pointers[0].cast());
    let v1 = _mm_loadu_si128(pointers[1].cast());
    let v2 = _mm_loadu_si128(pointers[2].cast());
    let v3 = _mm_loadu_si128(pointers[3].cast());
    let low = _mm256_inserti128_si256::<1>(_mm256_castsi128_si256(v0), v1);
    let high = _mm256_inserti128_si256::<1>(_mm256_castsi128_si256(v2), v3);
    join_packs(low, high)
}

/// Fixed-length no-pad leaf sponges, sixteen leaves per outer chunk.
#[target_feature(enable = "avx2,avx512f,avx512bw,vpclmulqdq")]
pub(crate) unsafe fn leaf_sponge_flat_no_pad_into(
    iv: [u128; 2],
    data: &[u8],
    leaf_size: usize,
    out: &mut [[u8; 32]],
    tables: &KernelTables,
) {
    const GROUPS: usize = 4;
    const LEAVES_PER_GROUP: usize = 4;
    const LEAVES_PER_CHUNK: usize = GROUPS * LEAVES_PER_GROUP;

    debug_assert!(leaf_size > 0 && leaf_size.is_multiple_of(32));
    debug_assert_eq!(data.len(), leaf_size * out.len());
    debug_assert!(out.len().is_multiple_of(LEAVES_PER_CHUNK));

    unsafe {
        let zero = _mm512_setzero_si512();
        let iv0 = broadcast_u128(iv[0]);
        let iv1 = broadcast_u128(iv[1]);

        for leaf_base in (0..out.len()).step_by(LEAVES_PER_CHUNK) {
            let mut states: [[__m512i; STATE_SIZE]; GROUPS] = [[zero, zero, iv0, iv1]; GROUPS];
            for block in (0..leaf_size).step_by(32) {
                for (group, state) in states.iter_mut().enumerate() {
                    let first = leaf_base + group * LEAVES_PER_GROUP;
                    let pointers = std::array::from_fn(|lane| {
                        data.as_ptr().add((first + lane) * leaf_size + block)
                    });
                    state[0] = _mm512_xor_si512(state[0], load_four_u128(pointers));
                    state[1] = _mm512_xor_si512(
                        state[1],
                        load_four_u128(pointers.map(|pointer| pointer.add(16))),
                    );
                }
                permute_groups(&mut states, tables);
            }

            for (group, state) in states.iter().enumerate() {
                let word0_low = _mm512_castsi512_si256(state[0]);
                let word0_high = _mm512_extracti64x4_epi64::<1>(state[0]);
                let word1_low = _mm512_castsi512_si256(state[1]);
                let word1_high = _mm512_extracti64x4_epi64::<1>(state[1]);
                let digests = [
                    _mm256_permute2x128_si256::<0x20>(word0_low, word1_low),
                    _mm256_permute2x128_si256::<0x31>(word0_low, word1_low),
                    _mm256_permute2x128_si256::<0x20>(word0_high, word1_high),
                    _mm256_permute2x128_si256::<0x31>(word0_high, word1_high),
                ];
                let base = leaf_base + group * LEAVES_PER_GROUP;
                for (lane, digest) in digests.into_iter().enumerate() {
                    _mm256_storeu_si256(out.as_mut_ptr().add(base + lane).cast(), digest);
                }
            }
        }
    }
}
