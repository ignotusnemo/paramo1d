// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! Register-domain Poseidon2b permutation kernel for AVX2 + VPCLMULQDQ.
//!
//! The generic packed round loop bounces every intermediate through
//! `PackedBlock128`'s `[u128; 2]` representation, forcing constant
//! vector↔general-register transitions between the CLMUL multiplies and the
//! XOR gluing. This kernel instead keeps the whole 66-round schedule in
//! `__m256i` locals: states load once at the absorb boundary and store once
//! at the squeeze boundary. It also processes several INDEPENDENT state
//! groups per call — one permutation is a serial multiply chain, so a lone
//! group leaves the carry-less-multiply unit idle waiting on latency;
//! interleaved groups convert the batch kernels from latency-bound to
//! throughput-bound.
//!
//! Bit-identical to `native::permutation::permute_flat_u128` per lane.

#![cfg(target_arch = "x86_64")]

use core::arch::x86_64::*;

use crate::batch::KernelTables;
use crate::native::permutation::{F_ROUNDS, N_ROUNDS, P_ROUNDS, STATE_SIZE};
use noid_core::packed::clmul_avx2::{mul_gcm_x2, square_gcm_clmul_x2};
use noid_core::packed::PackedBlock128;

#[inline]
#[target_feature(enable = "avx2,vpclmulqdq")]
unsafe fn bcast(c: u128) -> __m256i {
    _mm256_broadcastsi128_si256(core::mem::transmute::<u128, __m128i>(c))
}

#[inline]
#[target_feature(enable = "avx2,vpclmulqdq")]
unsafe fn sbox_x7(x: __m256i) -> __m256i {
    let x2 = square_gcm_clmul_x2(x);
    let x4 = square_gcm_clmul_x2(x2);
    let x6 = mul_gcm_x2(x, x2);
    mul_gcm_x2(x6, x4)
}

/// Full-round MDS: generic 4×4 with the is-one entries as bare XORs.
#[inline]
#[target_feature(enable = "avx2,vpclmulqdq")]
unsafe fn mds_full(s: &mut [__m256i; STATE_SIZE], t: &KernelTables) {
    // M = [5 7 1 3; 4 6 1 1; 1 3 5 7; 1 1 4 6]. In characteristic two,
    // 3x=2x+x, 5x=4x+x, 6x=4x+2x, 7x=4x+2x+x. Six products by 2/4 therefore
    // replace the generic ten non-identity products without changing the
    // linear map. This MDS runs once initially and after every full round.
    let [a, b, c, d] = *s;
    let two = bcast(t.mds_full_two);
    let four = bcast(t.mds_full_four);
    let a4 = mul_gcm_x2(a, four);
    let b2 = mul_gcm_x2(b, two);
    let b4 = mul_gcm_x2(b, four);
    let c4 = mul_gcm_x2(c, four);
    let d2 = mul_gcm_x2(d, two);
    let d4 = mul_gcm_x2(d, four);

    s[0] = _mm256_xor_si256(
        _mm256_xor_si256(_mm256_xor_si256(a4, a), _mm256_xor_si256(b4, b2)),
        _mm256_xor_si256(_mm256_xor_si256(b, c), _mm256_xor_si256(d2, d)),
    );
    s[1] = _mm256_xor_si256(
        _mm256_xor_si256(a4, _mm256_xor_si256(b4, b2)),
        _mm256_xor_si256(c, d),
    );
    s[2] = _mm256_xor_si256(
        _mm256_xor_si256(a, _mm256_xor_si256(b2, b)),
        _mm256_xor_si256(
            _mm256_xor_si256(c4, c),
            _mm256_xor_si256(d4, _mm256_xor_si256(d2, d)),
        ),
    );
    s[3] = _mm256_xor_si256(
        _mm256_xor_si256(a, b),
        _mm256_xor_si256(c4, _mm256_xor_si256(d4, d2)),
    );
}

/// Partial-round MDS: diagonal entries `c_i`, all off-diagonals 1, so
/// `out_i = c_i·s_i + (S + s_i)` with `S` the XOR of the whole state —
/// 4 multiplies and one shared sum instead of a dense row pass.
#[inline]
#[target_feature(enable = "avx2,vpclmulqdq")]
unsafe fn mds_partial(s: &mut [__m256i; STATE_SIZE], t: &KernelTables) {
    let sum = _mm256_xor_si256(_mm256_xor_si256(s[0], s[1]), _mm256_xor_si256(s[2], s[3]));
    for i in 0..STATE_SIZE {
        let diag = mul_gcm_x2(s[i], bcast(t.mds_partial_diag[i]));
        s[i] = _mm256_xor_si256(diag, _mm256_xor_si256(sum, s[i]));
    }
}

/// The full Poseidon2b schedule over `G` independent state groups held in
/// `__m256i` registers (each group = PACKED_LANES independent permutations).
#[inline]
#[target_feature(enable = "avx2,vpclmulqdq")]
unsafe fn permute_groups<const G: usize>(st: &mut [[__m256i; STATE_SIZE]; G], t: &KernelTables) {
    for g in 0..G {
        mds_full(&mut st[g], t);
    }
    for r in 0..N_ROUNDS {
        let is_full = !((F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&r));
        if is_full {
            for g in 0..G {
                for i in 0..STATE_SIZE {
                    let x = _mm256_xor_si256(st[g][i], bcast(t.rc[i][r]));
                    st[g][i] = sbox_x7(x);
                }
            }
            for g in 0..G {
                mds_full(&mut st[g], t);
            }
        } else {
            let rc0 = bcast(t.rc[0][r]);
            for g in 0..G {
                st[g][0] = sbox_x7(_mm256_xor_si256(st[g][0], rc0));
            }
            for g in 0..G {
                mds_partial(&mut st[g], t);
            }
        }
    }
}

#[inline]
#[target_feature(enable = "avx2,vpclmulqdq")]
unsafe fn load_group(s: &[PackedBlock128; STATE_SIZE]) -> [__m256i; STATE_SIZE] {
    std::array::from_fn(|i| _mm256_loadu_si256(&s[i] as *const PackedBlock128 as *const __m256i))
}

#[inline]
#[target_feature(enable = "avx2,vpclmulqdq")]
unsafe fn store_group(v: &[__m256i; STATE_SIZE], s: &mut [PackedBlock128; STATE_SIZE]) {
    for i in 0..STATE_SIZE {
        _mm256_storeu_si256(&mut s[i] as *mut PackedBlock128 as *mut __m256i, v[i]);
    }
}

/// Permute `states.len()` independent packed groups: G-wide register-domain
/// chunks first, then a single-group pass over the remainder.
///
/// # Safety
/// The CPU must support AVX2 and VPCLMULQDQ — callers gate on
/// `is_x86_feature_detected!` (or a statically-enabled build).
#[target_feature(enable = "avx2,vpclmulqdq")]
pub(crate) unsafe fn permute_flat_groups(
    states: &mut [[PackedBlock128; STATE_SIZE]],
    t: &KernelTables,
) {
    /// Groups per register-domain chunk. 4 groups × 4 state words = 16 ymm
    /// values plus multiply temporaries: the working set spills a little,
    /// but the interleaving keeps the CLMUL port saturated, which measures
    /// faster than any narrower arrangement.
    const G: usize = 4;
    unsafe {
        let mut chunks = states.chunks_exact_mut(G);
        for chunk in &mut chunks {
            let mut regs: [[__m256i; STATE_SIZE]; G] =
                std::array::from_fn(|g| load_group(&chunk[g]));
            permute_groups(&mut regs, t);
            for g in 0..G {
                store_group(&regs[g], &mut chunk[g]);
            }
        }
        for s in chunks.into_remainder() {
            let mut regs = [load_group(s)];
            permute_groups(&mut regs, t);
            store_group(&regs[0], s);
        }
    }
}

/// Single-group register-domain permutation (the `packed_poseidon2b_permute_flat`
/// fast path).
///
/// # Safety
/// See [`permute_flat_groups`].
#[target_feature(enable = "avx2,vpclmulqdq")]
pub(crate) unsafe fn permute_flat_one(states: &mut [PackedBlock128; STATE_SIZE], t: &KernelTables) {
    unsafe {
        let mut regs = [load_group(states)];
        permute_groups(&mut regs, t);
        store_group(&regs[0], states);
    }
}

/// Fixed-length, no-pad leaf sponges over leaf-major bytes.
///
/// The generic batch path has to materialize every packed state around each
/// rate block because the permutation entry point owns only one invocation.
/// A PCS leaf is a long dependent sponge chain (512 bytes / 16 invocations in
/// the production tree), so those boundaries repeatedly spill and reload all
/// 16 live YMM state registers.  Keep four packed groups (eight leaves) in
/// the register-domain kernel for the complete absorb schedule instead.
///
/// This is only an execution shortcut: the initial state, byte-to-lane
/// mapping, per-block XOR, permutation schedule and final flat-basis bytes are
/// identical to `Poseidon2bFlatSponge::finalize_no_pad`.
///
/// # Safety
/// The CPU must support AVX2 and VPCLMULQDQ. `data.len()` must equal
/// `leaf_size * out.len()`, `leaf_size` must be a positive multiple of 32,
/// and the leaf count must be a multiple of eight. Callers check all four.
#[target_feature(enable = "avx2,vpclmulqdq")]
pub(crate) unsafe fn leaf_sponge_flat_no_pad_into(
    iv: [u128; 2],
    data: &[u8],
    leaf_size: usize,
    out: &mut [[u8; 32]],
    t: &KernelTables,
) {
    const G: usize = 4;
    const LEAVES_PER_CHUNK: usize = G * 2;

    debug_assert!(leaf_size > 0 && leaf_size.is_multiple_of(32));
    debug_assert_eq!(data.len(), leaf_size * out.len());
    debug_assert!(out.len().is_multiple_of(LEAVES_PER_CHUNK));

    unsafe {
        let zero = _mm256_setzero_si256();
        let iv_hi = bcast(iv[0]);
        let iv_lo = bcast(iv[1]);

        for leaf_base in (0..out.len()).step_by(LEAVES_PER_CHUNK) {
            let mut states: [[__m256i; STATE_SIZE]; G] = [[zero, zero, iv_hi, iv_lo]; G];

            for block_offset in (0..leaf_size).step_by(32) {
                for g in 0..G {
                    let leaf0 = leaf_base + 2 * g;
                    let leaf1 = leaf0 + 1;
                    let p0 = data.as_ptr().add(leaf0 * leaf_size + block_offset);
                    let p1 = data.as_ptr().add(leaf1 * leaf_size + block_offset);

                    let w0_lo = _mm_loadu_si128(p0.cast::<__m128i>());
                    let w0_hi = _mm_loadu_si128(p1.cast::<__m128i>());
                    let w1_lo = _mm_loadu_si128(p0.add(16).cast::<__m128i>());
                    let w1_hi = _mm_loadu_si128(p1.add(16).cast::<__m128i>());
                    let w0 = _mm256_inserti128_si256(_mm256_castsi128_si256(w0_lo), w0_hi, 1);
                    let w1 = _mm256_inserti128_si256(_mm256_castsi128_si256(w1_lo), w1_hi, 1);
                    states[g][0] = _mm256_xor_si256(states[g][0], w0);
                    states[g][1] = _mm256_xor_si256(states[g][1], w1);
                }
                permute_groups(&mut states, t);
            }

            // Transpose `[leaf0.word, leaf1.word]` vectors into the normal
            // contiguous `[leaf0.word0, leaf0.word1]` digest layout.
            for g in 0..G {
                let digest0 = _mm256_permute2x128_si256(states[g][0], states[g][1], 0x20);
                let digest1 = _mm256_permute2x128_si256(states[g][0], states[g][1], 0x31);
                let dst = out.as_mut_ptr().add(leaf_base + 2 * g).cast::<__m256i>();
                _mm256_storeu_si256(dst, digest0);
                _mm256_storeu_si256(dst.add(1), digest1);
            }
        }
    }
}

/// One SCALAR permutation through the register-domain kernel: the state
/// rides the low 128-bit lane of each register; the high lane computes
/// garbage that never crosses lanes (every kernel op is per-128-bit-lane).
/// Still ~2.5× faster than the general-register scalar path — the CLMUL
/// products and the reduction stay in the vector domain.
///
/// # Safety
/// See [`permute_flat_groups`].
#[target_feature(enable = "avx2,vpclmulqdq")]
pub(crate) unsafe fn permute_flat_single_u128(flat: &mut [u128; STATE_SIZE], t: &KernelTables) {
    unsafe {
        let mut regs: [[__m256i; STATE_SIZE]; 1] = [std::array::from_fn(|i| {
            _mm256_zextsi128_si256(_mm_loadu_si128(&flat[i] as *const u128 as *const __m128i))
        })];
        permute_groups(&mut regs, t);
        for i in 0..STATE_SIZE {
            _mm_storeu_si128(
                &mut flat[i] as *mut u128 as *mut __m128i,
                _mm256_castsi256_si128(regs[0][i]),
            );
        }
    }
}
