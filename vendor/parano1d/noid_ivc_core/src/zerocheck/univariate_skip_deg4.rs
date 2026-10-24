//! Round-1 prover message for the **degree-4** zerocheck (univariate skip).
//!
//! Companion to [`super::univariate_skip`] for the degree-2 case. Encodes the
//! constraint
//!
//!   a(y) · b(y) · c(y) · d(y) ⊕ z(y) = 0   for all y ∈ {0,1}^m
//!
//! and emits a round-1 message that "skips" the first `K_SKIP = 6` boolean
//! coords via additive-NTT extension to a univariate variable.
//!
//! ## What changes vs the degree-2 round 1
//!
//! - **Four lookup-based FFTs per row** (a, b, c, d) rather than two (a, b).
//! - **Output domain Λ₄ has |Λ₄| = 192** rather than |Λ| = 64. The constraint
//!   polynomial restricted to the LCH univariate is degree < 4·2^K_SKIP − 3 =
//!   **253**, which needs ≥ 253 evaluation points to uniquely interpolate; the
//!   next power of 2 is **256 = 2^8 = |F₈|** itself, and with |S| = 64 we have
//!   |Λ₄| = 256 − 64 = 192 fresh evaluations to send.
//!
//! ## Domain layout
//!
//! ```text
//!   V₈ = F₈                  (the full 256-point F_2-subspace, i.e. all of F₈)
//!   S    = {0, 1, …, 63}     (first 64; same as the degree-2 S)
//!   Λ₄   = V₈ \ S = {64..255} (the 192 fresh evals)
//! ```
//!
//! ## NTT-extend trick
//!
//! The LCH novel polynomial basis `{W_0, W_1, …}` for the 6-dim subspace S is
//! the **prefix** of the basis for the 8-dim V₈ (same β recursion, same first
//! 6 basis vectors). So a polynomial of degree < 64 in the 6-dim basis is the
//! same polynomial in the 8-dim basis with zero coefficients on W_64..W_255.
//!
//! Therefore: `inv_NTT_S` (size 64) on the 64 input bits → 64 coefficients,
//! zero-pad to length 256, `fwd_NTT_V8` (size 256) → 256 evaluations on V₈.
//! First 64 reproduce the input bits; last 192 are the fresh evals on Λ₄.
//!
//! ## Naive vs optimized
//!
//! This file implements the **naive** reference following the degree-2
//! `round1_naive` template. Production-quality kernels (lookup tables,
//! deferred reductions, shift-reduce, SIMD) parallel `univariate_skip_optimized.rs`
//! and would land later; this file is the algorithmic skeleton.

use crate::field::{F8, F128, phi8};
use crate::ntt::AdditiveNttGf8;

use super::univariate_skip::build_eq;

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// log₂ size of the input skip domain S (same as the degree-2 K_SKIP).
pub const K_SKIP: usize = 6;
/// log₂ size of the full extended domain V₈.
pub const K_V8: usize = 8;

/// |S| = 2^K_SKIP = 64.
pub const S_SIZE: usize = 1usize << K_SKIP;
/// |V₈| = 2^K_V8 = 256.
pub const V8_SIZE: usize = 1usize << K_V8;
/// |Λ₄| = V8_SIZE − S_SIZE = 192.
pub const LAMBDA4_SIZE: usize = V8_SIZE - S_SIZE;

// ---------------------------------------------------------------------------
// Naive degree-4 round-1 prover message
// ---------------------------------------------------------------------------

/// Compute the round-1 prover message for the degree-4 zerocheck constraint
/// `a·b·c·d ⊕ z = 0`.
///
/// Returns `(p_abcd, p_z)`, each a length-`LAMBDA4_SIZE = 192` F128 vector of
/// evaluations on Λ₄. Both messages are evaluations on the same domain.
///
/// Preconditions:
/// - `a.len() == b.len() == c.len() == d.len() == z.len() == 2^m`.
/// - `r.len() == m`.
/// - `m >= K_SKIP`.
///
/// Index convention (same as `round1_naive`): for index `i ∈ 0..2^m`, the low
/// `K_SKIP` bits address the skip variables (`y_skip ∈ S`), the high `m −
/// K_SKIP` bits address the rest variables (`y_rest`).
pub fn round1_deg4_naive(
    a: &[bool],
    b: &[bool],
    c: &[bool],
    d: &[bool],
    z: &[bool],
    m: usize,
    r: &[F128],
) -> (Vec<F128>, Vec<F128>) {
    assert!(K_SKIP <= m, "K_SKIP must be ≤ m");
    let n = 1usize << m;
    assert_eq!(a.len(), n);
    assert_eq!(b.len(), n);
    assert_eq!(c.len(), n);
    assert_eq!(d.len(), n);
    assert_eq!(z.len(), n);
    assert_eq!(r.len(), m);

    let n_chunks_x = 1usize << (m - K_SKIP);

    // NTT pair: inv on S (size 64) then fwd on V₈ (size 256).
    // Shared offset = 0 so the 6-dim basis is the prefix of the 8-dim basis.
    let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
    let ntt_v8 = AdditiveNttGf8::new(K_V8, F8::ZERO);

    // eq table over the rest-of-r challenges.
    let eq_full = build_eq(&r[K_SKIP..]);
    debug_assert_eq!(eq_full.len(), n_chunks_x);

    let mut p_abcd = vec![F128::ZERO; LAMBDA4_SIZE];
    let mut p_z = vec![F128::ZERO; LAMBDA4_SIZE];

    // Scratch buffers — one V₈-sized buffer per factor.
    let mut a_col = vec![F8::ZERO; V8_SIZE];
    let mut b_col = vec![F8::ZERO; V8_SIZE];
    let mut c_col = vec![F8::ZERO; V8_SIZE];
    let mut d_col = vec![F8::ZERO; V8_SIZE];
    let mut z_col = vec![F8::ZERO; V8_SIZE];

    for x_rest in 0..n_chunks_x {
        let base = x_rest * S_SIZE;

        // 1. Load 64 bits of each factor into positions 0..64; clear 64..256.
        for s in 0..S_SIZE {
            a_col[s] = F8(a[base + s] as u8);
            b_col[s] = F8(b[base + s] as u8);
            c_col[s] = F8(c[base + s] as u8);
            d_col[s] = F8(d[base + s] as u8);
            z_col[s] = F8(z[base + s] as u8);
        }
        for s in S_SIZE..V8_SIZE {
            a_col[s] = F8::ZERO;
            b_col[s] = F8::ZERO;
            c_col[s] = F8::ZERO;
            d_col[s] = F8::ZERO;
            z_col[s] = F8::ZERO;
        }

        // 2. Extend each factor from S to V₈:
        //    inv on the first 64 entries  → 64 coefficients (6-dim novel basis).
        //    leave entries 64..256 as zero (= zero coeffs on W_64..W_255).
        //    fwd on the full 256          → 256 evaluations on V₈.
        // First 64 outputs of fwd match the original bits; entries 64..256 are
        // the fresh evaluations on Λ₄.
        for col in [&mut a_col, &mut b_col, &mut c_col, &mut d_col, &mut z_col] {
            ntt_s.inverse(&mut col[..S_SIZE]);
            // tail is already zero
            ntt_v8.forward(col);
        }

        // 3. Accumulate.  p_abcd[i] ← Σ_x eq_x · φ₈(a·b·c·d at λ_i),
        //                 p_z[i]    ← Σ_x eq_x · φ₈(z at λ_i),
        //                 for λ_i = S_SIZE + i ∈ Λ₄.
        let eq_x = eq_full[x_rest];
        for i in 0..LAMBDA4_SIZE {
            let lam = S_SIZE + i;
            let abcd = a_col[lam] * b_col[lam] * c_col[lam] * d_col[lam];
            p_abcd[i] += eq_x * phi8(abcd);
            p_z[i] += eq_x * phi8(z_col[lam]);
        }
    }

    (p_abcd, p_z)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    struct Rng(u64);
    impl Rng {
        fn new(seed: u64) -> Self {
            Self(seed)
        }
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            z ^ (z >> 31)
        }
        fn bits(&mut self, n: usize) -> Vec<bool> {
            (0..n).map(|_| self.next_u64() & 1 == 1).collect()
        }
        fn f128(&mut self) -> F128 {
            F128 {
                lo: self.next_u64(),
                hi: self.next_u64(),
            }
        }
    }

    /// Sanity: NTT-extend a length-64 F8 vector via the "inv on S, fwd on V₈"
    /// trick. The first 64 outputs should match the original input.
    #[test]
    fn ntt_extend_roundtrips_on_s() {
        let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
        let ntt_v8 = AdditiveNttGf8::new(K_V8, F8::ZERO);

        let mut rng = Rng::new(0xA17);
        let original_bits: Vec<F8> = (0..S_SIZE).map(|_| F8(rng.next_u64() as u8 & 1)).collect();

        let mut buf = vec![F8::ZERO; V8_SIZE];
        buf[..S_SIZE].copy_from_slice(&original_bits);
        ntt_s.inverse(&mut buf[..S_SIZE]);
        // tail is already zero (zero-padded coefficients on W_64..W_255).
        ntt_v8.forward(&mut buf);

        for i in 0..S_SIZE {
            assert_eq!(
                buf[i], original_bits[i],
                "NTT-extend on S mismatch at i={i}"
            );
        }
    }

    /// Shape: round1_deg4_naive produces the right-length outputs.
    #[test]
    fn round1_deg4_output_shape() {
        let m = K_SKIP + 1; // smallest non-trivial m
        let mut rng = Rng::new(0xBEEF);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c = rng.bits(1 << m);
        let d = rng.bits(1 << m);
        let z = rng.bits(1 << m);
        let r: Vec<F128> = (0..m).map(|_| rng.f128()).collect();
        let (p_abcd, p_z) = round1_deg4_naive(&a, &b, &c, &d, &z, m, &r);
        assert_eq!(p_abcd.len(), LAMBDA4_SIZE);
        assert_eq!(p_z.len(), LAMBDA4_SIZE);
    }

    /// Sanity vs the degree-2 round1: when c = d = (all 1), the degree-4
    /// product a·b·c·d collapses to a·b. The two messages should agree on
    /// **Λ ∩ Λ₄** (= empty since the degree-2 Λ = {64..127} and degree-4 Λ₄ =
    /// {64..255} overlap on positions 0..63 of each). So at λ = 64..127, the
    /// degree-2 and degree-4 messages must coincide (lifted via φ₈).
    ///
    /// This validates that the degree-4 path's NTT extension is doing the
    /// same thing as the degree-2 path on the matching subdomain.
    #[test]
    fn degree4_reduces_to_degree2_when_cd_one() {
        let m = K_SKIP + 1;
        let mut rng = Rng::new(123);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c = vec![true; 1 << m];
        let d = vec![true; 1 << m];
        let z = vec![false; 1 << m]; // zero linear term — focus on a·b·c·d
        let r: Vec<F128> = (0..m).map(|_| rng.f128()).collect();

        // degree-4 message.
        let (p_abcd, _p_z) = round1_deg4_naive(&a, &b, &c, &d, &z, m, &r);

        // degree-2 oracle: directly evaluate a·b on the SAME domain points
        // (λ ∈ V₈ \ S = positions 64..255) by the same NTT-extend trick.
        let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
        let ntt_v8 = AdditiveNttGf8::new(K_V8, F8::ZERO);
        let n_chunks_x = 1usize << (m - K_SKIP);
        let eq_full = build_eq(&r[K_SKIP..]);
        let mut p_ab_ref = vec![F128::ZERO; LAMBDA4_SIZE];
        let mut a_col = vec![F8::ZERO; V8_SIZE];
        let mut b_col = vec![F8::ZERO; V8_SIZE];
        for x_rest in 0..n_chunks_x {
            let base = x_rest * S_SIZE;
            for col in [&mut a_col, &mut b_col] {
                for v in col.iter_mut() {
                    *v = F8::ZERO;
                }
            }
            for s in 0..S_SIZE {
                a_col[s] = F8(a[base + s] as u8);
                b_col[s] = F8(b[base + s] as u8);
            }
            for col in [&mut a_col, &mut b_col] {
                ntt_s.inverse(&mut col[..S_SIZE]);
                ntt_v8.forward(col);
            }
            let eq_x = eq_full[x_rest];
            for i in 0..LAMBDA4_SIZE {
                let lam = S_SIZE + i;
                p_ab_ref[i] += eq_x * phi8(a_col[lam] * b_col[lam]);
            }
        }

        for i in 0..LAMBDA4_SIZE {
            assert_eq!(
                p_abcd[i],
                p_ab_ref[i],
                "degree-4 vs degree-2 mismatch at i={i} (λ={})",
                S_SIZE + i
            );
        }
    }

    /// Linear-only sanity: a = b = c = d = 0 ⇒ p_abcd = 0 everywhere; p_z
    /// matches a direct NTT extension of z.
    #[test]
    fn linear_only_path() {
        let m = K_SKIP + 2;
        let mut rng = Rng::new(0xC0DE);
        let a = vec![false; 1 << m];
        let b = vec![false; 1 << m];
        let c = vec![false; 1 << m];
        let d = vec![false; 1 << m];
        let z = rng.bits(1 << m);
        let r: Vec<F128> = (0..m).map(|_| rng.f128()).collect();
        let (p_abcd, p_z) = round1_deg4_naive(&a, &b, &c, &d, &z, m, &r);

        // p_abcd must be all zero.
        for v in &p_abcd {
            assert_eq!(*v, F128::ZERO);
        }

        // p_z reference: NTT-extend z on each x_rest row, lift via φ₈, weight by eq.
        let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
        let ntt_v8 = AdditiveNttGf8::new(K_V8, F8::ZERO);
        let n_chunks_x = 1usize << (m - K_SKIP);
        let eq_full = build_eq(&r[K_SKIP..]);
        let mut p_z_ref = vec![F128::ZERO; LAMBDA4_SIZE];
        let mut z_col = vec![F8::ZERO; V8_SIZE];
        for x_rest in 0..n_chunks_x {
            let base = x_rest * S_SIZE;
            for v in z_col.iter_mut() {
                *v = F8::ZERO;
            }
            for s in 0..S_SIZE {
                z_col[s] = F8(z[base + s] as u8);
            }
            ntt_s.inverse(&mut z_col[..S_SIZE]);
            ntt_v8.forward(&mut z_col);
            let eq_x = eq_full[x_rest];
            for i in 0..LAMBDA4_SIZE {
                p_z_ref[i] += eq_x * phi8(z_col[S_SIZE + i]);
            }
        }
        for i in 0..LAMBDA4_SIZE {
            assert_eq!(p_z[i], p_z_ref[i], "p_z mismatch at i={i}");
        }
    }
}
