//! Zerocheck PIOP over an **F128-valued** hypercube — the FieldR1cs
//! substrate.
//!
//! Proves `a(y) · b(y) + c(y) = 0` for all `y ∈ {0,1}^m`, where `a`, `b`, `c`
//! are vectors of `2^m` **field elements** (the boolean parent module proves
//! the same statement for bit vectors). The protocol shape is the parent's:
//! univariate skip over the low [`K_SKIP`] variables (round 1 on the φ_8
//! domain, verifier reconstruction via the S-zero trick), then `m − K_SKIP`
//! multilinear rounds with `(G(1), G(∞))` messages. Proof and claim reuse the
//! parent's [`ZerocheckProof`] / [`ZerocheckClaim`] types — the wire shape is
//! identical.
//!
//! **Deliberate protocol differences from the boolean zerocheck:**
//!
//! 1. **All rest-variable eq weights are sampled.** The boolean prover pins 7
//!    inner eq coordinates to protocol constants (`small_challenges_ghash` /
//!    `medium_challenges_ghash`) — a prover-side byte-table optimization that
//!    is sound for *bit-valued* `g = a·b ⊕ c` (a cheating pattern would need a
//!    subset of the fixed eq products XOR-summing to zero). With F128-valued
//!    `g` an adversary can scale violations freely and cancel any *known*
//!    fixed weights exactly, so fixed coordinates would be unsound here.
//!    Every eq weight in this protocol is drawn from the transcript.
//! 2. **No `r_skip` sampling.** The boolean path samples `k_skip` challenges
//!    it never uses (vestigial lockstep). Dropping them saves 6 squeezes per
//!    verify — which the in-circuit verifier trace replays at ~360
//!    constraints each.
//! 3. **Fresh domain label** (`history-field-zerocheck-v0`): field and boolean
//!    transcripts can never be confused for one another.
//!
//! The univariate-skip extension S → Λ runs the parent's additive-NTT
//! butterflies with the F8 twiddles lifted through `φ_8`, acting on F128
//! values ([`SkipExtender`]); equivalence with the verifier's Lagrange
//! conventions is pinned by tests against `lagrange_weights_naive`.

use crate::challenger::Challenger;
use crate::field::{F8, F128, phi8};
use crate::lincheck::build_eq_table;
use crate::ntt::compute_twiddles;
use crate::zerocheck::multilinear::{
    fold_in_place_pair, interpolate_at_z_combined, interpolate_at_z_on_lambda,
    lagrange_weights_naive, round_pair_naive,
};
use crate::zerocheck::{K_SKIP, VerifyError, ZerocheckClaim, ZerocheckProof};

// ---------------------------------------------------------------------------
// Univariate-skip extension S → Λ for F128-valued columns
// ---------------------------------------------------------------------------

/// Additive-NTT extension of a degree-`< 2^k` polynomial from its evaluations
/// on `S = φ_8({0..2^k−1})` to evaluations on `Λ = φ_8({2^k..2^{k+1}−1})`,
/// acting on **F128 values** with the F8 twiddle schedule lifted via `φ_8`.
///
/// This is the field-valued analogue of the parent's
/// `InvNttTableByteSingleGf8` (inverse NTT on the S coset, forward NTT on the
/// Λ coset), minus the bit-row byte tables.
pub struct SkipExtender {
    k: usize,
    tw_s: Vec<F128>,
    tw_l: Vec<F128>,
}

impl SkipExtender {
    pub fn new(k: usize) -> Self {
        assert!(k <= 7, "S ∪ Λ must fit in F_8");
        let lift = |tw: Vec<F8>| -> Vec<F128> { tw.into_iter().map(phi8).collect() };
        Self {
            k,
            tw_s: lift(compute_twiddles(k, F8::ZERO)),
            tw_l: lift(compute_twiddles(k, F8(1u8 << k))),
        }
    }

    /// In-place: `v` holds evaluations on S (index `i` ↔ node `φ_8(i)`);
    /// afterwards `v` holds evaluations on Λ (index `i` ↔ node `φ_8(2^k + i)`).
    pub fn extend_s_to_lambda(&self, v: &mut [F128]) {
        assert_eq!(v.len(), 1usize << self.k);
        if v.len() <= 1 {
            return;
        }
        ifft_rec_f128(v, &self.tw_s, 1);
        fft_rec_f128(v, &self.tw_l, 1);
    }
}

/// Forward additive-NTT recursion on F128 values (LCH coefficients →
/// evaluations). Mirror of `crate::ntt::fft_rec` with lifted twiddles.
fn fft_rec_f128(v: &mut [F128], tw: &[F128], idx: usize) {
    let n = v.len();
    if n == 1 {
        return;
    }
    let lambda = tw[idx - 1];
    let half = n >> 1;
    for i in 0..half {
        let w = v[half + i];
        v[i] += lambda * w;
        v[half + i] = w + v[i];
    }
    let (lo, hi) = v.split_at_mut(half);
    fft_rec_f128(lo, tw, 2 * idx);
    fft_rec_f128(hi, tw, 2 * idx + 1);
}

/// Inverse additive-NTT recursion on F128 values (evaluations → LCH
/// coefficients). Mirror of `crate::ntt::ifft_rec`.
fn ifft_rec_f128(v: &mut [F128], tw: &[F128], idx: usize) {
    let n = v.len();
    if n == 1 {
        return;
    }
    let half = n >> 1;
    {
        let (lo, hi) = v.split_at_mut(half);
        ifft_rec_f128(lo, tw, 2 * idx);
        ifft_rec_f128(hi, tw, 2 * idx + 1);
    }
    let lambda = tw[idx - 1];
    for i in 0..half {
        v[half + i] += v[i];
        v[i] += lambda * v[half + i];
    }
}

// ---------------------------------------------------------------------------
// Prove
// ---------------------------------------------------------------------------

/// Prove `a(y)·b(y) + c(y) = 0` for all `y ∈ {0,1}^m` over F128-valued
/// columns of length `2^m`. Requires `m ≥ K_SKIP + 1` (at least one
/// multilinear round past the skip).
///
/// Wire shape matches the boolean [`super::prove_packed`]: round-1 messages
/// are the `2^K_SKIP` evaluations of `P^{AB}` and `P^C` on Λ, multilinear
/// rounds send `(G(1), G(∞))`, then the final `â`, `b̂`, `ĉ` evaluations.
pub fn prove<C: Challenger>(
    a: &[F128],
    b: &[F128],
    c: &[F128],
    m: usize,
    challenger: &mut C,
) -> (ZerocheckProof, ZerocheckClaim) {
    use rayon::prelude::*;

    let k_skip = K_SKIP;
    let ell = 1usize << k_skip;
    assert!(m >= k_skip + 1, "prove requires m >= K_SKIP + 1");
    let n = 1usize << m;
    assert_eq!(a.len(), n);
    assert_eq!(b.len(), n);
    assert_eq!(c.len(), n);
    let n_mlv = m - k_skip;
    let n_rest = 1usize << n_mlv;

    challenger.observe_label(b"history-field-zerocheck-v0");

    // ---- 1. Sample the rest-variable eq weights (ALL random — see module doc).
    let r_rest = challenger.sample_f128_vec(n_mlv);
    let eq = build_eq_table(&r_rest);
    debug_assert_eq!(eq.len(), n_rest);

    // ---- 2. Round 1: P^{AB}(λ) and P^C on S, in one parallel pass over x.
    //
    // For each rest-assignment x: gather the contiguous 2^k_skip-blocks of a
    // and b, extend both S → Λ, and accumulate eq[x]·â(λ,x)·b̂(λ,x) into the
    // Λ-accumulator. C is linear in the skip variable, so its eq-weighted
    // fold happens on S and is extended once at the end.
    let extender = SkipExtender::new(k_skip);
    let chunk = 1usize.max(n_rest / (8 * rayon::current_num_threads().max(1)));
    let (p_ab, mut c_s) = (0..n_rest.div_ceil(chunk))
        .into_par_iter()
        .map(|ci| {
            let x_lo = ci * chunk;
            let x_hi = ((ci + 1) * chunk).min(n_rest);
            let mut acc_ab = vec![F128::ZERO; ell];
            let mut acc_c = vec![F128::ZERO; ell];
            let mut a_loc = vec![F128::ZERO; ell];
            let mut b_loc = vec![F128::ZERO; ell];
            for x in x_lo..x_hi {
                let base = x * ell;
                let w = eq[x];
                a_loc.copy_from_slice(&a[base..base + ell]);
                b_loc.copy_from_slice(&b[base..base + ell]);
                extender.extend_s_to_lambda(&mut a_loc);
                extender.extend_s_to_lambda(&mut b_loc);
                for s in 0..ell {
                    acc_ab[s] += w * a_loc[s] * b_loc[s];
                    acc_c[s] += w * c[base + s];
                }
            }
            (acc_ab, acc_c)
        })
        .reduce(
            || (vec![F128::ZERO; ell], vec![F128::ZERO; ell]),
            |(mut ab1, mut c1), (ab2, c2)| {
                for i in 0..ell {
                    ab1[i] += ab2[i];
                    c1[i] += c2[i];
                }
                (ab1, c1)
            },
        );
    let round1_ab = p_ab;
    extender.extend_s_to_lambda(&mut c_s);
    let round1_c = c_s;

    // ---- 3. Observe round-1 messages, sample the skip fold point z.
    challenger.observe_f128_slice(&round1_ab);
    challenger.observe_f128_slice(&round1_c);
    let z = challenger.sample_f128();

    // ---- 4. c-claim: ĉ(z, r_rest) by interpolating round1_c at z.
    let final_c_eval = interpolate_at_z_on_lambda(&round1_c, k_skip, z);

    // ---- 5. Fold a, b at z (Lagrange weights on S).
    let weights = lagrange_weights_naive(k_skip, z);
    let fold_at_z = |t: &[F128]| -> Vec<F128> {
        (0..n_rest)
            .into_par_iter()
            .map(|x| {
                let base = x * ell;
                let mut acc = F128::ZERO;
                for s in 0..ell {
                    acc += weights[s] * t[base + s];
                }
                acc
            })
            .collect()
    };
    let mut a_mlv = fold_at_z(a);
    let mut b_mlv = fold_at_z(b);

    // ---- 6. Multilinear rounds. Message convention matches the boolean
    // prover: wire carries the bare (G(1), G(∞)) (r_next[0] = ONE), the eq
    // weight of the bound variable is absorbed by the verifier's G(0)
    // reconstruction.
    let mut multilinear_msgs = Vec::with_capacity(n_mlv);
    let mut mlv_rhos: Vec<F128> = Vec::with_capacity(n_mlv);
    {
        let mut r_next = vec![F128::ONE; n_mlv];
        r_next[1..].copy_from_slice(&r_rest[1..]);
        let (m1, mi) = round_pair_naive(&a_mlv, &b_mlv, &r_next);
        multilinear_msgs.push((m1, mi));
        challenger.observe_f128(m1);
        challenger.observe_f128(mi);
        mlv_rhos.push(challenger.sample_f128());
    }
    for i in 0..(n_mlv - 1) {
        let rho_prev = mlv_rhos[i];
        fold_in_place_pair(&mut a_mlv, &mut b_mlv, rho_prev);
        let log_len = a_mlv.len().trailing_zeros() as usize;
        let mut r_next = vec![F128::ONE; log_len];
        r_next[1..].copy_from_slice(&r_rest[i + 2..]);
        let (m1, mi) = round_pair_naive(&a_mlv, &b_mlv, &r_next);
        multilinear_msgs.push((m1, mi));
        challenger.observe_f128(m1);
        challenger.observe_f128(mi);
        mlv_rhos.push(challenger.sample_f128());
    }

    // ---- 7. Final binding at the last challenge.
    let rho_last = *mlv_rhos.last().expect("at least one ρ sampled");
    fold_in_place_pair(&mut a_mlv, &mut b_mlv, rho_last);
    debug_assert_eq!(a_mlv.len(), 1);
    let final_a_eval = a_mlv[0];
    let final_b_eval = b_mlv[0];

    // ---- 8. FS-bind the final â, b̂ claims (lincheck's α-batched reduction
    // downstream is only sound if α is sampled after these are absorbed —
    // same argument as the boolean path).
    challenger.observe_f128(final_a_eval);
    challenger.observe_f128(final_b_eval);

    let proof = ZerocheckProof {
        round1_ab,
        round1_c,
        multilinear_rounds: multilinear_msgs,
        final_a_eval,
        final_b_eval,
        final_c_eval,
    };
    let claim = ZerocheckClaim {
        z,
        mlv_challenges: mlv_rhos,
        r_rest,
        a_eval: final_a_eval,
        b_eval: final_b_eval,
        c_eval: final_c_eval,
    };
    (proof, claim)
}

// ---------------------------------------------------------------------------
// Verify
// ---------------------------------------------------------------------------

/// Verify a field-zerocheck proof over `{0,1}^log_n`. Lockstep mirror of
/// [`prove`]; identical round algebra to the boolean [`super::verify`] except
/// that every rest eq weight is sampled (and no vestigial `r_skip` draw).
pub fn verify<C: Challenger>(
    log_n: usize,
    proof: &ZerocheckProof,
    challenger: &mut C,
) -> Result<ZerocheckClaim, VerifyError> {
    let m = log_n;
    let k_skip = K_SKIP;

    if m < k_skip + 1 {
        return Err(VerifyError::LogNTooSmall { log_n: m, k_skip });
    }
    let n_mlv = m - k_skip;
    let ell = 1usize << k_skip;

    if proof.round1_ab.len() != ell {
        return Err(VerifyError::BadRound1Length {
            expected: ell,
            got: proof.round1_ab.len(),
        });
    }
    if proof.round1_c.len() != ell {
        return Err(VerifyError::BadRound1Length {
            expected: ell,
            got: proof.round1_c.len(),
        });
    }
    if proof.multilinear_rounds.len() != n_mlv {
        return Err(VerifyError::BadMultilinearRoundsLength {
            expected: n_mlv,
            got: proof.multilinear_rounds.len(),
        });
    }

    challenger.observe_label(b"history-field-zerocheck-v0");

    // ---- Re-derive the rest eq weights.
    let r_rest = challenger.sample_f128_vec(n_mlv);

    // ---- Observe round-1 messages, sample z.
    challenger.observe_f128_slice(&proof.round1_ab);
    challenger.observe_f128_slice(&proof.round1_c);
    let z = challenger.sample_f128();

    // ---- Reconstruct ĉ(z, r_rest) from round1_c.
    let computed_c_eval = interpolate_at_z_on_lambda(&proof.round1_c, k_skip, z);
    if computed_c_eval != proof.final_c_eval {
        return Err(VerifyError::CEvalMismatch);
    }

    // ---- Initial AB running claim via the S-zero trick: interpolate the
    // combined polynomial (2^k_skip Λ-evaluations + assumed zeros on S) at z,
    // then P^{AB}(z) = P^{combined}(z) + P^C(z) in char 2.
    let combined_at_lambda: Vec<F128> = proof
        .round1_ab
        .iter()
        .zip(&proof.round1_c)
        .map(|(x, y)| *x + *y)
        .collect();
    let combined_at_z = interpolate_at_z_combined(&combined_at_lambda, k_skip, z);
    let p_c_at_z = interpolate_at_z_on_lambda(&proof.round1_c, k_skip, z);
    let mut c_running = combined_at_z + p_c_at_z;

    // ---- Multilinear chain: identical algebra to the boolean verify, with
    // the bound variable's eq weight = r_rest[i].
    let mut mlv_rhos: Vec<F128> = Vec::with_capacity(n_mlv);
    for (i, &(msg_1, msg_inf)) in proof.multilinear_rounds.iter().enumerate() {
        let r_eq = r_rest[i];
        let one_plus_r_eq = F128::ONE + r_eq;

        let g1 = msg_1;
        let g_inf = msg_inf;
        let g0 = (c_running + r_eq * g1) * one_plus_r_eq.inv();

        challenger.observe_f128(msg_1);
        challenger.observe_f128(msg_inf);
        let rho = challenger.sample_f128();
        mlv_rhos.push(rho);

        let one_plus_rho = F128::ONE + rho;
        c_running = g0 * one_plus_rho + g1 * rho + g_inf * rho * one_plus_rho;
    }

    // ---- Final consistency: G_final(ρ_all) = â·b̂.
    let expected_final = proof.final_a_eval * proof.final_b_eval;
    if c_running != expected_final {
        return Err(VerifyError::SumcheckFinalFailed);
    }

    // ---- FS-bind the final â, b̂ claims (mirrors prove).
    challenger.observe_f128(proof.final_a_eval);
    challenger.observe_f128(proof.final_b_eval);

    Ok(ZerocheckClaim {
        z,
        mlv_challenges: mlv_rhos,
        r_rest,
        a_eval: proof.final_a_eval,
        b_eval: proof.final_b_eval,
        c_eval: proof.final_c_eval,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::FsChallenger;
    use crate::field::PHI_8_TABLE;

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
        fn f128(&mut self) -> F128 {
            F128 {
                lo: self.next_u64(),
                hi: self.next_u64(),
            }
        }
        fn f128_vec(&mut self, n: usize) -> Vec<F128> {
            (0..n).map(|_| self.f128()).collect()
        }
    }

    /// The NTT-lifted S → Λ extension matches direct Lagrange interpolation
    /// from the S nodes — pins the domain/index conventions to the verifier's
    /// `lagrange_weights_naive` (φ_8(i) ↔ index i, Λ offset 2^k).
    #[test]
    fn skip_extender_matches_lagrange_oracle() {
        let mut rng = Rng::new(0x5EED);
        for k in 1..=6usize {
            let ell = 1usize << k;
            let extender = SkipExtender::new(k);
            for _ in 0..4 {
                let vals_s = rng.f128_vec(ell);
                let mut extended = vals_s.clone();
                extender.extend_s_to_lambda(&mut extended);
                for j in 0..ell {
                    let lambda_j = PHI_8_TABLE[ell + j];
                    let weights = lagrange_weights_naive(k, lambda_j);
                    let mut expected = F128::ZERO;
                    for s in 0..ell {
                        expected += weights[s] * vals_s[s];
                    }
                    assert_eq!(extended[j], expected, "k={k} j={j}");
                }
            }
        }
    }

    /// Honest roundtrip: c = a ⊙ b (field product), verify accepts and the
    /// claims agree byte-for-byte.
    #[test]
    fn prove_verify_roundtrip_honest() {
        for &m in &[7usize, 8, 10, 13] {
            let mut rng = Rng::new(100 + m as u64);
            let a = rng.f128_vec(1 << m);
            let b = rng.f128_vec(1 << m);
            let c: Vec<F128> = a.iter().zip(&b).map(|(x, y)| *x * *y).collect();

            let mut ch_prove = FsChallenger::new(b"field-zc-test-v0");
            let (proof, claim_p) = prove(&a, &b, &c, m, &mut ch_prove);

            assert_eq!(proof.round1_ab.len(), 1 << K_SKIP);
            assert_eq!(proof.multilinear_rounds.len(), m - K_SKIP);

            let mut ch_verify = FsChallenger::new(b"field-zc-test-v0");
            let claim_v = verify(m, &proof, &mut ch_verify)
                .unwrap_or_else(|e| panic!("verify rejected honest proof at m={m}: {e:?}"));
            assert_eq!(claim_p, claim_v, "claim mismatch at m={m}");

            // Post-verify transcript states agree (downstream challenges in
            // lockstep).
            assert_eq!(ch_prove.sample_f128(), ch_verify.sample_f128());
        }
    }

    /// The final claims are true MLE evaluations: check â(z, ρ) against a
    /// naive quirky MLE evaluation of the witness column.
    #[test]
    fn final_evals_match_naive_mle() {
        let m = 8;
        let mut rng = Rng::new(0xA11CE);
        let a = rng.f128_vec(1 << m);
        let b = rng.f128_vec(1 << m);
        let c: Vec<F128> = a.iter().zip(&b).map(|(x, y)| *x * *y).collect();
        let mut ch = FsChallenger::new(b"field-zc-test-v0");
        let (proof, claim) = prove(&a, &b, &c, m, &mut ch);

        // Quirky MLE eval: Σ_i f[i] · L_{i_skip}(z) · eq(point, i_rest).
        let quirky_eval = |f: &[F128], z: F128, point: &[F128]| -> F128 {
            let ell = 1usize << K_SKIP;
            let weights = lagrange_weights_naive(K_SKIP, z);
            let eq = build_eq_table(point);
            let mut acc = F128::ZERO;
            for (i, &v) in f.iter().enumerate() {
                acc += v * weights[i % ell] * eq[i / ell];
            }
            acc
        };
        assert_eq!(
            quirky_eval(&a, claim.z, &claim.mlv_challenges),
            proof.final_a_eval,
            "â mismatch"
        );
        assert_eq!(
            quirky_eval(&b, claim.z, &claim.mlv_challenges),
            proof.final_b_eval,
            "b̂ mismatch"
        );
        assert_eq!(
            quirky_eval(&c, claim.z, &claim.r_rest),
            proof.final_c_eval,
            "ĉ mismatch"
        );
    }

    /// A statement false at one point must be rejected — including
    /// perturbations that live purely in the field (not representable by a
    /// bit flip).
    #[test]
    fn false_statements_rejected() {
        for seed in 0..20u64 {
            let m = 7;
            let mut rng = Rng::new(0xBAD ^ seed);
            let a = rng.f128_vec(1 << m);
            let b = rng.f128_vec(1 << m);
            let mut c: Vec<F128> = a.iter().zip(&b).map(|(x, y)| *x * *y).collect();
            let idx = rng.next_u64() as usize % c.len();
            c[idx] += rng.f128() + F128::ONE; // ensure nonzero delta
            let mut ch_prove = FsChallenger::new(b"field-zc-test-v0");
            let (proof, _) = prove(&a, &b, &c, m, &mut ch_prove);
            let mut ch_verify = FsChallenger::new(b"field-zc-test-v0");
            assert!(
                verify(m, &proof, &mut ch_verify).is_err(),
                "false statement accepted (seed={seed})"
            );
        }
    }

    /// Byte-mutating any proof component must be rejected.
    #[test]
    fn mutations_rejected() {
        let m = 8;
        let mut rng = Rng::new(0xF00D);
        let a = rng.f128_vec(1 << m);
        let b = rng.f128_vec(1 << m);
        let c: Vec<F128> = a.iter().zip(&b).map(|(x, y)| *x * *y).collect();
        let mut ch = FsChallenger::new(b"field-zc-test-v0");
        let (proof, _) = prove(&a, &b, &c, m, &mut ch);

        let mutations: Vec<(&str, Box<dyn Fn(&mut ZerocheckProof)>)> = vec![
            ("round1_ab[0]", Box::new(|p| p.round1_ab[0].lo ^= 1)),
            ("round1_ab[63]", Box::new(|p| p.round1_ab[63].hi ^= 1)),
            ("round1_c[5]", Box::new(|p| p.round1_c[5].lo ^= 1)),
            ("mlv[0].0", Box::new(|p| p.multilinear_rounds[0].0.lo ^= 1)),
            (
                "mlv[last].1",
                Box::new(|p| {
                    let last = p.multilinear_rounds.len() - 1;
                    p.multilinear_rounds[last].1.hi ^= 1;
                }),
            ),
            ("final_a_eval", Box::new(|p| p.final_a_eval.lo ^= 1)),
            ("final_b_eval", Box::new(|p| p.final_b_eval.lo ^= 1)),
            ("final_c_eval", Box::new(|p| p.final_c_eval.hi ^= 1)),
        ];
        for (label, mutate) in mutations {
            let mut bad = proof.clone();
            mutate(&mut bad);
            let mut ch = FsChallenger::new(b"field-zc-test-v0");
            assert!(
                verify(m, &bad, &mut ch).is_err(),
                "mutation {label} accepted"
            );
        }

        // Shape corruptions.
        let mut bad = proof.clone();
        bad.round1_ab.pop();
        let mut ch = FsChallenger::new(b"field-zc-test-v0");
        assert!(matches!(
            verify(m, &bad, &mut ch),
            Err(VerifyError::BadRound1Length { .. })
        ));
        let mut bad = proof.clone();
        bad.multilinear_rounds.pop();
        let mut ch = FsChallenger::new(b"field-zc-test-v0");
        assert!(matches!(
            verify(m, &bad, &mut ch),
            Err(VerifyError::BadMultilinearRoundsLength { .. })
        ));
    }

    /// Product-preserving tamper of (â, b̂) passes the zerocheck's own final
    /// check but must diverge the downstream transcript (the α-batching
    /// defense — regression mirror of the boolean audit test).
    #[test]
    fn final_ab_claims_bound_to_transcript() {
        let m = 8;
        let mut rng = Rng::new(0xF1A7);
        let a = rng.f128_vec(1 << m);
        let b = rng.f128_vec(1 << m);
        let c: Vec<F128> = a.iter().zip(&b).map(|(x, y)| *x * *y).collect();
        let mut ch = FsChallenger::new(b"field-zc-test-v0");
        let (proof, _) = prove(&a, &b, &c, m, &mut ch);

        let mut ch_honest = FsChallenger::new(b"field-zc-test-v0");
        assert!(verify(m, &proof, &mut ch_honest).is_ok());
        let alpha_honest = ch_honest.sample_f128();

        let t = F128 {
            lo: 0x0123_4567_89ab_cdef,
            hi: 0xfedc_ba98_7654_3210,
        };
        let mut bad = proof.clone();
        bad.final_a_eval *= t;
        bad.final_b_eval *= t.inv();
        let mut ch_tampered = FsChallenger::new(b"field-zc-test-v0");
        assert!(
            verify(m, &bad, &mut ch_tampered).is_ok(),
            "tamper caught by zerocheck alone (unexpected but fine — defense in depth)"
        );
        let alpha_tampered = ch_tampered.sample_f128();
        assert_ne!(
            alpha_honest, alpha_tampered,
            "final â/b̂ claims not transcript-bound"
        );
    }

    /// Determinism: same inputs, same seed → identical proof.
    #[test]
    fn prove_deterministic() {
        let m = 7;
        let mut rng = Rng::new(0xD00D);
        let a = rng.f128_vec(1 << m);
        let b = rng.f128_vec(1 << m);
        let c: Vec<F128> = a.iter().zip(&b).map(|(x, y)| *x * *y).collect();
        let mut ch1 = FsChallenger::new(b"field-zc-test-v0");
        let mut ch2 = FsChallenger::new(b"field-zc-test-v0");
        let (p1, c1) = prove(&a, &b, &c, m, &mut ch1);
        let (p2, c2) = prove(&a, &b, &c, m, &mut ch2);
        assert_eq!(p1, p2);
        assert_eq!(c1, c2);
    }
}
