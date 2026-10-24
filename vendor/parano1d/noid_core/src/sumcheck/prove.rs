// SPDX-License-Identifier: Apache-2.0
// Adapted from binius64. Copyright (C) 2026 Paranoid Zero.

#![allow(clippy::needless_range_loop)]

//! Sum-Check Prover for binary tower fields.
//!
//! Architecture
//! ------------
//!
//! For each of `n_vars` rounds the prover emits a univariate round
//! polynomial of degree `round_degree`, absorbs its coefficients into
//! the Fiat-Shamir channel, draws one challenge, and folds the table
//! along the highest variable.
//!
//! `round_degree` is a parameter, not a constant. Degree-2 product
//! sumchecks and degree-7 KillShot sumchecks use the same engine with
//! explicit degree selection. The degree-7 path uses `round_degree = 8` (`d+1` for
//! degree-7 `g` under an `eq(r, x)` factor). For an honest *multilinear*
//! `f` the round poly is intrinsically linear, so `round_degree >= 1`
//! is always correct — higher degrees just record extra zero
//! coefficients.
//!
//! Fiat-Shamir
//! -----------
//!
//! Challenges are drawn from a `FiatShamir<F>` channel. The old XOR-sum
//! transcript placeholder is gone — any callsite that still ran on it
//! is migrated in this commit. Tests in this crate use the in-module
//! `XorChannel` mock, which is *insecure* but deterministic and
//! sufficient for prove ↔ verify round-trip tests where the only
//! requirement is that both sides agree on the challenge stream.

use super::super::mle::fold::fold_highest_var_inplace;
use crate::transcript::FiatShamir;
use crate::{Block128, TowerField};

/// Univariate polynomial in coefficient form: `coeffs[i]` is the
/// coefficient of `X^i`. `degree() = coeffs.len() - 1`.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RoundPolynomial<F> {
    pub coeffs: Vec<F>,
}

/// Sumcheck round polynomial in transcript form: `[c_0, c_2, …, c_d]`,
/// with the linear coefficient omitted. In characteristic 2 the round
/// identity `p(0) + p(1) = claim` reads `Σ_{i≥1} c_i = claim`, so
/// `c_1 = claim + Σ_{i≥2} c_i` is redundant given the running claim.
/// The verifier reconstructs it, which makes the per-round sum check
/// hold by construction and drops one field element per round from
/// both the transcript and the serialized proof.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CompressedRoundPolynomial<F> {
    /// `[c_0, c_2, …, c_d]` — `d` entries for a degree-`d` polynomial.
    pub coeffs_no_linear: Vec<F>,
}

impl<F: TowerField> CompressedRoundPolynomial<F> {
    /// Drop the linear coefficient from a full round polynomial. Only
    /// use on polynomials that satisfy the round identity against the
    /// claim the verifier will reconstruct with — every honest sumcheck
    /// round does.
    pub fn compress(poly: &RoundPolynomial<F>) -> Self {
        assert!(
            poly.coeffs.len() >= 2,
            "round polynomial must be at least linear"
        );
        let mut coeffs_no_linear = Vec::with_capacity(poly.coeffs.len() - 1);
        coeffs_no_linear.push(poly.coeffs[0]);
        coeffs_no_linear.extend_from_slice(&poly.coeffs[2..]);
        Self { coeffs_no_linear }
    }

    /// Degree of the reconstructed polynomial.
    pub fn degree(&self) -> usize {
        self.coeffs_no_linear.len()
    }

    /// Rebuild the full polynomial from the running sumcheck claim:
    /// `c_1 = claim + Σ_{i≥2} c_i`.
    pub fn reconstruct(&self, claim: F) -> RoundPolynomial<F> {
        assert!(!self.coeffs_no_linear.is_empty(), "empty round polynomial");
        let mut c1 = claim;
        for &c in &self.coeffs_no_linear[1..] {
            c1 += c;
        }
        let mut coeffs = Vec::with_capacity(self.coeffs_no_linear.len() + 1);
        coeffs.push(self.coeffs_no_linear[0]);
        coeffs.push(c1);
        coeffs.extend_from_slice(&self.coeffs_no_linear[1..]);
        RoundPolynomial { coeffs }
    }
}

impl<F: TowerField> RoundPolynomial<F> {
    pub fn from_coeffs(coeffs: Vec<F>) -> Self {
        Self { coeffs }
    }

    pub fn degree(&self) -> usize {
        self.coeffs.len().saturating_sub(1)
    }

    /// Horner evaluation: `c0 + x*(c1 + x*(c2 + ...))`.
    pub fn evaluate(&self, x: F) -> F {
        let mut acc = F::ZERO;
        for &c in self.coeffs.iter().rev() {
            acc = acc * x + c;
        }
        acc
    }

    /// Lagrange-interpolate from `(0, e0), (1, e1), …, (d, e_d)` with
    /// `d = evals.len() - 1`. Points are `F::from(k as u8)`, so this
    /// supports `evals.len() <= 256` — far beyond any sumcheck degree
    /// we will ever run.
    pub fn from_evals(evals: &[F]) -> Self {
        let n = evals.len();
        assert!(n > 0, "need at least one evaluation");
        assert!(n <= 256, "Lagrange X-axis indexes u8");
        let mut out = vec![F::ZERO; n];
        let mut tmp = vec![F::ZERO; n];
        for k in 0..n {
            let xk = F::from(k as u8);
            let mut num = vec![F::ZERO; n];
            num[0] = F::ONE;
            let mut deg = 0usize;
            let mut denom = F::ONE;
            for j in 0..n {
                if j == k {
                    continue;
                }
                let xj = F::from(j as u8);
                for slot in tmp.iter_mut().take(deg + 2) {
                    *slot = F::ZERO;
                }
                for i in 0..=deg {
                    tmp[i] += num[i] * xj;
                    tmp[i + 1] += num[i];
                }
                num.copy_from_slice(&tmp);
                deg += 1;
                denom *= xk + xj;
            }
            let scale = evals[k] * denom.invert();
            for i in 0..n {
                out[i] += num[i] * scale;
            }
        }
        Self { coeffs: out }
    }
}

/// Run the sumcheck prover for a single multilinear polynomial.
///
/// `evals`        — evaluations over `{0,1}^n`, length `2^n`.
/// `round_degree` — degree of the round polynomial recorded each round
///                  (≥ 1; the natural value for multilinear `f` is 1).
/// `channel`      — Fiat-Shamir channel; coefficients are absorbed and
///                  one challenge is squeezed per round.
///
/// Returns `(round_polys, final_eval, challenges)`.
pub fn prove_single_d<F: TowerField, T: FiatShamir<F>>(
    evals: &[F],
    round_degree: usize,
    channel: &mut T,
) -> (Vec<RoundPolynomial<F>>, F, Vec<F>) {
    let n = evals.len().trailing_zeros() as usize;
    assert_eq!(evals.len(), 1 << n, "evals length must be a power of 2");
    assert!(n > 0, "need at least 1 variable");
    assert!(
        round_degree >= 1,
        "round polynomial must be at least linear"
    );

    let mut current = evals.to_vec();
    let mut polys = Vec::with_capacity(n);
    let mut challenges = Vec::with_capacity(n);

    for _round in 0..n {
        let half = current.len() / 2;
        // For multilinear f the round poly is linear in α:
        //   u(α) = Σ_x f_α(x), f_α(x) = (1+α) f_lo(x) + α f_hi(x)
        // ⇒ u(α) = U0 + α · (U0 + U1), with U0=Σf_lo, U1=Σf_hi.
        let mut u0 = F::ZERO;
        let mut u1 = F::ZERO;
        for j in 0..half {
            u0 += current[j];
            u1 += current[j + half];
        }
        let sum = u0 + u1;
        let mut evals_round = Vec::with_capacity(round_degree + 1);
        for k in 0..=round_degree {
            evals_round.push(u0 + F::from(k as u8) * sum);
        }
        let poly = RoundPolynomial::from_evals(&evals_round);

        for &c in &poly.coeffs {
            channel.absorb(c);
        }
        let challenge = channel.squeeze();

        fold_highest_var_inplace(&mut current, challenge);
        polys.push(poly);
        challenges.push(challenge);
    }

    debug_assert_eq!(current.len(), 1);
    (polys, current[0], challenges)
}

// ---------------------------------------------------------------------------
// Packed Block128 variant
// ---------------------------------------------------------------------------

use crate::hardware::tower_to_flat_u128;
use crate::packed::{pack_slice_mut, PackedBlock128, PACKED_LANES};
use rayon::prelude::*;

/// Minimum number of packed elements to justify Rayon overhead.
const PARALLEL_THRESHOLD_PACKED: usize = 256;

/// Packed sumcheck prover for `Block128`. Identical API to
/// `prove_single_d`, but uses packed XOR for the per-round fold once
/// the table is large enough to amortise the lane setup.
pub fn prove_single_packed_d<T: FiatShamir<Block128>>(
    evals: &[Block128],
    round_degree: usize,
    channel: &mut T,
) -> (Vec<RoundPolynomial<Block128>>, Block128, Vec<Block128>) {
    let n = evals.len().trailing_zeros() as usize;
    assert_eq!(evals.len(), 1 << n, "evals length must be a power of 2");
    assert!(n > 0, "need at least 1 variable");
    assert!(
        round_degree >= 1,
        "round polynomial must be at least linear"
    );

    let mut current = evals.to_vec();
    let mut polys = Vec::with_capacity(n);
    let mut challenges = Vec::with_capacity(n);

    use crate::hardware::flat_to_tower_u128;
    const SUMCHECK_PAR_THRESHOLD: usize = 1 << 12;

    for _round in 0..n {
        let half = current.len() / 2;
        let (lo, hi) = current.split_at(half);
        let (u0_flat, u1_flat) = if half >= SUMCHECK_PAR_THRESHOLD {
            lo.par_iter()
                .zip(hi.par_iter())
                .fold(
                    || (0u128, 0u128),
                    |(a0, a1), (v_lo, v_hi)| {
                        (
                            a0 ^ tower_to_flat_u128(v_lo.0),
                            a1 ^ tower_to_flat_u128(v_hi.0),
                        )
                    },
                )
                .reduce(|| (0u128, 0u128), |(a0, a1), (b0, b1)| (a0 ^ b0, a1 ^ b1))
        } else {
            let mut u0_flat: u128 = 0;
            let mut u1_flat: u128 = 0;
            for j in 0..half {
                u0_flat ^= tower_to_flat_u128(lo[j].0);
                u1_flat ^= tower_to_flat_u128(hi[j].0);
            }
            (u0_flat, u1_flat)
        };
        let u0 = Block128(flat_to_tower_u128(u0_flat));
        let u1 = Block128(flat_to_tower_u128(u1_flat));
        let sum = u0 + u1;
        let mut evals_round = Vec::with_capacity(round_degree + 1);
        for k in 0..=round_degree {
            evals_round.push(u0 + Block128::from(k as u8) * sum);
        }
        let poly = RoundPolynomial::from_evals(&evals_round);

        for &c in &poly.coeffs {
            channel.absorb(c);
        }
        let challenge = channel.squeeze();

        let can_use_packed = if PACKED_LANES == 1 {
            true
        } else {
            half.is_multiple_of(PACKED_LANES) && half >= PACKED_LANES
        };
        if can_use_packed {
            fold_highest_var_packed_inplace(&mut current, challenge, half);
        } else {
            fold_highest_var_inplace(&mut current, challenge);
        }
        polys.push(poly);
        challenges.push(challenge);
    }

    debug_assert_eq!(current.len(), 1);
    (polys, current[0], challenges)
}

/// Fold the highest variable in-place using packed operations.
pub fn fold_highest_var_packed_inplace(
    current_evals: &mut Vec<Block128>,
    challenge: Block128,
    half: usize,
) {
    let packed = pack_slice_mut(&mut current_evals[..2 * half]);
    let packed_half = packed.len() / 2;
    let challenge_flat = tower_to_flat_u128(challenge.0);

    let fold_one = |lo: &mut PackedBlock128, hi: PackedBlock128| {
        let lo_flat = lo.to_flat();
        let hi_flat = hi.to_flat();
        let diff = hi_flat.xor(lo_flat);
        let scaled = diff.flat_scalar_mul(challenge_flat);
        let new_lo_flat = lo_flat.xor(scaled);
        *lo = new_lo_flat.to_tower();
    };

    if packed_half >= PARALLEL_THRESHOLD_PACKED {
        let (lo, hi) = packed.split_at_mut(packed_half);
        lo.par_iter_mut()
            .zip(hi.par_iter())
            .for_each(|(lo_val, &hi_val)| fold_one(lo_val, hi_val));
    } else {
        for i in 0..packed_half {
            let hi = packed[i + packed_half];
            fold_one(&mut packed[i], hi);
        }
    }

    current_evals.truncate(half);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Block128;

    type F = Block128;

    /// Insecure deterministic FS mock for noid_core internal tests.
    /// It exists only so prover and verifier agree on the challenge stream
    /// during local round-trip tests.
    #[derive(Default)]
    struct XorChannel {
        state: F,
    }

    impl FiatShamir<F> for XorChannel {
        fn absorb(&mut self, elem: F) {
            self.state += elem;
        }
        fn squeeze(&mut self) -> F {
            self.state += F::ONE;
            self.state
        }
    }

    #[test]
    fn test_from_evals_roundtrip_degree_2() {
        let e0 = F::from(5u8);
        let e1 = F::from(9u8);
        let e2 = F::from(3u8);
        let poly = RoundPolynomial::from_evals(&[e0, e1, e2]);
        assert_eq!(poly.degree(), 2);
        assert_eq!(poly.evaluate(F::ZERO), e0);
        assert_eq!(poly.evaluate(F::ONE), e1);
        assert_eq!(poly.evaluate(F::from(2u8)), e2);
    }

    #[test]
    fn test_from_evals_roundtrip_degree_8() {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let evals: Vec<F> = (0..9).map(|_| F::from(rng.gen::<u128>())).collect();
        let poly = RoundPolynomial::from_evals(&evals);
        assert_eq!(poly.degree(), 8);
        for (k, &e) in evals.iter().enumerate() {
            assert_eq!(poly.evaluate(F::from(k as u8)), e);
        }
    }

    #[test]
    fn test_prove_single_sum_consistency() {
        let evals = vec![F::ZERO, F::ONE, F::ONE, F::ZERO];
        let claimed_sum = evals.iter().fold(F::ZERO, |a, &b| a + b);
        let mut channel = XorChannel::default();
        let (round_polys, _, _) = prove_single_d(&evals, 2, &mut channel);
        assert_eq!(round_polys.len(), 2);
        let rp0 = &round_polys[0];
        assert_eq!(rp0.evaluate(F::ZERO) + rp0.evaluate(F::ONE), claimed_sum);
    }

    #[test]
    fn test_prove_single_larger() {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let n = 4;
        let evals: Vec<F> = (0..(1 << n)).map(|_| F::from(rng.gen::<u128>())).collect();
        let claimed_sum = evals.iter().fold(F::ZERO, |a, &b| a + b);
        let mut channel = XorChannel::default();
        let (round_polys, _, _) = prove_single_d(&evals, 2, &mut channel);
        assert_eq!(round_polys.len(), n);
        assert_eq!(
            round_polys[0].evaluate(F::ZERO) + round_polys[0].evaluate(F::ONE),
            claimed_sum
        );
    }

    #[test]
    fn test_prove_single_packed_matches_scalar() {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let n = 6;
        let evals: Vec<F> = (0..(1 << n)).map(|_| F::from(rng.gen::<u128>())).collect();

        let mut ch_s = XorChannel::default();
        let (scalar_polys, scalar_final, scalar_ch) = prove_single_d(&evals, 2, &mut ch_s);

        let mut ch_p = XorChannel::default();
        let (packed_polys, packed_final, packed_ch) = prove_single_packed_d(&evals, 2, &mut ch_p);

        assert_eq!(scalar_final, packed_final);
        assert_eq!(scalar_polys.len(), packed_polys.len());
        for (s, p) in scalar_polys.iter().zip(packed_polys.iter()) {
            assert_eq!(s.coeffs, p.coeffs);
        }
        assert_eq!(scalar_ch, packed_ch);
    }

    #[test]
    fn test_compressed_round_poly_roundtrip() {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        for degree in 1..=10usize {
            let coeffs: Vec<F> = (0..=degree).map(|_| F::from(rng.gen::<u128>())).collect();
            let poly = RoundPolynomial::from_coeffs(coeffs);
            // The claim the verifier reconstructs against is p(0) + p(1).
            let claim = poly.evaluate(F::ZERO) + poly.evaluate(F::ONE);
            let wire = CompressedRoundPolynomial::compress(&poly);
            assert_eq!(wire.degree(), degree);
            assert_eq!(wire.coeffs_no_linear.len(), degree);
            let rebuilt = wire.reconstruct(claim);
            assert_eq!(rebuilt, poly);
        }
    }

    #[test]
    fn test_compressed_round_poly_wrong_claim_changes_linear_term() {
        let poly = RoundPolynomial::from_coeffs(vec![F::from(3u8), F::from(7u8), F::from(9u8)]);
        let claim = poly.evaluate(F::ZERO) + poly.evaluate(F::ONE);
        let wire = CompressedRoundPolynomial::compress(&poly);
        let bad = wire.reconstruct(claim + F::ONE);
        assert_ne!(bad, poly);
        assert_eq!(bad.coeffs[1], poly.coeffs[1] + F::ONE);
        // Reconstruction pins the round identity by construction.
        assert_eq!(bad.evaluate(F::ZERO) + bad.evaluate(F::ONE), claim + F::ONE);
    }

    #[test]
    fn test_prove_single_d_higher_degree_records_zeros() {
        // For multilinear f, the round poly is linear: higher
        // `round_degree` just zero-pads the high coefficients.
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let evals: Vec<F> = (0..16).map(|_| F::from(rng.gen::<u128>())).collect();

        let mut ch_a = XorChannel::default();
        let (polys_d7, _, _) = prove_single_d(&evals, 7, &mut ch_a);

        for poly in &polys_d7 {
            assert_eq!(poly.degree(), 7);
            for k in 2..=7 {
                assert_eq!(poly.coeffs[k], F::ZERO);
            }
        }
    }
}
