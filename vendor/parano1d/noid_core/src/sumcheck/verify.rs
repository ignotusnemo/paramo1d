// SPDX-License-Identifier: Apache-2.0
// Adapted from binius64. Copyright (C) 2026 Paranoid Zero.

//! Sum-Check Verifier for binary tower fields.

use super::prove::RoundPolynomial;
use crate::transcript::FiatShamir;
use crate::TowerField;

/// Verify a sumcheck proof, replaying the prover's Fiat-Shamir channel.
///
/// `round_polys`    — the per-round univariate polynomials.
/// `channel`        — fresh FS channel, seeded identically to the
///                    prover's; coefficients are absorbed in order and
///                    one challenge is squeezed per round.
/// `initial_claim`  — the value the prover claims for the sum.
///
/// Returns `Some((final_claim, challenges))` on success, `None` on any
/// telescope-check failure. The caller validates `final_claim`
/// externally against the multilinear opening (or the next sumcheck in
/// a chain).
pub fn verify_with_channel<F: TowerField, T: FiatShamir<F>>(
    round_polys: &[RoundPolynomial<F>],
    initial_claim: F,
    channel: &mut T,
) -> Option<(F, Vec<F>)> {
    let mut claim = initial_claim;
    let mut challenges = Vec::with_capacity(round_polys.len());

    for poly in round_polys {
        let sum01 = poly.evaluate(F::ZERO) + poly.evaluate(F::ONE);
        if sum01 != claim {
            return None;
        }
        for &c in &poly.coeffs {
            channel.absorb(c);
        }
        let r = channel.squeeze();
        claim = poly.evaluate(r);
        challenges.push(r);
    }

    Some((claim, challenges))
}

#[cfg(test)]
mod tests {
    use super::super::prove::prove_single_d;
    use super::*;
    use crate::transcript::FiatShamir;
    use crate::Block128;

    type F = Block128;

    /// Same insecure XOR mock as the prover module — both sides use it
    /// in lockstep so the challenge stream matches.
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
    fn test_verify_accepts_valid_proof() {
        let evals = vec![F::ZERO, F::ONE, F::ONE, F::ZERO];
        let claimed_sum = evals.iter().fold(F::ZERO, |a, &b| a + b);

        let mut prover_ch = XorChannel::default();
        let (round_polys, final_eval, _) = prove_single_d(&evals, 2, &mut prover_ch);

        let mut verifier_ch = XorChannel::default();
        let res = verify_with_channel(&round_polys, claimed_sum, &mut verifier_ch);
        let (claim, _) = res.expect("valid proof must be accepted");
        assert_eq!(claim, final_eval);
    }

    #[test]
    fn test_verify_rejects_wrong_initial_claim() {
        let evals = vec![F::ZERO, F::ONE, F::ONE, F::ZERO];
        let mut prover_ch = XorChannel::default();
        let (round_polys, _, _) = prove_single_d(&evals, 2, &mut prover_ch);

        let mut verifier_ch = XorChannel::default();
        assert!(verify_with_channel(&round_polys, F::ONE, &mut verifier_ch).is_none());
    }

    #[test]
    fn test_verify_larger_polynomial() {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let n = 6;
        let evals: Vec<F> = (0..(1 << n)).map(|_| F::from(rng.gen::<u128>())).collect();
        let claimed_sum = evals.iter().fold(F::ZERO, |a, &b| a + b);

        let mut prover_ch = XorChannel::default();
        let (round_polys, final_eval, _) = prove_single_d(&evals, 2, &mut prover_ch);

        let mut verifier_ch = XorChannel::default();
        let (claim, _) = verify_with_channel(&round_polys, claimed_sum, &mut verifier_ch).unwrap();
        assert_eq!(claim, final_eval);
    }

    #[test]
    fn test_verify_degree_7_round_polys() {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let n = 5;
        let evals: Vec<F> = (0..(1 << n)).map(|_| F::from(rng.gen::<u128>())).collect();
        let claimed_sum = evals.iter().fold(F::ZERO, |a, &b| a + b);

        let mut prover_ch = XorChannel::default();
        let (round_polys, final_eval, _) = prove_single_d(&evals, 7, &mut prover_ch);

        let mut verifier_ch = XorChannel::default();
        let (claim, _) = verify_with_channel(&round_polys, claimed_sum, &mut verifier_ch).unwrap();
        assert_eq!(claim, final_eval);
        for poly in &round_polys {
            assert_eq!(poly.degree(), 7);
        }
    }
}
