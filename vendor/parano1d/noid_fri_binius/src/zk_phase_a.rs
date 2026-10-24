// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Native Phase-A algebra for the future witness-hiding authorization capsule.
//!
//! Phase A proves the product-sum relation
//!
//! ```text
//! <O_gamma, t> = sum_x O_gamma(x) * t(x),
//! O_gamma       = (1 - gamma) * B + gamma * C,
//! ```
//!
//! where `B` is the 2^11-cell authorization bank, `C` is an independently
//! fresh equal-size companion, and `t` is the transparent post-claim linear
//! relation. In characteristic two the affine line is evaluated as
//! `B + gamma * (B + C)`.
//!
//! The sumcheck binds variables from HIGH to LOW: round zero binds logical
//! variable 10 and round ten binds logical variable 0. Caller challenges are
//! consequently supplied as `[s_10, ..., s_0]`. Every public terminal point
//! returned by this module is nevertheless canonical LOW-to-HIGH
//! `[s_0, ..., s_10]`, matching the Phase-B MLE and `upper[256]` convention.
//!
//! A degree-two round polynomial is serialized as exactly `(p(1), p(infinity))`,
//! with `p(infinity)` denoting its quadratic coefficient. The verifier
//! recovers `p(0) = claim + p(1)` from `p(0) + p(1) = claim`, and hence the
//! missing linear coefficient is `claim + p(infinity)`.
//!
//! # Soundness preconditions
//!
//! This module checks native algebra only. A sound protocol must additionally:
//!
//! - bind both `B` and `C` before deriving `t`, `sigma`, and `gamma`;
//! - derive `t` after absorbing every scalar claim that it batches;
//! - absorb `sigma = <C,t>` before sampling an unbiased `gamma`, resampling
//!   the two rejected endpoints without transcript ambiguity;
//! - derive each sumcheck challenge after absorbing that round's two fields;
//! - use an independently fresh, non-reused companion `C`; and
//! - prove in Phase B, under the same commitment and `gamma`, that its
//!   terminal value is the very same `O_gamma(s)` checked here.
//!
//! It is deliberately disconnected from the active proof, transcript, RNG,
//! wire format, and verifier.

use noid_core::mle::evaluate::evaluate_slice;
use noid_core::{Block128, TowerField};
use zeroize::{Zeroize, Zeroizing};

use crate::zk_affine_code::{AFFINE_CODE_MESSAGE_LEN, AFFINE_CODE_MESSAGE_LOG};
use crate::zk_capsule::ZK_AUTH_CAPSULE_GEOMETRY;

pub const PHASE_A_VARS: usize = AFFINE_CODE_MESSAGE_LOG;
pub const PHASE_A_ORACLE_LEN: usize = AFFINE_CODE_MESSAGE_LEN;
pub const PHASE_A_ROUND_DEGREE: usize = 2;
pub const PHASE_A_SERIALIZED_FIELDS_PER_ROUND: usize = 2;

const _: () = assert!(PHASE_A_VARS == 11);
const _: () = assert!(PHASE_A_ORACLE_LEN == 2_048);
const _: () = assert!(ZK_AUTH_CAPSULE_GEOMETRY.bank_log == PHASE_A_VARS);
const _: () = assert!(ZK_AUTH_CAPSULE_GEOMETRY.bank_len == PHASE_A_ORACLE_LEN);
const _: () = assert!(ZK_AUTH_CAPSULE_GEOMETRY.companion_bank_len == PHASE_A_ORACLE_LEN);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkPhaseAError {
    BankLength { expected: usize, actual: usize },
    CompanionLength { expected: usize, actual: usize },
    RelationLength { expected: usize, actual: usize },
    ChallengeCount { expected: usize, actual: usize },
    GammaZero,
    GammaOne,
    ProverRoundInvariant { round: usize },
    ProverTerminalInvariant,
    VirtualOracleClaimMismatch,
    TerminalProductMismatch,
}

/// The two scalar claims fixed before `gamma` is sampled.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ZkPhaseARelationClaims<F = Block128> {
    /// `b = <B,t>`.
    pub bank: F,
    /// `sigma = <C,t>`.
    pub companion: F,
}

/// Exactly two serialized field elements for one degree-two sumcheck round.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ZkPhaseARoundProof<F = Block128> {
    /// The round polynomial evaluated at one.
    pub at_one: F,
    /// The quadratic coefficient, equivalently the value at infinity.
    pub at_infinity: F,
}

impl<F: TowerField> ZkPhaseARoundProof<F> {
    /// Advance one verifier claim at the caller-supplied round challenge.
    ///
    /// In characteristic two, `p(0) = claim + p(1)` and the linear
    /// coefficient is `claim + p(infinity)`. Therefore
    ///
    /// `p(r) = p(0) + r*(claim + p(infinity)) + r^2*p(infinity)`.
    #[inline]
    pub fn evaluate_from_claim(self, claim: F, challenge: F) -> F {
        let at_zero = claim + self.at_one;
        let linear = claim + self.at_infinity;
        at_zero + challenge * linear + challenge * challenge * self.at_infinity
    }
}

/// The Phase-A sumcheck body. No terminal value is duplicated in this proof:
/// production Phase B must supply the linked `O_gamma(s)` claim.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ZkPhaseAProof<F = Block128> {
    pub rounds: [ZkPhaseARoundProof<F>; PHASE_A_VARS],
}

/// Native prover result. `terminal_oracle_value` is an internal hand-off to
/// Phase B, not an independently trusted opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkPhaseAProverOutput<F = Block128> {
    pub proof: ZkPhaseAProof<F>,
    pub relation_claims: ZkPhaseARelationClaims<F>,
    pub initial_claim: F,
    pub terminal_point: [F; PHASE_A_VARS],
    pub terminal_oracle_value: F,
}

/// Values reconstructed by native verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZkPhaseAVerifierOutput<F = Block128> {
    pub initial_claim: F,
    pub terminal_point: [F; PHASE_A_VARS],
    pub terminal_relation_value: F,
    pub terminal_oracle_value: F,
}

#[inline]
fn check_gamma<F: TowerField>(gamma: F) -> Result<(), ZkPhaseAError> {
    if gamma == F::ZERO {
        return Err(ZkPhaseAError::GammaZero);
    }
    if gamma == F::ONE {
        return Err(ZkPhaseAError::GammaOne);
    }
    Ok(())
}

#[inline]
fn check_len(
    actual: usize,
    error: impl FnOnce(usize, usize) -> ZkPhaseAError,
) -> Result<(), ZkPhaseAError> {
    if actual != PHASE_A_ORACLE_LEN {
        return Err(error(PHASE_A_ORACLE_LEN, actual));
    }
    Ok(())
}

fn check_input_lengths<F>(
    bank: &[Block128],
    companion: &[F],
    relation: &[F],
) -> Result<(), ZkPhaseAError> {
    check_len(bank.len(), |expected, actual| ZkPhaseAError::BankLength {
        expected,
        actual,
    })?;
    check_len(companion.len(), |expected, actual| {
        ZkPhaseAError::CompanionLength { expected, actual }
    })?;
    check_len(relation.len(), |expected, actual| {
        ZkPhaseAError::RelationLength { expected, actual }
    })
}

fn check_challenges<F>(challenges_high_to_low: &[F]) -> Result<(), ZkPhaseAError> {
    if challenges_high_to_low.len() != PHASE_A_VARS {
        return Err(ZkPhaseAError::ChallengeCount {
            expected: PHASE_A_VARS,
            actual: challenges_high_to_low.len(),
        });
    }
    Ok(())
}

/// Construct `O_gamma = B + gamma*(B+C)` in natural bank order.
pub fn phase_a_virtual_oracle<F>(
    bank: &[Block128],
    companion: &[F],
    gamma: F,
) -> Result<Vec<F>, ZkPhaseAError>
where
    F: TowerField + From<Block128>,
{
    check_gamma(gamma)?;
    check_len(bank.len(), |expected, actual| ZkPhaseAError::BankLength {
        expected,
        actual,
    })?;
    check_len(companion.len(), |expected, actual| {
        ZkPhaseAError::CompanionLength { expected, actual }
    })?;

    Ok(bank
        .iter()
        .zip(companion)
        .map(|(&b, &c)| {
            let b = F::from(b);
            b + gamma * (b + c)
        })
        .collect())
}

/// Compute `b=<B,t>` and `sigma=<C,t>`.
pub fn phase_a_relation_claims<F>(
    bank: &[Block128],
    companion: &[F],
    relation: &[F],
) -> Result<ZkPhaseARelationClaims<F>, ZkPhaseAError>
where
    F: TowerField + From<Block128>,
{
    check_input_lengths(bank, companion, relation)?;
    Ok(ZkPhaseARelationClaims {
        bank: inner_product_base(bank, relation),
        companion: inner_product(companion, relation),
    })
}

/// Combine `b` and `sigma` into `<O_gamma,t>`.
pub fn phase_a_initial_claim<F: TowerField>(
    claims: ZkPhaseARelationClaims<F>,
    gamma: F,
) -> Result<F, ZkPhaseAError> {
    check_gamma(gamma)?;
    Ok(claims.bank + gamma * (claims.bank + claims.companion))
}

/// Convert caller challenge order `[s_10,...,s_0]` to the canonical MLE point
/// `[s_0,...,s_10]`.
pub fn phase_a_terminal_point<F: Copy>(
    challenges_high_to_low: &[F],
) -> Result<[F; PHASE_A_VARS], ZkPhaseAError> {
    check_challenges(challenges_high_to_low)?;
    Ok(std::array::from_fn(|low_variable| {
        challenges_high_to_low[PHASE_A_VARS - 1 - low_variable]
    }))
}

/// Build the exact 11-round, degree-two product sumcheck while deriving each
/// challenge only after its two-field round message exists.
///
/// `challenge_after_round` is called exactly once per round, in HIGH-to-LOW
/// variable order.  A Fiat--Shamir caller must absorb `round_proof.at_one`
/// and `round_proof.at_infinity` inside that callback before returning the
/// next challenge.  Keeping this sequencing inside the prover loop prevents
/// a caller from pre-sampling all Phase-A challenges before the messages that
/// are supposed to bind them.
fn prove_phase_a_virtual_oracle_owned_adaptive<F>(
    mut oracle: Zeroizing<Vec<F>>,
    relation: &[F],
    relation_claims: ZkPhaseARelationClaims<F>,
    gamma: F,
    mut challenge_after_round: impl FnMut(usize, ZkPhaseARoundProof<F>) -> F,
) -> Result<ZkPhaseAProverOutput<F>, ZkPhaseAError>
where
    F: TowerField + Zeroize,
{
    check_len(oracle.len(), |expected, actual| ZkPhaseAError::BankLength {
        expected,
        actual,
    })?;
    check_len(relation.len(), |expected, actual| {
        ZkPhaseAError::RelationLength { expected, actual }
    })?;
    check_gamma(gamma)?;

    let initial_claim = phase_a_initial_claim(relation_claims, gamma)?;
    if inner_product(&oracle, relation) != initial_claim {
        return Err(ZkPhaseAError::VirtualOracleClaimMismatch);
    }
    let mut relation_folded = Zeroizing::new(relation.to_vec());
    let mut running_claim = initial_claim;
    let mut rounds = [ZkPhaseARoundProof::default(); PHASE_A_VARS];
    let mut challenges_high_to_low = [F::ZERO; PHASE_A_VARS];

    for round in 0..PHASE_A_VARS {
        let half = oracle.len() / 2;
        let mut at_zero = F::ZERO;
        let mut linear = F::ZERO;
        let mut at_infinity = F::ZERO;

        // HIGH-to-LOW binding pairs the two halves. The surviving index bits
        // remain in canonical natural order for the lower variables.
        for low_index in 0..half {
            let oracle_zero = oracle[low_index];
            let oracle_delta = oracle_zero + oracle[low_index + half];
            let relation_zero = relation_folded[low_index];
            let relation_delta = relation_zero + relation_folded[low_index + half];

            at_zero += oracle_zero * relation_zero;
            linear += oracle_zero * relation_delta + oracle_delta * relation_zero;
            at_infinity += oracle_delta * relation_delta;
        }

        let at_one = at_zero + linear + at_infinity;
        if at_zero + at_one != running_claim {
            return Err(ZkPhaseAError::ProverRoundInvariant { round });
        }

        let round_proof = ZkPhaseARoundProof {
            at_one,
            at_infinity,
        };
        let challenge = challenge_after_round(round, round_proof);
        running_claim = round_proof.evaluate_from_claim(running_claim, challenge);
        rounds[round] = round_proof;
        challenges_high_to_low[round] = challenge;
        fold_highest_variable(&mut oracle, challenge);
        fold_highest_variable(&mut relation_folded, challenge);
    }

    let terminal_oracle_value = oracle[0];
    if relation_folded.len() != 1 || running_claim != relation_folded[0] * terminal_oracle_value {
        return Err(ZkPhaseAError::ProverTerminalInvariant);
    }

    Ok(ZkPhaseAProverOutput {
        proof: ZkPhaseAProof { rounds },
        relation_claims,
        initial_claim,
        terminal_point: phase_a_terminal_point(&challenges_high_to_low)?,
        terminal_oracle_value,
    })
}

/// Build Phase A from an already sampled virtual oracle `O_gamma`.
///
/// This is the exact interactive algebra needed by a witness-free simulator:
/// the caller supplies only a complete oracle on the affine fiber fixed by
/// `relation_claims` and `gamma`.  The initial inner product is checked before
/// any round message is released, and the oracle copy is zeroized after the
/// adaptive sumcheck.  Production authorization still reaches the same core
/// through [`prove_phase_a_adaptive`] and its consuming PCS typestate.
pub fn prove_phase_a_from_virtual_oracle_adaptive<F>(
    virtual_oracle: &[F],
    relation: &[F],
    relation_claims: ZkPhaseARelationClaims<F>,
    gamma: F,
    challenge_after_round: impl FnMut(usize, ZkPhaseARoundProof<F>) -> F,
) -> Result<ZkPhaseAProverOutput<F>, ZkPhaseAError>
where
    F: TowerField + Zeroize,
{
    prove_phase_a_virtual_oracle_owned_adaptive(
        Zeroizing::new(virtual_oracle.to_vec()),
        relation,
        relation_claims,
        gamma,
        challenge_after_round,
    )
}

pub fn prove_phase_a_adaptive<F>(
    bank: &[Block128],
    companion: &[F],
    relation: &[F],
    gamma: F,
    challenge_after_round: impl FnMut(usize, ZkPhaseARoundProof<F>) -> F,
) -> Result<ZkPhaseAProverOutput<F>, ZkPhaseAError>
where
    F: TowerField + From<Block128> + Zeroize,
{
    check_input_lengths(bank, companion, relation)?;
    let relation_claims = phase_a_relation_claims(bank, companion, relation)?;
    let virtual_oracle = Zeroizing::new(phase_a_virtual_oracle(bank, companion, gamma)?);
    prove_phase_a_virtual_oracle_owned_adaptive(
        virtual_oracle,
        relation,
        relation_claims,
        gamma,
        challenge_after_round,
    )
}

/// Build Phase A with an explicit, already derived HIGH-to-LOW challenge
/// vector.  This transcript-free adapter is retained for algebra tests and
/// verifier differentials; production Fiat--Shamir proving should use
/// [`prove_phase_a_adaptive`].
pub fn prove_phase_a<F>(
    bank: &[Block128],
    companion: &[F],
    relation: &[F],
    gamma: F,
    challenges_high_to_low: &[F],
) -> Result<ZkPhaseAProverOutput<F>, ZkPhaseAError>
where
    F: TowerField + From<Block128> + Zeroize,
{
    check_challenges(challenges_high_to_low)?;
    prove_phase_a_adaptive(bank, companion, relation, gamma, |round, _proof| {
        challenges_high_to_low[round]
    })
}

/// Verify Phase A against the Phase-B-supplied `terminal_oracle_value`.
///
/// The transparent terminal `t(s)` is recomputed locally. Acceptance is the
/// single final equality `running_claim == t(s) * O_gamma(s)` after replaying
/// all eleven round messages.
pub fn verify_phase_a<F>(
    proof: &ZkPhaseAProof<F>,
    relation_claims: ZkPhaseARelationClaims<F>,
    relation: &[F],
    gamma: F,
    challenges_high_to_low: &[F],
    terminal_oracle_value: F,
) -> Result<ZkPhaseAVerifierOutput<F>, ZkPhaseAError>
where
    F: TowerField,
{
    check_gamma(gamma)?;
    check_len(relation.len(), |expected, actual| {
        ZkPhaseAError::RelationLength { expected, actual }
    })?;
    check_challenges(challenges_high_to_low)?;
    let initial_claim = phase_a_initial_claim(relation_claims, gamma)?;
    let mut running_claim = initial_claim;
    for (&challenge, &round) in challenges_high_to_low.iter().zip(&proof.rounds) {
        running_claim = round.evaluate_from_claim(running_claim, challenge);
    }

    let terminal_point = phase_a_terminal_point(challenges_high_to_low)?;
    let terminal_relation_value = evaluate_slice(relation, &terminal_point);
    if running_claim != terminal_relation_value * terminal_oracle_value {
        return Err(ZkPhaseAError::TerminalProductMismatch);
    }

    Ok(ZkPhaseAVerifierOutput {
        initial_claim,
        terminal_point,
        terminal_relation_value,
        terminal_oracle_value,
    })
}

#[inline]
fn inner_product<F: TowerField>(left: &[F], right: &[F]) -> F {
    left.iter()
        .zip(right)
        .fold(F::ZERO, |sum, (&x, &y)| sum + x * y)
}

fn inner_product_base<F>(left: &[Block128], right: &[F]) -> F
where
    F: TowerField + From<Block128>,
{
    left.iter()
        .zip(right)
        .fold(F::ZERO, |sum, (&x, &y)| sum + F::from(x) * y)
}

/// Bind the highest remaining natural-order MLE variable.
fn fold_highest_variable<F: TowerField + Zeroize>(values: &mut Zeroizing<Vec<F>>, challenge: F) {
    debug_assert!(values.len().is_power_of_two() && values.len() >= 2);
    let half = values.len() / 2;
    for low_index in 0..half {
        let at_zero = values[low_index];
        let at_one = values[low_index + half];
        values[low_index] = at_zero + challenge * (at_zero + at_one);
    }
    for value in &mut values[half..] {
        value.zeroize();
    }
    values.truncate(half);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zk_capsule_algebra::{
        contract_high3_for_each_low8, evaluate_upper_at_low8, PHASE_B_HIGH_VARS, PHASE_B_LOW_VARS,
    };

    fn elem(index: usize, domain: u128) -> Block128 {
        Block128::from(
            domain
                .wrapping_mul(index as u128 + 1)
                .rotate_left((index % 127) as u32)
                ^ (index as u128 * 0x9E37_79B9),
        )
    }

    fn table(domain: u128) -> [Block128; PHASE_A_ORACLE_LEN] {
        std::array::from_fn(|index| elem(index, domain))
    }

    fn challenges() -> [Block128; PHASE_A_VARS] {
        std::array::from_fn(|round| elem(round + 31, 0xC4A1_1E6E))
    }

    fn gamma() -> Block128 {
        elem(19, 0x0006_A77A)
    }

    #[test]
    fn honest_product_sumcheck_reaches_transparent_terminal_product() {
        let bank = table(0xB4A9);
        let companion = table(0xC09A);
        let relation = table(0x7E1A710);
        let challenges = challenges();
        let gamma = gamma();

        let output = prove_phase_a(&bank, &companion, &relation, gamma, &challenges).unwrap();
        assert_eq!(output.proof.rounds.len(), PHASE_A_VARS);
        assert_eq!(PHASE_A_SERIALIZED_FIELDS_PER_ROUND, 2);

        let virtual_oracle = phase_a_virtual_oracle(&bank, &companion, gamma).unwrap();
        assert_eq!(
            output.initial_claim,
            inner_product(&virtual_oracle, &relation)
        );
        assert_eq!(
            output.terminal_oracle_value,
            evaluate_slice(&virtual_oracle, &output.terminal_point)
        );

        let verified = verify_phase_a(
            &output.proof,
            output.relation_claims,
            &relation,
            gamma,
            &challenges,
            output.terminal_oracle_value,
        )
        .unwrap();
        assert_eq!(verified.initial_claim, output.initial_claim);
        assert_eq!(verified.terminal_point, output.terminal_point);
        assert_eq!(
            verified.terminal_relation_value,
            evaluate_slice(&relation, &output.terminal_point)
        );
    }

    #[test]
    fn adaptive_driver_receives_each_round_before_deriving_its_challenge() {
        let bank = table(0xB4A9);
        let companion = table(0xC09A);
        let relation = table(0x7E1A710);
        let challenges = challenges();
        let gamma = gamma();
        let mut observed = Vec::new();

        let adaptive =
            prove_phase_a_adaptive(&bank, &companion, &relation, gamma, |round, proof| {
                assert_eq!(round, observed.len());
                observed.push(proof);
                challenges[round]
            })
            .unwrap();
        let explicit = prove_phase_a(&bank, &companion, &relation, gamma, &challenges).unwrap();

        assert_eq!(observed, adaptive.proof.rounds);
        assert_eq!(adaptive, explicit);
    }

    #[test]
    fn virtual_oracle_driver_is_the_same_phase_a_relation() {
        let bank = table(0xB4A9);
        let companion = table(0xC09A);
        let relation = table(0x7E1A710);
        let challenges = challenges();
        let gamma = gamma();
        let explicit = prove_phase_a(&bank, &companion, &relation, gamma, &challenges).unwrap();
        let virtual_oracle = phase_a_virtual_oracle(&bank, &companion, gamma).unwrap();

        let from_virtual = prove_phase_a_from_virtual_oracle_adaptive(
            &virtual_oracle,
            &relation,
            explicit.relation_claims,
            gamma,
            |round, _proof| challenges[round],
        )
        .unwrap();

        assert_eq!(from_virtual, explicit);
    }

    #[test]
    fn virtual_oracle_driver_rejects_the_wrong_affine_fiber_before_round_zero() {
        let bank = table(0xB4A9);
        let companion = table(0xC09A);
        let relation = table(0x7E1A710);
        let gamma = gamma();
        let virtual_oracle = phase_a_virtual_oracle(&bank, &companion, gamma).unwrap();
        let mut claims = phase_a_relation_claims(&bank, &companion, &relation).unwrap();
        claims.bank += Block128::ONE;
        let mut callback_calls = 0usize;

        assert_eq!(
            prove_phase_a_from_virtual_oracle_adaptive(
                &virtual_oracle,
                &relation,
                claims,
                gamma,
                |_round, _proof| {
                    callback_calls += 1;
                    Block128::ZERO
                },
            ),
            Err(ZkPhaseAError::VirtualOracleClaimMismatch)
        );
        assert_eq!(callback_calls, 0);
    }

    #[test]
    fn tampered_round_or_terminal_value_is_rejected() {
        let bank = table(0xB4A9);
        let companion = table(0xC09A);
        let relation = table(0x7E1A710);
        let challenges = challenges();
        let gamma = gamma();
        let output = prove_phase_a(&bank, &companion, &relation, gamma, &challenges).unwrap();

        let mut bad_round = output.proof.clone();
        bad_round.rounds[5].at_one += Block128::ONE;
        assert_eq!(
            verify_phase_a(
                &bad_round,
                output.relation_claims,
                &relation,
                gamma,
                &challenges,
                output.terminal_oracle_value,
            ),
            Err(ZkPhaseAError::TerminalProductMismatch)
        );

        assert_eq!(
            verify_phase_a(
                &output.proof,
                output.relation_claims,
                &relation,
                gamma,
                &challenges,
                output.terminal_oracle_value + Block128::ONE,
            ),
            Err(ZkPhaseAError::TerminalProductMismatch)
        );
    }

    #[test]
    fn affine_line_endpoints_are_rejected() {
        let bank = table(0xB4A9);
        let companion = table(0xC09A);
        let relation = table(0x7E1A710);
        let challenges = challenges();

        assert_eq!(
            phase_a_virtual_oracle(&bank, &companion, Block128::ZERO),
            Err(ZkPhaseAError::GammaZero)
        );
        assert_eq!(
            phase_a_virtual_oracle(&bank, &companion, Block128::ONE),
            Err(ZkPhaseAError::GammaOne)
        );
        assert_eq!(
            prove_phase_a(&bank, &companion, &relation, Block128::ZERO, &challenges,),
            Err(ZkPhaseAError::GammaZero)
        );
        assert_eq!(
            prove_phase_a(&bank, &companion, &relation, Block128::ONE, &challenges,),
            Err(ZkPhaseAError::GammaOne)
        );
    }

    #[test]
    fn high_to_low_round_order_returns_canonical_low_to_high_point() {
        let bank = table(0xB4A9);
        let companion = table(0xC09A);
        let relation = table(0x7E1A710);
        let challenges = challenges();
        let gamma = gamma();
        let expected_point = std::array::from_fn(|low| challenges[PHASE_A_VARS - 1 - low]);

        assert_eq!(phase_a_terminal_point(&challenges).unwrap(), expected_point);

        let output = prove_phase_a(&bank, &companion, &relation, gamma, &challenges).unwrap();
        let virtual_oracle = phase_a_virtual_oracle(&bank, &companion, gamma).unwrap();
        assert_eq!(output.terminal_point, expected_point);
        assert_eq!(
            output.terminal_oracle_value,
            evaluate_slice(&virtual_oracle, &expected_point)
        );
        assert_ne!(
            output.terminal_oracle_value,
            evaluate_slice(&virtual_oracle, &challenges)
        );
    }

    #[test]
    fn phase_a_terminal_v_is_the_same_phase_b_upper256_oracle_value() {
        let bank = table(0xB4A9);
        let companion = table(0xC09A);
        let relation = table(0x7E1A710);
        let challenges = challenges();
        let gamma = gamma();
        let output = prove_phase_a(&bank, &companion, &relation, gamma, &challenges).unwrap();

        let virtual_oracle: [Block128; PHASE_A_ORACLE_LEN] =
            phase_a_virtual_oracle(&bank, &companion, gamma)
                .unwrap()
                .try_into()
                .unwrap();
        let low: [Block128; PHASE_B_LOW_VARS] = std::array::from_fn(|i| output.terminal_point[i]);
        let high: [Block128; PHASE_B_HIGH_VARS] =
            std::array::from_fn(|i| output.terminal_point[PHASE_B_LOW_VARS + i]);
        let upper256 = contract_high3_for_each_low8(&virtual_oracle, &high);

        assert_eq!(
            output.terminal_oracle_value,
            evaluate_upper_at_low8(&upper256, &low)
        );
    }
}
