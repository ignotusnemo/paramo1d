// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Disconnected recursive trace twin of the degree-ten ZK MLE-check verifier.
//!
//! This module mirrors [`noid_gkr::zk_mlecheck::ZkMleCheckVerifierState`]
//! without owning a transcript. The caller supplies every statement value,
//! proof coefficient, and sampled challenge as a [`LinExpr`]. In particular,
//! neither the input point nor the terminal point is converted into a
//! build-time constant, so the matrix is fixed across proof contents.
//!
//! The production entry point is [`verify_zk_mlecheck_trace`]. Its array types
//! freeze the verifier at eleven high-to-low rounds and ten serialized
//! nonconstant coefficients per round. The caller must independently derive
//! and constrain `expected_main_final`; this gate only pins the unbatched
//! telescope result to that supplied expression.

use noid_gkr::zk_mlecheck::{ZK_MLECHECK_N_VARS, ZK_MLECHECK_ROUND_PROOF_COEFFS};

use super::{mul_ext, pin_eq_ext, ExtExpr, FieldR1csBuilder, F256};

/// One product for `lambda * mask_mle_eval`.
pub const ZK_MLECHECK_INIT_ROWS: usize = 3;
/// One endpoint-recovery product plus ten Horner products.
pub const ZK_MLECHECK_ROWS_PER_ROUND: usize = 3 * (1 + ZK_MLECHECK_ROUND_PROOF_COEFFS);
/// Eleven fixed rounds of the degree-ten telescope.
pub const ZK_MLECHECK_ROUND_ROWS: usize = ZK_MLECHECK_N_VARS * ZK_MLECHECK_ROWS_PER_ROUND;
/// One product for `lambda * mask_final_eval`.
pub const ZK_MLECHECK_UNBATCH_ROWS: usize = 3;
/// One equality pin against the independently supplied main terminal value.
pub const ZK_MLECHECK_FINAL_PIN_ROWS: usize = 2;
/// Exact incremental verifier ledger, excluding caller-owned witness inputs.
pub const ZK_MLECHECK_VERIFIER_ROWS: usize = ZK_MLECHECK_INIT_ROWS
    + ZK_MLECHECK_ROUND_ROWS
    + ZK_MLECHECK_UNBATCH_ROWS
    + ZK_MLECHECK_FINAL_PIN_ROWS;

const _: () = assert!(ZK_MLECHECK_N_VARS == 11);
const _: () = assert!(ZK_MLECHECK_ROUND_PROOF_COEFFS == 10);
const _: () = assert!(ZK_MLECHECK_ROWS_PER_ROUND == 33);
const _: () = assert!(ZK_MLECHECK_VERIFIER_ROWS == 371);

/// Dynamic field whose accidental constant embedding would change the frozen
/// recursive matrix. Round-coefficient indices are flattened as
/// `round * 10 + coefficient`, both zero-based.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkMleCheckTraceDynamicInput {
    InputPoint,
    MaskMleEval,
    Lambda,
    RoundCoefficient,
    Challenge,
    MaskFinalEval,
    ExpectedMainFinal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkMleCheckTraceError {
    /// A transcript/proof value was accidentally embedded in the matrix as a
    /// build-time constant instead of entering through an allocated wire.
    DynamicInputIsConstant {
        input: ZkMleCheckTraceDynamicInput,
        index: usize,
    },
    /// AuthGKR permits the protocol-owned zero main claim, but no other
    /// constant main claim is part of this trace class.
    NonzeroConstantMainClaim,
}

/// Fixed-shape recursive representation of one serialized MLE-check round.
#[derive(Clone, Debug)]
pub struct ZkMleCheckRoundProofTrace {
    /// Witness expressions `[a_1, ..., a_10]`; `a_0` is reconstructed.
    pub coeffs_without_constant: [ExtExpr; ZK_MLECHECK_ROUND_PROOF_COEFFS],
}

/// Fixed-shape disconnected verifier inputs.
///
/// Challenges are listed in transcript/round order: entry zero binds variable
/// ten, and entry ten binds variable zero. `input_point` and the output point
/// use canonical low-to-high variable order.
#[derive(Clone, Debug)]
pub struct ZkMleCheckVerifierTraceInputs {
    pub input_point: [ExtExpr; ZK_MLECHECK_N_VARS],
    pub main_claim: ExtExpr,
    pub mask_mle_eval: ExtExpr,
    pub lambda: ExtExpr,
    pub rounds: [ZkMleCheckRoundProofTrace; ZK_MLECHECK_N_VARS],
    pub challenges: [ExtExpr; ZK_MLECHECK_N_VARS],
    pub mask_final_eval: ExtExpr,
    /// Must be computed and bound independently by the surrounding trace.
    pub expected_main_final: ExtExpr,
}

/// Output aliases and derived expressions after the final equality pin.
#[derive(Clone, Debug)]
pub struct ZkMleCheckVerifierOutputTrace {
    /// Unbatched main-polynomial terminal evaluation.
    pub main_eval: ExtExpr,
    /// Alias of the caller-supplied final mask evaluation.
    pub mask_eval: ExtExpr,
    /// Canonical low-to-high point, despite high-to-low round execution.
    pub terminal_point: [ExtExpr; ZK_MLECHECK_N_VARS],
}

fn check_dynamic(
    expression: &ExtExpr,
    input: ZkMleCheckTraceDynamicInput,
    index: usize,
) -> Result<(), ZkMleCheckTraceError> {
    if expression.is_const() {
        Err(ZkMleCheckTraceError::DynamicInputIsConstant { input, index })
    } else {
        Ok(())
    }
}

/// Reject matrix-content substitutions before the first verifier row is
/// appended. A dynamic main claim is accepted; the only constant exception is
/// the exact protocol-owned zero used by the real AuthGKR relation.
fn preflight_dynamic_inputs(
    inputs: &ZkMleCheckVerifierTraceInputs,
) -> Result<(), ZkMleCheckTraceError> {
    for (variable, coordinate) in inputs.input_point.iter().enumerate() {
        check_dynamic(
            coordinate,
            ZkMleCheckTraceDynamicInput::InputPoint,
            variable,
        )?;
    }
    if inputs.main_claim.is_const() && inputs.main_claim.constant_value() != Some(F256::ZERO) {
        return Err(ZkMleCheckTraceError::NonzeroConstantMainClaim);
    }
    check_dynamic(
        &inputs.mask_mle_eval,
        ZkMleCheckTraceDynamicInput::MaskMleEval,
        0,
    )?;
    check_dynamic(&inputs.lambda, ZkMleCheckTraceDynamicInput::Lambda, 0)?;
    for round in 0..ZK_MLECHECK_N_VARS {
        for coefficient in 0..ZK_MLECHECK_ROUND_PROOF_COEFFS {
            check_dynamic(
                &inputs.rounds[round].coeffs_without_constant[coefficient],
                ZkMleCheckTraceDynamicInput::RoundCoefficient,
                round * ZK_MLECHECK_ROUND_PROOF_COEFFS + coefficient,
            )?;
        }
        check_dynamic(
            &inputs.challenges[round],
            ZkMleCheckTraceDynamicInput::Challenge,
            round,
        )?;
    }
    check_dynamic(
        &inputs.mask_final_eval,
        ZkMleCheckTraceDynamicInput::MaskFinalEval,
        0,
    )?;
    check_dynamic(
        &inputs.expected_main_final,
        ZkMleCheckTraceDynamicInput::ExpectedMainFinal,
        0,
    )
}

/// Stateful line-by-line twin of the native verifier telescope.
///
/// Production callers should use [`verify_zk_mlecheck_trace`], whose fixed
/// arrays make an incomplete or oversized round sequence unrepresentable.
struct ZkMleCheckVerifierStateTrace {
    input_point: [ExtExpr; ZK_MLECHECK_N_VARS],
    lambda: ExtExpr,
    running_claim: ExtExpr,
    completed_rounds: usize,
    terminal_point: [Option<ExtExpr>; ZK_MLECHECK_N_VARS],
}

impl ZkMleCheckVerifierStateTrace {
    fn new(
        b: &mut FieldR1csBuilder,
        input_point: &[ExtExpr; ZK_MLECHECK_N_VARS],
        main_claim: &ExtExpr,
        mask_mle_eval: &ExtExpr,
        lambda: &ExtExpr,
    ) -> Self {
        // Use the raw builder product throughout this fixed ledger. Preflight
        // rejects direct constant substitution; raw products additionally
        // preserve the row if a protocol-fixed affine combination happens to
        // simplify syntactically.
        let batched_mask = mul_ext(b, lambda, mask_mle_eval);
        Self {
            input_point: input_point.clone(),
            lambda: lambda.clone(),
            running_claim: main_claim.add(&batched_mask),
            completed_rounds: 0,
            terminal_point: std::array::from_fn(|_| None),
        }
    }

    /// Recover `a_0` from the MLE endpoint identity, then evaluate the full
    /// degree-ten polynomial at the witness challenge via Horner's rule.
    fn transition(
        &mut self,
        b: &mut FieldR1csBuilder,
        round: &ZkMleCheckRoundProofTrace,
        challenge: &ExtExpr,
    ) {
        assert!(
            self.completed_rounds < ZK_MLECHECK_N_VARS,
            "ZK MLE-check round exhausted"
        );
        let var_index = ZK_MLECHECK_N_VARS - 1 - self.completed_rounds;
        let alpha = &self.input_point[var_index];

        let nonconstant_sum = round
            .coeffs_without_constant
            .iter()
            .fold(ExtExpr::zero(), |sum, coeff| sum.add(coeff));
        // Subtraction is addition in characteristic two. This is the one
        // endpoint-recovery product charged by each round.
        let recovered_product = mul_ext(b, alpha, &nonconstant_sum);
        let a0 = self.running_claim.add(&recovered_product);

        // Exactly ten products for a degree-ten Horner evaluation. Start at
        // a_10, consume a_9 through a_1, then append recovered a_0.
        let mut evaluation =
            round.coeffs_without_constant[ZK_MLECHECK_ROUND_PROOF_COEFFS - 1].clone();
        for coeff in round.coeffs_without_constant[..ZK_MLECHECK_ROUND_PROOF_COEFFS - 1]
            .iter()
            .rev()
        {
            evaluation = mul_ext(b, &evaluation, challenge).add(coeff);
        }
        evaluation = mul_ext(b, &evaluation, challenge).add(&a0);

        self.running_claim = evaluation;
        self.terminal_point[var_index] = Some(challenge.clone());
        self.completed_rounds += 1;
    }

    fn finish_checked(
        self,
        b: &mut FieldR1csBuilder,
        mask_final_eval: &ExtExpr,
        expected_main_final: &ExtExpr,
    ) -> ZkMleCheckVerifierOutputTrace {
        assert_eq!(
            self.completed_rounds, ZK_MLECHECK_N_VARS,
            "ZK MLE-check rounds incomplete"
        );

        let unbatched_mask = mul_ext(b, &self.lambda, mask_final_eval);
        let main_eval = self.running_claim.add(&unbatched_mask);
        pin_eq_ext(b, &main_eval, expected_main_final);

        ZkMleCheckVerifierOutputTrace {
            main_eval,
            mask_eval: mask_final_eval.clone(),
            terminal_point: self.terminal_point.map(|coordinate| {
                coordinate.expect("all terminal coordinates assigned by fixed rounds")
            }),
        }
    }
}

/// Verify the complete disconnected ZK MLE-check telescope in a fixed trace.
///
/// This function performs exactly [`ZK_MLECHECK_VERIFIER_ROWS`] incremental
/// allocations when all supplied values are witness expressions: 1 init
/// product, 11 endpoint-recovery products, 110 Horner products, 1 unbatch
/// product, and 1 final equality pin.
pub fn verify_zk_mlecheck_trace(
    b: &mut FieldR1csBuilder,
    inputs: &ZkMleCheckVerifierTraceInputs,
) -> Result<ZkMleCheckVerifierOutputTrace, ZkMleCheckTraceError> {
    preflight_dynamic_inputs(inputs)?;

    let trace_start = b.num_wires();
    let mut state = ZkMleCheckVerifierStateTrace::new(
        b,
        &inputs.input_point,
        &inputs.main_claim,
        &inputs.mask_mle_eval,
        &inputs.lambda,
    );
    for (round, challenge) in inputs.rounds.iter().zip(&inputs.challenges) {
        state.transition(b, round, challenge);
    }
    let output = state.finish_checked(b, &inputs.mask_final_eval, &inputs.expected_main_final);
    debug_assert_eq!(b.num_wires() - trace_start, ZK_MLECHECK_VERIFIER_ROWS);
    Ok(output)
}

#[cfg(test)]
mod tests {
    use noid_core::{Block128, Block256, TowerField};
    use noid_gkr::zk_mlecheck::{
        combine_main_and_mask_round, ZkMleCheckMaskView, ZkMleCheckRoundProof,
        ZkMleCheckVerifierState, ZK_MLECHECK_MASK_LEN,
    };

    use super::super::{alloc_block256, const_block256, test_support::assert_ext_expr_is};
    use super::*;

    fn elem(index: usize, domain: u128) -> Block128 {
        Block128::from(
            domain
                .wrapping_mul(index as u128 + 1)
                .rotate_left((index % 127) as u32)
                ^ (index as u128 * 0x9E37_79B9_7F4A_7C15),
        )
    }

    fn cells(domain: u128) -> [Block128; ZK_MLECHECK_MASK_LEN] {
        std::array::from_fn(|index| elem(index, domain))
    }

    fn ext_elem(index: usize, domain: u128) -> Block256 {
        Block256::new(elem(index, domain), elem(index + 83, domain ^ 0xC1_256))
    }

    fn point(domain: u128) -> [Block256; ZK_MLECHECK_N_VARS] {
        std::array::from_fn(|index| ext_elem(index + 31, domain))
    }

    #[derive(Clone)]
    struct NativeFixture {
        input_point: [Block256; ZK_MLECHECK_N_VARS],
        main_claim: Block256,
        mask_claim: Block256,
        lambda: Block256,
        challenges: [Block256; ZK_MLECHECK_N_VARS],
        proofs: [ZkMleCheckRoundProof<Block256>; ZK_MLECHECK_N_VARS],
        main_final: Block256,
        mask_final: Block256,
    }

    /// Same honest two-separable-polynomial construction as the native
    /// `zk_mlecheck` verifier fixture, parameterized only for the matrix
    /// content-invariance check below.
    fn honest_fixture(salt: u128) -> NativeFixture {
        let main_cells = cells(0xA11CE ^ salt.rotate_left(7));
        let mask_cells = cells(0x6A5C ^ salt.rotate_left(19));
        let main = ZkMleCheckMaskView::checked(&main_cells).unwrap();
        let mask = ZkMleCheckMaskView::checked(&mask_cells).unwrap();
        let input_point = point(0x1A907 ^ salt.rotate_left(31));
        let lambda = ext_elem(77, 0x1A4BDA ^ salt.rotate_left(43));
        let challenges = point(0xC4A11 ^ salt.rotate_left(59));
        let main_claim = main.evaluate_mle(&input_point);
        let mask_claim = mask.evaluate_mle(&input_point);

        let proofs: [ZkMleCheckRoundProof<Block256>; ZK_MLECHECK_N_VARS] =
            std::array::from_fn(|round_index| {
                let main_round = main
                    .round_coefficients(&input_point, &challenges[..round_index])
                    .unwrap();
                let mask_round = mask
                    .round_coefficients(&input_point, &challenges[..round_index])
                    .unwrap();
                let combined = combine_main_and_mask_round(
                    &main_round.as_round_polynomial(),
                    &mask_round,
                    lambda,
                )
                .unwrap();
                ZkMleCheckRoundProof::truncate(&combined).unwrap()
            });

        let terminal_point =
            std::array::from_fn(|var_index| challenges[ZK_MLECHECK_N_VARS - 1 - var_index]);
        NativeFixture {
            input_point,
            main_claim,
            mask_claim,
            lambda,
            challenges,
            proofs,
            main_final: main.evaluate_final(&terminal_point),
            mask_final: mask.evaluate_final(&terminal_point),
        }
    }

    fn native_output(
        fixture: &NativeFixture,
    ) -> noid_gkr::zk_mlecheck::ZkMleCheckVerifierOutput<Block256> {
        let mut state = ZkMleCheckVerifierState::new(
            fixture.input_point,
            fixture.main_claim,
            fixture.mask_claim,
            fixture.lambda,
        );
        for (round, challenge) in fixture.proofs.iter().zip(fixture.challenges) {
            state.transition(round, challenge).unwrap();
        }
        state
            .finish_checked(fixture.mask_final, fixture.main_final)
            .unwrap()
    }

    fn alloc_inputs(
        b: &mut FieldR1csBuilder,
        fixture: &NativeFixture,
    ) -> ZkMleCheckVerifierTraceInputs {
        let input_point =
            std::array::from_fn(|index| alloc_block256(b, fixture.input_point[index]));
        let main_claim = alloc_block256(b, fixture.main_claim);
        let mask_mle_eval = alloc_block256(b, fixture.mask_claim);
        let lambda = alloc_block256(b, fixture.lambda);
        let rounds = std::array::from_fn(|round| ZkMleCheckRoundProofTrace {
            coeffs_without_constant: std::array::from_fn(|coefficient| {
                alloc_block256(
                    b,
                    fixture.proofs[round].coeffs_without_constant[coefficient],
                )
            }),
        });
        let challenges = std::array::from_fn(|round| alloc_block256(b, fixture.challenges[round]));
        let mask_final_eval = alloc_block256(b, fixture.mask_final);
        let expected_main_final = alloc_block256(b, fixture.main_final);

        ZkMleCheckVerifierTraceInputs {
            input_point,
            main_claim,
            mask_mle_eval,
            lambda,
            rounds,
            challenges,
            mask_final_eval,
            expected_main_final,
        }
    }

    fn build_trace(
        fixture: &NativeFixture,
    ) -> (
        noid_ivc_core::field_r1cs::FieldR1cs,
        Vec<noid_ivc_core::field::F128>,
        usize,
        [Block256; ZK_MLECHECK_N_VARS],
        Block256,
        Block256,
    ) {
        let mut b = FieldR1csBuilder::new();
        let inputs = alloc_inputs(&mut b, fixture);
        let before = b.num_wires();
        let output = verify_zk_mlecheck_trace(&mut b, &inputs).expect("dynamic trace inputs");
        let verifier_rows = b.num_wires() - before;
        let terminal_point = std::array::from_fn(|index| {
            super::super::test_support::tower_value_ext(&b, &output.terminal_point[index])
        });
        let main_eval = super::super::test_support::tower_value_ext(&b, &output.main_eval);
        let mask_eval = super::super::test_support::tower_value_ext(&b, &output.mask_eval);
        let (r1cs, witness) = b.build();
        (
            r1cs,
            witness,
            verifier_rows,
            terminal_point,
            main_eval,
            mask_eval,
        )
    }

    #[test]
    fn recursive_telescope_matches_native_and_exact_row_ledger() {
        let fixture = honest_fixture(0);
        let native = native_output(&fixture);

        let mut b = FieldR1csBuilder::new();
        let inputs = alloc_inputs(&mut b, &fixture);
        let before = b.num_wires();
        let output = verify_zk_mlecheck_trace(&mut b, &inputs).expect("dynamic trace inputs");
        assert_eq!(b.num_wires() - before, ZK_MLECHECK_VERIFIER_ROWS);
        assert_ext_expr_is(&b, &output.main_eval, native.main_eval, "main terminal");
        assert_ext_expr_is(&b, &output.mask_eval, native.mask_eval, "mask terminal");
        for (index, coordinate) in output.terminal_point.iter().enumerate() {
            assert_ext_expr_is(
                &b,
                coordinate,
                native.terminal_point[index],
                "terminal coordinate",
            );
            assert_eq!(
                native.terminal_point[index],
                fixture.challenges[ZK_MLECHECK_N_VARS - 1 - index],
                "terminal point must be canonical low-to-high",
            );
        }
        let (r1cs, witness) = b.build();
        assert!(r1cs.satisfies(&witness), "honest MLE-check trace failed");
    }

    #[test]
    fn coeff_challenge_mask_and_main_tampers_are_rejected() {
        let honest = honest_fixture(0);
        let assert_rejected = |candidate: NativeFixture, what: &str| {
            let (r1cs, witness, rows, ..) = build_trace(&candidate);
            assert_eq!(rows, ZK_MLECHECK_VERIFIER_ROWS, "{what} changed rows");
            assert!(!r1cs.satisfies(&witness), "{what} satisfied the trace");
        };

        let mut candidate = honest.clone();
        candidate.proofs[4].coeffs_without_constant[7] += Block256::ONE;
        assert_rejected(candidate, "round coefficient tamper");

        let mut candidate = honest.clone();
        candidate.challenges[3] += Block256::ONE;
        assert_rejected(candidate, "challenge tamper");

        let mut candidate = honest.clone();
        candidate.mask_claim += Block256::ONE;
        assert_rejected(candidate, "initial mask evaluation tamper");

        let mut candidate = honest.clone();
        candidate.mask_final += Block256::ONE;
        assert_rejected(candidate, "final mask evaluation tamper");

        let mut candidate = honest.clone();
        candidate.main_claim += Block256::ONE;
        assert_rejected(candidate, "initial main claim tamper");

        let mut candidate = honest;
        candidate.main_final += Block256::ONE;
        assert_rejected(candidate, "expected main terminal tamper");
    }

    #[test]
    fn high_to_low_variable_order_is_enforced() {
        let honest = honest_fixture(0);
        let mut wrong = honest.clone();
        wrong.input_point.swap(0, ZK_MLECHECK_N_VARS - 1);
        let (r1cs, witness, rows, terminal, ..) = build_trace(&wrong);
        assert_eq!(rows, ZK_MLECHECK_VERIFIER_ROWS);
        assert!(
            !r1cs.satisfies(&witness),
            "reversed endpoint alpha order passed"
        );

        // Round challenges still populate the public output in canonical
        // low-to-high order; the failure above comes from using the wrong
        // input alpha in recovery, not from silently changing that convention.
        for index in 0..ZK_MLECHECK_N_VARS {
            assert_eq!(
                terminal[index],
                honest.challenges[ZK_MLECHECK_N_VARS - 1 - index]
            );
        }
    }

    #[test]
    fn matrix_and_fixed_shape_are_invariant_across_honest_contents() {
        let left = honest_fixture(0);
        let right = honest_fixture(0xD15C_A11E_CAFE_BABE);
        let (left_r1cs, left_witness, left_rows, ..) = build_trace(&left);
        let (right_r1cs, right_witness, right_rows, ..) = build_trace(&right);

        assert!(left_r1cs.satisfies(&left_witness));
        assert!(right_r1cs.satisfies(&right_witness));
        assert_eq!(left_rows, ZK_MLECHECK_VERIFIER_ROWS);
        assert_eq!(right_rows, ZK_MLECHECK_VERIFIER_ROWS);
        assert_eq!(left_r1cs.useful_rows, right_r1cs.useful_rows);
        assert_eq!(left_r1cs.a_0, right_r1cs.a_0);
        assert_eq!(left_r1cs.b_0, right_r1cs.b_0);
        assert_eq!(
            left_r1cs.structural_statement_digest(),
            right_r1cs.structural_statement_digest(),
            "witness contents changed the verifier matrix",
        );
    }

    #[test]
    fn constant_challenges_and_coefficients_fail_before_appending_rows() {
        let fixture = honest_fixture(0xC1A5_5F1E);
        let mut b = FieldR1csBuilder::new();
        let mut inputs = alloc_inputs(&mut b, &fixture);

        inputs.challenges[3] = const_block256(fixture.challenges[3]);
        let before = b.num_wires();
        assert_eq!(
            verify_zk_mlecheck_trace(&mut b, &inputs).unwrap_err(),
            ZkMleCheckTraceError::DynamicInputIsConstant {
                input: ZkMleCheckTraceDynamicInput::Challenge,
                index: 3,
            }
        );
        assert_eq!(b.num_wires(), before, "challenge preflight appended rows");

        inputs.challenges[3] = alloc_block256(&mut b, fixture.challenges[3]);
        inputs.rounds[7].coeffs_without_constant[3] =
            const_block256(fixture.proofs[7].coeffs_without_constant[3]);
        let before = b.num_wires();
        assert_eq!(
            verify_zk_mlecheck_trace(&mut b, &inputs).unwrap_err(),
            ZkMleCheckTraceError::DynamicInputIsConstant {
                input: ZkMleCheckTraceDynamicInput::RoundCoefficient,
                index: 7 * ZK_MLECHECK_ROUND_PROOF_COEFFS + 3,
            }
        );
        assert_eq!(b.num_wires(), before, "coefficient preflight appended rows");
    }

    #[test]
    fn main_claim_allows_only_dynamic_or_exact_zero_constant() {
        let fixture = honest_fixture(0xA071_C6A1);
        assert_ne!(fixture.main_claim, Block256::ZERO);
        let mut b = FieldR1csBuilder::new();
        let mut inputs = alloc_inputs(&mut b, &fixture);

        inputs.main_claim = const_block256(fixture.main_claim);
        let before = b.num_wires();
        assert_eq!(
            verify_zk_mlecheck_trace(&mut b, &inputs).unwrap_err(),
            ZkMleCheckTraceError::NonzeroConstantMainClaim
        );
        assert_eq!(b.num_wires(), before, "main-claim preflight appended rows");

        inputs.main_claim = ExtExpr::zero();
        let before = b.num_wires();
        verify_zk_mlecheck_trace(&mut b, &inputs)
            .expect("protocol-owned zero main claim is an admitted class member");
        assert_eq!(b.num_wires() - before, ZK_MLECHECK_VERIFIER_ROWS);
    }
}
