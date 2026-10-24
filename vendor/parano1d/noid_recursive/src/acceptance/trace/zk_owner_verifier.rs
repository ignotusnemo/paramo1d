// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Disconnected recursive Owner AuthGKR verifier composition.
//!
//! This fixed-shape wrapper joins the independently tested terminal evaluator
//! and degree-ten MLE-check telescope. It deliberately owns no transcript:
//! `rho`, `lambda`, proof coefficients, and round challenges must already be
//! transcript-bound witness expressions supplied by the integrating Owner
//! channel.
//!
//! The AuthGKR main claim is the protocol-owned exact constant zero. Round
//! challenges arrive HIGH-to-LOW; their reversal is the canonical LOW-to-HIGH
//! terminal point used both by the five-claim Poseidon terminal evaluator and
//! by the MLE-check output. The terminal evaluator's result is passed directly
//! as `expected_main_final`, so there is no separately trusted terminal-main
//! witness.

use noid_gkr::zk_auth_capsule::{
    ZK_AUTH_CAPSULE_BANK_VARS, ZK_AUTH_CAPSULE_TERMINAL_OPERAND_CLAIMS,
};
use noid_gkr::zk_mlecheck::{ZK_MLECHECK_N_VARS, ZK_MLECHECK_ROUND_PROOF_COEFFS};

use super::zk_auth_terminal::{
    evaluate_auth_main_terminal_from_claims_trace, AuthCapsuleTerminalOperandClaimsTrace,
    ZkAuthTerminalTraceError, ZK_AUTH_TERMINAL_TRACE_ROWS,
};
use super::zk_mlecheck::{
    verify_zk_mlecheck_trace, ZkMleCheckRoundProofTrace, ZkMleCheckTraceError,
    ZkMleCheckVerifierTraceInputs, ZK_MLECHECK_VERIFIER_ROWS,
};
use super::{constrain_nonzero_ext, ExtExpr, FieldR1csBuilder, F256};

/// One extension inverse witness, product, and coordinate pins for `lambda != 0`.
pub const ZK_OWNER_VERIFIER_LAMBDA_ADMISSIBILITY_ROWS: usize = 7;
/// Exact incremental ledger after all caller-owned inputs are allocated.
pub const ZK_OWNER_VERIFIER_TRACE_ROWS: usize = ZK_OWNER_VERIFIER_LAMBDA_ADMISSIBILITY_ROWS
    + ZK_AUTH_TERMINAL_TRACE_ROWS
    + ZK_MLECHECK_VERIFIER_ROWS;

const _: () = assert!(ZK_AUTH_CAPSULE_BANK_VARS == ZK_MLECHECK_N_VARS);
const _: () = assert!(ZK_AUTH_CAPSULE_BANK_VARS == 11);
const _: () = assert!(ZK_AUTH_CAPSULE_TERMINAL_OPERAND_CLAIMS == 5);
const _: () = assert!(ZK_MLECHECK_ROUND_PROOF_COEFFS == 10);
const _: () = assert!(ZK_OWNER_VERIFIER_TRACE_ROWS == 871);

/// Dynamic field whose accidental embedding as a class-matrix constant must
/// be rejected before the wrapper appends its first row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkOwnerVerifierDynamicInput {
    Rho,
    MaskMleAtInput,
    MaskFinalAtTerminal,
    Lambda,
    RoundCoefficient,
    Challenge,
    TerminalOperandIncrementClaim,
    TerminalOperandLaneClaim,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkOwnerVerifierTraceError {
    DynamicInputIsConstant {
        input: ZkOwnerVerifierDynamicInput,
        index: usize,
    },
    /// Early construction failure. Soundness is independently enforced by
    /// the inverse-witness constraint in every successfully built instance.
    LambdaZero,
    Terminal(ZkAuthTerminalTraceError),
    MleCheck(ZkMleCheckTraceError),
}

impl From<ZkAuthTerminalTraceError> for ZkOwnerVerifierTraceError {
    fn from(value: ZkAuthTerminalTraceError) -> Self {
        Self::Terminal(value)
    }
}

impl From<ZkMleCheckTraceError> for ZkOwnerVerifierTraceError {
    fn from(value: ZkMleCheckTraceError) -> Self {
        Self::MleCheck(value)
    }
}

/// Fixed-shape inputs to one disconnected Owner AuthGKR verification.
#[derive(Clone, Debug)]
pub struct ZkOwnerVerifierTraceInput {
    /// MLE input point in canonical LOW-to-HIGH variable order.
    pub rho: [ExtExpr; ZK_AUTH_CAPSULE_BANK_VARS],
    pub mask_mle_at_input: ExtExpr,
    pub mask_final_at_terminal: ExtExpr,
    /// Transcript-derived nonzero mask-batching challenge.
    pub lambda: ExtExpr,
    /// Eleven degree-ten proof rounds in transcript HIGH-to-LOW order.
    pub rounds: [ZkMleCheckRoundProofTrace; ZK_AUTH_CAPSULE_BANK_VARS],
    /// Transcript challenges `[r_10, ..., r_0]` in round order.
    pub challenges_high_to_low: [ExtExpr; ZK_AUTH_CAPSULE_BANK_VARS],
    /// Five independently bound padded operand claims: increment and four lanes.
    pub terminal_operands: AuthCapsuleTerminalOperandClaimsTrace,
}

/// Derived aliases returned after the terminal and telescope pins succeed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkOwnerVerifierTraceOutput {
    pub expected_main_final: ExtExpr,
    pub main_eval: ExtExpr,
    pub mask_eval: ExtExpr,
    /// Canonical LOW-to-HIGH point `[r_0, ..., r_10]`.
    pub terminal_point: [ExtExpr; ZK_AUTH_CAPSULE_BANK_VARS],
}

fn check_dynamic(
    expression: &ExtExpr,
    input: ZkOwnerVerifierDynamicInput,
    index: usize,
) -> Result<(), ZkOwnerVerifierTraceError> {
    if expression.is_const() {
        Err(ZkOwnerVerifierTraceError::DynamicInputIsConstant { input, index })
    } else {
        Ok(())
    }
}

/// Perform a complete wrapper-level preflight so a late malformed input
/// cannot leave a partially appended terminal or MLE-check trace behind.
fn preflight_dynamic_inputs(
    input: &ZkOwnerVerifierTraceInput,
) -> Result<(), ZkOwnerVerifierTraceError> {
    for (index, coordinate) in input.rho.iter().enumerate() {
        check_dynamic(coordinate, ZkOwnerVerifierDynamicInput::Rho, index)?;
    }
    check_dynamic(
        &input.mask_mle_at_input,
        ZkOwnerVerifierDynamicInput::MaskMleAtInput,
        0,
    )?;
    check_dynamic(
        &input.mask_final_at_terminal,
        ZkOwnerVerifierDynamicInput::MaskFinalAtTerminal,
        0,
    )?;
    check_dynamic(&input.lambda, ZkOwnerVerifierDynamicInput::Lambda, 0)?;
    for round in 0..ZK_AUTH_CAPSULE_BANK_VARS {
        for coefficient in 0..ZK_MLECHECK_ROUND_PROOF_COEFFS {
            check_dynamic(
                &input.rounds[round].coeffs_without_constant[coefficient],
                ZkOwnerVerifierDynamicInput::RoundCoefficient,
                round * ZK_MLECHECK_ROUND_PROOF_COEFFS + coefficient,
            )?;
        }
        check_dynamic(
            &input.challenges_high_to_low[round],
            ZkOwnerVerifierDynamicInput::Challenge,
            round,
        )?;
    }
    check_dynamic(
        &input.terminal_operands.increment,
        ZkOwnerVerifierDynamicInput::TerminalOperandIncrementClaim,
        0,
    )?;
    for (lane, claim) in input.terminal_operands.lane.iter().enumerate() {
        check_dynamic(
            claim,
            ZkOwnerVerifierDynamicInput::TerminalOperandLaneClaim,
            lane,
        )?;
    }
    Ok(())
}

/// Verify the complete disconnected Owner AuthGKR terminal and MLE telescope.
///
/// With valid dynamic inputs this appends exactly
/// [`ZK_OWNER_VERIFIER_TRACE_ROWS`] rows: three for nonzero `lambda`, 167 for
/// the terminal evaluator, and 124 for the MLE-check verifier.
pub fn verify_zk_owner_trace(
    b: &mut FieldR1csBuilder,
    input: &ZkOwnerVerifierTraceInput,
) -> Result<ZkOwnerVerifierTraceOutput, ZkOwnerVerifierTraceError> {
    preflight_dynamic_inputs(input)?;
    if input.lambda.eval(b.values()) == F256::ZERO {
        return Err(ZkOwnerVerifierTraceError::LambdaZero);
    }

    let trace_start = b.num_wires();
    constrain_nonzero_ext(b, &input.lambda);
    debug_assert_eq!(
        b.num_wires() - trace_start,
        ZK_OWNER_VERIFIER_LAMBDA_ADMISSIBILITY_ROWS
    );

    let terminal_point = std::array::from_fn(|low_variable| {
        input.challenges_high_to_low[ZK_AUTH_CAPSULE_BANK_VARS - 1 - low_variable].clone()
    });
    let expected_main_final = evaluate_auth_main_terminal_from_claims_trace(
        b,
        &terminal_point,
        &input.terminal_operands,
    )?;

    let mle_input = ZkMleCheckVerifierTraceInputs {
        input_point: input.rho.clone(),
        main_claim: ExtExpr::zero(),
        mask_mle_eval: input.mask_mle_at_input.clone(),
        lambda: input.lambda.clone(),
        rounds: input.rounds.clone(),
        challenges: input.challenges_high_to_low.clone(),
        mask_final_eval: input.mask_final_at_terminal.clone(),
        expected_main_final: expected_main_final.clone(),
    };
    let mle_output = verify_zk_mlecheck_trace(b, &mle_input)?;

    // Both components must alias the same challenge expressions, not merely
    // evaluate to the same field values. This structural assertion costs no
    // trace rows and catches an internal ordering regression immediately.
    assert_eq!(
        mle_output.terminal_point, terminal_point,
        "Owner terminal-point expression alias drift"
    );
    debug_assert_eq!(b.num_wires() - trace_start, ZK_OWNER_VERIFIER_TRACE_ROWS);

    Ok(ZkOwnerVerifierTraceOutput {
        expected_main_final,
        main_eval: mle_output.main_eval,
        mask_eval: mle_output.mask_eval,
        terminal_point: mle_output.terminal_point,
    })
}

#[cfg(test)]
mod tests {
    use noid_core::{Block128, Block256, TowerField};
    use noid_gkr::layers::evaluate_permutation;
    use noid_gkr::zk_auth_capsule::{
        build_explicit_mlecheck_carrier, state_cell_index, AuthCapsuleTerminalOperandClaims,
        ZkAuthCapsuleBankView, ZK_AUTH_CAPSULE_BANK_LEN, ZK_AUTH_CAPSULE_LIBRA_MASK_OFFSET,
        ZK_AUTH_CAPSULE_PCS_COINS_OFFSET, ZK_AUTH_CAPSULE_REMAINING_PADDING_OFFSET,
    };
    use noid_gkr::zk_mlecheck::ZkMleCheckRoundProof;
    use noid_ivc_core::field_r1cs::FieldR1cs;
    use noid_poseidon2b::native::domain::{capacity_iv, TAG_ADDRFIX};

    use super::super::{
        alloc_block256, const_block256, flat_of_ext, test_support::tower_value_ext, LinExpr, F128,
    };
    use super::*;

    const DYNAMIC_INPUT_ROWS: usize = 2
        * (ZK_AUTH_CAPSULE_BANK_VARS
            + 3
            + ZK_AUTH_CAPSULE_BANK_VARS * ZK_MLECHECK_ROUND_PROOF_COEFFS
            + ZK_AUTH_CAPSULE_BANK_VARS
            + ZK_AUTH_CAPSULE_TERMINAL_OPERAND_CLAIMS);
    const COMPLETE_FIXTURE_ROWS: usize = 1 + DYNAMIC_INPUT_ROWS + ZK_OWNER_VERIFIER_TRACE_ROWS;

    fn elem(index: usize, domain: u128, salt: u128) -> Block128 {
        Block128::from(
            domain
                .wrapping_mul(index as u128 + 1)
                .rotate_left(((index * 13 + 5) % 127) as u32)
                ^ salt.rotate_left((index % 127) as u32)
                ^ (index as u128 + 3).wrapping_mul(0x9E37_79B9_7F4A_7C15),
        )
    }

    fn ext_elem(index: usize, domain: u128, salt: u128) -> Block256 {
        Block256::new(
            elem(index, domain, salt),
            elem(index + 131, domain ^ 0xC1_256, salt.rotate_left(53)),
        )
    }

    fn point(domain: u128, salt: u128) -> [Block256; ZK_AUTH_CAPSULE_BANK_VARS] {
        std::array::from_fn(|index| ext_elem(index + 23, domain, salt))
    }

    #[derive(Clone)]
    struct NativeCase {
        rho: [Block256; ZK_AUTH_CAPSULE_BANK_VARS],
        mask_mle_at_input: Block256,
        mask_final_at_terminal: Block256,
        lambda: Block256,
        rounds: [ZkMleCheckRoundProof<Block256>; ZK_AUTH_CAPSULE_BANK_VARS],
        challenges_high_to_low: [Block256; ZK_AUTH_CAPSULE_BANK_VARS],
        terminal_operands: AuthCapsuleTerminalOperandClaims<Block256>,
        terminal_point: [Block256; ZK_AUTH_CAPSULE_BANK_VARS],
        main_final: Block256,
    }

    /// Build the real 2048-cell bank and feed it through the native explicit
    /// AuthGKR carrier. The recursive fixture never fabricates round proofs.
    fn native_case(salt: u128) -> NativeCase {
        let iv = capacity_iv(TAG_ADDRFIX);
        let input = [
            elem(0, 0x5EC2_E7, salt),
            elem(1, 0x5EC2_E7, salt),
            iv[0],
            iv[1],
        ];
        let permutation = evaluate_permutation(input);
        let mut bank = vec![Block128::ZERO; ZK_AUTH_CAPSULE_BANK_LEN];
        for (round, row) in permutation.state.iter().enumerate() {
            for (lane, value) in row.iter().copied().enumerate() {
                bank[state_cell_index(round, lane).unwrap()] = value;
            }
        }
        for (index, cell) in bank
            .iter_mut()
            .enumerate()
            .take(ZK_AUTH_CAPSULE_LIBRA_MASK_OFFSET)
            .skip(ZK_AUTH_CAPSULE_PCS_COINS_OFFSET)
        {
            *cell = elem(index, 0xC01A_5, salt ^ 0x11);
        }
        for (index, cell) in bank
            .iter_mut()
            .enumerate()
            .take(ZK_AUTH_CAPSULE_REMAINING_PADDING_OFFSET)
            .skip(ZK_AUTH_CAPSULE_LIBRA_MASK_OFFSET)
        {
            *cell = elem(index, 0x11B2_A, salt ^ 0x22);
        }
        for (index, cell) in bank
            .iter_mut()
            .enumerate()
            .skip(ZK_AUTH_CAPSULE_REMAINING_PADDING_OFFSET)
        {
            *cell = elem(index, 0xA771_A6, salt ^ 0x33);
        }

        let rho = point(0x1A90_7, salt ^ 0x44);
        let challenges_high_to_low = point(0xC4A1_1, salt ^ 0x55);
        let mut lambda = ext_elem(77, 0x1A4B_DA, salt ^ 0x66);
        if lambda == Block256::ZERO {
            lambda = Block256::ONE;
        }
        let carrier = build_explicit_mlecheck_carrier(
            ZkAuthCapsuleBankView::checked(&bank).unwrap(),
            rho,
            lambda,
            challenges_high_to_low,
        )
        .expect("native explicit Owner carrier");
        NativeCase {
            rho,
            mask_mle_at_input: carrier.mask_mle_at_input,
            mask_final_at_terminal: carrier.mask_final_at_terminal,
            lambda,
            rounds: carrier
                .round_proofs
                .try_into()
                .expect("exact eleven rounds"),
            challenges_high_to_low,
            terminal_operands: carrier.terminal_operands,
            terminal_point: carrier.terminal_point,
            main_final: carrier.main_final_at_terminal,
        }
    }

    fn alloc_input(b: &mut FieldR1csBuilder, case: &NativeCase) -> ZkOwnerVerifierTraceInput {
        ZkOwnerVerifierTraceInput {
            rho: std::array::from_fn(|index| alloc_block256(b, case.rho[index])),
            mask_mle_at_input: alloc_block256(b, case.mask_mle_at_input),
            mask_final_at_terminal: alloc_block256(b, case.mask_final_at_terminal),
            lambda: alloc_block256(b, case.lambda),
            rounds: std::array::from_fn(|round| ZkMleCheckRoundProofTrace {
                coeffs_without_constant: std::array::from_fn(|coefficient| {
                    alloc_block256(b, case.rounds[round].coeffs_without_constant[coefficient])
                }),
            }),
            challenges_high_to_low: std::array::from_fn(|round| {
                alloc_block256(b, case.challenges_high_to_low[round])
            }),
            terminal_operands: AuthCapsuleTerminalOperandClaimsTrace {
                increment: alloc_block256(b, case.terminal_operands.increment),
                lane: std::array::from_fn(|lane| {
                    alloc_block256(b, case.terminal_operands.lane[lane])
                }),
            },
        }
    }

    struct BuiltCase {
        r1cs: FieldR1cs,
        witness: Vec<F128>,
        trace_rows: usize,
        output_values: (Block256, Block256, Block256),
        terminal_point: [Block256; ZK_AUTH_CAPSULE_BANK_VARS],
        terminal_aliases: bool,
        lambda_wires: [usize; 2],
    }

    fn input_wire(expression: &LinExpr) -> usize {
        assert_eq!(expression.terms.len(), 1);
        assert_eq!(expression.terms[0].1, F128::ONE);
        assert_eq!(expression.constant, F128::ZERO);
        expression.terms[0].0 as usize
    }

    fn build_case(case: &NativeCase) -> Result<BuiltCase, ZkOwnerVerifierTraceError> {
        let mut b = FieldR1csBuilder::new();
        let input = alloc_input(&mut b, case);
        assert_eq!(b.num_wires(), 1 + DYNAMIC_INPUT_ROWS);
        let lambda_wires = [input_wire(&input.lambda.lo), input_wire(&input.lambda.hi)];
        let expected_aliases: [ExtExpr; ZK_AUTH_CAPSULE_BANK_VARS] =
            std::array::from_fn(|low_variable| {
                input.challenges_high_to_low[ZK_AUTH_CAPSULE_BANK_VARS - 1 - low_variable].clone()
            });
        let before = b.num_wires();
        let output = verify_zk_owner_trace(&mut b, &input)?;
        let trace_rows = b.num_wires() - before;
        let terminal_aliases = output.terminal_point == expected_aliases;
        let output_values = (
            tower_value_ext(&b, &output.expected_main_final),
            tower_value_ext(&b, &output.main_eval),
            tower_value_ext(&b, &output.mask_eval),
        );
        let terminal_point =
            std::array::from_fn(|index| tower_value_ext(&b, &output.terminal_point[index]));
        let (r1cs, witness) = b.build();
        Ok(BuiltCase {
            r1cs,
            witness,
            trace_rows,
            output_values,
            terminal_point,
            terminal_aliases,
            lambda_wires,
        })
    }

    #[test]
    fn owner_wrapper_matches_real_native_carrier_and_exact_ledger() {
        let native = native_case(0xA11C_E001);
        let built = build_case(&native).expect("honest recursive Owner wrapper");
        assert!(built.r1cs.satisfies(&built.witness));
        assert_eq!(built.trace_rows, ZK_OWNER_VERIFIER_TRACE_ROWS);
        assert_eq!(ZK_OWNER_VERIFIER_LAMBDA_ADMISSIBILITY_ROWS, 7);
        assert_eq!(ZK_AUTH_TERMINAL_TRACE_ROWS, 493);
        assert_eq!(ZK_MLECHECK_VERIFIER_ROWS, 371);
        assert_eq!(ZK_OWNER_VERIFIER_TRACE_ROWS, 871);
        assert_eq!(built.r1cs.useful_rows, COMPLETE_FIXTURE_ROWS);
        assert_eq!(built.output_values.0, native.main_final);
        assert_eq!(built.output_values.1, native.main_final);
        assert_eq!(built.output_values.2, native.mask_final_at_terminal);
        assert_eq!(built.terminal_point, native.terminal_point);
        assert!(built.terminal_aliases);
    }

    #[test]
    fn owner_wrapper_rejects_coeff_operand_mask_rho_and_challenge_tampering() {
        let honest = native_case(0xA11C_E002);
        let assert_rejected = |candidate: NativeCase, name: &str| {
            let built = build_case(&candidate).expect("tamper retains fixed shape");
            assert_eq!(built.trace_rows, ZK_OWNER_VERIFIER_TRACE_ROWS);
            assert!(
                !built.r1cs.satisfies(&built.witness),
                "accepted {name} tamper"
            );
        };

        let mut candidate = honest.clone();
        candidate.rounds[4].coeffs_without_constant[7] += Block256::ONE;
        assert_rejected(candidate, "round coefficient");

        let mut candidate = honest.clone();
        candidate.terminal_operands.lane[2] += Block256::ONE;
        assert_rejected(candidate, "terminal operand claim");

        let mut candidate = honest.clone();
        candidate.mask_mle_at_input += Block256::ONE;
        assert_rejected(candidate, "input mask claim");

        let mut candidate = honest.clone();
        candidate.mask_final_at_terminal += Block256::ONE;
        assert_rejected(candidate, "final mask claim");

        let mut candidate = honest.clone();
        candidate.rho[6] += Block256::ONE;
        assert_rejected(candidate, "rho");

        let mut candidate = honest;
        candidate.challenges_high_to_low[3] += Block256::ONE;
        assert_rejected(candidate, "round challenge");
    }

    #[test]
    fn owner_wrapper_rejects_lambda_zero_preflight_and_in_circuit() {
        let honest = native_case(0xA11C_E003);

        let mut zero = honest.clone();
        zero.lambda = Block256::ZERO;
        assert!(matches!(
            build_case(&zero),
            Err(ZkOwnerVerifierTraceError::LambdaZero)
        ));

        let built = build_case(&honest).expect("honest wrapper");
        assert!(built.r1cs.satisfies(&built.witness));
        let mut tampered = built.witness.clone();
        let zero = flat_of_ext(Block256::ZERO);
        tampered[built.lambda_wires[0]] = zero.lo;
        tampered[built.lambda_wires[1]] = zero.hi;
        assert!(
            !built.r1cs.satisfies(&tampered),
            "zero lambda escaped inverse constraint"
        );
    }

    #[test]
    fn owner_wrapper_preflight_is_atomic_for_constants() {
        let native = native_case(0xA11C_E004);
        let mut b = FieldR1csBuilder::new();
        let mut input = alloc_input(&mut b, &native);

        input.lambda = const_block256(native.lambda);
        let before = b.num_wires();
        assert_eq!(
            verify_zk_owner_trace(&mut b, &input),
            Err(ZkOwnerVerifierTraceError::DynamicInputIsConstant {
                input: ZkOwnerVerifierDynamicInput::Lambda,
                index: 0,
            })
        );
        assert_eq!(b.num_wires(), before);

        input.lambda = alloc_block256(&mut b, native.lambda);
        input.terminal_operands.lane[3] = const_block256(native.terminal_operands.lane[3]);
        let before = b.num_wires();
        assert_eq!(
            verify_zk_owner_trace(&mut b, &input),
            Err(ZkOwnerVerifierTraceError::DynamicInputIsConstant {
                input: ZkOwnerVerifierDynamicInput::TerminalOperandLaneClaim,
                index: 3,
            })
        );
        assert_eq!(b.num_wires(), before, "late preflight appended rows");
    }

    #[test]
    fn owner_wrapper_shape_is_invariant_across_honest_contents() {
        let left = build_case(&native_case(0xA11C_E005)).expect("left wrapper");
        let right = build_case(&native_case(0xA11C_E006)).expect("right wrapper");
        assert!(left.r1cs.satisfies(&left.witness));
        assert!(right.r1cs.satisfies(&right.witness));
        assert_eq!(left.trace_rows, ZK_OWNER_VERIFIER_TRACE_ROWS);
        assert_eq!(right.trace_rows, ZK_OWNER_VERIFIER_TRACE_ROWS);
        assert_eq!(left.r1cs.useful_rows, right.r1cs.useful_rows);
        assert_eq!(
            left.r1cs.structural_statement_digest(),
            right.r1cs.structural_statement_digest(),
            "Owner wrapper matrix depends on witness contents"
        );
    }
}
