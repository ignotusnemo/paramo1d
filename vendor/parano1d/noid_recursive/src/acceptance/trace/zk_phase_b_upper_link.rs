// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Production recursive Phase-B upper/tail linkage.
//!
//! The capsule publishes `upper[256]`, the contraction of the three HIGH
//! bank variables at Phase A's terminal coordinates `s[8..11]`.  This trace
//! binds that table twice:
//!
//! - `MLE(upper, s[0..8]) = v`, where `v` is the exact terminal oracle value
//!   consumed by Phase A;
//! - `MLE(upper, beta[0..8]) = MLE(h8, s[8..11])`, where `h8` is obtained by
//!   locally folding adjacent cells of the revealed `tail16` at `beta[7]`.
//!
//! Every point is canonical LOW-to-HIGH.  In particular, `tail16` is the
//! natural table over variables 7 through 10 after the first seven Phase-B
//! folds, so its adjacent pairs differ in variable 7.  Folding table halves
//! here would silently bind the wrong variable.

use noid_fri_binius::zk_capsule_algebra::{
    FINAL_H_SYMBOLS, OWNER_BANK_POINT_VARS, PHASE_B_HIGH_VARS, PHASE_B_LOW_VARS, TAIL_SYMBOLS,
    UPPER_SYMBOLS,
};

use super::{evaluate_slice_ext_trace, mul_ext, pin_eq_ext, ExtExpr, FieldR1csBuilder};

pub const ZK_PHASE_B_UPPER_SYMBOLS: usize = UPPER_SYMBOLS;
pub const ZK_PHASE_B_TAIL_SYMBOLS: usize = TAIL_SYMBOLS;
pub const ZK_PHASE_B_H_SYMBOLS: usize = FINAL_H_SYMBOLS;

/// One complete eight-variable MLE fold.
pub const ZK_PHASE_B_UPPER_EVAL_ROWS: usize = 3 * (ZK_PHASE_B_UPPER_SYMBOLS - 1);
/// One multiplication per adjacent `tail16` pair at variable seven.
pub const ZK_PHASE_B_TAIL_LOCAL_FOLD_ROWS: usize = 3 * ZK_PHASE_B_H_SYMBOLS;
/// One complete three-variable MLE fold of `h8`.
pub const ZK_PHASE_B_H_EVAL_ROWS: usize = 3 * (ZK_PHASE_B_H_SYMBOLS - 1);
/// Two coordinate pins for each of the two extension-field links.
pub const ZK_PHASE_B_LINK_PIN_ROWS: usize = 4;
/// Exact incremental rows after all caller-owned dynamic inputs are allocated.
pub const ZK_PHASE_B_UPPER_LINK_TRACE_ROWS: usize = 2 * ZK_PHASE_B_UPPER_EVAL_ROWS
    + ZK_PHASE_B_TAIL_LOCAL_FOLD_ROWS
    + ZK_PHASE_B_H_EVAL_ROWS
    + ZK_PHASE_B_LINK_PIN_ROWS;

/// Active linkage ledger before the local tail and full `h8` evaluation:
/// `255 + 1 + 255 + 1 + 1`.
pub const ZK_PHASE_B_ACTIVE_LINKAGE_ROWS: usize = 2 * ZK_PHASE_B_UPPER_EVAL_ROWS + 7;
/// Fixed per-authorization delta of the selected exact tail linkage.
pub const ZK_PHASE_B_UPPER_LINK_ROWS_OVER_ACTIVE: usize =
    ZK_PHASE_B_UPPER_LINK_TRACE_ROWS - ZK_PHASE_B_ACTIVE_LINKAGE_ROWS;

const _: () = assert!(OWNER_BANK_POINT_VARS == 11);
const _: () = assert!(PHASE_B_LOW_VARS == 8);
const _: () = assert!(PHASE_B_HIGH_VARS == 3);
const _: () = assert!(ZK_PHASE_B_UPPER_SYMBOLS == 256);
const _: () = assert!(ZK_PHASE_B_TAIL_SYMBOLS == 16);
const _: () = assert!(ZK_PHASE_B_H_SYMBOLS == 8);
const _: () = assert!(ZK_PHASE_B_UPPER_EVAL_ROWS == 765);
const _: () = assert!(ZK_PHASE_B_TAIL_LOCAL_FOLD_ROWS == 24);
const _: () = assert!(ZK_PHASE_B_H_EVAL_ROWS == 21);
const _: () = assert!(ZK_PHASE_B_UPPER_LINK_TRACE_ROWS == 1_579);
const _: () = assert!(ZK_PHASE_B_ACTIVE_LINKAGE_ROWS == 1_537);
const _: () = assert!(ZK_PHASE_B_UPPER_LINK_ROWS_OVER_ACTIVE == 42);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkPhaseBUpperLinkDynamicInput {
    Upper,
    PhaseATerminalPoint,
    Beta,
    TerminalOracleValue,
    Tail,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkPhaseBUpperLinkTraceError {
    /// A proof/transcript value was embedded in the class matrix instead of
    /// entering through an allocated witness expression.
    DynamicInputIsConstant {
        input: ZkPhaseBUpperLinkDynamicInput,
        index: usize,
    },
}

#[derive(Clone, Debug)]
pub struct ZkPhaseBUpperLinkTraceInput {
    /// Published high-variable contraction, natural LOW-eight table order.
    pub upper: [ExtExpr; ZK_PHASE_B_UPPER_SYMBOLS],
    /// Shared Phase-A terminal point `[s_0, ..., s_10]`, LOW-to-HIGH.
    pub phase_a_terminal_point: [ExtExpr; OWNER_BANK_POINT_VARS],
    /// Phase-B fold challenges `[beta_0, ..., beta_7]`, LOW-to-HIGH.
    pub beta: [ExtExpr; PHASE_B_LOW_VARS],
    /// The same `v` expression supplied to Phase A's terminal equation.
    pub terminal_oracle_value: ExtExpr,
    /// Revealed natural table over variables 7 through 10.
    pub tail: [ExtExpr; ZK_PHASE_B_TAIL_SYMBOLS],
}

#[derive(Clone, Debug)]
pub struct ZkPhaseBUpperLinkTraceOutput {
    /// Exact aliases returned for integration-time identity assertions.
    pub phase_a_terminal_point: [ExtExpr; OWNER_BANK_POINT_VARS],
    pub beta: [ExtExpr; PHASE_B_LOW_VARS],
    pub terminal_oracle_value: ExtExpr,
    /// `MLE(upper, s[0..8])`, pinned to `terminal_oracle_value`.
    pub upper_at_phase_a_low: ExtExpr,
    /// `MLE(upper, beta)`.
    pub upper_at_beta: ExtExpr,
    /// `tail16` folded at adjacent pairs with `beta_7`.
    pub h: [ExtExpr; ZK_PHASE_B_H_SYMBOLS],
    /// `MLE(h, s[8..11])`, pinned to `upper_at_beta`.
    pub h_at_phase_a_high: ExtExpr,
}

fn check_dynamic(
    expression: &ExtExpr,
    input: ZkPhaseBUpperLinkDynamicInput,
    index: usize,
) -> Result<(), ZkPhaseBUpperLinkTraceError> {
    if expression.is_const() {
        Err(ZkPhaseBUpperLinkTraceError::DynamicInputIsConstant { input, index })
    } else {
        Ok(())
    }
}

fn preflight_dynamic_inputs(
    input: &ZkPhaseBUpperLinkTraceInput,
) -> Result<(), ZkPhaseBUpperLinkTraceError> {
    for (index, expression) in input.upper.iter().enumerate() {
        check_dynamic(expression, ZkPhaseBUpperLinkDynamicInput::Upper, index)?;
    }
    for (index, expression) in input.phase_a_terminal_point.iter().enumerate() {
        check_dynamic(
            expression,
            ZkPhaseBUpperLinkDynamicInput::PhaseATerminalPoint,
            index,
        )?;
    }
    for (index, expression) in input.beta.iter().enumerate() {
        check_dynamic(expression, ZkPhaseBUpperLinkDynamicInput::Beta, index)?;
    }
    check_dynamic(
        &input.terminal_oracle_value,
        ZkPhaseBUpperLinkDynamicInput::TerminalOracleValue,
        0,
    )?;
    for (index, expression) in input.tail.iter().enumerate() {
        check_dynamic(expression, ZkPhaseBUpperLinkDynamicInput::Tail, index)?;
    }
    Ok(())
}

/// Verify both exact Phase-B upper/tail links inside an F128 trace.
///
/// Transcript replay and construction of the committed `upper`/`tail` cells
/// live in the integrating capsule region.  This disconnected primitive only
/// consumes their already-bound aliases and appends exactly
/// [`ZK_PHASE_B_UPPER_LINK_TRACE_ROWS`] rows.
pub fn verify_zk_phase_b_upper_link_trace(
    b: &mut FieldR1csBuilder,
    input: &ZkPhaseBUpperLinkTraceInput,
) -> Result<ZkPhaseBUpperLinkTraceOutput, ZkPhaseBUpperLinkTraceError> {
    preflight_dynamic_inputs(input)?;
    let trace_start = b.num_wires();

    let upper_at_phase_a_low = evaluate_slice_ext_trace(
        b,
        &input.upper,
        &input.phase_a_terminal_point[..PHASE_B_LOW_VARS],
    );
    debug_assert_eq!(b.num_wires() - trace_start, ZK_PHASE_B_UPPER_EVAL_ROWS);
    pin_eq_ext(b, &upper_at_phase_a_low, &input.terminal_oracle_value);

    let upper_at_beta = evaluate_slice_ext_trace(b, &input.upper, &input.beta);
    debug_assert_eq!(
        b.num_wires() - trace_start,
        2 * ZK_PHASE_B_UPPER_EVAL_ROWS + 2
    );

    // Variable seven is the LOWEST surviving tail variable, hence adjacent
    // pairs. Characteristic two gives `a + beta_7 * (a + b)`.
    let h: [ExtExpr; ZK_PHASE_B_H_SYMBOLS] = std::array::from_fn(|index| {
        let at_zero = &input.tail[2 * index];
        let at_one = &input.tail[2 * index + 1];
        at_zero.add(&mul_ext(
            b,
            &input.beta[PHASE_B_LOW_VARS - 1],
            &at_zero.add(at_one),
        ))
    });
    debug_assert_eq!(
        b.num_wires() - trace_start,
        2 * ZK_PHASE_B_UPPER_EVAL_ROWS + 2 + ZK_PHASE_B_TAIL_LOCAL_FOLD_ROWS
    );

    let h_at_phase_a_high =
        evaluate_slice_ext_trace(b, &h, &input.phase_a_terminal_point[PHASE_B_LOW_VARS..]);
    pin_eq_ext(b, &upper_at_beta, &h_at_phase_a_high);

    debug_assert_eq!(
        b.num_wires() - trace_start,
        ZK_PHASE_B_UPPER_LINK_TRACE_ROWS
    );
    Ok(ZkPhaseBUpperLinkTraceOutput {
        phase_a_terminal_point: input.phase_a_terminal_point.clone(),
        beta: input.beta.clone(),
        terminal_oracle_value: input.terminal_oracle_value.clone(),
        upper_at_phase_a_low,
        upper_at_beta,
        h,
        h_at_phase_a_high,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::trace::{
        alloc_block256, alloc_blocks256, const_block256, test_support::tower_value_ext,
    };
    use noid_core::mle::evaluate::evaluate_slice;
    use noid_core::mle::fold::fold_variable_inplace;
    use noid_core::{Block128, Block256, TowerField};
    use noid_fri_binius::zk_capsule_algebra::{
        contract_high3_for_each_low8, evaluate_upper_at_low8, fold_bank_low8, tail16_local_fold,
        OWNER_BANK_RELATION_LEN,
    };
    use noid_ivc_core::field::F128;
    use noid_ivc_core::field_r1cs::FieldR1cs;

    const ZK_PHASE_B_DYNAMIC_INPUT_ROWS: usize = 2
        * (ZK_PHASE_B_UPPER_SYMBOLS
            + OWNER_BANK_POINT_VARS
            + PHASE_B_LOW_VARS
            + 1
            + ZK_PHASE_B_TAIL_SYMBOLS);
    const ZK_PHASE_B_FIXTURE_USEFUL_ROWS: usize =
        1 + ZK_PHASE_B_DYNAMIC_INPUT_ROWS + ZK_PHASE_B_UPPER_LINK_TRACE_ROWS;

    #[derive(Clone)]
    struct NativeCase {
        upper: [Block256; ZK_PHASE_B_UPPER_SYMBOLS],
        phase_a_terminal_point: [Block256; OWNER_BANK_POINT_VARS],
        beta: [Block256; PHASE_B_LOW_VARS],
        terminal_oracle_value: Block256,
        tail: [Block256; ZK_PHASE_B_TAIL_SYMBOLS],
        h: [Block256; ZK_PHASE_B_H_SYMBOLS],
        upper_at_beta: Block256,
        h_at_phase_a_high: Block256,
    }

    fn elem(index: usize, domain: u128, salt: u128) -> Block128 {
        let mut value = Block128::from(
            domain
                .wrapping_mul(index as u128 + 1)
                .rotate_left(((19 * index + 11) % 127) as u32)
                ^ salt.rotate_left(((7 * index + 3) % 127) as u32)
                ^ (index as u128 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15),
        );
        if value == Block128::ZERO || value == Block128::ONE {
            value += Block128::from(2u128);
        }
        value
    }

    fn ext_elem(index: usize, domain: u128, salt: u128) -> Block256 {
        Block256::new(
            elem(index, domain, salt),
            elem(index + 103, domain ^ 0xC1_256, salt.rotate_left(37)),
        )
    }

    fn native_case(salt: u128) -> NativeCase {
        let bank: [Block256; OWNER_BANK_RELATION_LEN] =
            std::array::from_fn(|index| ext_elem(index, 0xB4A9_2048, salt ^ 0x11));
        let phase_a_terminal_point: [Block256; OWNER_BANK_POINT_VARS] =
            std::array::from_fn(|index| ext_elem(index + 17, 0x5A11_0011, salt ^ 0x22));
        let beta: [Block256; PHASE_B_LOW_VARS] =
            std::array::from_fn(|index| ext_elem(index + 41, 0xBE7A_0008, salt ^ 0x33));
        let high_point: [Block256; PHASE_B_HIGH_VARS] =
            std::array::from_fn(|index| phase_a_terminal_point[PHASE_B_LOW_VARS + index]);
        let low_point: [Block256; PHASE_B_LOW_VARS] =
            std::array::from_fn(|index| phase_a_terminal_point[index]);

        let upper = contract_high3_for_each_low8(&bank, &high_point);
        let terminal_oracle_value = evaluate_upper_at_low8(&upper, &low_point);
        assert_eq!(
            terminal_oracle_value,
            evaluate_slice(&bank, &phase_a_terminal_point)
        );

        let h = fold_bank_low8(&bank, &beta);
        let upper_at_beta = evaluate_upper_at_low8(&upper, &beta);
        let h_at_phase_a_high = evaluate_slice(&h, &high_point);
        assert_eq!(upper_at_beta, h_at_phase_a_high);

        let mut after_seven = bank.to_vec();
        for &challenge in &beta[..PHASE_B_LOW_VARS - 1] {
            fold_variable_inplace(&mut after_seven, challenge, 0);
        }
        let tail: [Block256; ZK_PHASE_B_TAIL_SYMBOLS] =
            after_seven.try_into().expect("seven folds leave tail16");
        assert_eq!(tail16_local_fold(&tail, beta[7]), h);

        NativeCase {
            upper,
            phase_a_terminal_point,
            beta,
            terminal_oracle_value,
            tail,
            h,
            upper_at_beta,
            h_at_phase_a_high,
        }
    }

    fn alloc_input(b: &mut FieldR1csBuilder, case: &NativeCase) -> ZkPhaseBUpperLinkTraceInput {
        ZkPhaseBUpperLinkTraceInput {
            upper: alloc_blocks256(b, &case.upper)
                .try_into()
                .unwrap_or_else(|_| unreachable!("upper has a fixed array length")),
            phase_a_terminal_point: std::array::from_fn(|index| {
                alloc_block256(b, case.phase_a_terminal_point[index])
            }),
            beta: std::array::from_fn(|index| alloc_block256(b, case.beta[index])),
            terminal_oracle_value: alloc_block256(b, case.terminal_oracle_value),
            tail: std::array::from_fn(|index| alloc_block256(b, case.tail[index])),
        }
    }

    struct BuiltCase {
        r1cs: FieldR1cs,
        witness: Vec<F128>,
        trace_rows: usize,
        upper_at_phase_a_low: Block256,
        upper_at_beta: Block256,
        h: [Block256; ZK_PHASE_B_H_SYMBOLS],
        h_at_phase_a_high: Block256,
        exact_aliases: bool,
    }

    fn build_case(case: &NativeCase) -> Result<BuiltCase, ZkPhaseBUpperLinkTraceError> {
        let mut b = FieldR1csBuilder::new();
        let input = alloc_input(&mut b, case);
        assert_eq!(
            b.num_wires(),
            1 + ZK_PHASE_B_DYNAMIC_INPUT_ROWS,
            "fixture input ledger"
        );
        let expected_point_alias = input.phase_a_terminal_point.clone();
        let expected_beta_alias = input.beta.clone();
        let expected_v_alias = input.terminal_oracle_value.clone();
        let before = b.num_wires();
        let output = verify_zk_phase_b_upper_link_trace(&mut b, &input)?;
        let trace_rows = b.num_wires() - before;
        let exact_aliases = output.phase_a_terminal_point == expected_point_alias
            && output.beta == expected_beta_alias
            && output.terminal_oracle_value == expected_v_alias;
        let upper_at_phase_a_low = tower_value_ext(&b, &output.upper_at_phase_a_low);
        let upper_at_beta = tower_value_ext(&b, &output.upper_at_beta);
        let h = std::array::from_fn(|index| tower_value_ext(&b, &output.h[index]));
        let h_at_phase_a_high = tower_value_ext(&b, &output.h_at_phase_a_high);
        let (r1cs, witness) = b.build();
        Ok(BuiltCase {
            r1cs,
            witness,
            trace_rows,
            upper_at_phase_a_low,
            upper_at_beta,
            h,
            h_at_phase_a_high,
            exact_aliases,
        })
    }

    #[test]
    fn zk_phase_b_upper_link_matches_native_contract_and_low_folds() {
        let native = native_case(0xB255_0001);
        let built = build_case(&native).expect("trace builds");
        assert!(built.r1cs.satisfies(&built.witness));
        assert!(
            built.exact_aliases,
            "shared challenge/value aliases drifted"
        );
        assert_eq!(built.upper_at_phase_a_low, native.terminal_oracle_value);
        assert_eq!(built.upper_at_beta, native.upper_at_beta);
        assert_eq!(built.h, native.h);
        assert_eq!(built.h_at_phase_a_high, native.h_at_phase_a_high);
    }

    #[test]
    fn zk_phase_b_upper_link_rejects_s_beta_upper_v_and_tail_tampering() {
        let native = native_case(0xB255_0002);
        let mut mutations = Vec::new();

        let mut s = native.clone();
        s.phase_a_terminal_point[0] += Block256::ONE;
        mutations.push(("phase-A terminal point", s));

        let mut beta = native.clone();
        beta.beta[0] += Block256::ONE;
        mutations.push(("beta", beta));

        let mut upper = native.clone();
        upper.upper[73] += Block256::ONE;
        mutations.push(("upper", upper));

        let mut value = native.clone();
        value.terminal_oracle_value += Block256::ONE;
        mutations.push(("terminal v", value));

        let mut tail = native.clone();
        tail.tail[5] += Block256::ONE;
        mutations.push(("tail16", tail));

        for (name, mutation) in mutations {
            let built = build_case(&mutation).expect("tamper preserves fixed trace shape");
            assert!(
                !built.r1cs.satisfies(&built.witness),
                "accepted {name} tamper"
            );
        }
    }

    #[test]
    fn zk_phase_b_upper_link_refuses_constants_before_appending_rows() {
        let native = native_case(0xB255_0003);

        let checks = [
            (ZkPhaseBUpperLinkDynamicInput::Upper, 19usize, 0usize),
            (ZkPhaseBUpperLinkDynamicInput::PhaseATerminalPoint, 4, 1),
            (ZkPhaseBUpperLinkDynamicInput::Beta, 6, 2),
            (ZkPhaseBUpperLinkDynamicInput::TerminalOracleValue, 0, 3),
            (ZkPhaseBUpperLinkDynamicInput::Tail, 11, 4),
        ];

        for (expected_input, expected_index, kind) in checks {
            let mut b = FieldR1csBuilder::new();
            let mut input = alloc_input(&mut b, &native);
            match kind {
                0 => input.upper[expected_index] = const_block256(native.upper[expected_index]),
                1 => {
                    input.phase_a_terminal_point[expected_index] =
                        const_block256(native.phase_a_terminal_point[expected_index]);
                }
                2 => input.beta[expected_index] = const_block256(native.beta[expected_index]),
                3 => {
                    input.terminal_oracle_value = const_block256(native.terminal_oracle_value);
                }
                4 => input.tail[expected_index] = const_block256(native.tail[expected_index]),
                _ => unreachable!(),
            }
            let before = b.num_wires();
            assert!(matches!(
                verify_zk_phase_b_upper_link_trace(&mut b, &input),
                Err(ZkPhaseBUpperLinkTraceError::DynamicInputIsConstant { input, index })
                    if input == expected_input && index == expected_index
            ));
            assert_eq!(b.num_wires(), before, "failed preflight appended rows");
        }
    }

    #[test]
    fn zk_phase_b_upper_link_has_exact_row_delta_and_content_invariant_shape() {
        let left = build_case(&native_case(0xB255_0004)).expect("left trace");
        let right = build_case(&native_case(0xB255_0005)).expect("right trace");
        assert!(left.r1cs.satisfies(&left.witness));
        assert!(right.r1cs.satisfies(&right.witness));

        assert_eq!(ZK_PHASE_B_UPPER_EVAL_ROWS, 765);
        assert_eq!(ZK_PHASE_B_TAIL_LOCAL_FOLD_ROWS, 24);
        assert_eq!(ZK_PHASE_B_H_EVAL_ROWS, 21);
        assert_eq!(ZK_PHASE_B_LINK_PIN_ROWS, 4);
        assert_eq!(ZK_PHASE_B_UPPER_LINK_TRACE_ROWS, 1_579);
        assert_eq!(ZK_PHASE_B_ACTIVE_LINKAGE_ROWS, 1_537);
        assert_eq!(ZK_PHASE_B_UPPER_LINK_ROWS_OVER_ACTIVE, 42);
        assert_eq!(left.trace_rows, ZK_PHASE_B_UPPER_LINK_TRACE_ROWS);
        assert_eq!(right.trace_rows, ZK_PHASE_B_UPPER_LINK_TRACE_ROWS);
        assert_eq!(left.r1cs.useful_rows, ZK_PHASE_B_FIXTURE_USEFUL_ROWS);
        assert_eq!(right.r1cs.useful_rows, ZK_PHASE_B_FIXTURE_USEFUL_ROWS);
        assert_eq!(left.r1cs.statement_digest(), right.r1cs.statement_digest());
    }
}
