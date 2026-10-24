// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Production recursive terminal evaluator for the owner-
//! authorization ZK capsule.
//!
//! This is the fixed-shape F128 trace twin of
//! [`noid_gkr::zk_auth_capsule::evaluate_auth_main_terminal_from_claims`].
//! The caller supplies the eleven-coordinate terminal point in canonical
//! LOW-to-HIGH order and exactly five ZK-padded operand claims (`increment`,
//! then four input lanes) as witness expressions. No proof-dependent value may enter as
//! a build-time constant.
//!
//! The native reference materializes thirteen 2048-cell public tables. This
//! trace evaluates the same multilinear extensions without a 2048-way mux:
//!
//! - lane bits are variables 0..1;
//! - round bits are variables 2..8;
//! - the two `high = 00` selector bits are variables 9..10;
//! - one shared 128-cell round equality tensor evaluates the active, partial,
//!   and four round-constant tables;
//! - the full/partial MDS columns use one shared lane cross-product.
//!
//! These are polynomial factorizations, not Boolean-point shortcuts. In
//! particular every high/active selector remains present at arbitrary field
//! terminal points, exactly as in the native table MLE.

use noid_core::Block128;
use noid_gkr::zk_auth_capsule::{
    ZK_AUTH_CAPSULE_ACTIVE_ROUNDS, ZK_AUTH_CAPSULE_BANK_VARS,
    ZK_AUTH_CAPSULE_TERMINAL_OPERAND_CLAIMS,
};
use noid_poseidon2b::native::permutation::{
    F_ROUNDS, MDS_FULL, MDS_PARTIAL, P_ROUNDS, ROUND_CONSTANTS, STATE_SIZE,
};

use super::{
    eq_ind_partial_eval_ext_trace, flat_of, mul_ext, pow7_ext, ExtExpr, FieldR1csBuilder, F128,
    F256,
};

const STATE_LANE_BITS: usize = 2;
const STATE_ROUND_BITS: usize = 7;
const STATE_HIGH_BITS: usize = 2;
const STATE_ROUND_POINT_OFFSET: usize = STATE_LANE_BITS;
const STATE_HIGH_POINT_OFFSET: usize = STATE_LANE_BITS + STATE_ROUND_BITS;
const STORED_ROUNDS: usize = 1 << STATE_ROUND_BITS;

/// The first round-equality split is linear because it multiplies by one;
/// the remaining six splits allocate `2 + 4 + ... + 64` products.
pub const ZK_AUTH_TERMINAL_ROUND_EQ_ROWS: usize = 3 * (STORED_ROUNDS - 2);
/// One shared extension-field `lane_bit_0 * lane_bit_1` product.
pub const ZK_AUTH_TERMINAL_LANE_ROWS: usize = 3;
/// `high = (1 + r_9)(1 + r_10)`.
pub const ZK_AUTH_TERMINAL_HIGH_ROWS: usize = 3;
/// `high * active_round` and `high * partial_round`.
pub const ZK_AUTH_TERMINAL_ROUND_SELECTOR_ROWS: usize = 6;
/// Four independently valued public round-constant MLEs, each gated by high.
pub const ZK_AUTH_TERMINAL_RC_ROWS: usize = 3 * STATE_SIZE;
/// Two dynamic products (full and partial) for each public MDS column.
pub const ZK_AUTH_TERMINAL_MDS_ROWS: usize = 6 * STATE_SIZE;
/// Exact public fixed-table evaluation cost, shared across all thirteen
/// native tables (`active`, four MDS, four sigma, four RC).
pub const ZK_AUTH_TERMINAL_FIXED_TABLE_ROWS: usize = ZK_AUTH_TERMINAL_ROUND_EQ_ROWS
    + ZK_AUTH_TERMINAL_LANE_ROWS
    + ZK_AUTH_TERMINAL_HIGH_ROWS
    + ZK_AUTH_TERMINAL_ROUND_SELECTOR_ROWS
    + ZK_AUTH_TERMINAL_RC_ROWS
    + ZK_AUTH_TERMINAL_MDS_ROWS;

/// The extension x^7 chain costs ten rows because its two squarings use the
/// quadratic-tower square gadget. One sigma mix and one MDS contribution add
/// three rows each.
pub const ZK_AUTH_TERMINAL_ROWS_PER_LANE: usize = 16;
/// One final multiplication by the active selector.
pub const ZK_AUTH_TERMINAL_FINAL_ROWS: usize = 3;
/// Exact incremental ledger after the sixteen caller-owned witness inputs
/// have already been allocated.
pub const ZK_AUTH_TERMINAL_TRACE_ROWS: usize = ZK_AUTH_TERMINAL_FIXED_TABLE_ROWS
    + STATE_SIZE * ZK_AUTH_TERMINAL_ROWS_PER_LANE
    + ZK_AUTH_TERMINAL_FINAL_ROWS;

const _: () = assert!(ZK_AUTH_CAPSULE_BANK_VARS == 11);
const _: () = assert!(ZK_AUTH_CAPSULE_TERMINAL_OPERAND_CLAIMS == 5);
const _: () = assert!(STATE_SIZE == 1 << STATE_LANE_BITS);
const _: () =
    assert!(ZK_AUTH_CAPSULE_BANK_VARS == STATE_LANE_BITS + STATE_ROUND_BITS + STATE_HIGH_BITS);
const _: () = assert!(ZK_AUTH_CAPSULE_ACTIVE_ROUNDS == F_ROUNDS + P_ROUNDS);
const _: () = assert!(ZK_AUTH_CAPSULE_ACTIVE_ROUNDS == 66);
const _: () = assert!(ZK_AUTH_TERMINAL_ROUND_EQ_ROWS == 378);
const _: () = assert!(ZK_AUTH_TERMINAL_FIXED_TABLE_ROWS == 426);
const _: () = assert!(ZK_AUTH_TERMINAL_TRACE_ROWS == 493);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkAuthTerminalDynamicInput {
    TerminalPoint,
    IncrementClaim,
    LaneClaim,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkAuthTerminalTraceError {
    /// A proof/transcript value was accidentally embedded into the class
    /// matrix instead of entering through a witness wire.
    DynamicInputIsConstant {
        input: ZkAuthTerminalDynamicInput,
        index: usize,
    },
}

/// Recursive form of the native five ZK-padded terminal operand claims.
#[derive(Clone, Debug)]
pub struct AuthCapsuleTerminalOperandClaimsTrace {
    pub increment: ExtExpr,
    pub lane: [ExtExpr; STATE_SIZE],
}

fn check_dynamic(
    expression: &ExtExpr,
    input: ZkAuthTerminalDynamicInput,
    index: usize,
) -> Result<(), ZkAuthTerminalTraceError> {
    if expression.is_const() {
        Err(ZkAuthTerminalTraceError::DynamicInputIsConstant { input, index })
    } else {
        Ok(())
    }
}

fn preflight_dynamic_inputs(
    point: &[ExtExpr; ZK_AUTH_CAPSULE_BANK_VARS],
    claims: &AuthCapsuleTerminalOperandClaimsTrace,
) -> Result<(), ZkAuthTerminalTraceError> {
    for (index, coordinate) in point.iter().enumerate() {
        check_dynamic(coordinate, ZkAuthTerminalDynamicInput::TerminalPoint, index)?;
    }
    check_dynamic(
        &claims.increment,
        ZkAuthTerminalDynamicInput::IncrementClaim,
        0,
    )?;
    for (index, claim) in claims.lane.iter().enumerate() {
        check_dynamic(claim, ZkAuthTerminalDynamicInput::LaneClaim, index)?;
    }
    Ok(())
}

#[inline]
fn is_partial_round(round: usize) -> bool {
    (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&round)
}

#[inline]
fn tower_constant(value: u128) -> F128 {
    flat_of(Block128::from(value))
}

/// Evaluate one fixed four-cell lane table at `(r_0, r_1)`, sharing the
/// caller's `r_0*r_1` product across every MDS column.
fn fixed_lane_mle(
    table: &[[u128; STATE_SIZE]; STATE_SIZE],
    input_lane: usize,
    lane_0: &ExtExpr,
    lane_1: &ExtExpr,
    lane_cross: &ExtExpr,
) -> ExtExpr {
    let c0 = tower_constant(table[0][input_lane]);
    let c1 = tower_constant(table[1][input_lane]);
    let c2 = tower_constant(table[2][input_lane]);
    let c3 = tower_constant(table[3][input_lane]);

    // Multilinear interpolation in little-endian Boolean-index order:
    // c0 + r0(c0+c1) + r1(c0+c2) + r0*r1(c0+c1+c2+c3).
    ExtExpr::constant(F256::from_base(c0))
        .add(&lane_0.scale_base(c0 + c1))
        .add(&lane_1.scale_base(c0 + c2))
        .add(&lane_cross.scale_base(c0 + c1 + c2 + c3))
}

struct FixedTerminalTablesTrace {
    active: ExtExpr,
    mds: [ExtExpr; STATE_SIZE],
    sigma: [ExtExpr; STATE_SIZE],
    rc: [ExtExpr; STATE_SIZE],
}

/// Factor and evaluate the native public tables at an arbitrary field point.
fn evaluate_fixed_terminal_tables_trace(
    b: &mut FieldR1csBuilder,
    point: &[ExtExpr; ZK_AUTH_CAPSULE_BANK_VARS],
) -> FixedTerminalTablesTrace {
    let start = b.num_wires();

    let round_eq =
        eq_ind_partial_eval_ext_trace(b, &point[STATE_ROUND_POINT_OFFSET..STATE_HIGH_POINT_OFFSET]);
    debug_assert_eq!(round_eq.len(), STORED_ROUNDS);
    debug_assert_eq!(b.num_wires() - start, ZK_AUTH_TERMINAL_ROUND_EQ_ROWS);

    let mut active_round = ExtExpr::zero();
    let mut partial_round = ExtExpr::zero();
    let mut rc_round: [ExtExpr; STATE_SIZE] = std::array::from_fn(|_| ExtExpr::zero());
    for round in 0..ZK_AUTH_CAPSULE_ACTIVE_ROUNDS {
        active_round = active_round.add(&round_eq[round]);
        if is_partial_round(round) {
            partial_round = partial_round.add(&round_eq[round]);
        }
        for input_lane in 0..STATE_SIZE {
            if is_partial_round(round) && input_lane != 0 {
                continue;
            }
            rc_round[input_lane] = rc_round[input_lane].add(
                &round_eq[round].scale_base(tower_constant(ROUND_CONSTANTS[input_lane][round])),
            );
        }
    }

    let lane_cross = mul_ext(b, &point[0], &point[1]);
    let high_zero = mul_ext(
        b,
        &point[STATE_HIGH_POINT_OFFSET].add_const(F256::ONE),
        &point[STATE_HIGH_POINT_OFFSET + 1].add_const(F256::ONE),
    );
    let active = mul_ext(b, &high_zero, &active_round);
    let partial = mul_ext(b, &high_zero, &partial_round);
    // The active rounds are the disjoint union of full and partial rounds;
    // subtraction is addition in characteristic two.
    let full = active.add(&partial);

    let rc = std::array::from_fn(|input_lane| mul_ext(b, &high_zero, &rc_round[input_lane]));
    let sigma = std::array::from_fn(|input_lane| {
        if input_lane == 0 {
            active.clone()
        } else {
            full.clone()
        }
    });
    let mds = std::array::from_fn(|input_lane| {
        let full_lane = fixed_lane_mle(&MDS_FULL, input_lane, &point[0], &point[1], &lane_cross);
        let partial_lane =
            fixed_lane_mle(&MDS_PARTIAL, input_lane, &point[0], &point[1], &lane_cross);
        mul_ext(b, &full, &full_lane).add(&mul_ext(b, &partial, &partial_lane))
    });

    debug_assert_eq!(b.num_wires() - start, ZK_AUTH_TERMINAL_FIXED_TABLE_ROWS);
    FixedTerminalTablesTrace {
        active,
        mds,
        sigma,
        rc,
    }
}

/// Evaluate the exact degree-ten AuthGKR main terminal from its five padded
/// operand claims inside the recursive field trace.
///
/// The function owns no transcript and performs no terminal pin by itself;
/// its result is intended to be passed as `expected_main_final` to the
/// disconnected ZK MLE-check verifier. Every caller-supplied point coordinate
/// and claim must be a witness expression. With valid dynamic inputs this
/// appends exactly [`ZK_AUTH_TERMINAL_TRACE_ROWS`] rows.
pub fn evaluate_auth_main_terminal_from_claims_trace(
    b: &mut FieldR1csBuilder,
    point: &[ExtExpr; ZK_AUTH_CAPSULE_BANK_VARS],
    claims: &AuthCapsuleTerminalOperandClaimsTrace,
) -> Result<ExtExpr, ZkAuthTerminalTraceError> {
    preflight_dynamic_inputs(point, claims)?;
    let start = b.num_wires();
    let tables = evaluate_fixed_terminal_tables_trace(b, point);

    let mut q = claims.increment.clone();
    for input_lane in 0..STATE_SIZE {
        let state = &claims.lane[input_lane];
        let with_rc = state.add(&tables.rc[input_lane]);
        let seventh = pow7_ext(b, &with_rc);

        // Exact characteristic-two refactor of the native expression:
        // sigma*x^7 + (1+sigma)*state = state + sigma*(x^7+state).
        let poseidon_pi = state.add(&mul_ext(b, &tables.sigma[input_lane], &seventh.add(state)));
        q = q.add(&mul_ext(b, &tables.mds[input_lane], &poseidon_pi));
    }
    let result = mul_ext(b, &tables.active, &q);

    debug_assert_eq!(b.num_wires() - start, ZK_AUTH_TERMINAL_TRACE_ROWS);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::trace::{
        alloc_block256, const_block256, pin_eq_ext, test_support::assert_ext_expr_is,
    };
    use noid_core::{Block256, TowerField};
    use noid_gkr::layers::evaluate_permutation;
    use noid_gkr::zk_auth_capsule::{
        compute_terminal_operand_claims, evaluate_auth_main_terminal_from_claims, state_cell_index,
        validate_auth_main_relation, AuthCapsuleTerminalOperandClaims, ZkAuthCapsuleBankView,
        ZK_AUTH_CAPSULE_BANK_LEN,
    };
    use noid_ivc_core::field_r1cs::FieldR1cs;
    use noid_poseidon2b::native::domain::{capacity_iv, TAG_ADDRFIX};

    const DYNAMIC_INPUT_ROWS: usize =
        2 * (ZK_AUTH_CAPSULE_BANK_VARS + ZK_AUTH_CAPSULE_TERMINAL_OPERAND_CLAIMS);
    const EXPECTED_AND_PIN_ROWS: usize = 4;
    const COMPLETE_TEST_ROWS: usize =
        1 + DYNAMIC_INPUT_ROWS + ZK_AUTH_TERMINAL_TRACE_ROWS + EXPECTED_AND_PIN_ROWS;

    fn elem(index: usize, domain: u128) -> Block128 {
        Block128::from(
            domain
                .wrapping_mul(index as u128 + 1)
                .rotate_left((index * 11 % 127) as u32)
                ^ (index as u128 + 3).wrapping_mul(0x9E37_79B9_7F4A_7C15),
        )
    }

    fn ext_elem(index: usize, domain: u128) -> Block256 {
        Block256::new(elem(index, domain), elem(index + 89, domain ^ 0xC1_256))
    }

    fn point(domain: u128) -> [Block256; ZK_AUTH_CAPSULE_BANK_VARS] {
        std::array::from_fn(|index| ext_elem(index + 19, domain))
    }

    fn claims(domain: u128) -> AuthCapsuleTerminalOperandClaims<Block256> {
        AuthCapsuleTerminalOperandClaims {
            increment: ext_elem(101, domain),
            lane: std::array::from_fn(|lane| ext_elem(131 + lane, domain)),
        }
    }

    fn alloc_case(
        b: &mut FieldR1csBuilder,
        point: &[Block256; ZK_AUTH_CAPSULE_BANK_VARS],
        claims: AuthCapsuleTerminalOperandClaims<Block256>,
    ) -> (
        [ExtExpr; ZK_AUTH_CAPSULE_BANK_VARS],
        AuthCapsuleTerminalOperandClaimsTrace,
    ) {
        (
            std::array::from_fn(|index| alloc_block256(b, point[index])),
            AuthCapsuleTerminalOperandClaimsTrace {
                increment: alloc_block256(b, claims.increment),
                lane: std::array::from_fn(|lane| alloc_block256(b, claims.lane[lane])),
            },
        )
    }

    fn pinned_relation(
        point: [Block256; ZK_AUTH_CAPSULE_BANK_VARS],
        claims: AuthCapsuleTerminalOperandClaims<Block256>,
    ) -> (FieldR1cs, Vec<F128>) {
        let expected = evaluate_auth_main_terminal_from_claims(&point, claims)
            .expect("native terminal evaluation");
        let mut b = FieldR1csBuilder::new();
        let (point_w, claims_w) = alloc_case(&mut b, &point, claims);
        let trace_start = b.num_wires();
        let result = evaluate_auth_main_terminal_from_claims_trace(&mut b, &point_w, &claims_w)
            .expect("dynamic trace inputs");
        assert_eq!(b.num_wires() - trace_start, ZK_AUTH_TERMINAL_TRACE_ROWS);
        assert_ext_expr_is(&b, &result, expected, "auth main terminal");

        let expected_w = alloc_block256(&mut b, expected);
        pin_eq_ext(&mut b, &result, &expected_w);
        let (r1cs, witness) = b.build();
        assert_eq!(r1cs.useful_rows, COMPLETE_TEST_ROWS);
        assert!(r1cs.satisfies(&witness));
        (r1cs, witness)
    }

    #[test]
    fn auth_terminal_trace_matches_native_at_varied_points_and_claims() {
        for seed in [0x11u128, 0xA771, 0xDEAD_BEEF, u64::MAX as u128] {
            let point = point(seed ^ 0x7107);
            let claims = claims(seed ^ 0xC1A1);
            let expected = evaluate_auth_main_terminal_from_claims(&point, claims).unwrap();

            let mut b = FieldR1csBuilder::new();
            let (point_w, claims_w) = alloc_case(&mut b, &point, claims);
            let start = b.num_wires();
            let result =
                evaluate_auth_main_terminal_from_claims_trace(&mut b, &point_w, &claims_w).unwrap();
            assert_eq!(b.num_wires() - start, ZK_AUTH_TERMINAL_TRACE_ROWS);
            assert_ext_expr_is(&b, &result, expected, "varied auth terminal");
            let (r1cs, witness) = b.build();
            assert!(r1cs.satisfies(&witness));
        }
    }

    #[test]
    fn auth_terminal_trace_matches_direct_bank_carrier_fixture() {
        let iv = capacity_iv(TAG_ADDRFIX);
        let input = [elem(0, 0x5EC2E7), elem(1, 0x5EC2E7), iv[0], iv[1]];
        let permutation = evaluate_permutation(input);
        let mut bank = vec![Block128::ZERO; ZK_AUTH_CAPSULE_BANK_LEN];
        for (round, row) in permutation.state.iter().enumerate() {
            for (lane, value) in row.iter().copied().enumerate() {
                bank[state_cell_index(round, lane).unwrap()] = value;
            }
        }
        let bank = ZkAuthCapsuleBankView::checked(&bank).unwrap();
        validate_auth_main_relation(bank).unwrap();

        let terminal = point(0xBA4C_C411);
        let terminal_claims = compute_terminal_operand_claims(bank, &terminal);
        let expected = evaluate_auth_main_terminal_from_claims(&terminal, terminal_claims).unwrap();
        let mut b = FieldR1csBuilder::new();
        let (point_w, claims_w) = alloc_case(&mut b, &terminal, terminal_claims);
        let result =
            evaluate_auth_main_terminal_from_claims_trace(&mut b, &point_w, &claims_w).unwrap();
        assert_ext_expr_is(&b, &result, expected, "direct bank carrier terminal");
        let (r1cs, witness) = b.build();
        assert!(r1cs.satisfies(&witness));
    }

    #[test]
    fn auth_terminal_matrix_and_exact_rows_are_witness_invariant() {
        let relation = |seed: u128| {
            let point = point(seed ^ 0xA11CE);
            let claims = claims(seed ^ 0xC1A1);
            let (r1cs, witness) = pinned_relation(point, claims);
            assert!(r1cs.satisfies(&witness));
            (r1cs.statement_digest(), r1cs.useful_rows)
        };

        let cases = [
            relation(7),
            relation(99),
            relation(0xFEED),
            relation(u64::MAX as u128),
        ];
        for case in &cases[1..] {
            assert_eq!(case.0, cases[0].0, "auth terminal matrix drift");
            assert_eq!(case.1, cases[0].1, "auth terminal row-count drift");
        }
        assert_eq!(cases[0].1, COMPLETE_TEST_ROWS);
    }

    #[test]
    fn auth_terminal_point_high_selector_claim_output_and_product_tampering_reject() {
        let point = point(0xBAD5_E1EC);
        let claims = claims(0xC0FF_EE11);
        let expected = evaluate_auth_main_terminal_from_claims(&point, claims).unwrap();

        let mut b = FieldR1csBuilder::new();
        let (point_w, claims_w) = alloc_case(&mut b, &point, claims);
        let point_wire = point_w[4].lo.terms[0].0 as usize;
        let high_wire = point_w[STATE_HIGH_POINT_OFFSET].lo.terms[0].0 as usize;
        let claim_wire = claims_w.lane[2].lo.terms[0].0 as usize;
        let product_wire = b.num_wires();
        let result =
            evaluate_auth_main_terminal_from_claims_trace(&mut b, &point_w, &claims_w).unwrap();
        let expected_w = alloc_block256(&mut b, expected);
        let output_wire = expected_w.lo.terms[0].0 as usize;
        pin_eq_ext(&mut b, &result, &expected_w);
        let (r1cs, witness) = b.build();
        assert!(r1cs.satisfies(&witness));

        for (name, wire) in [
            ("terminal point", point_wire),
            ("high selector", high_wire),
            ("operand claim", claim_wire),
            ("fixed-table product", product_wire),
            ("terminal output", output_wire),
        ] {
            let mut bad = witness.clone();
            bad[wire] += F128::ONE;
            assert!(!r1cs.satisfies(&bad), "tampered {name} survived");
        }
    }

    #[test]
    fn auth_terminal_rejects_hardcoded_dynamic_inputs_before_adding_rows() {
        let native_point = point(0xC0A5E);
        let native_claims = claims(0xD1A1);
        let mut b = FieldR1csBuilder::new();
        let (mut point_w, claims_w) = alloc_case(&mut b, &native_point, native_claims);
        point_w[7] = const_block256(native_point[7]);
        let before = b.num_wires();
        assert_eq!(
            evaluate_auth_main_terminal_from_claims_trace(&mut b, &point_w, &claims_w),
            Err(ZkAuthTerminalTraceError::DynamicInputIsConstant {
                input: ZkAuthTerminalDynamicInput::TerminalPoint,
                index: 7,
            })
        );
        assert_eq!(b.num_wires(), before, "preflight must be atomic");
    }
}
