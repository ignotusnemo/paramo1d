// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Reusable application constructors. These are ordinary object programs and
//! policies; consensus has no application-name registry or deployment allowlist.

use noid_core::Block128;
use noid_poseidon2b::primitives::Address;

use super::integer_program::{
    pack_state, Instruction, Opcode, Operand, Predicate, PredicateSource, Register,
};
use super::{policy::*, ObjectOpening, PROGRAM_STEPS};

const KEEP_STATE: [[Block128; 2]; PROGRAM_STEPS] = [[Block128(0); 2]; PROGRAM_STEPS];

/// The payee may collect before expiry; the payer may recover at or after it.
/// No continuing call can drain the payment, and its closing fee is capped.
pub fn refundable_payment(
    payer: Address,
    payee: Address,
    expiry_height: u64,
    max_fee: u64,
) -> ObjectOpening {
    ObjectOpening {
        program: KEEP_STATE,
        state: Block128(0),
        claim_authority: payee,
        recovery_authority: payer,
        deadline: expiry_height,
        claim_recipient: payee,
        recovery_recipient: payer,
        rules: ObjectRules {
            max_fee,
            min_retained: 0,
            max_payout: 0,
            modes: CLAIM_CLOSE | RECOVERY_CLOSE,
        },
    }
}

/// Even the owner's correct authorization cannot spend before the unlock
/// height. Withdrawal then returns the balance, minus a capped fee, to owner.
pub fn timelocked_vault(owner: Address, unlock_height: u64, max_fee: u64) -> ObjectOpening {
    ObjectOpening {
        program: KEEP_STATE,
        state: Block128(0),
        claim_authority: owner,
        recovery_authority: owner,
        deadline: unlock_height,
        claim_recipient: owner,
        recovery_recipient: owner,
        rules: ObjectRules {
            max_fee,
            min_retained: 0,
            max_payout: 0,
            modes: RECOVERY_CLOSE,
        },
    }
}

/// A spending key can make bounded payments while preserving a reserve. It
/// cannot close the object. At expiry only the recovery key can withdraw the
/// remainder. The limit is per call, not per day or per key lifetime.
#[allow(clippy::too_many_arguments)]
pub fn allowance_wallet(
    spending_key: Address,
    recovery_key: Address,
    payout_recipient: Option<Address>,
    recover_at: u64,
    max_fee: u64,
    max_payout: u64,
    min_retained: u64,
) -> ObjectOpening {
    ObjectOpening {
        program: KEEP_STATE,
        state: Block128(0),
        claim_authority: spending_key,
        recovery_authority: recovery_key,
        deadline: recover_at,
        claim_recipient: payout_recipient.unwrap_or(spending_key),
        recovery_recipient: recovery_key,
        rules: ObjectRules {
            max_fee,
            min_retained,
            max_payout,
            modes: CLAIM_CONTINUE
                | RECOVERY_CLOSE
                | if payout_recipient.is_none() {
                    ANY_PAYOUT_RECIPIENT
                } else {
                    0
                },
        },
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScheduleError {
    EmptyPeriod,
    EmptyAmount,
    DeadlineBeforeStart,
    HeightOverflow,
    FeeExceedsBudget,
}

impl core::fmt::Display for ScheduleError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "contract schedule: {self:?}")
    }
}

impl std::error::Error for ScheduleError {}

fn validate_schedule(start: u64, period: u64, deadline: u64) -> Result<(), ScheduleError> {
    if period == 0 {
        return Err(ScheduleError::EmptyPeriod);
    }
    if start >= deadline {
        return Err(ScheduleError::DeadlineBeforeStart);
    }
    // Every height at which a claim is allowed must admit a next due height.
    // Recovery must never depend on a wrapping height calculation.
    if (deadline - 1).checked_add(period).is_none() {
        return Err(ScheduleError::HeightOverflow);
    }
    Ok(())
}

fn install(opening: &mut ObjectOpening, instructions: &[Instruction]) {
    assert!(instructions.len() <= PROGRAM_STEPS);
    for (target, instruction) in opening.program.iter_mut().zip(instructions) {
        *target = instruction.to_fields();
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PeriodBudget {
    pub start_height: u64,
    pub period_blocks: u64,
    /// Total debit per window, including transaction fees.
    pub budget: u64,
    pub recover_at: u64,
    pub max_fee: u64,
    pub max_payout: u64,
    pub min_retained: u64,
}

/// Enforce a budget across successive calls and recipients. The first window
/// starts at `start_height`. Once a window expires, the first successful call
/// starts a new window of `period_blocks`; unused budget is discarded. This is
/// not a trailing-window limit or a wall-clock scheduler. A recovery close at
/// the deadline returns the remainder without running the spending checks.
pub fn period_budget_wallet(
    spending_key: Address,
    recovery_key: Address,
    payout_recipient: Option<Address>,
    terms: PeriodBudget,
) -> Result<ObjectOpening, ScheduleError> {
    validate_schedule(terms.start_height, terms.period_blocks, terms.recover_at)?;
    if terms.budget == 0 {
        return Err(ScheduleError::EmptyAmount);
    }
    if terms.max_fee > terms.budget {
        return Err(ScheduleError::FeeExceedsBudget);
    }
    let mut opening = allowance_wallet(
        spending_key,
        recovery_key,
        payout_recipient,
        terms.recover_at,
        terms.max_fee,
        terms.max_payout,
        terms.min_retained.max(terms.max_fee),
    );
    opening.state = pack_state([terms.budget, terms.start_height + terms.period_blocks]);
    let before = Predicate::BEFORE_DEADLINE;
    let reset = Predicate {
        source: PredicateSource::Scratch0,
        inverted: true,
    };
    use {Opcode::*, Operand as O, Register as R};
    install(
        &mut opening,
        &[
            Instruction::new(
                AssertLessOrEqual,
                R::State0,
                O::Immediate,
                O::Height,
                terms.start_height,
            )
            .when(before),
            Instruction::new(LessThan, R::Scratch0, O::Height, O::State1, 0),
            // Disable all reset arithmetic on the recovery path.
            Instruction::new(Move, R::Scratch0, O::One, O::Zero, 0).when(before.not()),
            Instruction::new(Move, R::State0, O::Immediate, O::Zero, terms.budget).when(reset),
            Instruction::new(Add, R::State1, O::Height, O::Immediate, terms.period_blocks)
                .when(reset),
            Instruction::new(Add, R::Scratch1, O::Fee, O::Payout, 0).when(before),
            Instruction::new(AssertLessOrEqual, R::State0, O::Scratch1, O::State0, 0).when(before),
            Instruction::new(Subtract, R::State0, O::State0, O::Scratch1, 0).when(before),
        ],
    );
    Ok(opening)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RecurringPayment {
    pub first_due_height: u64,
    pub period_blocks: u64,
    pub payment: u64,
    pub recover_at: u64,
    pub max_fee: u64,
}

/// A payee can collect one fixed prepaid payment when due. A successful call
/// schedules the next payment relative to its inclusion height, so missed
/// periods do not accumulate charges. Someone must submit each transaction;
/// the contract does not create autonomous transactions. Only the payer may
/// close at expiry. A closing-fee reserve remains throughout the claim phase.
pub fn recurring_payment(
    payer: Address,
    payee: Address,
    terms: RecurringPayment,
) -> Result<ObjectOpening, ScheduleError> {
    validate_schedule(
        terms.first_due_height,
        terms.period_blocks,
        terms.recover_at,
    )?;
    if terms.payment == 0 {
        return Err(ScheduleError::EmptyAmount);
    }
    let mut opening = allowance_wallet(
        payee,
        payer,
        Some(payee),
        terms.recover_at,
        terms.max_fee,
        terms.payment,
        terms.max_fee,
    );
    opening.state = pack_state([0, terms.first_due_height]);
    let before = Predicate::BEFORE_DEADLINE;
    use {Opcode::*, Operand as O, Register as R};
    install(
        &mut opening,
        &[
            Instruction::new(AssertLessOrEqual, R::State0, O::State1, O::Height, 0).when(before),
            Instruction::new(
                AssertEqual,
                R::State0,
                O::Payout,
                O::Immediate,
                terms.payment,
            )
            .when(before),
            Instruction::new(Add, R::State0, O::State0, O::One, 0).when(before),
            Instruction::new(Add, R::State1, O::Height, O::Immediate, terms.period_blocks)
                .when(before),
        ],
    );
    Ok(opening)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrancheVesting {
    pub first_unlock_height: u64,
    pub period_blocks: u64,
    pub tranche_amount: u64,
    pub mature_at: u64,
    pub max_fee: u64,
}

/// Release fixed tranches to a beneficiary on an anchored block schedule.
/// Missed tranches remain claimable, one per call, because each successful
/// claim advances the previous due height rather than the current height.
/// At maturity the beneficiary can withdraw the entire remaining balance.
/// This is discrete vesting, not continuous proportional accrual.
pub fn tranche_vesting(
    beneficiary: Address,
    terms: TrancheVesting,
) -> Result<ObjectOpening, ScheduleError> {
    validate_schedule(
        terms.first_unlock_height,
        terms.period_blocks,
        terms.mature_at,
    )?;
    if terms.tranche_amount == 0 {
        return Err(ScheduleError::EmptyAmount);
    }
    let mut opening = allowance_wallet(
        beneficiary,
        beneficiary,
        Some(beneficiary),
        terms.mature_at,
        terms.max_fee,
        terms.tranche_amount,
        terms.max_fee,
    );
    opening.state = pack_state([0, terms.first_unlock_height]);
    let before = Predicate::BEFORE_DEADLINE;
    use {Opcode::*, Operand as O, Register as R};
    install(
        &mut opening,
        &[
            Instruction::new(AssertLessOrEqual, R::State0, O::State1, O::Height, 0).when(before),
            Instruction::new(
                AssertEqual,
                R::State0,
                O::Payout,
                O::Immediate,
                terms.tranche_amount,
            )
            .when(before),
            Instruction::new(Add, R::State0, O::State0, O::Payout, 0).when(before),
            Instruction::new(Add, R::State1, O::State1, O::Immediate, terms.period_blocks)
                .when(before),
        ],
    );
    Ok(opening)
}
