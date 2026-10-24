// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Bounded integer programs for the unfrozen v2 object ABI.
//!
//! Two persistent u64 registers share the existing 128-bit object state.
//! Two scratch registers start at zero on every call. Sixteen committed
//! instructions execute in order, with no jumps or loops. Context values
//! must come from the authenticated inclusion height and transaction body.

use noid_core::Block128;

pub const PROGRAM_STEPS: usize = 16;
pub const OPERAND_COUNT: usize = 24;
pub const OPCODE_COUNT: usize = 10;
pub const PREDICATE_COUNT: usize = 6;
pub const INSTRUCTION_BITS: usize = 20;
pub type Program = [[Block128; 2]; PROGRAM_STEPS];
pub const EMPTY_PROGRAM: Program = [[Block128(0); 2]; PROGRAM_STEPS];

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
#[repr(u8)]
pub enum Register {
    State0 = 0,
    State1 = 1,
    Scratch0 = 2,
    Scratch1 = 3,
}

impl Register {
    fn decode(value: u8) -> Self {
        match value {
            0 => Self::State0,
            1 => Self::State1,
            2 => Self::Scratch0,
            3 => Self::Scratch1,
            _ => unreachable!("two register bits"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
#[repr(u8)]
pub enum Operand {
    State0 = 0,
    State1 = 1,
    Scratch0 = 2,
    Scratch1 = 3,
    Immediate = 4,
    Height = 5,
    Fee = 6,
    Payout = 7,
    Retained = 8,
    InputAmount = 9,
    BeforeDeadline = 10,
    Terminal = 11,
    HasPayout = 12,
    Zero = 13,
    One = 14,
    AfterDeadline = 15,
    PayoutOwner0 = 16,
    PayoutOwner1 = 17,
    PayoutOwner2 = 18,
    PayoutOwner3 = 19,
    InputCreationId = 20,
    InputSlot = 21,
    RetainedSlot = 22,
    PayoutSlot = 23,
}

impl Operand {
    pub const ALL: [Self; OPERAND_COUNT] = [
        Self::State0,
        Self::State1,
        Self::Scratch0,
        Self::Scratch1,
        Self::Immediate,
        Self::Height,
        Self::Fee,
        Self::Payout,
        Self::Retained,
        Self::InputAmount,
        Self::BeforeDeadline,
        Self::Terminal,
        Self::HasPayout,
        Self::Zero,
        Self::One,
        Self::AfterDeadline,
        Self::PayoutOwner0,
        Self::PayoutOwner1,
        Self::PayoutOwner2,
        Self::PayoutOwner3,
        Self::InputCreationId,
        Self::InputSlot,
        Self::RetainedSlot,
        Self::PayoutSlot,
    ];
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
#[repr(u8)]
pub enum Opcode {
    Keep = 0,
    Move = 1,
    Add = 2,
    Subtract = 3,
    Min = 4,
    Max = 5,
    LessThan = 6,
    Equal = 7,
    AssertEqual = 8,
    AssertLessOrEqual = 9,
}

impl Opcode {
    pub const ALL: [Self; OPCODE_COUNT] = [
        Self::Keep,
        Self::Move,
        Self::Add,
        Self::Subtract,
        Self::Min,
        Self::Max,
        Self::LessThan,
        Self::Equal,
        Self::AssertEqual,
        Self::AssertLessOrEqual,
    ];
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
#[repr(u8)]
pub enum PredicateSource {
    Always = 0,
    BeforeDeadline = 1,
    Terminal = 2,
    HasPayout = 3,
    Scratch0 = 4,
    Scratch1 = 5,
}

impl PredicateSource {
    pub const ALL: [Self; PREDICATE_COUNT] = [
        Self::Always,
        Self::BeforeDeadline,
        Self::Terminal,
        Self::HasPayout,
        Self::Scratch0,
        Self::Scratch1,
    ];
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Predicate {
    pub source: PredicateSource,
    pub inverted: bool,
}

impl Predicate {
    pub const ALWAYS: Self = Self {
        source: PredicateSource::Always,
        inverted: false,
    };
    pub const BEFORE_DEADLINE: Self = Self {
        source: PredicateSource::BeforeDeadline,
        inverted: false,
    };

    pub const fn not(self) -> Self {
        Self {
            inverted: !self.inverted,
            ..self
        }
    }
}

/// A canonical pair of fields: a 20-bit descriptor and a u64 immediate.
/// Every descriptor field is committed even when the operation ignores it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Instruction {
    pub opcode: Opcode,
    pub destination: Register,
    pub left: Operand,
    pub right: Operand,
    pub predicate: Predicate,
    pub immediate: u64,
}

impl Instruction {
    pub const fn new(
        opcode: Opcode,
        destination: Register,
        left: Operand,
        right: Operand,
        immediate: u64,
    ) -> Self {
        Self {
            opcode,
            destination,
            left,
            right,
            predicate: Predicate::ALWAYS,
            immediate,
        }
    }

    pub const fn when(self, predicate: Predicate) -> Self {
        Self { predicate, ..self }
    }

    pub const fn to_fields(self) -> [Block128; 2] {
        let descriptor = (self.opcode as u128)
            | ((self.destination as u128) << 4)
            | ((self.left as u128) << 6)
            | ((self.right as u128) << 11)
            | ((self.predicate.source as u128) << 16)
            | ((self.predicate.inverted as u128) << 19);
        [Block128(descriptor), Block128(self.immediate as u128)]
    }

    pub fn from_fields(fields: [Block128; 2]) -> Option<Self> {
        let word = fields[0].0;
        if word >> INSTRUCTION_BITS != 0 || fields[1].0 > u64::MAX as u128 {
            return None;
        }
        Some(Self {
            opcode: *Opcode::ALL.get((word & 15) as usize)?,
            destination: Register::decode(((word >> 4) & 3) as u8),
            left: *Operand::ALL.get(((word >> 6) & 31) as usize)?,
            right: *Operand::ALL.get(((word >> 11) & 31) as usize)?,
            predicate: Predicate {
                source: *PredicateSource::ALL.get(((word >> 16) & 7) as usize)?,
                inverted: word & (1 << 19) != 0,
            },
            immediate: fields[1].0 as u64,
        })
    }
}

/// Values supplied by the enclosing authenticated object transition.
/// Payout-owner words are little-endian chunks of the canonical 32-byte owner.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Context {
    pub height: u64,
    pub fee: u64,
    pub payout: u64,
    pub retained: u64,
    pub input_amount: u64,
    pub before_deadline: bool,
    pub terminal: bool,
    pub has_payout: bool,
    pub payout_owner: [u64; 4],
    pub input_creation_id: u64,
    pub input_slot: u32,
    pub retained_slot: u32,
    pub payout_slot: u32,
}

impl Context {
    pub fn from_body(body: &crate::TxBody, height: u64, deadline: u64) -> Self {
        Self {
            height,
            fee: body.fee,
            payout: body.outputs[1].amount,
            retained: body.outputs[0].amount,
            input_amount: body.inputs[0].amount,
            before_deadline: height < deadline,
            terminal: body.validity_bitmap & crate::PAGED_SPEND_TERMINAL_BIT != 0,
            has_payout: body.validity_bitmap & crate::output_bitmap_bit(1) != 0,
            payout_owner: std::array::from_fn(|word| {
                u64::from_le_bytes(
                    body.outputs[1].owner.0[word * 8..word * 8 + 8]
                        .try_into()
                        .unwrap(),
                )
            }),
            input_creation_id: body.inputs[0].creation_id,
            input_slot: body.inputs[0].slot_index,
            retained_slot: body.outputs[0].slot_index,
            payout_slot: body.outputs[1].slot_index,
        }
    }

    pub fn operands(self, registers: [u64; 4], immediate: u64) -> [u64; OPERAND_COUNT] {
        [
            registers[0],
            registers[1],
            registers[2],
            registers[3],
            immediate,
            self.height,
            self.fee,
            self.payout,
            self.retained,
            self.input_amount,
            u64::from(self.before_deadline),
            u64::from(self.terminal),
            u64::from(self.has_payout),
            0,
            1,
            u64::from(!self.before_deadline),
            self.payout_owner[0],
            self.payout_owner[1],
            self.payout_owner[2],
            self.payout_owner[3],
            self.input_creation_id,
            u64::from(self.input_slot),
            u64::from(self.retained_slot),
            u64::from(self.payout_slot),
        ]
    }

    fn predicates(self, registers: [u64; 4]) -> [u64; PREDICATE_COUNT] {
        [
            1,
            u64::from(self.before_deadline),
            u64::from(self.terminal),
            u64::from(self.has_payout),
            registers[2],
            registers[3],
        ]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProgramError {
    Encoding { step: usize },
    NonBooleanPredicate { step: usize },
    Overflow { step: usize },
    Underflow { step: usize },
    Assertion { step: usize },
}

impl core::fmt::Display for ProgramError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "object program: {self:?}")
    }
}

impl std::error::Error for ProgramError {}

pub fn validate(program: &Program) -> Result<(), ProgramError> {
    for (step, fields) in program.iter().copied().enumerate() {
        Instruction::from_fields(fields).ok_or(ProgramError::Encoding { step })?;
    }
    Ok(())
}

pub const fn unpack_state(state: Block128) -> [u64; 2] {
    [state.0 as u64, (state.0 >> 64) as u64]
}

pub const fn pack_state(state: [u64; 2]) -> Block128 {
    Block128(state[0] as u128 | ((state[1] as u128) << 64))
}

pub fn execute(
    program: &Program,
    current: Block128,
    context: Context,
) -> Result<Block128, ProgramError> {
    validate(program)?;
    let state = unpack_state(current);
    let mut registers = [state[0], state[1], 0, 0];
    for (step, fields) in program.iter().copied().enumerate() {
        let instruction = Instruction::from_fields(fields).expect("validated program");
        let predicate = context.predicates(registers)[instruction.predicate.source as usize];
        if predicate > 1 {
            return Err(ProgramError::NonBooleanPredicate { step });
        }
        if (predicate == 1) == instruction.predicate.inverted {
            continue;
        }
        let operands = context.operands(registers, instruction.immediate);
        let left = operands[instruction.left as usize];
        let right = operands[instruction.right as usize];
        let destination = instruction.destination as usize;
        registers[destination] = match instruction.opcode {
            Opcode::Keep => registers[destination],
            Opcode::Move => left,
            Opcode::Add => left
                .checked_add(right)
                .ok_or(ProgramError::Overflow { step })?,
            Opcode::Subtract => left
                .checked_sub(right)
                .ok_or(ProgramError::Underflow { step })?,
            Opcode::Min => left.min(right),
            Opcode::Max => left.max(right),
            Opcode::LessThan => u64::from(left < right),
            Opcode::Equal => u64::from(left == right),
            Opcode::AssertEqual => {
                if left != right {
                    return Err(ProgramError::Assertion { step });
                }
                registers[destination]
            }
            Opcode::AssertLessOrEqual => {
                if left > right {
                    return Err(ProgramError::Assertion { step });
                }
                registers[destination]
            }
        };
    }
    Ok(pack_state([registers[0], registers[1]]))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn descriptor_roundtrip_and_reserved_encodings_reject() {
        for opcode in Opcode::ALL {
            for source in Operand::ALL {
                for predicate in PredicateSource::ALL {
                    let instruction = Instruction::new(
                        opcode,
                        Register::State1,
                        source,
                        Operand::Immediate,
                        u64::MAX,
                    )
                    .when(Predicate {
                        source: predicate,
                        inverted: true,
                    });
                    assert_eq!(
                        Instruction::from_fields(instruction.to_fields()),
                        Some(instruction)
                    );
                }
            }
        }
        for word in [
            10,
            15,
            24 << 6,
            31 << 11,
            6 << 16,
            7 << 16,
            1 << INSTRUCTION_BITS,
            u128::MAX,
        ] {
            assert!(
                Instruction::from_fields([Block128(word), Block128(0)]).is_none(),
                "word={word}"
            );
        }
        assert!(Instruction::from_fields([Block128(0), Block128(1u128 << 64)]).is_none());
    }

    fn single(opcode: Opcode, left: u64, right: u64) -> Result<Block128, ProgramError> {
        let mut program = EMPTY_PROGRAM;
        program[0] = Instruction::new(
            opcode,
            Register::State0,
            Operand::State0,
            Operand::Immediate,
            right,
        )
        .to_fields();
        execute(&program, pack_state([left, 37]), Context::default())
    }

    #[test]
    fn arithmetic_is_integer_and_fails_closed_at_u64_boundaries() {
        assert_eq!(single(Opcode::Add, 1, 1), Ok(pack_state([2, 37])));
        assert_eq!(
            single(Opcode::Add, u64::MAX - 1, 1),
            Ok(pack_state([u64::MAX, 37]))
        );
        assert_eq!(
            single(Opcode::Add, u64::MAX, 1),
            Err(ProgramError::Overflow { step: 0 })
        );
        assert_eq!(
            single(Opcode::Subtract, 0, 1),
            Err(ProgramError::Underflow { step: 0 })
        );
        assert_eq!(
            single(Opcode::Subtract, u64::MAX, u64::MAX),
            Ok(pack_state([0, 37]))
        );
        assert_eq!(single(Opcode::Min, u64::MAX, 1), Ok(pack_state([1, 37])));
        assert_eq!(
            single(Opcode::Max, 1, u64::MAX),
            Ok(pack_state([u64::MAX, 37]))
        );
        assert_eq!(single(Opcode::LessThan, 1, 2), Ok(pack_state([1, 37])));
        assert_eq!(single(Opcode::Equal, 2, 2), Ok(pack_state([1, 37])));
        assert_eq!(
            single(Opcode::AssertEqual, 1, 2),
            Err(ProgramError::Assertion { step: 0 })
        );
        assert_eq!(
            single(Opcode::AssertLessOrEqual, 2, 1),
            Err(ProgramError::Assertion { step: 0 })
        );
    }

    #[test]
    fn guarded_arithmetic_does_not_block_recovery_or_wrap_a_counter() {
        let mut program = EMPTY_PROGRAM;
        program[0] = Instruction::new(
            Opcode::Add,
            Register::State0,
            Operand::State0,
            Operand::One,
            0,
        )
        .when(Predicate::BEFORE_DEADLINE)
        .to_fields();
        let state = pack_state([u64::MAX, 0]);
        assert_eq!(execute(&program, state, Context::default()), Ok(state));
        assert_eq!(
            execute(
                &program,
                state,
                Context {
                    before_deadline: true,
                    ..Context::default()
                }
            ),
            Err(ProgramError::Overflow { step: 0 })
        );
        program[0] = Instruction::new(
            Opcode::Move,
            Register::Scratch0,
            Operand::Immediate,
            Operand::Zero,
            2,
        )
        .to_fields();
        program[1] = Instruction::new(
            Opcode::Move,
            Register::State0,
            Operand::One,
            Operand::Zero,
            0,
        )
        .when(Predicate {
            source: PredicateSource::Scratch0,
            inverted: false,
        })
        .to_fields();
        assert_eq!(
            execute(&program, state, Context::default()),
            Err(ProgramError::NonBooleanPredicate { step: 1 })
        );
    }

    #[test]
    fn context_sources_and_scratch_reset_are_explicit() {
        let mut program = EMPTY_PROGRAM;
        program[0] = Instruction::new(
            Opcode::Move,
            Register::State0,
            Operand::Height,
            Operand::Zero,
            0,
        )
        .to_fields();
        program[1] = Instruction::new(
            Opcode::Move,
            Register::State1,
            Operand::PayoutOwner3,
            Operand::Zero,
            0,
        )
        .to_fields();
        let context = Context {
            height: 91,
            payout_owner: [12, 23, 34, 45],
            ..Context::default()
        };
        assert_eq!(
            execute(&program, pack_state([1, 2]), context),
            Ok(pack_state([91, 45]))
        );
        program[0] = Instruction::new(
            Opcode::Move,
            Register::State0,
            Operand::Scratch0,
            Operand::Zero,
            0,
        )
        .to_fields();
        program[1] = Instruction::new(
            Opcode::Move,
            Register::Scratch0,
            Operand::Immediate,
            Operand::Zero,
            17,
        )
        .to_fields();
        let first = execute(&program, pack_state([1, 2]), context).unwrap();
        assert_eq!(unpack_state(first)[0], 0);
        assert_eq!(
            unpack_state(execute(&program, first, context).unwrap())[0],
            0
        );
    }
}
