// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! V2 contract carrier. Activation belongs to the network's fork schedule.
//! Commitments and execution match the bounded
//! integer HistoryStep relation and its authenticated transaction context.

pub mod applications;
pub mod integer_program;
pub mod policy;
pub use policy::ObjectRules;

use noid_core::Block128;
use noid_poseidon2b::native::{capacity_iv, DomainTag, Poseidon2bSponge};
use noid_poseidon2b::primitives::{Address, Digest};

use crate::{
    body_hash::*, output_bitmap_bit, validate_paged_spend, PagedSpendIntent, TxBody, TxInput,
    TxOutput, TxPage, MAX_TX_AUTHORIZATION_BYTES, PAGED_SPEND_CONTRACT_BIT, PAGED_SPEND_END_BIT,
    PAGED_SPEND_START_BIT, PAGED_SPEND_TERMINAL_BIT, TX_BODY_WIRE_SIZE, TX_INPUTS, TX_OUTPUTS,
};

pub const PROGRAM_STEPS: usize = integer_program::PROGRAM_STEPS;
/// Raw body fields carried by the component witness and bound to its spine.
/// This count is independent of the number of program instructions.
pub const BODY_CONTEXT_FIELDS: usize = 8;
/// Default for component research fixtures; production uses the pinned bank's
/// per-class call budget and never derives it from this value.
pub const CONTRACT_SLOTS: usize = 16;
pub const OBJECT_VERSION: u16 = 3;
const OPENING_MAGIC: &[u8; 8] = b"NOIDOBJ3";
pub const INTENT_MAGIC: &[u8; 8] = b"NOIDV2TX";
pub const OPENING_BYTES: usize = 8 + 2 + PROGRAM_STEPS * 32 + 16 + 4 * 32 + 8 + policy::RULE_BYTES;
pub const INTENT_PREFIX_BYTES: usize = INTENT_MAGIC.len() + OPENING_BYTES;
pub const MAX_INTENT_BYTES: usize =
    INTENT_PREFIX_BYTES + 7 + TX_BODY_WIRE_SIZE + MAX_TX_AUTHORIZATION_BYTES;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectError {
    Encoding,
    Version,
    Opcode { step: usize },
    Shape,
    OldObject,
    Successor,
    Recipient,
    Balance,
    Policy,
    FeeLimit,
    ReserveLimit,
    PayoutLimit,
    Program(integer_program::ProgramError),
    Page(String),
}

impl core::fmt::Display for ObjectError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "contract: {self:?}")
    }
}
impl std::error::Error for ObjectError {}

/// Holder-retained current opening. The State slot retains only its root,
/// amount and creation id. An opening alone is not an inclusion receipt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectOpening {
    pub program: [[Block128; 2]; PROGRAM_STEPS],
    pub state: Block128,
    pub claim_authority: Address,
    pub recovery_authority: Address,
    pub deadline: u64,
    pub claim_recipient: Address,
    pub recovery_recipient: Address,
    pub rules: ObjectRules,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedTransition {
    pub next: Block128,
    pub contexts: [Block128; BODY_CONTEXT_FIELDS],
    pub authority: Address,
    pub terminal: bool,
}

impl ObjectOpening {
    pub fn validate(&self) -> Result<(), ObjectError> {
        self.rules.validate()?;
        for (step, instruction) in self.program.iter().enumerate() {
            if integer_program::Instruction::from_fields(*instruction).is_none() {
                return Err(ObjectError::Opcode { step });
            }
        }
        Ok(())
    }

    pub fn code_id(&self) -> Digest {
        let mut code = Poseidon2bSponge::with_iv(capacity_iv(DomainTag::new(b"CNTCODE_")));
        for instruction in self.program {
            code.absorb_pair(instruction[0], instruction[1]);
        }
        code.finalize_no_pad()
    }

    pub fn root(&self) -> Address {
        let code = Address(self.code_id()).as_fields();
        let claim = self.claim_authority.as_fields();
        let recovery = self.recovery_authority.as_fields();
        let recipient = self.claim_recipient.as_fields();
        let refund = self.recovery_recipient.as_fields();
        let rules = self.rules.fields();
        let mut policy = Poseidon2bSponge::with_iv(capacity_iv(DomainTag::new(b"CNTPOL__")));
        for pair in [
            code,
            [Block128(self.deadline as u128), claim[0]],
            [claim[1], recovery[0]],
            [recovery[1], recipient[0]],
            [recipient[1], refund[0]],
            [refund[1], Block128(OBJECT_VERSION as u128)],
            [rules[0], rules[1]],
            [rules[2], rules[3]],
        ] {
            policy.absorb_pair(pair[0], pair[1]);
        }
        let policy = Address(policy.finalize_no_pad()).as_fields();
        let mut object = Poseidon2bSponge::with_iv(capacity_iv(DomainTag::new(b"CNTOBJ__")));
        object.absorb_pair(policy[0], policy[1]);
        object.absorb_pair(self.state, Block128(0));
        Address(object.finalize_no_pad())
    }

    pub fn authority_at(&self, height: u64) -> Address {
        if height < self.deadline {
            self.claim_authority
        } else {
            self.recovery_authority
        }
    }

    pub fn recipient_at(&self, height: u64) -> Address {
        if height < self.deadline {
            self.claim_recipient
        } else {
            self.recovery_recipient
        }
    }

    pub fn successor(&self, next: Block128) -> Self {
        Self {
            state: next,
            ..self.clone()
        }
    }

    pub fn execute(&self, body: &TxBody, height: u64) -> Result<Block128, ObjectError> {
        self.validate()?;
        integer_program::execute(
            &self.program,
            self.state,
            integer_program::Context::from_body(body, height, self.deadline),
        )
        .map_err(ObjectError::Program)
    }

    /// Native preflight; the enclosing HistoryStep still proves every binding.
    /// Height is supplied by the admitting node / block, never by the wire.
    pub fn check_call(&self, page: &TxPage, height: u64) -> Result<CheckedTransition, ObjectError> {
        self.validate()?;
        validate_paged_spend(std::slice::from_ref(page))
            .map_err(|e| ObjectError::Page(e.to_string()))?;
        let body = &page.body;
        let base = 1
            | output_bitmap_bit(0)
            | PAGED_SPEND_START_BIT
            | PAGED_SPEND_END_BIT
            | PAGED_SPEND_CONTRACT_BIT;
        let terminal = body.validity_bitmap & PAGED_SPEND_TERMINAL_BIT != 0;
        let expected = base
            | if terminal {
                PAGED_SPEND_TERMINAL_BIT
            } else {
                body.validity_bitmap & output_bitmap_bit(1)
            };
        if body.is_coinbase || body.validity_bitmap != expected {
            return Err(ObjectError::Shape);
        }
        if body.input_owner != self.root() {
            return Err(ObjectError::OldObject);
        }
        if !self.rules.permits(height < self.deadline, terminal) {
            return Err(ObjectError::Policy);
        }
        if body.fee > self.rules.max_fee {
            return Err(ObjectError::FeeLimit);
        }
        if !terminal {
            if body.outputs[0].amount < self.rules.min_retained {
                return Err(ObjectError::ReserveLimit);
            }
            if body.outputs[1].amount > self.rules.max_payout {
                return Err(ObjectError::PayoutLimit);
            }
            if body.validity_bitmap & output_bitmap_bit(1) != 0
                && self.rules.modes & policy::ANY_PAYOUT_RECIPIENT == 0
                && body.outputs[1].owner != self.recipient_at(height)
            {
                return Err(ObjectError::Recipient);
            }
        }
        let next = self.execute(body, height)?;
        if terminal {
            if body.outputs[0].owner != self.recipient_at(height) {
                return Err(ObjectError::Recipient);
            }
        } else if body.outputs[0].owner != self.successor(next).root() {
            return Err(ObjectError::Successor);
        }
        Ok(CheckedTransition {
            next,
            contexts: transaction_contexts(body),
            authority: self.authority_at(height),
            terminal,
        })
    }

    /// One-input, one-output call obeying the committed spending rules.
    pub fn build_call(
        &self,
        input: TxInput,
        output_slot: u32,
        fee: u64,
        epoch_anchor: Digest,
        height: u64,
        terminal: bool,
    ) -> Result<TxPage, ObjectError> {
        self.build_call_inner(
            input,
            output_slot,
            fee,
            epoch_anchor,
            height,
            terminal,
            None,
        )
    }

    /// A bounded payment while retaining the successor object in output zero.
    pub fn build_payment(
        &self,
        input: TxInput,
        successor_slot: u32,
        fee: u64,
        epoch_anchor: Digest,
        height: u64,
        payout: TxOutput,
    ) -> Result<TxPage, ObjectError> {
        self.build_call_inner(
            input,
            successor_slot,
            fee,
            epoch_anchor,
            height,
            false,
            Some(payout),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn build_call_inner(
        &self,
        input: TxInput,
        output_slot: u32,
        fee: u64,
        epoch_anchor: Digest,
        height: u64,
        terminal: bool,
        payout: Option<TxOutput>,
    ) -> Result<TxPage, ObjectError> {
        self.validate()?;
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        inputs[0] = input;
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: output_slot,
            amount: input
                .amount
                .checked_sub(fee)
                .and_then(|amount| amount.checked_sub(payout.map_or(0, |output| output.amount)))
                .ok_or(ObjectError::Balance)?,
            owner: Address([0; 32]),
        };
        if let Some(payout) = payout {
            outputs[1] = payout;
        }
        let mut body = TxBody {
            epoch_anchor,
            fee,
            input_owner: self.root(),
            inputs,
            outputs,
            validity_bitmap: 1
                | output_bitmap_bit(0)
                | PAGED_SPEND_START_BIT
                | PAGED_SPEND_END_BIT
                | PAGED_SPEND_CONTRACT_BIT
                | if payout.is_some() {
                    output_bitmap_bit(1)
                } else {
                    0
                }
                | if terminal {
                    PAGED_SPEND_TERMINAL_BIT
                } else {
                    0
                },
            is_coinbase: false,
        };
        body.outputs[0].owner = if terminal {
            self.recipient_at(height)
        } else {
            self.successor(self.execute(&body, height)?).root()
        };
        let page = TxPage::new(body).map_err(|e| ObjectError::Page(e.to_string()))?;
        self.check_call(&page, height)?;
        Ok(page)
    }

    /// Funding is an ordinary authorized payment to an opened root. There is
    /// no unique constructor namespace or authenticated historical origin yet.
    pub fn funding_output(&self, slot_index: u32, amount: u64) -> Result<TxOutput, ObjectError> {
        self.validate()?;
        Ok(TxOutput {
            slot_index,
            amount,
            owner: self.root(),
        })
    }

    pub fn to_bytes(&self) -> Result<[u8; OPENING_BYTES], ObjectError> {
        self.validate()?;
        let mut bytes = Vec::with_capacity(OPENING_BYTES);
        bytes.extend_from_slice(OPENING_MAGIC);
        bytes.extend_from_slice(&OBJECT_VERSION.to_le_bytes());
        for instruction in self.program {
            for field in instruction {
                bytes.extend_from_slice(&field.0.to_le_bytes());
            }
        }
        bytes.extend_from_slice(&self.state.0.to_le_bytes());
        bytes.extend_from_slice(&self.claim_authority.0);
        bytes.extend_from_slice(&self.recovery_authority.0);
        bytes.extend_from_slice(&self.deadline.to_le_bytes());
        bytes.extend_from_slice(&self.claim_recipient.0);
        bytes.extend_from_slice(&self.recovery_recipient.0);
        bytes.extend_from_slice(&self.rules.max_fee.to_le_bytes());
        bytes.extend_from_slice(&self.rules.min_retained.to_le_bytes());
        bytes.extend_from_slice(&self.rules.max_payout.to_le_bytes());
        bytes.push(self.rules.modes);
        Ok(bytes.try_into().expect("fixed opening length"))
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ObjectError> {
        if bytes.len() != OPENING_BYTES || &bytes[..8] != OPENING_MAGIC {
            return Err(ObjectError::Encoding);
        }
        if u16::from_le_bytes(bytes[8..10].try_into().unwrap()) != OBJECT_VERSION {
            return Err(ObjectError::Version);
        }
        let mut cursor = 10;
        let mut take = |len: usize| {
            let slice = &bytes[cursor..cursor + len];
            cursor += len;
            slice
        };
        let opening = Self {
            program: std::array::from_fn(|_| {
                std::array::from_fn(|_| Block128(u128::from_le_bytes(take(16).try_into().unwrap())))
            }),
            state: Block128(u128::from_le_bytes(take(16).try_into().unwrap())),
            claim_authority: Address(take(32).try_into().unwrap()),
            recovery_authority: Address(take(32).try_into().unwrap()),
            deadline: u64::from_le_bytes(take(8).try_into().unwrap()),
            claim_recipient: Address(take(32).try_into().unwrap()),
            recovery_recipient: Address(take(32).try_into().unwrap()),
            rules: ObjectRules {
                max_fee: u64::from_le_bytes(take(8).try_into().unwrap()),
                min_retained: u64::from_le_bytes(take(8).try_into().unwrap()),
                max_payout: u64::from_le_bytes(take(8).try_into().unwrap()),
                modes: take(1)[0],
            },
        };
        opening.validate()?;
        Ok(opening)
    }
}

pub fn transaction_contexts(body: &TxBody) -> [Block128; BODY_CONTEXT_FIELDS] {
    let leaves = body_hash_leaves(body);
    [
        leaves[TX8X2_LEAF_EPOCH_ANCHOR][0],
        leaves[TX8X2_LEAF_EPOCH_ANCHOR][1],
        leaves[TX8X2_LEAF_FEE][0],
        leaves[TX8X2_LEAF_OUTPUT0_DATA][1],
        leaves[TX8X2_LEAF_OUTPUT1_DATA][1],
        leaves[TX8X2_LEAF_OUTPUT1_OWNER][0],
        leaves[TX8X2_LEAF_OUTPUT1_OWNER][1],
        leaves[TX8X2_LEAF_FLAGS][0],
    ]
}

/// Explicit local envelope: one opening followed by one unchanged PagedSpend
/// and its existing authorization capsule. No second proof is introduced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectIntent {
    pub opening: ObjectOpening,
    pub spend: PagedSpendIntent,
}

impl ObjectIntent {
    pub fn to_bytes(&self) -> Result<Vec<u8>, ObjectError> {
        if self.spend.pages.len() != 1 {
            return Err(ObjectError::Shape);
        }
        let mut bytes =
            Vec::with_capacity(INTENT_PREFIX_BYTES + 330 + self.spend.authorization_bytes.len());
        bytes.extend_from_slice(INTENT_MAGIC);
        bytes.extend_from_slice(&self.opening.to_bytes()?);
        bytes.extend_from_slice(
            &self
                .spend
                .to_bytes()
                .map_err(|e| ObjectError::Page(e.to_string()))?,
        );
        Ok(bytes)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ObjectError> {
        if bytes.len() < INTENT_PREFIX_BYTES + 330
            || bytes.len() > MAX_INTENT_BYTES
            || !bytes.starts_with(INTENT_MAGIC)
        {
            return Err(ObjectError::Encoding);
        }
        // Reject extra pages before the general PagedSpend decoder allocates.
        let inner = &bytes[INTENT_PREFIX_BYTES..];
        if inner[1..3] != 1u16.to_le_bytes() {
            return Err(ObjectError::Shape);
        }
        let opening = ObjectOpening::from_bytes(&bytes[8..INTENT_PREFIX_BYTES])?;
        let spend =
            PagedSpendIntent::from_bytes(inner).map_err(|e| ObjectError::Page(e.to_string()))?;
        Ok(Self { opening, spend })
    }
}
