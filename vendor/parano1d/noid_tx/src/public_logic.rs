// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Shared native semantics for the sole Tx8x2 body.

use std::collections::HashSet;

use noid_poseidon2b::primitives::{Address, TxBodyHash};

use crate::{output_bitmap_bit, TxBody, TX_INPUTS, TX_OUTPUTS, TX_VALIDITY_MASK};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PublicLogicFacts {
    pub tx_body_hash: TxBodyHash,
    pub fee_u64: u64,
    pub n_live_inputs: u8,
    pub n_live_outputs: u8,
    pub input_sum: u128,
    pub output_sum: u128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PublicLogicError {
    Coinbase,
    BitmapHighBits {
        bitmap: u16,
    },
    DeadInputNotZero {
        index: usize,
    },
    DeadOutputNotZero {
        index: usize,
    },
    NoLiveInputs,
    CoinbaseInputOwner,
    CoinbaseBitmap {
        bitmap: u16,
    },
    DuplicateInputSlot {
        slot: u32,
    },
    DuplicateOutputSlot {
        slot: u32,
    },
    InputOutputSlotOverlap {
        slot: u32,
    },
    InputSumOverflow,
    OutputSumOverflow,
    OutputPlusFeeOverflow,
    BalanceMismatch {
        input_sum: u128,
        output_sum: u128,
        fee: u64,
    },
}

impl std::fmt::Display for PublicLogicError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for PublicLogicError {}

/// Canonical body checks shared by decode, mempool, sequential apply, delta
/// apply, proof-native validation, and template construction.
pub fn validate_body_semantics_no_hash(body: &TxBody) -> Result<(), PublicLogicError> {
    if body.validity_bitmap & !TX_VALIDITY_MASK != 0 {
        return Err(PublicLogicError::BitmapHighBits {
            bitmap: body.validity_bitmap,
        });
    }

    for (index, input) in body.inputs.iter().enumerate() {
        if !body.input_is_live(index) && *input != crate::TxInput::dummy() {
            return Err(PublicLogicError::DeadInputNotZero { index });
        }
    }
    for (index, output) in body.outputs.iter().enumerate() {
        if !body.output_is_live(index) && *output != crate::TxOutput::dummy() {
            return Err(PublicLogicError::DeadOutputNotZero { index });
        }
    }

    if body.is_coinbase {
        if body.input_owner != Address([0u8; 32]) {
            return Err(PublicLogicError::CoinbaseInputOwner);
        }
        let primary = output_bitmap_bit(0);
        let development = output_bitmap_bit(0) | output_bitmap_bit(1);
        if !matches!(body.validity_bitmap, bitmap if bitmap == primary || bitmap == development)
            || body.fee != 0
        {
            return Err(PublicLogicError::CoinbaseBitmap {
                bitmap: body.validity_bitmap,
            });
        }
        return unique_slots(body);
    }

    if body.live_input_count() == 0 {
        return Err(PublicLogicError::NoLiveInputs);
    }
    unique_slots(body)?;
    let (_, _, input_sum, output_sum) = sums(body)?;
    let expected = output_sum
        .checked_add(body.fee as u128)
        .ok_or(PublicLogicError::OutputPlusFeeOverflow)?;
    if input_sum != expected {
        return Err(PublicLogicError::BalanceMismatch {
            input_sum,
            output_sum,
            fee: body.fee,
        });
    }
    Ok(())
}

pub fn validate_public_tx_logic(body: &TxBody) -> Result<PublicLogicFacts, PublicLogicError> {
    if body.is_coinbase {
        return Err(PublicLogicError::Coinbase);
    }
    validate_body_semantics_no_hash(body)?;
    let (n_live_inputs, n_live_outputs, input_sum, output_sum) = sums(body)?;
    Ok(PublicLogicFacts {
        tx_body_hash: body.txid(),
        fee_u64: body.fee,
        n_live_inputs,
        n_live_outputs,
        input_sum,
        output_sum,
    })
}

fn unique_slots(body: &TxBody) -> Result<(), PublicLogicError> {
    let mut inputs = HashSet::with_capacity(TX_INPUTS);
    for (_, input) in body.live_inputs() {
        if !inputs.insert(input.slot_index) {
            return Err(PublicLogicError::DuplicateInputSlot {
                slot: input.slot_index,
            });
        }
    }

    let mut outputs = HashSet::with_capacity(TX_OUTPUTS);
    for (_, output) in body.live_outputs() {
        if !outputs.insert(output.slot_index) {
            return Err(PublicLogicError::DuplicateOutputSlot {
                slot: output.slot_index,
            });
        }
        if inputs.contains(&output.slot_index) {
            return Err(PublicLogicError::InputOutputSlotOverlap {
                slot: output.slot_index,
            });
        }
    }
    Ok(())
}

fn sums(body: &TxBody) -> Result<(u8, u8, u128, u128), PublicLogicError> {
    let mut input_sum = 0u128;
    for (_, input) in body.live_inputs() {
        input_sum = input_sum
            .checked_add(input.amount as u128)
            .ok_or(PublicLogicError::InputSumOverflow)?;
    }
    let mut output_sum = 0u128;
    for (_, output) in body.live_outputs() {
        output_sum = output_sum
            .checked_add(output.amount as u128)
            .ok_or(PublicLogicError::OutputSumOverflow)?;
    }
    Ok((
        body.live_input_count() as u8,
        body.live_output_count() as u8,
        input_sum,
        output_sum,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{TxInput, TxOutput};

    fn user_body() -> TxBody {
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        inputs[0] = TxInput {
            slot_index: 1,
            amount: 10,
            creation_id: 4,
        };
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: 2,
            amount: 9,
            owner: Address([8u8; 32]),
        };
        TxBody {
            epoch_anchor: [7u8; 32],
            fee: 1,
            input_owner: Address([6u8; 32]),
            inputs,
            outputs,
            validity_bitmap: 1 | output_bitmap_bit(0),
            is_coinbase: false,
        }
    }

    #[test]
    fn canonical_user_facts() {
        let facts = validate_public_tx_logic(&user_body()).unwrap();
        assert_eq!(facts.n_live_inputs, 1);
        assert_eq!(facts.n_live_outputs, 1);
        assert_eq!(
            (facts.input_sum, facts.output_sum, facts.fee_u64),
            (10, 9, 1)
        );
    }

    #[test]
    fn rejects_high_bits_and_dead_content() {
        let mut body = user_body();
        body.validity_bitmap |= 1 << 10;
        assert!(matches!(
            validate_body_semantics_no_hash(&body),
            Err(PublicLogicError::BitmapHighBits { .. })
        ));
        let mut body = user_body();
        body.inputs[7].amount = 1;
        assert_eq!(
            validate_body_semantics_no_hash(&body),
            Err(PublicLogicError::DeadInputNotZero { index: 7 })
        );
        let mut body = user_body();
        body.outputs[1].owner = Address([1u8; 32]);
        assert_eq!(
            validate_body_semantics_no_hash(&body),
            Err(PublicLogicError::DeadOutputNotZero { index: 1 })
        );
    }

    #[test]
    fn rejects_duplicate_and_overlapping_slots() {
        let mut body = user_body();
        body.inputs[1] = body.inputs[0];
        body.validity_bitmap |= 1 << 1;
        assert!(matches!(
            validate_body_semantics_no_hash(&body),
            Err(PublicLogicError::DuplicateInputSlot { slot: 1 })
        ));
        let mut body = user_body();
        body.outputs[0].slot_index = body.inputs[0].slot_index;
        assert!(matches!(
            validate_body_semantics_no_hash(&body),
            Err(PublicLogicError::InputOutputSlotOverlap { slot: 1 })
        ));
    }

    #[test]
    fn canonical_coinbase_is_exact() {
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: 5,
            amount: 50,
            owner: Address([9u8; 32]),
        };
        let body = TxBody {
            epoch_anchor: [3u8; 32],
            fee: 0,
            input_owner: Address([0u8; 32]),
            inputs: [TxInput::dummy(); TX_INPUTS],
            outputs,
            validity_bitmap: output_bitmap_bit(0),
            is_coinbase: true,
        };
        assert_eq!(validate_body_semantics_no_hash(&body), Ok(()));
        let mut bad = body;
        bad.validity_bitmap |= 1;
        assert!(matches!(
            validate_body_semantics_no_hash(&bad),
            Err(PublicLogicError::CoinbaseBitmap { .. })
        ));
    }

    #[test]
    fn canonical_development_payout_has_two_outputs() {
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: 5,
            amount: 50,
            owner: Address([8u8; 32]),
        };
        outputs[1] = TxOutput {
            slot_index: 6,
            amount: 50,
            owner: Address([9u8; 32]),
        };
        let body = TxBody {
            epoch_anchor: [3u8; 32],
            fee: 0,
            input_owner: Address([0u8; 32]),
            inputs: [TxInput::dummy(); TX_INPUTS],
            outputs,
            validity_bitmap: output_bitmap_bit(0) | output_bitmap_bit(1),
            is_coinbase: true,
        };
        assert!(body.is_development_payout_shape());
        assert_eq!(validate_body_semantics_no_hash(&body), Ok(()));
    }
}
