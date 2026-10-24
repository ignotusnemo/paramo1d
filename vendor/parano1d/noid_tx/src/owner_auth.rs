// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical one-owner authorization statement derived from Tx8x2.

use noid_poseidon2b::primitives::{Address, TxBodyHash};

use crate::{validate_public_tx_logic, PublicLogicError, TxBody};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OwnerAuthError {
    PublicLogic(PublicLogicError),
}

impl From<PublicLogicError> for OwnerAuthError {
    fn from(value: PublicLogicError) -> Self {
        Self::PublicLogic(value)
    }
}

impl std::fmt::Display for OwnerAuthError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for OwnerAuthError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CanonicalOwnerAuth {
    pub tx_body_hash: TxBodyHash,
    pub input_owner: Address,
}

pub fn canonical_owner_auth(body: &TxBody) -> Result<CanonicalOwnerAuth, OwnerAuthError> {
    let facts = validate_public_tx_logic(body)?;
    Ok(CanonicalOwnerAuth {
        tx_body_hash: facts.tx_body_hash,
        input_owner: body.input_owner,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{output_bitmap_bit, TxInput, TxOutput, TX_INPUTS, TX_OUTPUTS};

    #[test]
    fn statement_has_exactly_one_owner_and_derived_txid() {
        let owner = Address([4u8; 32]);
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        inputs[0] = TxInput {
            slot_index: 1,
            amount: 10,
            creation_id: 2,
        };
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: 2,
            amount: 9,
            owner,
        };
        let body = TxBody {
            epoch_anchor: [3u8; 32],
            fee: 1,
            input_owner: owner,
            inputs,
            outputs,
            validity_bitmap: 1 | output_bitmap_bit(0),
            is_coinbase: false,
        };
        let statement = canonical_owner_auth(&body).unwrap();
        assert_eq!(statement.input_owner, owner);
        assert_eq!(statement.tx_body_hash, body.txid());
    }
}
