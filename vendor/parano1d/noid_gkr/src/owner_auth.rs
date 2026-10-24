// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical public owner-authorization statement.
//!
//! Wallet authorization is proved by the selected witness-hiding ZK capsule.
//! This module deliberately contains only the fixed public layout and the
//! body-to-statement derivation shared by wallet proving and consensus
//! verification.  The retired native AuthGKR proof, transcript, private trace,
//! and capsule-opening API are not part of the production crate.

use noid_core::Block128;
use noid_tx::{canonical_owner_auth, CanonicalOwnerAuth, OwnerAuthError, TxBody};

/// The selected address-permutation table contains 512 field cells.
pub const OWNER_AUTH_NUM_VARS: usize = 9;

/// The single protocol owner-auth geometry.
///
/// This zero-sized marker has no owner-count constructor or variable fields:
/// every transaction authorizes exactly one canonical input owner.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct OwnerAuthLayout;

impl OwnerAuthLayout {
    pub const FIXED: Self = Self;

    #[inline]
    pub const fn cells(self) -> usize {
        1usize << OWNER_AUTH_NUM_VARS
    }
}

/// Public inputs reconstructed independently from the canonical transaction
/// body at every production verification boundary.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct OwnerAuthPublicInputs {
    pub layout: OwnerAuthLayout,
    pub tx_body_hash: [Block128; 2],
    pub expected_address: [Block128; 2],
}

impl OwnerAuthPublicInputs {
    pub fn new(tx_body_hash: [Block128; 2], expected_address: [Block128; 2]) -> Self {
        Self {
            layout: OwnerAuthLayout::FIXED,
            tx_body_hash,
            expected_address,
        }
    }
}

#[derive(Debug)]
pub enum OwnerAuthStatementError {
    Canonical(OwnerAuthError),
    LiveInputCountOutOfRange { actual: usize, max: usize },
}

impl From<OwnerAuthError> for OwnerAuthStatementError {
    fn from(value: OwnerAuthError) -> Self {
        Self::Canonical(value)
    }
}

impl std::fmt::Display for OwnerAuthStatementError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Canonical(error) => write!(f, "canonical owner auth failed: {error}"),
            Self::LiveInputCountOutOfRange { actual, max } => {
                write!(
                    f,
                    "live input count out of range: actual {actual}, max {max}"
                )
            }
        }
    }
}

impl std::error::Error for OwnerAuthStatementError {}

pub fn owner_auth_public_from_statement(
    statement: &CanonicalOwnerAuth,
) -> Result<OwnerAuthPublicInputs, OwnerAuthStatementError> {
    Ok(OwnerAuthPublicInputs::new(
        statement.tx_body_hash.as_fields(),
        statement.input_owner.as_fields(),
    ))
}

pub fn owner_auth_public_from_body(
    body: &TxBody,
) -> Result<OwnerAuthPublicInputs, OwnerAuthStatementError> {
    let statement = canonical_owner_auth(body)?;
    owner_auth_public_from_statement(&statement)
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::primitives::{derive_address, Address, SpendSecret};
    use noid_tx::{output_bitmap_bit, TxInput, TxOutput, TX_INPUTS, TX_OUTPUTS};

    fn canonical_body() -> TxBody {
        let secret = SpendSecret::from_bytes([0x31; 32]);
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        inputs[0] = TxInput {
            slot_index: 7,
            amount: 9,
            creation_id: 0,
        };
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: 8,
            amount: 8,
            owner: Address([0x42; 32]),
        };
        TxBody {
            epoch_anchor: [0xA5; 32],
            fee: 1,
            input_owner: derive_address(&secret),
            inputs,
            outputs,
            validity_bitmap: 1 | output_bitmap_bit(0),
            is_coinbase: false,
        }
    }

    #[test]
    fn fixed_public_layout_is_the_selected_state_table() {
        assert_eq!(OwnerAuthLayout::FIXED.cells(), 512);
        assert_eq!(OWNER_AUTH_NUM_VARS, 9);
    }

    #[test]
    fn public_statement_is_reconstructed_from_the_canonical_body() {
        let body = canonical_body();
        let public = owner_auth_public_from_body(&body).expect("canonical public statement");
        assert_eq!(public.layout, OwnerAuthLayout::FIXED);
        assert_eq!(public.tx_body_hash, body.txid().as_fields());
        assert_eq!(public.expected_address, body.input_owner.as_fields());
    }
}
