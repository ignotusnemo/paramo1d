// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical transparent transaction types.
//!
//! Paranoid has one fixed transaction form: eight possible spends and two
//! possible outputs. Liveness is represented only by `TxBody::validity_bitmap`;
//! dead records are the all-zero record. Wallet secrets are not transaction
//! fields and enter proving only through `noid_gkr::OwnerAuthWitness`.

use noid_core::Block128;
use noid_poseidon2b::primitives::{Address, Commitment, Digest, TxBodyHash};

pub const TX_INPUTS: usize = 8;
pub const TX_OUTPUTS: usize = 2;
pub const TX_ACTIONS: usize = TX_INPUTS + TX_OUTPUTS;
pub const TX_VALIDITY_MASK: u16 = (1u16 << TX_ACTIONS) - 1;

/// Bitmap bit of logical output `index`.
#[inline]
pub const fn output_bitmap_bit(index: usize) -> u16 {
    1u16 << (TX_INPUTS + index)
}

/// Pack transparent amount and monotone UTXO incarnation into one field lane.
#[inline]
pub const fn pack_amount_creation_id(amount: u64, creation_id: u64) -> Block128 {
    Block128(((creation_id as u128) << 64) | amount as u128)
}

/// Inverse of [`pack_amount_creation_id`], returning `(amount, creation_id)`.
#[inline]
pub const fn unpack_amount_creation_id(packed: Block128) -> (u64, u64) {
    (packed.0 as u64, (packed.0 >> 64) as u64)
}

/// One possible spend. Ownership is stated once by `TxBody::input_owner`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TxInput {
    pub slot_index: u32,
    pub amount: u64,
    pub creation_id: u64,
}

impl TxInput {
    pub const fn dummy() -> Self {
        Self {
            slot_index: 0,
            amount: 0,
            creation_id: 0,
        }
    }

    pub fn commitment(&self, owner: &Address) -> Commitment {
        noid_poseidon2b::primitives::hash_utxo_leaf(
            pack_amount_creation_id(self.amount, self.creation_id).0,
            owner,
        )
    }
}

/// One possible freshly allocated transparent UTXO.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TxOutput {
    pub slot_index: u32,
    pub amount: u64,
    pub owner: Address,
}

impl TxOutput {
    pub const fn dummy() -> Self {
        Self {
            slot_index: 0,
            amount: 0,
            owner: Address([0u8; 32]),
        }
    }

    /// State-leaf commitment after the block allocator assigns this output's
    /// monotone creation id. Outputs never choose their own id.
    pub fn commitment_with_creation_id(&self, creation_id: u64) -> Commitment {
        noid_poseidon2b::primitives::hash_utxo_leaf(
            pack_amount_creation_id(self.amount, creation_id).0,
            &self.owner,
        )
    }
}

/// The sole canonical transaction body (`Tx8x2`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TxBody {
    pub epoch_anchor: Digest,
    pub fee: u64,
    /// One owner shared by every live input; zero when no input is live.
    pub input_owner: Address,
    pub inputs: [TxInput; TX_INPUTS],
    pub outputs: [TxOutput; TX_OUTPUTS],
    /// Bits 0..7 select inputs and bits 8..9 select outputs. All other bits
    /// are zero in a canonical body.
    pub validity_bitmap: u16,
    pub is_coinbase: bool,
}

/// Transaction anti-replay epoch length in blocks. The exact boundary update
/// rule is enforced by the chain accumulator and block validator.
pub const TX_EPOCH_BLOCKS: u64 = 144;

impl TxBody {
    /// The canonical primary block reward shape.
    ///
    /// `is_coinbase` is the fixed-wire system-mint discriminator retained by
    /// the launch protocol. Block context distinguishes the primary reward
    /// from the two-output development-allocation payout below.
    #[inline]
    pub const fn is_primary_coinbase_shape(&self) -> bool {
        self.is_coinbase && self.validity_bitmap == output_bitmap_bit(0)
    }

    /// The canonical two-output development-allocation payout shape.
    ///
    /// Height, owners, amounts, and placement are consensus-bound by the
    /// block validator and HistoryStep relation; this helper deliberately
    /// recognizes only the fixed public-body shape.
    #[inline]
    pub const fn is_development_payout_shape(&self) -> bool {
        self.is_coinbase && self.validity_bitmap == (output_bitmap_bit(0) | output_bitmap_bit(1))
    }

    #[inline]
    pub fn input_is_live(&self, index: usize) -> bool {
        index < TX_INPUTS && self.validity_bitmap & (1u16 << index) != 0
    }

    #[inline]
    pub fn output_is_live(&self, index: usize) -> bool {
        index < TX_OUTPUTS && self.validity_bitmap & output_bitmap_bit(index) != 0
    }

    #[inline]
    pub fn live_inputs(&self) -> impl Iterator<Item = (usize, &TxInput)> {
        self.inputs
            .iter()
            .enumerate()
            .filter(|(index, _)| self.input_is_live(*index))
    }

    #[inline]
    pub fn live_outputs(&self) -> impl Iterator<Item = (usize, &TxOutput)> {
        self.outputs
            .iter()
            .enumerate()
            .filter(|(index, _)| self.output_is_live(*index))
    }

    #[inline]
    pub fn live_input_count(&self) -> usize {
        (self.validity_bitmap & 0x00ff).count_ones() as usize
    }

    #[inline]
    pub fn live_output_count(&self) -> usize {
        ((self.validity_bitmap >> TX_INPUTS) & 0x0003).count_ones() as usize
    }

    #[inline]
    pub fn txid(&self) -> TxBodyHash {
        crate::body_hash::hash_tx_body(self)
    }

    #[inline]
    pub fn claims_commitment(&self) -> Digest {
        crate::claims::compute_claims_commitment(self)
    }

    #[inline]
    pub fn validate_canonical(&self) -> Result<(), crate::PublicLogicError> {
        crate::validate_body_semantics_no_hash(self)
    }
}

/// A block transaction is exactly one body. Its id is always derived and is
/// never a second wire field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transaction {
    pub body: TxBody,
}

impl Transaction {
    #[inline]
    pub const fn new(body: TxBody) -> Self {
        Self { body }
    }

    #[inline]
    pub fn txid(&self) -> TxBodyHash {
        self.body.txid()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn amount_creation_id_pack_roundtrip() {
        for (amount, creation_id) in [(0, 0), (1, 2), (u64::MAX, u64::MAX)] {
            assert_eq!(
                unpack_amount_creation_id(pack_amount_creation_id(amount, creation_id)),
                (amount, creation_id)
            );
        }
    }

    #[test]
    fn bitmap_accessors_use_final_positions() {
        let body = TxBody {
            epoch_anchor: [0u8; 32],
            fee: 0,
            input_owner: Address([7u8; 32]),
            inputs: [TxInput::dummy(); TX_INPUTS],
            outputs: [TxOutput::dummy(); TX_OUTPUTS],
            validity_bitmap: (1 << 0) | (1 << 4) | (1 << 7) | (1 << 8) | (1 << 9),
            is_coinbase: false,
        };
        assert_eq!(
            body.live_inputs().map(|(i, _)| i).collect::<Vec<_>>(),
            vec![0, 4, 7]
        );
        assert_eq!(
            body.live_outputs().map(|(i, _)| i).collect::<Vec<_>>(),
            vec![0, 1]
        );
        assert_eq!(body.live_input_count(), 3);
        assert_eq!(body.live_output_count(), 2);
        assert!(!body.input_is_live(TX_INPUTS));
        assert!(!body.output_is_live(TX_OUTPUTS));
    }

    #[test]
    fn output_creation_id_is_bound() {
        let output = TxOutput {
            slot_index: 7,
            amount: 11,
            owner: Address([9u8; 32]),
        };
        assert_ne!(
            output.commitment_with_creation_id(0),
            output.commitment_with_creation_id(1)
        );
    }
}
