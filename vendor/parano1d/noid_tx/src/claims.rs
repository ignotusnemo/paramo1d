// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Commitment to the canonical live state claims of one Tx8x2 body.

use noid_core::Block128;
use noid_poseidon2b::native::{
    compression::Poseidon2bSponge,
    domain::{capacity_iv, TAG_CLAIMS},
};
use noid_poseidon2b::primitives::Digest;

use crate::{pack_amount_creation_id, TxBody};

pub fn compute_claims_commitment(body: &TxBody) -> Digest {
    let mut sponge = Poseidon2bSponge::with_iv(capacity_iv(TAG_CLAIMS));
    sponge.absorb(Block128::from(body.validity_bitmap as u128));
    let [input_owner_hi, input_owner_lo] = body.input_owner.as_fields();
    sponge.absorb_pair(input_owner_hi, input_owner_lo);

    for (index, input) in body.live_inputs() {
        sponge.absorb_pair(
            Block128::from(index as u128),
            Block128::from(input.slot_index as u128),
        );
        sponge.absorb(pack_amount_creation_id(input.amount, input.creation_id));
    }

    for (index, output) in body.live_outputs() {
        sponge.absorb_pair(
            Block128::from((crate::TX_INPUTS + index) as u128),
            Block128::from(output.slot_index as u128),
        );
        sponge.absorb(Block128::from(output.amount as u128));
        let [owner_hi, owner_lo] = output.owner.as_fields();
        sponge.absorb_pair(owner_hi, owner_lo);
    }

    sponge.finalize()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{output_bitmap_bit, TxInput, TxOutput, TX_INPUTS, TX_OUTPUTS};
    use noid_poseidon2b::primitives::Address;

    fn body() -> TxBody {
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        inputs[1] = TxInput {
            slot_index: 12,
            amount: 90,
            creation_id: 4,
        };
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: 20,
            amount: 87,
            owner: Address([3u8; 32]),
        };
        TxBody {
            epoch_anchor: [1u8; 32],
            fee: 3,
            input_owner: Address([2u8; 32]),
            inputs,
            outputs,
            validity_bitmap: (1 << 1) | output_bitmap_bit(0),
            is_coinbase: false,
        }
    }

    #[test]
    fn deterministic_and_live_surface_sensitive() {
        let body = body();
        let expected = compute_claims_commitment(&body);
        assert_eq!(expected, compute_claims_commitment(&body));

        let mut changed = body.clone();
        changed.inputs[1].creation_id ^= 1;
        assert_ne!(expected, compute_claims_commitment(&changed));
        let mut changed = body.clone();
        changed.input_owner.0[0] ^= 1;
        assert_ne!(expected, compute_claims_commitment(&changed));
        let mut changed = body.clone();
        changed.outputs[0].owner.0[0] ^= 1;
        assert_ne!(expected, compute_claims_commitment(&changed));
        let mut changed = body;
        changed.validity_bitmap ^= 1;
        assert_ne!(expected, compute_claims_commitment(&changed));
    }

    #[test]
    fn dead_records_do_not_enter_claim_stream() {
        let body = body();
        let expected = compute_claims_commitment(&body);
        let mut noncanonical = body;
        noncanonical.inputs[7].amount = 99;
        assert_eq!(expected, compute_claims_commitment(&noncanonical));
        assert!(noncanonical.validate_canonical().is_err());
    }
}
