// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical flattened Tx8x2 body-spine statement.

use noid_tx::{body_hash::body_hash_leaves, TxBody};

use crate::SpineInputs;

pub fn spine_inputs_from_body(body: &TxBody) -> SpineInputs {
    SpineInputs {
        leaves: body_hash_leaves(body),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{compute_tx_body_hash, SpineCircuit};
    use noid_poseidon2b::primitives::Address;
    use noid_tx::{output_bitmap_bit, TxInput, TxOutput, TX_INPUTS, TX_OUTPUTS};

    #[test]
    fn statement_is_the_exact_native_raw_leaf_array() {
        let owner = Address([0x33; 32]);
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        inputs[7] = TxInput {
            slot_index: 77,
            amount: 70,
            creation_id: 31,
        };
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[1] = TxOutput {
            slot_index: 91,
            amount: 63,
            owner: Address([0x44; 32]),
        };
        let body = TxBody {
            epoch_anchor: [0xA5; 32],
            fee: 7,
            input_owner: owner,
            inputs,
            outputs,
            validity_bitmap: (1 << 7) | output_bitmap_bit(1),
            is_coinbase: false,
        };
        let statement = spine_inputs_from_body(&body);
        assert_eq!(statement.leaves, body_hash_leaves(&body));
        assert_eq!(
            compute_tx_body_hash(&SpineCircuit::build(), &statement),
            body.txid().as_fields()
        );
    }
}
