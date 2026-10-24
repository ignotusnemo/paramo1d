// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Per-transaction consensus checks.
//!
//! These checks are cheap (O(1) per tx) and run before wallet authorization verification.
//! Ordering: cheapest first to fail fast.
//!
//! Checks covered here:
//!   1. canonical fixed body semantics
//!   2. structurally non-zero user anchor (exact equality is checked by the
//!      chain context against the current transaction epoch)
//!
//! Cross-tx slot conflicts (checks 4-5 in SPEC §6) are handled by
//! `validate_block_slot_conflicts()` in `validation.rs` since they require
//! looking at the full transaction set.

use crate::consensus::ConsensusError;
use noid_tx::Transaction;

/// Validate the per-tx consensus rules for a transaction.
///
/// Checks (ordered cheapest first):
/// The transaction id is derived from the body and therefore has no second
/// cached field whose binding could diverge.
pub fn validate_tx_consensus(tx: &Transaction) -> Result<(), ConsensusError> {
    // The shared predicate owns bitmap/dead-zero canonicality, one explicit
    // input owner, balance, range, and exact coinbase shape.
    noid_tx::validate_body_semantics_no_hash(&tx.body)
        .map_err(|e| ConsensusError::ShapeMismatch(format!("body semantics: {e}")))?;

    // 2. epoch_anchor: non-zero for non-coinbase (structural check).
    //    Exact equality with the current transaction-epoch id is owned by
    //    mempool admission and the chain context's direct block boundary.
    if !tx.body.is_coinbase && tx.body.epoch_anchor == [0u8; 32] {
        return Err(ConsensusError::BadEpochAnchor);
    }

    Ok(())
}

/// Check that every live action in a block touches a distinct physical slot.
///
/// Input/input, output/output, and input/output reuse all fail, including a
/// spend followed by a mint in a later transaction of the same block.
/// This is O(n × inputs) per block, bounded by the decoder transaction cap and
/// the consensus semantic live-input budget.
pub fn validate_block_slot_conflicts(txs: &[Transaction]) -> Result<(), ConsensusError> {
    use std::collections::HashSet;
    let mut touched: HashSet<u32> = HashSet::new();

    for tx in txs {
        for (_, inp) in tx.body.live_inputs() {
            if !touched.insert(inp.slot_index) {
                return Err(ConsensusError::SlotConflict);
            }
        }
        for (_, out) in tx.body.live_outputs() {
            if !touched.insert(out.slot_index) {
                return Err(ConsensusError::SlotConflict);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::primitives::Address;
    use noid_tx::{
        output_bitmap_bit, Transaction, TxBody, TxInput, TxOutput, TX_INPUTS, TX_OUTPUTS,
    };

    fn user_tx(input_slot: u32, output_slot: u32, anchor: [u8; 32]) -> Transaction {
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        inputs[0] = TxInput {
            slot_index: input_slot,
            amount: 10,
            creation_id: 1,
        };
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: output_slot,
            amount: 9,
            owner: Address([2u8; 32]),
        };
        Transaction::new(TxBody {
            epoch_anchor: anchor,
            fee: 1,
            input_owner: Address([1u8; 32]),
            inputs,
            outputs,
            validity_bitmap: 1 | output_bitmap_bit(0),
            is_coinbase: false,
        })
    }

    #[test]
    fn fixed_body_and_structural_anchor_validate() {
        let tx = user_tx(1, 2, [3u8; 32]);
        assert_eq!(validate_tx_consensus(&tx), Ok(()));

        let mut zero_anchor = tx.clone();
        zero_anchor.body.epoch_anchor = [0u8; 32];
        assert_eq!(
            validate_tx_consensus(&zero_anchor),
            Err(ConsensusError::BadEpochAnchor)
        );
    }

    #[test]
    fn block_touched_set_rejects_every_reuse_direction() {
        let a = user_tx(1, 2, [3u8; 32]);

        let duplicate_input = user_tx(1, 3, [3u8; 32]);
        assert_eq!(
            validate_block_slot_conflicts(&[a.clone(), duplicate_input]),
            Err(ConsensusError::SlotConflict)
        );

        let duplicate_output = user_tx(4, 2, [3u8; 32]);
        assert_eq!(
            validate_block_slot_conflicts(&[a.clone(), duplicate_output]),
            Err(ConsensusError::SlotConflict)
        );

        let spend_then_mint = user_tx(4, 1, [3u8; 32]);
        assert_eq!(
            validate_block_slot_conflicts(&[a.clone(), spend_then_mint]),
            Err(ConsensusError::SlotConflict)
        );

        let mint_then_spend = user_tx(2, 5, [3u8; 32]);
        assert_eq!(
            validate_block_slot_conflicts(&[a, mint_then_spend]),
            Err(ConsensusError::SlotConflict)
        );
    }

    #[test]
    fn reward_cannot_be_spent_inside_its_own_block() {
        use crate::consensus::params::coinbase_creation_id;

        let height = 7;
        let reward_slot = 9;
        let mut reward_outputs = [TxOutput::dummy(); TX_OUTPUTS];
        reward_outputs[0] = TxOutput {
            slot_index: reward_slot,
            amount: 10,
            owner: Address([1u8; 32]),
        };
        let reward = Transaction::new(TxBody {
            epoch_anchor: [2u8; 32],
            fee: 0,
            input_owner: Address([0u8; 32]),
            inputs: [TxInput::dummy(); TX_INPUTS],
            outputs: reward_outputs,
            validity_bitmap: output_bitmap_bit(0),
            is_coinbase: true,
        });
        let mut spend = user_tx(reward_slot, 10, [3u8; 32]);
        spend.body.inputs[0].creation_id = coinbase_creation_id(height);
        let spend = Transaction::new(spend.body);

        assert_eq!(
            validate_block_slot_conflicts(&[reward, spend]),
            Err(ConsensusError::SlotConflict)
        );
    }

    #[test]
    fn disjoint_actions_pass() {
        assert_eq!(
            validate_block_slot_conflicts(&[user_tx(1, 2, [3u8; 32]), user_tx(3, 4, [3u8; 32]),]),
            Ok(())
        );
    }
}
