// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Slot conflict resolution for block assembly.
//!
//! When two transactions in the candidate set both attempt to mint the same
//! output slot, the tie-break rule is deterministic: the winner is the
//! transaction whose derived txid is lexicographically smallest.
//!
//! This is called BEFORE block assembly, NOT during validation.
//! `validate_block_consensus` verifies absence of conflicts; this function
//! produces a conflict-free set for the miner to work with.

use std::collections::HashMap;

use noid_poseidon2b::primitives::TxBodyHash;
use noid_tx::Transaction;

/// Resolve slot conflicts in a candidate transaction set.
///
/// Returns `(winners, loser_hashes)` where:
/// - `winners`: conflict-free subset ready for block inclusion
/// - `loser_hashes`: txids of dropped transactions; their
///   wallets must request new slot hints and rebuild.
///
/// Algorithm (SPEC §15.2):
///   For each output slot claimed by more than one transaction,
///   keep only `argmin(txid)` (lexicographic minimum).
///   Transactions that lose on any single slot are fully excluded.
///
/// Input: `txs` MUST already be conflict-free for INPUT slots
/// (no two txs spending the same input). Cross-input conflicts are
/// rejected during mempool admission; this function handles OUTPUT-slot
/// conflicts only.
///
/// Complexity: O(txs × max_outputs).
pub fn resolve_slot_conflicts(txs: Vec<Transaction>) -> (Vec<Transaction>, Vec<TxBodyHash>) {
    // Map: output_slot → best (min txid, tx_index)
    let mut best: HashMap<u32, (TxBodyHash, usize)> = HashMap::new();

    for (i, tx) in txs.iter().enumerate() {
        let txid = tx.txid();
        for (_, out) in tx.body.live_outputs() {
            let slot = out.slot_index;
            let entry = best.entry(slot).or_insert((txid, i));
            if txid.0 < entry.0 .0 {
                *entry = (txid, i);
            }
        }
    }

    // A transaction is a loser if it contests any slot but is NOT the argmin winner
    // of that slot. A single slot loss disqualifies the entire transaction.
    let mut loser_indices: std::collections::HashSet<usize> = std::collections::HashSet::new();
    for (i, tx) in txs.iter().enumerate() {
        for (_, out) in tx.body.live_outputs() {
            if let Some(&(_, winner_idx)) = best.get(&out.slot_index) {
                if winner_idx != i {
                    loser_indices.insert(i);
                    break; // one losing slot is enough to disqualify
                }
            }
        }
    }

    let mut winners = Vec::new();
    let mut losers = Vec::new();

    for (i, tx) in txs.into_iter().enumerate() {
        if loser_indices.contains(&i) {
            losers.push(tx.txid());
        } else {
            winners.push(tx);
        }
    }

    (winners, losers)
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::primitives::Address;
    use noid_tx::{
        output_bitmap_bit, Transaction, TxBody, TxInput, TxOutput, TX_INPUTS, TX_OUTPUTS,
    };

    fn tx(input_slot: u32, output_slot: u32, seed: u8) -> Transaction {
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
            owner: Address([seed; 32]),
        };
        Transaction::new(TxBody {
            epoch_anchor: [seed; 32],
            fee: 1,
            input_owner: Address([seed; 32]),
            inputs,
            outputs,
            validity_bitmap: 1 | output_bitmap_bit(0),
            is_coinbase: false,
        })
    }

    #[test]
    fn same_output_keeps_smallest_derived_txid() {
        let a = tx(1, 9, 1);
        let b = tx(2, 9, 2);
        let expected = if a.txid().0 < b.txid().0 {
            a.txid()
        } else {
            b.txid()
        };
        let (winners, losers) = resolve_slot_conflicts(vec![a, b]);
        assert_eq!(winners.len(), 1);
        assert_eq!(winners[0].txid(), expected);
        assert_eq!(losers.len(), 1);
    }

    #[test]
    fn distinct_outputs_all_survive() {
        let txs = vec![tx(1, 8, 1), tx(2, 9, 2)];
        let (winners, losers) = resolve_slot_conflicts(txs);
        assert_eq!(winners.len(), 2);
        assert!(losers.is_empty());
    }
}
