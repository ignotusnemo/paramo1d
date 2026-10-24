// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical transaction ordering for block assembly .
//!
//! This is **miner policy**, not consensus. The block validator only checks
//! that `tx_root == compute_tx_root(block.transactions)` — it does NOT
//! enforce this specific ordering. Two valid blocks from different miners
//! MAY have different orderings of the same transaction set.
//!
//! 1. Coinbase transaction first (if present).
//! 2. Remaining transactions: descending fee (largest fee first).
//! 3. Tie-break: ascending derived txid (lexicographic).
//!
//! This rule is deterministic, fee-incentive-compatible, and easy to replicate.

use noid_tx::Transaction;

/// Order transactions for block assembly using the canonical rule.
///
/// Coinbase is placed first. Non-coinbase txs are sorted by descending fee,
/// then ascending txid for equal-fee ties.
///
/// This is O(n log n). Call after `resolve_slot_conflicts`.
pub fn order_block_txs(mut txs: Vec<Transaction>) -> Vec<Transaction> {
    // Stable partition: coinbase first.
    txs.sort_by(|a, b| {
        let a_cb = a.body.is_coinbase;
        let b_cb = b.body.is_coinbase;
        match (a_cb, b_cb) {
            (true, false) => std::cmp::Ordering::Less,
            (false, true) => std::cmp::Ordering::Greater,
            _ => {
                // Both same type: sort by descending fee, then ascending hash.
                b.body
                    .fee
                    .cmp(&a.body.fee)
                    .then_with(|| a.txid().0.cmp(&b.txid().0))
            }
        }
    });
    txs
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::primitives::Address;
    use noid_tx::{
        output_bitmap_bit, Transaction, TxBody, TxInput, TxOutput, TX_INPUTS, TX_OUTPUTS,
    };

    fn tx(fee: u64, seed: u8, coinbase: bool) -> Transaction {
        if coinbase {
            let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
            outputs[0] = TxOutput {
                slot_index: seed as u32,
                amount: 50,
                owner: Address([seed; 32]),
            };
            return Transaction::new(TxBody {
                epoch_anchor: [seed; 32],
                fee: 0,
                input_owner: Address([0u8; 32]),
                inputs: [TxInput::dummy(); TX_INPUTS],
                outputs,
                validity_bitmap: output_bitmap_bit(0),
                is_coinbase: true,
            });
        }
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        inputs[0] = TxInput {
            slot_index: seed as u32,
            amount: fee + 1,
            creation_id: 1,
        };
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: 100 + seed as u32,
            amount: 1,
            owner: Address([seed; 32]),
        };
        Transaction::new(TxBody {
            epoch_anchor: [seed; 32],
            fee,
            input_owner: Address([seed; 32]),
            inputs,
            outputs,
            validity_bitmap: 1 | output_bitmap_bit(0),
            is_coinbase: false,
        })
    }

    #[test]
    fn coinbase_first_then_fee_desc_then_txid() {
        let cb = tx(0, 9, true);
        let low = tx(2, 1, false);
        let hi_a = tx(5, 2, false);
        let hi_b = tx(5, 3, false);
        let ordered = order_block_txs(vec![low.clone(), hi_b.clone(), cb.clone(), hi_a.clone()]);
        assert!(ordered[0].body.is_coinbase);
        assert_eq!(ordered[3].txid(), low.txid());
        assert!(ordered[1].txid().0 <= ordered[2].txid().0);
    }
}
