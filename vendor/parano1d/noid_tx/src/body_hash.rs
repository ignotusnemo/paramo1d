// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical flattened Tx8x2 body hash.

use noid_core::{Block128, TowerField};
use noid_poseidon2b::primitives::{hash_tx8x2_leaves, TxBodyHash, TX8X2_LEAF_COUNT};

use crate::{pack_amount_creation_id, TxBody, TX_INPUTS};

pub const BODY_HASH_LEAVES: usize = TX8X2_LEAF_COUNT;
pub const TX8X2_LEAF_EPOCH_ANCHOR: usize = 0;
pub const TX8X2_LEAF_FEE: usize = 1;
pub const TX8X2_LEAF_INPUT_OWNER: usize = 2;
pub const TX8X2_LEAF_INPUT_BASE: usize = 3;
pub const TX8X2_LEAF_OUTPUT0_DATA: usize = 11;
pub const TX8X2_LEAF_OUTPUT0_OWNER: usize = 12;
pub const TX8X2_LEAF_OUTPUT1_DATA: usize = 13;
pub const TX8X2_LEAF_OUTPUT1_OWNER: usize = 14;
pub const TX8X2_LEAF_FLAGS: usize = 15;

#[inline]
fn digest_fields(digest: &[u8; 32]) -> [Block128; 2] {
    [
        Block128::from(u128::from_le_bytes(digest[..16].try_into().unwrap())),
        Block128::from(u128::from_le_bytes(digest[16..].try_into().unwrap())),
    ]
}

/// Exact L0..L15 statement consumed by native hashing, GKR and recursion.
pub fn body_hash_leaves(body: &TxBody) -> [[Block128; 2]; TX8X2_LEAF_COUNT] {
    let mut leaves = [[Block128::ZERO; 2]; TX8X2_LEAF_COUNT];
    leaves[TX8X2_LEAF_EPOCH_ANCHOR] = digest_fields(&body.epoch_anchor);
    leaves[TX8X2_LEAF_FEE] = [Block128::from(body.fee as u128), Block128::ZERO];
    leaves[TX8X2_LEAF_INPUT_OWNER] = body.input_owner.as_fields();

    for (index, input) in body.inputs.iter().enumerate() {
        leaves[TX8X2_LEAF_INPUT_BASE + index] = [
            Block128::from(input.slot_index as u128),
            pack_amount_creation_id(input.amount, input.creation_id),
        ];
    }

    leaves[TX8X2_LEAF_OUTPUT0_DATA] = [
        Block128::from(body.outputs[0].slot_index as u128),
        Block128::from(body.outputs[0].amount as u128),
    ];
    leaves[TX8X2_LEAF_OUTPUT0_OWNER] = body.outputs[0].owner.as_fields();
    leaves[TX8X2_LEAF_OUTPUT1_DATA] = [
        Block128::from(body.outputs[1].slot_index as u128),
        Block128::from(body.outputs[1].amount as u128),
    ];
    leaves[TX8X2_LEAF_OUTPUT1_OWNER] = body.outputs[1].owner.as_fields();
    leaves[TX8X2_LEAF_FLAGS] = [
        Block128::from(body.validity_bitmap as u128),
        Block128::from(body.is_coinbase as u128),
    ];
    leaves
}

pub fn hash_tx_body(body: &TxBody) -> TxBodyHash {
    hash_tx8x2_leaves(&body_hash_leaves(body))
}

const _: () = assert!(TX8X2_LEAF_INPUT_BASE + TX_INPUTS == TX8X2_LEAF_OUTPUT0_DATA);
const _: () = assert!(TX8X2_LEAF_FLAGS + 1 == TX8X2_LEAF_COUNT);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{output_bitmap_bit, TxInput, TxOutput, TX_OUTPUTS};
    use noid_core::CanonicalSerialize;
    use noid_poseidon2b::native::{capacity_iv, compress, TAG_TX8X2};
    use noid_poseidon2b::primitives::Address;
    use noid_poseidon2b::Poseidon2bPermutation;

    fn fixture() -> TxBody {
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        for (index, input) in inputs.iter_mut().enumerate() {
            *input = TxInput {
                slot_index: 0x1000 + index as u32,
                amount: 0x2000 + index as u64,
                creation_id: 0x3000 + index as u64,
            };
        }
        let outputs = [
            TxOutput {
                slot_index: 0x4000,
                amount: 0x5000,
                owner: Address([0x61; 32]),
            },
            TxOutput {
                slot_index: 0x4001,
                amount: 0x5001,
                owner: Address([0x72; 32]),
            },
        ];
        TxBody {
            epoch_anchor: [0xA5; 32],
            fee: 0x1234,
            input_owner: Address([0x53; 32]),
            inputs,
            outputs,
            validity_bitmap: 0x00ff | output_bitmap_bit(0) | output_bitmap_bit(1),
            is_coinbase: true,
        }
    }

    fn fields(bytes: [u8; 32]) -> [Block128; 2] {
        digest_fields(&bytes)
    }

    #[test]
    fn sentinel_fixture_maps_every_raw_leaf_exactly() {
        let body = fixture();
        let leaves = body_hash_leaves(&body);
        assert_eq!(leaves[0], fields(body.epoch_anchor));
        assert_eq!(
            leaves[1],
            [Block128::from(body.fee as u128), Block128::ZERO]
        );
        assert_eq!(leaves[2], body.input_owner.as_fields());
        for index in 0..TX_INPUTS {
            assert_eq!(
                leaves[3 + index],
                [
                    Block128::from(body.inputs[index].slot_index as u128),
                    pack_amount_creation_id(
                        body.inputs[index].amount,
                        body.inputs[index].creation_id,
                    ),
                ]
            );
        }
        assert_eq!(
            leaves[11],
            [Block128::from(0x4000u128), Block128::from(0x5000u128)]
        );
        assert_eq!(leaves[12], body.outputs[0].owner.as_fields());
        assert_eq!(
            leaves[13],
            [Block128::from(0x4001u128), Block128::from(0x5001u128)]
        );
        assert_eq!(leaves[14], body.outputs[1].owner.as_fields());
        assert_eq!(
            leaves[15],
            [Block128::from(body.validity_bitmap as u128), Block128::ONE,]
        );
    }

    #[test]
    fn native_hash_matches_manual_tree_and_one_permutation_wrap() {
        let leaves = body_hash_leaves(&fixture());
        let mut level: Vec<[u8; 32]> = leaves
            .iter()
            .map(|leaf| {
                let mut bytes = [0u8; 32];
                bytes[..16].copy_from_slice(&leaf[0].to_bytes());
                bytes[16..].copy_from_slice(&leaf[1].to_bytes());
                bytes
            })
            .collect();
        while level.len() > 1 {
            level = level
                .chunks_exact(2)
                .map(|pair| compress(&pair[0], &pair[1]))
                .collect();
        }
        let root = fields(level[0]);
        let [iv_hi, iv_lo] = capacity_iv(TAG_TX8X2);
        let mut state = [root[0], root[1], iv_hi, iv_lo];
        Poseidon2bPermutation.permute_mut(&mut state);
        let mut expected = [0u8; 32];
        expected[..16].copy_from_slice(&state[0].to_bytes());
        expected[16..].copy_from_slice(&state[1].to_bytes());
        assert_eq!(fixture().txid().0, expected);
    }

    #[test]
    fn every_raw_leaf_lane_is_hash_binding() {
        let leaves = body_hash_leaves(&fixture());
        let baseline = hash_tx8x2_leaves(&leaves);
        for leaf in 0..TX8X2_LEAF_COUNT {
            for lane in 0..2 {
                let mut changed = leaves;
                changed[leaf][lane] += Block128::ONE;
                assert_ne!(
                    hash_tx8x2_leaves(&changed),
                    baseline,
                    "unbound raw leaf lane L{leaf}[{lane}]"
                );
            }
        }
    }

    #[test]
    fn every_validity_bitmap_bit_is_individually_hash_binding() {
        let body = fixture();
        let baseline = body.txid();
        for bit in 0..crate::TX_ACTIONS {
            let mut changed = body.clone();
            changed.validity_bitmap ^= 1u16 << bit;
            assert_ne!(changed.txid(), baseline, "unbound validity bit {bit}");
        }
    }

    #[test]
    fn output_count_constant_is_two() {
        assert_eq!(TX_OUTPUTS, 2);
    }
}
