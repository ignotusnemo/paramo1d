// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Deterministic transaction fee model.
//!
//! Fees are charged for:
//! - a base anti-DoS component per transaction;
//! - a small input component for anti-DoS/prover work;
//! - an output component for created UTXOs;
//! - a state-growth component for `max(0, outputs - inputs)` net-new UTXO slots.
//!
//! The state-growth component scales with current occupancy and is burned by
//! consensus: miners may claim only `fee - burned_state_growth_fee` in coinbase.

use noid_tx::TxBody;

#[cfg(test)]
use crate::consensus::params::LOG_SLOTS_GENESIS;
use crate::consensus::params::{
    FEE_PER_INPUT, FEE_PER_OUTPUT, MIN_FEE_BASE, STATE_GROWTH_FEE_BASE,
};

/// Occupancy pressure thresholds in basis points.
pub const PRESSURE_LOW_BPS: u64 = 5_000; // 50%
pub const PRESSURE_HIGH_BPS: u64 = 7_500; // 75%
pub const PRESSURE_EXTREME_BPS: u64 = 9_000; // 90%

/// Detailed deterministic fee calculation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FeeBreakdown {
    /// Fixed per-tx anti-DoS component.
    pub base: u64,
    /// Fee for live inputs.
    pub input: u64,
    /// Fee for live outputs.
    pub output: u64,
    /// Fee for live inputs + live outputs, kept as a convenient aggregate.
    pub io: u64,
    /// Fee for net-new live UTXO slots. Burned by consensus.
    pub state_growth: u64,
    /// Required minimum total fee.
    pub required_total: u64,
    /// Portion of `required_total` that is burned.
    pub burned: u64,
}

impl FeeBreakdown {
    /// Portion of a fee at exactly `required_total` that a miner may claim.
    #[inline]
    pub fn claimable_at_minimum(self) -> u64 {
        self.required_total.saturating_sub(self.burned)
    }
}

/// Count live inputs and outputs in a tx body.
#[inline]
pub fn tx_live_counts(body: &TxBody) -> (u64, u64) {
    let n_inputs = body.live_input_count() as u64;
    let n_outputs = body.live_output_count() as u64;
    (n_inputs, n_outputs)
}

/// Current occupancy in basis points using integer arithmetic.
#[inline]
pub fn occupancy_bps(active_slot_count: u64, log_slots: u32) -> u64 {
    let capacity = 1u128.checked_shl(log_slots).unwrap_or(u128::MAX).max(1);
    ((active_slot_count as u128).saturating_mul(10_000) / capacity) as u64
}

/// Deterministic pressure multiplier for the state-growth component.
///
/// This is intentionally stepwise instead of floating-point. The multiplier only
/// affects net-new state growth; state-shrinking transactions remain free of
/// this pressure fee.
#[inline]
pub fn pressure_multiplier(active_slot_count: u64, log_slots: u32) -> u64 {
    match occupancy_bps(active_slot_count, log_slots) {
        bps if bps >= PRESSURE_EXTREME_BPS => 8,
        bps if bps >= PRESSURE_HIGH_BPS => 4,
        bps if bps >= PRESSURE_LOW_BPS => 2,
        _ => 1,
    }
}

/// Fee per net-new slot under current occupancy pressure.
#[inline]
pub fn state_growth_fee_per_slot(active_slot_count: u64, log_slots: u32) -> u64 {
    STATE_GROWTH_FEE_BASE.saturating_mul(pressure_multiplier(active_slot_count, log_slots))
}

/// Compute the deterministic required fee for arbitrary live I/O counts.
///
/// The formula is intentionally output-centric: inputs pay a small anti-DoS
/// component, outputs pay the larger ordinary I/O component, and only net-new
/// state growth is burned. The sole fixed body pays for its actual live
/// inputs/outputs and is naturally cheap when it shrinks live state.
pub fn fee_breakdown(
    n_inputs: u64,
    n_outputs: u64,
    active_slot_count: u64,
    log_slots: u32,
) -> FeeBreakdown {
    let net_new_slots = n_outputs.saturating_sub(n_inputs);

    let base = MIN_FEE_BASE;
    let input = FEE_PER_INPUT.saturating_mul(n_inputs);
    let output = FEE_PER_OUTPUT.saturating_mul(n_outputs);
    let io = input.saturating_add(output);
    let state_growth =
        state_growth_fee_per_slot(active_slot_count, log_slots).saturating_mul(net_new_slots);
    let required_total = base.saturating_add(io).saturating_add(state_growth);

    FeeBreakdown {
        base,
        input,
        output,
        io,
        state_growth,
        required_total,
        burned: state_growth,
    }
}

/// Compute the deterministic required fee for a concrete transaction body.
#[inline]
pub fn fee_breakdown_for_tx_body(
    body: &TxBody,
    active_slot_count: u64,
    log_slots: u32,
) -> FeeBreakdown {
    let (n_inputs, n_outputs) = tx_live_counts(body);
    fee_breakdown(n_inputs, n_outputs, active_slot_count, log_slots)
}

/// Required minimum fee for a concrete transaction body.
#[inline]
pub fn required_fee_for_tx_body(body: &TxBody, active_slot_count: u64, log_slots: u32) -> u64 {
    fee_breakdown_for_tx_body(body, active_slot_count, log_slots).required_total
}

/// Burned fee for a concrete transaction body at the protocol-required level.
///
/// Additional tip above the required fee is claimable by miners; only the
/// deterministic state-growth component is burned.
#[inline]
pub fn burned_fee_for_tx_body(body: &TxBody, active_slot_count: u64, log_slots: u32) -> u64 {
    fee_breakdown_for_tx_body(body, active_slot_count, log_slots).burned
}

/// Fee amount claimable by miners for coinbase accounting.
#[inline]
pub fn claimable_fee_for_tx_body(body: &TxBody, active_slot_count: u64, log_slots: u32) -> u64 {
    if body.is_coinbase {
        return 0;
    }
    let actual = body.fee;
    let burned = burned_fee_for_tx_body(body, active_slot_count, log_slots);
    actual.saturating_sub(burned)
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::primitives::Address;
    use noid_tx::{output_bitmap_bit, TxBody, TxInput, TxOutput, TX_INPUTS, TX_OUTPUTS};

    fn body(n_inputs: usize, n_outputs: usize, fee: u64) -> TxBody {
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        for (i, input) in inputs.iter_mut().take(n_inputs).enumerate() {
            *input = TxInput {
                slot_index: i as u32,
                amount: 100,
                creation_id: 1,
            };
        }
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        for (i, output) in outputs.iter_mut().take(n_outputs).enumerate() {
            *output = TxOutput {
                slot_index: 100 + i as u32,
                amount: 1,
                owner: Address([2u8; 32]),
            };
        }
        let input_bits = if n_inputs == 0 {
            0
        } else {
            (1u16 << n_inputs) - 1
        };
        let output_bits = (0..n_outputs).fold(0, |bits, i| bits | output_bitmap_bit(i));
        TxBody {
            epoch_anchor: [1u8; 32],
            fee,
            input_owner: if n_inputs == 0 {
                Address([0u8; 32])
            } else {
                Address([1u8; 32])
            },
            inputs,
            outputs,
            validity_bitmap: input_bits | output_bits,
            is_coinbase: false,
        }
    }

    #[test]
    fn live_bitmap_drives_fee_counts() {
        assert_eq!(tx_live_counts(&body(8, 2, 0)), (8, 2));
        assert_eq!(tx_live_counts(&body(1, 1, 0)), (1, 1));
    }

    #[test]
    fn state_shrinking_transaction_has_no_state_growth_burn() {
        let f = fee_breakdown(8, 1, 0, LOG_SLOTS_GENESIS);
        assert_eq!(f.state_growth, 0);
        assert_eq!(f.burned, 0);
    }

    #[test]
    fn pressure_only_multiplies_net_growth() {
        let low = fee_breakdown(1, 2, 0, LOG_SLOTS_GENESIS);
        let capacity = 1u64 << LOG_SLOTS_GENESIS;
        let high = fee_breakdown(1, 2, capacity * 9 / 10, LOG_SLOTS_GENESIS);
        assert!(high.state_growth > low.state_growth);
        assert_eq!(high.base, low.base);
        assert_eq!(high.io, low.io);
    }

    #[test]
    fn all_pressure_thresholds_and_capacity_expansion_use_exact_integer_boundaries() {
        let log_slots = LOG_SLOTS_GENESIS;
        let capacity = 1u64 << log_slots;
        for (bps, before, at) in [(5_000, 1, 2), (7_500, 2, 4), (9_000, 4, 8)] {
            let threshold = (capacity * bps).div_ceil(10_000);
            assert_eq!(pressure_multiplier(threshold - 1, log_slots), before);
            assert_eq!(pressure_multiplier(threshold, log_slots), at);
            assert_eq!(
                fee_breakdown(1, 2, threshold, log_slots).required_total,
                6_500 + 2_500 * at
            );
            assert_eq!(
                fee_breakdown(2, 2, threshold, log_slots).required_total,
                6_600
            );
            assert_eq!(
                fee_breakdown(8, 1, threshold, log_slots).required_total,
                6_500
            );
            assert_eq!(pressure_multiplier(threshold, log_slots + 1), 1);
        }
    }

    #[test]
    fn claimable_subtracts_deterministic_burn() {
        let mut body = body(1, 2, 1_000_000);
        body.fee = required_fee_for_tx_body(&body, 0, LOG_SLOTS_GENESIS);
        let breakdown = fee_breakdown_for_tx_body(&body, 0, LOG_SLOTS_GENESIS);
        assert_eq!(
            claimable_fee_for_tx_body(&body, 0, LOG_SLOTS_GENESIS),
            breakdown.required_total - breakdown.burned
        );
    }
}
