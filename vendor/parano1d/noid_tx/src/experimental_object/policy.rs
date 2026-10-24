// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Committed spending rules shared by native admission and the block relation.

use noid_core::Block128;

use super::ObjectError;

pub const CLAIM_CONTINUE: u8 = 1;
pub const CLAIM_CLOSE: u8 = 2;
pub const RECOVERY_CONTINUE: u8 = 4;
pub const RECOVERY_CLOSE: u8 = 8;
/// A continuing payment may choose its own recipient. Without this bit the
/// deadline-selected recipient is mandatory for both output forms.
pub const ANY_PAYOUT_RECIPIENT: u8 = 16;
pub const VALID_MODES: u8 = 31;
pub const RULE_BYTES: usize = 8 + 8 + 8 + 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ObjectRules {
    /// Maximum fee of every call, including a terminal call.
    pub max_fee: u64,
    /// Minimum amount retained in every continuing successor.
    pub min_retained: u64,
    /// Maximum second-output payment per continuing call, excluding its fee.
    /// This is not a rate limit: successive authorized calls may each pay it.
    pub max_payout: u64,
    /// Independently permit continuing/closing before/after the deadline.
    pub modes: u8,
}

impl ObjectRules {
    pub fn validate(self) -> Result<(), ObjectError> {
        if self.modes & !VALID_MODES != 0 {
            return Err(ObjectError::Policy);
        }
        Ok(())
    }

    pub fn fields(self) -> [Block128; 4] {
        [
            Block128(self.max_fee as u128),
            Block128(self.min_retained as u128),
            Block128(self.max_payout as u128),
            Block128(self.modes as u128),
        ]
    }

    pub fn permits(self, before_deadline: bool, terminal: bool) -> bool {
        let bit = match (before_deadline, terminal) {
            (true, false) => CLAIM_CONTINUE,
            (true, true) => CLAIM_CLOSE,
            (false, false) => RECOVERY_CONTINUE,
            (false, true) => RECOVERY_CLOSE,
        };
        self.modes & bit != 0
    }
}
