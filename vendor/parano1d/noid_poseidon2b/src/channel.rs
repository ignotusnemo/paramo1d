// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! Poseidon2b-backed Fiat-Shamir channel implementing
//! [`noid_core::transcript::FiatShamir`].
//!
//! This is the *production* transcript for protocols in `noid_core` that
//! previously used the insecure XOR-sum placeholder. Every squeeze advances
//! the sponge by one permutation and emits one Block128 challenge.
//!
//! The channel is seeded with its own capacity IV (`KSCHANNL`) so its
//! transcript states are not replayable across the other Fiat-Shamir
//! families (byte challenger, lane challenger, FRI channel). Any pinned
//! test vectors downstream (notably in `noid_fri` prover/verifier and
//! sumcheck transcripts) must be regenerated in the same commit that
//! changes the seed.

use noid_core::transcript::FiatShamir;
use noid_core::{Block128, Block256, TowerField};

use crate::native::compression::Poseidon2bSponge;
use crate::native::domain::{capacity_iv, TAG_KSCH256, TAG_KSCHANNL};

/// Fiat-Shamir channel backed by a Poseidon2b sponge.
#[derive(Clone)]
pub struct Poseidon2bChannel {
    sponge: Poseidon2bSponge,
    /// When we squeeze a rate block (two Block128s) we hand out the second
    /// one on the next call before advancing the sponge again.
    pending: Option<Block128>,
}

impl std::fmt::Debug for Poseidon2bChannel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Poseidon2bChannel([REDACTED])")
    }
}

impl Default for Poseidon2bChannel {
    fn default() -> Self {
        Self::new()
    }
}

impl Poseidon2bChannel {
    pub fn new() -> Self {
        Self {
            sponge: Poseidon2bSponge::with_iv(capacity_iv(TAG_KSCHANNL)),
            pending: None,
        }
    }

    /// Consume the transcript and return an exact four-lane bridge state.
    ///
    /// The construction-specific `close_tag` and a fixed zero lane form one
    /// complete final rate block, forcing exactly one final permutation. Any
    /// buffered second challenge is invalidated by the absorb. Returning all
    /// four lanes avoids introducing an unproved compression boundary between
    /// independently replayed transcript channels.
    pub fn close_into_bridge(mut self, close_tag: Block128) -> [Block128; 4] {
        assert!(
            self.sponge.absorb_is_aligned(),
            "bridge close must start at a fresh rate block"
        );
        self.absorb(close_tag);
        self.absorb(Block128::ZERO);
        self.sponge.full_state_after_aligned_absorb()
    }
}

impl FiatShamir<Block128> for Poseidon2bChannel {
    fn absorb(&mut self, elem: Block128) {
        // Absorbing invalidates any buffered challenge — future squeezes
        // must reflect the new state.
        self.pending = None;
        self.sponge.absorb(elem);
    }

    fn squeeze(&mut self) -> Block128 {
        if let Some(b) = self.pending.take() {
            return b;
        }
        // Commit any buffered absorb bytes to state before reading.
        self.sponge.flush_to_squeeze();
        let [a, b] = self.sponge.squeeze();
        self.pending = Some(b);
        a
    }
}

/// C1 Fiat-Shamir channel with GF(2^256) algebraic messages and challenges.
///
/// Poseidon2b itself remains the production GF(2^128), rate-two permutation.
/// One extension-field element therefore occupies exactly one rate block:
/// low coordinate first, high coordinate second. One squeeze consumes one
/// rate block and maps its two raw lanes through
/// [`Block256::from_raw_challenge_lanes`], yielding the selected 255-bit,
/// base-subfield-excluding challenge distribution without another
/// permutation or a retry loop.
#[derive(Clone)]
pub struct Poseidon2bWideChannel {
    sponge: Poseidon2bSponge,
    pending_base: Option<Block128>,
}

impl std::fmt::Debug for Poseidon2bWideChannel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Poseidon2bWideChannel([REDACTED])")
    }
}

impl Default for Poseidon2bWideChannel {
    fn default() -> Self {
        Self::new()
    }
}

impl Poseidon2bWideChannel {
    pub fn new() -> Self {
        Self {
            sponge: Poseidon2bSponge::with_iv(capacity_iv(TAG_KSCH256)),
            pending_base: None,
        }
    }

    #[inline]
    pub fn absorb_base(&mut self, elem: Block128) {
        self.pending_base = None;
        self.sponge.absorb(elem);
    }

    pub fn absorb_base_slice(&mut self, values: &[Block128]) {
        for &value in values {
            self.absorb_base(value);
        }
    }

    #[inline]
    pub fn absorb_wide(&mut self, value: Block256) {
        self.absorb_base(value.lo);
        self.absorb_base(value.hi);
    }

    #[inline]
    pub fn squeeze_wide(&mut self) -> Block256 {
        self.pending_base = None;
        self.sponge.flush_to_squeeze();
        let [lo, raw_hi] = self.sponge.squeeze();
        Block256::from_raw_challenge_lanes(lo, raw_hi)
    }

    /// Squeeze one raw GF(2^128) lane for non-algebraic transcript uses such
    /// as grinding and packed query seeds. Two consecutive calls share one
    /// rate-block permutation exactly like the legacy channel.
    pub fn squeeze_base(&mut self) -> Block128 {
        if let Some(value) = self.pending_base.take() {
            return value;
        }
        self.sponge.flush_to_squeeze();
        let [first, second] = self.sponge.squeeze();
        self.pending_base = Some(second);
        first
    }

    /// Consume the transcript and return the exact four-lane base-field
    /// bridge state used by the split Wallet transcript.
    pub fn close_into_bridge(mut self, close_tag: Block128) -> [Block128; 4] {
        assert!(
            self.sponge.absorb_is_aligned(),
            "wide bridge close must start at a fresh rate block"
        );
        self.absorb_base(close_tag);
        self.absorb_base(Block128::ZERO);
        self.sponge.full_state_after_aligned_absorb()
    }
}

impl FiatShamir<Block256> for Poseidon2bWideChannel {
    #[inline]
    fn absorb(&mut self, elem: Block256) {
        self.absorb_wide(elem);
    }

    #[inline]
    fn squeeze(&mut self) -> Block256 {
        self.squeeze_wide()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn channel_is_deterministic() {
        let mut c1 = Poseidon2bChannel::new();
        c1.absorb(Block128::from(42u128));
        let a1 = c1.squeeze();
        let b1 = c1.squeeze();

        let mut c2 = Poseidon2bChannel::new();
        c2.absorb(Block128::from(42u128));
        let a2 = c2.squeeze();
        let b2 = c2.squeeze();

        assert_eq!(a1, a2);
        assert_eq!(b1, b2);
    }

    #[test]
    fn distinct_inputs_distinct_challenges() {
        let mut c1 = Poseidon2bChannel::new();
        c1.absorb(Block128::from(1u128));
        let a = c1.squeeze();

        let mut c2 = Poseidon2bChannel::new();
        c2.absorb(Block128::from(2u128));
        let b = c2.squeeze();

        assert_ne!(a, b);
    }

    #[test]
    fn channel_iv_diverges_from_bare_sponge() {
        // Same absorb, different IV => different squeezes.
        let mut c = Poseidon2bChannel::new();
        c.absorb(Block128::from(1u128));
        let iv_challenge = c.squeeze();

        let mut bare = Poseidon2bSponge::new();
        bare.absorb(Block128::from(1u128));
        bare.flush_to_squeeze();
        let [bare_a, _] = bare.squeeze();

        assert_ne!(iv_challenge, bare_a);
    }

    #[test]
    fn channel_debug_never_formats_transcript_state() {
        let mut channel = Poseidon2bChannel::new();
        channel.absorb(Block128::from(0xA7A7_A7A7_A7A7_A7A7u128));
        assert_eq!(format!("{channel:?}"), "Poseidon2bChannel([REDACTED])");
    }

    #[test]
    fn consuming_bridge_closes_with_one_exact_full_block() {
        let close_tag = Block128::from(0x5A4B_BA1D_0000_0001u128);
        let mut channel = Poseidon2bChannel::new();
        channel.absorb(Block128::from(7u128));
        channel.absorb(Block128::from(9u128));
        let _eta = channel.squeeze();

        let bridge = channel.clone().close_into_bridge(close_tag);
        let same = channel.close_into_bridge(close_tag);
        assert_eq!(bridge, same);

        let mut changed = Poseidon2bChannel::new();
        changed.absorb(Block128::from(7u128));
        changed.absorb(Block128::from(10u128));
        let _eta = changed.squeeze();
        assert_ne!(bridge, changed.close_into_bridge(close_tag));
        assert!(bridge.iter().any(|&lane| lane != Block128::ZERO));
    }

    #[test]
    #[should_panic(expected = "bridge close must start at a fresh rate block")]
    fn consuming_bridge_rejects_a_half_filled_close_schedule() {
        let mut channel = Poseidon2bChannel::new();
        channel.absorb(Block128::from(7u128));
        let _ = channel.close_into_bridge(Block128::from(0x5A4B_BA1D_0000_0001u128));
    }

    #[test]
    fn wide_channel_is_deterministic_and_excludes_base_subfield() {
        let message = Block256::new(Block128::from(7u128), Block128::from(9u128));
        let mut a = Poseidon2bWideChannel::new();
        let mut b = Poseidon2bWideChannel::new();
        a.absorb(message);
        b.absorb(message);
        let a0 = a.squeeze();
        let b0 = b.squeeze();
        assert_eq!(a0, b0);
        assert!(!a0.is_in_base_subfield());
        assert_eq!(a.squeeze(), b.squeeze());
    }

    #[test]
    fn wide_channel_is_domain_separated_from_legacy_channel() {
        let value = Block128::from(42u128);
        let mut legacy = Poseidon2bChannel::new();
        legacy.absorb(value);
        legacy.absorb(Block128::ZERO);

        let mut wide = Poseidon2bWideChannel::new();
        wide.absorb(Block256::from(value));

        assert_ne!(legacy.squeeze(), wide.squeeze().lo);
    }

    #[test]
    fn wide_channel_bridge_closes_on_full_extension_blocks() {
        let mut channel = Poseidon2bWideChannel::new();
        channel.absorb(Block256::new(
            Block128::from(0x1234u128),
            Block128::from(0x5678u128),
        ));
        let _challenge = channel.squeeze();
        let bridge = channel.close_into_bridge(Block128::from(0xC1_0256u128));
        assert!(bridge.iter().any(|&lane| lane != Block128::ZERO));
    }
}
