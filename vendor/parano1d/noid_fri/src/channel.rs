// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Fiat–Shamir transcript for the FRI protocol.
//!
//! Keccak256 is replaced by a Poseidon2b sponge in *duplex* mode: absorbs go
//! through the sponge as byte-streaming; squeezes use the sponge's native
//! two-Block128-per-permutation rate output. One permutation yields two
//! challenges, amortising the hash cost over challenge-heavy phases
//! (folding rounds, query index generation).

use noid_core::{Block128, CanonicalSerialize};
use noid_poseidon2b::native::compression::Poseidon2bSponge;
use noid_poseidon2b::native::domain::{capacity_iv, TAG_FRICHANL};

use crate::merkle::VectorCommitment;
use crate::prover::FriCommitment;

/// Number of FRI queries. With inverse rate 4, each query contributes
/// `log2(4) = 2` bits **under the Reed-Solomon capacity conjecture**
/// (conjectured, not proven): 64 queries = 128-bit conjectured soundness.
/// The PROVABLE bounds for this phase are materially lower — roughly
/// 64 bits under the Johnson/list-decoding regime (proximity gaps) and
/// roughly 43 bits under unique decoding — so any security statement for
/// this proof system must name which regime it is quoting. 64 queries
/// keeps proof size and verifier work 33% below the former 96.
///
/// In debug builds (cargo test, cargo run without --release) we use a
/// smaller count so the test suite runs quickly — the protocol is still
/// exercised fully end-to-end. Benchmarks (release profile) use the
/// production value.
#[cfg(not(debug_assertions))]
pub const NUM_QUERIES: usize = 64;
#[cfg(debug_assertions)]
pub const NUM_QUERIES: usize = 10;

/// Base-2 log of the extension degree used for soundness amplification.
pub const TAU: usize = 7;

/// Fiat–Shamir channel backed by a Poseidon2b sponge (duplex mode).
///
/// `Clone` supports prover-side transcript grinding: probe nonces against a
/// snapshot of the channel state without mutating the live transcript.
#[derive(Clone)]
pub struct Channel {
    sponge: Poseidon2bSponge,
    /// One rate block (two Block128s) of buffered squeeze output.
    /// `None` if the next squeeze needs to trigger a permutation.
    pending: Option<Block128>,
    /// `true` once we've started squeezing; absorbs after this reset
    /// the pending block and re-enter absorb mode.
    squeezing: bool,
}

impl Channel {
    pub fn new() -> Self {
        Self {
            // Seeded with the FRI-transcript capacity IV: a zero-IV duplex
            // would share states with any other bare-sponge construction on
            // identical absorbs; the tag makes this transcript family
            // non-replayable across the other Fiat-Shamir channels.
            sponge: Poseidon2bSponge::with_iv(capacity_iv(TAG_FRICHANL)),
            pending: None,
            squeezing: false,
        }
    }

    // -----------------------------------------------------------------------
    // Observe (absorb)
    // -----------------------------------------------------------------------

    fn enter_absorb_mode(&mut self) {
        if self.squeezing {
            // Any pending rate output is invalidated — future squeezes
            // must reflect the new state.
            self.pending = None;
            self.squeezing = false;
        }
    }

    /// Absorb a single field element.
    pub fn observe_field_elem(&mut self, elem: Block128) {
        self.enter_absorb_mode();
        let mut bytes = [0u8; 16];
        elem.serialize(&mut bytes)
            .expect("Block128 serializes into 16 bytes");
        self.sponge.update(&bytes);
    }

    /// Absorb a slice of field elements.
    pub fn observe_field_elems(&mut self, elems: &[Block128]) {
        self.enter_absorb_mode();
        for &elem in elems {
            let mut bytes = [0u8; 16];
            elem.serialize(&mut bytes)
                .expect("Block128 serializes into 16 bytes");
            self.sponge.update(&bytes);
        }
    }

    /// Absorb a `VectorCommitment` (root hash + depth).
    ///
    /// The depth is absorbed as one whole 16-byte lane (u128 LE) so every
    /// absorb in the protocol stays rate-lane aligned — the in-circuit
    /// replay of this channel (the recursive acceptance proof re-verifies
    /// FRI openings in-circuit) is a lane duplex, and a misaligned integer
    /// absorb would force bit-split range checks on every subsequent witness
    /// value.
    pub fn observe_vector_commitment(&mut self, commitment: &VectorCommitment) {
        self.enter_absorb_mode();
        self.sponge.update(&commitment.root);
        self.sponge
            .update(&(commitment.depth as u128).to_le_bytes());
    }

    /// Absorb a `FriCommitment` (vector commitment + packing factor).
    ///
    /// Same lane-alignment rule as [`Self::observe_vector_commitment`].
    pub fn observe_fri_commitment(&mut self, commitment: &FriCommitment) {
        self.observe_vector_commitment(&commitment.vector_commitment);
        self.sponge
            .update(&(commitment.packing_factor as u128).to_le_bytes());
    }

    // -----------------------------------------------------------------------
    // Squeeze (challenge derivation)
    // -----------------------------------------------------------------------

    fn squeeze_block(&mut self) -> Block128 {
        if !self.squeezing {
            self.sponge.flush_to_squeeze();
            self.squeezing = true;
        }
        if let Some(b) = self.pending.take() {
            return b;
        }
        let [a, b] = self.sponge.squeeze();
        self.pending = Some(b);
        a
    }

    /// Squeeze a single random `Block128` challenge.
    pub fn get_random_point(&mut self) -> Block128 {
        self.squeeze_block()
    }

    /// Prover-side grind probe: the challenge that `observe_field_elem(elem)`
    /// followed by `get_random_point()` would produce, computed on a copy of
    /// the transcript in a single permutation (the squeeze's advance
    /// permutation is skipped — the probe state is discarded). The live
    /// transcript is untouched, so a grind loop can test candidate nonces in
    /// parallel and absorb only the accepted one.
    pub fn probe_squeeze(&self, elem: Block128) -> Block128 {
        let mut probe = self.clone();
        probe.observe_field_elem(elem);
        probe.sponge.flush_to_squeeze();
        probe.sponge.peek_rate()[0]
    }

    /// Squeeze `n` random challenges.
    pub fn get_random_points(&mut self, n: usize) -> Vec<Block128> {
        (0..n).map(|_| self.squeeze_block()).collect()
    }

    /// Generate query indices for the query phase.
    ///
    /// Draws `NUM_QUERIES` random field elements and reduces each modulo
    /// the domain size. If the domain is smaller than NUM_QUERIES we
    /// query every index once.
    pub fn gen_queries(&mut self, log_max_len: usize) -> Vec<usize> {
        let Some(domain_size) = 1usize.checked_shl(log_max_len as u32) else {
            // Out-of-range log size (malformed input): return no queries so
            // higher-level verifiers can fail shape checks cleanly.
            return vec![];
        };

        if domain_size == 0 {
            return vec![];
        }

        if domain_size < NUM_QUERIES {
            return (0..domain_size).collect();
        }

        let bit_mask = (domain_size - 1) as u128;
        let random_elems = self.get_random_points(NUM_QUERIES);
        random_elems
            .iter()
            .map(|elem| (elem.0 & bit_mask) as usize)
            .collect()
    }
}

impl Default for Channel {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_channel_deterministic() {
        let mut c1 = Channel::new();
        c1.observe_field_elem(Block128::from(42u8));
        let p1 = c1.get_random_point();

        let mut c2 = Channel::new();
        c2.observe_field_elem(Block128::from(42u8));
        let p2 = c2.get_random_point();

        assert_eq!(p1, p2);
    }

    #[test]
    fn test_channel_different_obs() {
        let mut c1 = Channel::new();
        c1.observe_field_elem(Block128::from(1u8));
        let p1 = c1.get_random_point();

        let mut c2 = Channel::new();
        c2.observe_field_elem(Block128::from(2u8));
        let p2 = c2.get_random_point();

        assert_ne!(p1, p2);
    }

    #[test]
    fn test_gen_queries() {
        let mut c = Channel::new();
        c.observe_field_elem(Block128::from(99u8));
        let queries = c.gen_queries(10); // domain 1024
        assert_eq!(queries.len(), NUM_QUERIES);
        for &q in &queries {
            assert!(q < 1024);
        }
    }

    #[test]
    fn test_interleaved_absorb_squeeze() {
        let mut c1 = Channel::new();
        c1.observe_field_elem(Block128::from(1u8));
        let a1 = c1.get_random_point();
        c1.observe_field_elem(Block128::from(2u8));
        let b1 = c1.get_random_point();

        let mut c2 = Channel::new();
        c2.observe_field_elem(Block128::from(1u8));
        let a2 = c2.get_random_point();
        c2.observe_field_elem(Block128::from(2u8));
        let b2 = c2.get_random_point();

        assert_eq!(a1, a2);
        assert_eq!(b1, b2);
        assert_ne!(a1, b1);
    }

    #[test]
    fn test_probe_squeeze_matches_live_squeeze() {
        // Fresh, half-block-buffered, block-aligned, and mid-squeeze
        // channel states: the probe must equal the live observe+squeeze
        // in every absorb/squeeze phase.
        let mut states: Vec<Channel> = vec![Channel::new()];
        let mut c = Channel::new();
        c.observe_field_elem(Block128::from(7u8)); // 16 bytes buffered
        states.push(c.clone());
        c.observe_field_elem(Block128::from(9u8)); // 32 bytes: rate-aligned
        states.push(c.clone());
        let _ = c.get_random_point(); // squeezing, pending block held
        states.push(c);

        for (i, ch) in states.into_iter().enumerate() {
            let elem = Block128::from(0xA5u128 + i as u128);
            let probed = ch.probe_squeeze(elem);
            let mut live = ch;
            live.observe_field_elem(elem);
            assert_eq!(probed, live.get_random_point(), "channel state {i}");
        }
    }

    #[test]
    fn test_squeeze_commits_to_later_absorb() {
        let mut c = Channel::new();
        c.observe_field_elem(Block128::from(1u8));
        let a = c.get_random_point();
        let b_no_obs = c.get_random_point();

        let mut c2 = Channel::new();
        c2.observe_field_elem(Block128::from(1u8));
        let a2 = c2.get_random_point();
        c2.observe_field_elem(Block128::from(99u8));
        let b_with_obs = c2.get_random_point();

        assert_eq!(a, a2);
        assert_ne!(b_no_obs, b_with_obs);
    }
}
