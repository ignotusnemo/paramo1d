// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! Fiat-Shamir transcripts / challenge channels for non-interactive proofs.
//!
//! This module defines the *interface* used throughout `noid_core`
//! (sumcheck, MLE helpers, etc.) so proof systems can plug in any
//! cryptographically-binding hash without the core crate depending on the
//! hash implementation directly. The concrete Poseidon2b-backed channel
//! lives in `noid_poseidon2b`, avoiding a dependency cycle.

use crate::TowerField;

/// Abstract Fiat-Shamir channel: absorb field elements, squeeze challenges.
///
/// Any honest implementation must be cryptographically binding.
pub trait FiatShamir<F: TowerField> {
    /// Absorb a single field element.
    fn absorb(&mut self, elem: F);

    /// Absorb a slice of field elements.
    fn absorb_slice(&mut self, elems: &[F]) {
        for &e in elems {
            self.absorb(e);
        }
    }

    /// Squeeze a single challenge.
    fn squeeze(&mut self) -> F;

    /// Squeeze `n` challenges.
    fn squeeze_n(&mut self, n: usize) -> Vec<F> {
        (0..n).map(|_| self.squeeze()).collect()
    }
}
