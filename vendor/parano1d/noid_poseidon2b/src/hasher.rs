// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Cryptographic hasher trait for FRI Merkle trees.

use noid_core::Block128;

/// 32-byte hash output used throughout the Merkle tree and FRI layer.
pub type HashOutput = [u8; 32];

/// Trait for cryptographic hashing used in Merkle trees and transcripts.
///
/// Implementations are expected to be collision-resistant and deterministic.
///
/// The batch methods (`batch_hash_pair`, `batch_compress`) exist so SIMD /
/// multi-lane implementations can amortise their per-call overhead. Default
/// impls fall back to a sequential loop over the single-element methods.
pub trait CryptographicHasher: Send + Sync {
    /// Hash a pair of field elements (used for Merkle leaf construction).
    fn hash_pair(&self, a: &Block128, b: &Block128) -> HashOutput;

    /// Hash a single field element.
    fn hash_field(&self, elem: &Block128) -> HashOutput;

    /// Hash the concatenation of two 32-byte digests.
    fn hash_concatenation(&self, a: &HashOutput, b: &HashOutput) -> HashOutput;

    /// Fixed-width 2-to-1 compression of two digests — used for Merkle
    /// inner nodes. Default falls back to `hash_concatenation`. See
    /// CRYPTO.md §4.1.
    fn compress(&self, a: &HashOutput, b: &HashOutput) -> HashOutput {
        self.hash_concatenation(a, b)
    }

    /// Batched `hash_pair` over an interleaved `[a0, b0, a1, b1, ...]` slice.
    ///
    /// `pairs.len() == 2 * out.len()`. Default impl is a plain scalar loop;
    /// override to dispatch to SIMD / multi-lane kernels.
    fn batch_hash_pair(&self, pairs: &[Block128], out: &mut [HashOutput]) {
        assert_eq!(pairs.len(), 2 * out.len());
        for (i, slot) in out.iter_mut().enumerate() {
            *slot = self.hash_pair(&pairs[2 * i], &pairs[2 * i + 1]);
        }
    }

    /// Batched `compress` over an interleaved `[l0, r0, l1, r1, ...]` slice
    /// of 32-byte digests.
    ///
    /// `pairs.len() == 2 * out.len()`. Default impl is a plain scalar loop;
    /// override to dispatch to SIMD / multi-lane kernels.
    fn batch_compress(&self, pairs: &[HashOutput], out: &mut [HashOutput]) {
        assert_eq!(pairs.len(), 2 * out.len());
        for (i, slot) in out.iter_mut().enumerate() {
            *slot = self.compress(&pairs[2 * i], &pairs[2 * i + 1]);
        }
    }
}
