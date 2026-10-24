// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Poseidon2b digest API.

use super::compression::Poseidon2bSponge;
use noid_core::Block128;

/// One-shot hash of a slice of bytes to a 32-byte digest.
pub fn poseidon2b_digest(data: &[u8]) -> [u8; 32] {
    let mut sponge = Poseidon2bSponge::new();
    sponge.update(data);
    sponge.finalize()
}

/// One-shot hash of a single field element to a 32-byte digest.
pub fn poseidon2b_digest_field(elem: Block128) -> [u8; 32] {
    let mut sponge = Poseidon2bSponge::new();
    sponge.absorb(elem);
    sponge.finalize()
}

/// One-shot hash of two field elements to a 32-byte digest.
pub fn poseidon2b_digest_pair(a: Block128, b: Block128) -> [u8; 32] {
    let mut sponge = Poseidon2bSponge::new();
    sponge.absorb_pair(a, b);
    sponge.finalize()
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_core::TowerField;

    #[test]
    fn test_digest_bytes() {
        let d1 = poseidon2b_digest(b"test");
        let d2 = poseidon2b_digest(b"test");
        assert_eq!(d1, d2);
    }

    #[test]
    fn test_digest_field() {
        let d1 = poseidon2b_digest_field(Block128::from(7u8));
        let d2 = poseidon2b_digest_field(Block128::from(7u8));
        assert_eq!(d1, d2);
    }

    #[test]
    fn test_digest_pair() {
        let d1 = poseidon2b_digest_pair(Block128::ONE, Block128::ZERO);
        let d2 = poseidon2b_digest_pair(Block128::ONE, Block128::ZERO);
        assert_eq!(d1, d2);
    }
}
