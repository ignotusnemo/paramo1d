// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. Ported from hekate-math.

use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use zeroize::Zeroize;

/// Serialization/deserialization error type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SerializationError;

impl core::fmt::Display for SerializationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "serialization error")
    }
}

/// The core trait for tower-constructed binary field elements.
///
/// The tower is:
///   Bit(GF2) ⊂ Block8(GF(2^8)) ⊂ Block16 ⊂ Block32 ⊂ Block64 ⊂ Block128
///
/// Each level `K` stores `EXTENSION_TAU` — the constant for the
/// quadratic extension to the next level, satisfying:
///   F_{2K} = F_K\[X\] / (X^2 + X + EXTENSION_TAU)
pub trait TowerField:
    Copy
    + Default
    + Clone
    + PartialEq
    + Eq
    + core::fmt::Debug
    + Send
    + Sync
    + From<u8>
    + From<u32>
    + From<u64>
    + From<u128>
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + CanonicalSerialize
    + CanonicalDeserialize
    + Zeroize
{
    /// Number of bits in this field element.
    const BITS: usize;

    /// Additive identity.
    const ZERO: Self;

    /// Multiplicative identity.
    const ONE: Self;

    /// The constant `TAU` such that the next extension field is
    /// defined as `F[X] / (X^2 + X + EXTENSION_TAU)`.
    const EXTENSION_TAU: Self;

    /// Returns the multiplicative inverse of this element.
    /// By convention, invert(0) == 0 (constant-time without branching).
    fn invert(&self) -> Self;

    /// Constructs a field element from uniform random bytes
    /// (e.g. hash output). Input is strictly 32 bytes.
    fn from_uniform_bytes(bytes: &[u8; 32]) -> Self;
}

/// Serialization of field elements to bytes (little-endian).
pub trait CanonicalSerialize {
    /// Size in bytes this element serializes to.
    fn serialized_size(&self) -> usize;

    /// Serialize into the provided buffer.
    /// Returns `Err(SerializationError)` if the buffer is too small.
    fn serialize(&self, writer: &mut [u8]) -> Result<(), SerializationError>;

    /// Convenience: serialize to a new `Vec<u8>`.
    fn to_bytes(&self) -> Vec<u8> {
        let size = self.serialized_size();
        let mut buf = vec![0u8; size];
        self.serialize(&mut buf).expect("Size calculation matches");
        buf
    }
}

/// Deserialization of field elements from bytes (little-endian).
pub trait CanonicalDeserialize: Sized {
    /// Deserialize from a byte slice.
    /// Returns `Err(SerializationError)` if the slice is too short or invalid.
    fn deserialize(bytes: &[u8]) -> Result<Self, SerializationError>;
}
