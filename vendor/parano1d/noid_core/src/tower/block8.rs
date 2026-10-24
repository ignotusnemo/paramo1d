// SPDX-License-Identifier: Apache-2.0
// Ported from hekate-math. Copyright (C) 2026 Paranoid Zero.

//! GF(2^8) — AES polynomial: x^8 + x^4 + x^3 + x + 1 (0x11B)

use crate::{Bit, CanonicalDeserialize, CanonicalSerialize, SerializationError, TowerField};
use serde::{Deserialize, Serialize};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use zeroize::Zeroize;

/// An element of GF(2^8) using the AES irreducible polynomial.
#[derive(Copy, Clone, Default, Debug, Eq, PartialEq, Serialize, Deserialize, Zeroize)]
#[repr(transparent)]
pub struct Block8(pub u8);

impl Block8 {
    pub const fn new(val: u8) -> Self {
        Self(val)
    }

    /// Precomputed GF(2^8) squaring table: `SQR_TABLE[a]` = a².
    /// Built at compile time from the multiplication table.
    pub const SQR_TABLE: [u8; 256] = {
        let mut table = [0u8; 256];
        let mut i = 0;
        while i < 256 {
            table[i] = GF256_MUL_TABLE[i][i];
            i += 1;
        }
        table
    };

    #[inline(always)]
    pub fn square(self) -> Self {
        Self(Self::SQR_TABLE[self.0 as usize])
    }
}

impl TowerField for Block8 {
    const BITS: usize = 8;
    const ZERO: Self = Block8(0);
    const ONE: Self = Block8(1);

    /// Extension constant for GF(2^8) → GF(2^16).
    /// Irreducible polynomial: X^2 + X + 0x20 = 0 over GF(2^8).
    const EXTENSION_TAU: Self = Block8(0x20);

    fn invert(&self) -> Self {
        // GF(2^8) inverse via lookup table — O(1), debug-mode fast.
        Self(GF256_INV_TABLE[self.0 as usize])
    }

    fn from_uniform_bytes(bytes: &[u8; 32]) -> Self {
        Self(bytes[0])
    }
}

// ---- Arithmetic ----

#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for Block8 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Sub for Block8 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self.add(rhs)
    }
}

impl Mul for Block8 {
    type Output = Self;

    #[inline(always)]
    fn mul(self, rhs: Self) -> Self::Output {
        // GF(2^8) multiplication via a precomputed 256×256 lookup table.
        // O(1), zero branches, zero loops — fast even in debug builds.
        Self(GF256_MUL_TABLE[self.0 as usize][rhs.0 as usize])
    }
}

/// Precomputed GF(2^8) multiplication table with AES poly 0x11B.
/// GF256_MUL_TABLE[a][b] = a * b  for all a, b in 0..256.
static GF256_MUL_TABLE: [[u8; 256]; 256] = {
    // We need a const fn to build this at compile time.
    // Use carry-less multiply + Barrett reduction.
    const fn gf256_mul_entry(a: u8, b: u8) -> u8 {
        // Carry-less 8×8 multiply into 15 bits.
        let a = a as u16;
        let b = b as u16;
        let mut p: u16 = 0;
        let mut i = 0u16;
        while i < 8 {
            if (b >> i) & 1 == 1 {
                p ^= a << i;
            }
            i += 1;
        }
        // Reduce mod 0x11B (x^8+x^4+x^3+x+1).
        // Process bits 14 down to 8.
        const POLY: u16 = 0x1B;
        if (p >> 14) & 1 == 1 {
            p ^= POLY << 6;
        }
        if (p >> 13) & 1 == 1 {
            p ^= POLY << 5;
        }
        if (p >> 12) & 1 == 1 {
            p ^= POLY << 4;
        }
        if (p >> 11) & 1 == 1 {
            p ^= POLY << 3;
        }
        if (p >> 10) & 1 == 1 {
            p ^= POLY << 2;
        }
        if (p >> 9) & 1 == 1 {
            p ^= POLY << 1;
        }
        if (p >> 8) & 1 == 1 {
            p ^= POLY;
        }
        p as u8
    }
    const fn build() -> [[u8; 256]; 256] {
        let mut table = [[0u8; 256]; 256];
        let mut a = 0usize;
        while a < 256 {
            let mut b = 0usize;
            while b < 256 {
                table[a][b] = gf256_mul_entry(a as u8, b as u8);
                b += 1;
            }
            a += 1;
        }
        table
    }
    build()
};

/// Precomputed GF(2^8) inverse table: GF256_INV_TABLE[a] = a^{-1}, with INV[0]=0.
static GF256_INV_TABLE: [u8; 256] = {
    const fn build() -> [u8; 256] {
        let mut table = [0u8; 256];
        // Use the multiply table to find inverses: search for b s.t. a*b == 1.
        // For a=0, inv=0 (convention).
        let mut a = 1usize;
        while a < 256 {
            let mut b = 1usize;
            while b < 256 {
                if GF256_MUL_TABLE[a][b] == 1 {
                    table[a] = b as u8;
                    break;
                }
                b += 1;
            }
            a += 1;
        }
        table
    }
    build()
};

impl AddAssign for Block8 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl SubAssign for Block8 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl MulAssign for Block8 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

// ---- Canonical Serialization ----

impl CanonicalSerialize for Block8 {
    fn serialized_size(&self) -> usize {
        1
    }
    fn serialize(&self, writer: &mut [u8]) -> Result<(), SerializationError> {
        if writer.is_empty() {
            return Err(SerializationError);
        }
        writer[0] = self.0;
        Ok(())
    }
}

impl CanonicalDeserialize for Block8 {
    fn deserialize(bytes: &[u8]) -> Result<Self, SerializationError> {
        if bytes.is_empty() {
            return Err(SerializationError);
        }
        Ok(Self(bytes[0]))
    }
}

// ---- From conversions ----

impl From<u8> for Block8 {
    fn from(val: u8) -> Self {
        Self(val)
    }
}
impl From<u32> for Block8 {
    fn from(val: u32) -> Self {
        Self(val as u8)
    }
}
impl From<u64> for Block8 {
    fn from(val: u64) -> Self {
        Self(val as u8)
    }
}
impl From<u128> for Block8 {
    fn from(val: u128) -> Self {
        Self(val as u8)
    }
}

impl From<Bit> for Block8 {
    fn from(val: Bit) -> Self {
        Self(val.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_mul_basics() {
        assert_eq!(Block8(2) * Block8(2), Block8(4));
        // AES test vector: 0x57 * 0x83 = 0xC1
        assert_eq!(Block8(0x57) * Block8(0x83), Block8(0xC1));
    }

    #[test]
    fn invert_exhaustive() {
        for i in 0u8..=255 {
            let val = Block8(i);
            if val == Block8::ZERO {
                assert_eq!(val.invert(), Block8::ZERO);
            } else {
                assert_eq!(val * val.invert(), Block8::ONE);
            }
        }
    }

    #[test]
    fn zeroize_works() {
        let mut secret = Block8(0xFF);
        secret.zeroize();
        assert_eq!(secret, Block8::ZERO);
    }
}
