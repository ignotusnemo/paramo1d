// SPDX-License-Identifier: Apache-2.0
// Ported from hekate-math. Copyright (C) 2026 Paranoid Zero.

//! GF(2^128) — the anchor field. Quadratic extension of GF(2^64).

use crate::{
    Bit, Block16, Block32, Block64, Block8, CanonicalDeserialize, CanonicalSerialize,
    SerializationError, TowerField,
};
use serde::{Deserialize, Serialize};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use zeroize::Zeroize;

/// Element of GF(2^128), stored as packed u128.
#[derive(Copy, Clone, Default, Debug, Eq, PartialEq, Serialize, Deserialize, Zeroize)]
#[repr(transparent)]
pub struct Block128(pub u128);

impl Block128 {
    /// TAU for the extension GF(2^128) → GF(2^256) (if needed).
    /// Embedding of Block64::TAU (0x2000_0000_0000_0000) into the high half.
    pub const TAU: Self = Block128(0x2000_0000_0000_0000_0000_0000_0000_0000);

    pub fn new(lo: Block64, hi: Block64) -> Self {
        Self((hi.0 as u128) << 64 | (lo.0 as u128))
    }

    pub fn split(self) -> (Block64, Block64) {
        (Block64(self.0 as u64), Block64((self.0 >> 64) as u64))
    }

    /// Return the raw u128 representation.
    #[inline(always)]
    pub fn to_u128(self) -> u128 {
        self.0
    }

    /// Squaring in GF(2^128) via the Frobenius endomorphism.
    ///
    /// In characteristic 2, (a+b)^2 = a^2 + b^2, so squaring is a linear
    /// map (bit-expansion + reduction). This is ~20x faster than general
    /// multiplication.
    #[inline(always)]
    pub fn square(self) -> Self {
        let (a, b) = self.split();
        let a2 = a.square();
        let b2 = b.square();
        let lo = a2 + (b2 * Block64::TAU);
        let hi = b2;
        Self::new(lo, hi)
    }
}

impl TowerField for Block128 {
    const BITS: usize = 128;
    const ZERO: Self = Block128(0);
    const ONE: Self = Block128(1);
    const EXTENSION_TAU: Self = Self::TAU;

    fn invert(&self) -> Self {
        let (l, h) = self.split();
        let h2 = h * h;
        let l2 = l * l;
        let hl = h * l;
        let norm = (h2 * Block64::TAU) + hl + l2;
        let norm_inv = norm.invert();
        let res_hi = h * norm_inv;
        let res_lo = (h + l) * norm_inv;
        Self::new(res_lo, res_hi)
    }

    fn from_uniform_bytes(bytes: &[u8; 32]) -> Self {
        let mut buf = [0u8; 16];
        buf.copy_from_slice(&bytes[0..16]);
        Self(u128::from_le_bytes(buf))
    }
}

// ---- Arithmetic ----

#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for Block128 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Sub for Block128 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

impl Mul for Block128 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let (a0, a1) = self.split();
        let (b0, b1) = rhs.split();

        // Karatsuba for quadratic extension
        let v0 = a0 * b0;
        let v1 = a1 * b1;
        let v_sum = (a0 + a1) * (b0 + b1);

        let c_lo = v0 + (v1 * Block64::TAU);
        let c_hi = v0 + v_sum;

        Self::new(c_lo, c_hi)
    }
}

impl AddAssign for Block128 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
impl SubAssign for Block128 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}
impl MulAssign for Block128 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

// ---- Canonical Serialization ----

impl CanonicalSerialize for Block128 {
    fn serialized_size(&self) -> usize {
        16
    }

    fn serialize(&self, writer: &mut [u8]) -> Result<(), SerializationError> {
        if writer.len() < 16 {
            return Err(SerializationError);
        }
        writer[..16].copy_from_slice(&self.0.to_le_bytes());
        Ok(())
    }
}

impl CanonicalDeserialize for Block128 {
    fn deserialize(bytes: &[u8]) -> Result<Self, SerializationError> {
        if bytes.len() < 16 {
            return Err(SerializationError);
        }
        let mut buf = [0u8; 16];
        buf.copy_from_slice(&bytes[..16]);
        Ok(Self(u128::from_le_bytes(buf)))
    }
}

// ---- From conversions ----

impl From<u8> for Block128 {
    fn from(val: u8) -> Self {
        Self(val as u128)
    }
}
impl From<u32> for Block128 {
    fn from(val: u32) -> Self {
        Self(val as u128)
    }
}
impl From<u64> for Block128 {
    fn from(val: u64) -> Self {
        Self(val as u128)
    }
}
impl From<u128> for Block128 {
    fn from(val: u128) -> Self {
        Self(val)
    }
}

impl From<Bit> for Block128 {
    fn from(val: Bit) -> Self {
        Self(val.0 as u128)
    }
}
impl From<Block8> for Block128 {
    fn from(val: Block8) -> Self {
        Self(val.0 as u128)
    }
}
impl From<Block16> for Block128 {
    fn from(val: Block16) -> Self {
        Self(val.0 as u128)
    }
}
impl From<Block32> for Block128 {
    fn from(val: Block32) -> Self {
        Self(val.0 as u128)
    }
}
impl From<Block64> for Block128 {
    fn from(val: Block64) -> Self {
        Self(val.0 as u128)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn karatsuba_x_squared() {
        let x = Block128::new(Block64::ZERO, Block64::ONE);
        let squared = x * x;
        let (lo, hi) = squared.split();
        assert_eq!(hi, Block64::ONE);
        assert_eq!(lo, Block64(0x2000_0000_0000_0000));
    }

    #[test]
    fn embed_homomorphism() {
        let mut rng = rand::thread_rng();
        for _ in 0..30 {
            let a = Block64(rng.gen());
            let b = Block64(rng.gen());
            assert_eq!(Block128::from(a + b), Block128::from(a) + Block128::from(b));
            assert_eq!(Block128::from(a * b), Block128::from(a) * Block128::from(b));
        }
    }

    #[test]
    fn invert_random() {
        let mut rng = rand::thread_rng();
        for _ in 0..300 {
            let val = Block128(rng.gen());
            if val == Block128::ZERO {
                assert_eq!(val.invert(), Block128::ZERO);
            } else {
                assert_eq!(val * val.invert(), Block128::ONE);
            }
        }
    }
}
