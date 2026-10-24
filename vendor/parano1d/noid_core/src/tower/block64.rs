// SPDX-License-Identifier: Apache-2.0
// Ported from hekate-math. Copyright (C) 2026 Paranoid Zero.

//! GF(2^64) — quadratic extension of GF(2^32).

use crate::{
    Bit, Block16, Block32, Block8, CanonicalDeserialize, CanonicalSerialize, SerializationError,
    TowerField,
};
use serde::{Deserialize, Serialize};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use zeroize::Zeroize;

/// Element of GF(2^64), stored as packed u64.
#[derive(Copy, Clone, Default, Debug, Eq, PartialEq, Serialize, Deserialize, Zeroize)]
#[repr(transparent)]
pub struct Block64(pub u64);

impl Block64 {
    /// TAU for the extension GF(2^64) → GF(2^128).
    /// Embedding of Block32::TAU (0x2000_0000) into the high half.
    pub const TAU: Self = Block64(0x2000_0000_0000_0000);

    pub fn new(lo: Block32, hi: Block32) -> Self {
        Self((hi.0 as u64) << 32 | (lo.0 as u64))
    }

    pub fn split(self) -> (Block32, Block32) {
        (Block32(self.0 as u32), Block32((self.0 >> 32) as u32))
    }
    #[inline(always)]
    pub fn square(self) -> Self {
        let (a, b) = self.split();
        let a2 = a.square();
        let b2 = b.square();
        let lo = a2 + (b2 * Block32::TAU);
        let hi = b2;
        Self::new(lo, hi)
    }
}

impl TowerField for Block64 {
    const BITS: usize = 64;
    const ZERO: Self = Block64(0);
    const ONE: Self = Block64(1);
    const EXTENSION_TAU: Self = Self::TAU;

    fn invert(&self) -> Self {
        let (l, h) = self.split();
        let h2 = h * h;
        let l2 = l * l;
        let hl = h * l;
        let norm = (h2 * Block32::TAU) + hl + l2;
        let norm_inv = norm.invert();
        let res_hi = h * norm_inv;
        let res_lo = (h + l) * norm_inv;
        Self::new(res_lo, res_hi)
    }

    fn from_uniform_bytes(bytes: &[u8; 32]) -> Self {
        let mut buf = [0u8; 8];
        buf.copy_from_slice(&bytes[0..8]);
        Self(u64::from_le_bytes(buf))
    }
}

// ---- Arithmetic ----

#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for Block64 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Sub for Block64 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}
impl Mul for Block64 {
    type Output = Self;

    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        let (a0, a1) = self.split();
        let (b0, b1) = rhs.split();

        // Karatsuba over the tower extension GF(2^64) = GF(2^32)[y]/(y^2+y+TAU_32).
        let v0 = a0 * b0;
        let v1 = a1 * b1;
        let v_sum = (a0 + a1) * (b0 + b1);

        let c_lo = v0 + (v1 * Block32::TAU);
        let c_hi = v0 + v_sum;

        Self::new(c_lo, c_hi)
    }
}
impl AddAssign for Block64 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
impl SubAssign for Block64 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}
impl MulAssign for Block64 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

// ---- Canonical Serialization ----
impl CanonicalSerialize for Block64 {
    fn serialized_size(&self) -> usize {
        8
    }

    fn serialize(&self, writer: &mut [u8]) -> Result<(), SerializationError> {
        if writer.len() < 8 {
            return Err(SerializationError);
        }
        writer[..8].copy_from_slice(&self.0.to_le_bytes());
        Ok(())
    }
}

impl CanonicalDeserialize for Block64 {
    fn deserialize(bytes: &[u8]) -> Result<Self, SerializationError> {
        if bytes.len() < 8 {
            return Err(SerializationError);
        }
        let mut buf = [0u8; 8];
        buf.copy_from_slice(&bytes[..8]);
        Ok(Self(u64::from_le_bytes(buf)))
    }
}

// ---- From conversions ----

impl From<u8> for Block64 {
    fn from(val: u8) -> Self {
        Self(val as u64)
    }
}
impl From<u32> for Block64 {
    fn from(val: u32) -> Self {
        Self(val as u64)
    }
}
impl From<u64> for Block64 {
    fn from(val: u64) -> Self {
        Self(val)
    }
}
impl From<u128> for Block64 {
    fn from(val: u128) -> Self {
        Self(val as u64)
    }
}

impl From<Bit> for Block64 {
    fn from(val: Bit) -> Self {
        Self(val.0 as u64)
    }
}
impl From<Block8> for Block64 {
    fn from(val: Block8) -> Self {
        Self(val.0 as u64)
    }
}
impl From<Block16> for Block64 {
    fn from(val: Block16) -> Self {
        Self(val.0 as u64)
    }
}
impl From<Block32> for Block64 {
    fn from(val: Block32) -> Self {
        Self(val.0 as u64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn karatsuba_x_squared() {
        let x = Block64::new(Block32::ZERO, Block32::ONE);
        let squared = x * x;
        let (lo, hi) = squared.split();
        assert_eq!(hi, Block32::ONE);
        assert_eq!(lo, Block32(0x2000_0000));
    }

    #[test]
    fn embed_homomorphism() {
        let mut rng = rand::thread_rng();
        for _ in 0..100 {
            let a = Block32(rng.gen());
            let b = Block32(rng.gen());
            assert_eq!(Block64::from(a + b), Block64::from(a) + Block64::from(b));
            assert_eq!(Block64::from(a * b), Block64::from(a) * Block64::from(b));
        }
    }

    #[test]
    fn invert_random() {
        let mut rng = rand::thread_rng();
        for _ in 0..1000 {
            let val = Block64(rng.gen());
            if val == Block64::ZERO {
                assert_eq!(val.invert(), Block64::ZERO);
            } else {
                assert_eq!(val * val.invert(), Block64::ONE);
            }
        }
    }
}
