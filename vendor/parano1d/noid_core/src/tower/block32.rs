// SPDX-License-Identifier: Apache-2.0
// Ported from hekate-math. Copyright (C) 2026 Paranoid Zero.

//! GF(2^32) — quadratic extension of GF(2^16).

use crate::{
    Bit, Block16, Block8, CanonicalDeserialize, CanonicalSerialize, SerializationError, TowerField,
};
use serde::{Deserialize, Serialize};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use zeroize::Zeroize;

#[derive(Copy, Clone, Default, Debug, Eq, PartialEq, Serialize, Deserialize, Zeroize)]
#[repr(transparent)]
pub struct Block32(pub u32);

impl Block32 {
    /// TAU for extending GF(2^32) → GF(2^64).
    /// This is the embedding of Block16::TAU shifted: (lo=0, hi=Block16::TAU).
    pub const TAU: Self = Block32(0x2000_0000);

    pub fn new(lo: Block16, hi: Block16) -> Self {
        Self((hi.0 as u32) << 16 | (lo.0 as u32))
    }

    pub fn split(self) -> (Block16, Block16) {
        (Block16(self.0 as u16), Block16((self.0 >> 16) as u16))
    }

    #[inline(always)]
    pub fn square(self) -> Self {
        let (a, b) = self.split();
        let a2 = a.square();
        let b2 = b.square();
        let lo = a2 + (b2 * Block16::TAU);
        let hi = b2;
        Self::new(lo, hi)
    }
}

impl TowerField for Block32 {
    const BITS: usize = 32;
    const ZERO: Self = Block32(0);
    const ONE: Self = Block32(1);
    const EXTENSION_TAU: Self = Self::TAU;

    fn invert(&self) -> Self {
        let (l, h) = self.split();
        let h2 = h * h;
        let l2 = l * l;
        let hl = h * l;
        let norm = (h2 * Block16::TAU) + hl + l2;
        let norm_inv = norm.invert();
        let res_hi = h * norm_inv;
        let res_lo = (h + l) * norm_inv;
        Self::new(res_lo, res_hi)
    }

    fn from_uniform_bytes(bytes: &[u8; 32]) -> Self {
        let mut buf = [0u8; 4];
        buf.copy_from_slice(&bytes[0..4]);
        Self(u32::from_le_bytes(buf))
    }
}

// ---- Arithmetic ----

#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for Block32 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Sub for Block32 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

impl Mul for Block32 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let (a0, a1) = self.split();
        let (b0, b1) = rhs.split();

        let v0 = a0 * b0;
        let v1 = a1 * b1;
        let v_sum = (a0 + a1) * (b0 + b1);

        // c_lo = a0*b0 + a1*b1*TAU,  c_hi = a0*b0 + (a0+a1)*(b0+b1)
        let c_lo = v0 + (v1 * Block16::TAU);
        let c_hi = v0 + v_sum;

        Self::new(c_lo, c_hi)
    }
}

impl AddAssign for Block32 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl SubAssign for Block32 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl MulAssign for Block32 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

// ---- Canonical Serialization ----

impl CanonicalSerialize for Block32 {
    fn serialized_size(&self) -> usize {
        4
    }
    fn serialize(&self, writer: &mut [u8]) -> Result<(), SerializationError> {
        if writer.len() < 4 {
            return Err(SerializationError);
        }
        writer[..4].copy_from_slice(&self.0.to_le_bytes());
        Ok(())
    }
}

impl CanonicalDeserialize for Block32 {
    fn deserialize(bytes: &[u8]) -> Result<Self, SerializationError> {
        if bytes.len() < 4 {
            return Err(SerializationError);
        }
        let mut buf = [0u8; 4];
        buf.copy_from_slice(&bytes[..4]);
        Ok(Self(u32::from_le_bytes(buf)))
    }
}

// ---- From conversions ----

impl From<u8> for Block32 {
    fn from(val: u8) -> Self {
        Self(val as u32)
    }
}
impl From<u16> for Block32 {
    fn from(val: u16) -> Self {
        Self(val as u32)
    }
}
impl From<u32> for Block32 {
    fn from(val: u32) -> Self {
        Self(val)
    }
}
impl From<u64> for Block32 {
    fn from(val: u64) -> Self {
        Self(val as u32)
    }
}
impl From<u128> for Block32 {
    fn from(val: u128) -> Self {
        Self(val as u32)
    }
}

impl From<Bit> for Block32 {
    fn from(val: Bit) -> Self {
        Self(val.0 as u32)
    }
}
impl From<Block8> for Block32 {
    fn from(val: Block8) -> Self {
        Self(val.0 as u32)
    }
}
impl From<Block16> for Block32 {
    fn from(val: Block16) -> Self {
        Self(val.0 as u32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn karatsuba_x_squared() {
        let x = Block32::new(Block16::ZERO, Block16::ONE);
        let squared = x * x;
        let (lo, hi) = squared.split();
        assert_eq!(hi, Block16::ONE);
        assert_eq!(lo, Block16(0x2000));
    }

    #[test]
    fn embed_homomorphism() {
        let mut rng = rand::thread_rng();
        for _ in 0..100 {
            let a = Block16(rng.gen());
            let b = Block16(rng.gen());
            assert_eq!(Block32::from(a + b), Block32::from(a) + Block32::from(b));
            assert_eq!(Block32::from(a * b), Block32::from(a) * Block32::from(b));
        }
    }

    #[test]
    fn invert_random() {
        let mut rng = rand::thread_rng();
        for _ in 0..1000 {
            let val = Block32(rng.gen());
            if val == Block32::ZERO {
                assert_eq!(val.invert(), Block32::ZERO);
            } else {
                assert_eq!(val * val.invert(), Block32::ONE);
            }
        }
    }
}
