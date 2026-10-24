// SPDX-License-Identifier: Apache-2.0
// Ported from hekate-math. Copyright (C) 2026 Paranoid Zero.

//! GF(2^16) — quadratic extension of GF(2^8) with TAU = (0x20 left-shifted).

use crate::{
    Bit, Block8, CanonicalDeserialize, CanonicalSerialize, SerializationError, TowerField,
};
use serde::{Deserialize, Serialize};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use zeroize::Zeroize;

/// Element of GF(2^16), represented internally as a packed u16.
/// The low byte is the first coordinate, the high byte the second.
#[derive(Copy, Clone, Default, Debug, Eq, PartialEq, Serialize, Deserialize, Zeroize)]
#[repr(transparent)]
pub struct Block16(pub u16);

impl Block16 {
    /// TAU for extending GF(2^16) → GF(2^32).
    /// This is the embedding of Block8::EXTENSION_TAU (0x20) shifted
    /// to the high part: (lo=0, hi=0x20).
    pub const TAU: Self = Block16(0x2000);

    pub fn new(lo: Block8, hi: Block8) -> Self {
        Self((hi.0 as u16) << 8 | (lo.0 as u16))
    }

    pub fn split(self) -> (Block8, Block8) {
        (Block8(self.0 as u8), Block8((self.0 >> 8) as u8))
    }

    #[inline(always)]
    pub fn square(self) -> Self {
        let (a, b) = self.split();
        // (a + b*y)^2 = a^2 + b^2*y^2 = a^2 + b^2*(y + TAU)
        //             = (a^2 + b^2*TAU) + b^2*y
        let a2 = a.square();
        let b2 = b.square();
        let lo = a2 + (b2 * Block8::EXTENSION_TAU);
        let hi = b2;
        Self::new(lo, hi)
    }
}

impl TowerField for Block16 {
    const BITS: usize = 16;
    const ZERO: Self = Block16(0);
    const ONE: Self = Block16(1);
    const EXTENSION_TAU: Self = Self::TAU;

    fn invert(&self) -> Self {
        let (l, h) = self.split();
        // Norm = h^2 * TAU_8 + h*l + l^2
        let h2 = h * h;
        let l2 = l * l;
        let hl = h * l;
        let norm = (h2 * Block8::EXTENSION_TAU) + hl + l2;
        let norm_inv = norm.invert();
        let res_hi = h * norm_inv;
        let res_lo = (h + l) * norm_inv;
        Self::new(res_lo, res_hi)
    }

    fn from_uniform_bytes(bytes: &[u8; 32]) -> Self {
        let mut buf = [0u8; 2];
        buf.copy_from_slice(&bytes[0..2]);
        Self(u16::from_le_bytes(buf))
    }
}

// ---- Arithmetic ----

#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for Block16 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Sub for Block16 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

impl Mul for Block16 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let (a0, a1) = self.split();
        let (b0, b1) = rhs.split();

        // Karatsuba multiplication for quadratic extensions:
        // (a0 + a1*X) * (b0 + b1*X)
        //   = (a0*b0 + a1*b1*TAU) + ((a0+a1)*(b0+b1) - a0*b0 - a1*b1)*X
        // In char 2: subtraction = addition.
        //   c_lo = a0*b0 + a1*b1*TAU
        //   c_hi = a0*b0 + (a0+a1)*(b0+b1)
        let v0 = a0 * b0;
        let v1 = a1 * b1;
        let v_sum = (a0 + a1) * (b0 + b1);

        let c_lo = v0 + (v1 * Block8::EXTENSION_TAU);
        let c_hi = v0 + v_sum;

        Self::new(c_lo, c_hi)
    }
}

impl AddAssign for Block16 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl SubAssign for Block16 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl MulAssign for Block16 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

// ---- Canonical Serialization ----

impl CanonicalSerialize for Block16 {
    fn serialized_size(&self) -> usize {
        2
    }

    fn serialize(&self, writer: &mut [u8]) -> Result<(), SerializationError> {
        if writer.len() < 2 {
            return Err(SerializationError);
        }
        writer[..2].copy_from_slice(&self.0.to_le_bytes());
        Ok(())
    }
}

impl CanonicalDeserialize for Block16 {
    fn deserialize(bytes: &[u8]) -> Result<Self, SerializationError> {
        if bytes.len() < 2 {
            return Err(SerializationError);
        }
        let mut buf = [0u8; 2];
        buf.copy_from_slice(&bytes[..2]);
        Ok(Self(u16::from_le_bytes(buf)))
    }
}

// ---- From conversions ----

impl From<u8> for Block16 {
    fn from(val: u8) -> Self {
        Self(val as u16)
    }
}
impl From<u16> for Block16 {
    fn from(val: u16) -> Self {
        Self(val)
    }
}
impl From<u32> for Block16 {
    fn from(val: u32) -> Self {
        Self(val as u16)
    }
}
impl From<u64> for Block16 {
    fn from(val: u64) -> Self {
        Self(val as u16)
    }
}
impl From<u128> for Block16 {
    fn from(val: u128) -> Self {
        Self(val as u16)
    }
}

impl From<Bit> for Block16 {
    fn from(val: Bit) -> Self {
        Self(val.0 as u16)
    }
}
impl From<Block8> for Block16 {
    fn from(val: Block8) -> Self {
        Self(val.0 as u16)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn karatsuba_x_squared() {
        // X = (lo=0, hi=1), so X^2 = X + TAU_8
        // TAU_8 = 0x20, so X^2 should be (lo=0x20, hi=1)
        let x = Block16::new(Block8::ZERO, Block8::ONE);
        let squared = x * x;
        let (lo, hi) = squared.split();
        assert_eq!(hi, Block8::ONE);
        assert_eq!(lo, Block8(0x20));
    }

    #[test]
    fn embed_homomorphism() {
        let mut rng = rand::thread_rng();
        for _ in 0..100 {
            let a = Block8(rng.gen());
            let b = Block8(rng.gen());

            let a_lifted: Block16 = a.into();
            let b_lifted: Block16 = b.into();

            // add homomorphism
            assert_eq!(Block16::from(a + b), a_lifted + b_lifted);
            // mul homomorphism
            assert_eq!(Block16::from(a * b), a_lifted * b_lifted);
        }
    }

    #[test]
    fn invert_random() {
        let mut rng = rand::thread_rng();
        for _ in 0..1000 {
            let val = Block16(rng.gen());
            if val == Block16::ZERO {
                assert_eq!(val.invert(), Block16::ZERO);
            } else {
                assert_eq!(val * val.invert(), Block16::ONE);
            }
        }
    }
}
