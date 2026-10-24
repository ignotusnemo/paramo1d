// SPDX-License-Identifier: Apache-2.0
// Ported from hekate-math. Copyright (C) 2026 Paranoid Zero.

//! `PackableField` trait and `PackedFlat<T>` fallback (WIDTH=1).

use crate::SerializationError;
use crate::TowerField;
use crate::{CanonicalDeserialize, CanonicalSerialize};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use zeroize::Zeroize;

/// A field that can pack multiple sub-field scalars into one word.
pub trait PackableField: TowerField {
    type Scalar: TowerField;
    const WIDTH: usize;
    fn broadcast(val: Self::Scalar) -> Self;
    fn pack(vals: &[Self::Scalar]) -> Self;
    fn unpack(&self) -> Vec<Self::Scalar>;
}

/// Trivial packed field: WIDTH=1, stores one scalar. Portable fallback.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct PackedFlat<T: TowerField>(pub T);

impl<T: TowerField> PackedFlat<T> {
    pub fn new(val: T) -> Self {
        Self(val)
    }
}

impl<T: TowerField + Zeroize> Zeroize for PackedFlat<T> {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl<T: TowerField> Add for PackedFlat<T> {
    type Output = Self;
    fn add(self, r: Self) -> Self {
        Self(self.0 + r.0)
    }
}
impl<T: TowerField> Sub for PackedFlat<T> {
    type Output = Self;
    fn sub(self, r: Self) -> Self {
        Self(self.0 - r.0)
    }
}
impl<T: TowerField> Mul for PackedFlat<T> {
    type Output = Self;
    fn mul(self, r: Self) -> Self {
        Self(self.0 * r.0)
    }
}
impl<T: TowerField> AddAssign for PackedFlat<T> {
    fn add_assign(&mut self, r: Self) {
        self.0 += r.0;
    }
}
impl<T: TowerField> SubAssign for PackedFlat<T> {
    fn sub_assign(&mut self, r: Self) {
        self.0 -= r.0;
    }
}
impl<T: TowerField> MulAssign for PackedFlat<T> {
    fn mul_assign(&mut self, r: Self) {
        self.0 *= r.0;
    }
}

impl<T: TowerField> CanonicalSerialize for PackedFlat<T> {
    fn serialized_size(&self) -> usize {
        self.0.serialized_size()
    }
    fn serialize(&self, w: &mut [u8]) -> Result<(), SerializationError> {
        self.0.serialize(w)
    }
}
impl<T: TowerField> CanonicalDeserialize for PackedFlat<T> {
    fn deserialize(b: &[u8]) -> Result<Self, SerializationError> {
        T::deserialize(b).map(PackedFlat)
    }
}

impl<T: TowerField> From<u8> for PackedFlat<T> {
    fn from(v: u8) -> Self {
        Self(T::from(v))
    }
}
impl<T: TowerField> From<u32> for PackedFlat<T> {
    fn from(v: u32) -> Self {
        Self(T::from(v))
    }
}
impl<T: TowerField> From<u64> for PackedFlat<T> {
    fn from(v: u64) -> Self {
        Self(T::from(v))
    }
}
impl<T: TowerField> From<u128> for PackedFlat<T> {
    fn from(v: u128) -> Self {
        Self(T::from(v))
    }
}

impl<T: TowerField> TowerField for PackedFlat<T> {
    const BITS: usize = T::BITS;
    const ZERO: Self = PackedFlat(T::ZERO);
    const ONE: Self = PackedFlat(T::ONE);
    const EXTENSION_TAU: Self = PackedFlat(T::EXTENSION_TAU);
    fn invert(&self) -> Self {
        Self(self.0.invert())
    }
    fn from_uniform_bytes(b: &[u8; 32]) -> Self {
        Self(T::from_uniform_bytes(b))
    }
}

impl<T: TowerField> PackableField for PackedFlat<T> {
    type Scalar = T;
    const WIDTH: usize = 1;
    fn broadcast(val: T) -> Self {
        Self(val)
    }
    fn pack(vals: &[T]) -> Self {
        assert_eq!(vals.len(), 1);
        Self(vals[0])
    }
    fn unpack(&self) -> Vec<T> {
        vec![self.0]
    }
}
