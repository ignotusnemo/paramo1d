// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! SIMD-accelerated squaring for binary tower fields.
//!
//! In GF(2^n), squaring is a LINEAR operation (Frobenius endomorphism):
//!   (a + b)^2 = a^2 + b^2
//!
//! The tower types implement this recursively:
//!   Block8  → precomputed 256-byte lookup table
//!   Block16 → (a^2 + b^2*TAU) + b^2*y
//!   Block32 → same pattern
//!   Block64 → same pattern
//!   Block128→ same pattern
//!
//! This module re-exports the scalar fast path for use in packed lanes.

use crate::Block128;

/// Fast Block128 squaring via the Frobenius endomorphism.
///
/// Delegates to `Block128::square()` which recursively uses
/// dedicated `square()` methods at each tower level, bottoming
/// out at a GF(2^8) lookup table.
#[inline(always)]
pub fn square_block128(x: Block128) -> Block128 {
    x.square()
}
