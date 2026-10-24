// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero. All rights reserved.

//! Fast Karatsuba multiplication for binary tower fields.
//!
//! The tower type hierarchy already implements Karatsuba recursively:
//!   Block128 → Block64 → Block32 → Block16 → Block8
//!
//! The base case `Block8::mul` uses a precomputed 256×256 lookup table,
//! so the full multiplication is already optimal.  This module simply
//! re-exports the scalar fast path for use in packed lanes.

use crate::Block128;

/// Fast Block128 multiplication.
///
/// Delegates to `Block128::mul` (via the `*` operator), which uses
/// recursive Karatsuba down to a GF(2^8) lookup-table base case.
#[inline(always)]
pub fn mul_block128_fast(a: Block128, b: Block128) -> Block128 {
    a * b
}
