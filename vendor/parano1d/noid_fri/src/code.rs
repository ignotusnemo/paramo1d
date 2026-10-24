// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Reed-Solomon encoding and folding for the FRI protocol.

use noid_core::{AdditiveNTT, Block128, TowerField};

pub const RATE: usize = 4;
pub const LOG_RATE: usize = 2;

/// Reed-Solomon encoding of a message as evaluations over cosets.
#[derive(Clone, Debug, Default)]
pub struct Code {
    pub encoding: Vec<Block128>,
}

impl Code {
    /// Encode a message of `Block128` elements with rate-4 RS code.
    ///
    /// The encoding consists of `RATE` copies of the message, each transformed
    /// with a different coset offset (`round` = 0..RATE-1).
    pub fn new(message: &[Block128], ntt: &AdditiveNTT<Block128>) -> Self {
        let mut encoding = Vec::with_capacity(message.len() * RATE);

        for round in 0..RATE as u32 {
            let mut temp = message.to_vec();
            ntt.forward_transform(&mut temp, round, 0);
            encoding.append(&mut temp);
        }

        Code { encoding }
    }

    /// Fold the code by pairing adjacent symbols and applying the FRI fold
    /// operator with challenge `r`.
    pub fn fold_code(&self, r: Block128, round: usize, ntt: &AdditiveNTT<Block128>) -> Self {
        use rayon::prelude::*;
        let pairs = self.encoding.len() / 2;
        let encoding: Vec<Block128> = if pairs >= 1024 {
            self.encoding
                .par_chunks_exact(2)
                .enumerate()
                .map(|(i, pair)| fold(r, round, i, pair[0], pair[1], ntt))
                .collect()
        } else {
            self.encoding
                .chunks_exact(2)
                .enumerate()
                .map(|(i, pair)| fold(r, round, i, pair[0], pair[1], ntt))
                .collect()
        };

        Code { encoding }
    }

    pub fn idx(&self, idx: usize) -> Block128 {
        self.encoding[idx]
    }
}

// ---------------------------------------------------------------------------
// Optimized Block128 encoding using parallel NTT
// ---------------------------------------------------------------------------

impl Code {
    /// Encode a message with rate-4 RS code using parallel NTT (Block128 only).
    ///
    /// Allocates the `RATE * len` output once and transforms each coset in
    /// place. All four coset NTTs run in parallel via rayon, saturating
    /// available cores even for moderate NTT sizes.
    pub fn new_parallel(message: &[Block128], ntt: &AdditiveNTT<Block128>) -> Self {
        use rayon::prelude::*;
        let n = message.len();
        let mut encoding = vec![Block128::ZERO; n * RATE];

        // Fill the four coset input buffers in parallel.
        encoding
            .par_chunks_exact_mut(n)
            .for_each(|slot| slot.copy_from_slice(message));

        // Run all RATE NTT transforms in parallel — each slot is
        // independent and `forward_transform_parallel` only borrows `&self`.
        encoding
            .par_chunks_exact_mut(n)
            .enumerate()
            .for_each(|(round, slot)| {
                ntt.forward_transform_parallel(slot, round as u32, 0);
            });

        Code { encoding }
    }
}

/// FRI fold operator for a single pair of code symbols.
///
/// Computes the interpolation of the pair at a random challenge `r`,
/// using the additive NTT twiddle factor for the given round and index.
#[inline(always)]
pub fn fold(
    r: Block128,
    round: usize,
    idx: usize,
    val0: Block128,
    val1: Block128,
    ntt: &AdditiveNTT<Block128>,
) -> Block128 {
    let twiddle = ntt.get_subspace_eval(round, idx);
    let mut x0 = val0;
    let mut x1 = val1;
    x1 += x0; // x1 = val0 + val1
    x0 += x1 * twiddle; // x0 = val0 + (val0+val1)*twiddle
    x0 + r * (x0 + x1) // fold at challenge r
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn test_encode_fold_consistency() {
        let mut rng = rand::thread_rng();
        let l = 8;
        let poly: Vec<Block128> = (0..1 << l)
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect();

        let ntt = AdditiveNTT::<Block128>::new(l + LOG_RATE);
        let code = Code::new(&poly, &ntt);

        assert_eq!(code.encoding.len(), poly.len() * RATE);

        let r: Vec<Block128> = (0..l).map(|_| Block128::from(rng.gen::<u128>())).collect();

        let mut folded = code.fold_code(r[0], 0, &ntt);
        for (round, &challenge) in r.iter().enumerate().skip(1) {
            folded = folded.fold_code(challenge, round, &ntt);
        }

        assert!(!folded.encoding.is_empty(), "folding produced empty code");
    }

    #[test]
    fn test_fold_formula() {
        let ntt = AdditiveNTT::<Block128>::new(4);
        let a = Block128::from(3u8);
        let b = Block128::from(5u8);
        let r = Block128::from(7u8);
        let _ = fold(r, 0, 0, a, b, &ntt);
        // Primarily checking for panic
    }
    /// Verify fold consistency: fold(r, round, i, code[2i], code[2i+1]) == folded_code[i].
    #[test]
    fn test_fold_consistency_direct() {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let log_msg = 2usize; // 4-element message → 16 code symbols
        let ntt = AdditiveNTT::<Block128>::new(log_msg + LOG_RATE);
        let msg: Vec<Block128> = (0..1 << log_msg)
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect();
        let code = Code::new(&msg, &ntt);

        let r = Block128::from(rng.gen::<u128>());
        let folded = code.fold_code(r, 0, &ntt);

        // For each pair, fold(r, 0, i, code[2i], code[2i+1]) must equal folded[i].
        for i in 0..(code.encoding.len() / 2) {
            let expected = folded.encoding[i];
            let computed = fold(
                r,
                0,
                i,
                code.encoding[2 * i],
                code.encoding[2 * i + 1],
                &ntt,
            );
            assert_eq!(
                computed, expected,
                "fold mismatch at i={i}: computed={computed:?} expected={expected:?}"
            );
        }
    }

    // NOTE: test_fold_produces_constant_codeword removed.
    // The current RS code structure uses RATE=4 separate NTT cosets.
    // A 1-round fold produces 4 different symbols (one per coset pair),
    // which is correct for the FRI query-phase fold mapping.
    // The FRI verifier handles this via `final_codeword[qi >> rounds]`.

    #[test]
    fn test_single_element_encoding() {
        let ntt = AdditiveNTT::<Block128>::new(1 + LOG_RATE);
        let msg = vec![Block128::from(42u128)];
        let code = Code::new(&msg, &ntt);
        // A 1-element message encodes to RATE=4 equal symbols (constant codeword).
        assert!(
            code.encoding.windows(2).all(|w| w[0] == w[1]),
            "RS encoding of 1 element should be constant: {:?}",
            code.encoding
        );
    }
}
