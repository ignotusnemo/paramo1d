//! Flat-basis closed-form encode kernel for the source-binding reduction.
//!
//! The wallet-capsule round-0 codeword is `Code::new_parallel(g_evals)` —
//! four cosets of the CONSTANT-twiddle additive NTT — so its MLE has the
//! closed form `codeword~(z) = Σ_i K_i(z)·g_evals[i]` with
//!
//! ```text
//!   K_i(z) = Σ_{c=0}^{3} eq₂(z_hi; c) · Π_{l=0}^{L-1} [ 1 + z_l·(1 + i_l + 2^{c+l}) ]
//! ```
//!
//! (`L = n_rounds` position bits low, 2 coset bits high, MLE LSB-first;
//! single-bit factor `M(b)[p][i] = 1 + p·(1 + i + b)`). This is the region
//! twin of `noid_fri_binius::encode_kernel`, EXCEPT the field is the flat
//! (GCM) `F128` that every region column carries, so the layer twiddle is
//! the flat image `tower_to_flat(2^{c+l})` of the native tower constant.
//! Because φ = `tower_to_flat` is a field isomorphism (multiplicative — the
//! same fact that lets `permute_flat` reproduce the tower permutation), the
//! flat kernel at any flat point reproduces the MLE of the φ-mapped tower
//! codeword; the source binding then stays entirely in the flat basis with
//! φ only at the codeword/root boundary.
//!
//! The weight actually discharged is `K_i(z)·eq(right, i)` (the source
//! binding's `g_evals = H ∘ eq_right`), fed to
//! [`crate::deep_chain::relations::verify_weighted_sum`] as its closed-form
//! `weights~(point)` callback — see [`source_weight_at`].

use crate::deep_chain::schedule::flat_of_tower_u128;
use crate::field::F128;

/// The flat layer twiddle `2^{c+l}` (native tower constant mapped through φ).
#[inline]
pub fn flat_twiddle(c: usize, l: usize) -> F128 {
    flat_of_tower_u128(1u128 << (c + l))
}

/// `eq₂(z_hi; c) = Π_k [c_k ? z_hi_k : 1 + z_hi_k]` over the 2 coset bits.
fn eq2(z_hi: &[F128], c: usize) -> F128 {
    let mut e = F128::ONE;
    for (k, &zk) in z_hi.iter().enumerate() {
        e = e * if (c >> k) & 1 == 1 {
            zk
        } else {
            F128::ONE + zk
        };
    }
    e
}

/// The encode kernel `K(z, x)` at a continuous message point `x`
/// (`x.len() == n_rounds`, `z.len() == n_rounds + 2`). Multilinear in `x`,
/// so it is the genuine MLE used at the sumcheck's derived point.
pub fn encode_kernel_weight_at(z: &[F128], x: &[F128], n_rounds: usize) -> F128 {
    assert_eq!(z.len(), n_rounds + 2, "encode kernel point arity");
    assert_eq!(x.len(), n_rounds, "message point arity");
    let z_pos = &z[..n_rounds];
    let z_hi = &z[n_rounds..];
    let mut total = F128::ZERO;
    for c in 0..4usize {
        let mut prod = F128::ONE;
        for (l, (&z_l, &x_l)) in z_pos.iter().zip(x.iter()).enumerate() {
            let two = flat_twiddle(c, l);
            prod = prod * (F128::ONE + z_l * (F128::ONE + x_l + two));
        }
        total += eq2(z_hi, c) * prod;
    }
    total
}

/// The encode kernel at a boolean message index `i`.
pub fn encode_kernel_weight(z: &[F128], i: usize, n_rounds: usize) -> F128 {
    let x: Vec<F128> = (0..n_rounds)
        .map(|l| {
            if (i >> l) & 1 == 1 {
                F128::ONE
            } else {
                F128::ZERO
            }
        })
        .collect();
    encode_kernel_weight_at(z, &x, n_rounds)
}

/// `eq(right, x) = Π_l [right_l·x_l + (1+right_l)(1+x_l)]` in the flat basis.
pub fn eq_at(right: &[F128], x: &[F128]) -> F128 {
    assert_eq!(right.len(), x.len(), "eq arity");
    let mut e = F128::ONE;
    for (&r, &xx) in right.iter().zip(x.iter()) {
        e = e * (r * xx + (F128::ONE + r) * (F128::ONE + xx));
    }
    e
}

/// The MLE of the source-binding weight SEQUENCE `W_i = K_i(z)·eq(right,i)`
/// evaluated at a continuous point `x` — the closed-form `weights~(point)`
/// callback for the encode discharge (`codeword~(z) = Σ_i W_i·H[i]`).
///
/// NB this is NOT `K(z,x)·eq(right,x)`: the product of two multilinears is
/// degree-2, whereas `W~` is genuinely multilinear. Both `K_i` and
/// `eq(right,i)` are tensors over the bits of `i`, so `W_i = Σ_c eq₂(z_hi;c)
/// Π_l h_{c,l}(i_l)` with `h_{c,l}(b) = f_{c,l}(b)·g_l(b)`, and its MLE folds
/// each bit ONCE: `Π_l [h_{c,l}(0)(1+x_l) + h_{c,l}(1)·x_l]`. Per-bit,
/// `f_{c,l}(0)=1+z_l(1+2^{c+l})`, `f_{c,l}(1)=1+z_l·2^{c+l}` (char 2),
/// `g_l(0)=1+right_l`, `g_l(1)=right_l`.
pub fn source_weight_at(z: &[F128], right: &[F128], x: &[F128], n_rounds: usize) -> F128 {
    assert_eq!(z.len(), n_rounds + 2, "encode kernel point arity");
    assert_eq!(x.len(), n_rounds, "message point arity");
    assert_eq!(right.len(), n_rounds, "right arity");
    let z_pos = &z[..n_rounds];
    let z_hi = &z[n_rounds..];
    let mut total = F128::ZERO;
    for c in 0..4usize {
        let mut prod = F128::ONE;
        for l in 0..n_rounds {
            let two = flat_twiddle(c, l);
            let f0 = F128::ONE + z_pos[l] * (F128::ONE + two);
            let f1 = F128::ONE + z_pos[l] * two;
            let g0 = F128::ONE + right[l];
            let g1 = right[l];
            let h0 = f0 * g0;
            let h1 = f1 * g1;
            prod = prod * (h0 * (F128::ONE + x[l]) + h1 * x[l]);
        }
        total += eq2(z_hi, c) * prod;
    }
    total
}

/// `codeword~(z) = Σ_i K_i(z)·g_evals[i]` (the closed-form codeword MLE).
pub fn encode_mle_via_kernel(g_evals: &[F128], z: &[F128], n_rounds: usize) -> F128 {
    assert_eq!(g_evals.len(), 1usize << n_rounds, "message length");
    let mut acc = F128::ZERO;
    for (i, &g) in g_evals.iter().enumerate() {
        acc += encode_kernel_weight(z, i, n_rounds) * g;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lincheck::build_eq_table;

    struct Rng(u64);
    impl Rng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            z ^ (z >> 31)
        }
        fn f128(&mut self) -> F128 {
            F128 {
                lo: self.next_u64(),
                hi: self.next_u64(),
            }
        }
    }

    fn mle_eval(vals: &[F128], z: &[F128]) -> F128 {
        let eq = build_eq_table(z);
        let mut acc = F128::ZERO;
        for (v, e) in vals.iter().zip(eq.iter()) {
            acc += *v * *e;
        }
        acc
    }

    /// The flat kernel is genuinely multilinear in `x` (agrees with the
    /// boolean-index weights when extended), and `encode_mle_via_kernel`
    /// matches the direct MLE of the codeword the kernel implies. (Cross-
    /// validation against the REAL tower `Code::new_parallel` lives in
    /// noid_recursive, which can reach noid_fri_binius.)
    #[test]
    fn flat_kernel_self_consistent_mle() {
        let mut rng = Rng(0xF1A7);
        for n_rounds in [1usize, 2, 3, 5] {
            let g: Vec<F128> = (0..(1usize << n_rounds)).map(|_| rng.f128()).collect();
            // Materialize the codeword the kernel implies at every boolean point.
            let codeword: Vec<F128> = (0..(1usize << (n_rounds + 2)))
                .map(|j| {
                    let z: Vec<F128> = (0..n_rounds + 2)
                        .map(|k| {
                            if (j >> k) & 1 == 1 {
                                F128::ONE
                            } else {
                                F128::ZERO
                            }
                        })
                        .collect();
                    encode_mle_via_kernel(&g, &z, n_rounds)
                })
                .collect();
            // At a random z, the closed-form kernel sum equals the codeword MLE.
            let z: Vec<F128> = (0..n_rounds + 2).map(|_| rng.f128()).collect();
            assert_eq!(
                encode_mle_via_kernel(&g, &z, n_rounds),
                mle_eval(&codeword, &z),
                "kernel not multilinear at n_rounds={n_rounds}"
            );
        }
    }
}
