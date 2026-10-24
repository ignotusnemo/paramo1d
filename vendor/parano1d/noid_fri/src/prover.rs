// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! FRI Prover: commit phase, query phase, and proof structures.
//!
//! Implements a PCS (Polynomial Commitment Scheme) over binary tower fields
//! using the FRI protocol with Poseidon2b Merkle trees.

use noid_core::{AdditiveNTT, Block128, TowerField};
use rayon::prelude::*;

use crate::channel::{Channel, TAU};
use crate::code::{Code, LOG_RATE};
use crate::hasher::{CryptographicHasher, HashOutput};
use crate::merkle::{compute_leaf_hashes, MerkleTree, VectorCommitment};

// ---------------------------------------------------------------------------
// Public proof structures
// ---------------------------------------------------------------------------

/// A degree-1 or degree-2 univariate polynomial stored by its coefficients.
///
/// Used to represent Sum-Check round oracles.
#[derive(Clone, Debug)]
pub struct Univariate {
    /// Coefficients in ascending degree order: `coeffs[0] + coeffs[1]*X + ...`
    pub coeffs: Vec<Block128>,
}

impl Univariate {
    pub fn new(coeffs: Vec<Block128>) -> Self {
        Self { coeffs }
    }

    /// Evaluate the polynomial at `x`.
    pub fn evaluate(&self, x: Block128) -> Block128 {
        let mut result = Block128::ZERO;
        let mut power = Block128::ONE;
        for &c in &self.coeffs {
            result += c * power;
            power *= x;
        }
        result
    }
}

/// The FRI commitment: root of the Merkle tree over the RS-encoded message,
/// plus metadata needed by the verifier.
#[derive(Clone, Debug)]
pub struct FriCommitment {
    pub vector_commitment: VectorCommitment,
    /// Number of field elements packed into each leaf (always 1 for us).
    pub packing_factor: usize,
    /// log2 of the number of message symbols.
    pub log_len: usize,
}

/// A full FRI evaluation proof (DEEP-FRI style).
///
/// Proves that a committed polynomial evaluates to `eval` at `eval_point`.
#[derive(Clone, Debug)]
pub struct EvalProof {
    /// Partial evaluations over the top TAU variables (the "left" split).
    pub upper_partial_evals: Vec<Block128>,
    /// Per-round Sum-Check univariate oracles.
    pub sum_check_oracles: Vec<Univariate>,
    /// Per-round FRI oracle commitments (roots of folded trees).
    pub fri_oracles: Vec<VectorCommitment>,
    /// Per-round queried symbol pairs `(s0, s1)` for each query index.
    pub fri_queried_symbols: Vec<Vec<(Block128, Block128)>>,
    /// Per-round Merkle paths for the queried symbol pairs.
    pub fri_merkle_paths: Vec<Vec<Vec<HashOutput>>>,
    /// The full final codeword after all folding rounds.
    /// Length = RATE (= 4) symbols encoding the single remaining message element.
    /// The verifier checks each query's fold result against
    /// `final_codeword[pair_idx % final_codeword.len()]`.
    pub final_codeword: Vec<Block128>,
}

impl EvalProof {
    pub fn byte_len(&self) -> usize {
        let upper = self.upper_partial_evals.len() * 16;
        let sc: usize = self
            .sum_check_oracles
            .iter()
            .map(|u| u.coeffs.len() * 16)
            .sum();
        let oracles = self.fri_oracles.len() * 32;
        let symbols: usize = self
            .fri_queried_symbols
            .iter()
            .map(|v| v.len() * 2 * 16)
            .sum();
        let paths: usize = self
            .fri_merkle_paths
            .iter()
            .map(|round| round.iter().map(|p| p.len() * 32).sum::<usize>())
            .sum();
        let final_cw = self.final_codeword.len() * 16;
        upper + sc + oracles + symbols + paths + final_cw
    }
}

// ---------------------------------------------------------------------------
// Optimized evaluation helpers (Block128 packed paths)
// ---------------------------------------------------------------------------

use noid_core::packed::PACKED_LANES;

/// Evaluate a multilinear extension at `point`.
/// Uses packed SIMD when the evaluation vector is large enough.
fn mle_evaluate(evals: &[Block128], point: &[Block128]) -> Block128 {
    if point.is_empty() {
        return if evals.is_empty() {
            Block128::ZERO
        } else {
            evals[0]
        };
    }
    // Use packed path when alignment and size allow it.
    if PACKED_LANES > 1 && evals.len() >= PACKED_LANES && evals.len().is_multiple_of(PACKED_LANES) {
        noid_core::mle::evaluate::evaluate_packed(evals, point)
    } else {
        mle_evaluate_scalar(evals, point)
    }
}

/// Scalar fallback for tiny inputs.
fn mle_evaluate_scalar(evals: &[Block128], point: &[Block128]) -> Block128 {
    let mut buf = evals.to_vec();
    for &r in point.iter().rev() {
        let half = buf.len() / 2;
        for i in 0..half {
            buf[i] = buf[i] + r * (buf[i + half] + buf[i]);
        }
        buf.truncate(half);
    }
    buf[0]
}

/// Fold an evaluation vector in half using packed ops when possible.
fn fold_evals(evals: &[Block128], r: Block128) -> Vec<Block128> {
    use rayon::prelude::*;
    let half = evals.len() / 2;
    if PACKED_LANES > 1 && half >= PACKED_LANES && evals.len().is_multiple_of(PACKED_LANES) {
        let mut data = evals.to_vec();
        noid_core::sumcheck::prove::fold_highest_var_packed_inplace(&mut data, r, half);
        data
    } else if half >= 1024 {
        let (lo, hi) = evals.split_at(half);
        lo.par_iter()
            .zip(hi.par_iter())
            .map(|(l, h)| *l + r * *h)
            .collect()
    } else {
        (0..half).map(|i| evals[i] + r * evals[i + half]).collect()
    }
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Commit to a multilinear polynomial given by its evaluations on the hypercube.
///
/// Encodes the evaluations with the Reed-Solomon code and returns both the
/// Merkle commitment and the `Code` object (needed for the proof phase).
pub fn commit(
    evals: &[Block128],
    ntt: &AdditiveNTT<Block128>,
    hasher: &dyn CryptographicHasher,
) -> (FriCommitment, MerkleTree, Code) {
    assert!(
        evals.len().is_power_of_two(),
        "evaluation vector length must be a power of two"
    );
    let log_len = evals.len().trailing_zeros() as usize;

    // Encode with parallel NTT (Block128-only optimized path).
    let code = Code::new_parallel(evals, ntt);

    // Build Merkle tree over the encoded symbols using parallel hashing.
    // Pair adjacent symbols for the leaf hashing (rate=4, so 4*len symbols).
    let leaf_hashes = compute_leaf_hashes(&code.encoding, hasher);
    let tree = MerkleTree::new_parallel(leaf_hashes, hasher);
    let root = tree.get_root();
    let depth = tree.num_layers() - 1;

    let commitment = FriCommitment {
        vector_commitment: VectorCommitment { root, depth },
        packing_factor: 1,
        log_len,
    };

    (commitment, tree, code)
}

/// Generate a FRI evaluation proof for `eval_point`.
///
/// Assumes `evals` is the same vector that was committed with `commit()`.
///
/// The caller is responsible for having absorbed the commitment that binds
/// `evals` into the transcript **before** this call (via
/// `channel.observe_fri_commitment(...)`). This is what lets the
/// RLC-batched path skip the commitment step entirely: the batched
/// codeword `C_batch = Σ λ_i · C_i` is a linear combination of already-
/// committed columns, so the per-column roots upstream are sufficient
/// binding — no extra Merkle tree over `C_batch` is needed.
pub fn prove(
    evals: &[Block128],
    eval_point: &[Block128],
    ntt: &AdditiveNTT<Block128>,
    channel: &mut Channel,
    hasher: &dyn CryptographicHasher,
) -> EvalProof {
    // Absorb the opening point. Any statement that binds the *polynomial*
    // (a commitment root, a tower of column roots, etc.) must already be
    // in the transcript by this point — see the doc comment above.
    channel.observe_field_elems(eval_point);

    // Split eval_point:
    //   right = point[0..n-tau]  — the low variables (folded first, define columns)
    //   left  = point[n-tau..]   — the high variables (define row index)
    let tau = TAU.min(eval_point.len());
    let n = eval_point.len();
    let (right, left) = eval_point.split_at(n - tau);

    // -----------------------------------------------------------------------
    // Compute upper partial evaluations.
    // Row `i` is indexed by the high `tau` bits; each row has `2^(n-tau)` evals.
    // Evaluate each row at `right`.
    // -----------------------------------------------------------------------
    let n_rows = 1 << tau;
    let row_len = evals.len() / n_rows;
    let upper_partial_evals: Vec<Block128> = {
        use rayon::prelude::*;
        (0..n_rows)
            .into_par_iter()
            .map(|row| {
                let row_evals = &evals[row * row_len..(row + 1) * row_len];
                mle_evaluate(row_evals, right)
            })
            .collect()
    };

    // Compute the claimed evaluation = inner product of upper_partial_evals
    // and the eq indicator over the left (high) variables.
    let left_eq = noid_core::mle::eq::eq_ind_partial_eval(left);
    let eval: Block128 = upper_partial_evals
        .iter()
        .zip(left_eq.iter())
        .map(|(&v, &e)| v * e)
        .fold(Block128::ZERO, |a, b| a + b);
    channel.observe_field_elem(eval);

    // -----------------------------------------------------------------------
    // Draw tensor-batching challenge and batch rows.
    // -----------------------------------------------------------------------
    let tensor_batching_point = channel.get_random_points(tau);
    let batching_eq = noid_core::mle::eq::eq_ind_partial_eval(&tensor_batching_point);

    // Batched eval vector: batched[j] = Σ_i batching_eq[i] * row[i][j]
    // Parallelize over output columns; each column reads one value per row
    // independently. Deterministic: reduction order is fixed per column.
    let batched_evals: Vec<Block128> = {
        use rayon::prelude::*;
        if row_len >= 1024 {
            (0..row_len)
                .into_par_iter()
                .map(|j| {
                    let mut acc = Block128::ZERO;
                    for (row_idx, &coeff) in batching_eq.iter().enumerate() {
                        acc += coeff * evals[row_idx * row_len + j];
                    }
                    acc
                })
                .collect()
        } else {
            let mut out = vec![Block128::ZERO; row_len];
            for (row_idx, &coeff) in batching_eq.iter().enumerate() {
                for (j, val) in evals[row_idx * row_len..(row_idx + 1) * row_len]
                    .iter()
                    .enumerate()
                {
                    out[j] += coeff * *val;
                }
            }
            out
        }
    };

    // -----------------------------------------------------------------------
    // FRI commit phase — iteratively fold.
    //
    // The sumcheck operates on h(X) = g(X) * eq(X, right), so that:
    //   Σ_X h(X) = Σ_X g(X)*eq(X,right) = g(right) = <batching_eq, upper_partial_evals>
    //
    // The initial sumcheck claim is therefore the inner product of the
    // batching_eq weights and the upper partial evaluations — which the
    // verifier can reconstruct independently.
    // -----------------------------------------------------------------------
    let n_rounds = right.len();

    // Compute eq(X, right) for all X in {0,1}^(n-tau).
    let eq_right = noid_core::mle::eq::eq_ind_partial_eval(right);

    // Pointwise multiply: h[j] = batched[j] * eq_right[j].
    // Σ_j h[j] = <batching_eq, upper_partial_evals> (the sumcheck claim).
    let sumcheck_evals: Vec<Block128> = {
        use rayon::prelude::*;
        if batched_evals.len() >= 1024 {
            batched_evals
                .par_iter()
                .zip(eq_right.par_iter())
                .map(|(&g, &e)| g * e)
                .collect()
        } else {
            batched_evals
                .iter()
                .zip(eq_right.iter())
                .map(|(&g, &e)| g * e)
                .collect()
        }
    };

    // Initial sumcheck claim = Σ_j h[j] = <batching_eq, upper_partial_evals>.
    // This is what the verifier independently computes from upper_partial_evals.
    let sum_check_claim: Block128 = upper_partial_evals
        .iter()
        .zip(batching_eq.iter())
        .map(|(&u, &b)| u * b)
        .fold(Block128::ZERO, |a, x| a + x);

    let mut current_evals = sumcheck_evals;
    let mut sum_check_oracles: Vec<Univariate> = Vec::with_capacity(n_rounds);
    let mut fri_oracles: Vec<VectorCommitment> = Vec::with_capacity(n_rounds);
    let mut fri_trees: Vec<MerkleTree> = Vec::with_capacity(n_rounds);
    let mut fri_codes: Vec<Code> = Vec::with_capacity(n_rounds);
    let mut random_challenges: Vec<Block128> = Vec::with_capacity(n_rounds);

    // Encode the sumcheck polynomial h = g * eq(·, right) into an RS codeword.
    // The code and evals must stay in sync throughout folding.
    let mut current_code = Code::new_parallel(&current_evals, ntt);

    // `claim` tracks the running sumcheck claim across rounds.
    // Round 0 starts with the batched-polynomial sum over the hypercube.
    // Each subsequent round starts with oracle_prev(r_prev).
    let mut claim = sum_check_claim;

    for round in 0..n_rounds {
        // Build a degree-1 sumcheck oracle that satisfies:
        //   oracle(0) + oracle(1) == claim
        //
        // p(0) = Σ_{i < half} evals[i]   (sum over lower half of current evals)
        // p(1) = claim - p(0)              (forced to satisfy the check)
        //
        // This is correct because the MLE sumcheck oracle over a multilinear
        // polynomial evaluated at a random point r_{round} computes:
        //   p(X) = Σ_{(x_1,...,x_{n-1})} f(X, x_1,...,x_{n-1})
        // so p(0) = sum of lower half, and p(0)+p(1) must equal the claim.
        let oracle = compute_sumcheck_round_oracle(&current_evals, claim);
        sum_check_oracles.push(oracle.clone());

        // Commit the current code to a Merkle tree (parallel build).
        let leaf_hashes = compute_leaf_hashes(&current_code.encoding, hasher);
        let tree = MerkleTree::new_parallel(leaf_hashes, hasher);
        let vc = VectorCommitment {
            root: tree.get_root(),
            depth: tree.num_layers() - 1,
        };
        fri_oracles.push(vc.clone());
        fri_trees.push(tree);
        fri_codes.push(current_code.clone());

        // Transcript order (must match verifier exactly):
        //   1. Absorb sumcheck oracle coefficients.
        //   2. Absorb the FRI oracle commitment for this round.
        //   3. Squeeze the folding challenge.
        channel.observe_field_elems(&oracle.coeffs);
        channel.observe_vector_commitment(&vc);
        let r = channel.get_random_point();
        random_challenges.push(r);

        // Advance the claim to oracle(r) for the next round.
        claim = oracle.evaluate(r);

        // Fold the evaluation vector and the code.
        current_evals = fold_evals(&current_evals, r);
        current_code = current_code.fold_code(r, round, ntt);
    }

    // After n_rounds of folding, the codeword has length RATE (= 4).
    // Send the full final codeword so the verifier can check each
    // query's fold result against the correct position.
    let final_codeword = current_code.encoding.clone();
    channel.observe_field_elems(&final_codeword);

    // -----------------------------------------------------------------------
    // FRI query phase.
    // -----------------------------------------------------------------------
    // Query domain: same log-size as the initial (round-0) code domain.
    // fri_codes[r] and fri_trees[r] correspond to the code *at the start of*
    // round r (before folding).  The query-phase verifier opens fri_oracles[r]
    // and checks fold consistency between consecutive rounds.
    let log_domain = n_rounds + LOG_RATE;
    let query_indices = channel.gen_queries(log_domain);

    let mut fri_queried_symbols: Vec<Vec<(Block128, Block128)>> = Vec::with_capacity(n_rounds);
    let mut fri_merkle_paths: Vec<Vec<Vec<HashOutput>>> = Vec::with_capacity(n_rounds);

    for round in 0..n_rounds {
        let code = &fri_codes[round];
        let tree = &fri_trees[round];

        // Scale the query index into the current (smaller) domain.
        // Round 0 has domain size 2^(n_rounds+LOG_RATE); each subsequent round
        // halves the domain, so we right-shift by `round`.
        //
        // Each query is independent: symbol reads and Merkle-path lookups are
        // read-only against `code` and `tree`. Parallelizing across queries is
        // deterministic because the output vectors are produced by an ordered
        // `collect`, preserving `query_indices` order for the verifier.
        let (symbols_round, paths_round): (Vec<(Block128, Block128)>, Vec<Vec<HashOutput>>) =
            query_indices
                .par_iter()
                .map(|&qi| {
                    let scaled = qi >> round;
                    let pair_idx = scaled >> 1;
                    let s0 = code.idx(pair_idx * 2);
                    let s1 = code.idx(pair_idx * 2 + 1);
                    ((s0, s1), tree.get_merkle_path(pair_idx))
                })
                .unzip();
        fri_queried_symbols.push(symbols_round);
        fri_merkle_paths.push(paths_round);
    }

    EvalProof {
        upper_partial_evals,
        sum_check_oracles,
        fri_oracles,
        fri_queried_symbols,
        fri_merkle_paths,
        final_codeword,
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Public wrapper for testing.
#[cfg(test)]
pub fn fold_evals_pub(evals: &[Block128], r: Block128) -> Vec<Block128> {
    fold_evals(evals, r)
}

/// Compute a degree-1 sumcheck oracle satisfying `p(0) + p(1) == claim`.
///
/// In a multilinear sumcheck over GF(2^128):
///   p(0) = Σ_{i < half} evals[i]   (sum of the "X=0" half)
///   p(1) = claim XOR p(0)           (forced: p(0)+p(1) must equal claim)
///
/// The claim flows from round to round as `claim_{r+1} = p_r(challenge_r)`.
/// Encoding as coefficients: p(X) = p0 + (p0 XOR p1)*X  (linear, char 2).
fn compute_sumcheck_round_oracle(evals: &[Block128], claim: Block128) -> Univariate {
    let half = evals.len() / 2;

    // p(0) = sum of the lower half (evals with leading variable = 0).
    let p0 = evals[..half].iter().fold(Block128::ZERO, |acc, &v| acc + v);

    // p(1) is forced so that p(0)+p(1) == claim  (in GF(2), + == XOR).
    let p1 = claim + p0;

    // Degree-1 polynomial: p(X) = p0 + (p0 XOR p1)*X.
    // coeffs[0] = p(0) = p0
    // coeffs[1] = p(1) - p(0) = p1 XOR p0  (char 2)
    let c0 = p0;
    let c1 = p0 + p1; // == claim (in char 2)

    Univariate::new(vec![c0, c1])
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::native::compression::Poseidon2bSponge;
    use rand::Rng;

    fn make_random_evals(log_len: usize) -> Vec<Block128> {
        let mut rng = rand::thread_rng();
        (0..1 << log_len)
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect()
    }
    #[test]
    fn test_univariate_evaluate() {
        // p(X) = 3 + 2*X
        let p = Univariate::new(vec![Block128::from(3u8), Block128::from(2u8)]);
        assert_eq!(p.evaluate(Block128::ZERO), Block128::from(3u8));
        assert_eq!(
            p.evaluate(Block128::ONE),
            Block128::from(3u8) + Block128::from(2u8)
        );
    }

    #[test]
    fn test_commit_smoke() {
        let ntt = AdditiveNTT::<Block128>::new(4 + crate::code::LOG_RATE);
        let hasher = Poseidon2bSponge::new();
        let evals = make_random_evals(4);
        let (commitment, _tree, code) = commit(&evals, &ntt, &hasher);
        assert_eq!(code.encoding.len(), evals.len() * crate::code::RATE);
        assert!(commitment.log_len == 4);
    }

    #[test]
    fn test_prove_and_verify() {
        use crate::verifier::verify;

        let log_len = 4usize;
        let ntt = AdditiveNTT::<Block128>::new(log_len + LOG_RATE);
        let hasher = Poseidon2bSponge::new();
        let evals = make_random_evals(log_len);

        // Commit
        let (commitment, _tree, _code) = commit(&evals, &ntt, &hasher);

        // Build an eval_point of length log_len
        let mut rng = rand::thread_rng();
        let eval_point: Vec<Block128> = (0..log_len)
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect();

        // Prove — caller binds the commitment into the transcript
        // before calling `prove` (per-column reuse contract).
        let mut prover_channel = Channel::new();
        prover_channel.observe_fri_commitment(&commitment);
        let proof = prove(&evals, &eval_point, &ntt, &mut prover_channel, &hasher);

        // The claimed evaluation
        let claimed_eval = mle_evaluate(&evals, &eval_point);

        // Verify
        let mut verifier_channel = Channel::new();
        verifier_channel.observe_fri_commitment(&commitment);
        let result = verify(
            &eval_point,
            claimed_eval,
            proof,
            &ntt,
            &mut verifier_channel,
            &hasher,
        );
        assert!(result.is_ok(), "verification failed: {:?}", result);
    }

    /// Prove and verify with log_len = TAU+2 (2 FRI folding rounds).
    /// This exercises the sumcheck transcript ordering fix.
    #[test]
    fn test_prove_and_verify_with_folding_rounds() {
        use crate::channel::TAU;
        use crate::verifier::verify;

        let log_len = TAU + 2; // 9 → n_rounds = 2
        let ntt = AdditiveNTT::<Block128>::new(log_len + LOG_RATE);
        let hasher = Poseidon2bSponge::new();
        let evals = make_random_evals(log_len);

        let (commitment, _tree, _code) = commit(&evals, &ntt, &hasher);

        let mut rng = rand::thread_rng();
        let eval_point: Vec<Block128> = (0..log_len)
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect();

        let mut prover_channel = Channel::new();
        prover_channel.observe_fri_commitment(&commitment);
        let proof = prove(&evals, &eval_point, &ntt, &mut prover_channel, &hasher);

        let claimed_eval = mle_evaluate(&evals, &eval_point);

        let mut verifier_channel = Channel::new();
        verifier_channel.observe_fri_commitment(&commitment);
        let result = verify(
            &eval_point,
            claimed_eval,
            proof,
            &ntt,
            &mut verifier_channel,
            &hasher,
        );

        assert!(
            result.is_ok(),
            "prove/verify with {} folding rounds failed: {:?}",
            log_len - TAU,
            result
        );
    }

    /// Prove and verify with log_len = TAU+4 (4 FRI folding rounds).
    #[test]
    fn test_prove_and_verify_many_folding_rounds() {
        use crate::channel::TAU;
        use crate::verifier::verify;

        let log_len = TAU + 4; // 11 → n_rounds = 4
        let ntt = AdditiveNTT::<Block128>::new(log_len + LOG_RATE);
        let hasher = Poseidon2bSponge::new();
        let evals = make_random_evals(log_len);

        let (commitment, _tree, _code) = commit(&evals, &ntt, &hasher);

        let mut rng = rand::thread_rng();
        let eval_point: Vec<Block128> = (0..log_len)
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect();

        let mut prover_channel = Channel::new();
        prover_channel.observe_fri_commitment(&commitment);
        let proof = prove(&evals, &eval_point, &ntt, &mut prover_channel, &hasher);

        let claimed_eval = mle_evaluate(&evals, &eval_point);

        let mut verifier_channel = Channel::new();
        verifier_channel.observe_fri_commitment(&commitment);
        let result = verify(
            &eval_point,
            claimed_eval,
            proof,
            &ntt,
            &mut verifier_channel,
            &hasher,
        );

        assert!(
            result.is_ok(),
            "prove/verify with {} folding rounds failed: {:?}",
            log_len - TAU,
            result
        );
    }

    /// Determinism: the same seed must produce byte-identical proofs
    /// across different rayon thread-pool sizes. This guards PoW (CRYPTO.md §7.2)
    /// — the Fiat-Shamir transcript must be deterministic given the seed, so
    /// the final proof-transcript hash is a valid grinding target.
    #[test]
    fn test_prove_determinism_across_thread_counts() {
        use crate::channel::TAU;
        use rand::rngs::StdRng;
        use rand::SeedableRng;

        let log_len = TAU + 3;
        let ntt = AdditiveNTT::<Block128>::new(log_len + LOG_RATE);
        let hasher = Poseidon2bSponge::new();

        let mut rng = StdRng::seed_from_u64(0xDEAD_C0DE_D00D_F00D);
        let evals: Vec<Block128> = (0..1 << log_len)
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect();
        let eval_point: Vec<Block128> = (0..log_len)
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect();

        let run = |threads: usize| -> EvalProof {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap();
            pool.install(|| {
                let (commitment, _t, _c) = commit(&evals, &ntt, &hasher);
                let mut ch = Channel::new();
                ch.observe_fri_commitment(&commitment);
                prove(&evals, &eval_point, &ntt, &mut ch, &hasher)
            })
        };

        let p1 = run(1);
        let p4 = run(4);
        let p8 = run(8);

        // Compare on the transcript-visible fields; byte-identical means the
        // Fiat-Shamir transcript evolved identically across thread counts.
        assert_eq!(p1.upper_partial_evals, p4.upper_partial_evals);
        assert_eq!(p1.upper_partial_evals, p8.upper_partial_evals);
        for i in 0..p1.sum_check_oracles.len() {
            assert_eq!(
                p1.sum_check_oracles[i].coeffs,
                p4.sum_check_oracles[i].coeffs
            );
            assert_eq!(
                p1.sum_check_oracles[i].coeffs,
                p8.sum_check_oracles[i].coeffs
            );
        }
        for i in 0..p1.fri_oracles.len() {
            assert_eq!(p1.fri_oracles[i].root, p4.fri_oracles[i].root);
            assert_eq!(p1.fri_oracles[i].root, p8.fri_oracles[i].root);
        }
        assert_eq!(p1.final_codeword, p4.final_codeword);
        assert_eq!(p1.final_codeword, p8.final_codeword);
    }

    /// Minimal 1-fold debug test: TAU+1 rounds, seeded RNG.
    #[test]
    fn test_fold_1_round_minimal() {
        use crate::channel::TAU;
        use crate::verifier::verify;

        let log_len = TAU + 1; // 8 → 1 fold round, row_len=1
        let ntt = AdditiveNTT::<Block128>::new(log_len + LOG_RATE);
        let hasher = Poseidon2bSponge::new();

        // Use a known simple polynomial: constant f = 5.
        let n = 1usize << log_len;
        let evals: Vec<Block128> = (0..n).map(|i| Block128::from(i as u128 + 1)).collect();

        let (commitment, _tree, _code) = commit(&evals, &ntt, &hasher);
        let eval_point: Vec<Block128> = (0..log_len)
            .map(|i| Block128::from(i as u128 + 2))
            .collect();

        let claimed_eval = mle_evaluate(&evals, &eval_point);
        let mut prover_channel = Channel::new();
        prover_channel.observe_fri_commitment(&commitment);
        let proof = prove(&evals, &eval_point, &ntt, &mut prover_channel, &hasher);

        eprintln!("final_codeword={:?}", proof.final_codeword);
        eprintln!("n_rounds={}", proof.fri_oracles.len());

        let mut verifier_channel = Channel::new();
        verifier_channel.observe_fri_commitment(&commitment);
        let result = verify(
            &eval_point,
            claimed_eval,
            proof,
            &ntt,
            &mut verifier_channel,
            &hasher,
        );
        assert!(result.is_ok(), "1-fold minimal failed: {:?}", result);
    }
}
