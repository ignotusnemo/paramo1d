// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! The batched Merkle path killshot in the trace.
//!
//! Trace twins of `noid_gkr::merkle_batch_killshot`:
//! [`verify_batched_merkle_killshot_trace`] ← `verify_batched_merkle_killshot`
//! and [`discharge_batched_merkle_trace`] ←
//! `discharge_batched_merkle_reductions_native`. One module serves the tx-root
//! component (`MerkleCircuit::build()`, TAG_COMPRESS) and the exact-state
//! path batches (`TAG_EXSTNOD`).
//!
//! ## Shape note
//!
//! `active_depth` is a TRACE-STRUCTURE constant: it is a class parameter
//! (padded tx-tree depth or state-trie `log_slots`), not block
//! content. Path DIRECTIONS are block content (slot keys, tx indices) and
//! enter as witness booleans: the absorbed packed-directions lane is an
//! affine combination of the bit wires, the chain claims carry the union
//! of both branches' terms with bit-scaled coefficients (mirroring the
//! native union form), and the discharge replays each level through a
//! left/right mux — so the R1CS matrix depends only on the shape class.

use noid_core::{Block128, TowerField};
use noid_gkr::merkle_batch_killshot::{
    BatchedMerkleProofKillShot, MERKLE_CHAIN_LINEAR_RELATION_TAG, MERKLE_PIN_LANES,
};
use noid_gkr::merkle_circuit::{MerkleCircuit, MerklePathInputs, MAX_MERKLE_DEPTH};
use noid_poseidon2b::native::domain::capacity_iv;
use noid_poseidon2b::native::permutation::{MDS_FULL, N_ROUNDS, STATE_SIZE};

use super::batch_eval::{
    verify_linear_eval_prebound_trace, LinearEvalClaimTrace, LinearEvalProofTrace,
    LinearEvalTermTrace, MultiBatchEvalProofTrace,
};
use super::block_spine::{
    close_spine_family_batch, spine_point_index, verify_block_spine_shift_trace,
    verify_block_spine_unified_trace, BlockSpineShiftProofTrace, BlockSpineUnifiedProofTrace,
    ColumnAccumulator,
};
use super::{
    alloc_block, const_block, flat_of, mul, pin_zero, BatchEvalReductionTrace, FieldR1csBuilder,
    LinExpr, RawChannelTrace, F128,
};

/// Trace twin of `MerklePathInputs`. Digest lanes are witness expressions;
/// `active_depth` is trace structure (module docs); `direction_bits` are
/// witness booleans. The canonical zero padding beyond `active_depth`
/// (native `inputs_are_canonical`) is structural: those lanes are
/// constants, and the packed-directions lane sums only the active bits.
pub struct MerklePathInputsTrace {
    pub leaf: [LinExpr; 2],
    pub siblings: Vec<[LinExpr; 2]>,
    pub direction_bits: Vec<LinExpr>,
    pub expected_root: [LinExpr; 2],
    pub active_depth: usize,
}

impl MerklePathInputsTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &MerklePathInputs) -> Self {
        assert!(
            native.active_depth > 0 && native.active_depth <= MAX_MERKLE_DEPTH,
            "path off the trace shape"
        );
        // Canonicity is structural: beyond active_depth the wires do not
        // exist — the padding lanes are literal zero constants.
        for level in native.active_depth..MAX_MERKLE_DEPTH {
            assert_eq!(
                native.siblings[level],
                [Block128::ZERO; 2],
                "non-canonical sibling padding"
            );
            assert!(!native.directions[level], "non-canonical direction padding");
        }
        Self {
            leaf: std::array::from_fn(|i| alloc_block(b, native.leaf[i])),
            siblings: (0..native.active_depth)
                .map(|l| std::array::from_fn(|i| alloc_block(b, native.siblings[l][i])))
                .collect(),
            direction_bits: native.directions[..native.active_depth]
                .iter()
                .map(|&d| LinExpr::from_wire(b.alloc_bool(d)))
                .collect(),
            expected_root: std::array::from_fn(|i| alloc_block(b, native.expected_root[i])),
            active_depth: native.active_depth,
        }
    }

    fn live_slots(&self) -> usize {
        MerkleCircuit::live_slots(self.active_depth)
    }
}

/// Trace twin of `BatchedMerkleProofKillShot`.
pub struct BatchedMerkleProofTrace {
    pub main: BlockSpineUnifiedProofTrace,
    pub shift: BlockSpineShiftProofTrace,
    pub chain: LinearEvalProofTrace,
    pub batch: MultiBatchEvalProofTrace,
    pub n_paths: usize,
    pub num_vars: usize,
    pub live_slots: usize,
}

impl BatchedMerkleProofTrace {
    pub fn alloc(
        b: &mut FieldR1csBuilder,
        native: &BatchedMerkleProofKillShot,
        inputs: &[MerklePathInputsTrace],
    ) -> Self {
        let live_slots: usize = inputs.iter().map(MerklePathInputsTrace::live_slots).sum();
        let num_vars = noid_gkr::block_spine::num_vars_for(live_slots);
        assert_eq!(native.n_paths, inputs.len(), "proof off the trace shape");
        assert_eq!(native.live_slots, live_slots, "proof off the trace shape");
        assert_eq!(native.num_vars, num_vars, "proof off the trace shape");
        Self {
            main: BlockSpineUnifiedProofTrace::alloc(b, &native.kill_shot.main, num_vars),
            shift: BlockSpineShiftProofTrace::alloc(b, &native.kill_shot.shift, num_vars),
            chain: LinearEvalProofTrace::alloc(b, &native.chain, num_vars),
            batch: MultiBatchEvalProofTrace::alloc(b, &native.batch, num_vars, 3),
            n_paths: inputs.len(),
            num_vars,
            live_slots,
        }
    }
}

/// Trace twin of `absorb_public_batch` (Merkle).
fn absorb_public_batch_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    circuit: &MerkleCircuit,
    inputs: &[MerklePathInputsTrace],
) {
    ch.absorb_const_tower(b, inputs.len() as u128);
    ch.absorb_const_tower(b, circuit.node_tag.as_u64() as u128);
    for input in inputs {
        // absorb_public_path: depth-first prefix, active levels only, all
        // direction bits packed into one lane. Depth is trace structure
        // (constant lane); the directions lane is the affine combination
        // Σ bit_level·2^level of the witness bits (tower-basis powers —
        // native packs an integer), which binds the bits to the killshot
        // transcript.
        ch.absorb_const_tower(b, input.active_depth as u128);
        ch.absorb(b, &input.expected_root[0]);
        ch.absorb(b, &input.expected_root[1]);
        ch.absorb(b, &input.leaf[0]);
        ch.absorb(b, &input.leaf[1]);
        let mut directions = LinExpr::zero();
        for level in 0..input.active_depth {
            ch.absorb(b, &input.siblings[level][0]);
            ch.absorb(b, &input.siblings[level][1]);
            directions = directions
                .add(&input.direction_bits[level].scale(flat_of(Block128::from(1u128 << level))));
        }
        ch.absorb(b, &directions);
    }
}

/// Trace twin of `append_path_chain_claims_at_offset` — same claim and term
/// order as the native union form: both branches' terms are present, with
/// coefficients and values scaled by the direction bit `d` / `1 + d`
/// (char 2), so the claim layout depends only on the depth.
fn append_path_chain_claims_trace(
    b: &mut FieldR1csBuilder,
    circuit: &MerkleCircuit,
    input: &MerklePathInputsTrace,
    slot_offset: usize,
    num_vars: usize,
    claims: &mut Vec<LinearEvalClaimTrace>,
) {
    let mds = |row: usize, col: usize| Block128::from(MDS_FULL[row][col]);
    let depth = input.active_depth;
    let [iv_hi, iv_lo] = capacity_iv(circuit.node_tag);
    let iv_const = |lane: usize| flat_of(mds(lane, 2) * iv_hi + mds(lane, 3) * iv_lo);
    let mds_pair = |lane: usize, pair: &[LinExpr; 2]| {
        pair[0]
            .scale(flat_of(mds(lane, 0)))
            .add(&pair[1].scale(flat_of(mds(lane, 1))))
    };
    let state_term = |slot: usize, round: usize, lane: usize, coeff: LinExpr| LinearEvalTermTrace {
        index: spine_point_index(num_vars, slot, round, lane),
        coeff,
    };
    let const_coeff = |v: Block128| LinExpr::constant(flat_of(v));

    for level in 0..depth {
        let perm_a_slot = slot_offset + level * 2;
        let perm_b_slot = perm_a_slot + 1;
        let d = &input.direction_bits[level];
        let not_d = d.add_const(F128::ONE);

        for lane in 0..STATE_SIZE {
            let mut terms = vec![state_term(perm_a_slot, 0, lane, const_coeff(Block128::ONE))];
            let mut value =
                mul(b, d, &mds_pair(lane, &input.siblings[level])).add_const(iv_const(lane));
            if level == 0 {
                value = value.add(&mul(b, &not_d, &mds_pair(lane, &input.leaf)));
            } else {
                let prev_perm_b = perm_a_slot - 1;
                terms.push(state_term(
                    prev_perm_b,
                    N_ROUNDS,
                    0,
                    not_d.scale(flat_of(mds(lane, 0))),
                ));
                terms.push(state_term(
                    prev_perm_b,
                    N_ROUNDS,
                    1,
                    not_d.scale(flat_of(mds(lane, 1))),
                ));
            }
            claims.push(LinearEvalClaimTrace { terms, value });
        }

        for lane in 0..STATE_SIZE {
            let mut terms = vec![state_term(perm_b_slot, 0, lane, const_coeff(Block128::ONE))];
            for src_lane in 0..STATE_SIZE {
                terms.push(state_term(
                    perm_a_slot,
                    N_ROUNDS,
                    src_lane,
                    const_coeff(mds(lane, src_lane)),
                ));
            }
            let mut value = mul(b, &not_d, &mds_pair(lane, &input.siblings[level]));
            if level == 0 {
                value = value.add(&mul(b, d, &mds_pair(lane, &input.leaf)));
            } else {
                let prev_perm_b = perm_a_slot - 1;
                terms.push(state_term(
                    prev_perm_b,
                    N_ROUNDS,
                    0,
                    d.scale(flat_of(mds(lane, 0))),
                ));
                terms.push(state_term(
                    prev_perm_b,
                    N_ROUNDS,
                    1,
                    d.scale(flat_of(mds(lane, 1))),
                ));
            }
            claims.push(LinearEvalClaimTrace { terms, value });
        }
    }

    let last_perm_b = slot_offset + (depth - 1) * 2 + 1;
    for lane in 0..MERKLE_PIN_LANES {
        claims.push(LinearEvalClaimTrace {
            terms: vec![state_term(
                last_perm_b,
                N_ROUNDS,
                lane,
                const_coeff(Block128::ONE),
            )],
            value: input.expected_root[lane].clone(),
        });
    }
}

/// Trace twin of `verify_batched_merkle_killshot`.
pub fn verify_batched_merkle_killshot_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    circuit: &MerkleCircuit,
    proof: &BatchedMerkleProofTrace,
    inputs: &[MerklePathInputsTrace],
) -> [BatchEvalReductionTrace; 3] {
    assert!(!inputs.is_empty());
    assert_eq!(proof.n_paths, inputs.len());
    let live_slots: usize = inputs.iter().map(MerklePathInputsTrace::live_slots).sum();
    assert_eq!(proof.live_slots, live_slots);
    assert_eq!(
        proof.num_vars,
        noid_gkr::block_spine::num_vars_for(proof.live_slots)
    );

    absorb_public_batch_trace(b, ch, circuit, inputs);

    let main_red =
        verify_block_spine_unified_trace(b, ch, &proof.main, proof.num_vars, proof.live_slots);
    let shift_red = verify_block_spine_shift_trace(b, ch, &proof.shift, &main_red, proof.num_vars);

    let mut chain_claims = Vec::new();
    let mut slot_offset = 0usize;
    for input in inputs {
        append_path_chain_claims_trace(
            b,
            circuit,
            input,
            slot_offset,
            proof.num_vars,
            &mut chain_claims,
        );
        slot_offset += input.live_slots();
    }
    let chain_red = verify_linear_eval_prebound_trace(
        b,
        ch,
        &proof.chain,
        &chain_claims,
        proof.num_vars,
        MERKLE_CHAIN_LINEAR_RELATION_TAG,
    );

    close_spine_family_batch(
        b,
        ch,
        &main_red,
        &shift_red,
        &chain_red,
        &proof.batch,
        proof.num_vars,
    )
}

/// Trace twin of `discharge_batched_merkle_reductions_native`: replay the
/// live compression chains (`merkle_oracle::evaluate_merkle`'s live prefix)
/// through the accumulator and pin the derived roots and column values.
pub fn discharge_batched_merkle_trace(
    b: &mut FieldR1csBuilder,
    circuit: &MerkleCircuit,
    inputs: &[MerklePathInputsTrace],
    reductions: &[BatchEvalReductionTrace; 3],
) {
    assert!(!inputs.is_empty());
    let [iv_hi, iv_lo] = capacity_iv(circuit.node_tag);
    let live_slots: usize = inputs.iter().map(MerklePathInputsTrace::live_slots).sum();
    let mut acc = ColumnAccumulator::new(b, &reductions[0].point, live_slots);

    for input in inputs {
        // merkle_oracle::build_state_in for the live chain: per level PermA
        // absorbs the left digest over the IV, PermB XOR-absorbs the right
        // digest into PermA's output rate.
        let mut current = [input.leaf[0].clone(), input.leaf[1].clone()];
        for level in 0..input.active_depth {
            let sibling = &input.siblings[level];
            // Left/right mux on the direction bit (d = 1 → current digest
            // is the right child): one shared product per lane.
            let d = &input.direction_bits[level];
            let mut left = [LinExpr::zero(), LinExpr::zero()];
            let mut right = [LinExpr::zero(), LinExpr::zero()];
            for lane in 0..2 {
                let t = mul(b, d, &current[lane].add(&sibling[lane]));
                left[lane] = current[lane].add(&t);
                right[lane] = sibling[lane].add(&t);
            }
            let perm_a_in: [LinExpr; STATE_SIZE] = [
                left[0].clone(),
                left[1].clone(),
                const_block(iv_hi),
                const_block(iv_lo),
            ];
            let a_out = acc.push_slot(b, &perm_a_in);
            let perm_b_in: [LinExpr; STATE_SIZE] = [
                a_out[0].add(&right[0]),
                a_out[1].add(&right[1]),
                a_out[2].clone(),
                a_out[3].clone(),
            ];
            let b_out = acc.push_slot(b, &perm_b_in);
            current = [b_out[0].clone(), b_out[1].clone()];
        }
        // `witness.derived_root != input.expected_root → false` → pins.
        pin_zero(b, &current[0].add(&input.expected_root[0]));
        pin_zero(b, &current[1].add(&input.expected_root[1]));
    }

    let (state_value, sin_value, sout_value) = acc.finish();
    pin_zero(b, &state_value.add(&reductions[0].value));
    pin_zero(b, &sin_value.add(&reductions[1].value));
    pin_zero(b, &sout_value.add(&reductions[2].value));
}

/// Full [K]+[D] Merkle slot (component twin of `verify_tx_root_component`
/// and of the exact-state path legs — the caller picks the circuit tag and
/// supplies the channel, since exact-state runs several killshots per slot).
pub fn build_batched_merkle_slot(
    b: &mut FieldR1csBuilder,
    circuit: &MerkleCircuit,
    proof: &BatchedMerkleProofKillShot,
    inputs: &[MerklePathInputs],
) -> Vec<MerklePathInputsTrace> {
    let inputs_t: Vec<MerklePathInputsTrace> = inputs
        .iter()
        .map(|i| MerklePathInputsTrace::alloc(b, i))
        .collect();
    let proof_t = BatchedMerkleProofTrace::alloc(b, proof, &inputs_t);
    let mut ch = RawChannelTrace::new();
    let reds = verify_batched_merkle_killshot_trace(b, &mut ch, circuit, &proof_t, &inputs_t);
    discharge_batched_merkle_trace(b, circuit, &inputs_t, &reds);
    inputs_t
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_gkr::merkle_batch_killshot::{
        discharge_batched_merkle_reductions_native, prove_batched_merkle_killshot,
        verify_batched_merkle_killshot,
    };
    use noid_gkr::merkle_oracle::compute_merkle_root_with_directions;
    use noid_poseidon2b::channel::Poseidon2bChannel;

    fn fixture(seed: u64, depth: usize, dir_mask: u32) -> MerklePathInputs {
        let mut s = seed as u128 | 1;
        let mut rnd = || {
            s = s.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(13);
            Block128::from(s)
        };
        let leaf = [rnd(), rnd()];
        let mut siblings = [[Block128::ZERO; 2]; MAX_MERKLE_DEPTH];
        let mut directions = [false; MAX_MERKLE_DEPTH];
        for level in 0..depth {
            siblings[level] = [rnd(), rnd()];
            directions[level] = (dir_mask >> level) & 1 == 1;
        }
        let circuit = MerkleCircuit::build();
        let expected_root = compute_merkle_root_with_directions(
            &circuit,
            leaf,
            &siblings[..depth],
            &directions,
            depth,
        );
        MerklePathInputs {
            leaf,
            siblings,
            directions,
            expected_root,
            active_depth: depth,
        }
    }

    struct Fixture {
        proof: BatchedMerkleProofKillShot,
        inputs: Vec<MerklePathInputs>,
    }

    fn make_fixture() -> Fixture {
        let circuit = MerkleCircuit::build();
        // Varied depths AND directions (exercises every claim branch).
        let inputs = vec![
            fixture(1, 3, 0b101),
            fixture(2, 1, 0b1),
            fixture(3, 5, 0b01010),
        ];
        let mut ch = Poseidon2bChannel::new();
        let (proof, _) = prove_batched_merkle_killshot(&circuit, &inputs, &mut ch);
        Fixture { proof, inputs }
    }

    fn native_accepts(f: &Fixture) -> bool {
        let circuit = MerkleCircuit::build();
        let mut ch = Poseidon2bChannel::new();
        verify_batched_merkle_killshot(&circuit, &f.proof, &f.inputs, &mut ch)
            .map(|red| discharge_batched_merkle_reductions_native(&circuit, &f.inputs, &red))
            .unwrap_or(false)
    }

    fn trace_accepts(f: &Fixture) -> bool {
        let circuit = MerkleCircuit::build();
        let mut b = FieldR1csBuilder::new();
        let _ = build_batched_merkle_slot(&mut b, &circuit, &f.proof, &f.inputs);
        let (r1cs, z) = b.build();
        r1cs.satisfies(&z)
    }

    /// Fixed-matrix class gate: two batches of the SAME class (same depth
    /// sequence) but different content — leaves, siblings, keys and
    /// DIRECTIONS — must build byte-identical R1CS matrices. This is the
    /// recursion's protocol-constant-matrix requirement; a failure means
    /// block content leaked back into trace structure.
    #[test]
    fn fixed_matrix_within_class() {
        let digest = |seeds: [u64; 3], dirs: [u32; 3]| {
            let circuit = MerkleCircuit::build();
            let inputs = vec![
                fixture(seeds[0], 3, dirs[0]),
                fixture(seeds[1], 1, dirs[1]),
                fixture(seeds[2], 5, dirs[2]),
            ];
            let mut ch = Poseidon2bChannel::new();
            let (proof, _) = prove_batched_merkle_killshot(&circuit, &inputs, &mut ch);
            let mut b = FieldR1csBuilder::new();
            let _ = build_batched_merkle_slot(&mut b, &circuit, &proof, &inputs);
            let (r1cs, _z) = b.build();
            r1cs.statement_digest()
        };
        assert_eq!(
            digest([1, 2, 3], [0b101, 0b1, 0b01010]),
            digest([7, 8, 9], [0b010, 0b0, 0b10101]),
            "Merkle slot matrix depends on block content"
        );
    }

    #[test]
    fn batched_merkle_trace_positive() {
        let f = make_fixture();
        assert!(native_accepts(&f), "native fixture broken");
        let circuit = MerkleCircuit::build();
        let mut b = FieldR1csBuilder::new();
        let _ = build_batched_merkle_slot(&mut b, &circuit, &f.proof, &f.inputs);
        let (r1cs, z) = b.build();
        assert!(r1cs.satisfies(&z), "honest merkle trace unsatisfiable");
        eprintln!(
            "batched merkle slot (3 paths, depths 3/1/5): {} useful rows (k_log = {})",
            r1cs.useful_rows, r1cs.k_log
        );
    }

    fn visit_proof_fields(p: &mut BatchedMerkleProofKillShot, f: &mut dyn FnMut(&mut Block128)) {
        for rp in &mut p.kill_shot.main.round_polys {
            for c in &mut rp.coeffs_no_linear {
                f(c);
            }
        }
        f(&mut p.kill_shot.main.s_in_dec_at_r);
        f(&mut p.kill_shot.main.s_out_dec_at_r);
        f(&mut p.kill_shot.main.state_dec_at_r);
        f(&mut p.kill_shot.main.state_at_r);
        for v in &mut p.kill_shot.main.s_out_lane_dec_at_r {
            f(v);
        }
        for v in &mut p.kill_shot.main.state_lane_dec_at_r {
            f(v);
        }
        for rp in &mut p.kill_shot.shift.round_polys {
            for c in &mut rp.coeffs_no_linear {
                f(c);
            }
        }
        f(&mut p.kill_shot.shift.s_in_at_r2);
        f(&mut p.kill_shot.shift.s_out_at_r2);
        f(&mut p.kill_shot.shift.state_at_r2);
        for r in &mut p.chain.rounds {
            for e in &mut r.evals_at_1_2 {
                f(e);
            }
        }
        f(&mut p.chain.b_final);
        for r in &mut p.batch.rounds {
            for e in &mut r.evals_at_1_2 {
                f(e);
            }
        }
        for v in &mut p.batch.b_finals {
            f(v);
        }
    }

    /// Replay-completeness auto-mutator (proof side). 0 surviving mutants.
    #[test]
    fn batched_merkle_proof_mutator_kills_all() {
        let f = make_fixture();
        let mut n_fields = 0usize;
        {
            let mut c = f.proof.clone();
            visit_proof_fields(&mut c, &mut |_| n_fields += 1);
        }
        let stride: usize = std::env::var("NOID_TRACE_MUTATE_STRIDE")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(1);
        let mut survivors = Vec::new();
        for target in (0..n_fields).step_by(stride) {
            let mut bad_proof = f.proof.clone();
            let mut i = 0usize;
            visit_proof_fields(&mut bad_proof, &mut |v| {
                if i == target {
                    *v += Block128::ONE;
                }
                i += 1;
            });
            let bad = Fixture {
                proof: bad_proof,
                inputs: f.inputs.clone(),
            };
            assert!(
                !native_accepts(&bad),
                "native accepted proof mutant {target}"
            );
            if trace_accepts(&bad) {
                survivors.push(target);
            }
        }
        assert!(
            survivors.is_empty(),
            "surviving merkle proof mutants: {survivors:?} of {n_fields}"
        );
    }

    /// Statement/discharge mutator: every live digest lane of every path.
    #[test]
    fn batched_merkle_statement_mutator_kills_all() {
        let f = make_fixture();
        let mut survivors = Vec::new();
        let mut target_id = 0usize;
        for path in 0..f.inputs.len() {
            let depth = f.inputs[path].active_depth;
            for lane_slot in 0..(2 + 2 + depth * 2) {
                let mut bad_inputs = f.inputs.clone();
                let p = &mut bad_inputs[path];
                match lane_slot {
                    0 | 1 => p.leaf[lane_slot] += Block128::ONE,
                    2 | 3 => p.expected_root[lane_slot - 2] += Block128::ONE,
                    k => {
                        let k = k - 4;
                        p.siblings[k / 2][k % 2] += Block128::ONE;
                    }
                }
                let bad = Fixture {
                    proof: f.proof.clone(),
                    inputs: bad_inputs,
                };
                assert!(
                    !native_accepts(&bad),
                    "native accepted statement mutant {target_id}"
                );
                if trace_accepts(&bad) {
                    survivors.push(target_id);
                }
                target_id += 1;
            }
        }
        assert!(
            survivors.is_empty(),
            "surviving merkle statement mutants: {survivors:?}"
        );
    }

    /// Cross-test "trace ⇔ native" on randomized honest/mutated cases.
    #[test]
    fn batched_merkle_native_trace_equivalence() {
        let cases: usize = std::env::var("NOID_TRACE_CROSS_CASES")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(100);
        let mut seed = 0x3E5C_1E77u128;
        let mut next = |m: u128| {
            seed = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
            (seed >> 16) % m
        };
        let f = make_fixture();
        let mut n_fields = 0usize;
        {
            let mut c = f.proof.clone();
            visit_proof_fields(&mut c, &mut |_| n_fields += 1);
        }
        for case in 0..cases {
            let case_f = if case % 2 == 0 {
                Fixture {
                    proof: f.proof.clone(),
                    inputs: f.inputs.clone(),
                }
            } else {
                let target = next(n_fields as u128) as usize;
                let mut bad_proof = f.proof.clone();
                let mut i = 0usize;
                visit_proof_fields(&mut bad_proof, &mut |v| {
                    if i == target {
                        *v += Block128::ONE;
                    }
                    i += 1;
                });
                Fixture {
                    proof: bad_proof,
                    inputs: f.inputs.clone(),
                }
            };
            assert_eq!(
                native_accepts(&case_f),
                trace_accepts(&case_f),
                "native/trace divergence on case {case}"
            );
        }
    }
}
