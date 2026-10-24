// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! The tx-body spine killshots in the trace.
//!
//! Trace twins of:
//! - [`verify_block_spine_killshot_trace`] ←
//!   `noid_gkr::block_spine::verify_block_spine_killshot` (the final
//!   31-slot Tx8x2 tree) + `discharge_block_spine_reductions_native`.
//!
//! The discharge walks the native `SpineCircuit`
//! descriptor tables (build-time structure) and rebuilds every slot's
//! `state_in` as an AFFINE combination of the leaf payload wires, the IV
//! constants and previous slots' permutation outputs (the oracle
//! `build_state_in` / `chain_absorb_pair` relations are all XOR chains) —
//! the permutation replay itself lives in [`ColumnAccumulator::push_slot`].
//! The wrap digests are bound to the `tx_body_hashes` wires by the killshot's
//! own `tx_hash_pins` linear relation, exactly as native.

use noid_core::Block128;
use noid_gkr::block_spine::{num_vars_for, BlockSpineProof, BLOCK_SPINE_TX_HASH_PIN_TAG};
use noid_gkr::spine_sumcheck::N_SPINE_SLOTS;
use noid_gkr::tx_body_layout::InstanceRole;
use noid_gkr::{SpineCircuit, SpineInputs};
use noid_poseidon2b::native::permutation::{N_ROUNDS, STATE_SIZE};

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
    alloc_block, const_block, BatchEvalReductionTrace, FieldR1csBuilder, LinExpr, RawChannelTrace,
    F128,
};

// ---------------------------------------------------------------------------
// Statement wire types
// ---------------------------------------------------------------------------

/// Final Tx8x2 raw-leaf count. The binary tree is complete at depth four.
pub use noid_tx::body_hash::BODY_HASH_LEAVES as TX_BODY_RAW_LEAVES;

/// Trace twin of the final Tx8x2 `SpineInputs`: the 16 raw two-lane leaves
/// consumed directly by the first compression level.
pub struct SpineInputsTrace {
    pub leaves: [[LinExpr; 2]; TX_BODY_RAW_LEAVES],
}

impl SpineInputsTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &SpineInputs) -> Self {
        Self {
            leaves: std::array::from_fn(|leaf| {
                std::array::from_fn(|lane| alloc_block(b, native.leaves[leaf][lane]))
            }),
        }
    }
}

/// Trace twin of `BlockSpineProof`.
pub struct TxBodySpineProofTrace {
    pub main: BlockSpineUnifiedProofTrace,
    pub shift: BlockSpineShiftProofTrace,
    pub tx_hash_pins: LinearEvalProofTrace,
    pub batch: MultiBatchEvalProofTrace,
    pub num_vars: usize,
    pub live_slots: usize,
}

impl TxBodySpineProofTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &BlockSpineProof, n_instances: usize) -> Self {
        let live_slots = n_instances * N_SPINE_SLOTS;
        let num_vars = num_vars_for(live_slots);
        assert_eq!(native.live_slots, live_slots, "proof off the trace shape");
        assert_eq!(native.num_vars, num_vars, "proof off the trace shape");
        Self {
            main: BlockSpineUnifiedProofTrace::alloc(b, &native.kill_shot.main, num_vars),
            shift: BlockSpineShiftProofTrace::alloc(b, &native.kill_shot.shift, num_vars),
            tx_hash_pins: LinearEvalProofTrace::alloc(b, &native.tx_hash_pins, num_vars),
            batch: MultiBatchEvalProofTrace::alloc(b, &native.batch, num_vars, 3),
            num_vars,
            live_slots,
        }
    }
}

// ---------------------------------------------------------------------------
// [K] — verifier replay
// ---------------------------------------------------------------------------

/// Trace twin of `tx_hash_pin_claims`.
fn tx_hash_pin_claims_trace(
    tx_body_hashes: &[[LinExpr; 2]],
    slots_per_tx: usize,
    num_vars: usize,
) -> Vec<LinearEvalClaimTrace> {
    let mut claims = Vec::with_capacity(tx_body_hashes.len() * 2);
    for (tx_idx, tx_hash) in tx_body_hashes.iter().enumerate() {
        let wrap_slot = tx_idx * slots_per_tx + (slots_per_tx - 1);
        for lane in 0..2 {
            claims.push(LinearEvalClaimTrace {
                terms: vec![LinearEvalTermTrace {
                    index: spine_point_index(num_vars, wrap_slot, N_ROUNDS, lane),
                    coeff: LinExpr::constant(F128::ONE),
                }],
                value: tx_hash[lane].clone(),
            });
        }
    }
    claims
}

fn verify_tx_body_spine_killshot_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    proof: &TxBodySpineProofTrace,
    tx_body_hashes: &[[LinExpr; 2]],
    slots_per_tx: usize,
    pin_tag: u128,
) -> [BatchEvalReductionTrace; 3] {
    assert_eq!(proof.live_slots, tx_body_hashes.len() * slots_per_tx);
    assert_eq!(proof.num_vars, num_vars_for(proof.live_slots));

    // Absorb all tx_body_hashes (binds block contents).
    for hash in tx_body_hashes {
        ch.absorb(b, &hash[0]);
        ch.absorb(b, &hash[1]);
    }

    let main_red =
        verify_block_spine_unified_trace(b, ch, &proof.main, proof.num_vars, proof.live_slots);
    let shift_red = verify_block_spine_shift_trace(b, ch, &proof.shift, &main_red, proof.num_vars);

    let pin_claims = tx_hash_pin_claims_trace(tx_body_hashes, slots_per_tx, proof.num_vars);
    let pin_red = verify_linear_eval_prebound_trace(
        b,
        ch,
        &proof.tx_hash_pins,
        &pin_claims,
        proof.num_vars,
        pin_tag,
    );

    close_spine_family_batch(
        b,
        ch,
        &main_red,
        &shift_red,
        &pin_red,
        &proof.batch,
        proof.num_vars,
    )
}

/// Trace twin of the sole `verify_block_spine_killshot`.
pub fn verify_block_spine_killshot_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut RawChannelTrace,
    proof: &TxBodySpineProofTrace,
    tx_body_hashes: &[[LinExpr; 2]],
) -> [BatchEvalReductionTrace; 3] {
    verify_tx_body_spine_killshot_trace(
        b,
        ch,
        proof,
        tx_body_hashes,
        N_SPINE_SLOTS,
        BLOCK_SPINE_TX_HASH_PIN_TAG,
    )
}

// ---------------------------------------------------------------------------
// [D] — discharge replay (oracle build_state_in transliterations)
// ---------------------------------------------------------------------------

fn chain_absorb_pair_trace(
    prev_out: &[[LinExpr; STATE_SIZE]],
    src: usize,
    absorb: [LinExpr; 2],
) -> [LinExpr; STATE_SIZE] {
    let s = &prev_out[src];
    [
        s[0].add(&absorb[0]),
        s[1].add(&absorb[1]),
        s[2].clone(),
        s[3].clone(),
    ]
}

/// Trace twin of `oracle::build_state_in` + `evaluate_spine`, pushing every
/// slot into the accumulator. Returns nothing — the wrap binding happens via
/// the killshot's tx_hash_pins relation.
fn push_tx_body_spine_slots(
    b: &mut FieldR1csBuilder,
    acc: &mut ColumnAccumulator,
    circuit: &SpineCircuit,
    inputs: &SpineInputsTrace,
) {
    let mut outs: Vec<[LinExpr; STATE_SIZE]> = Vec::with_capacity(circuit.slots.len());
    let digest = |outs: &[[LinExpr; STATE_SIZE]], id: usize| -> [LinExpr; 2] {
        [outs[id][0].clone(), outs[id][1].clone()]
    };
    for slot in &circuit.slots {
        let [iv_hi, iv_lo] = slot.capacity_iv;
        let state_in: [LinExpr; STATE_SIZE] = match slot.role {
            InstanceRole::CompressPermA { level, pos } => {
                let left = match slot.left_child {
                    Some(id) => digest(&outs, id),
                    None => resolve_raw_leaf(inputs, level, pos, true),
                };
                [
                    left[0].clone(),
                    left[1].clone(),
                    const_block(iv_hi),
                    const_block(iv_lo),
                ]
            }
            InstanceRole::CompressPermB { level, pos } => {
                let right = match slot.right_child {
                    Some(id) => digest(&outs, id),
                    None => resolve_raw_leaf(inputs, level, pos, false),
                };
                chain_absorb_pair_trace(&outs, slot.prev_output_src.unwrap(), right)
            }
            InstanceRole::WrapPerm => {
                let root = digest(&outs, slot.left_child.unwrap());
                [
                    root[0].clone(),
                    root[1].clone(),
                    const_block(iv_hi),
                    const_block(iv_lo),
                ]
            }
        };
        let out = acc.push_slot(b, &state_in);
        outs.push(out);
    }
}

/// Trace twin of `oracle::resolve_child_digest`'s raw-leaf branch. Only the
/// eight level-one compression nodes consume external leaves; every higher
/// child is the digest of a preceding spine slot.
fn resolve_raw_leaf(inputs: &SpineInputsTrace, level: u8, pos: u8, is_left: bool) -> [LinExpr; 2] {
    assert_eq!(level, 1, "raw child outside level-1 compress");
    let leaf = 2 * pos as usize + usize::from(!is_left);
    inputs
        .leaves
        .get(leaf)
        .unwrap_or_else(|| panic!("raw leaf out of range at compress (pos={pos})"))
        .clone()
}

/// Trace twin of the tx-body component discharge.
pub fn discharge_tx_body_trace(
    b: &mut FieldR1csBuilder,
    inputs: &[SpineInputsTrace],
    reductions: &[BatchEvalReductionTrace; 3],
) {
    assert!(!inputs.is_empty());
    let circuit = SpineCircuit::build();
    let live_slots = inputs.len() * N_SPINE_SLOTS;
    let mut acc = ColumnAccumulator::new(b, &reductions[0].point, live_slots);
    for input in inputs {
        push_tx_body_spine_slots(b, &mut acc, &circuit, input);
    }
    let (state_value, sin_value, sout_value) = acc.finish();
    super::pin_zero(b, &state_value.add(&reductions[0].value));
    super::pin_zero(b, &sin_value.add(&reductions[1].value));
    super::pin_zero(b, &sout_value.add(&reductions[2].value));
}

// ---------------------------------------------------------------------------
// Full slot assembly: killshot on a fresh channel plus discharge.
// ---------------------------------------------------------------------------

/// Final Tx8x2 [K]+[D] slot. Returns input and tx-body-hash
/// wires (shared with any other slot that consumes the same hashes — e.g.
/// the tx-root Merkle leaves and the receipt bindings).
pub fn build_tx_body_slot(
    b: &mut FieldR1csBuilder,
    proof: &BlockSpineProof,
    inputs: &[SpineInputs],
    tx_body_hashes: &[[Block128; 2]],
) -> (Vec<SpineInputsTrace>, Vec<[LinExpr; 2]>) {
    assert_eq!(inputs.len(), tx_body_hashes.len());
    let inputs_t: Vec<SpineInputsTrace> = inputs
        .iter()
        .map(|i| SpineInputsTrace::alloc(b, i))
        .collect();
    let hashes_t: Vec<[LinExpr; 2]> = tx_body_hashes
        .iter()
        .map(|h| std::array::from_fn(|i| alloc_block(b, h[i])))
        .collect();
    let proof_t = TxBodySpineProofTrace::alloc(b, proof, inputs.len());
    let mut ch = RawChannelTrace::new();
    let reds = verify_block_spine_killshot_trace(b, &mut ch, &proof_t, &hashes_t);
    discharge_tx_body_trace(b, &inputs_t, &reds);
    (inputs_t, hashes_t)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use noid_core::TowerField;
    use noid_gkr::block_spine::{
        discharge_block_spine_reductions_native, prove_block_spine_killshot,
        verify_block_spine_killshot, BlockSpineMle,
    };
    use noid_gkr::spine_sumcheck::reconstruct_slot_states;
    use noid_poseidon2b::channel::Poseidon2bChannel;

    fn tx_body_inputs(seed: u128) -> SpineInputs {
        SpineInputs {
            leaves: std::array::from_fn(|leaf| {
                std::array::from_fn(|lane| Block128::from(seed + 1 + (2 * leaf + lane) as u128))
            }),
        }
    }

    struct TxBodyFixture {
        proof: BlockSpineProof,
        inputs: Vec<SpineInputs>,
        hashes: Vec<[Block128; 2]>,
    }

    fn tx_body_fixture(n: usize) -> TxBodyFixture {
        let circuit = SpineCircuit::build();
        let inputs: Vec<SpineInputs> = (0..n).map(|i| tx_body_inputs(i as u128 * 97)).collect();
        let mut all_state_ins = Vec::new();
        let mut hashes = Vec::new();
        for input in &inputs {
            let states = reconstruct_slot_states(&circuit, input);
            all_state_ins.extend(states.iter().map(|(s, _)| *s));
            let wrap = states.last().unwrap();
            hashes.push([wrap.1[0], wrap.1[1]]);
        }
        let mle = BlockSpineMle::build(n, &all_state_ins);
        let mut ch = Poseidon2bChannel::new();
        let (proof, _) = prove_block_spine_killshot(n, &mle, &hashes, &mut ch);
        TxBodyFixture {
            proof,
            inputs,
            hashes,
        }
    }

    #[test]
    fn final_topology_is_31_contiguous_slots_per_transaction() {
        let circuit = SpineCircuit::build();
        assert_eq!(N_SPINE_SLOTS, 31);
        assert_eq!(circuit.slots.len(), N_SPINE_SLOTS);
        assert_eq!(circuit.wrap_id(), 30);
        assert!(matches!(
            circuit.slots[0].role,
            InstanceRole::CompressPermA { level: 1, pos: 0 }
        ));
        assert!(matches!(
            circuit.slots[29].role,
            InstanceRole::CompressPermB { level: 4, pos: 0 }
        ));
        assert!(matches!(circuit.slots[30].role, InstanceRole::WrapPerm));

        let fixture = tx_body_fixture(2);
        assert_eq!(fixture.proof.live_slots, 2 * N_SPINE_SLOTS);
        assert_eq!(fixture.proof.live_slots, 62);

        let hashes = vec![
            [LinExpr::zero(), LinExpr::zero()],
            [LinExpr::zero(), LinExpr::zero()],
        ];
        let num_vars = num_vars_for(2 * N_SPINE_SLOTS);
        let claims = tx_hash_pin_claims_trace(&hashes, N_SPINE_SLOTS, num_vars);
        assert_eq!(
            claims[2].terms[0].index,
            spine_point_index(num_vars, 61, N_ROUNDS, 0),
            "the second wrap must be slot 61, with no per-tx padding gap"
        );
    }

    fn native_accepts(f: &TxBodyFixture) -> bool {
        let circuit = SpineCircuit::build();
        let mut ch = Poseidon2bChannel::new();
        let Some(red) = verify_block_spine_killshot(&f.proof, f.inputs.len(), &f.hashes, &mut ch)
        else {
            return false;
        };
        let mut slot_state_ins = Vec::new();
        for input in &f.inputs {
            slot_state_ins.extend(
                reconstruct_slot_states(&circuit, input)
                    .iter()
                    .map(|(s, _)| *s),
            );
        }
        discharge_block_spine_reductions_native(f.inputs.len(), &slot_state_ins, &red)
    }

    fn trace_accepts(f: &TxBodyFixture) -> bool {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut b = FieldR1csBuilder::new();
            let _ = build_tx_body_slot(&mut b, &f.proof, &f.inputs, &f.hashes);
            let (r1cs, z) = b.build();
            r1cs.satisfies(&z)
        }))
        .unwrap_or(false)
    }

    /// Fixed-matrix class gate: same tx count, different tx content must
    /// build byte-identical R1CS matrices (the recursion's
    /// protocol-constant-matrix requirement).
    #[test]
    fn fixed_matrix_within_class() {
        let digest = |n: usize, seed0: u128| {
            let circuit = SpineCircuit::build();
            let inputs: Vec<SpineInputs> = (0..n)
                .map(|i| tx_body_inputs(seed0 + i as u128 * 97))
                .collect();
            let mut all_state_ins = Vec::new();
            let mut hashes = Vec::new();
            for input in &inputs {
                let states = reconstruct_slot_states(&circuit, input);
                all_state_ins.extend(states.iter().map(|(s, _)| *s));
                let wrap = states.last().unwrap();
                hashes.push([wrap.1[0], wrap.1[1]]);
            }
            let mle = BlockSpineMle::build(n, &all_state_ins);
            let mut ch = Poseidon2bChannel::new();
            let (proof, _) = prove_block_spine_killshot(n, &mle, &hashes, &mut ch);
            let mut b = FieldR1csBuilder::new();
            let _ = build_tx_body_slot(&mut b, &proof, &inputs, &hashes);
            let (r1cs, _z) = b.build();
            r1cs.statement_digest()
        };
        assert_eq!(
            digest(2, 5),
            digest(2, 987_654),
            "tx-body slot matrix depends on block content"
        );
    }

    #[test]
    fn tx_body_trace_positive() {
        for n in [1usize, 2] {
            let f = tx_body_fixture(n);
            assert!(native_accepts(&f), "native fixture broken");
            let mut b = FieldR1csBuilder::new();
            let _ = build_tx_body_slot(&mut b, &f.proof, &f.inputs, &f.hashes);
            let (r1cs, z) = b.build();
            assert!(
                r1cs.satisfies(&z),
                "honest tx-body spine trace unsat (n={n})"
            );
            if n == 1 {
                eprintln!(
                    "tx-body slot (1 tx): {} useful rows (k_log = {})",
                    r1cs.useful_rows, r1cs.k_log
                );
            }
        }
    }

    fn visit_spine_proof_fields(p: &mut BlockSpineProof, f: &mut dyn FnMut(&mut Block128)) {
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
        for r in &mut p.tx_hash_pins.rounds {
            for e in &mut r.evals_at_1_2 {
                f(e);
            }
        }
        f(&mut p.tx_hash_pins.b_final);
        for r in &mut p.batch.rounds {
            for e in &mut r.evals_at_1_2 {
                f(e);
            }
        }
        for v in &mut p.batch.b_finals {
            f(v);
        }
    }

    /// Replay-completeness auto-mutator (final Tx8x2 tree @1 tx).
    /// 0 surviving mutants.
    #[test]
    fn tx_body_proof_mutator_kills_all() {
        let f = tx_body_fixture(1);
        let mut n_fields = 0usize;
        {
            let mut c = f.proof.clone();
            visit_spine_proof_fields(&mut c, &mut |_| n_fields += 1);
        }
        let stride: usize = std::env::var("NOID_TRACE_MUTATE_STRIDE")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(1);

        let mut survivors = Vec::new();
        for target in (0..n_fields).step_by(stride) {
            let mut bad_proof = f.proof.clone();
            let mut i = 0usize;
            visit_spine_proof_fields(&mut bad_proof, &mut |v| {
                if i == target {
                    *v += Block128::ONE;
                }
                i += 1;
            });
            let bad = TxBodyFixture {
                proof: bad_proof,
                inputs: f.inputs.clone(),
                hashes: f.hashes.clone(),
            };
            assert!(!native_accepts(&bad), "native accepted mutant {target}");
            if trace_accepts(&bad) {
                survivors.push(target);
            }
        }
        assert!(
            survivors.is_empty(),
            "surviving tx-body spine proof mutants: {survivors:?} of {n_fields}"
        );
    }

    /// Statement + discharge-data mutator: every leaf payload lane and
    /// tx hash lane.
    #[test]
    fn tx_body_statement_mutator_kills_all() {
        let f = tx_body_fixture(1);
        const STATEMENT_LANES: usize = TX_BODY_RAW_LEAVES * 2;
        // 16 raw leaves × 2 lanes + 2 hash lanes.
        let mutate = |target: usize| -> TxBodyFixture {
            let mut inputs = f.inputs.clone();
            let mut hashes = f.hashes.clone();
            let i0 = &mut inputs[0];
            if target < STATEMENT_LANES {
                i0.leaves[target / 2][target % 2] += Block128::ONE;
            } else if target < STATEMENT_LANES + 2 {
                hashes[0][target - STATEMENT_LANES] += Block128::ONE;
            } else {
                unreachable!();
            }
            TxBodyFixture {
                proof: f.proof.clone(),
                inputs,
                hashes,
            }
        };
        let mut survivors = Vec::new();
        for target in 0..STATEMENT_LANES + 2 {
            let bad = mutate(target);
            assert!(
                !native_accepts(&bad),
                "native accepted statement mutant {target}"
            );
            if trace_accepts(&bad) {
                survivors.push(target);
            }
        }
        assert!(
            survivors.is_empty(),
            "surviving tx-body spine statement mutants: {survivors:?}"
        );
    }

    #[test]
    fn raw_leaf_recombination_is_rejected() {
        let f = tx_body_fixture(1);
        let mut bad = TxBodyFixture {
            proof: f.proof.clone(),
            inputs: f.inputs.clone(),
            hashes: f.hashes.clone(),
        };
        bad.inputs[0].leaves.swap(0, TX_BODY_RAW_LEAVES - 1);
        assert!(!native_accepts(&bad));
        assert!(!trace_accepts(&bad));
    }

    /// Cross-test "trace ⇔ native" on randomized honest/mutated cases.
    #[test]
    fn tx_body_native_trace_equivalence() {
        let cases: usize = std::env::var("NOID_TRACE_CROSS_CASES")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(100);
        let mut seed = 0x5B1E_Fu128;
        let mut next = |m: u128| {
            seed = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
            (seed >> 16) % m
        };

        let f = tx_body_fixture(1);
        let mut n_fields = 0usize;
        {
            let mut c = f.proof.clone();
            visit_spine_proof_fields(&mut c, &mut |_| n_fields += 1);
        }
        for case in 0..cases {
            let case_f = if case % 2 == 0 {
                TxBodyFixture {
                    proof: f.proof.clone(),
                    inputs: f.inputs.clone(),
                    hashes: f.hashes.clone(),
                }
            } else {
                let target = next(n_fields as u128) as usize;
                let mut bad_proof = f.proof.clone();
                let mut i = 0usize;
                visit_spine_proof_fields(&mut bad_proof, &mut |v| {
                    if i == target {
                        *v += Block128::ONE;
                    }
                    i += 1;
                });
                TxBodyFixture {
                    proof: bad_proof,
                    inputs: f.inputs.clone(),
                    hashes: f.hashes.clone(),
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
