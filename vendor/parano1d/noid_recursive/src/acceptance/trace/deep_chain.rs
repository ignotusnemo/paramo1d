//! Trace twins of the deep-chain engine verifiers — the [G] slot bodies.
//!
//! Line-by-line transliterations of `noid_ivc_core::deep_chain`:
//! [`verify_deep_chain_walk_trace`] replays the 66-layer walk verifier,
//! [`verify_column_relation_trace`] the generic column-relation sumcheck,
//! [`verify_shift_discharge_trace`] the successor-kernel reduction. Same
//! absorb/squeeze order on the [`FsChannelTrace`], same checks; every
//! proof field is witness, every relation structure and round schedule is
//! a protocol constant baked at build time.
//!
//! Cost drivers (per the module they mirror): the walk absorbs
//! `w_log`×8-lane compressed round polynomials per layer (~5 permutations
//! each) — near-flat in transaction count; the relation and shift twins
//! are O(w_log) rounds each. All MDS/round-constant algebra folds into
//! affine expressions (zero rows); the only multiplications are Horner
//! walks, S-boxes on claimed values, per-group eq evaluations, and claim
//! batching.

use noid_ivc_core::deep_chain::c1::C1MultiDeepChainWalkProof;
use noid_ivc_core::deep_chain::relations::c1::{
    claimed_refs as c1_claimed_refs, C1ColumnRelationProof, C1RelationTerm, C1ShiftDischargeProof,
};
use noid_ivc_core::deep_chain::relations::{
    claimed_refs, ColRef, ColumnRelationProof, FixedPattern, RelationTerm, ShiftDischargeProof,
    WeightedSumProof, MAX_TERM_FACTORS, RELATION_DEGREE,
};
use noid_ivc_core::deep_chain::schedule::flat_of_tower_u128;
use noid_ivc_core::deep_chain::{
    flat_mds, flat_round_constant, is_full_round, DeepChainWalkProof, MultiDeepChainWalkProof,
    WALK_DEGREE,
};
use noid_ivc_core::field_circuit::FsChannelOps;
#[cfg(test)]
use noid_ivc_core::field_circuit::FsChannelTrace;
use noid_poseidon2b::native::permutation::{N_ROUNDS, STATE_SIZE};

use super::{
    mul, mul_ext, pin_eq, pin_eq_ext, pow7_ext, ExtExpr, FieldR1csBuilder, LinExpr, F128, F256,
};

// ---------------------------------------------------------------------------
// Proof wires
// ---------------------------------------------------------------------------

/// A claim group as expressions.
#[derive(Clone)]
pub struct LaneClaimGroupTrace {
    pub point: Vec<LinExpr>,
    pub values: [LinExpr; STATE_SIZE],
}

/// Witness allocation of a [`DeepChainWalkProof`].
pub struct DeepChainWalkProofTrace {
    pub layers: Vec<WalkLayerProofTrace>,
}

pub struct WalkLayerProofTrace {
    pub round_coeffs: Vec<[LinExpr; WALK_DEGREE]>,
    pub next_values: [LinExpr; STATE_SIZE],
}

impl DeepChainWalkProofTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &DeepChainWalkProof, w_log: usize) -> Self {
        assert_eq!(native.layers.len(), N_ROUNDS, "walk proof layer count");
        let layers = native
            .layers
            .iter()
            .map(|l| {
                assert_eq!(l.round_coeffs.len(), w_log, "walk proof round count");
                WalkLayerProofTrace {
                    round_coeffs: l
                        .round_coeffs
                        .iter()
                        .map(|wire| std::array::from_fn(|i| alloc_expr(b, wire[i])))
                        .collect(),
                    next_values: std::array::from_fn(|i| alloc_expr(b, l.next_values[i])),
                }
            })
            .collect();
        Self { layers }
    }
}

/// Witness allocation of a multi-instance walk proof (equal-domain V1 or
/// ragged-domain V2, according to the verifier entry point).
pub struct MultiDeepChainWalkProofTrace {
    pub layers: Vec<MultiWalkLayerProofTrace>,
}

pub struct MultiWalkLayerProofTrace {
    pub round_coeffs: Vec<[LinExpr; WALK_DEGREE]>,
    pub next_values: Vec<[LinExpr; STATE_SIZE]>,
}

impl MultiDeepChainWalkProofTrace {
    pub fn alloc(
        b: &mut FieldR1csBuilder,
        native: &MultiDeepChainWalkProof,
        w_log: usize,
        instances: usize,
    ) -> Self {
        assert!(instances > 0, "multi-walk instance count");
        assert_eq!(native.layers.len(), N_ROUNDS, "multi-walk layer count");
        let layers = native
            .layers
            .iter()
            .map(|layer| {
                assert_eq!(layer.round_coeffs.len(), w_log, "multi-walk round count");
                assert_eq!(
                    layer.next_values.len(),
                    instances,
                    "multi-walk next-value instance count"
                );
                MultiWalkLayerProofTrace {
                    round_coeffs: layer
                        .round_coeffs
                        .iter()
                        .map(|wire| std::array::from_fn(|i| alloc_expr(b, wire[i])))
                        .collect(),
                    next_values: layer
                        .next_values
                        .iter()
                        .map(|values| std::array::from_fn(|i| alloc_expr(b, values[i])))
                        .collect(),
                }
            })
            .collect();
        Self { layers }
    }

    /// Allocate the V2 wire shape from its ordered native domain widths.
    pub fn alloc_ragged(
        b: &mut FieldR1csBuilder,
        native: &MultiDeepChainWalkProof,
        w_logs: &[usize],
    ) -> Self {
        assert!(!w_logs.is_empty(), "multi-walk instance count");
        let max_w_log = *w_logs.iter().max().expect("one multi-walk instance");
        Self::alloc(b, native, max_w_log, w_logs.len())
    }
}

/// One genuine C1 claim group represented in the base-field circuit.
#[derive(Clone)]
pub struct C1LaneClaimGroupTrace {
    pub point: Vec<ExtExpr>,
    pub values: [ExtExpr; STATE_SIZE],
}

/// Witness allocation of the genuine extension-field ragged walk proof.
pub struct C1MultiDeepChainWalkProofTrace {
    pub layers: Vec<C1MultiWalkLayerProofTrace>,
}

pub struct C1MultiWalkLayerProofTrace {
    pub round_coeffs: Vec<[ExtExpr; WALK_DEGREE]>,
    pub next_values: Vec<[ExtExpr; STATE_SIZE]>,
}

impl C1MultiDeepChainWalkProofTrace {
    pub fn alloc_ragged(
        b: &mut FieldR1csBuilder,
        native: &C1MultiDeepChainWalkProof,
        w_logs: &[usize],
    ) -> Self {
        assert!(!w_logs.is_empty(), "C1 multi-walk instance count");
        let max_w_log = *w_logs.iter().max().expect("one C1 multi-walk instance");
        assert_eq!(native.layers.len(), N_ROUNDS, "C1 multi-walk layer count");
        let layers = native
            .layers
            .iter()
            .map(|layer| {
                assert_eq!(
                    layer.round_coeffs.len(),
                    max_w_log,
                    "C1 multi-walk round count"
                );
                assert_eq!(
                    layer.next_values.len(),
                    w_logs.len(),
                    "C1 multi-walk next-value instance count"
                );
                C1MultiWalkLayerProofTrace {
                    round_coeffs: layer
                        .round_coeffs
                        .iter()
                        .map(|wire| std::array::from_fn(|i| alloc_ext_expr(b, wire[i])))
                        .collect(),
                    next_values: layer
                        .next_values
                        .iter()
                        .map(|values| std::array::from_fn(|i| alloc_ext_expr(b, values[i])))
                        .collect(),
                }
            })
            .collect();
        Self { layers }
    }
}

fn alloc_expr(b: &mut FieldR1csBuilder, v: F128) -> LinExpr {
    LinExpr::from_wire(b.alloc_f128(v))
}

fn alloc_ext_expr(b: &mut FieldR1csBuilder, value: F256) -> ExtExpr {
    ExtExpr::new(
        LinExpr::from_wire(b.alloc_f128(value.lo)),
        LinExpr::from_wire(b.alloc_f128(value.hi)),
    )
}

/// x^7 on an expression: 4 multiplication rows.
pub fn sbox7_trace(b: &mut FieldR1csBuilder, x: &LinExpr) -> LinExpr {
    let x2 = mul(b, x, x);
    let x4 = mul(b, &x2, &x2);
    let x3 = mul(b, x, &x2);
    mul(b, &x3, &x4)
}

fn layer_terms_trace(
    b: &mut FieldR1csBuilder,
    q: usize,
    values: &[LinExpr; STATE_SIZE],
) -> [LinExpr; STATE_SIZE] {
    if is_full_round(q) {
        std::array::from_fn(|lane| {
            let x = values[lane].add(&LinExpr::constant(flat_round_constant(lane, q)));
            sbox7_trace(b, &x)
        })
    } else {
        std::array::from_fn(|lane| {
            if lane == 0 {
                let x = values[0].add(&LinExpr::constant(flat_round_constant(0, q)));
                sbox7_trace(b, &x)
            } else {
                values[lane].clone()
            }
        })
    }
}

// ---------------------------------------------------------------------------
// Shared sumcheck pieces
// ---------------------------------------------------------------------------

/// Reconstruct + Horner for a compressed wire `[c_0, c_2..c_d]`: the linear
/// coefficient is `claim + Σ_{i≥2} c_i` (free XOR algebra), then evaluate
/// at `r` with d multiplications.
fn compressed_horner(
    b: &mut FieldR1csBuilder,
    wire: &[LinExpr],
    claim: &LinExpr,
    r: &LinExpr,
) -> LinExpr {
    let mut c1 = claim.clone();
    for c in &wire[1..] {
        c1 = c1.add(c);
    }
    // coeffs = [wire[0], c1, wire[1], .., wire[d−1]] — Horner top-down.
    let mut acc = wire[wire.len() - 1].clone();
    for c in wire[1..wire.len() - 1].iter().rev() {
        let t = mul(b, &acc, r);
        acc = t.add(c);
    }
    let t = mul(b, &acc, r);
    acc = t.add(&c1);
    let t = mul(b, &acc, r);
    t.add(&wire[0])
}

fn compressed_horner_ext(
    b: &mut FieldR1csBuilder,
    wire: &[ExtExpr],
    claim: &ExtExpr,
    challenge: &ExtExpr,
) -> ExtExpr {
    let mut linear = claim.clone();
    for coefficient in &wire[1..] {
        linear = linear.add(coefficient);
    }
    let mut accumulator = wire[wire.len() - 1].clone();
    for coefficient in wire[1..wire.len() - 1].iter().rev() {
        accumulator = mul_ext(b, &accumulator, challenge).add(coefficient);
    }
    accumulator = mul_ext(b, &accumulator, challenge).add(&linear);
    mul_ext(b, &accumulator, challenge).add(&wire[0])
}

fn layer_terms_ext_trace(
    b: &mut FieldR1csBuilder,
    round: usize,
    values: &[ExtExpr; STATE_SIZE],
) -> [ExtExpr; STATE_SIZE] {
    if is_full_round(round) {
        std::array::from_fn(|lane| {
            let value = values[lane].add(&ExtExpr::constant(F256::from_base(flat_round_constant(
                lane, round,
            ))));
            pow7_ext(b, &value)
        })
    } else {
        std::array::from_fn(|lane| {
            if lane == 0 {
                let value = values[0].add(&ExtExpr::constant(F256::from_base(
                    flat_round_constant(0, round),
                )));
                pow7_ext(b, &value)
            } else {
                values[lane].clone()
            }
        })
    }
}

fn eq_eval_ext_trace(b: &mut FieldR1csBuilder, left: &[ExtExpr], right: &[ExtExpr]) -> ExtExpr {
    assert_eq!(left.len(), right.len(), "C1 equality point arity");
    let mut product = ExtExpr::one();
    for (left, right) in left.iter().zip(right) {
        // xy + (1 + x)(1 + y) = 1 + x + y in characteristic two.
        let factor = ExtExpr::one().add(left).add(right);
        product = mul_ext(b, &product, &factor);
    }
    product
}

// ---------------------------------------------------------------------------
// The walk verifier twin
// ---------------------------------------------------------------------------

/// Trace twin of `deep_chain::verify_deep_chain_walk`. Group points and
/// values are expressions the caller ties to its relation twins; returns
/// the terminal layer-0 claim group for the wiring substitution.
pub fn verify_deep_chain_walk_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut impl FsChannelOps,
    w_log: usize,
    out_groups: &[LaneClaimGroupTrace],
    proof: &DeepChainWalkProofTrace,
) -> LaneClaimGroupTrace {
    assert!(!out_groups.is_empty());
    for g in out_groups {
        assert_eq!(g.point.len(), w_log, "walk group point arity");
    }
    assert_eq!(proof.layers.len(), N_ROUNDS);

    ch.observe_label(b, b"history-deep-chain-walk-v0");
    for g in out_groups {
        ch.observe_f128_slice(b, &g.point);
        ch.observe_f128_slice(b, &g.values);
    }

    let mut group_points: Vec<Vec<LinExpr>> = out_groups.iter().map(|g| g.point.clone()).collect();
    let mut group_values: Vec<[LinExpr; STATE_SIZE]> =
        out_groups.iter().map(|g| g.values.clone()).collect();

    let mut terminal: Option<LaneClaimGroupTrace> = None;
    for (li, layer_proof) in proof.layers.iter().enumerate() {
        let layer = N_ROUNDS - li;
        let q = layer - 1;
        let alpha = ch.sample_f128(b);

        // Lane weights α^{4g+i+1} — a running product chain of wires.
        let mut weights: Vec<[LinExpr; STATE_SIZE]> = Vec::with_capacity(group_points.len());
        let mut power = LinExpr::constant(F128::ONE);
        for _ in 0..group_points.len() {
            let w: [LinExpr; STATE_SIZE] = std::array::from_fn(|_| {
                power = mul(b, &power, &alpha);
                power.clone()
            });
            weights.push(w);
        }

        // Running claim.
        let mut claim = LinExpr::zero();
        for (vals, w_g) in group_values.iter().zip(weights.iter()) {
            for i in 0..STATE_SIZE {
                claim = claim.add(&mul(b, &w_g[i], &vals[i]));
            }
        }

        let mut point = Vec::with_capacity(w_log);
        for wire in &layer_proof.round_coeffs {
            ch.observe_f128_slice(b, wire);
            let r = ch.sample_f128(b);
            claim = compressed_horner(b, wire, &claim, &r);
            point.push(r);
        }
        ch.observe_f128_slice(b, &layer_proof.next_values);

        // term_j on the claimed next values (round constants are free adds).
        let mds = flat_mds(is_full_round(q));
        let terms = layer_terms_trace(b, q, &layer_proof.next_values);

        // expected = Σ_g eq(ρ_g, point) · Σ_j c_{g,j}·term_j with
        // c_{g,j} = Σ_i w_{g,i}·MDS[i][j] — MDS entries are constants, so
        // c_{g,j} is affine in the weight wires (zero rows).
        let mut expected = LinExpr::zero();
        for (g_point, w_g) in group_points.iter().zip(weights.iter()) {
            let mut dot = LinExpr::zero();
            for j in 0..STATE_SIZE {
                let mut c_gj = LinExpr::zero();
                for i in 0..STATE_SIZE {
                    c_gj = c_gj.add(&w_g[i].scale(mds[i][j]));
                }
                dot = dot.add(&mul(b, &c_gj, &terms[j]));
            }
            let eq = b.eq_eval_trace(g_point, &point);
            expected = expected.add(&mul(b, &eq, &dot));
        }
        pin_eq(b, &expected, &claim);

        group_points = vec![point.clone()];
        group_values = vec![layer_proof.next_values.clone()];
        terminal = Some(LaneClaimGroupTrace {
            point,
            values: layer_proof.next_values.clone(),
        });
    }
    terminal.expect("N_ROUNDS ≥ 1")
}

/// Trace twin of `verify_multi_deep_chain_walk`.
///
/// Every instance has the same `w_log` but its own state columns and claim
/// groups.  Instance count and each group count enter the V1 transcript before
/// a single power ladder batches all claims.  The layer sumcheck point is
/// shared; the four next-layer values and terminal claim remain per-instance.
pub fn verify_multi_deep_chain_walk_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut impl FsChannelOps,
    w_log: usize,
    out_groups: &[Vec<LaneClaimGroupTrace>],
    proof: &MultiDeepChainWalkProofTrace,
) -> Vec<LaneClaimGroupTrace> {
    assert!(!out_groups.is_empty(), "at least one multi-walk instance");
    for groups in out_groups {
        assert!(!groups.is_empty(), "every instance needs an output claim");
        assert!(
            groups.iter().all(|group| group.point.len() == w_log),
            "multi-walk claim point arity"
        );
    }
    assert_eq!(proof.layers.len(), N_ROUNDS, "multi-walk layer count");
    assert!(proof.layers.iter().all(|layer| {
        layer.round_coeffs.len() == w_log && layer.next_values.len() == out_groups.len()
    }));

    let count_lane = |count: usize| {
        LinExpr::constant(F128 {
            lo: u64::try_from(count).expect("multi-walk count exceeds u64"),
            hi: 0,
        })
    };
    ch.observe_label(b, b"history-deep-chain-multi-walk-v1");
    ch.observe_f128(b, &count_lane(out_groups.len()));
    for groups in out_groups {
        ch.observe_f128(b, &count_lane(groups.len()));
        for group in groups {
            ch.observe_f128_slice(b, &group.point);
            ch.observe_f128_slice(b, &group.values);
        }
    }

    let mut groups = out_groups.to_vec();
    for (layer_index, layer_proof) in proof.layers.iter().enumerate() {
        let layer = N_ROUNDS - layer_index;
        let q = layer - 1;
        let alpha = ch.sample_f128(b);

        // One canonical power ladder across instance-major, group-major, then
        // lane-major order, matching the native verifier exactly.
        let mut power = LinExpr::constant(F128::ONE);
        let weights: Vec<Vec<[LinExpr; STATE_SIZE]>> = groups
            .iter()
            .map(|instance| {
                instance
                    .iter()
                    .map(|_| {
                        std::array::from_fn(|_| {
                            power = mul(b, &power, &alpha);
                            power.clone()
                        })
                    })
                    .collect()
            })
            .collect();

        let mut claim = LinExpr::zero();
        for (instance_groups, instance_weights) in groups.iter().zip(&weights) {
            for (group, lane_weights) in instance_groups.iter().zip(instance_weights) {
                for lane in 0..STATE_SIZE {
                    claim = claim.add(&mul(b, &lane_weights[lane], &group.values[lane]));
                }
            }
        }

        let mut point = Vec::with_capacity(w_log);
        for wire in &layer_proof.round_coeffs {
            ch.observe_f128_slice(b, wire);
            let challenge = ch.sample_f128(b);
            claim = compressed_horner(b, wire, &claim, &challenge);
            point.push(challenge);
        }
        let flat_next = layer_proof
            .next_values
            .iter()
            .flat_map(|values| values.iter().cloned())
            .collect::<Vec<_>>();
        ch.observe_f128_slice(b, &flat_next);

        let mds = flat_mds(is_full_round(q));
        let mut expected = LinExpr::zero();
        for ((instance_groups, instance_weights), instance_next) in
            groups.iter().zip(&weights).zip(&layer_proof.next_values)
        {
            let terms = layer_terms_trace(b, q, instance_next);
            for (group, lane_weights) in instance_groups.iter().zip(instance_weights) {
                let mut dot = LinExpr::zero();
                for output_lane in 0..STATE_SIZE {
                    let mut column_weight = LinExpr::zero();
                    for input_lane in 0..STATE_SIZE {
                        column_weight = column_weight
                            .add(&lane_weights[input_lane].scale(mds[input_lane][output_lane]));
                    }
                    dot = dot.add(&mul(b, &column_weight, &terms[output_lane]));
                }
                let eq = b.eq_eval_trace(&group.point, &point);
                expected = expected.add(&mul(b, &eq, &dot));
            }
        }
        pin_eq(b, &expected, &claim);

        groups = layer_proof
            .next_values
            .iter()
            .map(|values| {
                vec![LaneClaimGroupTrace {
                    point: point.clone(),
                    values: values.clone(),
                }]
            })
            .collect();
    }

    groups
        .into_iter()
        .map(|mut instance| instance.pop().expect("one terminal group per instance"))
        .collect()
}

/// Trace twin of `deep_chain::verify_ragged_multi_deep_chain_walk` (V2).
///
/// Each instance retains its native `w_logs[a]`-coordinate state columns.  A
/// common `W = max(w_logs)` sumcheck aligns a smaller instance to the zero high
/// suffix: its state MLE ignores high challenges while its equality weight is
/// multiplied by `∏(1 + r_j)`.  Consequently its returned terminal point is
/// the native low prefix, not a padded outer-column point.
pub fn verify_ragged_multi_deep_chain_walk_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut impl FsChannelOps,
    w_logs: &[usize],
    out_groups: &[Vec<LaneClaimGroupTrace>],
    proof: &MultiDeepChainWalkProofTrace,
) -> Vec<LaneClaimGroupTrace> {
    assert!(!out_groups.is_empty(), "at least one multi-walk instance");
    assert_eq!(w_logs.len(), out_groups.len(), "one width per instance");
    let max_w_log = *w_logs.iter().max().expect("one multi-walk instance");
    for (groups, &w_log) in out_groups.iter().zip(w_logs) {
        assert!(!groups.is_empty(), "every instance needs an output claim");
        assert!(
            groups.iter().all(|group| group.point.len() == w_log),
            "ragged multi-walk claim point arity"
        );
    }
    assert_eq!(proof.layers.len(), N_ROUNDS, "multi-walk layer count");
    assert!(proof.layers.iter().all(|layer| {
        layer.round_coeffs.len() == max_w_log && layer.next_values.len() == out_groups.len()
    }));

    let count_lane = |count: usize| {
        LinExpr::constant(F128 {
            lo: u64::try_from(count).expect("multi-walk count exceeds u64"),
            hi: 0,
        })
    };
    ch.observe_label(b, b"history-deep-chain-ragged-multi-walk-v2");
    ch.observe_f128(b, &count_lane(out_groups.len()));
    for (&w_log, groups) in w_logs.iter().zip(out_groups) {
        ch.observe_f128(b, &count_lane(w_log));
        ch.observe_f128(b, &count_lane(groups.len()));
        for group in groups {
            ch.observe_f128_slice(b, &group.point);
            ch.observe_f128_slice(b, &group.values);
        }
    }

    let mut groups = out_groups.to_vec();
    for (layer_index, layer_proof) in proof.layers.iter().enumerate() {
        let layer = N_ROUNDS - layer_index;
        let q = layer - 1;
        let alpha = ch.sample_f128(b);

        let mut power = LinExpr::constant(F128::ONE);
        let weights: Vec<Vec<[LinExpr; STATE_SIZE]>> = groups
            .iter()
            .map(|instance| {
                instance
                    .iter()
                    .map(|_| {
                        std::array::from_fn(|_| {
                            power = mul(b, &power, &alpha);
                            power.clone()
                        })
                    })
                    .collect()
            })
            .collect();

        let mut claim = LinExpr::zero();
        for (instance_groups, instance_weights) in groups.iter().zip(&weights) {
            for (group, lane_weights) in instance_groups.iter().zip(instance_weights) {
                for lane in 0..STATE_SIZE {
                    claim = claim.add(&mul(b, &lane_weights[lane], &group.values[lane]));
                }
            }
        }

        let mut point = Vec::with_capacity(max_w_log);
        for wire in &layer_proof.round_coeffs {
            ch.observe_f128_slice(b, wire);
            let challenge = ch.sample_f128(b);
            claim = compressed_horner(b, wire, &claim, &challenge);
            point.push(challenge);
        }
        let flat_next = layer_proof
            .next_values
            .iter()
            .flat_map(|values| values.iter().cloned())
            .collect::<Vec<_>>();
        ch.observe_f128_slice(b, &flat_next);

        let mds = flat_mds(is_full_round(q));
        let high_gates = w_logs
            .iter()
            .map(|&w_log| {
                let mut gate = LinExpr::constant(F128::ONE);
                for coordinate in &point[w_log..] {
                    gate = mul(b, &gate, &coordinate.add_const(F128::ONE));
                }
                gate
            })
            .collect::<Vec<_>>();
        let mut expected = LinExpr::zero();
        for (instance, ((instance_groups, instance_weights), instance_next)) in groups
            .iter()
            .zip(&weights)
            .zip(&layer_proof.next_values)
            .enumerate()
        {
            let terms = layer_terms_trace(b, q, instance_next);
            let w_log = w_logs[instance];
            for (group, lane_weights) in instance_groups.iter().zip(instance_weights) {
                let mut dot = LinExpr::zero();
                for output_lane in 0..STATE_SIZE {
                    let mut column_weight = LinExpr::zero();
                    for input_lane in 0..STATE_SIZE {
                        column_weight = column_weight
                            .add(&lane_weights[input_lane].scale(mds[input_lane][output_lane]));
                    }
                    dot = dot.add(&mul(b, &column_weight, &terms[output_lane]));
                }
                let low_eq = b.eq_eval_trace(&group.point, &point[..w_log]);
                let aligned_eq = mul(b, &low_eq, &high_gates[instance]);
                expected = expected.add(&mul(b, &aligned_eq, &dot));
            }
        }
        pin_eq(b, &expected, &claim);

        groups = layer_proof
            .next_values
            .iter()
            .enumerate()
            .map(|(instance, values)| {
                vec![LaneClaimGroupTrace {
                    point: point[..w_logs[instance]].to_vec(),
                    values: values.clone(),
                }]
            })
            .collect();
    }

    groups
        .into_iter()
        .map(|mut instance| instance.pop().expect("one terminal group per instance"))
        .collect()
}

/// Trace twin of the genuine GF(2^256) single-group ragged walk.
///
/// The committed Poseidon columns remain base-field columns, while every
/// claim, Fiat-Shamir draw, sumcheck message, fold, and terminal evaluation
/// is represented as an [`ExtExpr`]. The transcript order is identical to
/// `deep_chain::c1::verify_ragged_deep_chain_walk`.
pub fn verify_c1_ragged_deep_chain_walk_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut impl FsChannelOps,
    w_logs: &[usize],
    out_groups: &[C1LaneClaimGroupTrace],
    proof: &C1MultiDeepChainWalkProofTrace,
) -> Vec<C1LaneClaimGroupTrace> {
    assert!(!w_logs.is_empty(), "at least one C1 walk child");
    assert_eq!(w_logs.len(), out_groups.len(), "one width per C1 child");
    let max_w_log = *w_logs.iter().max().expect("one C1 walk child");
    assert!(
        out_groups
            .iter()
            .zip(w_logs)
            .all(|(group, &w_log)| group.point.len() == w_log),
        "C1 walk point arity"
    );
    assert_eq!(proof.layers.len(), N_ROUNDS, "C1 walk layer count");
    assert!(proof.layers.iter().all(|layer| {
        layer.round_coeffs.len() == max_w_log && layer.next_values.len() == out_groups.len()
    }));

    let count = |value: usize| {
        ExtExpr::constant(F256::from_base(F128::new(
            u64::try_from(value).expect("C1 walk count exceeds u64"),
            0,
        )))
    };
    ch.observe_label(b, b"history-deep-chain-ragged-multi-walk-c1-v1");
    ch.observe_f256(b, &count(out_groups.len()));
    for (&w_log, group) in w_logs.iter().zip(out_groups) {
        ch.observe_f256(b, &count(w_log));
        ch.observe_f256(b, &ExtExpr::one());
        ch.observe_f256_slice(b, &group.point);
        ch.observe_f256_slice(b, &group.values);
    }

    let mut groups = out_groups.to_vec();
    for (layer_index, layer_proof) in proof.layers.iter().enumerate() {
        let layer = N_ROUNDS - layer_index;
        let round = layer - 1;
        let alpha = ch.sample_f256(b);

        let mut power = ExtExpr::one();
        let weights = groups
            .iter()
            .map(|_| {
                std::array::from_fn(|_| {
                    power = mul_ext(b, &power, &alpha);
                    power.clone()
                })
            })
            .collect::<Vec<[ExtExpr; STATE_SIZE]>>();
        let mds = flat_mds(is_full_round(round));
        let columns = weights
            .iter()
            .map(|lane_weights| {
                std::array::from_fn(|column| {
                    (0..STATE_SIZE).fold(ExtExpr::zero(), |sum, lane| {
                        sum.add(&lane_weights[lane].scale_base(mds[lane][column]))
                    })
                })
            })
            .collect::<Vec<[ExtExpr; STATE_SIZE]>>();

        let mut claim = ExtExpr::zero();
        for (group, lane_weights) in groups.iter().zip(&weights) {
            for lane in 0..STATE_SIZE {
                claim = claim.add(&mul_ext(b, &lane_weights[lane], &group.values[lane]));
            }
        }

        let mut point = Vec::with_capacity(max_w_log);
        for wire in &layer_proof.round_coeffs {
            ch.observe_f256_slice(b, wire);
            let challenge = ch.sample_f256(b);
            claim = compressed_horner_ext(b, wire, &claim, &challenge);
            point.push(challenge);
        }
        let flat_next = layer_proof
            .next_values
            .iter()
            .flat_map(|values| values.iter().cloned())
            .collect::<Vec<_>>();
        ch.observe_f256_slice(b, &flat_next);

        let mut expected = ExtExpr::zero();
        for child in 0..groups.len() {
            let terms = layer_terms_ext_trace(b, round, &layer_proof.next_values[child]);
            let mut high_gate = ExtExpr::one();
            for coordinate in &point[w_logs[child]..] {
                high_gate = mul_ext(b, &high_gate, &coordinate.add(&ExtExpr::one()));
            }
            let low_eq = eq_eval_ext_trace(b, &groups[child].point, &point[..w_logs[child]]);
            let aligned_eq = mul_ext(b, &low_eq, &high_gate);
            let mut dot = ExtExpr::zero();
            for lane in 0..STATE_SIZE {
                dot = dot.add(&mul_ext(b, &columns[child][lane], &terms[lane]));
            }
            expected = expected.add(&mul_ext(b, &aligned_eq, &dot));
        }
        pin_eq_ext(b, &expected, &claim);

        groups = layer_proof
            .next_values
            .iter()
            .enumerate()
            .map(|(child, values)| C1LaneClaimGroupTrace {
                point: point[..w_logs[child]].to_vec(),
                values: values.clone(),
            })
            .collect();
    }
    groups
}

// ---------------------------------------------------------------------------
// Genuine C1 column-relation and shift verifier twins
// ---------------------------------------------------------------------------

pub struct C1ColumnRelationProofTrace {
    pub rounds: Vec<[ExtExpr; RELATION_DEGREE]>,
    pub final_values: Vec<ExtExpr>,
}

impl C1ColumnRelationProofTrace {
    pub fn alloc(
        b: &mut FieldR1csBuilder,
        native: &C1ColumnRelationProof,
        w_log: usize,
        claimed_refs: usize,
    ) -> Self {
        assert_eq!(native.rounds.len(), w_log, "C1 relation round count");
        assert_eq!(
            native.final_values.len(),
            claimed_refs,
            "C1 relation value count"
        );
        Self {
            rounds: native
                .rounds
                .iter()
                .map(|wire| std::array::from_fn(|index| alloc_ext_expr(b, wire[index])))
                .collect(),
            final_values: native
                .final_values
                .iter()
                .copied()
                .map(|value| alloc_ext_expr(b, value))
                .collect(),
        }
    }
}

pub struct C1RelationTermTrace {
    pub coeff: ExtExpr,
    pub factors: Vec<ColRef>,
}

fn c1_structure_lane(low: usize, high: usize) -> ExtExpr {
    ExtExpr::constant(F256::from_base(F128::new(low as u64, high as u64)))
}

fn encode_c1_reference(reference: ColRef, lanes: &mut Vec<ExtExpr>) {
    match reference {
        ColRef::Committed(index) => lanes.push(c1_structure_lane(0, index)),
        ColRef::CommittedShift(index) => lanes.push(c1_structure_lane(1, index)),
        ColRef::Internal(index) => lanes.push(c1_structure_lane(2, index)),
        ColRef::Fixed(index) => lanes.push(c1_structure_lane(3, index)),
        ColRef::CommittedShift2(index) => lanes.push(c1_structure_lane(4, index)),
        ColRef::Window {
            col,
            stride_log,
            offset,
        } => {
            lanes.push(c1_structure_lane(5, col));
            lanes.push(c1_structure_lane(stride_log, offset));
        }
    }
}

fn absorb_c1_relation_header_trace(
    b: &mut FieldR1csBuilder,
    channel: &mut impl FsChannelOps,
    target: &ExtExpr,
    eq_point: &[ExtExpr],
    terms: &[C1RelationTermTrace],
) {
    channel.observe_label(b, b"history-deep-chain-relation-c1-v1");
    channel.observe_f256(b, target);
    channel.observe_f256_slice(b, eq_point);
    let mut structure = vec![c1_structure_lane(terms.len(), 0)];
    for term in terms {
        structure.push(term.coeff.clone());
        structure.push(c1_structure_lane(term.factors.len(), 0));
        for &factor in &term.factors {
            encode_c1_reference(factor, &mut structure);
        }
    }
    channel.observe_f256_slice(b, &structure);
}

fn eq_tensor_extend_ext(
    b: &mut FieldR1csBuilder,
    tensor: &[ExtExpr],
    coordinate: &ExtExpr,
) -> Vec<ExtExpr> {
    let high = tensor
        .iter()
        .map(|value| mul_ext(b, value, coordinate))
        .collect::<Vec<_>>();
    let mut next = Vec::with_capacity(2 * tensor.len());
    for (value, high) in tensor.iter().zip(&high) {
        next.push(value.add(high));
    }
    next.extend(high);
    next
}

fn fixed_pattern_dot_gate_ext(
    b: &mut FieldR1csBuilder,
    pattern: &FixedPattern,
    tensor: &[ExtExpr],
    point: &[ExtExpr],
) -> ExtExpr {
    assert_eq!(tensor.len(), pattern.table.len(), "C1 eq tensor arity");
    let mut layer = pattern
        .table
        .iter()
        .zip(tensor)
        .filter(|(value, _)| **value != F128::ZERO)
        .map(|(&value, tensor)| tensor.scale_base(value))
        .collect::<Vec<_>>();
    if layer.is_empty() {
        layer.push(ExtExpr::zero());
    }
    while layer.len() > 1 {
        layer = layer
            .chunks(2)
            .map(|pair| {
                if pair.len() == 2 {
                    pair[0].add(&pair[1])
                } else {
                    pair[0].clone()
                }
            })
            .collect();
    }
    let mut value = layer.pop().expect("non-empty C1 fixed fold");
    if let Some((first, bits)) = &pattern.hi_gate {
        assert_eq!(
            point.len(),
            first + bits.len(),
            "C1 gated pattern point arity"
        );
        for (coordinate, bit) in bits.iter().enumerate() {
            let factor = if *bit {
                point[first + coordinate].clone()
            } else {
                point[first + coordinate].add(&ExtExpr::one())
            };
            value = mul_ext(b, &value, &factor);
        }
    }
    value
}

pub fn verify_c1_column_relation_trace(
    b: &mut FieldR1csBuilder,
    channel: &mut impl FsChannelOps,
    w_log: usize,
    target: &ExtExpr,
    eq_point: &[ExtExpr],
    terms: &[C1RelationTermTrace],
    fixed: &[FixedPattern],
    proof: &C1ColumnRelationProofTrace,
) -> Vec<ExtExpr> {
    assert_eq!(eq_point.len(), w_log, "C1 relation point arity");
    assert_eq!(proof.rounds.len(), w_log, "C1 relation round count");
    let shape = terms
        .iter()
        .map(|term| {
            assert!(term.factors.len() <= MAX_TERM_FACTORS);
            C1RelationTerm {
                coeff: F256::ZERO,
                factors: term.factors.clone(),
            }
        })
        .collect::<Vec<_>>();
    let claimed = c1_claimed_refs(&shape);
    assert_eq!(proof.final_values.len(), claimed.len());

    absorb_c1_relation_header_trace(b, channel, target, eq_point, terms);
    let mut claim = target.clone();
    let mut point = Vec::with_capacity(w_log);
    for wire in &proof.rounds {
        channel.observe_f256_slice(b, wire);
        let challenge = channel.sample_f256(b);
        claim = compressed_horner_ext(b, wire, &claim, &challenge);
        point.push(challenge);
    }
    channel.observe_f256_slice(b, &proof.final_values);

    let mut fixed_used = Vec::new();
    for term in terms {
        for factor in &term.factors {
            if let ColRef::Fixed(index) = factor {
                if !fixed_used.contains(index) {
                    fixed_used.push(*index);
                }
            }
        }
    }
    fixed_used.sort_by_key(|index| fixed[*index].low_log);
    let mut fixed_cache = vec![None; fixed.len()];
    let mut tensor = vec![ExtExpr::one()];
    let mut current_log = 0usize;
    for index in fixed_used {
        while current_log < fixed[index].low_log {
            tensor = eq_tensor_extend_ext(b, &tensor, &point[current_log]);
            current_log += 1;
        }
        fixed_cache[index] = Some(fixed_pattern_dot_gate_ext(
            b,
            &fixed[index],
            &tensor,
            &point,
        ));
    }

    let mut relation = ExtExpr::zero();
    for term in terms {
        let mut product = term.coeff.clone();
        for factor in &term.factors {
            let value = match factor {
                ColRef::Fixed(index) => fixed_cache[*index]
                    .clone()
                    .expect("pre-evaluated C1 fixed pattern"),
                _ => {
                    let index = claimed
                        .iter()
                        .position(|reference| reference == factor)
                        .expect("claimed C1 relation reference");
                    proof.final_values[index].clone()
                }
            };
            product = mul_ext(b, &product, &value);
        }
        relation = relation.add(&product);
    }
    let equality = eq_eval_ext_trace(b, eq_point, &point);
    let expected = mul_ext(b, &equality, &relation);
    pin_eq_ext(b, &expected, &claim);
    point
}

pub struct C1ShiftDischargeProofTrace {
    pub rounds: Vec<[ExtExpr; 2]>,
    pub final_value: ExtExpr,
}

impl C1ShiftDischargeProofTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &C1ShiftDischargeProof, w_log: usize) -> Self {
        assert_eq!(native.rounds.len(), w_log, "C1 shift round count");
        Self {
            rounds: native
                .rounds
                .iter()
                .map(|wire| std::array::from_fn(|index| alloc_ext_expr(b, wire[index])))
                .collect(),
            final_value: alloc_ext_expr(b, native.final_value),
        }
    }
}

fn c1_shift_kernel_eval_trace(
    b: &mut FieldR1csBuilder,
    rho: &[ExtExpr],
    sigma: &[ExtExpr],
) -> ExtExpr {
    assert_eq!(rho.len(), sigma.len(), "C1 shift point arity");
    let mut suffix = vec![ExtExpr::one(); rho.len() + 1];
    for coordinate in (0..rho.len()).rev() {
        let matched = ExtExpr::one().add(&rho[coordinate]).add(&sigma[coordinate]);
        suffix[coordinate] = mul_ext(b, &matched, &suffix[coordinate + 1]);
    }
    let mut result = ExtExpr::zero();
    let mut prefix = ExtExpr::one();
    for coordinate in 0..rho.len() {
        let with_rho = mul_ext(b, &prefix, &rho[coordinate]);
        let transition = mul_ext(b, &with_rho, &ExtExpr::one().add(&sigma[coordinate]));
        result = result.add(&mul_ext(b, &transition, &suffix[coordinate + 1]));
        let with_sigma = mul_ext(b, &prefix, &sigma[coordinate]);
        prefix = mul_ext(b, &with_sigma, &ExtExpr::one().add(&rho[coordinate]));
    }
    result
}

fn c1_shift_pow2_kernel_eval_trace(
    b: &mut FieldR1csBuilder,
    shift_log: usize,
    rho: &[ExtExpr],
    sigma: &[ExtExpr],
) -> ExtExpr {
    assert_eq!(rho.len(), sigma.len(), "C1 shift point arity");
    assert!(shift_log < rho.len(), "C1 shift below domain");
    let mut low_match = ExtExpr::one();
    for coordinate in 0..shift_log {
        let matched = ExtExpr::one().add(&rho[coordinate]).add(&sigma[coordinate]);
        low_match = mul_ext(b, &low_match, &matched);
    }
    let high = c1_shift_kernel_eval_trace(b, &rho[shift_log..], &sigma[shift_log..]);
    mul_ext(b, &low_match, &high)
}

pub fn verify_c1_shift_discharge_trace(
    b: &mut FieldR1csBuilder,
    channel: &mut impl FsChannelOps,
    w_log: usize,
    sigma: &[ExtExpr],
    target: &ExtExpr,
    shift_log: usize,
    proof: &C1ShiftDischargeProofTrace,
) -> Vec<ExtExpr> {
    assert_eq!(sigma.len(), w_log, "C1 shift point arity");
    assert_eq!(proof.rounds.len(), w_log, "C1 shift round count");
    assert!(shift_log < w_log, "C1 shift below domain");
    channel.observe_label(b, b"history-deep-chain-shift-c1-v1");
    channel.observe_f256(b, &c1_structure_lane(shift_log, 0));
    channel.observe_f256(b, target);
    channel.observe_f256_slice(b, sigma);

    let mut claim = target.clone();
    let mut point = Vec::with_capacity(w_log);
    for wire in &proof.rounds {
        channel.observe_f256_slice(b, wire);
        let linear = claim.add(&wire[1]);
        let challenge = channel.sample_f256(b);
        let quadratic = mul_ext(b, &wire[1], &challenge);
        let linearized = quadratic.add(&linear);
        claim = mul_ext(b, &linearized, &challenge).add(&wire[0]);
        point.push(challenge);
    }
    channel.observe_f256(b, &proof.final_value);
    let kernel = c1_shift_pow2_kernel_eval_trace(b, shift_log, sigma, &point);
    let expected = mul_ext(b, &kernel, &proof.final_value);
    pin_eq_ext(b, &expected, &claim);
    point
}

// ---------------------------------------------------------------------------
// Column-relation verifier twin
// ---------------------------------------------------------------------------

/// Witness allocation of a [`ColumnRelationProof`].
pub struct ColumnRelationProofTrace {
    pub rounds: Vec<[LinExpr; RELATION_DEGREE]>,
    pub final_values: Vec<LinExpr>,
}

impl ColumnRelationProofTrace {
    pub fn alloc(
        b: &mut FieldR1csBuilder,
        native: &ColumnRelationProof,
        w_log: usize,
        n_refs: usize,
    ) -> Self {
        assert_eq!(native.rounds.len(), w_log, "relation round count");
        assert_eq!(native.final_values.len(), n_refs, "relation value count");
        Self {
            rounds: native
                .rounds
                .iter()
                .map(|wire| std::array::from_fn(|i| alloc_expr(b, wire[i])))
                .collect(),
            final_values: native
                .final_values
                .iter()
                .map(|&v| alloc_expr(b, v))
                .collect(),
        }
    }
}

/// The relation term list as the trace consumes it: structure (factor refs)
/// is a protocol constant; coefficients may be expressions (challenge-
/// derived, e.g. the α-batched MDS weights of a wiring substitution).
pub struct RelationTermTrace {
    pub coeff: LinExpr,
    pub factors: Vec<ColRef>,
}

/// The native header absorbs `(target, eq_point, structure lanes)`; the
/// twin mirrors it with the structure lanes as constants. The structure
/// lanes bind ONLY the term/factor encoding — coefficients are absorbed as
/// expressions so challenge-derived coefficients stay sound.
fn absorb_relation_header_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut impl FsChannelOps,
    target: &LinExpr,
    eq_point: &[LinExpr],
    terms: &[RelationTermTrace],
) {
    ch.observe_label(b, b"history-deep-chain-relation-v0");
    ch.observe_f128(b, target);
    ch.observe_f128_slice(b, eq_point);
    let lane = |a: u64, bb: u64| LinExpr::constant(F128 { lo: a, hi: bb });
    let mut lanes = vec![lane(terms.len() as u64, 0)];
    for t in terms {
        lanes.push(t.coeff.clone());
        lanes.push(lane(t.factors.len() as u64, 0));
        for f in &t.factors {
            match f {
                ColRef::Committed(i) => lanes.push(lane(0, *i as u64)),
                ColRef::CommittedShift(i) => lanes.push(lane(1, *i as u64)),
                ColRef::Internal(i) => lanes.push(lane(2, *i as u64)),
                ColRef::Fixed(i) => lanes.push(lane(3, *i as u64)),
                ColRef::CommittedShift2(i) => lanes.push(lane(4, *i as u64)),
                ColRef::Window {
                    col,
                    stride_log,
                    offset,
                } => {
                    lanes.push(lane(5, *col as u64));
                    lanes.push(lane(*stride_log as u64, *offset as u64));
                }
            }
        }
    }
    ch.observe_f128_slice(b, &lanes);
}

/// One doubling step of the eq tensor (mirrors `build_eq_table`: the new
/// variable is the HIGH bit; `(1+p)·t = t + p·t`, one multiplication per
/// parent entry).
fn eq_tensor_extend(b: &mut FieldR1csBuilder, tensor: &[LinExpr], p_j: &LinExpr) -> Vec<LinExpr> {
    let his: Vec<LinExpr> = tensor.iter().map(|t| mul(b, t, p_j)).collect();
    let mut next = Vec::with_capacity(tensor.len() * 2);
    for (t, hi) in tensor.iter().zip(his.iter()) {
        next.push(t.add(hi));
    }
    next.extend(his);
    next
}

/// Dot a pattern's constant table with a prebuilt eq tensor of its low
/// coordinates (zero rows — a pure linear combination), then apply the
/// hi-gate factors (`ρ_j` / `1+ρ_j` per pinned coordinate).
fn fixed_pattern_dot_gate(
    b: &mut FieldR1csBuilder,
    pattern: &FixedPattern,
    tensor: &[LinExpr],
    point: &[LinExpr],
) -> LinExpr {
    assert_eq!(tensor.len(), pattern.table.len(), "eq tensor arity");
    // Balanced affine fold: `LinExpr::add` copies both sides, so a linear
    // accumulation over a 2^14-entry table would cost O(n²) term copies.
    // The pairwise tree produces the identical canonical expression (sorted
    // merge is order-independent) in O(n log n).
    let mut layer: Vec<LinExpr> = pattern
        .table
        .iter()
        .zip(tensor.iter())
        .filter(|(v, _)| **v != F128::ZERO)
        .map(|(v, t)| t.scale(*v))
        .collect();
    if layer.is_empty() {
        layer.push(LinExpr::zero());
    }
    while layer.len() > 1 {
        layer = layer
            .chunks(2)
            .map(|pair| {
                if pair.len() == 2 {
                    pair[0].add(&pair[1])
                } else {
                    pair[0].clone()
                }
            })
            .collect();
    }
    let mut acc = layer.pop().expect("non-empty fold layer");
    if let Some((first, bits)) = &pattern.hi_gate {
        assert_eq!(point.len(), first + bits.len(), "gated pattern point arity");
        for (j, bit) in bits.iter().enumerate() {
            let p = &point[first + j];
            let f = if *bit {
                p.clone()
            } else {
                p.add_const(F128::ONE)
            };
            acc = mul(b, &acc, &f);
        }
    }
    acc
}

/// Closed-form MLE evaluation of a [`FixedPattern`] at an expression point:
/// build the eq tensor of the low `low_log` coordinates (2^low_log − 1
/// multiplications), then dot it with the constant table (zero rows) and
/// apply the hi-gate factors, if any.
pub fn fixed_pattern_eval_trace(
    b: &mut FieldR1csBuilder,
    pattern: &FixedPattern,
    point: &[LinExpr],
) -> LinExpr {
    assert!(point.len() >= pattern.low_log, "fixed pattern point arity");
    let mut tensor: Vec<LinExpr> = vec![LinExpr::constant(F128::ONE)];
    for p_j in &point[..pattern.low_log] {
        tensor = eq_tensor_extend(b, &tensor, p_j);
    }
    fixed_pattern_dot_gate(b, pattern, &tensor, point)
}

/// Trace twin of `relations::verify_column_relation`; returns the derived
/// point (final claim values live in `proof.final_values`, ordered by
/// [`claimed_refs`]-equivalent structure order; Fixed factors are
/// evaluated in closed form from the protocol-constant patterns).
pub fn verify_column_relation_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut impl FsChannelOps,
    w_log: usize,
    target: &LinExpr,
    eq_point: &[LinExpr],
    terms: &[RelationTermTrace],
    fixed: &[FixedPattern],
    proof: &ColumnRelationProofTrace,
) -> Vec<LinExpr> {
    assert_eq!(eq_point.len(), w_log);
    assert_eq!(proof.rounds.len(), w_log);
    let native_shape: Vec<RelationTerm> = terms
        .iter()
        .map(|t| {
            assert!(t.factors.len() <= MAX_TERM_FACTORS);
            RelationTerm {
                coeff: F128::ZERO,
                factors: t.factors.clone(),
            }
        })
        .collect();
    let claimed = claimed_refs(&native_shape);
    assert_eq!(proof.final_values.len(), claimed.len());

    absorb_relation_header_trace(b, ch, target, eq_point, terms);

    let mut claim = target.clone();
    let mut point = Vec::with_capacity(w_log);
    for wire in &proof.rounds {
        ch.observe_f128_slice(b, wire);
        let r = ch.sample_f128(b);
        claim = compressed_horner(b, wire, &claim, &r);
        point.push(r);
    }
    ch.observe_f128_slice(b, &proof.final_values);

    // Each distinct Fixed ref is evaluated once per relation, and ALL the
    // relation's patterns share ONE incrementally-built eq tensor (each
    // pattern reads the 2^low_log prefix stage it needs) — n patterns of a
    // common period cost one tensor, not n.
    let mut fixed_used: Vec<usize> = Vec::new();
    for t in terms {
        for f in &t.factors {
            if let ColRef::Fixed(i) = f {
                if !fixed_used.contains(i) {
                    fixed_used.push(*i);
                }
            }
        }
    }
    let mut fixed_cache: Vec<Option<LinExpr>> = vec![None; fixed.len()];
    {
        let mut by_low = fixed_used.clone();
        by_low.sort_by_key(|i| fixed[*i].low_log);
        let mut tensor: Vec<LinExpr> = vec![LinExpr::constant(F128::ONE)];
        let mut cur_log = 0usize;
        for i in by_low {
            while cur_log < fixed[i].low_log {
                tensor = eq_tensor_extend(b, &tensor, &point[cur_log]);
                cur_log += 1;
            }
            fixed_cache[i] = Some(fixed_pattern_dot_gate(b, &fixed[i], &tensor, &point));
        }
    }
    let mut sum = LinExpr::zero();
    for t in terms {
        let mut prod = t.coeff.clone();
        for f in &t.factors {
            let value = match f {
                ColRef::Fixed(i) => fixed_cache[*i].clone().expect("pre-evaluated"),
                _ => {
                    let fi = claimed.iter().position(|r| r == f).expect("claimed ref");
                    proof.final_values[fi].clone()
                }
            };
            prod = mul(b, &prod, &value);
        }
        sum = sum.add(&prod);
    }
    let eq = b.eq_eval_trace(eq_point, &point);
    let expected = mul(b, &eq, &sum);
    pin_eq(b, &expected, &claim);
    point
}

// ---------------------------------------------------------------------------
// Shift-discharge verifier twin
// ---------------------------------------------------------------------------

pub struct ShiftDischargeProofTrace {
    pub rounds: Vec<[LinExpr; 2]>,
    pub final_value: LinExpr,
}

impl ShiftDischargeProofTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &ShiftDischargeProof, w_log: usize) -> Self {
        assert_eq!(native.rounds.len(), w_log, "shift round count");
        Self {
            rounds: native
                .rounds
                .iter()
                .map(|wire| std::array::from_fn(|i| alloc_expr(b, wire[i])))
                .collect(),
            final_value: alloc_expr(b, native.final_value),
        }
    }
}

/// Closed-form successor kernel `N(ρ, σ)` on expressions (see
/// `relations::shift_kernel_eval`): prefix/suffix products over the
/// coordinate pairs — O(n) multiplications.
pub fn shift_kernel_eval_trace(
    b: &mut FieldR1csBuilder,
    rho: &[LinExpr],
    sigma: &[LinExpr],
) -> LinExpr {
    assert_eq!(rho.len(), sigma.len());
    let n = rho.len();
    let one = LinExpr::constant(F128::ONE);
    let mut suffix = vec![LinExpr::constant(F128::ONE); n + 1];
    for i in (0..n).rev() {
        let m1 = mul(b, &rho[i], &sigma[i]);
        let m2 = mul(b, &one.add(&rho[i]), &one.add(&sigma[i]));
        let matched = m1.add(&m2);
        suffix[i] = mul(b, &matched, &suffix[i + 1]);
    }
    let mut acc = LinExpr::zero();
    let mut prefix = LinExpr::constant(F128::ONE);
    for k in 0..n {
        let t1 = mul(b, &prefix, &rho[k]);
        let t2 = mul(b, &t1, &one.add(&sigma[k]));
        acc = acc.add(&mul(b, &t2, &suffix[k + 1]));
        let p1 = mul(b, &prefix, &sigma[k]);
        prefix = mul(b, &p1, &one.add(&rho[k]));
    }
    acc
}

/// `2^shift_log`-step kernel on expressions (see
/// `relations::shift_pow2_kernel_eval`): matched low coordinates times the
/// successor kernel on the rest.
pub fn shift_pow2_kernel_eval_trace(
    b: &mut FieldR1csBuilder,
    shift_log: usize,
    rho: &[LinExpr],
    sigma: &[LinExpr],
) -> LinExpr {
    assert_eq!(rho.len(), sigma.len());
    assert!(shift_log < rho.len());
    let one = LinExpr::constant(F128::ONE);
    let mut acc = LinExpr::constant(F128::ONE);
    for i in 0..shift_log {
        let m1 = mul(b, &rho[i], &sigma[i]);
        let m2 = mul(b, &one.add(&rho[i]), &one.add(&sigma[i]));
        let matched = m1.add(&m2);
        acc = mul(b, &acc, &matched);
    }
    let high = shift_kernel_eval_trace(b, &rho[shift_log..], &sigma[shift_log..]);
    mul(b, &acc, &high)
}

/// Trace twin of `relations::verify_shift_discharge` (and its
/// `2^shift_log` variant); returns the derived point (pair it with
/// `proof.final_value` as the plain column claim).
pub fn verify_shift_discharge_trace(
    b: &mut FieldR1csBuilder,
    ch: &mut impl FsChannelOps,
    w_log: usize,
    sigma: &[LinExpr],
    target: &LinExpr,
    shift_log: usize,
    proof: &ShiftDischargeProofTrace,
) -> Vec<LinExpr> {
    assert_eq!(sigma.len(), w_log);
    assert_eq!(proof.rounds.len(), w_log);
    assert!(shift_log < w_log);

    ch.observe_label(b, b"history-deep-chain-shift-v0");
    ch.observe_f128(
        b,
        &LinExpr::constant(F128 {
            lo: shift_log as u64,
            hi: 0,
        }),
    );
    ch.observe_f128(b, target);
    ch.observe_f128_slice(b, sigma);

    let mut claim = target.clone();
    let mut point = Vec::with_capacity(w_log);
    for wire in &proof.rounds {
        ch.observe_f128_slice(b, wire);
        // Degree 2: c_1 = claim + c_2; p(r) = (c_2·r + c_1)·r + c_0.
        let c1 = claim.add(&wire[1]);
        let r = ch.sample_f128(b);
        let t = mul(b, &wire[1], &r);
        let t = mul(b, &t.add(&c1), &r);
        claim = t.add(&wire[0]);
        point.push(r);
    }
    ch.observe_f128(b, &proof.final_value);

    let kernel = shift_pow2_kernel_eval_trace(b, shift_log, sigma, &point);
    let expected = mul(b, &kernel, &proof.final_value);
    pin_eq(b, &expected, &claim);
    point
}

// ---------------------------------------------------------------------------
// Weighted-sum discharge verifier twin + source-binding encode kernel
// ---------------------------------------------------------------------------

pub struct WeightedSumProofTrace {
    pub rounds: Vec<[LinExpr; 2]>,
    pub final_value: LinExpr,
}

impl WeightedSumProofTrace {
    pub fn alloc(b: &mut FieldR1csBuilder, native: &WeightedSumProof, w_log: usize) -> Self {
        assert_eq!(native.rounds.len(), w_log, "weighted-sum round count");
        Self {
            rounds: native
                .rounds
                .iter()
                .map(|wire| std::array::from_fn(|i| alloc_expr(b, wire[i])))
                .collect(),
            final_value: alloc_expr(b, native.final_value),
        }
    }
}

/// Trace twin of `relations::verify_weighted_sum`: the degree-2 sumcheck
/// `Σ_i weights[i]·col[i] = target` reduced to a plain `col~(point)` claim.
/// `weight_eval` builds `weights~(point)` as an expression from the derived
/// point (the closed-form kernel — only known after the rounds are drawn),
/// mirroring the native callback. Returns the derived point.
pub fn verify_weighted_sum_trace<W>(
    b: &mut FieldR1csBuilder,
    ch: &mut impl FsChannelOps,
    w_log: usize,
    target: &LinExpr,
    proof: &WeightedSumProofTrace,
    weight_eval: W,
) -> Vec<LinExpr>
where
    W: FnOnce(&mut FieldR1csBuilder, &[LinExpr]) -> LinExpr,
{
    assert_eq!(proof.rounds.len(), w_log);
    ch.observe_label(b, b"history-deep-chain-weighted-v0");
    ch.observe_f128(b, target);

    let mut claim = target.clone();
    let mut point = Vec::with_capacity(w_log);
    for wire in &proof.rounds {
        ch.observe_f128_slice(b, wire);
        // Degree 2: c_1 = claim + c_2; p(r) = (c_2·r + c_1)·r + c_0.
        let c1 = claim.add(&wire[1]);
        let r = ch.sample_f128(b);
        let t = mul(b, &wire[1], &r);
        let t = mul(b, &t.add(&c1), &r);
        claim = t.add(&wire[0]);
        point.push(r);
    }
    ch.observe_f128(b, &proof.final_value);

    let weight = weight_eval(b, &point);
    let expected = mul(b, &weight, &proof.final_value);
    pin_eq(b, &expected, &claim);
    point
}

/// `eq(right, x) = Π_l [right_l·x_l + (1+right_l)(1+x_l)]` on expressions —
/// the H-claim discharge weight (`H~(right) = Σ_i eq(right,i)·H[i]`), and the
/// closed-form `weights~(point)` callback for [`verify_weighted_sum_trace`].
pub fn eq_at_trace(b: &mut FieldR1csBuilder, right: &[LinExpr], x: &[LinExpr]) -> LinExpr {
    assert_eq!(right.len(), x.len(), "eq arity");
    let one = LinExpr::constant(F128::ONE);
    let mut acc = one.clone();
    for (r, xx) in right.iter().zip(x.iter()) {
        let hit = mul(b, r, xx);
        let miss = mul(b, &one.add(r), &one.add(xx));
        acc = mul(b, &acc, &hit.add(&miss));
    }
    acc
}

/// Trace twin of `encode_kernel::source_weight_at`: the MLE of the
/// source-binding weight sequence `W_i = K_i(z)·eq(right,i)` at an expression
/// point `x`. Flat-basis twiddles `tower_to_flat(2^{c+l})` are constants, so
/// the only multiplications are the per-bit tensor folds — `O(n_rounds)`.
pub fn source_weight_at_trace(
    b: &mut FieldR1csBuilder,
    z: &[LinExpr],
    right: &[LinExpr],
    x: &[LinExpr],
    n_rounds: usize,
) -> LinExpr {
    assert_eq!(z.len(), n_rounds + 2, "encode kernel point arity");
    assert_eq!(right.len(), n_rounds, "right arity");
    assert_eq!(x.len(), n_rounds, "message point arity");
    let z_pos = &z[..n_rounds];
    let z_hi = &z[n_rounds..];
    let one = LinExpr::constant(F128::ONE);
    let mut total = LinExpr::zero();
    for c in 0..4usize {
        // eq₂(z_hi; c).
        let mut eq2 = one.clone();
        for (k, zk) in z_hi.iter().enumerate() {
            let factor = if (c >> k) & 1 == 1 {
                zk.clone()
            } else {
                one.add(zk)
            };
            eq2 = mul(b, &eq2, &factor);
        }
        // Π_l [ h_l(0)(1+x_l) + h_l(1)·x_l ], h_l(bit) = f_l(bit)·g_l(bit).
        let mut prod = one.clone();
        for l in 0..n_rounds {
            let two = LinExpr::constant(flat_of_tower_u128(1u128 << (c + l)));
            // f0 = 1 + z_l·(1+two); f1 = 1 + z_l·two (mul-by-const folds).
            let f0 = one.add(&mul(b, &z_pos[l], &one.add(&two)));
            let f1 = one.add(&mul(b, &z_pos[l], &two));
            let g0 = one.add(&right[l]);
            let g1 = right[l].clone();
            let h0 = mul(b, &f0, &g0);
            let h1 = mul(b, &f1, &g1);
            let lo = mul(b, &h0, &one.add(&x[l]));
            let hi = mul(b, &h1, &x[l]);
            let term = lo.add(&hi);
            prod = mul(b, &prod, &term);
        }
        total = total.add(&mul(b, &eq2, &prod));
    }
    total
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use noid_ivc_core::challenger::{Challenger, FsLaneChallenger};
    use noid_ivc_core::deep_chain::relations::{
        prove_column_relation, prove_shift_discharge, RelationColumns,
    };
    use noid_ivc_core::deep_chain::{
        apply_round, prove_deep_chain_walk, prove_multi_deep_chain_walk,
        prove_ragged_multi_deep_chain_walk, LaneClaimGroup,
    };
    use noid_ivc_core::lincheck::build_eq_table;

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

        fn f256(&mut self) -> F256 {
            F256::new(self.f128(), self.f128())
        }
    }

    fn mle_eval(col: &[F128], point: &[F128]) -> F128 {
        let eq = build_eq_table(point);
        let mut acc = F128::ZERO;
        for (v, e) in col.iter().zip(eq.iter()) {
            acc += *v * *e;
        }
        acc
    }

    fn mle_eval_ext(col: &[F128], point: &[F256]) -> F256 {
        assert_eq!(col.len(), 1usize << point.len());
        let mut folded = col.iter().copied().map(F256::from_base).collect::<Vec<_>>();
        for &challenge in point {
            folded = folded
                .chunks_exact(2)
                .map(|pair| pair[0] + challenge * (pair[0] + pair[1]))
                .collect();
        }
        folded[0]
    }

    fn mle_eval_f256(values: &[F256], point: &[F256]) -> F256 {
        assert_eq!(values.len(), 1usize << point.len());
        let mut folded = values.to_vec();
        for &challenge in point {
            folded = folded
                .chunks_exact(2)
                .map(|pair| pair[0] + challenge * (pair[0] + pair[1]))
                .collect();
        }
        folded[0]
    }

    /// Walk twin: lockstep with the native verifier, satisfiable trace,
    /// proof-wire auto-mutator with 0 survivors, measured row count.
    #[test]
    fn walk_twin_lockstep_and_mutations() {
        let w_log = 3;
        let w = 1usize << w_log;
        let mut rng = Rng(0x7A1C);
        let s0: [Vec<F128>; STATE_SIZE] =
            std::array::from_fn(|_| (0..w).map(|_| rng.f128()).collect());
        let mut out: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
        for widx in 0..w {
            let mut state: [F128; STATE_SIZE] = std::array::from_fn(|j| s0[j][widx]);
            for q in 0..N_ROUNDS {
                state = apply_round(q, state);
            }
            for j in 0..STATE_SIZE {
                out[j][widx] = state[j];
            }
        }
        let point: Vec<F128> = (0..w_log).map(|_| rng.f128()).collect();
        let values: [F128; STATE_SIZE] = std::array::from_fn(|j| mle_eval(&out[j], &point));
        let groups = [LaneClaimGroup {
            point: point.clone(),
            values,
        }];

        let mut ch_native = FsLaneChallenger::new(b"walk-twin-test");
        let (proof, native_terminal) = prove_deep_chain_walk(&s0, &groups, &mut ch_native);

        let mut b = FieldR1csBuilder::new();
        let mut ch = FsChannelTrace::new(&mut b, b"walk-twin-test");
        let groups_e = [LaneClaimGroupTrace {
            point: point.iter().map(|&v| alloc_expr(&mut b, v)).collect(),
            values: std::array::from_fn(|j| alloc_expr(&mut b, values[j])),
        }];
        let mutation_start = b.num_wires();
        let proof_e = DeepChainWalkProofTrace::alloc(&mut b, &proof, w_log);
        let mutation_end = b.num_wires();
        let terminal = verify_deep_chain_walk_trace(&mut b, &mut ch, w_log, &groups_e, &proof_e);
        let rows = b.num_wires();

        // Lockstep + terminal agreement.
        let c_n = ch_native.sample_f128();
        let c_t = ch.sample_f128(&mut b);
        assert_eq!(c_t.eval(b.values()), c_n, "walk twin transcript diverged");
        for j in 0..STATE_SIZE {
            assert_eq!(
                terminal.values[j].eval(b.values()),
                native_terminal.values[j],
                "terminal value lane {j}"
            );
        }
        eprintln!("[deep-chain] walk twin rows @w_log={w_log}: {rows}");

        let (r1cs, z) = b.build();
        assert!(r1cs.satisfies(&z), "honest walk twin unsatisfiable");

        use rayon::prelude::*;
        let survivors: Vec<usize> = (mutation_start..mutation_end)
            .into_par_iter()
            .filter(|&t| {
                let mut bad = z.clone();
                bad[t] += F128::ONE;
                r1cs.satisfies(&bad)
            })
            .collect();
        assert!(survivors.is_empty(), "walk twin survivors: {survivors:?}");
    }

    /// Equal-domain multi-walk twin: native/trace lockstep, exact verifier-row
    /// comparison against two sequential V0 walks, and targeted cross-instance
    /// mutation checks with the returned terminals discharged.
    #[test]
    fn multi_walk_twin_lockstep_rows_and_mutations() {
        let w_log = 2;
        let w = 1usize << w_log;
        let mut rng = Rng(0xB471_CE11);
        let instances = (0..2)
            .map(|_| std::array::from_fn(|_| (0..w).map(|_| rng.f128()).collect::<Vec<_>>()))
            .collect::<Vec<[Vec<F128>; STATE_SIZE]>>();
        let outputs = instances
            .iter()
            .map(|s0| {
                let mut out: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
                for widx in 0..w {
                    let mut state: [F128; STATE_SIZE] = std::array::from_fn(|lane| s0[lane][widx]);
                    for q in 0..N_ROUNDS {
                        state = apply_round(q, state);
                    }
                    for lane in 0..STATE_SIZE {
                        out[lane][widx] = state[lane];
                    }
                }
                out
            })
            .collect::<Vec<_>>();
        let groups = outputs
            .iter()
            .enumerate()
            .map(|(instance, output)| {
                (0..=instance)
                    .map(|_| {
                        let point = (0..w_log).map(|_| rng.f128()).collect::<Vec<_>>();
                        let values = std::array::from_fn(|lane| mle_eval(&output[lane], &point));
                        LaneClaimGroup { point, values }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert_eq!(groups.iter().map(Vec::len).collect::<Vec<_>>(), [1, 2]);

        let instance_refs = instances.iter().collect::<Vec<_>>();
        let mut ch_native = FsLaneChallenger::new(b"multi-walk-twin-test");
        let (proof, native_terminals) =
            prove_multi_deep_chain_walk(&instance_refs, &groups, &mut ch_native);

        let mut b = FieldR1csBuilder::new();
        let mut ch = FsChannelTrace::new(&mut b, b"multi-walk-twin-test");
        let groups_e = groups
            .iter()
            .map(|instance_groups| {
                instance_groups
                    .iter()
                    .map(|group| LaneClaimGroupTrace {
                        point: group
                            .point
                            .iter()
                            .map(|&value| alloc_expr(&mut b, value))
                            .collect(),
                        values: std::array::from_fn(|lane| alloc_expr(&mut b, group.values[lane])),
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let verifier_start = b.num_wires();
        let mutation_start = b.num_wires();
        let proof_e = MultiDeepChainWalkProofTrace::alloc(&mut b, &proof, w_log, instances.len());
        let mutation_end = b.num_wires();
        let terminals =
            verify_multi_deep_chain_walk_trace(&mut b, &mut ch, w_log, &groups_e, &proof_e);
        let multi_rows = b.num_wires() - verifier_start;

        let c_native = ch_native.sample_f128();
        let c_trace = ch.sample_f128(&mut b);
        assert_eq!(
            c_trace.eval(b.values()),
            c_native,
            "multi-walk twin transcript diverged"
        );
        assert_eq!(terminals.len(), native_terminals.len());
        for ((terminal, native), s0) in terminals.iter().zip(&native_terminals).zip(&instances) {
            for (coordinate, native_coordinate) in terminal.point.iter().zip(&native.point) {
                assert_eq!(coordinate.eval(b.values()), *native_coordinate);
                pin_eq(&mut b, coordinate, &LinExpr::constant(*native_coordinate));
            }
            for lane in 0..STATE_SIZE {
                assert_eq!(terminal.values[lane].eval(b.values()), native.values[lane]);
                assert_eq!(
                    mle_eval(&s0[lane], &native.point),
                    native.values[lane],
                    "dishonest native terminal lane {lane}"
                );
                pin_eq(
                    &mut b,
                    &terminal.values[lane],
                    &LinExpr::constant(native.values[lane]),
                );
            }
        }

        // Baseline the exact same two instances as sequential V0 walks on one
        // transcript. Input-claim allocations are excluded from both counts.
        let mut separate_native_ch = FsLaneChallenger::new(b"multi-walk-separate-test");
        let mut separate_proofs = Vec::with_capacity(instances.len());
        for (s0, instance_groups) in instances.iter().zip(&groups) {
            let (separate_proof, _) =
                prove_deep_chain_walk(s0, instance_groups, &mut separate_native_ch);
            separate_proofs.push(separate_proof);
        }
        let mut separate_builder = FieldR1csBuilder::new();
        let mut separate_ch =
            FsChannelTrace::new(&mut separate_builder, b"multi-walk-separate-test");
        let separate_groups_e = groups
            .iter()
            .map(|instance_groups| {
                instance_groups
                    .iter()
                    .map(|group| LaneClaimGroupTrace {
                        point: group
                            .point
                            .iter()
                            .map(|&value| alloc_expr(&mut separate_builder, value))
                            .collect(),
                        values: std::array::from_fn(|lane| {
                            alloc_expr(&mut separate_builder, group.values[lane])
                        }),
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let separate_start = separate_builder.num_wires();
        for (instance_groups, separate_proof) in separate_groups_e.iter().zip(&separate_proofs) {
            let separate_proof_e =
                DeepChainWalkProofTrace::alloc(&mut separate_builder, separate_proof, w_log);
            verify_deep_chain_walk_trace(
                &mut separate_builder,
                &mut separate_ch,
                w_log,
                instance_groups,
                &separate_proof_e,
            );
        }
        let separate_rows = separate_builder.num_wires() - separate_start;
        let separate_native_post = separate_native_ch.sample_f128();
        let separate_trace_post = separate_ch.sample_f128(&mut separate_builder);
        assert_eq!(
            separate_trace_post.eval(separate_builder.values()),
            separate_native_post,
            "sequential V0 baseline transcript diverged"
        );
        assert!(
            multi_rows < separate_rows,
            "multi-walk did not save verifier rows: multi={multi_rows}, separate={separate_rows}"
        );
        eprintln!(
            "[deep-chain] multi walk twin rows @instances=2,w_log={w_log}: \
             multi={multi_rows}, separate={separate_rows}, saved={}",
            separate_rows - multi_rows
        );

        let per_layer = w_log * WALK_DEGREE + instances.len() * STATE_SIZE;
        assert_eq!(
            mutation_end - mutation_start,
            N_ROUNDS * per_layer,
            "unexpected multi-proof wire layout"
        );
        let (r1cs, z) = b.build();
        assert!(r1cs.satisfies(&z), "honest multi-walk twin unsatisfiable");

        let coeff_wire = mutation_start + (N_ROUNDS / 2) * per_layer + WALK_DEGREE + 3;
        let mut bad_coeff = z.clone();
        bad_coeff[coeff_wire] += F128::ONE;
        assert!(
            !r1cs.satisfies(&bad_coeff),
            "aggregate round-coefficient mutation survived"
        );

        let next_values_offset = w_log * WALK_DEGREE;
        let one_instance_wire =
            mutation_start + (N_ROUNDS / 4) * per_layer + next_values_offset + STATE_SIZE + 2;
        let mut bad_instance = z.clone();
        bad_instance[one_instance_wire] += F128::ONE;
        assert!(
            !r1cs.satisfies(&bad_instance),
            "one-instance next-value mutation survived"
        );

        let swap_base = mutation_start + (N_ROUNDS / 3) * per_layer + next_values_offset;
        assert!(
            (0..STATE_SIZE).any(|lane| z[swap_base + lane] != z[swap_base + STATE_SIZE + lane]),
            "chosen instance next-value vectors unexpectedly coincide"
        );
        let mut swapped = z.clone();
        for lane in 0..STATE_SIZE {
            swapped.swap(swap_base + lane, swap_base + STATE_SIZE + lane);
        }
        assert!(
            !r1cs.satisfies(&swapped),
            "cross-instance next-value swap survived"
        );
    }

    /// Ragged-domain V2 twin: mixed native widths stay unpadded, the trace is
    /// transcript-identical to the native verifier, returned points have their
    /// per-instance arity, and the shared proof is cheaper than two individual
    /// walk replays while targeted coefficient/value/swap mutations fail.
    #[test]
    fn ragged_multi_walk_twin_lockstep_differential_and_mutations() {
        let w_logs = [1usize, 3];
        let max_w_log = *w_logs.iter().max().unwrap();
        let mut rng = Rng(0xA11D_CE11);
        let instances = w_logs
            .iter()
            .map(|&w_log| {
                let w = 1usize << w_log;
                std::array::from_fn(|_| (0..w).map(|_| rng.f128()).collect::<Vec<_>>())
            })
            .collect::<Vec<[Vec<F128>; STATE_SIZE]>>();
        let outputs = instances
            .iter()
            .map(|s0| {
                let w = s0[0].len();
                let mut out: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
                for widx in 0..w {
                    let mut state: [F128; STATE_SIZE] = std::array::from_fn(|lane| s0[lane][widx]);
                    for q in 0..N_ROUNDS {
                        state = apply_round(q, state);
                    }
                    for lane in 0..STATE_SIZE {
                        out[lane][widx] = state[lane];
                    }
                }
                out
            })
            .collect::<Vec<_>>();
        let groups = outputs
            .iter()
            .zip(&w_logs)
            .enumerate()
            .map(|(instance, (output, &w_log))| {
                (0..=instance)
                    .map(|_| {
                        let point = (0..w_log).map(|_| rng.f128()).collect::<Vec<_>>();
                        let values = std::array::from_fn(|lane| mle_eval(&output[lane], &point));
                        LaneClaimGroup { point, values }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let instance_refs = instances.iter().collect::<Vec<_>>();
        let mut ch_native = FsLaneChallenger::new(b"ragged-multi-walk-twin-test");
        let (proof, native_terminals) =
            prove_ragged_multi_deep_chain_walk(&instance_refs, &groups, &mut ch_native);

        let mut b = FieldR1csBuilder::new();
        let mut ch = FsChannelTrace::new(&mut b, b"ragged-multi-walk-twin-test");
        let groups_e = groups
            .iter()
            .map(|instance_groups| {
                instance_groups
                    .iter()
                    .map(|group| LaneClaimGroupTrace {
                        point: group
                            .point
                            .iter()
                            .map(|&value| alloc_expr(&mut b, value))
                            .collect(),
                        values: std::array::from_fn(|lane| alloc_expr(&mut b, group.values[lane])),
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let verifier_start = b.num_wires();
        let mutation_start = b.num_wires();
        let proof_e = MultiDeepChainWalkProofTrace::alloc_ragged(&mut b, &proof, &w_logs);
        let mutation_end = b.num_wires();
        let terminals = verify_ragged_multi_deep_chain_walk_trace(
            &mut b, &mut ch, &w_logs, &groups_e, &proof_e,
        );
        let ragged_rows = b.num_wires() - verifier_start;

        let native_post = ch_native.sample_f128();
        let trace_post = ch.sample_f128(&mut b);
        assert_eq!(
            trace_post.eval(b.values()),
            native_post,
            "ragged multi-walk twin transcript diverged"
        );
        for (instance, (((terminal, native), s0), &w_log)) in terminals
            .iter()
            .zip(&native_terminals)
            .zip(&instances)
            .zip(&w_logs)
            .enumerate()
        {
            assert_eq!(terminal.point.len(), w_log);
            assert_eq!(native.point.len(), w_log);
            for (coordinate, native_coordinate) in terminal.point.iter().zip(&native.point) {
                assert_eq!(coordinate.eval(b.values()), *native_coordinate);
                pin_eq(&mut b, coordinate, &LinExpr::constant(*native_coordinate));
            }
            for lane in 0..STATE_SIZE {
                assert_eq!(terminal.values[lane].eval(b.values()), native.values[lane]);
                assert_eq!(
                    mle_eval(&s0[lane], &native.point),
                    native.values[lane],
                    "ragged terminal {instance}, lane {lane}"
                );
                pin_eq(
                    &mut b,
                    &terminal.values[lane],
                    &LinExpr::constant(native.values[lane]),
                );
            }
        }

        // Differential trace baseline over the exact same claims and native
        // columns.  It uses independent V0 transcripts, so equality means
        // both terminals discharge honestly, not byte-identical challenges.
        let mut separate_native_ch = FsLaneChallenger::new(b"ragged-multi-separate-test");
        let separate_proofs = instances
            .iter()
            .zip(&groups)
            .map(|(s0, instance_groups)| {
                prove_deep_chain_walk(s0, instance_groups, &mut separate_native_ch).0
            })
            .collect::<Vec<_>>();
        let mut separate_builder = FieldR1csBuilder::new();
        let mut separate_ch =
            FsChannelTrace::new(&mut separate_builder, b"ragged-multi-separate-test");
        let separate_groups_e = groups
            .iter()
            .map(|instance_groups| {
                instance_groups
                    .iter()
                    .map(|group| LaneClaimGroupTrace {
                        point: group
                            .point
                            .iter()
                            .map(|&value| alloc_expr(&mut separate_builder, value))
                            .collect(),
                        values: std::array::from_fn(|lane| {
                            alloc_expr(&mut separate_builder, group.values[lane])
                        }),
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let separate_start = separate_builder.num_wires();
        for (((instance_groups, separate_proof), &w_log), s0) in separate_groups_e
            .iter()
            .zip(&separate_proofs)
            .zip(&w_logs)
            .zip(&instances)
        {
            let separate_proof_e =
                DeepChainWalkProofTrace::alloc(&mut separate_builder, separate_proof, w_log);
            let terminal = verify_deep_chain_walk_trace(
                &mut separate_builder,
                &mut separate_ch,
                w_log,
                instance_groups,
                &separate_proof_e,
            );
            for lane in 0..STATE_SIZE {
                assert_eq!(
                    mle_eval(
                        &s0[lane],
                        &terminal
                            .point
                            .iter()
                            .map(|x| x.eval(separate_builder.values()))
                            .collect::<Vec<_>>()
                    ),
                    terminal.values[lane].eval(separate_builder.values()),
                    "individual trace terminal lane {lane}"
                );
            }
        }
        let separate_rows = separate_builder.num_wires() - separate_start;
        let separate_native_post = separate_native_ch.sample_f128();
        let separate_trace_post = separate_ch.sample_f128(&mut separate_builder);
        assert_eq!(
            separate_trace_post.eval(separate_builder.values()),
            separate_native_post,
            "ragged individual baseline transcript diverged"
        );
        assert!(
            ragged_rows < separate_rows,
            "ragged multi-walk did not save rows: ragged={ragged_rows}, separate={separate_rows}"
        );
        eprintln!(
            "[deep-chain] ragged multi twin rows @w_logs={w_logs:?}: \
             ragged={ragged_rows}, separate={separate_rows}, saved={}",
            separate_rows - ragged_rows
        );

        let per_layer = max_w_log * WALK_DEGREE + instances.len() * STATE_SIZE;
        assert_eq!(mutation_end - mutation_start, N_ROUNDS * per_layer);
        let (r1cs, z) = b.build();
        assert!(
            r1cs.satisfies(&z),
            "honest ragged multi-walk twin unsatisfiable"
        );

        let coeff_wire = mutation_start + (N_ROUNDS / 2) * per_layer + 2 * WALK_DEGREE + 3;
        let mut bad_coeff = z.clone();
        bad_coeff[coeff_wire] += F128::ONE;
        assert!(
            !r1cs.satisfies(&bad_coeff),
            "ragged coefficient mutation survived"
        );

        let next_values_offset = max_w_log * WALK_DEGREE;
        let instance_wire =
            mutation_start + (N_ROUNDS / 4) * per_layer + next_values_offset + STATE_SIZE + 2;
        let mut bad_instance = z.clone();
        bad_instance[instance_wire] += F128::ONE;
        assert!(
            !r1cs.satisfies(&bad_instance),
            "ragged next-value mutation survived"
        );

        let swap_base = mutation_start + (N_ROUNDS / 3) * per_layer + next_values_offset;
        let mut swapped = z.clone();
        for lane in 0..STATE_SIZE {
            swapped.swap(swap_base + lane, swap_base + STATE_SIZE + lane);
        }
        assert!(!r1cs.satisfies(&swapped), "ragged instance swap survived");
    }

    /// Genuine C1 ragged walk: the recursive trace is transcript-identical to
    /// the native GF(2^256) verifier, returns the authenticated base-column
    /// openings, and rejects targeted proof mutations.
    #[test]
    fn c1_ragged_walk_twin_lockstep_rows_and_mutations() {
        use noid_ivc_core::deep_chain::c1::{prove_ragged_deep_chain_walk, C1LaneClaimGroup};

        let w_logs = [1usize, 2];
        let max_w_log = *w_logs.iter().max().unwrap();
        let mut rng = Rng(0xC1_A11D_CE11);
        let instances = w_logs
            .iter()
            .map(|&w_log| {
                let width = 1usize << w_log;
                std::array::from_fn(|_| (0..width).map(|_| rng.f128()).collect::<Vec<_>>())
            })
            .collect::<Vec<[Vec<F128>; STATE_SIZE]>>();
        let outputs: Vec<[Vec<F128>; STATE_SIZE]> = instances
            .iter()
            .map(|input| {
                let width = input[0].len();
                let rows = (0..width)
                    .map(|index| {
                        let mut state = std::array::from_fn(|lane| input[lane][index]);
                        for round in 0..N_ROUNDS {
                            state = apply_round(round, state);
                        }
                        state
                    })
                    .collect::<Vec<_>>();
                std::array::from_fn(|lane| rows.iter().map(|row| row[lane]).collect::<Vec<_>>())
            })
            .collect::<Vec<_>>();
        let groups = outputs
            .iter()
            .zip(&w_logs)
            .map(|(output, &w_log)| {
                let point = (0..w_log).map(|_| rng.f256()).collect::<Vec<_>>();
                let values = std::array::from_fn(|lane| mle_eval_ext(&output[lane], &point));
                C1LaneClaimGroup { point, values }
            })
            .collect::<Vec<_>>();

        let references = instances.iter().collect::<Vec<_>>();
        let mut native_channel = FsLaneChallenger::new_c1(b"c1-ragged-walk-twin-test");
        let (proof, native_terminals) =
            prove_ragged_deep_chain_walk(&references, &groups, &mut native_channel);

        let mut builder = FieldR1csBuilder::new();
        let mut channel = noid_ivc_core::field_circuit::FsChannelUnionRecorder::new_c1(
            b"c1-ragged-walk-twin-test",
        );
        let group_traces = groups
            .iter()
            .map(|group| C1LaneClaimGroupTrace {
                point: group
                    .point
                    .iter()
                    .copied()
                    .map(|value| alloc_ext_expr(&mut builder, value))
                    .collect(),
                values: std::array::from_fn(|lane| {
                    alloc_ext_expr(&mut builder, group.values[lane])
                }),
            })
            .collect::<Vec<_>>();
        let verifier_start = builder.num_wires();
        let mutation_start = builder.num_wires();
        let proof_trace =
            C1MultiDeepChainWalkProofTrace::alloc_ragged(&mut builder, &proof, &w_logs);
        let mutation_end = builder.num_wires();
        let terminals = verify_c1_ragged_deep_chain_walk_trace(
            &mut builder,
            &mut channel,
            &w_logs,
            &group_traces,
            &proof_trace,
        );
        let verifier_rows = builder.num_wires() - verifier_start;

        let native_post = native_channel.sample_f256();
        let trace_post = channel.sample_f256(&mut builder);
        assert_eq!(
            trace_post.eval(builder.values()),
            native_post,
            "C1 walk twin transcript diverged"
        );
        let recording = channel.finish();
        for (child, ((terminal, native), input)) in terminals
            .iter()
            .zip(&native_terminals)
            .zip(&instances)
            .enumerate()
        {
            assert_eq!(terminal.point.len(), w_logs[child]);
            for (coordinate, &native_coordinate) in terminal.point.iter().zip(&native.point) {
                assert_eq!(coordinate.eval(builder.values()), native_coordinate);
                pin_eq_ext(
                    &mut builder,
                    coordinate,
                    &ExtExpr::constant(native_coordinate),
                );
            }
            for lane in 0..STATE_SIZE {
                assert_eq!(
                    terminal.values[lane].eval(builder.values()),
                    native.values[lane]
                );
                assert_eq!(
                    mle_eval_ext(&input[lane], &native.point),
                    native.values[lane],
                    "C1 terminal child {child}, lane {lane}"
                );
                pin_eq_ext(
                    &mut builder,
                    &terminal.values[lane],
                    &ExtExpr::constant(native.values[lane]),
                );
            }
        }

        eprintln!(
            "[deep-chain] genuine C1 ragged walk rows @w_logs={w_logs:?}: {verifier_rows}; \
             transcript_perms={}, transcript_data={}, transcript_challenges={}",
            recording.perms,
            recording.data_wires.len(),
            recording.challenge_wires.len(),
        );
        let f256_values_per_layer = max_w_log * WALK_DEGREE + instances.len() * STATE_SIZE;
        let base_wires_per_layer = 2 * f256_values_per_layer;
        assert_eq!(
            mutation_end - mutation_start,
            N_ROUNDS * base_wires_per_layer,
            "unexpected C1 proof wire layout"
        );

        let (r1cs, witness) = builder.build();
        assert!(
            r1cs.satisfies(&witness),
            "honest C1 walk twin unsatisfiable"
        );

        let coefficient_wire =
            mutation_start + (N_ROUNDS / 2) * base_wires_per_layer + 2 * (WALK_DEGREE + 3);
        let mut bad_coefficient = witness.clone();
        bad_coefficient[coefficient_wire] += F128::ONE;
        assert!(
            !r1cs.satisfies(&bad_coefficient),
            "C1 round-coefficient mutation survived"
        );

        let next_values_offset = 2 * max_w_log * WALK_DEGREE;
        let next_value_wire = mutation_start
            + (N_ROUNDS / 4) * base_wires_per_layer
            + next_values_offset
            + 2 * (STATE_SIZE + 1);
        let mut bad_next_value = witness.clone();
        bad_next_value[next_value_wire] += F128::ONE;
        assert!(
            !r1cs.satisfies(&bad_next_value),
            "C1 next-value mutation survived"
        );
    }

    /// The genuine C1 relation and shift twins replay one shared wide
    /// transcript, match the native verifier's next challenge, and constrain
    /// the proof-carried extension values.
    #[test]
    fn c1_relation_and_shift_twins_lockstep_rows_and_mutations() {
        use noid_ivc_core::deep_chain::relations::c1::{
            prove_column_relation, prove_shift_discharge, C1RelationTerm,
        };
        use noid_ivc_core::deep_chain::relations::RelationColumns;

        let w_log = 3usize;
        let width = 1usize << w_log;
        let mut rng = Rng(0xC1_7E1A_7101);
        let committed_a = (0..width).map(|_| rng.f128()).collect::<Vec<_>>();
        let committed_b = (0..width).map(|_| rng.f128()).collect::<Vec<_>>();
        let internal = (0..width).map(|_| rng.f128()).collect::<Vec<_>>();
        let fixed = FixedPattern::new(
            2,
            vec![F128::ZERO, F128::ONE, F128::new(5, 0), F128::new(11, 0)],
        );
        let committed = vec![committed_a.as_slice(), committed_b.as_slice()];
        let internals = vec![internal.as_slice()];
        let fixed_patterns = vec![fixed];
        let columns = RelationColumns {
            committed: &committed,
            internal: &internals,
            fixed: &fixed_patterns,
        };
        let terms = vec![
            C1RelationTerm {
                coeff: rng.f256(),
                factors: vec![ColRef::Committed(0), ColRef::Internal(0)],
            },
            C1RelationTerm {
                coeff: rng.f256(),
                factors: vec![ColRef::CommittedShift(1), ColRef::Fixed(0)],
            },
        ];
        let fixed_column = fixed_patterns[0].materialize(width);
        let relation_values = (0..width)
            .map(|index| {
                let shifted = if index == 0 {
                    F128::ZERO
                } else {
                    committed_b[index - 1]
                };
                terms[0].coeff
                    * F256::from_base(committed_a[index])
                    * F256::from_base(internal[index])
                    + terms[1].coeff
                        * F256::from_base(shifted)
                        * F256::from_base(fixed_column[index])
            })
            .collect::<Vec<_>>();
        let eq_point = (0..w_log).map(|_| rng.f256()).collect::<Vec<_>>();
        let target = mle_eval_f256(&relation_values, &eq_point);

        let mut native = FsLaneChallenger::new_c1(b"c1-relation-shift-twin");
        let (relation_proof, relation_point, relation_values) =
            prove_column_relation(target, &eq_point, &terms, &columns, &mut native);
        let references = c1_claimed_refs(&terms);
        let shifted_index = references
            .iter()
            .position(|reference| *reference == ColRef::CommittedShift(1))
            .unwrap();
        let shifted_target = relation_values[shifted_index];
        let (shift_proof, native_shift_point) =
            prove_shift_discharge(&committed_b, &relation_point, shifted_target, &mut native);

        let mut builder = FieldR1csBuilder::new();
        let mut channel =
            noid_ivc_core::field_circuit::FsChannelUnionRecorder::new_c1(b"c1-relation-shift-twin");
        let target_trace = alloc_ext_expr(&mut builder, target);
        let eq_point_trace = eq_point
            .iter()
            .copied()
            .map(|value| alloc_ext_expr(&mut builder, value))
            .collect::<Vec<_>>();
        let term_traces = terms
            .iter()
            .map(|term| C1RelationTermTrace {
                coeff: ExtExpr::constant(term.coeff),
                factors: term.factors.clone(),
            })
            .collect::<Vec<_>>();
        let mutation_start = builder.num_wires();
        let relation_trace = C1ColumnRelationProofTrace::alloc(
            &mut builder,
            &relation_proof,
            w_log,
            references.len(),
        );
        let shift_trace = C1ShiftDischargeProofTrace::alloc(&mut builder, &shift_proof, w_log);
        let mutation_end = builder.num_wires();
        let row_start = builder.num_wires();
        let relation_point_trace = verify_c1_column_relation_trace(
            &mut builder,
            &mut channel,
            w_log,
            &target_trace,
            &eq_point_trace,
            &term_traces,
            &fixed_patterns,
            &relation_trace,
        );
        let shift_point_trace = verify_c1_shift_discharge_trace(
            &mut builder,
            &mut channel,
            w_log,
            &relation_point_trace,
            &relation_trace.final_values[shifted_index],
            0,
            &shift_trace,
        );
        let rows = builder.num_wires() - row_start;

        let native_post = native.sample_f256();
        let trace_post = channel.sample_f256(&mut builder);
        assert_eq!(trace_post.eval(builder.values()), native_post);
        let recording = channel.finish();
        for (trace, native) in relation_point_trace.iter().zip(&relation_point) {
            assert_eq!(trace.eval(builder.values()), *native);
        }
        for (trace, native) in shift_point_trace.iter().zip(&native_shift_point) {
            assert_eq!(trace.eval(builder.values()), *native);
            pin_eq_ext(&mut builder, trace, &ExtExpr::constant(*native));
        }
        assert_eq!(
            shift_trace.final_value.eval(builder.values()),
            mle_eval_ext(&committed_b, &native_shift_point)
        );
        eprintln!(
            "[deep-chain] genuine C1 relation+shift rows={rows}, transcript_perms={}, \
             transcript_data={}, transcript_challenges={}",
            recording.perms,
            recording.data_wires.len(),
            recording.challenge_wires.len(),
        );

        let (r1cs, witness) = builder.build();
        assert!(
            r1cs.satisfies(&witness),
            "honest C1 relation+shift twin unsatisfiable"
        );
        assert!(mutation_end > mutation_start);
        let mut bad = witness.clone();
        bad[mutation_start + 3] += F128::ONE;
        assert!(!r1cs.satisfies(&bad), "C1 relation proof mutation survived");
    }

    /// Production-width row and transcript profile for the fused Link/Block
    /// C1 walk. Correctness is covered by the non-ignored small twin above;
    /// this benchmark intentionally avoids constructing all nine output tables.
    #[test]
    #[ignore = "production-width C1 recursive profile"]
    fn c1_joint_b25_recursive_row_profile() {
        use noid_ivc_core::deep_chain::c1::{prove_ragged_deep_chain_walk, C1LaneClaimGroup};

        let w_logs = [14usize, 15, 17, 16, 12, 15, 16, 12, 13];
        let mut rng = Rng(0xC1_B25_C1AC);
        let instances = w_logs
            .iter()
            .map(|&w_log| {
                let width = 1usize << w_log;
                std::array::from_fn(|_| (0..width).map(|_| rng.f128()).collect::<Vec<_>>())
            })
            .collect::<Vec<[Vec<F128>; STATE_SIZE]>>();
        let groups = w_logs
            .iter()
            .map(|&w_log| C1LaneClaimGroup {
                point: (0..w_log).map(|_| rng.f256()).collect(),
                values: std::array::from_fn(|_| rng.f256()),
            })
            .collect::<Vec<_>>();
        let references = instances.iter().collect::<Vec<_>>();
        let mut native_channel = FsLaneChallenger::new_c1(b"c1-joint-b25-recursive-profile");
        let (proof, _) = prove_ragged_deep_chain_walk(&references, &groups, &mut native_channel);

        let mut builder = FieldR1csBuilder::new();
        let mut channel = noid_ivc_core::field_circuit::FsChannelUnionRecorder::new_c1(
            b"c1-joint-b25-recursive-profile",
        );
        let group_traces = groups
            .iter()
            .map(|group| C1LaneClaimGroupTrace {
                point: group
                    .point
                    .iter()
                    .copied()
                    .map(|value| alloc_ext_expr(&mut builder, value))
                    .collect(),
                values: std::array::from_fn(|lane| {
                    alloc_ext_expr(&mut builder, group.values[lane])
                }),
            })
            .collect::<Vec<_>>();
        let row_start = builder.num_wires();
        let proof_trace =
            C1MultiDeepChainWalkProofTrace::alloc_ragged(&mut builder, &proof, &w_logs);
        let terminals = verify_c1_ragged_deep_chain_walk_trace(
            &mut builder,
            &mut channel,
            &w_logs,
            &group_traces,
            &proof_trace,
        );
        let rows = builder.num_wires() - row_start;
        let native_post = native_channel.sample_f256();
        let trace_post = channel.sample_f256(&mut builder);
        assert_eq!(trace_post.eval(builder.values()), native_post);
        let recording = channel.finish();
        eprintln!(
            "[deep-chain] genuine C1 joint B25 rows={rows}, transcript_perms={}, \
             transcript_data={}, transcript_challenges={}, terminals={}",
            recording.perms,
            recording.data_wires.len(),
            recording.challenge_wires.len(),
            terminals.len(),
        );
    }

    /// Fixed-pattern factors in the twin: a periodic selector gating a
    /// 3-factor term, lockstep with the native verifier, mutations
    /// rejected. Exercises the closed-form tensor evaluation.
    #[test]
    fn fixed_pattern_twin_lockstep_and_mutations() {
        use noid_ivc_core::deep_chain::relations::FixedPattern;
        let w_log = 4;
        let low_log = 2;
        let w = 1usize << w_log;
        let mut rng = Rng(0xF17ED2);
        let sel: Vec<F128> = (0..w)
            .map(|_| {
                if rng.f128().lo & 1 == 1 {
                    F128::ONE
                } else {
                    F128::ZERO
                }
            })
            .collect();
        let a: Vec<F128> = (0..w).map(|_| rng.f128()).collect();
        let mut table = vec![F128::ZERO; 1 << low_log];
        table[1] = F128::ONE;
        table[2] = F128 { lo: 9, hi: 0 };
        let fixed = vec![FixedPattern::new(low_log, table.clone())];
        let terms = vec![
            noid_ivc_core::deep_chain::relations::RelationTerm {
                coeff: F128::ONE,
                factors: vec![ColRef::Fixed(0), ColRef::Committed(0), ColRef::Committed(1)],
            },
            noid_ivc_core::deep_chain::relations::RelationTerm {
                coeff: F128::ONE,
                factors: vec![ColRef::Committed(1)],
            },
        ];
        let mut rng2 = Rng(0xEE2);
        let eq_point: Vec<F128> = (0..w_log).map(|_| rng2.f128()).collect();
        let eq = build_eq_table(&eq_point);
        let mut target = F128::ZERO;
        for i in 0..w {
            let pat = table[i & ((1 << low_log) - 1)];
            target += eq[i] * (pat * sel[i] * a[i] + a[i]);
        }

        let committed: Vec<&[F128]> = vec![&sel, &a];
        let columns = RelationColumns {
            committed: &committed,
            internal: &[],
            fixed: &fixed,
        };
        let mut ch_native = FsLaneChallenger::new(b"fixed-twin-test");
        let (proof, native_point, _) =
            prove_column_relation(target, &eq_point, &terms, &columns, &mut ch_native);

        let mut b = FieldR1csBuilder::new();
        let mut ch = FsChannelTrace::new(&mut b, b"fixed-twin-test");
        let target_e = alloc_expr(&mut b, target);
        let eq_point_e: Vec<LinExpr> = eq_point.iter().map(|&v| alloc_expr(&mut b, v)).collect();
        let terms_e: Vec<RelationTermTrace> = terms
            .iter()
            .map(|t| RelationTermTrace {
                coeff: LinExpr::constant(t.coeff),
                factors: t.factors.clone(),
            })
            .collect();
        let mutation_start = b.num_wires();
        let proof_e = ColumnRelationProofTrace::alloc(&mut b, &proof, w_log, 2);
        let mutation_end = b.num_wires();
        let point_e = verify_column_relation_trace(
            &mut b,
            &mut ch,
            w_log,
            &target_e,
            &eq_point_e,
            &terms_e,
            &fixed,
            &proof_e,
        );

        let c_n = ch_native.sample_f128();
        let c_t = ch.sample_f128(&mut b);
        assert_eq!(c_t.eval(b.values()), c_n, "fixed twin transcript diverged");
        for (e, n) in point_e.iter().zip(native_point.iter()) {
            assert_eq!(e.eval(b.values()), *n);
        }

        let (r1cs, z) = b.build();
        assert!(r1cs.satisfies(&z), "honest fixed twin unsatisfiable");

        use rayon::prelude::*;
        let survivors: Vec<usize> = (mutation_start..mutation_end)
            .into_par_iter()
            .filter(|&t| {
                let mut bad = z.clone();
                bad[t] += F128::ONE;
                r1cs.satisfies(&bad)
            })
            .collect();
        assert!(survivors.is_empty(), "fixed twin survivors: {survivors:?}");
    }

    /// Relation + shift twins: lockstep on a wiring-shaped relation and its
    /// shift discharge, satisfiable, wire mutations rejected.
    #[test]
    fn relation_and_shift_twins_lockstep_and_mutations() {
        let w_log = 3;
        let w = 1usize << w_log;
        let mut rng = Rng(0x511AD);
        let carry: Vec<F128> = (0..w).map(|_| rng.f128()).collect();
        let absorb: Vec<F128> = (0..w).map(|_| rng.f128()).collect();
        let committed: Vec<&[F128]> = vec![&carry, &absorb];
        let columns = RelationColumns {
            committed: &committed,
            internal: &[],
            fixed: &[],
        };
        let coeff3 = F128 { lo: 3, hi: 0 };
        let coeff5 = F128 { lo: 5, hi: 0 };
        let terms = vec![
            noid_ivc_core::deep_chain::relations::RelationTerm {
                coeff: coeff3,
                factors: vec![ColRef::CommittedShift(0)],
            },
            noid_ivc_core::deep_chain::relations::RelationTerm {
                coeff: coeff5,
                factors: vec![ColRef::Committed(1)],
            },
        ];
        let mut rng2 = Rng(0xEEE);
        let eq_point: Vec<F128> = (0..w_log).map(|_| rng2.f128()).collect();
        let eq = build_eq_table(&eq_point);
        let mut target = F128::ZERO;
        for i in 0..w {
            let sh = if i == 0 { F128::ZERO } else { carry[i - 1] };
            target += eq[i] * (coeff3 * sh + coeff5 * absorb[i]);
        }

        let mut ch_native = FsLaneChallenger::new(b"relation-twin-test");
        let (proof, native_point, _) =
            prove_column_relation(target, &eq_point, &terms, &columns, &mut ch_native);
        // Follow with the shift discharge natively.
        let shift_value = proof.final_values[0];
        let (shift_proof, native_shift_point) =
            prove_shift_discharge(&carry, &native_point, shift_value, &mut ch_native);

        let mut b = FieldR1csBuilder::new();
        let mut ch = FsChannelTrace::new(&mut b, b"relation-twin-test");
        let target_e = alloc_expr(&mut b, target);
        let eq_point_e: Vec<LinExpr> = eq_point.iter().map(|&v| alloc_expr(&mut b, v)).collect();
        let terms_e = vec![
            RelationTermTrace {
                coeff: LinExpr::constant(coeff3),
                factors: vec![ColRef::CommittedShift(0)],
            },
            RelationTermTrace {
                coeff: LinExpr::constant(coeff5),
                factors: vec![ColRef::Committed(1)],
            },
        ];
        let mutation_start = b.num_wires();
        let proof_e = ColumnRelationProofTrace::alloc(&mut b, &proof, w_log, 2);
        let shift_e = ShiftDischargeProofTrace::alloc(&mut b, &shift_proof, w_log);
        let mutation_end = b.num_wires();

        let point_e = verify_column_relation_trace(
            &mut b,
            &mut ch,
            w_log,
            &target_e,
            &eq_point_e,
            &terms_e,
            &[],
            &proof_e,
        );
        let shift_point_e = verify_shift_discharge_trace(
            &mut b,
            &mut ch,
            w_log,
            &point_e,
            &proof_e.final_values[0],
            0,
            &shift_e,
        );

        let c_n = ch_native.sample_f128();
        let c_t = ch.sample_f128(&mut b);
        assert_eq!(
            c_t.eval(b.values()),
            c_n,
            "relation twin transcript diverged"
        );
        for (e, n) in point_e.iter().zip(native_point.iter()) {
            assert_eq!(e.eval(b.values()), *n);
        }
        for (e, n) in shift_point_e.iter().zip(native_shift_point.iter()) {
            assert_eq!(e.eval(b.values()), *n);
        }

        let (r1cs, z) = b.build();
        assert!(r1cs.satisfies(&z), "honest relation twin unsatisfiable");

        use rayon::prelude::*;
        let survivors: Vec<usize> = (mutation_start..mutation_end)
            .into_par_iter()
            .filter(|&t| {
                let mut bad = z.clone();
                bad[t] += F128::ONE;
                r1cs.satisfies(&bad)
            })
            .collect();
        assert!(
            survivors.is_empty(),
            "relation twin survivors: {survivors:?}"
        );
    }

    /// The source-binding discharge twin: the in-trace weighted-sum verifier
    /// with the encode-kernel weight (`K_i(z)·eq(right,i)`) matches the native
    /// reduction lane-for-lane — same transcript, same derived point, honest
    /// R1CS satisfiable, and the terminal claim is the true `H` opening.
    #[test]
    fn weighted_sum_source_binding_twin() {
        use noid_ivc_core::deep_chain::encode_kernel::source_weight_at;
        use noid_ivc_core::deep_chain::relations::prove_weighted_sum;

        let n_rounds = 5usize;
        let w = 1usize << n_rounds;
        let mut rng = Rng(0x50FA11);
        let h: Vec<F128> = (0..w).map(|_| rng.f128()).collect();
        let right: Vec<F128> = (0..n_rounds).map(|_| rng.f128()).collect();
        let z: Vec<F128> = (0..n_rounds + 2).map(|_| rng.f128()).collect();
        let weights: Vec<F128> = (0..w)
            .map(|i| {
                let x: Vec<F128> = (0..n_rounds)
                    .map(|l| {
                        if (i >> l) & 1 == 1 {
                            F128::ONE
                        } else {
                            F128::ZERO
                        }
                    })
                    .collect();
                source_weight_at(&z, &right, &x, n_rounds)
            })
            .collect();
        let mut target = F128::ZERO;
        for i in 0..w {
            target += weights[i] * h[i];
        }

        let mut ch_native = FsLaneChallenger::new(b"wsum-twin");
        let (proof, native_point) = prove_weighted_sum(&h, &weights, target, &mut ch_native);

        let mut b = FieldR1csBuilder::new();
        let mut ch = FsChannelTrace::new(&mut b, b"wsum-twin");
        let target_e = alloc_expr(&mut b, target);
        let z_e: Vec<LinExpr> = z.iter().map(|&v| alloc_expr(&mut b, v)).collect();
        let right_e: Vec<LinExpr> = right.iter().map(|&v| alloc_expr(&mut b, v)).collect();
        let mutation_start = b.num_wires();
        let proof_e = WeightedSumProofTrace::alloc(&mut b, &proof, n_rounds);
        let mutation_end = b.num_wires();

        let point_e =
            verify_weighted_sum_trace(&mut b, &mut ch, n_rounds, &target_e, &proof_e, |b, pt| {
                source_weight_at_trace(b, &z_e, &right_e, pt, n_rounds)
            });

        let c_n = ch_native.sample_f128();
        let c_t = ch.sample_f128(&mut b);
        assert_eq!(c_t.eval(b.values()), c_n, "wsum twin transcript diverged");
        for (e, n) in point_e.iter().zip(native_point.iter()) {
            assert_eq!(e.eval(b.values()), *n, "wsum twin point diverged");
        }
        // The terminal claim is the true H opening at the derived point.
        assert_eq!(mle_eval(&h, &native_point), proof.final_value);

        let (r1cs, zz) = b.build();
        assert!(r1cs.satisfies(&zz), "honest wsum twin unsatisfiable");

        // Every allocated proof wire is constrained (0 surviving mutants).
        use rayon::prelude::*;
        let survivors: Vec<usize> = (mutation_start..mutation_end)
            .into_par_iter()
            .filter(|&t| {
                let mut bad = zz.clone();
                bad[t] += F128::ONE;
                r1cs.satisfies(&bad)
            })
            .collect();
        assert!(survivors.is_empty(), "wsum twin survivors: {survivors:?}");
    }

    /// The H-claim twin: `H~(right) = claim` as a weighted-sum discharge with
    /// the `eq(right,·)` weight — the second source-binding leg, in-region,
    /// matching the native reduction and 0-mutant.
    #[test]
    fn h_claim_eq_weight_twin() {
        use noid_ivc_core::deep_chain::relations::prove_weighted_sum;

        let n_rounds = 5usize;
        let w = 1usize << n_rounds;
        let mut rng = Rng(0x11C1A1);
        let h: Vec<F128> = (0..w).map(|_| rng.f128()).collect();
        let right: Vec<F128> = (0..n_rounds).map(|_| rng.f128()).collect();
        let eq_weights = build_eq_table(&right);
        let claim = {
            let mut c = F128::ZERO;
            for i in 0..w {
                c += eq_weights[i] * h[i];
            }
            c
        };

        let mut ch_native = FsLaneChallenger::new(b"hclaim-twin");
        let (proof, native_point) = prove_weighted_sum(&h, &eq_weights, claim, &mut ch_native);

        let mut b = FieldR1csBuilder::new();
        let mut ch = FsChannelTrace::new(&mut b, b"hclaim-twin");
        let claim_e = alloc_expr(&mut b, claim);
        let right_e: Vec<LinExpr> = right.iter().map(|&v| alloc_expr(&mut b, v)).collect();
        let mutation_start = b.num_wires();
        let proof_e = WeightedSumProofTrace::alloc(&mut b, &proof, n_rounds);
        let mutation_end = b.num_wires();

        let point_e =
            verify_weighted_sum_trace(&mut b, &mut ch, n_rounds, &claim_e, &proof_e, |b, pt| {
                eq_at_trace(b, &right_e, pt)
            });

        let c_n = ch_native.sample_f128();
        let c_t = ch.sample_f128(&mut b);
        assert_eq!(
            c_t.eval(b.values()),
            c_n,
            "h-claim twin transcript diverged"
        );
        for (e, n) in point_e.iter().zip(native_point.iter()) {
            assert_eq!(e.eval(b.values()), *n);
        }
        assert_eq!(mle_eval(&h, &native_point), proof.final_value);

        let (r1cs, zz) = b.build();
        assert!(r1cs.satisfies(&zz), "honest h-claim twin unsatisfiable");
        use rayon::prelude::*;
        let survivors: Vec<usize> = (mutation_start..mutation_end)
            .into_par_iter()
            .filter(|&t| {
                let mut bad = zz.clone();
                bad[t] += F128::ONE;
                r1cs.satisfies(&bad)
            })
            .collect();
        assert!(
            survivors.is_empty(),
            "h-claim twin survivors: {survivors:?}"
        );
    }
}
