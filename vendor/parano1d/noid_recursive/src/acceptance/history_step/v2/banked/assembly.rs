// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

use super::*;
use parent::{prepare_parent, PreparedParent};

pub struct Built {
    class: Class,
    matrix: HistoryStepMatrixLease,
    witness: Vec<F128>,
    io: Vec<F128>,
    preparations: Preparations,
}

struct Assembly {
    class: Class,
    builder: FieldR1csBuilder,
    block: SelectedZkBlockSlotsAssembly,
    parent: HistoryStepParentRegionPreparation,
    io_seal: DeferredHistoryStepIo,
    io: Vec<F128>,
    matrix: Option<HistoryStepMatrixLease>,
}

fn parent_selector(
    builder: &mut FieldR1csBuilder,
    authenticated: &LinExpr,
    class: Class,
) -> [LinExpr; 2] {
    let large = LinExpr::from_wire(builder.alloc_bool(class == Class::Large));
    pin_eq(builder, authenticated, &large);
    [large.add_const(F128::ONE), large]
}

/// Exact carry is part of the relation, including a previously used large
/// matrix after returning to small blocks. The inactive fold has no authority.
fn bind_lane(
    builder: &mut FieldR1csBuilder,
    cells: &[LinExpr],
    prev: &[LinExpr],
    lane: Lane,
    gate: &LinExpr,
    folded: &C1MatrixAccClaimTrace,
) {
    let outputs = folded
        .point
        .iter()
        .flat_map(|p| [&p.lo, &p.hi])
        .chain([&folded.value.lo, &folded.value.hi]);
    for (offset, value) in (lane.point..lane.live).zip(outputs) {
        let delta = mul(builder, gate, &value.add(&prev[offset]));
        pin_eq(builder, &cells[offset], &prev[offset].add(&delta));
    }
    let delta = mul(builder, gate, &prev[lane.live].add_const(F128::ONE));
    pin_eq(builder, &cells[lane.live], &prev[lane.live].add(&delta));
}

fn prepare_assembly<const TIER: usize>(
    runtime: &Runtime,
    prepared: PreparedParent<'_>,
    current: HistoryStepBlockInput<TIER>,
    frozen: bool,
) -> Result<Assembly, V2Error> {
    let PreparedParent {
        selected,
        current: class,
        envelopes,
        scratch,
        folds,
        io,
    } = prepared;
    let config = runtime.bank.config().class(class);
    if config.pages() != TIER {
        return Err(V2Error::Runtime);
    }
    let matrix = if frozen {
        None
    } else {
        Some(runtime.load_matrix(class)?)
    };
    let mut builder = if frozen {
        FieldR1csBuilder::new()
    } else {
        FieldR1csBuilder::new_witness_only()
    };
    let (cells, io_seal) =
        allocate_deferred_history_step_io(&mut builder, &runtime.bank.config().io_spec(), &io, ACC);
    let gate = cells[BASE].add_const(F128::ONE);
    let boolean = mul(&mut builder, &cells[BASE], &gate);
    pin_eq(&mut builder, &boolean, &LinExpr::zero());
    pin_eq(
        &mut builder,
        &cells[TIP_CLASS],
        &LinExpr::constant(f128_from_u128(class.wire_id() as u128)),
    );
    let params = Class::ALL.map(|c| runtime.bank.config().class(c).pcs_params());
    let r_proofs = Class::ALL.map(|c| RPcsProof {
        native: &envelopes[c.index()].proof().field.pcs_open,
        params: &params[c.index()],
        commitment_root: flat_digest_lanes(&envelopes[c.index()].proof().commitment.root),
    });
    let (children, parents): (Vec<_>, Vec<_>) =
        scratch.into_iter().map(|s| (s.child, s.parent)).unzip();
    let columns = prepare_history_step_parent_columns(
        &mut builder,
        &r_proofs,
        selected.index(),
        &runtime.parts.geometry,
        children,
        parents,
    )?;
    let HistoryStepBlockInput {
        start_accumulator,
        end_accumulator,
        components,
        authorization,
        sealed_header,
        parent_header,
        ..
    } = current;
    let parent_seal = ParentSealTrace::alloc(&mut builder, &parent_header);
    let block = build_block_slots_selected_zk_prefix(
        &mut builder,
        &start_accumulator,
        &end_accumulator,
        &components,
        &sealed_header,
        TIER,
        authorization,
        &parent_header,
        &parent_seal.block_id,
        BlockRelationProfile::ScheduledV2(config),
    );
    pin_eq(
        &mut builder,
        &parent_seal.height,
        &block.slots().start_acc.height,
    );
    pin_eq(
        &mut builder,
        &cells[ORIGIN_ACC],
        &LinExpr::constant(flat_of(noid_core::Block128(
            (config.activation_height() - 1) as u128,
        ))),
    );
    let roots = envelopes
        .iter()
        .map(|e| alloc_flat_digest(&mut builder, &e.proof().commitment.root))
        .collect::<Vec<_>>();
    let prev = envelopes[selected.index()]
        .proof()
        .io
        .iter()
        .map(|v| LinExpr::from_wire(builder.alloc_f128(*v)))
        .collect::<Vec<_>>();
    let selectors = parent_selector(&mut builder, &prev[TIP_CLASS], selected);
    // The entire ordered bank and sealed legacy boundary are inherited.
    for index in BANK..POINT {
        pin_eq(&mut builder, &cells[index], &prev[index]);
    }
    let mut obligations = Vec::new();
    let mut recorded_children = Vec::new();
    let mut recorded_parents = Vec::new();
    for arm in Class::ALL {
        let slot = arm.index();
        let entry = runtime.bank.config().class(arm);
        let envelope = envelopes[slot].proof();
        let proof = C1FieldR1csProofTrace::alloc_shape_mode(
            &mut builder,
            &envelope.field,
            &entry.shape(),
            &params[slot],
            false,
        );
        let arm_gate = mul(&mut builder, &gate, &selectors[slot]);
        let mut arm_obligations = PcsWalkObligations::default();
        let mut recorder = BaseSelectableParentRecorder::new_c1(PROOF_DOMAIN);
        let mut child = None;
        let mut error = None;
        let (_, fresh) = with_pin_gate(&arm_gate, || {
            verify_field_c1_trace_deferred_region_with_post_commit_context_expr(
                &mut builder,
                &mut recorder,
                &entry.shape(),
                &params[slot],
                &[
                    prev[MATRIX + 2 * slot].clone(),
                    prev[MATRIX + 2 * slot + 1].clone(),
                ],
                &roots[slot],
                &proof,
                &runtime.bank.config().io_spec(),
                &prev,
                &[
                    prev[POST + 2 * slot].clone(),
                    prev[POST + 2 * slot + 1].clone(),
                ],
                Some(&mut arm_obligations),
                |builder, context| match verify_joint_c1_region_sidecar_trace_post_commit(
                    builder,
                    context,
                    &runtime.parts.parent_vk,
                    runtime.parts.block_vk(arm),
                    &envelope.sidecar,
                ) {
                    Ok(recording) => child = Some(recording),
                    Err(e) => error = Some(e),
                },
            )
        });
        if let Some(error) = error {
            return Err(error.into());
        }
        obligations.push(arm_obligations);
        recorded_children.push(child.ok_or(V2Error::Layout)?);
        recorded_parents.push(recorder.finish());
        let lane = Lane::for_class(arm);
        let incoming = C1MatrixAccClaimTrace {
            point: prev[lane.point..lane.value]
                .chunks_exact(2)
                .map(|x| ExtExpr::new(x[0].clone(), x[1].clone()))
                .collect(),
            value: ExtExpr::new(prev[lane.value].clone(), prev[lane.value + 1].clone()),
        };
        let fold = C1MatrixFoldProofTrace::alloc(&mut builder, &folds[slot], entry.outer_m());
        let mut channel = FsChannelTrace::new_c1(&mut builder, FOLD_DOMAIN);
        channel.observe_label(&mut builder, ROUTE_DOMAIN);
        channel.observe_lanes(&mut builder, 1, std::slice::from_ref(&prev[TIP_CLASS]));
        let outgoing = with_pin_gate(&arm_gate, || {
            verify_matrix_claim_fold_c1_trace(
                &mut builder,
                &mut channel,
                entry.shape().k_log,
                entry.shape().k_skip,
                &fresh,
                &incoming,
                &prev[lane.live],
                &fold,
            )
        });
        bind_lane(&mut builder, &cells, &prev, lane, &arm_gate, &outgoing);
        // A new origin cannot import an unchecked v2 matrix claim.
        with_pin_gate(&cells[BASE], || {
            for cell in &cells[lane.point..=lane.live] {
                pin_eq(&mut builder, cell, &LinExpr::zero());
            }
        });
    }
    let parent = with_pin_gate(&gate, || {
        finalize_history_step_parent_region(
            &mut builder,
            columns,
            &obligations,
            &selectors,
            &recorded_children,
            &recorded_parents,
        )
    })?;
    for lane in 0..2 {
        with_pin_gate(&gate, || {
            pin_eq(
                &mut builder,
                &parent_seal.semantic_id[lane],
                &prev[ACC + 1 + lane],
            )
        });
        with_pin_gate(&cells[BASE], || {
            pin_eq(
                &mut builder,
                &parent_seal.block_id[lane],
                &cells[ORIGIN_ID + lane],
            );
            pin_eq(
                &mut builder,
                &parent_seal.semantic_id[lane],
                &cells[ORIGIN_ACC + 1 + lane],
            );
        });
    }
    for (index, start) in block.slots().start_acc.ordered_lanes().iter().enumerate() {
        with_pin_gate(&gate, || pin_eq(&mut builder, start, &prev[ACC + index]));
        with_pin_gate(&cells[BASE], || {
            pin_eq(&mut builder, start, &cells[ORIGIN_ACC + index])
        });
    }
    for (index, end) in block.slots().end_acc.ordered_lanes().iter().enumerate() {
        pin_eq(&mut builder, end, &cells[ACC + index]);
    }
    Ok(Assembly {
        class,
        builder,
        block,
        parent,
        io_seal,
        io,
        matrix,
    })
}

enum AssemblyOutput {
    Frozen(FrozenV2),
    Built(Built),
}

fn finish_assembly(
    runtime: &Runtime,
    assembly: Assembly,
    header: &BlockHeader,
    end: &ChainAccumulator,
) -> Result<AssemblyOutput, V2Error> {
    let Assembly {
        class,
        mut builder,
        mut block,
        parent,
        io_seal,
        mut io,
        matrix,
    } = assembly;
    let config = runtime.bank.config().class(class);
    io_seal.seal(&mut builder, &mut io, ACC, end)?;
    block
        .seal_direct_tail(&mut builder, header, end)
        .map_err(|_| V2Error::Boundary)?;
    let used = builder.num_wires();
    let limit = 1usize << config.outer_m();
    if used > limit {
        return Err(V2Error::Shape { used, limit });
    }
    let block = finalize_selected_zk_block_region(block, config.outer_m())?;
    let preparations = Preparations { parent, block };
    match matrix {
        None => {
            let (matrix, witness) = builder.build();
            let (matrix, witness) =
                crate::acceptance::expand_empty_field_tail(matrix, witness, config.shape());
            Ok(AssemblyOutput::Frozen(FrozenV2 {
                matrix,
                witness,
                preparations,
            }))
        }
        Some(matrix) => {
            let (_, mut witness) = builder.build_witness_only();
            witness.resize(limit, F128::ZERO);
            if used != matrix.useful_rows()
                || preparations.parent.vk() != runtime.parts.parent_vk()
                || preparations.block.vk() != runtime.parts.block_vk(class)
            {
                return Err(V2Error::Runtime);
            }
            runtime.bank.parse(&io)?;
            Ok(AssemblyOutput::Built(Built {
                class,
                matrix,
                witness,
                io,
                preparations,
            }))
        }
    }
}

pub fn assemble_frozen<const TIER: usize>(
    runtime: &Runtime,
    origin: &Origin,
    parent: Option<&Terminal>,
    current: HistoryStepBlockInput<TIER>,
) -> Result<FrozenV2, V2Error> {
    let prepared = prepare_parent(runtime, origin, parent, &current)?;
    let header = current.sealed_header;
    let end = current.end_accumulator.clone();
    let assembly = prepare_assembly(runtime, prepared, current, true)?;
    match finish_assembly(runtime, assembly, &header, &end)? {
        AssemblyOutput::Frozen(frozen) => Ok(frozen),
        _ => unreachable!("frozen assembly"),
    }
}

#[must_use = "dropping this value cancels the unsealed block attempt"]
pub struct PreparedForPow {
    assembly: Assembly,
    header: BlockHeader,
    parent_header: BlockHeader,
    start: ChainAccumulator,
}

pub fn prepare_for_pow<const TIER: usize>(
    runtime: &Runtime,
    origin: &Origin,
    parent: Option<&Terminal>,
    current: HistoryStepBlockInput<TIER>,
) -> Result<PreparedForPow, V2Error> {
    if current.sealed_header.nonce != 0 {
        return Err(V2Error::Boundary);
    }
    let prepared = prepare_parent(runtime, origin, parent, &current)?;
    let header = current.sealed_header;
    let parent_header = current.parent_header;
    let start = current.start_accumulator.clone();
    Ok(PreparedForPow {
        assembly: prepare_assembly(runtime, prepared, current, false)?,
        header,
        parent_header,
        start,
    })
}
impl PreparedForPow {
    pub fn retained_witness_bytes(&self) -> usize {
        self.assembly.builder.retained_witness_bytes()
    }
    pub fn seal_nonce(mut self, runtime: &Runtime, nonce: u128) -> Result<Built, V2Error> {
        self.header.nonce = nonce;
        let end = self
            .start
            .advance(&self.parent_header, &self.header)
            .map_err(|_| V2Error::Boundary)?;
        match finish_assembly(runtime, self.assembly, &self.header, &end)? {
            AssemblyOutput::Built(built) => Ok(built),
            _ => unreachable!("witness assembly"),
        }
    }
}

pub fn prove_built(
    runtime: &Runtime,
    built: &Built,
    cancellation: &std::sync::atomic::AtomicBool,
) -> Result<Terminal, V2Error> {
    if cancellation.load(std::sync::atomic::Ordering::Acquire) {
        return Err(V2Error::Cancelled);
    }
    let class = built.class;
    let config = runtime.bank.config().class(class);
    runtime.bank.authenticate(class, &built.matrix)?;
    if runtime.bank.parse(&built.io)?.class != class {
        return Err(V2Error::Io);
    }
    if built.preparations.parent.vk() != runtime.parts.parent_vk()
        || built.preparations.block.vk() != runtime.parts.block_vk(class)
    {
        return Err(V2Error::Runtime);
    }
    let params = config.pcs_params();
    let spec = runtime.bank.config().io_spec();
    macro_rules! prove {
        ($function:path, $matrix:expr) => {{
            let parent = built.preparations.parent.certified_c1_prover_plan()?;
            let block = built.preparations.block.certified_c1_prover_plan()?;
            let mut channel = FsLaneChallenger::new_c1(PROOF_DOMAIN);
            $function(
                $matrix,
                &built.witness,
                &params,
                &spec,
                &built.io,
                &runtime.bank.post_commit_digest(class),
                cancellation,
                &mut channel,
                |context| -> Result<JointC1RegionSidecarProof, RegionSidecarError> {
                    let (proof, claims) = crate::region_sidecar::prove_joint_c1_region_sidecar(
                        &parent,
                        &block,
                        context.witness(),
                        context,
                    )?;
                    context.append_c1_claims(claims);
                    Ok(proof)
                },
            )
            .map_err(|_| V2Error::Cancelled)
        }};
    }
    let (field, sidecar, commitment, _) = match &built.matrix {
        HistoryStepMatrixLease::Resident(m) => prove!(
            prove_field_c1_with_public_io_and_post_commit_context_cancellable,
            m.as_ref()
        ),
        HistoryStepMatrixLease::Compact(m) => prove!(
            prove_field_compact_c1_with_public_io_and_post_commit_context_cancellable,
            m.as_ref()
        ),
    }?;
    if cancellation.load(std::sync::atomic::Ordering::Acquire) {
        return Err(V2Error::Cancelled);
    }
    Ok(Terminal {
        class,
        proof: V2Proof {
            field,
            commitment,
            io: built.io.clone(),
            sidecar: sidecar?,
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selector_and_every_carried_or_folded_coordinate_are_constrained() {
        let mut digest = None;
        for selected in Class::ALL {
            for recursive in [false, true] {
                let mut builder = FieldR1csBuilder::new();
                let prior: Vec<_> = (0..IO_LEN)
                    .map(|i| f128_from_u128(i as u128 + 17))
                    .collect();
                let prev: Vec<_> = prior
                    .iter()
                    .map(|v| LinExpr::from_wire(builder.alloc_f128(*v)))
                    .collect();
                let class_wire = builder.alloc_f128(f128_from_u128(selected.wire_id() as u128));
                let selectors =
                    parent_selector(&mut builder, &LinExpr::from_wire(class_wire), selected);
                let recursive = LinExpr::from_wire(builder.alloc_bool(recursive));
                let mut outputs = prior.clone();
                let mut folded = Vec::new();
                for class in Class::ALL {
                    let lane = Lane::for_class(class);
                    if class == selected && recursive.eval(builder.values()) == F128::ONE {
                        outputs[lane.point..lane.live].fill(f128_from_u128(7));
                        outputs[lane.live] = F128::ONE;
                    }
                    let component = LinExpr::constant(f128_from_u128(7));
                    folded.push(C1MatrixAccClaimTrace {
                        point: vec![
                            ExtExpr::new(component.clone(), component.clone());
                            lane.point_len()
                        ],
                        value: ExtExpr::new(component.clone(), component),
                    });
                }
                let wires: Vec<_> = outputs.iter().map(|v| builder.alloc_f128(*v)).collect();
                let cells: Vec<_> = wires.iter().map(|w| LinExpr::from_wire(*w)).collect();
                for class in Class::ALL {
                    let gate = mul(&mut builder, &recursive, &selectors[class.index()]);
                    bind_lane(
                        &mut builder,
                        &cells,
                        &prev,
                        Lane::for_class(class),
                        &gate,
                        &folded[class.index()],
                    );
                }
                let (matrix, witness) = builder.build();
                assert!(matrix.satisfies(&witness));
                if let Some(expected) = digest {
                    assert_eq!(matrix.statement_digest(), expected);
                }
                digest = Some(matrix.statement_digest());
                for index in POINT..ACC {
                    let mut changed = witness.clone();
                    changed[wires[index].0 as usize] += F128::ONE;
                    assert!(!matrix.satisfies(&changed), "unbound claim cell {index}");
                }
                let mut changed = witness;
                changed[class_wire.0 as usize] += F128::ONE;
                assert!(
                    !matrix.satisfies(&changed),
                    "unauthenticated parent selector"
                );
            }
        }
    }
}
