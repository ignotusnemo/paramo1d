// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Honest streaming freezer for the canonical two-class HistoryStep bank.
//!
//! The provider replays one native-valid chain from genesis to obtain one
//! exact parent checkpoint per tier, then forks one native-valid child from
//! each checkpoint for every `(current,parent)` class. Matrices move directly
//! into the caller's store; the freezer never retains a matrix bank in RAM.

use std::sync::Arc;
use std::time::{Duration, Instant};

use noid_ivc_core::field_r1cs::FieldR1cs;

use super::{
    assemble_frozen_history_step_base, assemble_frozen_history_step_recursive,
    derive_history_step_direct_block_vk, derive_history_step_runtime_parts,
    pin_history_step_class_bank, prove_history_step, BlockRegionSidecarVk, ChainAccumulator,
    HistoryStepBlockInput, HistoryStepError, HistoryStepMatrixLease, HistoryStepMatrixSource,
    HistoryStepMatrixSourceError, HistoryStepParent, HistoryStepRuntime, HistoryStepRuntimeParts,
    HistoryStepTerminal,
};
use crate::acceptance::history_step_bank::{
    CanonicalHistoryStepClassId, PinnedHistoryStepClassBank, HISTORY_STEP_CLASS_COUNT,
    HISTORY_STEP_TIER_SLOT_COUNT,
};

/// One consuming backbone witness. The variant is the compile-time Block tier;
/// no runtime tier value can disagree with its relation type.
pub enum HistoryStepFreezeInput {
    B25(HistoryStepBlockInput<25>),
    B255(HistoryStepBlockInput<255>),
}

impl HistoryStepFreezeInput {
    fn current_slot(&self) -> usize {
        match self {
            Self::B25(_) => 0,
            Self::B255(_) => 1,
        }
    }

    fn start_accumulator(&self) -> &ChainAccumulator {
        match self {
            Self::B25(input) => input.start_accumulator(),
            Self::B255(input) => input.start_accumulator(),
        }
    }

    fn end_accumulator(&self) -> &ChainAccumulator {
        match self {
            Self::B25(input) => input.end_accumulator(),
            Self::B255(input) => input.end_accumulator(),
        }
    }
}

/// Resettable deterministic witness stream owned by release tooling.
pub trait HistoryStepFreezeInputProvider {
    type Error;

    fn reset_backbone(&mut self) -> Result<(), Self::Error>;

    fn next_backbone(
        &mut self,
        expected_start: &ChainAccumulator,
    ) -> Result<Option<HistoryStepFreezeInput>, Self::Error>;

    fn b25(
        &mut self,
        class: CanonicalHistoryStepClassId,
        expected_start: &ChainAccumulator,
    ) -> Result<HistoryStepBlockInput<25>, Self::Error>;

    fn b255(
        &mut self,
        class: CanonicalHistoryStepClassId,
        expected_start: &ChainAccumulator,
    ) -> Result<HistoryStepBlockInput<255>, Self::Error>;
}

/// Streaming release store. `install` takes matrix ownership so the caller
/// can write and drop it before any later `load` materializes a parent matrix.
pub trait HistoryStepFreezeMatrixStore: HistoryStepMatrixSource {
    type Error;

    fn install(
        &self,
        class: CanonicalHistoryStepClassId,
        matrix: FieldR1cs,
    ) -> Result<(), Self::Error>;

    /// Release-tooling progress hook. It fires exactly once per class, after
    /// the final bank-authenticated matrix has been exported. The default is
    /// intentionally silent so the proof library owns no user-facing logs.
    fn final_class_built(
        &self,
        _class: CanonicalHistoryStepClassId,
        _wires: usize,
        _elapsed: Duration,
    ) {
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HistoryStepFreezeStage {
    ProvisionalDirectBlockVk,
    ProvisionalRuntimeParts,
    BootstrapRuntime,
    BootstrapProve,
    BootstrapAssemble,
    BootstrapReplaceDirectBlockVk,
    CandidateRuntime,
    CandidateBackbone,
    CandidateClass,
    FinalBank,
    FinalRuntime,
    FinalBackbone,
    FinalClass,
}

impl core::fmt::Display for HistoryStepFreezeStage {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::ProvisionalDirectBlockVk => "provisional direct-Block VK derivation",
            Self::ProvisionalRuntimeParts => "provisional runtime-material derivation",
            Self::BootstrapRuntime => "bootstrap runtime construction",
            Self::BootstrapProve => "bootstrap backbone proving",
            Self::BootstrapAssemble => "bootstrap class assembly",
            Self::BootstrapReplaceDirectBlockVk => "bootstrap direct-Block VK replacement",
            Self::CandidateRuntime => "candidate runtime construction",
            Self::CandidateBackbone => "candidate backbone proving",
            Self::CandidateClass => "candidate class assembly",
            Self::FinalBank => "final bank construction",
            Self::FinalRuntime => "final runtime construction",
            Self::FinalBackbone => "final backbone proving",
            Self::FinalClass => "final class assembly",
        })
    }
}

#[derive(Debug)]
pub enum HistoryStepFreezeError<ProviderError, StoreError> {
    Provider(ProviderError),
    Store(StoreError),
    Relation {
        stage: HistoryStepFreezeStage,
        class: Option<CanonicalHistoryStepClassId>,
        source: HistoryStepError,
    },
    Backbone,
    ParentVk,
    DirectBlockVk(CanonicalHistoryStepClassId),
    MatrixDigest(CanonicalHistoryStepClassId),
}

impl<P: core::fmt::Display, S: core::fmt::Display> core::fmt::Display
    for HistoryStepFreezeError<P, S>
{
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Provider(error) => write!(formatter, "HistoryStep witness provider: {error}"),
            Self::Store(error) => write!(formatter, "HistoryStep matrix store: {error}"),
            Self::Relation {
                stage,
                class,
                source,
            } => {
                write!(formatter, "HistoryStep freezer {stage}")?;
                if let Some(class) = class {
                    write!(
                        formatter,
                        " for c{:02} (current B{})",
                        class.index(),
                        class.current_tier(),
                    )?;
                }
                write!(formatter, ": {source}")
            }
            Self::Backbone => formatter.write_str("HistoryStep freezer backbone is not canonical"),
            Self::ParentVk => formatter.write_str("HistoryStep parent recursion VK drifted"),
            Self::DirectBlockVk(class) => write!(
                formatter,
                "HistoryStep direct Block VK drifted in class {}",
                class.index()
            ),
            Self::MatrixDigest(class) => write!(
                formatter,
                "HistoryStep matrix digest drifted in class {}",
                class.index()
            ),
        }
    }
}

impl<P, S> HistoryStepFreezeError<P, S> {
    fn relation(
        stage: HistoryStepFreezeStage,
        class: Option<CanonicalHistoryStepClassId>,
        source: HistoryStepError,
    ) -> Self {
        Self::Relation {
            stage,
            class,
            source,
        }
    }
}

/// Final bank and complete compact runtime material. Matrix ownership remains
/// in the streaming store supplied to [`freeze_history_step_bank`].
pub struct FrozenHistoryStepBank {
    bank: PinnedHistoryStepClassBank,
    parts: HistoryStepRuntimeParts,
}

impl FrozenHistoryStepBank {
    pub fn bank(&self) -> &PinnedHistoryStepClassBank {
        &self.bank
    }

    pub fn parts(&self) -> &HistoryStepRuntimeParts {
        &self.parts
    }

    pub fn into_parts(self) -> (PinnedHistoryStepClassBank, HistoryStepRuntimeParts) {
        (self.bank, self.parts)
    }
}

struct SharedFreezeMatrixSource<S>(Arc<S>);

impl<S: HistoryStepMatrixSource> HistoryStepMatrixSource for SharedFreezeMatrixSource<S> {
    fn load(
        &self,
        class: CanonicalHistoryStepClassId,
    ) -> Result<HistoryStepMatrixLease, HistoryStepMatrixSourceError> {
        self.0.load(class)
    }
}

fn runtime<S: HistoryStepMatrixSource + 'static>(
    digests: [[u8; 32]; HISTORY_STEP_CLASS_COUNT],
    parts: &HistoryStepRuntimeParts,
    store: &Arc<S>,
) -> Result<HistoryStepRuntime, HistoryStepError> {
    HistoryStepRuntime::new(
        pin_history_step_class_bank(digests, parts)?,
        Box::new(SharedFreezeMatrixSource(Arc::clone(store))),
        parts.clone(),
    )
}

fn prove_input(
    runtime: &HistoryStepRuntime,
    parent: Option<&HistoryStepTerminal>,
    input: HistoryStepFreezeInput,
) -> Result<HistoryStepTerminal, HistoryStepError> {
    match input {
        HistoryStepFreezeInput::B25(input) => prove_history_step(runtime, parent, input),
        HistoryStepFreezeInput::B255(input) => prove_history_step(runtime, parent, input),
    }
}

fn assemble_input(
    runtime: &HistoryStepRuntime,
    parent: Option<&HistoryStepTerminal>,
    input: HistoryStepFreezeInput,
) -> Result<super::FrozenHistoryStep, HistoryStepError> {
    macro_rules! assemble {
        ($input:expr) => {
            match parent {
                Some(parent) => assemble_frozen_history_step_recursive(
                    runtime,
                    HistoryStepParent::new(runtime, parent)?,
                    $input,
                ),
                None => assemble_frozen_history_step_base(runtime, $input),
            }
        };
    }
    match input {
        HistoryStepFreezeInput::B25(input) => assemble!(input),
        HistoryStepFreezeInput::B255(input) => assemble!(input),
    }
}

fn derive_provisional_parts<P, S>(
    provider: &mut P,
) -> Result<HistoryStepRuntimeParts, HistoryStepFreezeError<P::Error, S>>
where
    P: HistoryStepFreezeInputProvider,
{
    provider
        .reset_backbone()
        .map_err(HistoryStepFreezeError::Provider)?;
    let mut expected = crate::accumulator::genesis_accumulator();
    let mut vks: [Option<BlockRegionSidecarVk>; HISTORY_STEP_TIER_SLOT_COUNT] =
        std::array::from_fn(|_| None);
    while vks.iter().any(Option::is_none) {
        let input = provider
            .next_backbone(&expected)
            .map_err(HistoryStepFreezeError::Provider)?
            .ok_or(HistoryStepFreezeError::Backbone)?;
        if input.start_accumulator() != &expected {
            return Err(HistoryStepFreezeError::Backbone);
        }
        let slot = input.current_slot();
        expected = input.end_accumulator().clone();
        if vks[slot].is_none() {
            let class =
                CanonicalHistoryStepClassId::new(slot).expect("backbone tier slot is canonical");
            let vk = match input {
                HistoryStepFreezeInput::B25(input) => derive_history_step_direct_block_vk(input),
                HistoryStepFreezeInput::B255(input) => derive_history_step_direct_block_vk(input),
            }
            .map_err(|source| {
                HistoryStepFreezeError::relation(
                    HistoryStepFreezeStage::ProvisionalDirectBlockVk,
                    Some(class),
                    source,
                )
            })?;
            vks[slot] = Some(vk);
        }
    }
    provider
        .reset_backbone()
        .map_err(HistoryStepFreezeError::Provider)?;
    derive_history_step_runtime_parts(vks.map(|vk| vk.expect("all tier VKs derived"))).map_err(
        |source| {
            HistoryStepFreezeError::relation(
                HistoryStepFreezeStage::ProvisionalRuntimeParts,
                None,
                source,
            )
        },
    )
}

fn prove_backbone<P, S>(
    runtime: &HistoryStepRuntime,
    provider: &mut P,
    stage: HistoryStepFreezeStage,
) -> Result<[HistoryStepTerminal; HISTORY_STEP_TIER_SLOT_COUNT], HistoryStepFreezeError<P::Error, S>>
where
    P: HistoryStepFreezeInputProvider,
{
    provider
        .reset_backbone()
        .map_err(HistoryStepFreezeError::Provider)?;
    let mut expected = crate::accumulator::genesis_accumulator();
    let mut tip: Option<HistoryStepTerminal> = None;
    let mut checkpoints: [Option<HistoryStepTerminal>; HISTORY_STEP_TIER_SLOT_COUNT] =
        std::array::from_fn(|_| None);
    while let Some(input) = provider
        .next_backbone(&expected)
        .map_err(HistoryStepFreezeError::Provider)?
    {
        if input.start_accumulator() != &expected {
            return Err(HistoryStepFreezeError::Backbone);
        }
        let advertised_slot = input.current_slot();
        let class = CanonicalHistoryStepClassId::new(advertised_slot)
            .ok_or(HistoryStepFreezeError::Backbone)?;
        let next = prove_input(runtime, tip.as_ref(), input)
            .map_err(|source| HistoryStepFreezeError::relation(stage, Some(class), source))?;
        if next.class_id().current_slot() != advertised_slot {
            return Err(HistoryStepFreezeError::Backbone);
        }
        expected = next.accumulator().clone();
        if let Some(previous) = tip.take() {
            let previous_slot = previous.class_id().current_slot();
            if advertised_slot < previous_slot {
                return Err(HistoryStepFreezeError::Backbone);
            }
            if advertised_slot > previous_slot {
                if checkpoints[previous_slot].replace(previous).is_some() {
                    return Err(HistoryStepFreezeError::Backbone);
                }
            }
        }
        tip = Some(next);
    }
    let tip = tip.ok_or(HistoryStepFreezeError::Backbone)?;
    let slot = tip.class_id().current_slot();
    if checkpoints[slot].replace(tip).is_some() {
        return Err(HistoryStepFreezeError::Backbone);
    }
    let [Some(b25), Some(b255)] = checkpoints else {
        return Err(HistoryStepFreezeError::Backbone);
    };
    Ok([b25, b255])
}

fn class_input<P, S>(
    provider: &mut P,
    class: CanonicalHistoryStepClassId,
    start: &ChainAccumulator,
) -> Result<HistoryStepFreezeInput, HistoryStepFreezeError<P::Error, S>>
where
    P: HistoryStepFreezeInputProvider,
{
    match class.current_slot() {
        0 => provider.b25(class, start).map(HistoryStepFreezeInput::B25),
        1 => provider
            .b255(class, start)
            .map(HistoryStepFreezeInput::B255),
        _ => unreachable!("canonical class current slot"),
    }
    .map_err(HistoryStepFreezeError::Provider)
}

fn build_all_classes<P, S>(
    runtime: &HistoryStepRuntime,
    parts: &HistoryStepRuntimeParts,
    provider: &mut P,
    store: &S,
    checkpoints: &[HistoryStepTerminal; HISTORY_STEP_TIER_SLOT_COUNT],
    expected: Option<&[[u8; 32]; HISTORY_STEP_CLASS_COUNT]>,
    stage: HistoryStepFreezeStage,
) -> Result<[[u8; 32]; HISTORY_STEP_CLASS_COUNT], HistoryStepFreezeError<P::Error, S::Error>>
where
    P: HistoryStepFreezeInputProvider,
    S: HistoryStepFreezeMatrixStore,
{
    let mut digests = [[0u8; 32]; HISTORY_STEP_CLASS_COUNT];
    for index in 0..HISTORY_STEP_CLASS_COUNT {
        let started = Instant::now();
        let class =
            CanonicalHistoryStepClassId::from_index(index).expect("fixed HistoryStep class index");
        // Freeze against the B25 checkpoint, then rebuild against every other
        // parent checkpoint below. The two-arm relation must make those
        // matrices byte-identical for a fixed current class.
        let parent = &checkpoints[0];
        let input = class_input::<P, S::Error>(provider, class, parent.accumulator())?;
        let built = assemble_input(runtime, Some(parent), input)
            .map_err(|source| HistoryStepFreezeError::relation(stage, Some(class), source))?;
        if built.class_id() != class
            || built.parent_recursion_vk() != parts.parent_recursion_vk()
            || built.direct_block_vk() != &parts.direct_block_vks()[class.current_slot()]
        {
            return Err(
                if built.parent_recursion_vk() != parts.parent_recursion_vk() {
                    HistoryStepFreezeError::ParentVk
                } else {
                    HistoryStepFreezeError::DirectBlockVk(class)
                },
            );
        }
        let digest = built.matrix().structural_statement_digest();
        let wires = built.useful_rows();
        for alternate_parent in checkpoints.iter().skip(1) {
            let alternate_input =
                class_input::<P, S::Error>(provider, class, alternate_parent.accumulator())?;
            let alternate = assemble_input(runtime, Some(alternate_parent), alternate_input)
                .map_err(|source| HistoryStepFreezeError::relation(stage, Some(class), source))?;
            if alternate.class_id() != class
                || alternate.parent_recursion_vk() != parts.parent_recursion_vk()
                || alternate.direct_block_vk() != &parts.direct_block_vks()[class.current_slot()]
            {
                return Err(HistoryStepFreezeError::ParentVk);
            }
            if alternate.useful_rows() != wires
                || alternate.matrix().structural_statement_digest() != digest
            {
                return Err(HistoryStepFreezeError::MatrixDigest(class));
            }
        }
        if expected.is_some_and(|expected| expected[index] != digest) {
            return Err(HistoryStepFreezeError::MatrixDigest(class));
        }
        digests[index] = digest;
        store
            .install(class, built.into_matrix())
            .map_err(HistoryStepFreezeError::Store)?;
        if expected.is_some() {
            store.final_class_built(class, wires, started.elapsed());
        }
    }
    Ok(digests)
}

/// Freeze both launch classes from honest native-valid witnesses. Bootstrap
/// proofs use provisional bank values only inside release tooling; the final
/// pass rebuilds every matrix under the completed bank and rejects any digest
/// or VK drift before returning release material.
pub fn freeze_history_step_bank<P, S>(
    provider: &mut P,
    store: Arc<S>,
) -> Result<FrozenHistoryStepBank, HistoryStepFreezeError<P::Error, S::Error>>
where
    P: HistoryStepFreezeInputProvider,
    S: HistoryStepFreezeMatrixStore + 'static,
{
    let mut parts = derive_provisional_parts::<P, S::Error>(provider)?;
    let mut digests = [[0u8; 32]; HISTORY_STEP_CLASS_COUNT];
    let mut known = [false; HISTORY_STEP_CLASS_COUNT];

    // The two-arm parent envelope pins both direct-Block VK digests into
    // every class matrix, so replacing one provisional VK staleness-wipes
    // every matrix frozen before it. Discovery therefore runs twice: phase A
    // walks the backbone only until every provisional VK has been replaced
    // by its integrated twin (wiping and restarting on each replacement),
    // phase B reruns discovery under the stable parts and freezes both
    // matrices — any further VK drift there is a hard error.
    let mut actualized = [false; HISTORY_STEP_TIER_SLOT_COUNT];
    'phases: for stable_parts in [false, true] {
        digests = [[0u8; 32]; HISTORY_STEP_CLASS_COUNT];
        known = [false; HISTORY_STEP_CLASS_COUNT];
        let pass_budget = if stable_parts {
            HISTORY_STEP_CLASS_COUNT + 1
        } else {
            4 * HISTORY_STEP_CLASS_COUNT
        };
        for _ in 0..pass_budget {
            let partial = runtime(digests, &parts, &store).map_err(|source| {
                HistoryStepFreezeError::relation(
                    HistoryStepFreezeStage::BootstrapRuntime,
                    None,
                    source,
                )
            })?;
            provider
                .reset_backbone()
                .map_err(HistoryStepFreezeError::Provider)?;
            let mut expected = crate::accumulator::genesis_accumulator();
            let mut tip: Option<HistoryStepTerminal> = None;
            let mut discovered = false;
            while let Some(input) = provider
                .next_backbone(&expected)
                .map_err(HistoryStepFreezeError::Provider)?
            {
                if input.start_accumulator() != &expected {
                    return Err(HistoryStepFreezeError::Backbone);
                }
                let current_slot = input.current_slot();
                let class = CanonicalHistoryStepClassId::new(current_slot)
                    .ok_or(HistoryStepFreezeError::Backbone)?;
                if known[class.index()] {
                    let next = prove_input(&partial, tip.as_ref(), input).map_err(|source| {
                        HistoryStepFreezeError::relation(
                            HistoryStepFreezeStage::BootstrapProve,
                            Some(class),
                            source,
                        )
                    })?;
                    expected = next.accumulator().clone();
                    tip = Some(next);
                    continue;
                }
                let built = assemble_input(&partial, tip.as_ref(), input).map_err(|source| {
                    HistoryStepFreezeError::relation(
                        HistoryStepFreezeStage::BootstrapAssemble,
                        Some(class),
                        source,
                    )
                })?;
                if built.class_id() != class
                    || built.parent_recursion_vk() != parts.parent_recursion_vk()
                {
                    return Err(HistoryStepFreezeError::ParentVk);
                }
                let actual_vk = built.direct_block_vk().clone();
                let vk_changed = &actual_vk != &parts.direct_block_vks()[current_slot];
                let digest = built.matrix().structural_statement_digest();
                store
                    .install(class, built.into_matrix())
                    .map_err(HistoryStepFreezeError::Store)?;
                if vk_changed {
                    if stable_parts {
                        return Err(HistoryStepFreezeError::DirectBlockVk(class));
                    }
                    parts = parts
                        .with_direct_block_vk(current_slot, actual_vk)
                        .map_err(|source| {
                            HistoryStepFreezeError::relation(
                                HistoryStepFreezeStage::BootstrapReplaceDirectBlockVk,
                                Some(class),
                                source,
                            )
                        })?;
                    digests = [[0u8; 32]; HISTORY_STEP_CLASS_COUNT];
                    known = [false; HISTORY_STEP_CLASS_COUNT];
                } else {
                    digests[class.index()] = digest;
                    known[class.index()] = true;
                }
                actualized[current_slot] = true;
                discovered = true;
                break;
            }
            if !stable_parts && actualized.iter().all(|&slot| slot) {
                continue 'phases;
            }
            if !discovered {
                break;
            }
        }
    }
    if !known.iter().all(|&class| class) {
        return Err(HistoryStepFreezeError::Backbone);
    }

    let partial = runtime(digests, &parts, &store).map_err(|source| {
        HistoryStepFreezeError::relation(HistoryStepFreezeStage::CandidateRuntime, None, source)
    })?;
    let checkpoints = prove_backbone::<P, S::Error>(
        &partial,
        provider,
        HistoryStepFreezeStage::CandidateBackbone,
    )?;
    let candidate = build_all_classes(
        &partial,
        &parts,
        provider,
        store.as_ref(),
        &checkpoints,
        None,
        HistoryStepFreezeStage::CandidateClass,
    )?;
    for index in 0..HISTORY_STEP_CLASS_COUNT {
        if known[index] && candidate[index] != digests[index] {
            let class = CanonicalHistoryStepClassId::from_index(index)
                .expect("fixed HistoryStep class index");
            return Err(HistoryStepFreezeError::MatrixDigest(class));
        }
    }

    let final_bank = pin_history_step_class_bank(candidate, &parts).map_err(|source| {
        HistoryStepFreezeError::relation(HistoryStepFreezeStage::FinalBank, None, source)
    })?;
    let final_runtime = HistoryStepRuntime::new(
        final_bank.clone(),
        Box::new(SharedFreezeMatrixSource(Arc::clone(&store))),
        parts.clone(),
    )
    .map_err(|source| {
        HistoryStepFreezeError::relation(HistoryStepFreezeStage::FinalRuntime, None, source)
    })?;
    let final_checkpoints = prove_backbone::<P, S::Error>(
        &final_runtime,
        provider,
        HistoryStepFreezeStage::FinalBackbone,
    )?;
    build_all_classes(
        &final_runtime,
        &parts,
        provider,
        store.as_ref(),
        &final_checkpoints,
        Some(&candidate),
        HistoryStepFreezeStage::FinalClass,
    )?;

    Ok(FrozenHistoryStepBank {
        bank: final_bank,
        parts,
    })
}
