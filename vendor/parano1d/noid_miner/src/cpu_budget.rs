// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Process-wide CPU admission for internal PoW, HistoryStep, verification, and
//! wallet-proof work.
//!
//! Block production is a sequence of CPU-heavy phases, not a permanent CPU
//! split: all workers search PoW, then the same workers prove HistoryStep. The
//! process therefore owns exactly one fixed Rayon pool. An internal miner
//! leaves a small host-visible CPU reserve for networking, RPC and storage;
//! inbound verification also enters the shared pool, so no
//! caller can activate a second full worker set.
//!
//! A local wallet proof and its admission verification are latency-sensitive
//! and have priority over the interruptible PoW phase. Registering either
//! makes PoW stop at its next cancellation checkpoint. Existing P2P/snapshot
//! verification remains work-conserving beside mining and gains no authority
//! to cancel PoW. An already-running HistoryStep drains before local wallet
//! work starts; network verification keeps its existing concurrent policy.

use std::sync::{
    atomic::{AtomicU8, AtomicUsize, Ordering},
    Arc, Condvar, Mutex, OnceLock,
};
use std::time::Instant;

const PROCESS_PHASE_WORKER_STACK_BYTES: usize = 64 * 1024 * 1024;

thread_local! {
    /// Rayon exposes a thread index for every pool, so an index alone cannot
    /// distinguish our process pool from the global pool. Mark the actual
    /// worker lifetime instead; nested phase boundaries can then execute
    /// directly without re-injecting a job into the same scheduler.
    static PROCESS_PHASE_POOL_WORKER: std::cell::Cell<bool> = const {
        std::cell::Cell::new(false)
    };
}

/// Whether this process performs PoW internally.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProcessCpuBudgetMode {
    /// Prover and external-miner nodes do not enter the internal PoW phase.
    /// The one process pool may contain every host-visible CPU.
    ProofOnly,
    /// Internal mining enables PoW within the protocol-safe worker ceiling.
    InternalMiner,
}

/// Logical CPUs kept outside the proof/PoW Rayon pool so the daemon continues
/// to drain headers, serve peers, answer RPC and commit storage while mining.
/// This is scheduler capacity, not hard CPU affinity: the OS may run any node
/// task on any core.
pub const fn mining_protocol_thread_reserve(available_threads: usize) -> usize {
    match available_threads {
        0 | 1 => 0,
        2..=7 => 1,
        _ => 2,
    }
}

/// Production ceiling for internal proof and PoW workers.
pub const fn internal_miner_thread_ceiling(available_threads: usize) -> usize {
    let usable =
        available_threads.saturating_sub(mining_protocol_thread_reserve(available_threads));
    if usable == 0 {
        1
    } else {
        usable
    }
}

/// Immutable worker-count plan for one process and its sequential phases.
///
/// Phase capacities are intentionally not additive. For an internal miner on
/// 12 visible CPUs this reports one 10-worker pool, a 10-worker PoW phase, and
/// a 10-worker HistoryStep phase. Those phases reuse the same workers while
/// two logical CPUs remain schedulable for protocol work.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProcessCpuBudgetPlan {
    pub available_threads: usize,
    pub shared_pool_threads: usize,
    pub pow_phase_threads: usize,
    pub history_step_phase_threads: usize,
    pub inbound_verifier_threads: usize,
}

impl ProcessCpuBudgetPlan {
    /// Total Rayon workers admitted by this plan. Phase capacities above are
    /// views of this same worker set and must never be summed.
    pub const fn admitted_rayon_threads(self) -> usize {
        self.shared_pool_threads
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ProcessCpuBudgetError {
    #[error("process CPU budget is not configured")]
    NotConfigured,
    #[error("process CPU budget requires at least one available logical CPU")]
    NoAvailableThreads,
    #[error(
        "requested CPU thread count {requested} is outside the host-visible range 1..={available}"
    )]
    InvalidThreadCount { requested: usize, available: usize },
    #[error("internal PoW phase is disabled for a proof-only process")]
    PowPhaseDisabled,
    #[error("failed to build {role} Rayon pool: {detail}")]
    PoolBuild { role: &'static str, detail: String },
    #[error(
        "process CPU budget is already configured as {active:?}, requested incompatible {requested:?}"
    )]
    AlreadyConfigured {
        active: ProcessCpuBudgetPlan,
        requested: ProcessCpuBudgetPlan,
    },
}

/// Calculate the fixed phase plan without constructing any threads.
///
pub fn plan_process_cpu_budget(
    available_threads: usize,
    mode: ProcessCpuBudgetMode,
) -> Result<ProcessCpuBudgetPlan, ProcessCpuBudgetError> {
    let worker_threads = match mode {
        ProcessCpuBudgetMode::ProofOnly => available_threads,
        ProcessCpuBudgetMode::InternalMiner => internal_miner_thread_ceiling(available_threads),
    };
    plan_process_cpu_budget_with_threads(available_threads, worker_threads, mode)
}

/// Calculate a fixed phase plan with an explicit worker limit.
///
/// The host-visible count remains part of the plan for truthful UI and logs;
/// every CPU-heavy phase reuses exactly `worker_threads` workers.
pub fn plan_process_cpu_budget_with_threads(
    available_threads: usize,
    worker_threads: usize,
    mode: ProcessCpuBudgetMode,
) -> Result<ProcessCpuBudgetPlan, ProcessCpuBudgetError> {
    if available_threads == 0 {
        return Err(ProcessCpuBudgetError::NoAvailableThreads);
    }
    if worker_threads == 0 || worker_threads > available_threads {
        return Err(ProcessCpuBudgetError::InvalidThreadCount {
            requested: worker_threads,
            available: available_threads,
        });
    }

    let pow_phase_threads = match mode {
        ProcessCpuBudgetMode::ProofOnly => 0,
        ProcessCpuBudgetMode::InternalMiner => worker_threads,
    };
    let plan = ProcessCpuBudgetPlan {
        available_threads,
        shared_pool_threads: worker_threads,
        pow_phase_threads,
        history_step_phase_threads: worker_threads,
        inbound_verifier_threads: worker_threads,
    };
    debug_assert_eq!(plan.admitted_rayon_threads(), worker_threads);
    Ok(plan)
}

struct ProcessCpuBudget {
    plan: ProcessCpuBudgetPlan,
    phase_pool: Arc<rayon::ThreadPool>,
    observed_phases: AtomicU8,
    phase_admission: Mutex<PhaseAdmissionState>,
    phase_ready: Condvar,
    wallet_priority_requests: AtomicUsize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProcessCpuPhase {
    Pow,
    HistoryStep,
    InboundVerify,
    WalletProof,
    WalletVerify,
}

impl ProcessCpuPhase {
    const fn label(self) -> &'static str {
        match self {
            Self::Pow => "PoW",
            Self::HistoryStep => "HistoryStep",
            Self::InboundVerify => "InboundVerify",
            Self::WalletProof => "WalletProof",
            Self::WalletVerify => "WalletVerify",
        }
    }

    const fn bit(self) -> u8 {
        match self {
            Self::Pow => 1 << 0,
            Self::HistoryStep => 1 << 1,
            Self::InboundVerify => 1 << 2,
            Self::WalletProof => 1 << 3,
            Self::WalletVerify => 1 << 4,
        }
    }

    const fn is_wallet_priority(self) -> bool {
        matches!(self, Self::WalletProof | Self::WalletVerify)
    }
}

#[derive(Default)]
struct PhaseAdmissionState {
    active_exclusive: Option<ProcessCpuPhase>,
}

struct PhaseAdmissionGuard<'a> {
    budget: &'a ProcessCpuBudget,
    phase: ProcessCpuPhase,
}

impl Drop for PhaseAdmissionGuard<'_> {
    fn drop(&mut self) {
        let mut admission = self
            .budget
            .phase_admission
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        debug_assert_ne!(self.phase, ProcessCpuPhase::InboundVerify);
        debug_assert_eq!(admission.active_exclusive, Some(self.phase));
        admission.active_exclusive = None;
        if self.phase.is_wallet_priority() {
            let previous = self
                .budget
                .wallet_priority_requests
                .fetch_sub(1, Ordering::SeqCst);
            debug_assert!(previous > 0);
        }
        drop(admission);
        self.budget.phase_ready.notify_all();
    }
}

impl ProcessCpuBudget {
    fn build(plan: ProcessCpuBudgetPlan) -> Result<Self, ProcessCpuBudgetError> {
        let phase_pool = rayon::ThreadPoolBuilder::new()
            .num_threads(plan.shared_pool_threads)
            .stack_size(PROCESS_PHASE_WORKER_STACK_BYTES)
            .thread_name(|index| format!("noid-cpu-{index}"))
            .start_handler(|_| {
                PROCESS_PHASE_POOL_WORKER.with(|marker| {
                    debug_assert!(!marker.get());
                    marker.set(true);
                });
                // These workers own the 64-MiB stack required by the deep
                // recursive verifier. Keep verification on this admitted
                // worker instead of activating an extra worker pool.
                noid_ivc_core::verifier::set_budgeted_large_stack_worker(true);
            })
            .exit_handler(|_| {
                noid_ivc_core::verifier::set_budgeted_large_stack_worker(false);
                PROCESS_PHASE_POOL_WORKER.with(|marker| marker.set(false));
            })
            .build()
            .map(Arc::new)
            .map_err(|error| ProcessCpuBudgetError::PoolBuild {
                role: "shared phase",
                detail: error.to_string(),
            })?;
        Ok(Self {
            plan,
            phase_pool,
            observed_phases: AtomicU8::new(0),
            phase_admission: Mutex::new(PhaseAdmissionState::default()),
            phase_ready: Condvar::new(),
            wallet_priority_requests: AtomicUsize::new(0),
        })
    }

    fn admit_phase(&self, phase: ProcessCpuPhase) -> PhaseAdmissionGuard<'_> {
        debug_assert_ne!(phase, ProcessCpuPhase::InboundVerify);
        if phase.is_wallet_priority() {
            // Publish before taking the admission lock so active PoW workers
            // and newly queued block-production phases yield to the local user.
            self.wallet_priority_requests.fetch_add(1, Ordering::SeqCst);
        }

        let mut admission = self
            .phase_admission
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if phase.is_wallet_priority() {
            while admission.active_exclusive.is_some() {
                admission = self
                    .phase_ready
                    .wait(admission)
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
            }
            admission.active_exclusive = Some(phase);
        } else {
            // PoW and HistoryStep remain mutually exclusive. Neither may jump
            // ahead of a published local-wallet request.
            while admission.active_exclusive.is_some() || self.wallet_priority_requested() {
                admission = self
                    .phase_ready
                    .wait(admission)
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
            }
            admission.active_exclusive = Some(phase);
        }
        drop(admission);
        PhaseAdmissionGuard {
            budget: self,
            phase,
        }
    }

    fn install_phase<R: Send>(
        &self,
        phase: ProcessCpuPhase,
        operation: impl FnOnce() -> R + Send,
    ) -> R {
        if PROCESS_PHASE_POOL_WORKER.with(|marker| marker.get()) {
            return self.run_phase_operation(phase, 0, true, operation);
        }
        let queued_at = Instant::now();
        if phase == ProcessCpuPhase::InboundVerify {
            // Preserve the original network behavior exactly: verification is
            // work-conserving beside every other phase and never enters the
            // local-wallet priority gate.
            return self.phase_pool.install(|| {
                let pool_queue_ms = queued_at.elapsed().as_millis() as u64;
                self.run_phase_operation(phase, pool_queue_ms, false, operation)
            });
        }
        let _admission = self.admit_phase(phase);
        self.phase_pool.install(|| {
            let pool_queue_ms = queued_at.elapsed().as_millis() as u64;
            self.run_phase_operation(phase, pool_queue_ms, false, operation)
        })
    }

    fn wallet_priority_requested(&self) -> bool {
        self.wallet_priority_requests.load(Ordering::Acquire) > 0
    }

    fn pow_preemption_requested(&self) -> bool {
        self.wallet_priority_requested()
    }

    fn run_phase_operation<R>(
        &self,
        phase: ProcessCpuPhase,
        pool_queue_ms: u64,
        nested_same_pool: bool,
        operation: impl FnOnce() -> R,
    ) -> R {
        debug_assert!(PROCESS_PHASE_POOL_WORKER.with(|marker| marker.get()));
        let observed_threads = rayon::current_num_threads();
        debug_assert_eq!(observed_threads, self.plan.shared_pool_threads);
        let first_phase_entry =
            self.observed_phases.fetch_or(phase.bit(), Ordering::AcqRel) & phase.bit() == 0;
        tracing::debug!(
            phase = phase.label(),
            phase_threads = observed_threads,
            shared_pool_threads = self.plan.shared_pool_threads,
            pool_queue_ms,
            nested_same_pool,
            first_phase_entry,
            "CPU phase entered shared bounded Rayon pool"
        );
        operation()
    }

    #[cfg(test)]
    fn phase_pool(&self) -> Arc<rayon::ThreadPool> {
        Arc::clone(&self.phase_pool)
    }
}

static PROCESS_CPU_BUDGET: OnceLock<Arc<ProcessCpuBudget>> = OnceLock::new();

fn host_available_threads() -> usize {
    std::thread::available_parallelism()
        .map(|parallelism| parallelism.get())
        .unwrap_or(1)
        .max(1)
}

fn select_process_worker_threads(
    available: usize,
    mode: ProcessCpuBudgetMode,
    requested_threads: Option<usize>,
) -> Result<usize, ProcessCpuBudgetError> {
    if available == 0 {
        return Err(ProcessCpuBudgetError::NoAvailableThreads);
    }
    if let Some(requested) = requested_threads {
        if requested == 0 || requested > available {
            return Err(ProcessCpuBudgetError::InvalidThreadCount {
                requested,
                available,
            });
        }
    }
    let ceiling = match mode {
        ProcessCpuBudgetMode::ProofOnly => available,
        ProcessCpuBudgetMode::InternalMiner => internal_miner_thread_ceiling(available),
    };
    Ok(requested_threads.unwrap_or(ceiling).min(ceiling))
}

/// Configure the fixed process pool exactly once. Repeating the same plan is
/// idempotent; attempting to change it after any worker can have started is a
/// startup error. The pool uses every CPU visible through the process affinity
/// and cgroup limits; the global `RAYON_NUM_THREADS` setting cannot silently
/// restore a one-core PoW path or construct an independent scheduler.
pub fn configure_process_cpu_budget(
    mode: ProcessCpuBudgetMode,
) -> Result<ProcessCpuBudgetPlan, ProcessCpuBudgetError> {
    configure_process_cpu_budget_with_threads(mode, None)
}

/// Configure the process pool with an optional startup worker limit.
/// `None` uses every visible CPU for a proof-only node and the protocol-safe
/// ceiling for an internal miner. Explicit miner requests are capped at the
/// same ceiling so a local tuning choice cannot starve the P2P reactor.
pub fn configure_process_cpu_budget_with_threads(
    mode: ProcessCpuBudgetMode,
    requested_threads: Option<usize>,
) -> Result<ProcessCpuBudgetPlan, ProcessCpuBudgetError> {
    let available = host_available_threads();
    let worker_threads = select_process_worker_threads(available, mode, requested_threads)?;
    if requested_threads.is_some_and(|requested| requested > worker_threads) {
        tracing::info!(
            requested_threads = requested_threads.unwrap_or(worker_threads),
            admitted_threads = worker_threads,
            protocol_reserve = available.saturating_sub(worker_threads),
            "mining CPU request capped to preserve node networking capacity"
        );
    }
    let requested = plan_process_cpu_budget_with_threads(available, worker_threads, mode)?;
    if let Some(active) = PROCESS_CPU_BUDGET.get() {
        return if active.plan == requested {
            Ok(active.plan)
        } else {
            Err(ProcessCpuBudgetError::AlreadyConfigured {
                active: active.plan,
                requested,
            })
        };
    }

    let candidate = Arc::new(ProcessCpuBudget::build(requested)?);
    if PROCESS_CPU_BUDGET.set(candidate).is_err() {
        let active = PROCESS_CPU_BUDGET
            .get()
            .expect("process CPU budget initialized by racing caller");
        if active.plan != requested {
            return Err(ProcessCpuBudgetError::AlreadyConfigured {
                active: active.plan,
                requested,
            });
        }
    }
    tracing::debug!(
        available_threads = requested.available_threads,
        shared_pool_threads = requested.shared_pool_threads,
        pow_phase_threads = requested.pow_phase_threads,
        history_step_phase_threads = requested.history_step_phase_threads,
        inbound_verifier_threads = requested.inbound_verifier_threads,
        admitted_rayon_threads = requested.admitted_rayon_threads(),
        "single bounded process CPU pool configured for sequential phases"
    );
    Ok(requested)
}

/// The active plan, if startup has already configured the process pool.
pub fn configured_process_cpu_budget() -> Option<ProcessCpuBudgetPlan> {
    PROCESS_CPU_BUDGET.get().map(|budget| budget.plan)
}

fn process_cpu_budget_from(
    configured: &OnceLock<Arc<ProcessCpuBudget>>,
) -> Result<Arc<ProcessCpuBudget>, ProcessCpuBudgetError> {
    configured
        .get()
        .map(Arc::clone)
        .ok_or(ProcessCpuBudgetError::NotConfigured)
}

fn process_cpu_budget() -> Result<Arc<ProcessCpuBudget>, ProcessCpuBudgetError> {
    process_cpu_budget_from(&PROCESS_CPU_BUDGET)
}

/// Run the PoW search phase on the complete shared process pool.
///
/// The production miner calls this phase before HistoryStep. The pool itself
/// remains work-conserving for inbound verification; phase ordering belongs to
/// the miner state machine, not to a second scheduler or worker set.
pub fn install_pow_phase_cpu<R: Send>(
    operation: impl FnOnce() -> R + Send,
) -> Result<R, ProcessCpuBudgetError> {
    let budget = process_cpu_budget()?;
    if budget.plan.pow_phase_threads == 0 {
        return Err(ProcessCpuBudgetError::PowPhaseDisabled);
    }
    Ok(budget.install_phase(ProcessCpuPhase::Pow, operation))
}

/// Run the fused HistoryStep build/prove phase on the complete shared process
/// pool after PoW has fixed the block nonce.
pub fn install_history_step_phase_cpu<R: Send>(
    operation: impl FnOnce() -> R + Send,
) -> Result<R, ProcessCpuBudgetError> {
    Ok(process_cpu_budget()?.install_phase(ProcessCpuPhase::HistoryStep, operation))
}

/// Run inbound terminal verification on the same fixed process pool as PoW
/// and HistoryStep. This admits no independent verifier worker set and
/// preserves the existing work-conserving network policy beside mining.
pub fn install_inbound_verifier_cpu<R: Send>(
    operation: impl FnOnce() -> R + Send,
) -> Result<R, ProcessCpuBudgetError> {
    Ok(process_cpu_budget()?.install_phase(ProcessCpuPhase::InboundVerify, operation))
}

/// Run a latency-sensitive local wallet authorization proof on the same fixed
/// process pool as block production.
///
/// The request preempts only interruptible PoW. An already-running
/// HistoryStep remains atomic and drains first; network verification keeps its
/// existing work-conserving behavior.
pub fn install_wallet_proof_cpu<R: Send>(
    operation: impl FnOnce() -> R + Send,
) -> Result<R, ProcessCpuBudgetError> {
    Ok(process_cpu_budget()?.install_phase(ProcessCpuPhase::WalletProof, operation))
}

/// Run the authorization verification for a locally built wallet transaction.
///
/// Unlike ordinary inbound network verification, this remains part of the
/// latency-sensitive GUI submission and preempts interruptible PoW.
pub fn install_wallet_verifier_cpu<R: Send>(
    operation: impl FnOnce() -> R + Send,
) -> Result<R, ProcessCpuBudgetError> {
    Ok(process_cpu_budget()?.install_phase(ProcessCpuPhase::WalletVerify, operation))
}

/// Whether latency-sensitive local wallet work is waiting for or currently
/// owns the shared pool.
///
/// PoW polls this alongside its ordinary cancellation flag. Keeping the signal
/// inside the CPU budget prevents the RPC and miner layers from sharing a
/// second lifecycle channel. Network verification does not set this signal.
pub(crate) fn pow_preemption_requested() -> bool {
    PROCESS_CPU_BUDGET
        .get()
        .is_some_and(|budget| budget.pow_preemption_requested())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unconfigured_process_budget_fails_closed_without_panicking() {
        let unconfigured = OnceLock::new();
        assert!(matches!(
            process_cpu_budget_from(&unconfigured),
            Err(ProcessCpuBudgetError::NotConfigured)
        ));
    }

    #[test]
    fn twelve_thread_miner_reserves_two_for_protocol_work() {
        assert_eq!(
            plan_process_cpu_budget(12, ProcessCpuBudgetMode::ProofOnly).unwrap(),
            ProcessCpuBudgetPlan {
                available_threads: 12,
                shared_pool_threads: 12,
                pow_phase_threads: 0,
                history_step_phase_threads: 12,
                inbound_verifier_threads: 12,
            }
        );
        let default_plan =
            plan_process_cpu_budget(12, ProcessCpuBudgetMode::InternalMiner).unwrap();
        assert_eq!(
            default_plan,
            ProcessCpuBudgetPlan {
                available_threads: 12,
                shared_pool_threads: 10,
                pow_phase_threads: 10,
                history_step_phase_threads: 10,
                inbound_verifier_threads: 10,
            }
        );
        assert_eq!(default_plan.admitted_rayon_threads(), 10);
        assert_ne!(default_plan.pow_phase_threads, 1);
    }

    #[test]
    fn miner_protocol_reserve_scales_for_small_and_large_hosts() {
        assert_eq!(internal_miner_thread_ceiling(1), 1);
        assert_eq!(internal_miner_thread_ceiling(2), 1);
        assert_eq!(internal_miner_thread_ceiling(4), 3);
        assert_eq!(internal_miner_thread_ceiling(7), 6);
        assert_eq!(internal_miner_thread_ceiling(8), 6);
        assert_eq!(internal_miner_thread_ceiling(12), 10);
        assert_eq!(internal_miner_thread_ceiling(32), 30);
    }

    #[test]
    fn explicit_all_core_mining_request_is_capped_but_validated() {
        assert_eq!(
            select_process_worker_threads(12, ProcessCpuBudgetMode::InternalMiner, Some(12))
                .unwrap(),
            10
        );
        assert_eq!(
            select_process_worker_threads(12, ProcessCpuBudgetMode::InternalMiner, Some(7))
                .unwrap(),
            7
        );
        assert!(matches!(
            select_process_worker_threads(12, ProcessCpuBudgetMode::InternalMiner, Some(13)),
            Err(ProcessCpuBudgetError::InvalidThreadCount { .. })
        ));
    }

    #[test]
    fn explicit_worker_limit_is_shared_by_every_enabled_phase() {
        assert_eq!(
            plan_process_cpu_budget_with_threads(12, 8, ProcessCpuBudgetMode::InternalMiner)
                .unwrap(),
            ProcessCpuBudgetPlan {
                available_threads: 12,
                shared_pool_threads: 8,
                pow_phase_threads: 8,
                history_step_phase_threads: 8,
                inbound_verifier_threads: 8,
            }
        );
        assert!(matches!(
            plan_process_cpu_budget_with_threads(12, 0, ProcessCpuBudgetMode::InternalMiner),
            Err(ProcessCpuBudgetError::InvalidThreadCount { .. })
        ));
        assert!(matches!(
            plan_process_cpu_budget_with_threads(12, 13, ProcessCpuBudgetMode::InternalMiner),
            Err(ProcessCpuBudgetError::InvalidThreadCount { .. })
        ));
    }

    #[test]
    fn every_cpu_phase_uses_one_protocol_safe_worker_pool() {
        let plan = plan_process_cpu_budget(12, ProcessCpuBudgetMode::InternalMiner).unwrap();
        let budget = ProcessCpuBudget::build(plan).unwrap();

        let pow_handle = budget.phase_pool();
        let history_handle = budget.phase_pool();
        let inbound_handle = budget.phase_pool();
        let wallet_handle = budget.phase_pool();
        let wallet_verify_handle = budget.phase_pool();
        assert!(Arc::ptr_eq(&pow_handle, &history_handle));
        assert!(Arc::ptr_eq(&pow_handle, &inbound_handle));
        assert!(Arc::ptr_eq(&pow_handle, &wallet_handle));
        assert!(Arc::ptr_eq(&pow_handle, &wallet_verify_handle));

        assert_eq!(
            budget.install_phase(ProcessCpuPhase::Pow, rayon::current_num_threads),
            10
        );
        assert_eq!(
            budget.install_phase(ProcessCpuPhase::HistoryStep, rayon::current_num_threads),
            10
        );
        assert_eq!(
            budget.install_phase(ProcessCpuPhase::InboundVerify, rayon::current_num_threads),
            10
        );
        assert_eq!(
            budget.install_phase(ProcessCpuPhase::WalletProof, rayon::current_num_threads),
            10
        );
        assert_eq!(
            budget.install_phase(ProcessCpuPhase::WalletVerify, rayon::current_num_threads),
            10
        );
    }

    #[test]
    fn wallet_proof_preempts_pow_and_beats_an_already_queued_phase() {
        use std::sync::mpsc;
        use std::time::Duration;

        let plan = plan_process_cpu_budget_with_threads(2, 2, ProcessCpuBudgetMode::InternalMiner)
            .unwrap();
        let budget = Arc::new(ProcessCpuBudget::build(plan).unwrap());
        let events = Arc::new(Mutex::new(Vec::new()));
        let (pow_started_tx, pow_started_rx) = mpsc::sync_channel(1);

        let pow_budget = Arc::clone(&budget);
        let pow_priority = Arc::clone(&budget);
        let pow_events = Arc::clone(&events);
        let pow = std::thread::spawn(move || {
            pow_budget.install_phase(ProcessCpuPhase::Pow, move || {
                pow_events.lock().unwrap().push("pow-start");
                pow_started_tx.send(()).unwrap();
                while !pow_priority.pow_preemption_requested() {
                    std::thread::yield_now();
                }
                pow_events.lock().unwrap().push("pow-stop");
            });
        });
        pow_started_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("PoW phase did not start");

        // Queue ordinary work first. The later wallet request must still win
        // admission after it asks the active PoW phase to drain.
        let history_budget = Arc::clone(&budget);
        let history_events = Arc::clone(&events);
        let history = std::thread::spawn(move || {
            history_budget.install_phase(ProcessCpuPhase::HistoryStep, move || {
                history_events.lock().unwrap().push("history");
            });
        });

        let wallet_budget = Arc::clone(&budget);
        let wallet_events = Arc::clone(&events);
        let wallet = std::thread::spawn(move || {
            wallet_budget.install_phase(ProcessCpuPhase::WalletProof, move || {
                wallet_events.lock().unwrap().push("wallet");
            });
        });

        pow.join().unwrap();
        wallet.join().unwrap();
        history.join().unwrap();
        assert_eq!(
            *events.lock().unwrap(),
            ["pow-start", "pow-stop", "wallet", "history"]
        );
    }

    #[test]
    fn inbound_verification_remains_work_conserving_during_pow() {
        use std::sync::atomic::AtomicBool;
        use std::sync::mpsc;
        use std::time::Duration;

        let plan = plan_process_cpu_budget_with_threads(2, 2, ProcessCpuBudgetMode::InternalMiner)
            .unwrap();
        let budget = Arc::new(ProcessCpuBudget::build(plan).unwrap());
        let events = Arc::new(Mutex::new(Vec::new()));
        let (pow_started_tx, pow_started_rx) = mpsc::sync_channel(1);
        let (verify_finished_tx, verify_finished_rx) = mpsc::sync_channel(1);
        let release_pow = Arc::new(AtomicBool::new(false));

        let pow_budget = Arc::clone(&budget);
        let pow_release = Arc::clone(&release_pow);
        let pow_events = Arc::clone(&events);
        let pow = std::thread::spawn(move || {
            pow_budget.install_phase(ProcessCpuPhase::Pow, move || {
                pow_events.lock().unwrap().push("pow-start");
                pow_started_tx.send(()).unwrap();
                while !pow_release.load(Ordering::Acquire) {
                    std::thread::yield_now();
                }
                pow_events.lock().unwrap().push("pow-stop");
            });
        });
        pow_started_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("PoW phase did not start");

        let verify_budget = Arc::clone(&budget);
        let verify_events = Arc::clone(&events);
        let verify = std::thread::spawn(move || {
            verify_budget.install_phase(ProcessCpuPhase::InboundVerify, move || {
                verify_events.lock().unwrap().push("verify");
                verify_finished_tx.send(()).unwrap();
            });
        });

        verify_finished_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("inbound verifier waited for background PoW to stop");
        assert!(
            !pow.is_finished(),
            "network verification must not cancel background PoW"
        );
        release_pow.store(true, Ordering::Release);
        verify.join().unwrap();
        pow.join().unwrap();
        assert_eq!(*events.lock().unwrap(), ["pow-start", "verify", "pow-stop"]);
    }

    #[test]
    fn one_cpu_internal_miner_still_has_an_all_core_pow_phase() {
        let plan = plan_process_cpu_budget(1, ProcessCpuBudgetMode::InternalMiner).unwrap();
        assert_eq!(plan.shared_pool_threads, 1);
        assert_eq!(plan.pow_phase_threads, 1);
        assert_eq!(plan.history_step_phase_threads, 1);
    }
}
