pub mod api;
pub mod artifacts;
pub mod collector;
pub mod courier_api;
pub mod headers;
pub mod matrix_store;
pub mod mobile;
mod mobile_control;
mod mobile_wallet;
mod network_route;
pub mod rpc;
mod verifier_session;
pub mod verify;
mod wallet_checkpoint;

pub use artifacts::MatrixMode;
pub use verify::{verify_bundle, VerifiedState, Verifier};

pub fn ensure_verification_hardware() -> anyhow::Result<()> {
    #[cfg(all(target_os = "android", target_arch = "aarch64"))]
    {
        // Read the OS capabilities even when target-feature makes Rust's
        // feature-detection macros assume the static compilation contract.
        unsafe extern "C" {
            fn getauxval(kind: usize) -> usize;
        }
        const REQUIRED: usize = (1 << 1) | (1 << 3) | (1 << 4);
        let capabilities = unsafe { getauxval(16) };
        anyhow::ensure!(
            capabilities & REQUIRED == REQUIRED,
            "This device needs ARM NEON, AES and PMULL for Paramo1d verification"
        );
    }
    noid_core::cpu::ensure_production_hardware()?;
    Ok(())
}

pub fn available_workers() -> usize {
    std::thread::available_parallelism().map_or(1, usize::from)
}

pub fn resolve_workers(requested: Option<usize>) -> anyhow::Result<usize> {
    let available = available_workers();
    let workers = requested.unwrap_or(available);
    anyhow::ensure!(
        workers > 0 && workers <= available,
        "verification worker count must be 1 through {available}"
    );
    Ok(workers)
}
