pub mod api;
pub mod artifacts;
pub mod collector;
pub mod headers;
pub mod matrix_store;
pub mod rpc;
pub mod verify;

pub use artifacts::MatrixMode;
pub use verify::{verify_bundle, VerifiedState, Verifier};

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
