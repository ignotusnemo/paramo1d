use anyhow::{ensure, Result};
use std::{
    cell::RefCell,
    future::{pending, Future},
    io,
    sync::{
        atomic::{AtomicU8, Ordering},
        Mutex, OnceLock,
    },
};
use tokio_util::sync::CancellationToken;

static ACTIVE: OnceLock<Mutex<CancellationToken>> = OnceLock::new();
static PHASE: AtomicU8 = AtomicU8::new(0);
thread_local! { static OPERATION: RefCell<Option<CancellationToken>> = const { RefCell::new(None) }; }
pub fn set_active(active: bool) {
    let mut token = ACTIVE
        .get_or_init(|| Mutex::new(CancellationToken::new()))
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    if active {
        if token.is_cancelled() {
            *token = CancellationToken::new();
            crate::artifacts::matrix_cache_budget(crate::artifacts::FOREGROUND_MATRIX_CACHE);
        }
        if PHASE.load(Ordering::Relaxed) == 0 {
            PHASE.store(1, Ordering::Relaxed);
        }
    } else {
        token.cancel();
        crate::artifacts::matrix_cache_budget(crate::artifacts::BACKGROUND_MATRIX_CACHE);
        PHASE.store(0, Ordering::Relaxed);
    }
}
pub fn phase() -> &'static str {
    match PHASE.load(Ordering::Relaxed) {
        1 => "starting",
        2 => "following",
        3 => "verifying",
        _ => "paused",
    }
}
pub fn verifying() {
    if !token().is_some_and(|t| t.is_cancelled()) {
        PHASE.store(3, Ordering::Relaxed);
    }
}
pub fn token() -> Option<CancellationToken> {
    OPERATION.with(|slot| slot.borrow().clone())
}
pub fn check() -> Result<()> {
    ensure!(
        !token().is_some_and(|t| t.is_cancelled()),
        "Wallet check paused"
    );
    Ok(())
}
pub fn check_io() -> io::Result<()> {
    if token().is_some_and(|t| t.is_cancelled()) {
        Err(io::Error::new(
            io::ErrorKind::ConnectionAborted,
            "Wallet check paused",
        ))
    } else {
        Ok(())
    }
}
struct Scope(Option<CancellationToken>);
impl Drop for Scope {
    fn drop(&mut self) {
        OPERATION.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}
fn scoped<T>(token: CancellationToken, work: impl FnOnce() -> Result<T>) -> Result<T> {
    let _scope = Scope(OPERATION.with(|slot| slot.replace(Some(token))));
    check()?;
    work()
}
pub fn run<T>(work: impl FnOnce() -> Result<T>) -> Result<T> {
    let token = ACTIVE
        .get_or_init(|| Mutex::new(CancellationToken::new()))
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone();
    let result = scoped(token.clone(), || {
        let result = work();
        check()?;
        result
    });
    if !token.is_cancelled() {
        PHASE.store(2, Ordering::Relaxed);
    }
    result
}
pub async fn cancellable<T>(future: impl Future<Output = Result<T>>) -> Result<T> {
    let token = token();
    tokio::select! {
        biased;
        _ = async { match token { Some(t) => t.cancelled().await, None => pending::<()>().await } } => Err(anyhow::anyhow!("Wallet check paused")),
        result = future => result,
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn a_new_session_cannot_uncancel_inflight_work() {
        let old = CancellationToken::new();
        scoped(old.clone(), || {
            assert!(check().is_ok());
            old.cancel();
            assert_eq!(
                check_io().unwrap_err().kind(),
                io::ErrorKind::ConnectionAborted
            );
            scoped(CancellationToken::new(), || {
                check()?;
                Ok(())
            })?;
            assert!(check().is_err());
            Ok(())
        })
        .unwrap();
        assert!(token().is_none());
    }
    #[test]
    fn a_cancelled_matrix_read_returns_without_retrying() {
        use std::io::{Read, Write};
        let t = CancellationToken::new();
        let mut file = tempfile::tempfile().unwrap();
        file.write_all(&[1, 2, 3, 4]).unwrap();
        let mut reader = crate::matrix_store::MatrixReader::Plain(file);
        scoped(t.clone(), || {
            t.cancel();
            assert_eq!(
                reader.read_exact(&mut [0; 4]).unwrap_err().kind(),
                io::ErrorKind::ConnectionAborted
            );
            Ok(())
        })
        .unwrap();
    }
    #[test]
    fn a_waiting_network_operation_stops_on_pause() {
        let t = CancellationToken::new();
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        scoped(t.clone(), || {
            t.cancel();
            assert!(rt.block_on(cancellable(pending::<Result<()>>())).is_err());
            Ok(())
        })
        .unwrap();
    }
}
