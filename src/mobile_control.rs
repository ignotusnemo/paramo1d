use anyhow::{ensure, Result};
use std::{
    cell::RefCell,
    future::{pending, Future},
    io,
    sync::{
        atomic::{AtomicBool, AtomicU8, Ordering},
        Mutex, OnceLock,
    },
    time::Instant,
};
use tokio_util::sync::CancellationToken;

static ACTIVE: OnceLock<Mutex<CancellationToken>> = OnceLock::new();
static PHASE: AtomicU8 = AtomicU8::new(0);
static RENEWING_AUTHORIZATION: AtomicBool = AtomicBool::new(false);
static NETWORK_WAIT: Mutex<Option<(usize, Instant)>> = Mutex::new(None);

pub(crate) struct NetworkWait {
    stage: &'static str,
    began: Instant,
}
pub(crate) fn waiting_for_network(stage: &'static str) -> NetworkWait {
    let mut current = NETWORK_WAIT.lock().unwrap_or_else(|e| e.into_inner());
    match current.as_mut() {
        Some((count, _)) => *count += 1,
        None => *current = Some((1, Instant::now())),
    }
    network_log(&format!("{stage} started"));
    NetworkWait {
        stage,
        began: Instant::now(),
    }
}
impl Drop for NetworkWait {
    fn drop(&mut self) {
        let mut current = NETWORK_WAIT.lock().unwrap_or_else(|e| e.into_inner());
        if let Some((count, _)) = current.as_mut() {
            *count -= 1;
            if *count == 0 {
                *current = None;
            }
        }
        network_log(&format!(
            "{} finished in {} ms",
            self.stage,
            self.began.elapsed().as_millis()
        ));
    }
}
pub(crate) fn network_progress() {
    if let Some((_, progress)) = NETWORK_WAIT
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .as_mut()
    {
        *progress = Instant::now();
    }
}
pub(crate) fn network_wait_ms() -> Option<u64> {
    NETWORK_WAIT
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .as_ref()
        .map(|(_, progress)| progress.elapsed().as_millis().min(u128::from(u64::MAX)) as u64)
}
fn network_log(message: &str) {
    #[cfg(target_os = "android")]
    {
        #[link(name = "log")]
        extern "C" {
            fn __android_log_write(
                priority: i32,
                tag: *const std::ffi::c_char,
                text: *const std::ffi::c_char,
            ) -> i32;
        }
        if let Ok(text) = std::ffi::CString::new(message) {
            unsafe {
                __android_log_write(4, c"Paramo1dNetwork".as_ptr(), text.as_ptr());
            }
        }
    }
    #[cfg(not(target_os = "android"))]
    let _ = message;
}
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
        4 => "finding_coins",
        _ => "paused",
    }
}
pub(crate) fn finding_coins() {
    PHASE.store(4, Ordering::Relaxed);
}
pub fn verifying() {
    if !token().is_some_and(|t| t.is_cancelled()) {
        PHASE.store(3, Ordering::Relaxed);
    }
}
pub(crate) struct AuthorizationRenewal;
impl Drop for AuthorizationRenewal {
    fn drop(&mut self) {
        RENEWING_AUTHORIZATION.store(false, Ordering::Relaxed);
    }
}
pub(crate) fn renew_authorization() -> AuthorizationRenewal {
    RENEWING_AUTHORIZATION.store(true, Ordering::Relaxed);
    AuthorizationRenewal
}
pub(crate) fn renewing_authorization() -> bool {
    RENEWING_AUTHORIZATION.load(Ordering::Relaxed)
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
    static WAIT_TESTS: Mutex<()> = Mutex::new(());
    #[test]
    fn authorization_renewal_clears_on_failure() {
        let result: Result<()> = (|| {
            let _renewal = renew_authorization();
            assert!(renewing_authorization());
            anyhow::bail!("Interrupted renewal")
        })();
        assert!(result.is_err());
        assert!(!renewing_authorization());
    }
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
        let _serial = WAIT_TESTS.lock().unwrap();
        let t = CancellationToken::new();
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        scoped(t.clone(), || {
            assert!(rt
                .block_on(cancellable(async {
                    let _waiting = waiting_for_network("test-cancel");
                    assert!(network_wait_ms().is_some());
                    t.cancel();
                    pending::<Result<()>>().await
                }))
                .is_err());
            assert!(network_wait_ms().is_none());
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn rpc_cancels_header_and_body_waits_and_accepts_a_new_session() {
        let _serial = WAIT_TESTS.lock().unwrap();
        use std::io::{Read, Write};
        use std::net::{TcpListener, TcpStream};
        use std::time::Duration;

        fn request(stream: &mut TcpStream) -> serde_json::Value {
            stream
                .set_read_timeout(Some(Duration::from_secs(2)))
                .unwrap();
            let mut header = Vec::new();
            while !header.ends_with(b"\r\n\r\n") {
                assert!(header.len() < 16384);
                let mut byte = [0];
                stream.read_exact(&mut byte).unwrap();
                header.push(byte[0]);
            }
            let length = std::str::from_utf8(&header)
                .unwrap()
                .lines()
                .find_map(|line| {
                    line.split_once(':')
                        .filter(|(name, _)| name.eq_ignore_ascii_case("content-length"))
                        .map(|(_, value)| value.trim().parse::<usize>().unwrap())
                })
                .unwrap();
            assert!(length < 16384);
            let mut body = vec![0; length];
            stream.read_exact(&mut body).unwrap();
            serde_json::from_slice(&body).unwrap()
        }
        fn accept(listener: &TcpListener) -> TcpStream {
            let deadline = Instant::now() + Duration::from_secs(3);
            loop {
                match listener.accept() {
                    Ok((stream, _)) => return stream,
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                        assert!(Instant::now() < deadline, "RPC test connection deadline");
                        std::thread::sleep(Duration::from_millis(5));
                    }
                    Err(error) => panic!("{error}"),
                }
            }
        }
        for partial_body in [false, true] {
            let listener = TcpListener::bind("127.0.0.1:0").unwrap();
            listener.set_nonblocking(true).unwrap();
            let endpoint = format!("http://{}", listener.local_addr().unwrap());
            let cancelled = CancellationToken::new();
            let stop = cancelled.clone();
            let server = std::thread::spawn(move || {
                let mut first = accept(&listener);
                assert_eq!(request(&mut first)["method"], "paranoid_getChainInfo");
                if partial_body {
                    first.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 1000\r\nConnection: close\r\n\r\n{").unwrap();
                }
                std::thread::sleep(Duration::from_millis(100));
                stop.cancel();
                drop(first);
                let mut next = accept(&listener);
                let query = request(&mut next);
                let body = serde_json::to_vec(
                    &serde_json::json!({"jsonrpc":"2.0","id":query["id"],"result":{"height":42}}),
                )
                .unwrap();
                write!(
                    next,
                    "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                    body.len()
                )
                .unwrap();
                next.write_all(&body).unwrap();
            });
            let mut rpc = crate::rpc::Rpc::new(&endpoint).unwrap();
            let began = Instant::now();
            let result = scoped(cancelled, || {
                rpc.call("getChainInfo", serde_json::json!([]))
            });
            assert_eq!(result.unwrap_err().to_string(), "Wallet check paused");
            assert!(
                began.elapsed() < Duration::from_secs(2),
                "Cancellation must precede the 30-second HTTP deadline"
            );
            assert!(network_wait_ms().is_none());
            let result = scoped(CancellationToken::new(), || {
                rpc.call("getChainInfo", serde_json::json!([]))
            })
            .unwrap();
            assert_eq!(result["height"], 42);
            server.join().unwrap();
        }
    }
}
