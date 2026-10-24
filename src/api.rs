use crate::{verify_bundle, MatrixMode, Verifier};
use serde::Deserialize;
use serde_json::{json, Value};
use std::{
    ffi::{c_char, CString},
    path::PathBuf,
    sync::Mutex,
};

const MAX_CONFIG_BYTES: usize = 8192;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    artifacts: PathBuf,
    bundle: PathBuf,
    #[serde(default)]
    threads: Option<usize>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct OpenRequest {
    artifacts: PathBuf,
    #[serde(default)]
    threads: Option<usize>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BundleRequest {
    bundle: PathBuf,
}

pub struct NativeSession {
    verifier: Mutex<Verifier>,
    pool: rayon::ThreadPool,
}

impl NativeSession {
    fn open(bytes: &[u8]) -> anyhow::Result<Self> {
        anyhow::ensure!(
            bytes.len() <= MAX_CONFIG_BYTES,
            "session configuration byte limit"
        );
        let request: OpenRequest = serde_json::from_slice(bytes)?;
        let threads = crate::resolve_workers(request.threads)?;
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()?;
        let verifier =
            pool.install(|| Verifier::open(&request.artifacts, MatrixMode::Streaming))?;
        Ok(Self {
            verifier: Mutex::new(verifier),
            pool,
        })
    }

    fn verify(&self, bytes: &[u8]) -> anyhow::Result<crate::VerifiedState> {
        anyhow::ensure!(
            bytes.len() <= MAX_CONFIG_BYTES,
            "bundle configuration byte limit"
        );
        let request: BundleRequest = serde_json::from_slice(bytes)?;
        let mut guard = self
            .verifier
            .lock()
            .map_err(|_| anyhow::anyhow!("session worker lock"))?;
        let verifier = &mut *guard;
        self.pool
            .install(|| verifier.verify_bundle(&request.bundle))
    }
}

fn verified_output(result: anyhow::Result<crate::VerifiedState>) -> Value {
    match result {
        Ok(state) => json!({"ok":true, "verified":state}),
        Err(error) => json!({"ok":false, "error":format!("{error:#}")}),
    }
}

pub fn verify_json(bytes: &[u8]) -> Value {
    let result = (|| -> anyhow::Result<_> {
        anyhow::ensure!(
            bytes.len() <= MAX_CONFIG_BYTES,
            "verification configuration byte limit"
        );
        let request: Request = serde_json::from_slice(bytes)?;
        let threads = crate::resolve_workers(request.threads)?;
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()?;
        pool.install(|| verify_bundle(&request.artifacts, &request.bundle, MatrixMode::Streaming))
    })();
    verified_output(result)
}

fn output(value: Value) -> *mut c_char {
    CString::new(value.to_string())
        .expect("JSON encodes NUL bytes")
        .into_raw()
}

/// Verify an owned bundle using a bounded JSON configuration.
///
/// # Safety
/// `data` must point to `length` readable bytes for the duration of this call.
/// Release the returned UTF-8 JSON using `paramo1d_free_json`.
#[no_mangle]
pub unsafe extern "C" fn paramo1d_verify_json(data: *const u8, length: usize) -> *mut c_char {
    if data.is_null() || length > MAX_CONFIG_BYTES {
        return output(json!({"ok":false, "error":"invalid verification configuration buffer"}));
    }
    let bytes = unsafe { std::slice::from_raw_parts(data, length) };
    let result = std::panic::catch_unwind(|| verify_json(bytes));
    output(result.unwrap_or_else(|_| json!({"ok":false, "error":"verification worker failed"})))
}

#[no_mangle]
pub extern "C" fn paramo1d_profile_json() -> *mut c_char {
    output(
        serde_json::to_value(crate::artifacts::profile()).expect("compiled profile serialization"),
    )
}

/// Create a verification session that retains authenticated runtime data.
///
/// # Safety
/// `data` must point to `length` readable bytes. If `error` is non-null, it
/// must point to a writable string pointer. On failure that pointer receives
/// owned JSON to release with `paramo1d_free_json`. Success writes null.
#[no_mangle]
pub unsafe extern "C" fn paramo1d_session_new_json(
    data: *const u8,
    length: usize,
    error: *mut *mut c_char,
) -> *mut NativeSession {
    if !error.is_null() {
        unsafe {
            *error = std::ptr::null_mut();
        }
    }
    let result = std::panic::catch_unwind(|| -> anyhow::Result<_> {
        anyhow::ensure!(
            !data.is_null() && length <= MAX_CONFIG_BYTES,
            "invalid session configuration buffer"
        );
        let bytes = unsafe { std::slice::from_raw_parts(data, length) };
        NativeSession::open(bytes)
    })
    .unwrap_or_else(|_| Err(anyhow::anyhow!("session creation failed")));
    match result {
        Ok(session) => Box::into_raw(Box::new(session)),
        Err(reason) => {
            if !error.is_null() {
                unsafe {
                    *error = output(json!({"ok":false,"error":format!("{reason:#}")}));
                }
            }
            std::ptr::null_mut()
        }
    }
}

/// Verify one bundle while retaining the session's authenticated caches.
///
/// # Safety
/// `session` must be a live pointer returned by `paramo1d_session_new_json`.
/// `data` must point to `length` readable bytes. Concurrent calls are
/// serialized. Release the returned JSON with `paramo1d_free_json`.
#[no_mangle]
pub unsafe extern "C" fn paramo1d_session_verify_json(
    session: *mut NativeSession,
    data: *const u8,
    length: usize,
) -> *mut c_char {
    if session.is_null() || data.is_null() || length > MAX_CONFIG_BYTES {
        return output(json!({"ok":false,"error":"invalid session verification buffer"}));
    }
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let session = unsafe { &*session };
        let bytes = unsafe { std::slice::from_raw_parts(data, length) };
        verified_output(session.verify(bytes))
    }));
    output(result.unwrap_or_else(|_| json!({"ok":false,"error":"session verification failed"})))
}

/// Release an owned verification session.
///
/// # Safety
/// `session` must be null or an unreleased pointer from this library.
/// Finish all verification calls before releasing the session.
#[no_mangle]
pub unsafe extern "C" fn paramo1d_session_free(session: *mut NativeSession) {
    if !session.is_null() {
        drop(unsafe { Box::from_raw(session) });
    }
}

/// Release a string returned by this library.
///
/// # Safety
/// `value` must be null or an unreleased pointer returned by this library.
#[no_mangle]
pub unsafe extern "C" fn paramo1d_free_json(value: *mut c_char) {
    if !value.is_null() {
        drop(unsafe { CString::from_raw(value) });
    }
}
