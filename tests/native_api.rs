use paramo1d::api::{
    paramo1d_free_json, paramo1d_profile_json, paramo1d_session_free, paramo1d_session_new_json,
    paramo1d_session_verify_json, paramo1d_verify_json, verify_json,
};
use std::ffi::CStr;

#[test]
fn native_configuration_enforces_shape_and_worker_bounds() {
    for bytes in [
        b"{".as_slice(),
        br#"{"artifacts":"/unused","bundle":"/unused","threads":0}"#,
        br#"{"artifacts":"/unused","bundle":"/unused","threads":65535}"#,
        br#"{"artifacts":"/unused","bundle":"/unused","remote_trust":true}"#,
    ] {
        let result = verify_json(bytes);
        assert_eq!(result["ok"], false);
        assert!(result["error"].as_str().is_some());
    }
    assert_eq!(verify_json(&[b' '; 8193])["ok"], false);
}

#[test]
fn default_workers_match_available_hardware() {
    let available = paramo1d::available_workers();
    assert!(available >= 1);
    assert_eq!(paramo1d::resolve_workers(None).unwrap(), available);
    assert_eq!(
        paramo1d::resolve_workers(Some(available)).unwrap(),
        available
    );
    assert!(paramo1d::resolve_workers(Some(0)).is_err());
    assert!(paramo1d::resolve_workers(Some(available + 1)).is_err());
}

#[test]
fn native_sessions_return_owned_errors_for_invalid_creation_and_calls() {
    unsafe {
        let mut error = std::ptr::null_mut();
        let session = paramo1d_session_new_json(std::ptr::null(), 0, &mut error);
        assert!(session.is_null());
        assert!(!error.is_null());
        let value: serde_json::Value =
            serde_json::from_slice(CStr::from_ptr(error).to_bytes()).unwrap();
        assert_eq!(value["ok"], false);
        paramo1d_free_json(error);
        assert!(
            paramo1d_session_new_json(std::ptr::dangling(), 8193, std::ptr::null_mut()).is_null()
        );
        let result = paramo1d_session_verify_json(std::ptr::null_mut(), std::ptr::null(), 0);
        let value: serde_json::Value =
            serde_json::from_slice(CStr::from_ptr(result).to_bytes()).unwrap();
        assert_eq!(value["ok"], false);
        paramo1d_free_json(result);
        paramo1d_session_free(std::ptr::null_mut());
    }
}

#[test]
fn native_boundary_checks_buffers_before_reading_and_owns_results() {
    unsafe {
        for (pointer, length) in [(std::ptr::null(), 0), (std::ptr::dangling::<u8>(), 8193)] {
            let result = paramo1d_verify_json(pointer, length);
            let value: serde_json::Value =
                serde_json::from_slice(CStr::from_ptr(result).to_bytes()).unwrap();
            assert_eq!(value["ok"], false);
            paramo1d_free_json(result);
        }
        let result = paramo1d_profile_json();
        let value: serde_json::Value =
            serde_json::from_slice(CStr::from_ptr(result).to_bytes()).unwrap();
        assert_eq!(
            value["upstream_commit"],
            paramo1d::artifacts::profile().upstream_commit
        );
        paramo1d_free_json(result);
        paramo1d_free_json(std::ptr::null_mut());
    }
}
