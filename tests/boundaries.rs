use noid_chain::consensus::genesis::genesis_header;
use paramo1d::{artifacts::read_bounded, headers::CheckedHeaders, rpc::Rpc};
use std::{fs, io::Write};

#[test]
fn verified_headers_keep_an_owned_immutable_copy() {
    let mut file = tempfile::NamedTempFile::new().unwrap();
    file.write_all(&genesis_header().to_bytes()).unwrap();
    let verified = CheckedHeaders::verify(file.path()).unwrap();
    fs::write(file.path(), [0; 212]).unwrap();
    assert_eq!(verified.at(0).unwrap(), genesis_header());
    assert_eq!(verified.summary().height, 0);
}

#[test]
fn malformed_foreign_and_missing_headers_reject() {
    let file = tempfile::NamedTempFile::new().unwrap();
    assert!(CheckedHeaders::verify(file.path()).is_err());
    fs::write(file.path(), [0; 211]).unwrap();
    assert!(CheckedHeaders::verify(file.path()).is_err());
    let mut foreign = genesis_header();
    foreign.state_root[0] ^= 1;
    fs::write(file.path(), foreign.to_bytes()).unwrap();
    assert!(CheckedHeaders::verify(file.path()).is_err());
    fs::write(file.path(), genesis_header().to_bytes()).unwrap();
    let verified = CheckedHeaders::verify(file.path()).unwrap();
    assert!(verified.at(1).is_err());
    assert!(verified.at(u64::MAX).is_err());
}

#[test]
fn file_byte_limits_are_enforced_before_decoding() {
    let file = tempfile::NamedTempFile::new().unwrap();
    fs::write(file.path(), [0; 33]).unwrap();
    assert!(read_bounded(file.path(), 32).is_err());
    assert_eq!(read_bounded(file.path(), 33).unwrap().len(), 33);
}

#[test]
fn rpc_transport_limits_plain_http_to_loopback() {
    for url in [
        "http://127.0.0.1:9601",
        "http://[::1]:9601",
        "https://example.com/rpc",
    ] {
        assert!(Rpc::new(url).is_ok(), "{url}");
    }
    for url in [
        "http://example.com",
        "http://127.0.0.1.evil.example",
        "https://user:password@example.com",
        "file:///tmp/socket",
        "https://example.com/#fragment",
    ] {
        assert!(Rpc::new(url).is_err(), "{url}");
    }
}
