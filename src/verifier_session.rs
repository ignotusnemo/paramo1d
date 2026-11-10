//! Reuse verified material on the wallet worker while binding every cache hit to bytes.
use crate::{artifacts, MatrixMode, VerifiedState, Verifier};
use anyhow::{ensure, Context, Result};
use sha2::{Digest, Sha512};
use std::{
    cell::RefCell,
    fs::File,
    io::Read,
    ops::{Deref, DerefMut},
    path::{Path, PathBuf},
    time::Instant,
};

type Fingerprint = [u8; 64];
fn add_file(hash: &mut Sha512, path: &Path, cap: u64, optional: bool) -> Result<()> {
    let file = match File::open(path) {
        Ok(file) => file,
        Err(e) if optional && e.kind() == std::io::ErrorKind::NotFound => {
            hash.update([0]);
            return Ok(());
        }
        Err(e) => return Err(e).with_context(|| format!("open {}", path.display())),
    };
    let length = file.metadata()?.len();
    ensure!(length <= cap, "Verification input exceeds cache byte limit");
    hash.update([1]);
    hash.update(length.to_le_bytes());
    let mut reader = file.take(cap + 1);
    let mut buffer = [0u8; 65536];
    let mut seen = 0u64;
    loop {
        crate::mobile_control::check()?;
        let count = reader.read(&mut buffer)?;
        if count == 0 {
            break;
        };
        seen += count as u64;
        ensure!(seen <= cap, "Verification input grew beyond cache limit");
        hash.update(&buffer[..count]);
    }
    ensure!(seen == length, "Verification input changed while reading");
    Ok(())
}
fn bundle_fingerprint(directory: &Path) -> Result<Fingerprint> {
    let mut hash = Sha512::new();
    hash.update(b"Paramo1d/verified-boundary/1\0");
    for (name, cap, optional) in [
        ("headers.bin", 8 * 1024 * 1024 * 1024, false),
        ("terminal.bin", 1_100_000, false),
        ("origin.bin", artifacts::MAX_ORIGIN_BYTES, false),
        ("current-origin.bin", artifacts::MAX_ORIGIN_BYTES, true),
    ] {
        hash.update((name.len() as u64).to_le_bytes());
        hash.update(name.as_bytes());
        add_file(&mut hash, &directory.join(name), cap, optional)?;
    }
    Ok(hash.finalize().into())
}
struct Cached {
    path: PathBuf,
    digest: Fingerprint,
    state: VerifiedState,
}
pub(crate) struct Session {
    artifacts: PathBuf,
    verifier: Verifier,
    last: Option<Cached>,
}
impl Deref for Session {
    type Target = Verifier;
    fn deref(&self) -> &Verifier {
        &self.verifier
    }
}
impl DerefMut for Session {
    fn deref_mut(&mut self) -> &mut Verifier {
        &mut self.verifier
    }
}
impl Session {
    fn cached_bundle(&self, bundle: &Path) -> Result<Option<VerifiedState>> {
        let start = Instant::now();
        if let Some(cached) = &self.last {
            let path = bundle.canonicalize()?;
            if cached.path == path
                && self.verifier.cached_state_is_current(&cached.state)
                && cached.digest == bundle_fingerprint(&path)?
            {
                return Ok(Some(
                    cached.state.clone().reused(start.elapsed().as_millis()),
                ));
            }
        }
        Ok(None)
    }
    pub fn prepare_resume(&mut self, bundle: &Path) -> Result<(u64, Option<VerifiedState>)> {
        if let Some(state) = self.cached_bundle(bundle)? {
            return Ok((state.height(), Some(state)));
        }
        if let Some(headers) = self.verifier.prepare_resume_headers(bundle)? {
            self.last = None;
            return Ok((headers.height, None));
        }
        let state = self.verify_bundle(bundle)?;
        Ok((state.height(), Some(state)))
    }
    pub fn discard_resume_headers(&mut self) -> bool {
        let discarded = self.verifier.discard_resume_headers();
        if discarded {
            self.last = None;
        }
        discarded
    }
    pub fn verify_bundle(&mut self, bundle: &Path) -> Result<VerifiedState> {
        let start = Instant::now();
        let path = bundle.canonicalize()?;
        let digest = bundle_fingerprint(&path)?;
        if let Some(cached) = &self.last {
            if cached.path == path
                && self.verifier.cached_state_is_current(&cached.state)
                && cached.digest == digest
            {
                return Ok(cached.state.clone().reused(start.elapsed().as_millis()));
            }
        }
        // Runtime metadata was authenticated against the compiled release pins
        // when this session opened. MatrixSource authenticates every consumed
        // span against that runtime, including spans read after a file changes.
        let state = self.verifier.verify_bundle(&path)?;
        ensure!(
            bundle_fingerprint(&path)? == digest,
            "Verification bundle changed during verification"
        );
        self.last = Some(Cached {
            path,
            digest,
            state: state.clone(),
        });
        Ok(state)
    }
}
thread_local! {static SESSION:RefCell<Option<Session>>=const{RefCell::new(None)};}
pub(crate) fn with<T>(artifacts: &Path, work: impl FnOnce(&mut Session) -> Result<T>) -> Result<T> {
    let path = artifacts.canonicalize()?;
    SESSION.with(|slot| {
        let mut slot = slot
            .try_borrow_mut()
            .map_err(|_| anyhow::anyhow!("Verification is already in progress"))?;
        if !slot.as_ref().is_some_and(|s| s.artifacts == path) {
            *slot = None;
            *slot = Some(Session {
                verifier: Verifier::open(&path, MatrixMode::Streaming)?,
                artifacts: path,
                last: None,
            });
        }
        work(slot.as_mut().expect("initialized verification session"))
    })
}
pub(crate) fn verify(artifacts: &Path, bundle: &Path) -> Result<VerifiedState> {
    with(artifacts, |s| s.verify_bundle(bundle))
}
pub(crate) fn header(
    artifacts: &Path,
    bundle: &Path,
    height: u64,
) -> Result<noid_chain::BlockHeader> {
    with(artifacts, |s| {
        s.verify_bundle(bundle)?;
        s.checked_header(height)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cache_identity_changes_when_proof_inputs_change() {
        let dir = tempfile::tempdir().unwrap();
        for name in ["headers.bin", "terminal.bin", "origin.bin"] {
            std::fs::write(dir.path().join(name), [1, 2, 3]).unwrap();
        }
        let before = bundle_fingerprint(dir.path()).unwrap();
        std::fs::write(dir.path().join("terminal.bin"), [1, 2, 4]).unwrap();
        assert_ne!(before, bundle_fingerprint(dir.path()).unwrap());
        std::fs::write(dir.path().join("terminal.bin"), [1, 2, 3]).unwrap();
        assert_eq!(before, bundle_fingerprint(dir.path()).unwrap());
        std::fs::write(dir.path().join("current-origin.bin"), [1]).unwrap();
        assert_ne!(before, bundle_fingerprint(dir.path()).unwrap());
    }
    #[test]
    #[ignore = "requires a prepared public artifact directory and verified mainnet bundle"]
    fn a_modified_real_bundle_cannot_reuse_the_verified_result() {
        let artifacts = PathBuf::from(std::env::var("PARAMO1D_TEST_ARTIFACTS").unwrap());
        let source = PathBuf::from(std::env::var("PARAMO1D_TEST_BUNDLE").unwrap());
        let dir = tempfile::tempdir().unwrap();
        for item in std::fs::read_dir(source).unwrap() {
            let item = item.unwrap();
            if item.file_type().unwrap().is_file() {
                std::fs::copy(item.path(), dir.path().join(item.file_name())).unwrap();
            }
        }
        let first = verify(&artifacts, dir.path()).unwrap();
        let second = verify(&artifacts, dir.path()).unwrap();
        assert_eq!(first.height(), second.height());
        assert!(second.reused_verification());
        let path = dir.path().join("terminal.bin");
        let mut bytes = std::fs::read(&path).unwrap();
        bytes[0] ^= 1;
        std::fs::write(&path, bytes).unwrap();
        assert!(verify(&artifacts, dir.path()).is_err());
    }
    #[test]
    #[ignore = "requires two public mainnet bundles and prepared verification parameters"]
    fn a_fresh_proof_replaces_an_unusable_saved_terminal() {
        let artifacts = PathBuf::from(std::env::var("PARAMO1D_TEST_ARTIFACTS").unwrap());
        let old_source = PathBuf::from(std::env::var("PARAMO1D_TEST_PREVIOUS_BUNDLE").unwrap());
        let source = PathBuf::from(std::env::var("PARAMO1D_TEST_BUNDLE").unwrap());
        let reference: serde_json::Value = serde_json::from_slice(
            &std::fs::read(std::env::var("PARAMO1D_TEST_REFERENCE").unwrap()).unwrap(),
        )
        .unwrap();
        let directory = tempfile::tempdir().unwrap();
        let old = directory.path().join("old");
        let changed = directory.path().join("changed");
        for (input, output) in [(&old_source, &old), (&source, &changed)] {
            std::fs::create_dir(output).unwrap();
            for name in [
                "headers.bin",
                "terminal.bin",
                "origin.bin",
                "current-origin.bin",
            ] {
                if input.join(name).is_file() {
                    std::fs::copy(input.join(name), output.join(name)).unwrap();
                }
            }
            let path = output.join("terminal.bin");
            let mut bytes = std::fs::read(&path).unwrap();
            bytes[0] ^= 1;
            std::fs::write(path, bytes).unwrap();
        }
        let mut session = Session {
            artifacts: artifacts.canonicalize().unwrap(),
            verifier: Verifier::open(&artifacts, MatrixMode::Streaming).unwrap(),
            last: None,
        };
        let (old_height, state) = session.prepare_resume(&old).unwrap();
        assert!(state.is_none());
        assert!(session.verify_bundle(&old).is_err());
        assert!(session.verify_bundle(&changed).is_err());
        assert!(session.discard_resume_headers());
        assert!(!session.discard_resume_headers());
        assert!(session.prepare_resume(&old).unwrap().1.is_none());
        let fresh = session.verify_bundle(&source).unwrap();
        assert!(fresh.height() > old_height);
        assert_eq!(
            fresh.height(),
            reference["verified"]["height"].as_u64().unwrap()
        );
        assert_eq!(
            fresh.block_hash(),
            reference["verified"]["block_hash"].as_str().unwrap()
        );
        assert_eq!(
            fresh.state_root(),
            reference["verified"]["state_root"].as_str().unwrap()
        );
        assert!(!session.discard_resume_headers());
        let cached = session.prepare_resume(&source).unwrap().1.unwrap();
        assert!(cached.reused_verification());
    }
}
