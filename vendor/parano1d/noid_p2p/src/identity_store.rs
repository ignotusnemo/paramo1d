// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Durable libp2p node identity.
//!
//! A PeerId is a network identity, not a per-process session identifier.
//! Rotating it on every restart invalidates cached `/p2p/<peer-id>` addresses,
//! Kademlia routing entries, relay reservations, and peer reputation.  This
//! module creates one Ed25519 key on first start and then loads it fail-closed.

use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::path::Path;

use anyhow::{bail, Context, Result};
use libp2p::identity::{KeyType, Keypair};

const IDENTITY_FILE: &str = "p2p_identity.key";
const IDENTITY_MAGIC: &[u8; 16] = b"NOID-P2P-KEY-v1!";
const MAX_IDENTITY_BYTES: usize = 512;

pub(crate) fn load_or_create(data_dir: &Path) -> Result<Keypair> {
    std::fs::create_dir_all(data_dir)
        .with_context(|| format!("create P2P identity directory {}", data_dir.display()))?;
    let path = data_dir.join(IDENTITY_FILE);
    match load(&path) {
        Ok(keypair) => Ok(keypair),
        Err(error)
            if error
                .downcast_ref::<std::io::Error>()
                .is_some_and(|io| io.kind() == std::io::ErrorKind::NotFound) =>
        {
            create(&path)
        }
        Err(error) => Err(error),
    }
}

fn create(path: &Path) -> Result<Keypair> {
    let keypair = Keypair::generate_ed25519();
    let mut encoded = keypair
        .to_protobuf_encoding()
        .context("encode generated Ed25519 P2P identity")?;
    if encoded.len() > MAX_IDENTITY_BYTES - IDENTITY_MAGIC.len() {
        encoded.fill(0);
        bail!("generated P2P identity exceeds the bounded file format");
    }

    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options
            .mode(0o600)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW);
    }
    let mut file = match options.open(path) {
        Ok(file) => file,
        // A concurrent creator won. Never overwrite or rotate its identity.
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            encoded.fill(0);
            return load(path);
        }
        Err(error) => {
            encoded.fill(0);
            return Err(error).with_context(|| format!("create P2P identity {}", path.display()));
        }
    };
    let write_result = (|| -> std::io::Result<()> {
        file.write_all(IDENTITY_MAGIC)?;
        file.write_all(&encoded)?;
        file.sync_all()
    })();
    encoded.fill(0);
    write_result.with_context(|| format!("persist P2P identity {}", path.display()))?;

    #[cfg(unix)]
    if let Some(parent) = path.parent() {
        File::open(parent)
            .and_then(|directory| directory.sync_all())
            .with_context(|| format!("sync P2P identity directory {}", parent.display()))?;
    }

    Ok(keypair)
}

fn load(path: &Path) -> Result<Keypair> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW);
    }
    let file = options
        .open(path)
        .with_context(|| format!("open P2P identity {}", path.display()))?;
    validate_metadata(path, &file)?;

    let mut bytes = Vec::with_capacity(MAX_IDENTITY_BYTES + 1);
    file.take((MAX_IDENTITY_BYTES + 1) as u64)
        .read_to_end(&mut bytes)
        .with_context(|| format!("read P2P identity {}", path.display()))?;
    if bytes.len() <= IDENTITY_MAGIC.len() || bytes.len() > MAX_IDENTITY_BYTES {
        bytes.fill(0);
        bail!(
            "P2P identity {} has an invalid bounded length",
            path.display()
        );
    }
    if &bytes[..IDENTITY_MAGIC.len()] != IDENTITY_MAGIC {
        bytes.fill(0);
        bail!(
            "P2P identity {} has an invalid format marker",
            path.display()
        );
    }

    let decoded = Keypair::from_protobuf_encoding(&bytes[IDENTITY_MAGIC.len()..]);
    bytes.fill(0);
    let keypair = decoded.with_context(|| format!("decode P2P identity {}", path.display()))?;
    if keypair.key_type() != KeyType::Ed25519 {
        bail!("P2P identity {} is not Ed25519", path.display());
    }
    Ok(keypair)
}

fn validate_metadata(path: &Path, file: &File) -> Result<()> {
    let metadata = file
        .metadata()
        .with_context(|| format!("stat P2P identity {}", path.display()))?;
    if !metadata.is_file() {
        bail!("P2P identity {} is not a regular file", path.display());
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        let mode = metadata.permissions().mode() & 0o777;
        if mode != 0o600 {
            bail!(
                "P2P identity {} has insecure permissions {:o}, expected 600",
                path.display(),
                mode
            );
        }
        let owner = metadata.uid();
        // SAFETY: geteuid has no preconditions and does not access pointers.
        let expected_owner = unsafe { libc::geteuid() };
        if owner != expected_owner {
            bail!(
                "P2P identity {} belongs to uid {}, expected {}",
                path.display(),
                owner,
                expected_owner
            );
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identity_is_created_owner_only_and_reused() {
        let directory = tempfile::tempdir().unwrap();
        let first = load_or_create(directory.path()).unwrap();
        let first_peer = first.public().to_peer_id();
        let second = load_or_create(directory.path()).unwrap();
        assert_eq!(second.public().to_peer_id(), first_peer);

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = std::fs::metadata(directory.path().join(IDENTITY_FILE))
                .unwrap()
                .permissions()
                .mode()
                & 0o777;
            assert_eq!(mode, 0o600);
        }
    }

    #[test]
    fn corrupt_identity_fails_instead_of_rotating_peer_id() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join(IDENTITY_FILE);
        std::fs::write(&path, b"corrupt").unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600)).unwrap();
        }
        assert!(load_or_create(directory.path()).is_err());
        assert_eq!(std::fs::read(path).unwrap(), b"corrupt");
    }

    #[cfg(unix)]
    #[test]
    fn public_permissions_and_symlinks_are_rejected() {
        use std::os::unix::fs::PermissionsExt;

        let directory = tempfile::tempdir().unwrap();
        let _ = load_or_create(directory.path()).unwrap();
        let path = directory.path().join(IDENTITY_FILE);
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o644)).unwrap();
        assert!(load_or_create(directory.path()).is_err());

        std::fs::remove_file(&path).unwrap();
        let target = directory.path().join("target.key");
        std::fs::write(&target, b"not-an-identity").unwrap();
        std::os::unix::fs::symlink(&target, &path).unwrap();
        assert!(load_or_create(directory.path()).is_err());
    }
}
