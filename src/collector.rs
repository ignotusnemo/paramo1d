use crate::artifacts::{read_bounded, MAX_ORIGIN_BYTES};
use anyhow::{ensure, Context, Result};
use libmdbx::{Database, DatabaseOptions, Mode, NoWriteMap, ObjectLength};
use noid_chain::{
    block_header::{block_id, semantic_header_id},
    history_step::HistoryStepTerminalMetadata,
    storage::serial::{decode_chain_tip, decode_header, u64_key},
};
use noid_recursive::acceptance::history_step::v2::capacity_banked;
use serde_json::{json, Value};
use std::{
    fs::{self, File},
    io::Write,
    path::Path,
};

pub fn copy_origins(source: &Path, destination: &Path, height: u64) -> Result<usize> {
    let mut total = 0;
    let mut old = false;
    let mut current = false;
    for (count, entry) in fs::read_dir(source)?.enumerate() {
        ensure!(count < 32, "origin directory entry limit");
        let path = entry?.path();
        if path.extension().and_then(|s| s.to_str()) != Some("origin") {
            continue;
        }
        let bytes = read_bounded(&path, MAX_ORIGIN_BYTES)?;
        if bytes.starts_with(b"O1V2OR02") {
            ensure!(
                !old,
                "multiple retirement origins require a selected source directory"
            );
            total += bytes.len();
            fs::write(destination.join("origin.bin"), bytes)?;
            old = true;
        } else if bytes.starts_with(b"O1A4OR01")
            && noid_chain::consensus::params::v2_1_active(height)
        {
            ensure!(
                !current,
                "multiple current origins require a selected source directory"
            );
            total += bytes.len();
            fs::write(destination.join("current-origin.bin"), bytes)?;
            current = true;
        }
    }
    ensure!(old, "retirement origin required");
    ensure!(
        !noid_chain::consensus::params::v2_1_active(height) || current,
        "current origin required"
    );
    Ok(total)
}

pub fn export(node: &Path, output: &Path, selected_height: Option<u64>) -> Result<Value> {
    ensure!(!output.exists(), "output bundle already exists");
    let parent = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    fs::create_dir_all(parent)?;
    let temporary = tempfile::Builder::new()
        .prefix(".paramo1d-export-")
        .tempdir_in(parent)?;
    let database = Database::<NoWriteMap>::open_with_options(
        node,
        DatabaseOptions {
            mode: Mode::ReadOnly,
            max_tables: Some(64),
            no_rdahead: true,
            ..Default::default()
        },
    )?;
    let transaction = database.begin_ro_txn()?;
    let tip_table = transaction.open_table(Some("tip"))?;
    let tip: Vec<u8> = transaction
        .get(&tip_table, &[0u8])?
        .context("node has no canonical tip")?;
    let (tip_height, tip_hash) = decode_chain_tip(&tip).context("canonical tip encoding")?;
    let height = selected_height.unwrap_or(tip_height);
    ensure!(
        height <= tip_height && height < 40_000_000,
        "requested boundary height"
    );
    let table = transaction.open_table(Some("headers"))?;
    let mut last = None;
    let mut headers = File::create(temporary.path().join("headers.bin"))?;
    for at in 0..=height {
        let bytes: Vec<u8> = transaction
            .get(&table, &u64_key(at))?
            .context("missing canonical header")?;
        let header = decode_header(&bytes).context("stored header encoding")?;
        ensure!(header.height == at, "stored header height");
        headers.write_all(&header.to_bytes())?;
        last = Some(header);
    }
    headers.sync_all()?;
    drop(headers);
    let header = last.context("missing selected header")?;
    ensure!(
        height != tip_height || block_id(&header) == tip_hash,
        "canonical tip header identity"
    );
    let semantic = semantic_header_id(&header);
    let proofs = transaction.open_table(Some("history_step_proof_objects"))?;
    let mut terminal = None;
    for class in 0..3u8 {
        let mut key = [0; 41];
        key[..8].copy_from_slice(&height.to_be_bytes());
        key[8..40].copy_from_slice(&semantic);
        key[40] = class;
        if let Some(ObjectLength(length)) = transaction.get(&proofs, &key)? {
            ensure!((1..=1_100_000).contains(&length), "stored proof byte limit");
            let bytes: Vec<u8> = transaction
                .get(&proofs, &key)?
                .context("proof disappeared in read transaction")?;
            let metadata = HistoryStepTerminalMetadata::decode_prefix(&bytes)?;
            ensure!(
                metadata.terminal_height() == height
                    && metadata.terminal_hash() == semantic
                    && metadata.class_id() == class,
                "stored proof identity"
            );
            terminal = Some(bytes);
            break;
        }
    }
    if terminal.is_none() {
        let table = transaction.open_table(Some("history_step_terminals"))?;
        if let Some(ObjectLength(length)) = transaction.get(&table, &u64_key(height))? {
            ensure!(
                (1..=1_100_000).contains(&length),
                "stored terminal byte limit"
            );
            let bytes: Vec<u8> = transaction
                .get(&table, &u64_key(height))?
                .context("terminal disappeared in read transaction")?;
            let prefix = noid_chain::history_step::HISTORY_STEP_TERMINAL_BINDING_BYTES;
            let marker = bytes.len() == prefix + 44 && bytes[prefix..prefix + 4] == *b"RSM1";
            if !marker {
                terminal = Some(bytes);
            }
        }
    }
    if terminal.is_none() {
        for (count, entry) in fs::read_dir(node.join("fork-origins"))?.enumerate() {
            ensure!(count < 32, "origin lookup entry limit");
            let path = entry?.path();
            if path.extension().and_then(|s| s.to_str()) != Some("origin") {
                continue;
            }
            let bytes = read_bounded(&path, MAX_ORIGIN_BYTES)?;
            if bytes.starts_with(b"O1A4OR01") {
                let certificate =
                    capacity_banked::AuthorizationOriginCertificate::from_bytes(&bytes)
                        .map_err(|e| anyhow::anyhow!("origin codec: {e}"))?;
                if *certificate.parent_header() == header {
                    terminal = Some(certificate.terminal_bytes().to_vec());
                    break;
                }
            }
        }
    }
    let terminal = terminal.context("complete proof for the selected boundary is unavailable")?;
    let metadata = HistoryStepTerminalMetadata::decode_prefix(&terminal)?;
    ensure!(
        metadata.terminal_height() == height && metadata.terminal_hash() == semantic,
        "exported terminal identity"
    );
    let proof_bytes = terminal.len();
    fs::write(temporary.path().join("terminal.bin"), terminal)?;
    let origin_bytes = copy_origins(&node.join("fork-origins"), temporary.path(), height)?;
    let manifest = json!({"schema":1, "network":crate::artifacts::profile().network,
        "height":height, "block_hash":hex::encode(block_id(&header)),
        "proof_class":metadata.class_id(), "proof_bytes":proof_bytes, "origin_bytes":origin_bytes,
        "headers":height + 1, "header_bytes":(height + 1) * 212});
    fs::write(
        temporary.path().join("bundle.json"),
        serde_json::to_vec_pretty(&manifest)?,
    )?;
    fs::rename(temporary.path(), output)?;
    Ok(manifest)
}
