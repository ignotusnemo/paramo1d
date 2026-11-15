use anyhow::{ensure, Context, Result};
use noid_chain::{
    consensus::{
        difficulty::{add_work, block_work},
        genesis::genesis_header,
        header::{asert_anchor_height, validate_header_timeless_prehashed},
        params::{CONSENSUS_FINALITY_DEPTH, EXPANSION_HEADER_LOOKBACK},
        pow::{block_id, pow_header_fields},
    },
    wire::BLOCK_HEADER_WIRE_SIZE,
    BlockHeader,
};
use noid_core::hardware::{flat_to_tower_u128, tower_to_flat_u128};
use noid_poseidon2b::{
    batch::leaf_sponge_flat_batch_with_iv_into,
    native::domain::{capacity_iv_flat, TAG_BLOCKHDR, TAG_POWHDR},
};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha512};
use std::{
    collections::VecDeque,
    fs::File,
    io::{Read, Seek, SeekFrom, Write},
    path::Path,
    sync::Mutex,
};

const MAX_HEADER_FILE_BYTES: u64 = 8 * 1024 * 1024 * 1024;
const HEADER_CHUNK: usize = 4096;
const HASH_BATCH: usize = 128;
const CHECKPOINT_DOMAIN: &[u8] = b"Paramo1d/verified-header-prefix/1";

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PrefixRecord {
    version: u8,
    count: u64,
    tip: String,
    work: String,
    sha512: String,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SealedPrefix {
    record: PrefixRecord,
    tag: String,
}

fn copy_and_hash(input: &mut File, output: &mut impl Write, bytes: u64) -> Result<String> {
    let mut hash = Sha512::new();
    let mut remaining = bytes;
    let mut buffer = [0u8; 65536];
    input.seek(SeekFrom::Start(0))?;
    while remaining > 0 {
        crate::mobile_control::check()?;
        let count = remaining.min(buffer.len() as u64) as usize;
        input.read_exact(&mut buffer[..count])?;
        output.write_all(&buffer[..count])?;
        hash.update(&buffer[..count]);
        remaining -= count as u64;
    }
    ensure!(
        input.read(&mut buffer[..1])? == 0,
        "Header checkpoint length changed"
    );
    Ok(hex::encode(hash.finalize()))
}

struct HeaderHashes {
    id: [u8; 32],
    pow: [u8; 32],
}

fn hash_batch(headers: &[BlockHeader]) -> Vec<HeaderHashes> {
    let mut pow_fields = Vec::with_capacity(headers.len() * 256);
    let mut id_fields = Vec::with_capacity(headers.len() * 288);
    for header in headers {
        for field in pow_header_fields(header) {
            let flat = tower_to_flat_u128(field.0).to_le_bytes();
            pow_fields.extend_from_slice(&flat);
            id_fields.extend_from_slice(&flat);
        }
        // BLOCKHDR uses the canonical tower-basis 0x80...01 padding block.
        for field in [0x80u128, 1u128 << 120] {
            id_fields.extend_from_slice(&tower_to_flat_u128(field).to_le_bytes());
        }
    }
    let mut ids = vec![[0; 32]; headers.len()];
    let mut pow = vec![[0; 32]; headers.len()];
    leaf_sponge_flat_batch_with_iv_into(
        capacity_iv_flat(TAG_BLOCKHDR),
        false,
        &id_fields,
        288,
        &mut ids,
    );
    leaf_sponge_flat_batch_with_iv_into(
        capacity_iv_flat(TAG_POWHDR),
        false,
        &pow_fields,
        256,
        &mut pow,
    );
    ids.into_iter()
        .zip(pow)
        .map(|(mut id, mut pow)| {
            for hash in [&mut id, &mut pow] {
                for lane in hash.chunks_exact_mut(16) {
                    let flat = u128::from_le_bytes(lane.try_into().expect("hash lane"));
                    lane.copy_from_slice(&flat_to_tower_u128(flat).to_le_bytes());
                }
            }
            HeaderHashes { id, pow }
        })
        .collect()
}

pub struct CheckedHeaders {
    file: Mutex<File>,
    pub(crate) tip: BlockHeader,
    pub(crate) work: [u8; 32],
    pub(crate) count: u64,
    pub(crate) reused: u64,
}

#[derive(Clone, Debug, Serialize)]
pub struct HeaderSummary {
    pub height: u64,
    pub hash: String,
    pub state_root: String,
    pub chainwork_le: String,
    pub header_bytes: u64,
}

pub fn read_header(file: &mut File, height: u64) -> Result<BlockHeader> {
    let at = height
        .checked_mul(BLOCK_HEADER_WIRE_SIZE as u64)
        .context("header offset overflow")?;
    file.seek(SeekFrom::Start(at))?;
    let mut bytes = [0; BLOCK_HEADER_WIRE_SIZE];
    file.read_exact(&mut bytes)
        .with_context(|| format!("read header {height}"))?;
    let mut input = bytes.as_slice();
    let header =
        BlockHeader::decode(&mut input).map_err(|e| anyhow::anyhow!("header encoding: {e:?}"))?;
    ensure!(
        input.is_empty() && header.height == height,
        "noncanonical header location"
    );
    Ok(header)
}

impl CheckedHeaders {
    pub(crate) fn save_checkpoint(&self, path: &Path) -> Result<()> {
        if crate::wallet_checkpoint::local_tag(CHECKPOINT_DOMAIN, b"")?.is_none() {
            return Ok(());
        }
        let bytes = self
            .count
            .checked_mul(BLOCK_HEADER_WIRE_SIZE as u64)
            .context("Header checkpoint bytes")?;
        let mut input = self
            .file
            .lock()
            .map_err(|_| anyhow::anyhow!("Header checkpoint lock"))?;
        let mut sink = std::io::sink();
        let digest = copy_and_hash(&mut input, &mut sink, bytes)?;
        let record = PrefixRecord {
            version: 1,
            count: self.count,
            tip: hex::encode(self.tip.to_bytes()),
            work: hex::encode(self.work),
            sha512: digest,
        };
        let tag =
            crate::wallet_checkpoint::local_tag(CHECKPOINT_DOMAIN, &serde_json::to_vec(&record)?)?
                .context("Header checkpoint identity")?;
        let folder = path.parent().context("Header checkpoint directory")?;
        let mut out = tempfile::NamedTempFile::new_in(folder)?;
        out.write_all(&serde_json::to_vec(&SealedPrefix { record, tag })?)?;
        out.as_file().sync_all()?;
        out.persist(folder.join("headers-auth.json"))
            .map_err(|e| e.error)?;
        Ok(())
    }

    pub(crate) fn restore_checkpoint(path: &Path) -> Result<Self> {
        let folder = path.parent().context("Header checkpoint directory")?;
        let data = crate::artifacts::read_bounded(&folder.join("headers-auth.json"), 16384)?;
        let sealed: SealedPrefix = serde_json::from_slice(&data)?;
        crate::wallet_checkpoint::check_local_tag(
            CHECKPOINT_DOMAIN,
            &serde_json::to_vec(&sealed.record)?,
            &sealed.tag,
        )?;
        let r = sealed.record;
        let bytes = r
            .count
            .checked_mul(BLOCK_HEADER_WIRE_SIZE as u64)
            .context("Header checkpoint bytes")?;
        ensure!(
            r.version == 1 && r.count > 0 && bytes <= MAX_HEADER_FILE_BYTES,
            "Header checkpoint shape"
        );
        let tip = BlockHeader::from_bytes(&hex::decode(r.tip)?)
            .map_err(|_| anyhow::anyhow!("Header checkpoint tip"))?;
        let work = hex::decode(r.work)?
            .try_into()
            .map_err(|_| anyhow::anyhow!("Header checkpoint work"))?;
        ensure!(
            tip.height.checked_add(1) == Some(r.count),
            "Header checkpoint count"
        );
        let mut input = File::open(path)?;
        ensure!(
            input.metadata()?.len() == bytes,
            "Header checkpoint file size"
        );
        let mut file = tempfile::tempfile_in(folder)?;
        ensure!(
            copy_and_hash(&mut input, &mut file, bytes)? == r.sha512,
            "Header checkpoint bytes changed"
        );
        ensure!(
            read_header(&mut file, 0)? == genesis_header()
                && read_header(&mut file, tip.height)? == tip,
            "Header checkpoint boundaries"
        );
        Ok(Self {
            file: Mutex::new(file),
            tip,
            work,
            count: r.count,
            reused: r.count,
        })
    }

    pub fn verify(path: &Path) -> Result<Self> {
        Self::verify_after(path, None)
    }

    pub(crate) fn verify_after(path: &Path, previous: Option<&Self>) -> Result<Self> {
        let input = File::open(path)?;
        ensure!(
            input.metadata()?.len() <= MAX_HEADER_FILE_BYTES,
            "header input byte limit"
        );
        let parent = path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        let mut file = tempfile::tempfile_in(parent)?;
        let bytes = std::io::copy(&mut input.take(MAX_HEADER_FILE_BYTES + 1), &mut file)?;
        ensure!(
            bytes > 0 && bytes <= MAX_HEADER_FILE_BYTES,
            "header file byte limit"
        );
        ensure!(
            bytes % BLOCK_HEADER_WIRE_SIZE as u64 == 0,
            "truncated header file"
        );
        let count = bytes / BLOCK_HEADER_WIRE_SIZE as u64;
        let reused = if let Some(previous) = previous.filter(|p| p.count <= count) {
            let mut checked = previous
                .file
                .lock()
                .map_err(|_| anyhow::anyhow!("header store lock"))?;
            checked.seek(SeekFrom::Start(0))?;
            file.seek(SeekFrom::Start(0))?;
            let mut left = vec![0; 1024 * 1024];
            let mut right = vec![0; left.len()];
            let mut remaining = previous.count * BLOCK_HEADER_WIRE_SIZE as u64;
            let mut same = true;
            while remaining > 0 {
                let n = remaining.min(left.len() as u64) as usize;
                checked.read_exact(&mut left[..n])?;
                file.read_exact(&mut right[..n])?;
                if left[..n] != right[..n] {
                    same = false;
                    break;
                }
                remaining -= n as u64;
            }
            if same {
                previous.count
            } else {
                0
            }
        } else {
            0
        };
        let mut parent = read_header(&mut file, 0)?;
        ensure!(
            parent == genesis_header(),
            "chain genesis differs from the compiled network"
        );
        let mut parent_id = block_id(&parent);
        let mut work = block_work(&parent.difficulty_target);
        let mut recent = VecDeque::from([parent]);
        let mut anchor = parent;
        if reused > 0 {
            let checked = previous.expect("matched verified prefix");
            parent = checked.tip;
            parent_id = block_id(&parent);
            work = checked.work;
            recent.clear();
            for height in parent.height.saturating_sub(EXPANSION_HEADER_LOOKBACK)..=parent.height {
                recent.push_back(read_header(&mut file, height)?);
            }
        }
        let terminal_output = std::env::var_os("PARAMO1D_TERMINAL").is_some();
        let mut encoded = vec![0; HEADER_CHUNK * BLOCK_HEADER_WIRE_SIZE];
        for first in (reused.max(1)..count).step_by(HEADER_CHUNK) {
            crate::mobile_control::check()?;
            let length = (count - first).min(HEADER_CHUNK as u64) as usize;
            file.seek(SeekFrom::Start(first * BLOCK_HEADER_WIRE_SIZE as u64))?;
            let chunk = &mut encoded[..length * BLOCK_HEADER_WIRE_SIZE];
            file.read_exact(chunk)?;
            let decoded = chunk
                .chunks_exact(BLOCK_HEADER_WIRE_SIZE)
                .enumerate()
                .map(|(i, bytes)| {
                    let mut input = bytes;
                    let header = BlockHeader::decode(&mut input)
                        .map_err(|e| anyhow::anyhow!("header encoding: {e:?}"))?;
                    ensure!(
                        input.is_empty() && header.height == first + i as u64,
                        "noncanonical header location"
                    );
                    Ok(header)
                })
                .collect::<Result<Vec<_>>>()?;
            let hashes = decoded
                .par_chunks(HASH_BATCH)
                .map(hash_batch)
                .collect::<Vec<_>>();
            for (header, hash) in decoded.into_iter().zip(hashes.into_iter().flatten()) {
                let height = header.height;
                ensure!((24..=32).contains(&header.log_slots), "header State depth");
                ensure!(
                    header.active_slot_count <= 1u64 << header.log_slots,
                    "header occupancy"
                );
                let timestamps: Vec<_> = recent
                    .iter()
                    .rev()
                    .take(11)
                    .map(|h| h.timestamp)
                    .collect::<Vec<_>>()
                    .into_iter()
                    .rev()
                    .collect();
                let active: Vec<_> = if parent.height >= EXPANSION_HEADER_LOOKBACK {
                    let start = parent.height - EXPANSION_HEADER_LOOKBACK;
                    let end = parent.height - CONSENSUS_FINALITY_DEPTH;
                    recent
                        .iter()
                        .filter(|h| h.height >= start && h.height <= end)
                        .map(|h| h.active_slot_count)
                        .collect()
                } else {
                    Vec::new()
                };
                let anchor_height = asert_anchor_height(parent.height);
                if anchor.height != anchor_height {
                    anchor = read_header(&mut file, anchor_height)?;
                }
                validate_header_timeless_prehashed(
                    &header,
                    &parent,
                    parent_id,
                    hash.pow,
                    &timestamps,
                    &active,
                    anchor.height,
                    anchor.timestamp,
                    &anchor.difficulty_target,
                )
                .with_context(|| format!("header consensus at height {height}"))?;
                work = add_work(&work, &block_work(&header.difficulty_target));
                parent_id = hash.id;
                parent = header;
                recent.push_back(header);
                while recent.len() > EXPANSION_HEADER_LOOKBACK as usize + 1 {
                    recent.pop_front();
                }
            }
            if terminal_output {
                eprint!(
                    "\r  CHECKED    {} / {} header proofs of work",
                    parent.height + 1,
                    count
                );
            }
        }
        if terminal_output {
            eprintln!();
        }
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_secs();
        noid_chain::consensus::timestamps::validate_future_drift(parent.timestamp, now)?;
        Ok(Self {
            file: Mutex::new(file),
            tip: parent,
            work,
            count,
            reused,
        })
    }

    pub fn at(&self, height: u64) -> Result<BlockHeader> {
        ensure!(height < self.count, "header outside verified chain");
        let mut file = self
            .file
            .lock()
            .map_err(|_| anyhow::anyhow!("header store lock"))?;
        read_header(&mut file, height)
    }

    pub fn summary(&self) -> HeaderSummary {
        HeaderSummary {
            height: self.tip.height,
            hash: hex::encode(block_id(&self.tip)),
            state_root: hex::encode(self.tip.state_root),
            chainwork_le: hex::encode(self.work),
            header_bytes: self.count * BLOCK_HEADER_WIRE_SIZE as u64,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn authenticated_header_resume_binds_bytes_work_identity_and_new_extension() {
        let directory = tempfile::tempdir().unwrap();
        let old = directory.path().join("old");
        let new = directory.path().join("new");
        std::fs::create_dir_all(&old).unwrap();
        std::fs::create_dir_all(&new).unwrap();
        let path = old.join("headers.bin");
        let genesis = genesis_header();
        std::fs::write(&path, genesis.to_bytes()).unwrap();
        let checked = CheckedHeaders::verify(&path).unwrap();
        let args = serde_json::json!({"seed_hex":hex::encode([19u8;32])});
        crate::wallet_checkpoint::with_identity(&args, || {
            checked.save_checkpoint(&path).unwrap();
            let restored = CheckedHeaders::restore_checkpoint(&path).unwrap();
            assert_eq!(restored.tip, checked.tip);
            assert_eq!(restored.work, checked.work);
            let next = new.join("headers.bin");
            let mut bytes = genesis.to_bytes().to_vec();
            bytes.extend_from_slice(include_bytes!("../tests/fixtures/mainnet-first-header.bin"));
            std::fs::write(&next, &bytes).unwrap();
            let extended = CheckedHeaders::verify_after(&next, Some(&restored)).unwrap();
            let fresh = CheckedHeaders::verify(&next).unwrap();
            assert_eq!(extended.reused, 1);
            assert_eq!(extended.tip, fresh.tip);
            assert_eq!(extended.work, fresh.work);
            let checkpoint = std::fs::read(old.join("headers-auth.json")).unwrap();
            let mut forged: serde_json::Value = serde_json::from_slice(&checkpoint).unwrap();
            forged["record"]["work"] = serde_json::json!("ff".repeat(32));
            std::fs::write(
                old.join("headers-auth.json"),
                serde_json::to_vec(&forged).unwrap(),
            )
            .unwrap();
            assert!(CheckedHeaders::restore_checkpoint(&path).is_err());
            std::fs::write(old.join("headers-auth.json"), checkpoint).unwrap();
            let mut changed = genesis.to_bytes().to_vec();
            changed[40] ^= 1;
            std::fs::write(&path, changed).unwrap();
            assert!(CheckedHeaders::restore_checkpoint(&path).is_err());
            std::fs::write(&path, genesis.to_bytes()).unwrap();
        });
        assert!(CheckedHeaders::restore_checkpoint(&path).is_err());
        crate::wallet_checkpoint::with_identity(
            &serde_json::json!({"seed_hex":hex::encode([18u8;32])}),
            || assert!(CheckedHeaders::restore_checkpoint(&path).is_err()),
        );
    }

    #[test]
    fn batched_header_domains_match_scalar_consensus_for_every_field() {
        let headers: Vec<_> = (0..259u64)
            .map(|i| {
                let mut h = genesis_header();
                h.prev_block_hash = [i as u8; 32];
                h.state_root = [i.wrapping_mul(17) as u8; 32];
                h.tx_root = [i.wrapping_mul(31) as u8; 32];
                h.timestamp = h.timestamp.wrapping_add(i);
                h.height = i;
                h.miner_address.0 = [i.wrapping_mul(43) as u8; 32];
                h.nonce = ((i as u128) << 80) | (i as u128).wrapping_mul(179);
                h.difficulty_target = [i.wrapping_mul(71) as u8; 32];
                h.log_slots = 24 + (i % 9) as u32;
                h.active_slot_count = i * 101;
                h.alloc_counter = i * 313;
                h
            })
            .collect();
        for chunk in headers.chunks(HASH_BATCH) {
            for (h, hashes) in chunk.iter().zip(hash_batch(chunk)) {
                assert_eq!(hashes.id, block_id(h));
                assert_eq!(
                    hashes.pow,
                    noid_chain::consensus::pow::poseidon_pow_digest(h)
                );
            }
        }
    }

    #[test]
    #[cfg(not(feature = "isolated-testnet"))]
    fn batched_admission_matches_core_consensus_on_mainnet_and_changed_headers() {
        use noid_chain::consensus::header::validate_header_timeless_prehashed_parent;
        let parent = genesis_header();
        let first =
            BlockHeader::from_bytes(include_bytes!("../tests/fixtures/mainnet-first-header.bin"))
                .unwrap();
        let check = |header: &BlockHeader| {
            let hash = hash_batch(std::slice::from_ref(header)).pop().unwrap();
            let original = validate_header_timeless_prehashed_parent(
                header,
                &parent,
                block_id(&parent),
                &[parent.timestamp],
                &[],
                0,
                parent.timestamp,
                &parent.difficulty_target,
            );
            let batch = validate_header_timeless_prehashed(
                header,
                &parent,
                block_id(&parent),
                hash.pow,
                &[parent.timestamp],
                &[],
                0,
                parent.timestamp,
                &parent.difficulty_target,
            );
            assert_eq!(original.is_ok(), batch.is_ok());
            original.is_ok()
        };
        assert!(check(&first));
        for field in 0..11 {
            let mut h = first;
            match field {
                0 => h.prev_block_hash[0] ^= 1,
                1 => h.state_root[0] ^= 1,
                2 => h.tx_root[0] ^= 1,
                3 => h.timestamp = parent.timestamp,
                4 => h.height += 1,
                5 => h.miner_address.0[0] ^= 1,
                6 => h.nonce ^= 1,
                7 => h.difficulty_target[0] ^= 1,
                8 => h.log_slots += 1,
                9 => h.active_slot_count += 1,
                _ => h.alloc_counter += 1,
            }
            check(&h);
        }
        let file = tempfile::NamedTempFile::new().unwrap();
        std::fs::write(file.path(), parent.to_bytes()).unwrap();
        let genesis = CheckedHeaders::verify(file.path()).unwrap();
        let both = [parent.to_bytes(), first.to_bytes()].concat();
        std::fs::write(file.path(), &both).unwrap();
        let appended = CheckedHeaders::verify_after(file.path(), Some(&genesis)).unwrap();
        assert_eq!(appended.reused, 1);
        assert_eq!(appended.summary().hash, hex::encode(block_id(&first)));
        let fresh = CheckedHeaders::verify(file.path()).unwrap();
        assert_eq!(appended.work, fresh.work);
        std::fs::write(file.path(), [0u8; 424]).unwrap();
        assert!(CheckedHeaders::verify_after(file.path(), Some(&appended)).is_err());
    }
}
