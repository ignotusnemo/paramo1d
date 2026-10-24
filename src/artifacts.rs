use crate::matrix_store::{write_chunked, MatrixReader};
use anyhow::{ensure, Context, Result};
use noid_ivc_core::{
    field_r1cs::SeekableFieldR1csArtifact,
    matrix_claim::c1::{
        AuthenticatedC1MatrixClaimEvaluations, C1FreshLincheckClaim, C1MatrixAccClaim,
        C1MatrixClaimEvaluator,
    },
    proof::FieldShape,
};
use noid_recursive::{
    acceptance::history_step::{
        self as legacy,
        v2::{banked as v2, capacity_banked as v21, V2Error},
    },
    CanonicalHistoryStepClassId, HistoryStepMatrixLease, HistoryStepMatrixSource,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    fs::{self, File},
    io::{Read, Write},
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
};

pub const MAX_MATRIX_BYTES: u64 = 1024 * 1024 * 1024;
pub const MAX_ORIGIN_BYTES: u64 = 48 * 1024 * 1024;

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ArtifactPin {
    pub source: String,
    pub sha256: String,
    pub bytes: usize,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Profile {
    pub network: String,
    pub upstream_commit: String,
    pub artifacts: BTreeMap<String, ArtifactPin>,
    #[serde(default)]
    pub matrix_caches: BTreeMap<String, ArtifactPin>,
}

pub fn profile() -> Profile {
    #[cfg(feature = "isolated-testnet")]
    let encoded = include_str!("../profiles/isolated.json");
    #[cfg(not(feature = "isolated-testnet"))]
    let encoded = include_str!("../profiles/mainnet.json");
    serde_json::from_str(encoded).expect("compiled release profile")
}

pub fn read_bounded(path: &Path, cap: u64) -> Result<Vec<u8>> {
    let file = File::open(path).with_context(|| format!("open {}", path.display()))?;
    ensure!(file.metadata()?.len() <= cap, "file exceeds its byte limit");
    let mut bytes = Vec::new();
    file.take(cap + 1).read_to_end(&mut bytes)?;
    ensure!(bytes.len() as u64 <= cap, "file grew beyond its byte limit");
    Ok(bytes)
}

fn pinned(directory: &Path, name: &str) -> Result<Vec<u8>> {
    let profile = profile();
    let pin = profile
        .artifacts
        .get(name)
        .context("unknown release artifact")?;
    let bytes = read_bounded(&directory.join(name), pin.bytes as u64)?;
    ensure!(
        bytes.len() == pin.bytes,
        "release artifact length mismatch: {name}"
    );
    ensure!(
        hex::encode(Sha256::digest(&bytes)) == pin.sha256,
        "release artifact pin mismatch: {name}"
    );
    Ok(bytes)
}

pub fn prepare(source: &Path, destination: &Path) -> Result<serde_json::Value> {
    fs::create_dir_all(destination)?;
    for (name, pin) in profile().artifacts {
        let bytes = read_bounded(&source.join(pin.source), pin.bytes as u64)?;
        ensure!(
            hex::encode(Sha256::digest(&bytes)) == pin.sha256,
            "source release pin mismatch: {name}"
        );
        let mut file = tempfile::NamedTempFile::new_in(destination)?;
        file.write_all(&bytes)?;
        file.as_file().sync_all()?;
        file.persist(destination.join(name))?;
    }
    let mut sizes = BTreeMap::new();
    for (bank, names) in [
        ("v2", &["small", "large"][..]),
        ("v21", &["small", "large", "native"][..]),
    ] {
        for class in names {
            let encoded = source.join(format!(
                "history-step-pack-{bank}/{bank}-{class}.field-r1cs.zst"
            ));
            let mut decoder = zstd::stream::read::Decoder::new(File::open(&encoded)?)?;
            decoder.window_log_max(27)?;
            let mut output = tempfile::NamedTempFile::new_in(destination)?;
            let (logical, stored) =
                write_chunked(&mut decoder, output.as_file_mut(), MAX_MATRIX_BYTES)?;
            let name = format!("{bank}-{class}.pmatrix");
            output.persist(destination.join(&name))?;
            sizes.insert(
                name,
                serde_json::json!({"decoded": logical, "stored": stored}),
            );
        }
    }
    let caches = prepare_caches(destination, destination)?;
    Ok(
        serde_json::json!({"network": profile().network, "matrix_bytes": sizes, "matrix_caches": caches}),
    )
}

pub fn prepare_caches(directory: &Path, destination: &Path) -> Result<serde_json::Value> {
    prepare_selected_caches(directory, destination, &[])
}

pub fn prepare_selected_caches(
    directory: &Path,
    destination: &Path,
    selected: &[String],
) -> Result<serde_json::Value> {
    fs::create_dir_all(destination)?;
    let runtime = Runtime::load(directory, MatrixMode::Streaming)?;
    let mut pins = BTreeMap::new();
    let descriptors = v2::Class::ALL
        .into_iter()
        .map(|c| {
            (
                "v2",
                c.index(),
                runtime.previous.bank().config().class(c).shape(),
                runtime.previous.bank().matrix_digest(c),
            )
        })
        .chain(v21::Class::ALL.into_iter().map(|c| {
            (
                "v21",
                c.index(),
                runtime.current.bank().config().class(c).shape(),
                runtime.current.bank().matrix_digest(c),
            )
        }));
    for (bank, class, shape, digest) in descriptors {
        let name = format!("{bank}-{}", class_name(class));
        if !selected.is_empty() && !selected.contains(&name) {
            continue;
        }
        let source = directory.join(format!("{name}.field-r1cs"));
        let mut matrix = SeekableFieldR1csArtifact::preflight_for_c1(
            MatrixReader::open(&source, MAX_MATRIX_BYTES)?,
            shape,
            digest,
            MAX_MATRIX_BYTES,
        )?;
        let checked = matrix.evaluate_matrix_claims_c1(None, None)?;
        ensure!(
            checked.structural_digest() == digest,
            "prepared matrix identity"
        );
        let bytes = matrix
            .export_c1_span_cache()
            .context("authenticated matrix spans")?;
        let file_name = format!("{name}.spancache");
        let sha256 = hex::encode(Sha256::digest(&bytes));
        if let Some(pin) = profile().matrix_caches.get(&name) {
            ensure!(
                pin.bytes == bytes.len() && pin.sha256 == sha256,
                "prepared matrix cache pin: {name}"
            );
        }
        let mut output = tempfile::NamedTempFile::new_in(destination)?;
        output.write_all(&bytes)?;
        output.as_file().sync_all()?;
        output.persist(destination.join(&file_name))?;
        pins.insert(
            name,
            ArtifactPin {
                source: file_name,
                sha256,
                bytes: bytes.len(),
            },
        );
    }
    Ok(serde_json::to_value(pins)?)
}

struct UnavailableRows;
impl v2::MatrixSource for UnavailableRows {
    fn load(&self, _: v2::Class) -> Result<HistoryStepMatrixLease, V2Error> {
        Err(V2Error::Matrix)
    }
}
impl v21::MatrixSource for UnavailableRows {
    fn load(&self, _: v21::Class) -> Result<HistoryStepMatrixLease, V2Error> {
        Err(V2Error::Matrix)
    }
}

struct MatrixFile {
    path: PathBuf,
    shape: FieldShape,
    digest: [u8; 32],
    cache_pin: Option<ArtifactPin>,
    reader: Mutex<Option<SeekableFieldR1csArtifact<MatrixReader>>>,
}
impl MatrixFile {
    fn evaluate(
        &self,
        fresh: Option<&C1FreshLincheckClaim>,
        accumulated: Option<&C1MatrixAccClaim>,
    ) -> Result<AuthenticatedC1MatrixClaimEvaluations, V2Error> {
        let mut reader = self.reader.lock().map_err(|_| V2Error::Matrix)?;
        if reader.is_none() {
            let file =
                MatrixReader::open(&self.path, MAX_MATRIX_BYTES).map_err(|_| V2Error::Matrix)?;
            let mut matrix = SeekableFieldR1csArtifact::preflight_for_c1(
                file,
                self.shape,
                self.digest,
                MAX_MATRIX_BYTES,
            )
            .map_err(|_| V2Error::Matrix)?;
            if let Some(pin) = &self.cache_pin {
                let path = self.path.with_extension("spancache");
                if path.exists() {
                    let bytes =
                        read_bounded(&path, pin.bytes as u64).map_err(|_| V2Error::Matrix)?;
                    let hash: [u8; 32] = hex::decode(&pin.sha256)
                        .map_err(|_| V2Error::Matrix)?
                        .try_into()
                        .map_err(|_| V2Error::Matrix)?;
                    matrix
                        .restore_c1_span_cache(&bytes, hash)
                        .map_err(|_| V2Error::Matrix)?;
                }
            }
            *reader = Some(matrix);
        }
        reader
            .as_mut()
            .ok_or(V2Error::Matrix)?
            .evaluate_matrix_claims_c1(fresh, accumulated)
            .map_err(|_| V2Error::Matrix)
    }
}
struct V2Files([MatrixFile; 2]);
struct V21Files([MatrixFile; 3]);
impl v2::VerifierMatrixSource for V2Files {
    fn evaluate(
        &self,
        class: v2::Class,
        fresh: Option<&C1FreshLincheckClaim>,
        accumulated: Option<&C1MatrixAccClaim>,
    ) -> Result<AuthenticatedC1MatrixClaimEvaluations, V2Error> {
        self.0[class.index()].evaluate(fresh, accumulated)
    }
}
impl v21::VerifierMatrixSource for V21Files {
    fn evaluate(
        &self,
        class: v21::Class,
        fresh: Option<&C1FreshLincheckClaim>,
        accumulated: Option<&C1MatrixAccClaim>,
    ) -> Result<AuthenticatedC1MatrixClaimEvaluations, V2Error> {
        self.0[class.index()].evaluate(fresh, accumulated)
    }
}

pub struct Runtime {
    pub legacy: legacy::HistoryStepRuntime,
    pub previous: v2::Runtime,
    pub current: v21::Runtime,
    pub retirement: v2::PinnedRetirementKeys,
}

#[derive(Debug, Clone, Copy, clap::ValueEnum, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum MatrixMode {
    Streaming,
    Resident,
}

impl Runtime {
    pub fn load(directory: &Path, mode: MatrixMode) -> Result<Self> {
        let bytes = pinned(directory, "legacy")?;
        let digest = bytes[bytes.len() - 32..].try_into()?;
        let metadata = noid_miner::decode_history_step_runtime_metadata_pinned(&bytes, digest)?;
        let k0 = pinned(directory, "retirement0")?;
        let k1 = pinned(directory, "retirement1")?;
        // Derive protocol key digests from the release-pinned key bytes.
        let key_pins = [key_digest(&k0)?, key_digest(&k1)?];
        let retirement =
            v2::PinnedRetirementKeys::from_release(metadata.bank(), [&k0, &k1], key_pins)
                .map_err(|e| anyhow::anyhow!("retirement keys: {e}"))?;
        let (legacy_bank, legacy_parts) = metadata.into_parts();
        let legacy =
            legacy::HistoryStepRuntime::new(legacy_bank, Box::new(RetiredRows), legacy_parts)
                .map_err(|e| anyhow::anyhow!("legacy runtime: {e}"))?;
        let bytes = pinned(directory, "v2")?;
        ensure!(bytes.starts_with(b"O1V2BNK1"), "v2 metadata framing");
        let parts = v2::RuntimeParts::decode_compact(&bytes[76..])
            .map_err(|e| anyhow::anyhow!("v2 parts: {e}"))?;
        let bank = v2::Bank::pin(
            [bytes[8..40].try_into()?, bytes[40..72].try_into()?],
            &parts,
        );
        let previous = match mode {
            MatrixMode::Streaming => {
                let files = v2::Class::ALL.map(|c| MatrixFile {
                    path: directory.join(format!("v2-{}.field-r1cs", class_name(c.index()))),
                    shape: bank.config().class(c).shape(),
                    digest: bank.matrix_digest(c),
                    cache_pin: profile()
                        .matrix_caches
                        .get(&format!("v2-{}", class_name(c.index())))
                        .cloned(),
                    reader: Mutex::new(None),
                });
                v2::Runtime::new(bank, parts, Box::new(UnavailableRows))
                    .map_err(|e| anyhow::anyhow!("v2 runtime: {e}"))?
                    .with_verifier_matrix_source(Box::new(V2Files(files)))
            }
            MatrixMode::Resident => {
                let metadata = noid_miner::v2_artifacts::decode_v2_runtime_metadata_pinned(
                    &bytes,
                    bank.digest(),
                )
                .map_err(anyhow::Error::msg)?;
                let compressed = v2::Class::ALL.map(|c| {
                    compress_file(
                        &directory.join(format!("v2-{}.field-r1cs", class_name(c.index()))),
                    )
                });
                metadata
                    .into_runtime(collect_array(compressed)?)
                    .map_err(anyhow::Error::msg)?
            }
        };
        let bytes = pinned(directory, "v21")?;
        ensure!(bytes.starts_with(b"O1V21BN1"), "v2.1 metadata framing");
        let parts = v21::RuntimeParts::decode_compact(&bytes[108..])
            .map_err(|e| anyhow::anyhow!("v2.1 parts: {e}"))?;
        let bank = v21::Bank::pin(
            [
                bytes[8..40].try_into()?,
                bytes[40..72].try_into()?,
                bytes[72..104].try_into()?,
            ],
            &parts,
        );
        ensure!(
            bank.config().schedule() == noid_chain::consensus::forks::ACTIVE_SCHEDULE,
            "release schedule mismatch"
        );
        ensure!(
            Some(bank.config().activation_height())
                == noid_chain::consensus::params::V2_1_ACTIVATION_HEIGHT,
            "release activation mismatch"
        );
        let current = match mode {
            MatrixMode::Streaming => {
                let files = v21::Class::ALL.map(|c| MatrixFile {
                    path: directory.join(format!("v21-{}.field-r1cs", class_name(c.index()))),
                    shape: bank.config().class(c).shape(),
                    digest: bank.matrix_digest(c),
                    cache_pin: profile()
                        .matrix_caches
                        .get(&format!("v21-{}", class_name(c.index())))
                        .cloned(),
                    reader: Mutex::new(None),
                });
                v21::Runtime::new(bank, parts, Box::new(UnavailableRows))
                    .map_err(|e| anyhow::anyhow!("v2.1 runtime: {e}"))?
                    .with_verifier_matrix_source(Box::new(V21Files(files)))
            }
            MatrixMode::Resident => {
                let metadata = noid_miner::v21_artifacts::decode_v21_runtime_metadata_pinned(
                    &bytes,
                    bank.digest(),
                )
                .map_err(anyhow::Error::msg)?;
                let compressed = v21::Class::ALL.map(|c| {
                    compress_file(
                        &directory.join(format!("v21-{}.field-r1cs", class_name(c.index()))),
                    )
                });
                metadata
                    .into_runtime(collect_array(compressed)?)
                    .map_err(anyhow::Error::msg)?
            }
        };
        Ok(Self {
            legacy,
            previous,
            current,
            retirement,
        })
    }
}

fn class_name(index: usize) -> &'static str {
    ["small", "large", "native"][index]
}

fn collect_array<const N: usize>(values: [Result<Arc<[u8]>>; N]) -> Result<[Arc<[u8]>; N]> {
    values
        .into_iter()
        .collect::<Result<Vec<_>>>()?
        .try_into()
        .map_err(|_| anyhow::anyhow!("matrix count"))
}

fn compress_file(path: &Path) -> Result<Arc<[u8]>> {
    let input = MatrixReader::open(path, MAX_MATRIX_BYTES)?;
    Ok(Arc::from(zstd::stream::encode_all(input, 1)?))
}

fn key_digest(bytes: &[u8]) -> Result<[u8; 32]> {
    ensure!(bytes.len() == 304, "retirement key length");
    Ok(noid_poseidon2b::native::poseidon2b_hash_byte_slices(
        b"NOID/SPARSE-MATRIX-KEY/C1/V1",
        &[&bytes[8..]],
    ))
}

struct RetiredRows;
impl HistoryStepMatrixSource for RetiredRows {
    fn load(
        &self,
        _: CanonicalHistoryStepClassId,
    ) -> Result<HistoryStepMatrixLease, noid_recursive::HistoryStepMatrixSourceError> {
        Err(noid_recursive::HistoryStepMatrixSourceError)
    }
}
