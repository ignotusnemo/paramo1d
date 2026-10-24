use crate::{
    artifacts::{self, MatrixMode, Runtime, MAX_ORIGIN_BYTES},
    headers::{CheckedHeaders, HeaderSummary},
};
use anyhow::{ensure, Context, Result};
use noid_chain::{
    consensus::{params, tx_epoch_anchor_height_for_child},
    history_step::HistoryStepTerminalMetadata,
};
use noid_recursive::acceptance::history_step::v2::{banked as v2, capacity_banked as v21};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::{path::Path, time::Instant};

#[derive(Debug, Serialize)]
pub struct VerifiedState {
    network: String,
    height: u64,
    block_hash: String,
    state_root: String,
    proof_class: u8,
    proof_bytes: usize,
    origin_bytes: usize,
    matrix_mode: MatrixMode,
    verified_headers: HeaderSummary,
    elapsed_ms: u128,
    reused_origins: u8,
    worker_threads: usize,
    header_ms: u128,
    origin_ms: u128,
    proof_ms: u128,
    reused_headers: u64,
}

pub struct Verifier {
    runtime: Runtime,
    mode: MatrixMode,
    previous: Option<CachedOrigin<v2::VerifiedOrigin>>,
    current: Option<CachedOrigin<v21::VerifiedOrigin>>,
    current_predecessor: Option<[u8; 32]>,
    headers: Option<CheckedHeaders>,
}

struct CachedOrigin<T> {
    encoded_digest: [u8; 32],
    parent: noid_chain::BlockHeader,
    epoch: noid_chain::BlockHeader,
    verified: T,
}

impl<T> CachedOrigin<T> {
    fn matches(&self, digest: [u8; 32], headers: &CheckedHeaders) -> Result<bool> {
        if self.encoded_digest != digest {
            return Ok(false);
        }
        ensure!(
            self.parent == headers.at(self.parent.height)?,
            "cached origin parent chain"
        );
        ensure!(
            self.epoch == headers.at(self.epoch.height)?,
            "cached origin epoch chain"
        );
        Ok(true)
    }
}

pub fn verify_bundle(
    artifact_directory: &Path,
    bundle: &Path,
    mode: MatrixMode,
) -> Result<VerifiedState> {
    let start = Instant::now();
    let mut verifier = Verifier::open(artifact_directory, mode)?;
    let mut result = verifier.verify_bundle(bundle)?;
    result.elapsed_ms = start.elapsed().as_millis();
    Ok(result)
}

impl Verifier {
    pub fn claimed_origin_request(&self, bytes: &[u8]) -> Result<[u8; 32]> {
        let metadata = HistoryStepTerminalMetadata::decode_prefix(bytes)?;
        if params::v2_1_active(metadata.terminal_height()) {
            let terminal = v21::decode_terminal(&self.runtime.current, bytes)
                .map_err(|e| anyhow::anyhow!("terminal codec: {e}"))?;
            Ok(terminal
                .claimed_origin(&self.runtime.current)
                .map_err(|e| anyhow::anyhow!("origin claim: {e}"))?
                .request_binding())
        } else {
            let terminal = v2::decode_terminal(&self.runtime.previous, bytes)
                .map_err(|e| anyhow::anyhow!("terminal codec: {e}"))?;
            Ok(terminal
                .claimed_origin(&self.runtime.previous)
                .map_err(|e| anyhow::anyhow!("origin claim: {e}"))?
                .request_binding())
        }
    }

    pub fn open(artifact_directory: &Path, mode: MatrixMode) -> Result<Self> {
        noid_core::cpu::ensure_production_hardware()?;
        Ok(Self {
            runtime: Runtime::load(artifact_directory, mode)?,
            mode,
            previous: None,
            current: None,
            current_predecessor: None,
            headers: None,
        })
    }

    pub fn verify_bundle(&mut self, bundle: &Path) -> Result<VerifiedState> {
        let start = Instant::now();
        let headers =
            CheckedHeaders::verify_after(&bundle.join("headers.bin"), self.headers.as_ref())?;
        if let Some(previous) = &self.headers {
            ensure!(
                !noid_chain::consensus::difficulty::le256_lt(&headers.work, &previous.work),
                "candidate work below accepted chain"
            );
            let finalized = previous
                .tip
                .height
                .saturating_sub(params::CONSENSUS_FINALITY_DEPTH);
            ensure!(
                headers.at(finalized)? == previous.at(finalized)?,
                "candidate crosses accepted finality"
            );
            if headers.work == previous.work {
                ensure!(
                    headers.tip == previous.tip,
                    "equal-work candidate differs from accepted tip"
                );
            }
        }
        let header_ms = start.elapsed().as_millis();
        let origin_started = Instant::now();
        let origin_ms;
        let proof_started;
        let bytes = artifacts::read_bounded(&bundle.join("terminal.bin"), 1_100_000)?;
        let metadata = HistoryStepTerminalMetadata::decode_prefix(&bytes)?;
        let height = metadata.terminal_height();
        let header = headers.at(height)?;
        ensure!(
            metadata.terminal_hash() == noid_chain::block_header::semantic_header_id(&header),
            "terminal header identity"
        );
        ensure!(
            headers.tip.height == height,
            "terminal must cover the checked chain tip"
        );
        let epoch = headers.at(tx_epoch_anchor_height_for_child(height))?;
        let runtime = &self.runtime;
        let origin = artifacts::read_bounded(&bundle.join("origin.bin"), MAX_ORIGIN_BYTES)?;
        let mut origin_bytes = origin.len();
        let origin_digest = Sha256::digest(&origin).into();
        if std::env::var_os("PARAMO1D_TERMINAL").is_some() {
            eprintln!("  ORIGIN     Authenticating the fork certificate");
        }
        let mut reused_origins = 0;
        if self
            .previous
            .as_ref()
            .map(|cached| cached.matches(origin_digest, &headers))
            .transpose()?
            .unwrap_or(false)
        {
            reused_origins += 1;
        } else {
            let verified = verify_previous_origin(runtime, &origin, &headers)?;
            let certificate = v2::RetirementOriginCertificate::from_bytes(&origin)
                .map_err(|e| anyhow::anyhow!("retirement origin codec: {e}"))?;
            self.previous = Some(CachedOrigin {
                encoded_digest: origin_digest,
                parent: *certificate.legacy_certificate().parent_header(),
                epoch: *certificate.legacy_certificate().epoch_header(),
                verified,
            });
        }
        drop(origin);
        let previous = &self
            .previous
            .as_ref()
            .context("verified predecessor origin")?
            .verified;
        let accepted_state = if params::v2_1_active(height) {
            let current_origin_bytes =
                artifacts::read_bounded(&bundle.join("current-origin.bin"), MAX_ORIGIN_BYTES)?;
            let digest = Sha256::digest(&current_origin_bytes).into();
            let predecessor = previous.origin().request_binding();
            if self.current_predecessor == Some(predecessor)
                && self
                    .current
                    .as_ref()
                    .map(|cached| cached.matches(digest, &headers))
                    .transpose()?
                    .unwrap_or(false)
            {
                reused_origins += 1;
            } else {
                let certificate =
                    v21::AuthorizationOriginCertificate::from_bytes(&current_origin_bytes)
                        .map_err(|e| anyhow::anyhow!("v2.1 origin codec: {e}"))?;
                ensure!(
                    *certificate.parent_header()
                        == headers.at(certificate.parent_header().height)?,
                    "v2.1 origin parent chain"
                );
                ensure!(
                    *certificate.epoch_header() == headers.at(certificate.epoch_header().height)?,
                    "v2.1 origin epoch chain"
                );
                ensure!(
                    certificate.previous_origin_request() == predecessor,
                    "origin predecessor identity"
                );
                let current = certificate
                    .verify(&runtime.previous, previous, runtime.current.bank())
                    .map_err(|e| anyhow::anyhow!("v2.1 origin verification: {e}"))?;
                self.current = Some(CachedOrigin {
                    encoded_digest: digest,
                    parent: *certificate.parent_header(),
                    epoch: *certificate.epoch_header(),
                    verified: current,
                });
                self.current_predecessor = Some(predecessor);
            }
            origin_bytes += current_origin_bytes.len();
            drop(current_origin_bytes);
            let current = &self
                .current
                .as_ref()
                .context("verified current origin")?
                .verified;
            let terminal = v21::decode_terminal(&runtime.current, &bytes)
                .map_err(|e| anyhow::anyhow!("v2.1 terminal codec: {e}"))?;
            origin_ms = origin_started.elapsed().as_millis();
            proof_started = Instant::now();
            if std::env::var_os("PARAMO1D_TERMINAL").is_some() {
                eprintln!("  PROOF      Verifying current recursive State proof");
            }
            let accepted =
                v21::verify_terminal(&runtime.current, current, &terminal, &header, &epoch)
                    .map_err(|e| anyhow::anyhow!("v2.1 terminal verification: {e}"))?;
            accepted.accumulator().state_root
        } else {
            ensure!(
                params::v2_active(height),
                "terminal predates the supported v2 profile"
            );
            let terminal = v2::decode_terminal(&runtime.previous, &bytes)
                .map_err(|e| anyhow::anyhow!("v2 terminal codec: {e}"))?;
            origin_ms = origin_started.elapsed().as_millis();
            proof_started = Instant::now();
            if std::env::var_os("PARAMO1D_TERMINAL").is_some() {
                eprintln!("  PROOF      Verifying current recursive State proof");
            }
            let accepted =
                v2::verify_terminal(&runtime.previous, previous, &terminal, &header, &epoch)
                    .map_err(|e| anyhow::anyhow!("v2 terminal verification: {e}"))?;
            accepted.accumulator().state_root
        };
        let result = VerifiedState {
            network: artifacts::profile().network,
            height,
            block_hash: hex::encode(noid_chain::consensus::pow::block_id(&header)),
            state_root: hex::encode(accepted_state),
            proof_class: metadata.class_id(),
            proof_bytes: bytes.len(),
            origin_bytes,
            matrix_mode: self.mode,
            verified_headers: headers.summary(),
            elapsed_ms: start.elapsed().as_millis(),
            reused_origins,
            worker_threads: rayon::current_num_threads(),
            header_ms,
            origin_ms,
            proof_ms: proof_started.elapsed().as_millis(),
            reused_headers: headers.reused,
        };
        self.headers = Some(headers);
        Ok(result)
    }
}

impl VerifiedState {
    pub fn height(&self) -> u64 {
        self.height
    }
    pub fn state_root(&self) -> &str {
        &self.state_root
    }
    pub fn block_hash(&self) -> &str {
        &self.block_hash
    }
}

fn verify_previous_origin(
    runtime: &Runtime,
    bytes: &[u8],
    headers: &CheckedHeaders,
) -> Result<v2::VerifiedOrigin> {
    let certificate = v2::RetirementOriginCertificate::from_bytes(bytes)
        .map_err(|e| anyhow::anyhow!("retirement origin codec: {e}"))?;
    let legacy = certificate.legacy_certificate();
    ensure!(
        *legacy.parent_header() == headers.at(legacy.parent_header().height)?,
        "retirement origin parent chain"
    );
    ensure!(
        *legacy.epoch_header() == headers.at(legacy.epoch_header().height)?,
        "retirement origin epoch chain"
    );
    certificate
        .verify(
            &runtime.legacy,
            runtime.previous.bank(),
            &runtime.retirement,
        )
        .map_err(|e| anyhow::anyhow!("retirement origin verification: {e}"))
        .context("authenticate the complete previous origin")
}
