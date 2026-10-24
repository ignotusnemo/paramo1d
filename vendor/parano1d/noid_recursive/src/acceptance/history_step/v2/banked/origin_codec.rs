// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Bounded transition-release certificate. It transports the actual last
//! legacy terminal and its sealed boundary, never an asserted State snapshot.
//! Verification uses the pinned old rows; matrix-free retirement is separate.

use super::*;

const MAGIC: &[u8; 8] = b"O1V2OR01";
const HEADER: usize = noid_chain::wire::BLOCK_HEADER_WIRE_SIZE;
const PREFIX: usize = MAGIC.len() + 2 * HEADER + 4;
pub const MAX_LEGACY_ORIGIN_BYTES: usize =
    PREFIX + noid_chain::consensus::wire_limits::MAX_HISTORY_STEP_TERMINAL_TRANSPORT_BYTES;

#[derive(Clone, Debug)]
pub struct LegacyOriginCertificate {
    parent: BlockHeader,
    epoch: BlockHeader,
    terminal: Vec<u8>,
}

impl LegacyOriginCertificate {
    pub fn new(
        parent: BlockHeader,
        epoch: BlockHeader,
        terminal: Vec<u8>,
    ) -> Result<Self, V2Error> {
        Self::check_metadata(&parent, &epoch, &terminal)?;
        Ok(Self {
            parent,
            epoch,
            terminal,
        })
    }

    fn check_metadata(
        parent: &BlockHeader,
        epoch: &BlockHeader,
        terminal: &[u8],
    ) -> Result<(), V2Error> {
        use noid_chain::history_step::HistoryStepTerminalMetadata;
        if parent.height == 0
            || epoch.height
                != noid_chain::consensus::tx_epoch_anchor_height_for_child(parent.height)
            || terminal.len() <= noid_chain::history_step::HISTORY_STEP_TERMINAL_BINDING_BYTES
            || terminal.len()
                > noid_chain::consensus::wire_limits::history_step_terminal_bytes_limit(
                    parent.height,
                )
        {
            return Err(V2Error::Origin);
        }
        // This carrier always contains a legacy terminal. Its framing does
        // not select the executable's v2 bank; verify() checks that exact
        // boundary against the independently supplied successor bank.
        let legacy_schedule = noid_chain::consensus::forks::ForkSchedule::new(
            noid_chain::consensus::params::V1_1_ACTIVATION_HEIGHT,
            None,
        )
        .ok_or(V2Error::Origin)?;
        let metadata =
            HistoryStepTerminalMetadata::decode_prefix_with_schedule(terminal, legacy_schedule)
                .map_err(|_| V2Error::Origin)?;
        if metadata.terminal_height() != parent.height
            || metadata.terminal_hash() != noid_chain::block_header::semantic_header_id(parent)
            || metadata.class_id() >= 2
        {
            return Err(V2Error::Origin);
        }
        Ok(())
    }

    pub fn parent_header(&self) -> &BlockHeader {
        &self.parent
    }
    pub fn epoch_header(&self) -> &BlockHeader {
        &self.epoch
    }
    pub fn terminal_bytes(&self) -> &[u8] {
        &self.terminal
    }

    /// Decoding supplies no authority. Every loaded certificate is fully
    /// checked against the old release bank before entering an origin cache.
    pub fn verify(
        &self,
        legacy: &HistoryStepRuntime,
        next: &Bank,
    ) -> Result<VerifiedOrigin, V2Error> {
        Self::check_metadata(&self.parent, &self.epoch, &self.terminal)?;
        if self.parent.height.checked_add(1) != Some(next.config().activation_height()) {
            return Err(V2Error::Boundary);
        }
        let terminal = decode_history_step_terminal(legacy, &self.terminal)?;
        VerifiedOrigin::from_legacy(legacy, &terminal, &self.parent, &self.epoch, next)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(PREFIX + self.terminal.len());
        out.extend_from_slice(MAGIC);
        out.extend_from_slice(&self.parent.to_bytes());
        out.extend_from_slice(&self.epoch.to_bytes());
        out.extend_from_slice(&(self.terminal.len() as u32).to_le_bytes());
        out.extend_from_slice(&self.terminal);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, V2Error> {
        if bytes.len() <= PREFIX
            || bytes.len() > MAX_LEGACY_ORIGIN_BYTES
            || !bytes.starts_with(MAGIC)
        {
            return Err(V2Error::Origin);
        }
        let length = u32::from_le_bytes(
            bytes[PREFIX - 4..PREFIX]
                .try_into()
                .map_err(|_| V2Error::Origin)?,
        ) as usize;
        if length != bytes.len() - PREFIX {
            return Err(V2Error::Origin);
        }
        let parent = BlockHeader::from_bytes(&bytes[8..8 + HEADER]).map_err(|_| V2Error::Origin)?;
        let epoch =
            BlockHeader::from_bytes(&bytes[8 + HEADER..PREFIX - 4]).map_err(|_| V2Error::Origin)?;
        // Check framing, schedule and all public bindings before copying the
        // proof bytes. The recursive verifier subsequently checks the proof.
        Self::check_metadata(&parent, &epoch, &bytes[PREFIX..])?;
        Self::new(parent, epoch, bytes[PREFIX..].to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn origin_framing_remains_legacy_and_does_not_select_a_successor_bank() {
        use noid_chain::consensus::{forks::ForkSchedule, params};
        use noid_chain::history_step::{
            HistoryStepTerminalMetadata, HISTORY_STEP_TERMINAL_V2_VERSION,
        };
        let legacy_schedule = ForkSchedule::new(params::V1_1_ACTIVATION_HEIGHT, None).unwrap();
        let mut parent = noid_chain::consensus::genesis_header();
        // Framing alone has no authority to select a different fork boundary.
        parent.height = params::V2_ACTIVATION_HEIGHT.unwrap_or(10) + 1;
        let mut epoch = noid_chain::consensus::genesis_header();
        epoch.height = noid_chain::consensus::tx_epoch_anchor_height_for_child(parent.height);
        let mut bytes = HistoryStepTerminalMetadata::new_with_schedule(
            parent.height,
            noid_chain::block_header::semantic_header_id(&parent),
            0,
            legacy_schedule,
        )
        .unwrap()
        .encode_prefix_with_schedule(legacy_schedule)
        .to_vec();
        bytes.push(0);
        assert!(LegacyOriginCertificate::new(parent, epoch, bytes.clone()).is_ok());
        bytes[0] = HISTORY_STEP_TERMINAL_V2_VERSION;
        assert!(LegacyOriginCertificate::new(parent, epoch, bytes).is_err());
    }

    #[test]
    fn origin_carrier_bounds_and_boundary_are_checked_before_proof_work() {
        let Some(height) = noid_chain::consensus::params::V2_ACTIVATION_HEIGHT else {
            return;
        };
        let mut epoch = noid_chain::consensus::genesis_header();
        let mut parent = epoch;
        parent.height = height - 1;
        epoch.height = noid_chain::consensus::tx_epoch_anchor_height_for_child(parent.height);
        let mut terminal = noid_chain::history_step::HistoryStepTerminalMetadata::new(
            parent.height,
            noid_chain::block_header::semantic_header_id(&parent),
            0,
        )
        .unwrap()
        .encode_prefix()
        .to_vec();
        terminal.push(1); // Deliberately opaque; this test grants no validity.
        let certificate = LegacyOriginCertificate::new(parent, epoch, terminal).unwrap();
        let bytes = certificate.to_bytes();
        assert_eq!(
            LegacyOriginCertificate::from_bytes(&bytes)
                .unwrap()
                .to_bytes(),
            bytes
        );
        for length in 0..bytes.len() {
            assert!(LegacyOriginCertificate::from_bytes(&bytes[..length]).is_err());
        }
        let mut over = bytes.clone();
        over.push(0);
        assert!(LegacyOriginCertificate::from_bytes(&over).is_err());
        let mut huge = bytes.clone();
        huge[PREFIX - 4..PREFIX].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(LegacyOriginCertificate::from_bytes(&huge).is_err());
        let mut wrong = bytes.clone();
        wrong[PREFIX + 9] ^= 1;
        assert!(LegacyOriginCertificate::from_bytes(&wrong).is_err());
        let mut wrong = bytes;
        wrong[PREFIX + 41] = 2;
        assert!(LegacyOriginCertificate::from_bytes(&wrong).is_err());
        assert!(
            LegacyOriginCertificate::from_bytes(&vec![0; MAX_LEGACY_ORIGIN_BYTES + 1]).is_err()
        );
    }
}
