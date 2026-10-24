// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Single-class terminal encoding. Public IO carries the immutable legacy
//! origin; the independently verified origin certificate remains mandatory.

use super::super::wire::{
    decode_f128_vec, decode_field_proof, encode_f128_vec, encode_field_proof, field_proof_len,
    Reader,
};
use super::*;
use crate::region_sidecar::{
    canonical_joint_c1_region_sidecar_len, decode_joint_c1_region_sidecar_canonical,
    encode_joint_c1_region_sidecar_canonical,
};

pub const V2_TERMINAL_VERSION: u8 = 6;
const PREFIX: usize = 42;
// Research single-class wire; it cannot be mistaken for a legacy class.
const SINGLE_CLASS_WIRE_ID: u8 = 0;

pub fn terminal_max_bytes(runtime: &V2Runtime) -> Result<usize, V2Error> {
    Ok(PREFIX
        + 32
        + runtime.bank.config().layout().len * 16
        + field_proof_len(
            runtime.bank.config().shape(),
            &runtime.bank.config().pcs_params(),
        )?
        + canonical_joint_c1_region_sidecar_len(
            &runtime.parts.parent_vk,
            &runtime.parts.block_vk,
            runtime.bank.config().outer_m(),
        )?)
}

pub fn encode_terminal(runtime: &V2Runtime, terminal: &V2Terminal) -> Result<Vec<u8>, V2Error> {
    let parsed = runtime.bank.parse(&terminal.proof.io)?;
    parsed.origin.check(&runtime.bank)?;
    if pcs_params_statement_bytes(&terminal.proof.commitment.params)
        != pcs_params_statement_bytes(&runtime.bank.config().pcs_params())
    {
        return Err(V2Error::Runtime);
    }
    let max = terminal_max_bytes(runtime)?;
    let mut out = Vec::with_capacity(max);
    out.push(V2_TERMINAL_VERSION);
    out.extend_from_slice(&parsed.accumulator.height.to_le_bytes());
    out.extend_from_slice(&parsed.accumulator.tip_semantic_id);
    out.push(SINGLE_CLASS_WIRE_ID);
    out.extend_from_slice(&terminal.proof.commitment.root);
    encode_f128_vec(
        &mut out,
        &terminal.proof.io,
        runtime.bank.config().layout().len,
    )?;
    encode_field_proof(
        &mut out,
        &terminal.proof.field,
        runtime.bank.config().shape(),
        &runtime.bank.config().pcs_params(),
        true,
    )?;
    out.extend_from_slice(&encode_joint_c1_region_sidecar_canonical(
        &runtime.parts.parent_vk,
        &runtime.parts.block_vk,
        runtime.bank.config().outer_m(),
        &terminal.proof.sidecar,
    )?);
    if out.len() > max {
        return Err(V2Error::Io);
    }
    Ok(out)
}

/// Bounded decode is not acceptance. The caller must invoke `verify_terminal`
/// with an authenticated origin and the selected sealed header.
pub fn decode_terminal(runtime: &V2Runtime, bytes: &[u8]) -> Result<V2Terminal, V2Error> {
    if bytes.len() < PREFIX + 32 + runtime.bank.config().layout().len * 16
        || bytes.len() > terminal_max_bytes(runtime)?
        || bytes[0] != V2_TERMINAL_VERSION
        || bytes[41] != SINGLE_CLASS_WIRE_ID
    {
        return Err(V2Error::Io);
    }
    let height = u64::from_le_bytes(bytes[1..9].try_into().map_err(|_| V2Error::Io)?);
    if height < runtime.bank.config().activation_height() {
        return Err(V2Error::Boundary);
    }
    let mut reader = Reader::new(&bytes[PREFIX..]);
    let root = reader.hash()?;
    let io = decode_f128_vec(&mut reader, runtime.bank.config().layout().len)?;
    // Reject a forged origin or metadata before proof allocations and PCS work.
    let parsed = runtime.bank.parse(&io)?;
    parsed.origin.check(&runtime.bank)?;
    if height != parsed.accumulator.height || bytes[9..41] != parsed.accumulator.tip_semantic_id {
        return Err(V2Error::Boundary);
    }
    let field = decode_field_proof(
        &mut reader,
        runtime.bank.config().shape(),
        &runtime.bank.config().pcs_params(),
        true,
    )?;
    let len = canonical_joint_c1_region_sidecar_len(
        &runtime.parts.parent_vk,
        &runtime.parts.block_vk,
        runtime.bank.config().outer_m(),
    )?;
    let sidecar = decode_joint_c1_region_sidecar_canonical(
        &runtime.parts.parent_vk,
        &runtime.parts.block_vk,
        runtime.bank.config().outer_m(),
        reader.take(len)?,
    )?;
    reader.finish()?;
    Ok(V2Terminal {
        proof: V2Proof {
            field,
            commitment: Commitment {
                root,
                params: runtime.bank.config().pcs_params(),
            },
            io,
            sidecar,
        },
    })
}
