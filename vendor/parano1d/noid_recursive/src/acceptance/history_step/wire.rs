// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Height-selected canonical terminal wire codec.
//!
//! Prefix (42 bytes): `version:u8 || height:u64-le || semantic_id:[u8;32] ||
//! class_id:u8`. The remaining proof shape is derived entirely from the
//! authenticated class/runtime. Before V1.1 activation the legacy full-path
//! encoding is byte-for-byte unchanged. After activation query records carry
//! their leaves first, followed by shared sibling dictionaries. Dictionary
//! keys/counts are derived from query positions, never supplied by the peer.
//! The decoded proof, transcript and recursive matrices are unchanged.

mod shared_paths;

use noid_chain::history_step::{
    history_step_terminal_wire_version_with_activation, HISTORY_STEP_TERMINAL_SHARED_PATH_VERSION,
};

use noid_ivc_core::field::{F128, F256};
use noid_ivc_core::pcs::basefold::{C1QueryOpening, C1RoundMessage};
use noid_ivc_core::pcs::{
    compute_fri_arities, default_fri_queries, fri_commit_layout, C1BaseFoldProof, Commitment,
    PcsParams, RoundCommitment, LOG_PACKING,
};
use noid_ivc_core::proof::{C1FieldR1csProof, FieldShape};

use super::relation::{validate_terminal_metadata, verify_history_step_terminal, HistoryStepProof};
use super::*;
use crate::acceptance::history_step_bank::{
    history_step_bank_block_accumulator, CanonicalHistoryStepClassId, HISTORY_STEP_CLASS_COUNT,
};
use crate::region_sidecar::{
    canonical_joint_c1_region_sidecar_len, decode_joint_c1_region_sidecar_canonical,
    encode_joint_c1_region_sidecar_canonical,
};

const PREFIX_BYTES: usize = 42;
const HASH_BYTES: usize = 32;
const F128_BYTES: usize = 16;
const F256_BYTES: usize = 32;

fn add(left: usize, right: usize) -> Result<usize, HistoryStepError> {
    left.checked_add(right)
        .ok_or(HistoryStepError::WireEncoding)
}

fn mul(left: usize, right: usize) -> Result<usize, HistoryStepError> {
    left.checked_mul(right)
        .ok_or(HistoryStepError::WireEncoding)
}

#[derive(Clone, Debug)]
struct BaseFoldWireShape {
    round_messages: usize,
    round_commitments: usize,
    final_codeword: usize,
    plaintext_tail: usize,
    queries: usize,
    initial_leaf: usize,
    initial_path: usize,
    post_row_batch_leaf: usize,
    post_row_batch_path: usize,
    epoch_shapes: Vec<(usize, usize)>,
}

impl BaseFoldWireShape {
    fn path_depths(&self) -> Vec<usize> {
        let mut depths = vec![self.initial_path, self.post_row_batch_path];
        depths.extend(self.epoch_shapes.iter().map(|(_, depth)| *depth));
        depths
    }

    fn full_path_bytes(&self) -> Result<usize, HistoryStepError> {
        let depth_sum = self.path_depths().into_iter().try_fold(0, add)?;
        mul(mul(self.queries, depth_sum)?, HASH_BYTES)
    }

    fn derive(params: &PcsParams) -> Result<Self, HistoryStepError> {
        let log_msg_len = params
            .m
            .checked_sub(LOG_PACKING)
            .ok_or(HistoryStepError::WireEncoding)?;
        let log_dim = log_msg_len
            .checked_sub(params.log_batch_size)
            .ok_or(HistoryStepError::WireEncoding)?;
        let k_code = log_dim
            .checked_add(params.log_inv_rate)
            .ok_or(HistoryStepError::WireEncoding)?;
        if k_code >= usize::BITS as usize
            || params.log_batch_size >= usize::BITS as usize
            || params.log_inv_rate >= usize::BITS as usize
        {
            return Err(HistoryStepError::WireEncoding);
        }
        let arities = compute_fri_arities(log_dim);
        let (round_commitments, tail_layout) = fri_commit_layout(k_code, &arities);
        let first_arity = arities.first().copied();
        let mut consumed = first_arity.unwrap_or(0);
        let mut epoch_shapes = Vec::with_capacity(round_commitments);
        for index in 0..round_commitments {
            let arity = *arities
                .get(index + 1)
                .ok_or(HistoryStepError::WireEncoding)?;
            consumed = consumed
                .checked_add(arity)
                .ok_or(HistoryStepError::WireEncoding)?;
            let depth = k_code
                .checked_sub(consumed)
                .ok_or(HistoryStepError::WireEncoding)?;
            epoch_shapes.push((1usize << arity, depth));
        }
        Ok(Self {
            round_messages: log_msg_len,
            round_commitments,
            final_codeword: 1usize << params.log_inv_rate,
            plaintext_tail: tail_layout.map_or(0, |(len, _)| len),
            queries: default_fri_queries(params.log_dim(), params.log_inv_rate),
            initial_leaf: 1usize << params.log_batch_size,
            initial_path: k_code,
            post_row_batch_leaf: first_arity.map_or(0, |arity| 1usize << arity),
            post_row_batch_path: first_arity.map_or(0, |arity| k_code - arity),
            epoch_shapes,
        })
    }

    fn query_encoded_len(&self) -> Result<usize, HistoryStepError> {
        let mut query_len = 8usize;
        query_len = add(query_len, mul(self.initial_leaf, F128_BYTES)?)?;
        query_len = add(query_len, mul(self.initial_path, HASH_BYTES)?)?;
        query_len = add(query_len, mul(self.post_row_batch_leaf, F256_BYTES)?)?;
        query_len = add(query_len, mul(self.post_row_batch_path, HASH_BYTES)?)?;
        for (leaf, path) in &self.epoch_shapes {
            query_len = add(query_len, mul(*leaf, F256_BYTES)?)?;
            query_len = add(query_len, mul(*path, HASH_BYTES)?)?;
        }
        Ok(query_len)
    }

    fn encoded_len(&self) -> Result<usize, HistoryStepError> {
        let mut len = mul(self.round_messages, 2 * F256_BYTES)?;
        len = add(len, HASH_BYTES)?;
        len = add(len, mul(self.round_commitments, HASH_BYTES)?)?;
        len = add(len, 2 * F256_BYTES)?;
        len = add(len, mul(self.final_codeword, F256_BYTES)?)?;
        len = add(len, mul(self.plaintext_tail, F256_BYTES)?)?;
        len = add(len, 8)?;
        add(len, mul(self.queries, self.query_encoded_len()?)?)
    }
}

pub(super) fn field_proof_len(
    shape: FieldShape,
    params: &PcsParams,
) -> Result<usize, HistoryStepError> {
    if shape.k_skip >= usize::BITS as usize || shape.m < shape.k_skip || shape.k_log < shape.k_skip
    {
        return Err(HistoryStepError::WireEncoding);
    }
    let skip = 1usize << shape.k_skip;
    let zerocheck_lanes = add(add(mul(skip, 2)?, mul(shape.m - shape.k_skip, 2)?)?, 3)?;
    let lincheck_lanes = add(mul(shape.k_log - shape.k_skip, 2)?, skip)?;
    let basefold = BaseFoldWireShape::derive(params)?.encoded_len()?;
    add(
        mul(add(zerocheck_lanes, lincheck_lanes)?, F256_BYTES)?,
        basefold,
    )
}

fn terminal_len_for_class(
    runtime: &HistoryStepRuntime,
    class: CanonicalHistoryStepClassId,
) -> Result<usize, HistoryStepError> {
    let entry = runtime.bank().entry(class);
    let mut len = PREFIX_BYTES;
    len = add(len, HASH_BYTES)?;
    len = add(len, mul(runtime.bank().spec().io_len, F128_BYTES)?)?;
    len = add(len, field_proof_len(entry.shape(), entry.pcs_params())?)?;
    len = add(
        len,
        canonical_joint_c1_region_sidecar_len(
            runtime.parent_recursion_vk(),
            runtime
                .direct_block_vk(class.current_slot())
                .ok_or(HistoryStepError::RuntimeBlockVk(class.current_slot()))?,
            entry.shape().m,
        )?,
    )?;
    Ok(len)
}

pub fn history_step_terminal_max_wire_bytes(
    runtime: &HistoryStepRuntime,
) -> Result<usize, HistoryStepError> {
    (0..HISTORY_STEP_CLASS_COUNT).try_fold(0usize, |maximum, index| {
        let class =
            CanonicalHistoryStepClassId::from_index(index).ok_or(HistoryStepError::InvalidClass)?;
        Ok(maximum.max(terminal_len_for_class(runtime, class)?))
    })
}

fn put_f128(out: &mut Vec<u8>, value: F128) {
    out.extend_from_slice(&value.lo.to_le_bytes());
    out.extend_from_slice(&value.hi.to_le_bytes());
}

fn put_f256(out: &mut Vec<u8>, value: F256) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_hash(out: &mut Vec<u8>, value: &[u8; HASH_BYTES]) {
    out.extend_from_slice(value);
}

pub(super) struct Reader<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Reader<'a> {
    pub(super) fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    pub(super) fn take(&mut self, count: usize) -> Result<&'a [u8], HistoryStepError> {
        let end = add(self.position, count)?;
        let bytes = self
            .bytes
            .get(self.position..end)
            .ok_or(HistoryStepError::WireEncoding)?;
        self.position = end;
        Ok(bytes)
    }

    fn u8(&mut self) -> Result<u8, HistoryStepError> {
        Ok(*self
            .take(1)?
            .first()
            .ok_or(HistoryStepError::WireEncoding)?)
    }

    fn u64(&mut self) -> Result<u64, HistoryStepError> {
        Ok(u64::from_le_bytes(
            self.take(8)?
                .try_into()
                .map_err(|_| HistoryStepError::WireEncoding)?,
        ))
    }

    fn f128(&mut self) -> Result<F128, HistoryStepError> {
        let bytes = self.take(F128_BYTES)?;
        Ok(F128 {
            lo: u64::from_le_bytes(
                bytes[..8]
                    .try_into()
                    .map_err(|_| HistoryStepError::WireEncoding)?,
            ),
            hi: u64::from_le_bytes(
                bytes[8..]
                    .try_into()
                    .map_err(|_| HistoryStepError::WireEncoding)?,
            ),
        })
    }

    fn f256(&mut self) -> Result<F256, HistoryStepError> {
        let bytes: [u8; F256_BYTES] = self
            .take(F256_BYTES)?
            .try_into()
            .map_err(|_| HistoryStepError::WireEncoding)?;
        Ok(F256::from_le_bytes(bytes))
    }

    pub(super) fn hash(&mut self) -> Result<[u8; HASH_BYTES], HistoryStepError> {
        self.take(HASH_BYTES)?
            .try_into()
            .map_err(|_| HistoryStepError::WireEncoding)
    }

    pub(super) fn finish(self) -> Result<(), HistoryStepError> {
        if self.position == self.bytes.len() {
            Ok(())
        } else {
            Err(HistoryStepError::WireEncoding)
        }
    }
}

pub(super) fn encode_f128_vec(
    out: &mut Vec<u8>,
    values: &[F128],
    expected: usize,
) -> Result<(), HistoryStepError> {
    if values.len() != expected {
        return Err(HistoryStepError::WireEncoding);
    }
    for value in values {
        put_f128(out, *value);
    }
    Ok(())
}

pub(super) fn decode_f128_vec(
    reader: &mut Reader<'_>,
    count: usize,
) -> Result<Vec<F128>, HistoryStepError> {
    let mut values = Vec::with_capacity(count);
    for _ in 0..count {
        values.push(reader.f128()?);
    }
    Ok(values)
}

fn encode_f256_pair_vec(
    out: &mut Vec<u8>,
    values: &[(F256, F256)],
    expected: usize,
) -> Result<(), HistoryStepError> {
    if values.len() != expected {
        return Err(HistoryStepError::WireEncoding);
    }
    for &(left, right) in values {
        put_f256(out, left);
        put_f256(out, right);
    }
    Ok(())
}

fn decode_f256_pair_vec(
    reader: &mut Reader<'_>,
    count: usize,
) -> Result<Vec<(F256, F256)>, HistoryStepError> {
    let mut values = Vec::with_capacity(count);
    for _ in 0..count {
        values.push((reader.f256()?, reader.f256()?));
    }
    Ok(values)
}

fn encode_f256_vec(
    out: &mut Vec<u8>,
    values: &[F256],
    expected: usize,
) -> Result<(), HistoryStepError> {
    if values.len() != expected {
        return Err(HistoryStepError::WireEncoding);
    }
    for &value in values {
        put_f256(out, value);
    }
    Ok(())
}

fn decode_f256_vec(reader: &mut Reader<'_>, count: usize) -> Result<Vec<F256>, HistoryStepError> {
    let mut values = Vec::with_capacity(count);
    for _ in 0..count {
        values.push(reader.f256()?);
    }
    Ok(values)
}

fn encode_hash_vec(
    out: &mut Vec<u8>,
    values: &[[u8; HASH_BYTES]],
    expected: usize,
) -> Result<(), HistoryStepError> {
    if values.len() != expected {
        return Err(HistoryStepError::WireEncoding);
    }
    for value in values {
        put_hash(out, value);
    }
    Ok(())
}

fn decode_hash_vec(
    reader: &mut Reader<'_>,
    count: usize,
) -> Result<Vec<[u8; HASH_BYTES]>, HistoryStepError> {
    let mut values = Vec::with_capacity(count);
    for _ in 0..count {
        values.push(reader.hash()?);
    }
    Ok(values)
}

pub(super) fn encode_field_proof(
    out: &mut Vec<u8>,
    proof: &C1FieldR1csProof,
    shape: FieldShape,
    params: &PcsParams,
    shared: bool,
) -> Result<(), HistoryStepError> {
    let skip = 1usize << shape.k_skip;
    encode_f256_vec(out, &proof.zerocheck.round1_ab, skip)?;
    encode_f256_vec(out, &proof.zerocheck.round1_c, skip)?;
    encode_f256_pair_vec(
        out,
        &proof.zerocheck.multilinear_rounds,
        shape.m - shape.k_skip,
    )?;
    put_f256(out, proof.zerocheck.final_a_eval);
    put_f256(out, proof.zerocheck.final_b_eval);
    put_f256(out, proof.zerocheck.final_c_eval);
    encode_f256_pair_vec(out, &proof.lincheck.rounds, shape.k_log - shape.k_skip)?;
    encode_f256_vec(out, &proof.lincheck.z_partial, skip)?;
    encode_basefold(
        out,
        &proof.pcs_open,
        &BaseFoldWireShape::derive(params)?,
        shared,
    )
}

pub(super) fn decode_field_proof(
    reader: &mut Reader<'_>,
    shape: FieldShape,
    params: &PcsParams,
    shared: bool,
) -> Result<C1FieldR1csProof, HistoryStepError> {
    let skip = 1usize << shape.k_skip;
    let zerocheck = noid_ivc_core::zerocheck::field_c1::C1ZerocheckProof {
        round1_ab: decode_f256_vec(reader, skip)?,
        round1_c: decode_f256_vec(reader, skip)?,
        multilinear_rounds: decode_f256_pair_vec(reader, shape.m - shape.k_skip)?,
        final_a_eval: reader.f256()?,
        final_b_eval: reader.f256()?,
        final_c_eval: reader.f256()?,
    };
    let lincheck = noid_ivc_core::lincheck::c1::C1LincheckProof {
        rounds: decode_f256_pair_vec(reader, shape.k_log - shape.k_skip)?,
        z_partial: decode_f256_vec(reader, skip)?,
    };
    let pcs_open = decode_basefold(reader, &BaseFoldWireShape::derive(params)?, shared)?;
    Ok(C1FieldR1csProof {
        zerocheck,
        lincheck,
        pcs_open,
    })
}

fn encode_query(
    out: &mut Vec<u8>,
    query: &C1QueryOpening,
    shape: &BaseFoldWireShape,
    shared: bool,
) -> Result<(), HistoryStepError> {
    let position = u64::try_from(query.position).map_err(|_| HistoryStepError::WireEncoding)?;
    out.extend_from_slice(&position.to_le_bytes());
    encode_f128_vec(out, &query.initial_leaf, shape.initial_leaf)?;
    if !shared {
        encode_hash_vec(out, &query.initial_path, shape.initial_path)?;
    }
    encode_f256_vec(out, &query.post_row_batch_leaf, shape.post_row_batch_leaf)?;
    if !shared {
        encode_hash_vec(out, &query.post_row_batch_path, shape.post_row_batch_path)?;
    }
    if query.epoch_leaves.len() != shape.epoch_shapes.len()
        || query.epoch_paths.len() != shape.epoch_shapes.len()
    {
        return Err(HistoryStepError::WireEncoding);
    }
    for (index, (leaf, path)) in shape.epoch_shapes.iter().enumerate() {
        encode_f256_vec(out, &query.epoch_leaves[index], *leaf)?;
        if !shared {
            encode_hash_vec(out, &query.epoch_paths[index], *path)?;
        }
    }
    Ok(())
}

fn decode_query(
    reader: &mut Reader<'_>,
    shape: &BaseFoldWireShape,
    shared: bool,
) -> Result<C1QueryOpening, HistoryStepError> {
    let position = usize::try_from(reader.u64()?).map_err(|_| HistoryStepError::WireEncoding)?;
    if shared && position >= (1usize << shape.initial_path) {
        return Err(HistoryStepError::WireEncoding);
    }
    let initial_leaf = decode_f128_vec(reader, shape.initial_leaf)?;
    let initial_path = decode_hash_vec(reader, if shared { 0 } else { shape.initial_path })?;
    let post_row_batch_leaf = decode_f256_vec(reader, shape.post_row_batch_leaf)?;
    let post_row_batch_path =
        decode_hash_vec(reader, if shared { 0 } else { shape.post_row_batch_path })?;
    let mut epoch_leaves = Vec::with_capacity(shape.epoch_shapes.len());
    let mut epoch_paths = Vec::with_capacity(shape.epoch_shapes.len());
    for (leaf, path) in &shape.epoch_shapes {
        epoch_leaves.push(decode_f256_vec(reader, *leaf)?);
        epoch_paths.push(decode_hash_vec(reader, if shared { 0 } else { *path })?);
    }
    Ok(C1QueryOpening {
        position,
        initial_leaf,
        initial_path,
        post_row_batch_leaf,
        post_row_batch_path,
        epoch_leaves,
        epoch_paths,
    })
}

fn encode_basefold(
    out: &mut Vec<u8>,
    proof: &C1BaseFoldProof,
    shape: &BaseFoldWireShape,
    shared: bool,
) -> Result<(), HistoryStepError> {
    if proof.round_messages.len() != shape.round_messages
        || proof.round_commitments.len() != shape.round_commitments
        || proof.queries.len() != shape.queries
    {
        return Err(HistoryStepError::WireEncoding);
    }
    for message in &proof.round_messages {
        put_f256(out, message.u_0);
        put_f256(out, message.u_2);
    }
    put_hash(out, &proof.post_row_batch_commit.root);
    for commitment in &proof.round_commitments {
        put_hash(out, &commitment.root);
    }
    put_f256(out, proof.final_a);
    put_f256(out, proof.final_b);
    encode_f256_vec(out, &proof.final_codeword, shape.final_codeword)?;
    encode_f256_vec(out, &proof.plaintext_tail, shape.plaintext_tail)?;
    out.extend_from_slice(&proof.pow_nonce.to_le_bytes());
    for query in &proof.queries {
        encode_query(out, query, shape, shared)?;
    }
    if shared {
        encode_shared_paths(out, &proof.queries, shape)?;
    }
    Ok(())
}

fn decode_basefold(
    reader: &mut Reader<'_>,
    shape: &BaseFoldWireShape,
    shared: bool,
) -> Result<C1BaseFoldProof, HistoryStepError> {
    let mut round_messages = Vec::with_capacity(shape.round_messages);
    for _ in 0..shape.round_messages {
        round_messages.push(C1RoundMessage {
            u_0: reader.f256()?,
            u_2: reader.f256()?,
        });
    }
    let post_row_batch_commit = RoundCommitment {
        root: reader.hash()?,
    };
    let mut round_commitments = Vec::with_capacity(shape.round_commitments);
    for _ in 0..shape.round_commitments {
        round_commitments.push(RoundCommitment {
            root: reader.hash()?,
        });
    }
    let final_a = reader.f256()?;
    let final_b = reader.f256()?;
    let final_codeword = decode_f256_vec(reader, shape.final_codeword)?;
    let plaintext_tail = decode_f256_vec(reader, shape.plaintext_tail)?;
    let pow_nonce = reader.u64()?;
    let mut queries = Vec::with_capacity(shape.queries);
    for _ in 0..shape.queries {
        queries.push(decode_query(reader, shape, shared)?);
    }
    if shared {
        decode_shared_paths(reader, &mut queries, shape)?;
    }
    Ok(C1BaseFoldProof {
        round_messages,
        post_row_batch_commit,
        round_commitments,
        final_a,
        final_b,
        final_codeword,
        plaintext_tail,
        pow_nonce,
        queries,
    })
}

fn positions_for_tree(
    queries: &[C1QueryOpening],
    initial_depth: usize,
    depth: usize,
) -> Result<Vec<usize>, HistoryStepError> {
    let shift = initial_depth
        .checked_sub(depth)
        .ok_or(HistoryStepError::WireEncoding)?;
    if queries
        .iter()
        .any(|q| q.position >= (1usize << initial_depth))
    {
        return Err(HistoryStepError::WireEncoding);
    }
    Ok(queries.iter().map(|q| q.position >> shift).collect())
}

fn encode_shared_paths(
    out: &mut Vec<u8>,
    queries: &[C1QueryOpening],
    shape: &BaseFoldWireShape,
) -> Result<(), HistoryStepError> {
    for (tree, depth) in shape.path_depths().into_iter().enumerate() {
        let positions = positions_for_tree(queries, shape.initial_path, depth)?;
        let paths: Vec<&[[u8; HASH_BYTES]]> = queries
            .iter()
            .map(|q| match tree {
                0 => q.initial_path.as_slice(),
                1 => q.post_row_batch_path.as_slice(),
                _ => q.epoch_paths[tree - 2].as_slice(),
            })
            .collect();
        shared_paths::encode(out, &positions, depth, &paths)?;
    }
    Ok(())
}

fn decode_shared_paths(
    reader: &mut Reader<'_>,
    queries: &mut [C1QueryOpening],
    shape: &BaseFoldWireShape,
) -> Result<(), HistoryStepError> {
    for (tree, depth) in shape.path_depths().into_iter().enumerate() {
        let positions = positions_for_tree(queries, shape.initial_path, depth)?;
        let paths = shared_paths::decode(reader, &positions, depth)?;
        for (q, path) in queries.iter_mut().zip(paths) {
            match tree {
                0 => q.initial_path = path,
                1 => q.post_row_batch_path = path,
                _ => q.epoch_paths[tree - 2] = path,
            }
        }
    }
    Ok(())
}

pub fn encode_history_step_terminal(
    runtime: &HistoryStepRuntime,
    terminal: &HistoryStepTerminal,
) -> Result<Vec<u8>, HistoryStepError> {
    encode_terminal_in_format(runtime, terminal, terminal.wire_version())
}

fn encode_terminal_in_format(
    runtime: &HistoryStepRuntime,
    terminal: &HistoryStepTerminal,
    version: u8,
) -> Result<Vec<u8>, HistoryStepError> {
    if !matches!(
        version,
        HISTORY_STEP_WIRE_VERSION | HISTORY_STEP_TERMINAL_SHARED_PATH_VERSION
    ) {
        return Err(HistoryStepError::WireVersion);
    }
    validate_terminal_metadata(runtime, terminal, None)?;
    let entry = runtime.bank().entry(terminal.class_id);
    let expected = terminal_len_for_class(runtime, terminal.class_id)?;
    let shared = version == HISTORY_STEP_TERMINAL_SHARED_PATH_VERSION;
    let block_vk = runtime
        .direct_block_vk(terminal.class_id.current_slot())
        .ok_or(HistoryStepError::RuntimeBlockVk(
            terminal.class_id.current_slot(),
        ))?;
    let sidecar = encode_joint_c1_region_sidecar_canonical(
        runtime.parent_recursion_vk(),
        block_vk,
        entry.shape().m,
        &terminal.proof.sidecar,
    )?;
    let mut out = Vec::with_capacity(expected);
    out.push(version);
    out.extend_from_slice(&terminal.height.to_le_bytes());
    out.extend_from_slice(&terminal.semantic_id);
    out.push(terminal.class_id.wire_id());
    put_hash(&mut out, &terminal.proof.commitment.root);
    encode_f128_vec(&mut out, &terminal.proof.io, runtime.bank().spec().io_len)?;
    encode_field_proof(
        &mut out,
        &terminal.proof.field_proof,
        entry.shape(),
        entry.pcs_params(),
        shared,
    )?;
    out.extend_from_slice(&sidecar);
    if (!shared && out.len() != expected) || (shared && out.len() > expected) {
        return Err(HistoryStepError::WireLength {
            expected,
            actual: out.len(),
        });
    }
    Ok(out)
}

pub fn decode_history_step_terminal(
    runtime: &HistoryStepRuntime,
    bytes: &[u8],
) -> Result<HistoryStepTerminal, HistoryStepError> {
    decode_terminal_with_activation(
        runtime,
        bytes,
        noid_chain::consensus::params::V1_1_ACTIVATION_HEIGHT,
    )
}

// Keep schedule injection private: diagnostics return measurements, never an
// alternate accepted-terminal capability for a caller-selected fork height.
fn decode_terminal_with_activation(
    runtime: &HistoryStepRuntime,
    bytes: &[u8],
    activation: Option<u64>,
) -> Result<HistoryStepTerminal, HistoryStepError> {
    if bytes.len() < PREFIX_BYTES {
        return Err(HistoryStepError::WireLength {
            expected: PREFIX_BYTES,
            actual: bytes.len(),
        });
    }
    let height = u64::from_le_bytes(bytes[1..9].try_into().expect("bounded prefix"));
    decode_terminal_in_format(
        runtime,
        bytes,
        history_step_terminal_wire_version_with_activation(height, activation),
    )
}

// Private format decoding is also exercised by the lossless-codec audit below.
// Only the height-gated public entry point is used by node/consensus admission.
fn decode_terminal_in_format(
    runtime: &HistoryStepRuntime,
    bytes: &[u8],
    expected_version: u8,
) -> Result<HistoryStepTerminal, HistoryStepError> {
    if bytes.len() < PREFIX_BYTES {
        return Err(HistoryStepError::WireLength {
            expected: PREFIX_BYTES,
            actual: bytes.len(),
        });
    }
    let mut prefix = Reader::new(&bytes[..PREFIX_BYTES]);
    let version = prefix.u8()?;
    let height = prefix.u64()?;
    if version != expected_version
        || !matches!(
            version,
            HISTORY_STEP_WIRE_VERSION | HISTORY_STEP_TERMINAL_SHARED_PATH_VERSION
        )
    {
        return Err(HistoryStepError::WireVersion);
    }
    let shared = version == HISTORY_STEP_TERMINAL_SHARED_PATH_VERSION;
    let semantic_id = prefix.hash()?;
    let class_id = CanonicalHistoryStepClassId::from_index(prefix.u8()? as usize)
        .ok_or(HistoryStepError::InvalidClass)?;
    prefix.finish()?;
    let expected = terminal_len_for_class(runtime, class_id)?;
    let entry = runtime.bank().entry(class_id);
    let minimum = expected
        .checked_sub(BaseFoldWireShape::derive(entry.pcs_params())?.full_path_bytes()?)
        .ok_or(HistoryStepError::WireEncoding)?;
    let allowed_length = if shared {
        // Both input and expanded allocations are bounded before decoding.
        // The expanded proof has the exact original class-derived shape.
        expected <= noid_chain::consensus::wire_limits::MAX_HISTORY_STEP_TERMINAL_TRANSPORT_BYTES
            && (minimum..=expected).contains(&bytes.len())
            && bytes.len()
                <= noid_chain::consensus::wire_limits::V1_1_MAX_HISTORY_STEP_TERMINAL_BYTES
    } else {
        bytes.len() == expected
    };
    if !allowed_length {
        return Err(HistoryStepError::WireLength {
            expected,
            actual: bytes.len(),
        });
    }

    // All allocations are class-bounded. Shared dictionaries have at most
    // q * depth entries and their exact counts come from bounded positions.
    let mut reader = Reader::new(&bytes[PREFIX_BYTES..]);
    let commitment_root = reader.hash()?;
    let io = decode_f128_vec(&mut reader, runtime.bank().spec().io_len)?;
    let field_proof = decode_field_proof(&mut reader, entry.shape(), entry.pcs_params(), shared)?;
    let block_vk = runtime
        .direct_block_vk(class_id.current_slot())
        .ok_or(HistoryStepError::RuntimeBlockVk(class_id.current_slot()))?;
    let sidecar_len = canonical_joint_c1_region_sidecar_len(
        runtime.parent_recursion_vk(),
        block_vk,
        entry.shape().m,
    )?;
    let sidecar = decode_joint_c1_region_sidecar_canonical(
        runtime.parent_recursion_vk(),
        block_vk,
        entry.shape().m,
        reader.take(sidecar_len)?,
    )?;
    reader.finish()?;
    let proof = HistoryStepProof {
        field_proof,
        commitment: Commitment {
            root: commitment_root,
            params: entry.pcs_params().clone(),
        },
        io,
        sidecar,
    };
    let accumulator = history_step_bank_block_accumulator(runtime.bank(), &proof.io)?;
    let terminal = HistoryStepTerminal {
        height,
        semantic_id,
        class_id,
        accumulator,
        proof,
    };
    validate_terminal_metadata(runtime, &terminal, None)?;
    Ok(terminal)
}

/// Diagnostic measurements, not a decoded or accepted terminal capability.
#[derive(Debug)]
pub struct HistoryStepWireAudit {
    pub legacy_bytes: usize,
    pub shared_bytes: usize,
    pub fork_format_checks: usize,
    pub malformed_inputs_rejected: usize,
    /// Warm, alternating-order samples. Destruction of the returned object is
    /// excluded, as it is from an ordinary encode/decode function call.
    pub legacy_encode_ns: Vec<u128>,
    pub shared_encode_ns: Vec<u128>,
    pub legacy_decode_ns: Vec<u128>,
    pub shared_decode_ns: Vec<u128>,
}

/// Check both byte representations of a native terminal without changing any
/// activation rule. Returns lengths and codec timings only.
/// This diagnostic does not return a decoded/accepted terminal capability and
/// cannot be used to admit a post-fork encoding before activation.
pub fn audit_history_step_terminal_encodings(
    runtime: &HistoryStepRuntime,
    terminal: &HistoryStepTerminal,
    expected_header: &BlockHeader,
    epoch_anchor_header: &BlockHeader,
) -> Result<HistoryStepWireAudit, HistoryStepError> {
    let legacy = encode_terminal_in_format(runtime, terminal, HISTORY_STEP_WIRE_VERSION)?;
    let shared =
        encode_terminal_in_format(runtime, terminal, HISTORY_STEP_TERMINAL_SHARED_PATH_VERSION)?;
    let mut fork_format_checks = 0;
    let mut malformed_inputs_rejected = 0;
    for (version, bytes) in [
        (HISTORY_STEP_WIRE_VERSION, &legacy),
        (HISTORY_STEP_TERMINAL_SHARED_PATH_VERSION, &shared),
    ] {
        let restored = decode_terminal_in_format(runtime, bytes, version)?;
        if encode_terminal_in_format(runtime, &restored, HISTORY_STEP_WIRE_VERSION)? != legacy
            || encode_terminal_in_format(runtime, &restored, version)? != *bytes
        {
            return Err(HistoryStepError::WireEncoding);
        }
        // Check the very same native verifier on each recovered proof, not
        // only byte equality with the previously verified original terminal.
        let _verified =
            verify_history_step_terminal(runtime, &restored, expected_header, epoch_anchor_header)?;

        // Simulate the terminal just before, at, and after a fork without
        // changing the node's actual activation constant or proof relation.
        for activation in [
            None,
            Some(terminal.height),
            terminal.height.checked_add(1),
            terminal.height.checked_sub(1),
        ] {
            let allowed = version
                == history_step_terminal_wire_version_with_activation(terminal.height, activation);
            match decode_terminal_with_activation(runtime, bytes, activation) {
                Ok(decoded) if allowed => {
                    if encode_terminal_in_format(runtime, &decoded, HISTORY_STEP_WIRE_VERSION)?
                        != legacy
                    {
                        return Err(HistoryStepError::WireEncoding);
                    }
                }
                Err(HistoryStepError::WireVersion) if !allowed => {}
                _ => return Err(HistoryStepError::WireEncoding),
            }
            fork_format_checks += 1;
        }

        for length in [0, 1, 8, 9, PREFIX_BYTES - 1, PREFIX_BYTES, bytes.len() - 1] {
            if decode_terminal_in_format(runtime, &bytes[..length], version).is_ok() {
                return Err(HistoryStepError::WireEncoding);
            }
            malformed_inputs_rejected += 1;
        }
        let mut malformed = bytes.to_vec();
        malformed.push(0);
        if decode_terminal_in_format(runtime, &malformed, version).is_ok() {
            return Err(HistoryStepError::WireEncoding);
        }
        malformed_inputs_rejected += 1;
        malformed.truncate(bytes.len());
        for class in [HISTORY_STEP_CLASS_COUNT as u8, u8::MAX] {
            malformed[41] = class;
            if decode_terminal_in_format(runtime, &malformed, version).is_ok() {
                return Err(HistoryStepError::WireEncoding);
            }
            malformed_inputs_rejected += 1;
        }
        malformed[41] = bytes[41];
        for invalid_version in 0..=u8::MAX {
            if matches!(
                invalid_version,
                HISTORY_STEP_WIRE_VERSION | HISTORY_STEP_TERMINAL_SHARED_PATH_VERSION
            ) {
                continue;
            }
            malformed[0] = invalid_version;
            if decode_terminal_in_format(runtime, &malformed, invalid_version).is_ok() {
                return Err(HistoryStepError::WireEncoding);
            }
            malformed_inputs_rejected += 1;
        }
        malformed[0] = version;
        // A damaged commitment may parse, but it must not pass native proof
        // verification. No codec success can substitute for that verification.
        malformed[PREFIX_BYTES] ^= 1;
        if let Ok(damaged) = decode_terminal_in_format(runtime, &malformed, version) {
            if verify_history_step_terminal(runtime, &damaged, expected_header, epoch_anchor_header)
                .is_ok()
            {
                return Err(HistoryStepError::WireEncoding);
            }
        }
        malformed_inputs_rejected += 1;
    }
    const WARMUP: usize = 4;
    const SAMPLES: usize = 32;
    let mut audit = HistoryStepWireAudit {
        legacy_bytes: legacy.len(),
        shared_bytes: shared.len(),
        fork_format_checks,
        malformed_inputs_rejected,
        legacy_encode_ns: Vec::with_capacity(SAMPLES),
        shared_encode_ns: Vec::with_capacity(SAMPLES),
        legacy_decode_ns: Vec::with_capacity(SAMPLES),
        shared_decode_ns: Vec::with_capacity(SAMPLES),
    };
    for sample in 0..WARMUP + SAMPLES {
        // Alternate the first format to avoid giving one format a fixed cache
        // or frequency-ramp advantage. Equality checks are outside the timers.
        let mut formats = [
            (HISTORY_STEP_WIRE_VERSION, &legacy),
            (HISTORY_STEP_TERMINAL_SHARED_PATH_VERSION, &shared),
        ];
        if sample % 2 != 0 {
            formats.reverse();
        }
        for (version, bytes) in formats {
            let started = std::time::Instant::now();
            let encoded = encode_terminal_in_format(
                std::hint::black_box(runtime),
                std::hint::black_box(terminal),
                version,
            )?;
            let encode_ns = started.elapsed().as_nanos();
            if encoded != *bytes {
                return Err(HistoryStepError::WireEncoding);
            }
            let started = std::time::Instant::now();
            let restored = decode_terminal_in_format(
                std::hint::black_box(runtime),
                std::hint::black_box(bytes),
                version,
            )?;
            std::hint::black_box(&restored);
            let decode_ns = started.elapsed().as_nanos();
            if sample >= WARMUP {
                if version == HISTORY_STEP_WIRE_VERSION {
                    audit.legacy_encode_ns.push(encode_ns);
                    audit.legacy_decode_ns.push(decode_ns);
                } else {
                    audit.shared_encode_ns.push(encode_ns);
                    audit.shared_decode_ns.push(decode_ns);
                }
            }
        }
    }
    Ok(audit)
}

pub fn decode_verify_history_step_terminal(
    runtime: &HistoryStepRuntime,
    bytes: &[u8],
    expected_header: &BlockHeader,
    epoch_anchor_header: &BlockHeader,
) -> Result<AcceptedHistoryStepTerminal, HistoryStepError> {
    let terminal = decode_history_step_terminal(runtime, bytes)?;
    verify_history_step_terminal(runtime, &terminal, expected_header, epoch_anchor_header)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::history_step_bank::{
        canonical_history_step_pcs_params, HISTORY_STEP_FRI_QUERIES,
    };

    // Codec fixtures have consistent shared-node labels, but are not complete
    // valid FRI proofs. Real Merkle paths are tested in shared_paths.rs.
    fn codec_fixture(shape: &BaseFoldWireShape) -> C1BaseFoldProof {
        let depths = shape.path_depths();
        let queries = (0..shape.queries)
            .map(|i| {
                let i = if i + 1 == shape.queries { 0 } else { i };
                let position = (i * 104_729 ^ (i >> 2)) & ((1usize << shape.initial_path) - 1);
                let mut paths: Vec<Vec<[u8; 32]>> = depths
                    .iter()
                    .enumerate()
                    .map(|(tree, &depth)| {
                        let p = position >> (shape.initial_path - depth);
                        (0..depth)
                            .map(|level| {
                                let mut hash = [0; 32];
                                hash[..8].copy_from_slice(&(level as u64).to_le_bytes());
                                hash[8..16]
                                    .copy_from_slice(&(((p >> level) ^ 1) as u64).to_le_bytes());
                                hash[16..24].copy_from_slice(&(tree as u64).to_le_bytes());
                                hash
                            })
                            .collect()
                    })
                    .collect();
                let initial_path = std::mem::take(&mut paths[0]);
                let post_row_batch_path = std::mem::take(&mut paths[1]);
                C1QueryOpening {
                    position,
                    initial_leaf: vec![F128::ZERO; shape.initial_leaf],
                    initial_path,
                    post_row_batch_leaf: vec![F256::ZERO; shape.post_row_batch_leaf],
                    post_row_batch_path,
                    epoch_leaves: shape
                        .epoch_shapes
                        .iter()
                        .map(|(n, _)| vec![F256::ZERO; *n])
                        .collect(),
                    epoch_paths: paths.into_iter().skip(2).collect(),
                }
            })
            .collect();
        C1BaseFoldProof {
            round_messages: vec![
                C1RoundMessage {
                    u_0: F256::ZERO,
                    u_2: F256::ZERO
                };
                shape.round_messages
            ],
            post_row_batch_commit: RoundCommitment { root: [1; 32] },
            round_commitments: vec![RoundCommitment { root: [2; 32] }; shape.round_commitments],
            final_a: F256::ZERO,
            final_b: F256::ZERO,
            final_codeword: vec![F256::ZERO; shape.final_codeword],
            plaintext_tail: vec![F256::ZERO; shape.plaintext_tail],
            pow_nonce: 0x1234,
            queries,
        }
    }

    #[test]
    fn shared_paths_restore_every_legacy_basefold_byte_for_both_classes() {
        for index in 0..HISTORY_STEP_CLASS_COUNT {
            let class = CanonicalHistoryStepClassId::from_index(index).unwrap();
            let shape =
                BaseFoldWireShape::derive(&canonical_history_step_pcs_params(class)).unwrap();
            let proof = codec_fixture(&shape);
            let mut full = Vec::new();
            encode_basefold(&mut full, &proof, &shape, false).unwrap();
            assert_eq!(full.len(), shape.encoded_len().unwrap());
            let mut shared = Vec::new();
            encode_basefold(&mut shared, &proof, &shape, true).unwrap();
            assert!(shared.len() < full.len());
            assert!(shared.len() >= full.len() - shape.full_path_bytes().unwrap());
            let mut reader = Reader::new(&shared);
            let restored = decode_basefold(&mut reader, &shape, true).unwrap();
            reader.finish().unwrap();
            assert_eq!(proof, restored);
            let mut roundtrip = Vec::new();
            encode_basefold(&mut roundtrip, &restored, &shape, false).unwrap();
            assert_eq!(full, roundtrip);
            roundtrip.clear();
            encode_basefold(&mut roundtrip, &restored, &shape, true).unwrap();
            assert_eq!(shared, roundtrip);
        }
    }

    #[test]
    fn shared_basefold_rejects_bad_positions_truncation_and_conflicting_paths() {
        let class = CanonicalHistoryStepClassId::from_index(0).unwrap();
        let shape = BaseFoldWireShape::derive(&canonical_history_step_pcs_params(class)).unwrap();
        let mut proof = codec_fixture(&shape);
        let mut encoded = Vec::new();
        encode_basefold(&mut encoded, &proof, &shape, true).unwrap();
        for cut in [0, 1, 63, encoded.len() / 2, encoded.len() - 1] {
            assert!(decode_basefold(&mut Reader::new(&encoded[..cut]), &shape, true).is_err());
        }
        let prefix_bytes =
            shape.encoded_len().unwrap() - shape.queries * shape.query_encoded_len().unwrap();
        encoded[prefix_bytes..prefix_bytes + 8]
            .copy_from_slice(&(1u64 << shape.initial_path).to_le_bytes());
        assert!(decode_basefold(&mut Reader::new(&encoded), &shape, true).is_err());
        proof.queries.last_mut().unwrap().initial_path[0][0] ^= 1;
        assert!(encode_basefold(&mut Vec::new(), &proof, &shape, true).is_err());
        // The pre-activation codec still serializes arbitrary full paths. It
        // has not inherited any new compact-format validation rule.
        assert!(encode_basefold(&mut Vec::new(), &proof, &shape, false).is_ok());
        proof.queries[0].position = 1usize << shape.initial_path;
        assert!(encode_basefold(&mut Vec::new(), &proof, &shape, true).is_err());
    }

    #[test]
    fn c1_history_basefold_wire_shapes_are_exact() {
        let expected = [
            // B25: k_code=19. Exact encoded lengths are pinned below.
            (0usize, 19usize, 3_720usize, 500_560usize),
            // B255: k_code=21, FRI arities [4,4,4,4,3].
            (1usize, 21usize, 3_976usize, 547_024usize),
        ];

        for (class_index, expected_k_code, expected_query_bytes, expected_total) in expected {
            let class = CanonicalHistoryStepClassId::from_index(class_index)
                .expect("canonical History class");
            let params = canonical_history_step_pcs_params(class);
            let shape = BaseFoldWireShape::derive(&params).expect("canonical BaseFold wire shape");
            assert_eq!(params.k_code(), expected_k_code);
            assert_eq!(shape.queries, HISTORY_STEP_FRI_QUERIES);
            assert_eq!(
                shape
                    .query_encoded_len()
                    .expect("canonical query wire length"),
                expected_query_bytes
            );
            assert_eq!(
                shape.encoded_len().expect("canonical BaseFold wire length"),
                expected_total
            );
        }
    }
}
