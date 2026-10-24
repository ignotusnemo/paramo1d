// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Allocation-bounded compressed framing for header inventory batches.
//!
//! The generic libp2p CBOR codec buffers as many as ten MiB before decoding
//! attacker-controlled sequence lengths.  Header sync has a much smaller
//! consensus surface: at most 4,096 fixed-size records. Each record contains
//! one unchanged canonical header and bounded exact-object availability. This
//! codec checks the count, compressed length, frame length, declared content
//! size and zstd window before decompression.

use std::io;

use crate::header_protocol::{HeaderInventoryRecord, HEADER_INVENTORY_RECORD_BYTES};
use crate::object_protocol::DataResponseStatus;
use crate::protocol::{GetHeadersRequest, GetHeadersResponse};
use async_trait::async_trait;
use futures::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use libp2p::{request_response, swarm::StreamProtocol};

const REQUEST_MAGIC: [u8; 4] = *b"NHQ5";
const LEGACY_REQUEST_MAGIC: [u8; 4] = *b"NHQ4";
const RESPONSE_MAGIC: [u8; 4] = *b"NHB5";
const LEGACY_RESPONSE_MAGIC: [u8; 4] = *b"NHB4";
const REQUEST_BYTES: usize = 4 + 8 + 2 + 2;
// magic + count + flags + status + retry + reserved + compressed length +
// snapshot height + snapshot hash
const RESPONSE_HEADER_BYTES: usize = 4 + 2 + 1 + 1 + 2 + 2 + 4 + 8 + 32;
const LEGACY_RESPONSE_HEADER_BYTES: usize = 4 + 2 + 1 + 1 + 4 + 8 + 32;
const RESPONSE_HAS_SNAPSHOT_BOUNDARY: u8 = 1;
const HEADER_COMPRESSION_LEVEL: i32 = 1;
const HEADER_ZSTD_WINDOW_LOG_MAX: u32 = 21;
/// Fixed bytes preceding the compressed inventory payload in one response.
pub const HEADER_RESPONSE_PREFIX_BYTES: usize = RESPONSE_HEADER_BYTES;
/// Maximum compressed-framing header inventory batch.
pub const MAX_HEADERS_PER_BATCH: usize = 4_096;
/// Maximum fixed-record bytes produced by one compressed response.
pub const MAX_UNCOMPRESSED_HEADER_BYTES: usize =
    MAX_HEADERS_PER_BATCH * HEADER_INVENTORY_RECORD_BYTES;

const _: () = assert!(
    MAX_UNCOMPRESSED_HEADER_BYTES <= (1usize << HEADER_ZSTD_WINDOW_LOG_MAX),
    "header batch must fit inside the bounded zstd window"
);

/// Fixed-framing header request/response codec.
#[derive(Debug, Clone, Copy, Default)]
pub struct HeaderSyncCodec;

#[async_trait]
impl request_response::Codec for HeaderSyncCodec {
    type Protocol = StreamProtocol;
    type Request = GetHeadersRequest;
    type Response = GetHeadersResponse;

    async fn read_request<T>(
        &mut self,
        protocol: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Request>
    where
        T: AsyncRead + Unpin + Send,
    {
        let mut encoded = [0u8; REQUEST_BYTES];
        io.read_exact(&mut encoded).await?;
        let expected_magic = if is_legacy_protocol(protocol) {
            LEGACY_REQUEST_MAGIC
        } else {
            REQUEST_MAGIC
        };
        if encoded[..4] != expected_magic {
            return Err(invalid_data("invalid header-sync request magic/version"));
        }
        if encoded[14] > 1 || encoded[15] != 0 {
            return Err(invalid_data("non-zero header-sync request reserved bytes"));
        }
        let count = u16::from_le_bytes(encoded[12..14].try_into().expect("fixed count"));
        validate_count(count)?;
        ensure_eof(io).await?;
        Ok(GetHeadersRequest {
            start_height: u64::from_le_bytes(
                encoded[4..12].try_into().expect("fixed start height"),
            ),
            count,
            include_inventory: encoded[14] == 1,
        })
    }

    async fn read_response<T>(
        &mut self,
        protocol: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Response>
    where
        T: AsyncRead + Unpin + Send,
    {
        let (status, count, flags, compressed_len, snapshot_height, snapshot_hash) =
            if is_legacy_protocol(protocol) {
                let mut header = [0u8; LEGACY_RESPONSE_HEADER_BYTES];
                io.read_exact(&mut header).await?;
                if header[..4] != LEGACY_RESPONSE_MAGIC {
                    return Err(invalid_data("invalid header-sync response magic/version"));
                }
                if header[6] & !RESPONSE_HAS_SNAPSHOT_BOUNDARY != 0 || header[7] != 0 {
                    return Err(invalid_data(
                        "invalid header-sync response flags/reserved byte",
                    ));
                }
                (
                    DataResponseStatus::Ready,
                    u16::from_le_bytes(header[4..6].try_into().expect("fixed count")),
                    header[6],
                    u32::from_le_bytes(header[8..12].try_into().expect("fixed compressed length"))
                        as usize,
                    u64::from_le_bytes(header[12..20].try_into().expect("fixed snapshot height")),
                    header[20..52].try_into().expect("fixed snapshot hash"),
                )
            } else {
                let mut header = [0u8; RESPONSE_HEADER_BYTES];
                io.read_exact(&mut header).await?;
                if header[..4] != RESPONSE_MAGIC {
                    return Err(invalid_data("invalid header-sync response magic/version"));
                }
                if header[6] & !RESPONSE_HAS_SNAPSHOT_BOUNDARY != 0 || header[10..12] != [0, 0] {
                    return Err(invalid_data(
                        "invalid header-sync response flags/reserved bytes",
                    ));
                }
                let retry_after_ms =
                    u16::from_le_bytes(header[8..10].try_into().expect("fixed retry"));
                let status = match header[7] {
                    0 if retry_after_ms == 0 => DataResponseStatus::Ready,
                    1 => DataResponseStatus::Busy { retry_after_ms },
                    _ => return Err(invalid_data("invalid header-sync response status")),
                };
                if !status.is_canonical() {
                    return Err(invalid_data("non-canonical header-sync response status"));
                }
                (
                    status,
                    u16::from_le_bytes(header[4..6].try_into().expect("fixed count")),
                    header[6],
                    u32::from_le_bytes(header[12..16].try_into().expect("fixed compressed length"))
                        as usize,
                    u64::from_le_bytes(header[16..24].try_into().expect("fixed snapshot height")),
                    header[24..56].try_into().expect("fixed snapshot hash"),
                )
            };
        validate_count(count)?;
        if matches!(status, DataResponseStatus::Busy { .. }) {
            if count != 0
                || flags != 0
                || compressed_len != 0
                || snapshot_height != 0
                || snapshot_hash != [0; 32]
            {
                return Err(invalid_data("busy header-sync response carries data"));
            }
            ensure_eof(io).await?;
            return Ok(GetHeadersResponse {
                status,
                records: Vec::new(),
                snapshot_boundary: None,
            });
        }
        let snapshot_boundary = if flags & RESPONSE_HAS_SNAPSHOT_BOUNDARY != 0 {
            if snapshot_height == 0 || snapshot_hash == [0; 32] {
                return Err(invalid_data("invalid advertised snapshot boundary"));
            }
            Some(crate::object_protocol::ChainPoint::new(
                snapshot_height,
                snapshot_hash,
            ))
        } else {
            if snapshot_height != 0 || snapshot_hash != [0; 32] {
                return Err(invalid_data("noncanonical missing snapshot boundary"));
            }
            None
        };
        let canonical_len = canonical_payload_len(count)?;
        validate_compressed_len(canonical_len, compressed_len)?;

        // Both attacker-controlled lengths have passed count-relative hard
        // caps. Read exactly one bounded frame before invoking zstd.
        let mut compressed = Vec::new();
        compressed.try_reserve_exact(compressed_len).map_err(|_| {
            io::Error::new(io::ErrorKind::OutOfMemory, "header batch allocation failed")
        })?;
        compressed.resize(compressed_len, 0);
        io.read_exact(&mut compressed).await?;
        ensure_eof(io).await?;

        validate_zstd_frame(&compressed, canonical_len)?;
        let payload = decompress_canonical_headers(&compressed, canonical_len)?;

        let count = usize::from(count);
        let mut records = Vec::new();
        records.try_reserve_exact(count).map_err(|_| {
            io::Error::new(io::ErrorKind::OutOfMemory, "header batch allocation failed")
        })?;
        for encoded in payload.chunks_exact(HEADER_INVENTORY_RECORD_BYTES) {
            records.push(
                HeaderInventoryRecord::decode(encoded)
                    .map_err(|_| invalid_data("header inventory decode failed"))?,
            );
        }
        Ok(GetHeadersResponse {
            status,
            records,
            snapshot_boundary,
        })
    }

    async fn write_request<T>(
        &mut self,
        protocol: &Self::Protocol,
        io: &mut T,
        request: Self::Request,
    ) -> io::Result<()>
    where
        T: AsyncWrite + Unpin + Send,
    {
        validate_count(request.count)?;
        let mut encoded = [0u8; REQUEST_BYTES];
        encoded[..4].copy_from_slice(if is_legacy_protocol(protocol) {
            &LEGACY_REQUEST_MAGIC
        } else {
            &REQUEST_MAGIC
        });
        encoded[4..12].copy_from_slice(&request.start_height.to_le_bytes());
        encoded[12..14].copy_from_slice(&request.count.to_le_bytes());
        encoded[14] = request.include_inventory as u8;
        io.write_all(&encoded).await
    }

    async fn write_response<T>(
        &mut self,
        protocol: &Self::Protocol,
        io: &mut T,
        response: Self::Response,
    ) -> io::Result<()>
    where
        T: AsyncWrite + Unpin + Send,
    {
        let GetHeadersResponse {
            status,
            records,
            snapshot_boundary,
        } = response;
        if !status.is_canonical() {
            return Err(invalid_data("non-canonical header-sync response status"));
        }
        if matches!(status, DataResponseStatus::Busy { .. })
            && (!records.is_empty() || snapshot_boundary.is_some())
        {
            return Err(invalid_data("busy header-sync response carries data"));
        }
        if matches!(status, DataResponseStatus::Busy { .. }) && !is_legacy_protocol(protocol) {
            let mut response_header = [0u8; RESPONSE_HEADER_BYTES];
            response_header[..4].copy_from_slice(&RESPONSE_MAGIC);
            response_header[7] = 1;
            response_header[8..10].copy_from_slice(
                &status
                    .busy_retry_after_ms()
                    .expect("busy status has a retry interval")
                    .to_le_bytes(),
            );
            io.write_all(&response_header).await?;
            return Ok(());
        }
        // Header v4 has no explicit Busy representation. An empty canonical
        // response preserves bounded server work and makes a v2.0.1 caller
        // retry normally without treating the peer as corrupt.
        let records = if matches!(status, DataResponseStatus::Busy { .. }) {
            Vec::new()
        } else {
            records
        };
        let snapshot_boundary = if matches!(status, DataResponseStatus::Busy { .. }) {
            None
        } else {
            snapshot_boundary
        };
        let count = u16::try_from(records.len())
            .map_err(|_| invalid_data("header batch count does not fit u16"))?;
        validate_count(count)?;
        let canonical_len = canonical_payload_len(count)?;
        let mut canonical = Vec::new();
        canonical.try_reserve_exact(canonical_len).map_err(|_| {
            io::Error::new(io::ErrorKind::OutOfMemory, "header batch allocation failed")
        })?;
        for record in records {
            canonical.extend_from_slice(
                &record
                    .encode()
                    .map_err(|_| invalid_data("invalid outgoing header inventory"))?,
            );
        }
        let compressed =
            zstd::bulk::compress(&canonical, HEADER_COMPRESSION_LEVEL).map_err(|error| {
                io::Error::other(format!("header zstd compression failed: {error}"))
            })?;
        validate_compressed_len(canonical_len, compressed.len()).map_err(|_| {
            io::Error::other("header zstd encoder exceeded its deterministic bound")
        })?;
        let compressed_len = u32::try_from(compressed.len())
            .map_err(|_| io::Error::other("compressed header batch length does not fit u32"))?;

        if is_legacy_protocol(protocol) {
            let mut response_header = [0u8; LEGACY_RESPONSE_HEADER_BYTES];
            response_header[..4].copy_from_slice(&LEGACY_RESPONSE_MAGIC);
            response_header[4..6].copy_from_slice(&count.to_le_bytes());
            response_header[8..12].copy_from_slice(&compressed_len.to_le_bytes());
            if let Some(boundary) = snapshot_boundary {
                validate_outgoing_boundary(boundary)?;
                response_header[6] = RESPONSE_HAS_SNAPSHOT_BOUNDARY;
                response_header[12..20].copy_from_slice(&boundary.height.to_le_bytes());
                response_header[20..52].copy_from_slice(&boundary.hash);
            }
            io.write_all(&response_header).await?;
        } else {
            let mut response_header = [0u8; RESPONSE_HEADER_BYTES];
            response_header[..4].copy_from_slice(&RESPONSE_MAGIC);
            response_header[4..6].copy_from_slice(&count.to_le_bytes());
            response_header[12..16].copy_from_slice(&compressed_len.to_le_bytes());
            if let Some(boundary) = snapshot_boundary {
                validate_outgoing_boundary(boundary)?;
                response_header[6] = RESPONSE_HAS_SNAPSHOT_BOUNDARY;
                response_header[16..24].copy_from_slice(&boundary.height.to_le_bytes());
                response_header[24..56].copy_from_slice(&boundary.hash);
            }
            io.write_all(&response_header).await?;
        }
        io.write_all(&compressed).await
    }
}

fn is_legacy_protocol(protocol: &StreamProtocol) -> bool {
    protocol.as_ref().ends_with("/sync/headers/4")
}

fn validate_outgoing_boundary(boundary: crate::object_protocol::ChainPoint) -> io::Result<()> {
    if boundary.height == 0 || boundary.hash == [0; 32] {
        return Err(invalid_data("invalid outgoing snapshot boundary"));
    }
    Ok(())
}

fn validate_count(count: u16) -> io::Result<()> {
    if usize::from(count) > MAX_HEADERS_PER_BATCH {
        return Err(invalid_data(
            "declared header batch count exceeds the fixed cap",
        ));
    }
    Ok(())
}

fn canonical_payload_len(count: u16) -> io::Result<usize> {
    usize::from(count)
        .checked_mul(HEADER_INVENTORY_RECORD_BYTES)
        .filter(|len| *len <= MAX_UNCOMPRESSED_HEADER_BYTES)
        .ok_or_else(|| invalid_data("header batch canonical length exceeds the fixed cap"))
}

fn validate_compressed_len(canonical_len: usize, compressed_len: usize) -> io::Result<()> {
    let maximum = zstd::zstd_safe::compress_bound(canonical_len);
    if compressed_len == 0 || compressed_len > maximum {
        return Err(invalid_data(
            "compressed header batch length exceeds its count-relative bound",
        ));
    }
    Ok(())
}

fn validate_zstd_frame(compressed: &[u8], canonical_len: usize) -> io::Result<()> {
    let frame_len = zstd::zstd_safe::find_frame_compressed_size(compressed)
        .map_err(|_| invalid_data("invalid header zstd frame"))?;
    if frame_len != compressed.len() {
        return Err(invalid_data(
            "header response must contain exactly one zstd frame",
        ));
    }
    let content_size = zstd::zstd_safe::get_frame_content_size(compressed)
        .map_err(|_| invalid_data("invalid header zstd content size"))?;
    if content_size != Some(canonical_len as u64) {
        return Err(invalid_data(
            "header zstd content size does not match the declared count",
        ));
    }
    Ok(())
}

fn decompress_canonical_headers(compressed: &[u8], canonical_len: usize) -> io::Result<Vec<u8>> {
    let mut decoder = zstd::bulk::Decompressor::new()
        .map_err(|error| io::Error::other(format!("header zstd decoder init failed: {error}")))?;
    decoder
        .window_log_max(HEADER_ZSTD_WINDOW_LOG_MAX)
        .map_err(|error| io::Error::other(format!("header zstd window setup failed: {error}")))?;
    let decoded = decoder
        .decompress(compressed, canonical_len)
        .map_err(|_| invalid_data("header zstd decompression failed"))?;
    if decoded.len() != canonical_len {
        return Err(invalid_data(
            "decompressed header payload has the wrong canonical length",
        ));
    }
    Ok(decoded)
}

async fn ensure_eof<T: AsyncRead + Unpin + Send>(io: &mut T) -> io::Result<()> {
    let mut trailing = [0u8; 1];
    if io.read(&mut trailing).await? != 0 {
        return Err(invalid_data("trailing bytes in header-sync message"));
    }
    Ok(())
}

fn invalid_data(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.to_owned())
}

#[cfg(test)]
mod tests {
    use futures::io::Cursor;
    use libp2p::request_response::Codec;
    use noid_chain::BlockHeader;

    use super::*;

    fn protocol() -> StreamProtocol {
        StreamProtocol::new("/noid/test/sync/headers/5")
    }

    fn legacy_protocol() -> StreamProtocol {
        StreamProtocol::new("/noid/test/sync/headers/4")
    }

    fn response_header(count: u16, compressed_len: usize) -> Vec<u8> {
        let mut encoded = vec![0u8; RESPONSE_HEADER_BYTES];
        encoded[..4].copy_from_slice(&RESPONSE_MAGIC);
        encoded[4..6].copy_from_slice(&count.to_le_bytes());
        encoded[12..16].copy_from_slice(&(compressed_len as u32).to_le_bytes());
        encoded
    }

    fn compress(payload: &[u8]) -> Vec<u8> {
        zstd::bulk::compress(payload, HEADER_COMPRESSION_LEVEL).unwrap()
    }

    fn fixture_header(height: u64, marker: u8) -> BlockHeader {
        let mut header = noid_chain::consensus::genesis::genesis_header();
        header.height = height;
        header.state_root = [marker; 32];
        header.tx_root = [marker.wrapping_add(1); 32];
        header.nonce = u128::from(marker);
        header
    }

    fn fixture_record(height: u64, marker: u8) -> HeaderInventoryRecord {
        HeaderInventoryRecord::header_only(fixture_header(height, marker))
    }

    fn framed_response(count: u16, canonical: &[u8]) -> Vec<u8> {
        let compressed = compress(canonical);
        let mut encoded = response_header(count, compressed.len());
        encoded.extend_from_slice(&compressed);
        encoded
    }

    #[tokio::test]
    async fn request_is_exact_and_caps_count() {
        let request = GetHeadersRequest {
            start_height: 41,
            count: MAX_HEADERS_PER_BATCH as u16,
            include_inventory: true,
        };
        let mut wire = Cursor::new(Vec::new());
        HeaderSyncCodec
            .write_request(&protocol(), &mut wire, request)
            .await
            .unwrap();
        assert_eq!(wire.get_ref().len(), REQUEST_BYTES);
        wire.set_position(0);
        let decoded = HeaderSyncCodec
            .read_request(&protocol(), &mut wire)
            .await
            .unwrap();
        assert_eq!(decoded.start_height, 41);
        assert_eq!(decoded.count, MAX_HEADERS_PER_BATCH as u16);
        assert!(decoded.include_inventory);

        let mut oversized = wire.into_inner();
        oversized[12..14].copy_from_slice(&((MAX_HEADERS_PER_BATCH as u16) + 1).to_le_bytes());
        let error = HeaderSyncCodec
            .read_request(&protocol(), &mut Cursor::new(oversized))
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    }

    #[tokio::test]
    async fn malicious_count_rejects_before_any_header_payload_read_or_reserve() {
        // Only the fixed header is supplied. InvalidData (rather than EOF)
        // demonstrates that the count gate fires before a payload read.
        let error = HeaderSyncCodec
            .read_response(&protocol(), &mut Cursor::new(response_header(u16::MAX, 1)))
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("count"));
    }

    #[tokio::test]
    async fn response_round_trip_restores_exact_canonical_headers() {
        let snapshot_boundary = crate::object_protocol::ChainPoint::new(42, [0xA5; 32]);
        let response = GetHeadersResponse {
            status: DataResponseStatus::Ready,
            records: vec![fixture_record(1, 0x11), fixture_record(2, 0x22)],
            snapshot_boundary: Some(snapshot_boundary),
        };
        let mut wire = Cursor::new(Vec::new());
        HeaderSyncCodec
            .write_response(&protocol(), &mut wire, response)
            .await
            .unwrap();
        assert_eq!(&wire.get_ref()[..4], &RESPONSE_MAGIC);
        let compressed_len = u32::from_le_bytes(wire.get_ref()[12..16].try_into().unwrap());
        assert_eq!(
            wire.get_ref().len(),
            RESPONSE_HEADER_BYTES + compressed_len as usize
        );
        assert!(wire.get_ref().len() < RESPONSE_HEADER_BYTES + 2 * HEADER_INVENTORY_RECORD_BYTES);
        wire.set_position(0);
        let decoded = HeaderSyncCodec
            .read_response(&protocol(), &mut wire)
            .await
            .unwrap();
        assert_eq!(decoded.status, DataResponseStatus::Ready);
        assert_eq!(decoded.records[0], fixture_record(1, 0x11));
        assert_eq!(decoded.records[1], fixture_record(2, 0x22));
        assert_eq!(decoded.snapshot_boundary, Some(snapshot_boundary));
    }

    #[tokio::test]
    async fn legacy_v4_round_trip_is_byte_compatible_with_v2_0_1() {
        let snapshot_boundary = crate::object_protocol::ChainPoint::new(42, [0xA5; 32]);
        let response = GetHeadersResponse {
            status: DataResponseStatus::Ready,
            records: vec![fixture_record(1, 0x11), fixture_record(2, 0x22)],
            snapshot_boundary: Some(snapshot_boundary),
        };
        let mut wire = Cursor::new(Vec::new());
        HeaderSyncCodec
            .write_response(&legacy_protocol(), &mut wire, response)
            .await
            .unwrap();
        assert_eq!(&wire.get_ref()[..4], &LEGACY_RESPONSE_MAGIC);
        let compressed_len = u32::from_le_bytes(wire.get_ref()[8..12].try_into().unwrap());
        assert_eq!(
            wire.get_ref().len(),
            LEGACY_RESPONSE_HEADER_BYTES + compressed_len as usize
        );
        wire.set_position(0);
        let decoded = HeaderSyncCodec
            .read_response(&legacy_protocol(), &mut wire)
            .await
            .unwrap();
        assert_eq!(decoded.status, DataResponseStatus::Ready);
        assert_eq!(decoded.records[0], fixture_record(1, 0x11));
        assert_eq!(decoded.records[1], fixture_record(2, 0x22));
        assert_eq!(decoded.snapshot_boundary, Some(snapshot_boundary));

        let request = GetHeadersRequest {
            start_height: 7,
            count: 9,
            include_inventory: true,
        };
        let mut request_wire = Cursor::new(Vec::new());
        HeaderSyncCodec
            .write_request(&legacy_protocol(), &mut request_wire, request)
            .await
            .unwrap();
        assert_eq!(&request_wire.get_ref()[..4], &LEGACY_REQUEST_MAGIC);
        request_wire.set_position(0);
        let decoded = HeaderSyncCodec
            .read_request(&legacy_protocol(), &mut request_wire)
            .await
            .unwrap();
        assert_eq!(decoded.start_height, 7);
        assert_eq!(decoded.count, 9);
        assert!(decoded.include_inventory);
    }

    #[tokio::test]
    async fn writer_rejects_oversized_batch_before_partial_output() {
        let mut wire = Cursor::new(Vec::new());
        let error = HeaderSyncCodec
            .write_response(
                &protocol(),
                &mut wire,
                GetHeadersResponse {
                    status: DataResponseStatus::Ready,
                    records: vec![fixture_record(1, 1); MAX_HEADERS_PER_BATCH + 1],
                    snapshot_boundary: None,
                },
            )
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(wire.get_ref().is_empty());
    }

    #[tokio::test]
    async fn compressed_length_cap_fires_before_payload_read_or_reserve() {
        let canonical_len = HEADER_INVENTORY_RECORD_BYTES;
        let oversized = zstd::zstd_safe::compress_bound(canonical_len) + 1;
        let error = HeaderSyncCodec
            .read_response(&protocol(), &mut Cursor::new(response_header(1, oversized)))
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("compressed"));
    }

    #[tokio::test]
    async fn response_rejects_zstd_content_size_that_disagrees_with_count() {
        let one_header = vec![0x33; HEADER_INVENTORY_RECORD_BYTES];
        let error = HeaderSyncCodec
            .read_response(
                &protocol(),
                &mut Cursor::new(framed_response(2, &one_header)),
            )
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("content size"));
    }

    #[tokio::test]
    async fn response_rejects_multiple_zstd_frames_inside_declared_payload() {
        let canonical = vec![0x44; HEADER_INVENTORY_RECORD_BYTES];
        let mut compressed = compress(&canonical);
        compressed.extend_from_slice(&compress(&[]));
        assert!(compressed.len() <= zstd::zstd_safe::compress_bound(canonical.len()));
        let mut wire = response_header(1, compressed.len());
        wire.extend_from_slice(&compressed);

        let error = HeaderSyncCodec
            .read_response(&protocol(), &mut Cursor::new(wire))
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("exactly one"));
    }

    #[tokio::test]
    async fn maximum_batch_round_trip_stays_exact_and_bounded() {
        let records = (0..MAX_HEADERS_PER_BATCH)
            .map(|height| fixture_record(height as u64, height as u8))
            .collect::<Vec<_>>();
        let expected = records.clone();
        let mut wire = Cursor::new(Vec::new());
        HeaderSyncCodec
            .write_response(
                &protocol(),
                &mut wire,
                GetHeadersResponse {
                    status: DataResponseStatus::Ready,
                    records,
                    snapshot_boundary: None,
                },
            )
            .await
            .unwrap();
        assert!(
            wire.get_ref().len()
                <= RESPONSE_HEADER_BYTES
                    + zstd::zstd_safe::compress_bound(MAX_UNCOMPRESSED_HEADER_BYTES)
        );
        wire.set_position(0);
        let decoded = HeaderSyncCodec
            .read_response(&protocol(), &mut wire)
            .await
            .unwrap();
        assert_eq!(decoded.records, expected);
    }

    #[tokio::test]
    async fn busy_response_is_payload_free_and_round_trips() {
        let response = GetHeadersResponse {
            status: DataResponseStatus::Busy {
                retry_after_ms: 700,
            },
            records: Vec::new(),
            snapshot_boundary: None,
        };
        let mut wire = Cursor::new(Vec::new());
        HeaderSyncCodec
            .write_response(&protocol(), &mut wire, response)
            .await
            .unwrap();
        assert_eq!(wire.get_ref().len(), RESPONSE_HEADER_BYTES);
        wire.set_position(0);
        let decoded = HeaderSyncCodec
            .read_response(&protocol(), &mut wire)
            .await
            .unwrap();
        assert_eq!(
            decoded.status,
            DataResponseStatus::Busy {
                retry_after_ms: 700
            }
        );
        assert!(decoded.records.is_empty());
        assert!(decoded.snapshot_boundary.is_none());
    }

    #[tokio::test]
    async fn busy_response_degrades_to_empty_ready_for_legacy_v4() {
        let response = GetHeadersResponse {
            status: DataResponseStatus::Busy {
                retry_after_ms: 700,
            },
            records: Vec::new(),
            snapshot_boundary: None,
        };
        let mut wire = Cursor::new(Vec::new());
        HeaderSyncCodec
            .write_response(&legacy_protocol(), &mut wire, response)
            .await
            .unwrap();
        assert_eq!(&wire.get_ref()[..4], &LEGACY_RESPONSE_MAGIC);
        wire.set_position(0);
        let decoded = HeaderSyncCodec
            .read_response(&legacy_protocol(), &mut wire)
            .await
            .unwrap();
        assert_eq!(decoded.status, DataResponseStatus::Ready);
        assert!(decoded.records.is_empty());
        assert!(decoded.snapshot_boundary.is_none());
    }

    #[tokio::test]
    async fn writer_rejects_busy_response_with_headers() {
        let mut wire = Cursor::new(Vec::new());
        let error = HeaderSyncCodec
            .write_response(
                &protocol(),
                &mut wire,
                GetHeadersResponse {
                    status: DataResponseStatus::Busy {
                        retry_after_ms: 700,
                    },
                    records: vec![fixture_record(1, 1)],
                    snapshot_boundary: None,
                },
            )
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(wire.get_ref().is_empty());
    }

    #[tokio::test]
    async fn response_rejects_trailing_bytes() {
        let mut wire = framed_response(0, &[]);
        wire.push(0xAA);
        let error = HeaderSyncCodec
            .read_response(&protocol(), &mut Cursor::new(wire))
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    }
}
