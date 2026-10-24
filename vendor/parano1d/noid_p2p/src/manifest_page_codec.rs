// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Exact content-addressed transfer for snapshot descriptor pages.

use std::{io, sync::Arc};

use async_trait::async_trait;
use futures::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use libp2p::{request_response, swarm::StreamProtocol};

use crate::{
    inbound_budget::process_global_inbound_budget,
    object_protocol::{ChainPoint, DataResponseStatus, SnapshotId},
    protocol::{
        GetSnapshotManifestPageRequest, GetSnapshotManifestPageResponse,
        SnapshotManifestPageObjectId, SnapshotManifestPageRef,
        SNAPSHOT_MANIFEST_DESCRIPTORS_PER_PAGE, SNAPSHOT_MANIFEST_DESCRIPTOR_BYTES,
        SNAPSHOT_MANIFEST_PAGE_HEADER_BYTES,
    },
};

const REQUEST_MAGIC: [u8; 4] = *b"PMQ1";
const RESPONSE_MAGIC: [u8; 4] = *b"PMS1";
const OBJECT_ID_BYTES: usize = 8 + 32 + 32 + 32 + 4 + 2 + 32 + 4 + 2;
const REQUEST_BYTES: usize = 4 + OBJECT_ID_BYTES;
const RESPONSE_HEADER_BYTES: usize = 4 + 1 + 1 + 2 + OBJECT_ID_BYTES;
const AVAILABLE: u8 = 1;
const UNAVAILABLE: u8 = 0;
pub const MAX_SNAPSHOT_MANIFEST_PAGE_BYTES: usize = SNAPSHOT_MANIFEST_PAGE_HEADER_BYTES
    + SNAPSHOT_MANIFEST_DESCRIPTORS_PER_PAGE * SNAPSHOT_MANIFEST_DESCRIPTOR_BYTES;

#[derive(Debug, Clone)]
pub struct ManifestPageCodec {
    inbound_budget: Arc<tokio::sync::Semaphore>,
}

impl Default for ManifestPageCodec {
    fn default() -> Self {
        Self {
            inbound_budget: process_global_inbound_budget(),
        }
    }
}

#[async_trait]
impl request_response::Codec for ManifestPageCodec {
    type Protocol = StreamProtocol;
    type Request = GetSnapshotManifestPageRequest;
    type Response = GetSnapshotManifestPageResponse;

    async fn read_request<T>(
        &mut self,
        _protocol: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Request>
    where
        T: AsyncRead + Unpin + Send,
    {
        let mut encoded = [0u8; REQUEST_BYTES];
        io.read_exact(&mut encoded).await?;
        if encoded[..4] != REQUEST_MAGIC {
            return Err(invalid_data("invalid manifest-page request magic/version"));
        }
        let object = decode_object(&encoded[4..])?;
        ensure_eof(io).await?;
        Ok(GetSnapshotManifestPageRequest { object })
    }

    async fn read_response<T>(
        &mut self,
        _protocol: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Response>
    where
        T: AsyncRead + Unpin + Send,
    {
        let mut header = [0u8; RESPONSE_HEADER_BYTES];
        io.read_exact(&mut header).await?;
        if header[..4] != RESPONSE_MAGIC {
            return Err(invalid_data("invalid manifest-page response magic/version"));
        }
        let retry_after_ms = u16::from_le_bytes(header[6..8].try_into().unwrap());
        let status = match header[4] {
            0 if retry_after_ms == 0 => DataResponseStatus::Ready,
            1 => DataResponseStatus::Busy { retry_after_ms },
            _ => return Err(invalid_data("invalid manifest-page response status")),
        };
        if !status.is_canonical() {
            return Err(invalid_data("non-canonical manifest-page response status"));
        }
        let availability = header[5];
        if availability != AVAILABLE && availability != UNAVAILABLE {
            return Err(invalid_data("invalid manifest-page availability marker"));
        }
        if matches!(status, DataResponseStatus::Busy { .. }) && availability == AVAILABLE {
            return Err(invalid_data("busy manifest-page response carries data"));
        }
        let object = decode_object(&header[8..])?;
        let (data, inbound_memory_permit) = if availability == AVAILABLE {
            let len = usize::try_from(object.page.encoded_len)
                .map_err(|_| invalid_data("manifest-page length does not fit usize"))?;
            let permits = u32::try_from(len)
                .map_err(|_| invalid_data("manifest-page byte budget overflow"))?;
            let permit = Arc::clone(&self.inbound_budget)
                .acquire_many_owned(permits)
                .await
                .map_err(|_| {
                    io::Error::new(
                        io::ErrorKind::BrokenPipe,
                        "manifest-page byte budget closed",
                    )
                })?;
            let mut bytes = vec![0u8; len];
            io.read_exact(&mut bytes).await?;
            (Some(Arc::from(bytes)), Some(Arc::new(permit)))
        } else {
            (None, None)
        };
        ensure_eof(io).await?;
        Ok(GetSnapshotManifestPageResponse {
            object,
            status,
            data,
            inbound_memory_permit,
            outbound_memory_permit: None,
        })
    }

    async fn write_request<T>(
        &mut self,
        _protocol: &Self::Protocol,
        io: &mut T,
        request: Self::Request,
    ) -> io::Result<()>
    where
        T: AsyncWrite + Unpin + Send,
    {
        validate_object(request.object)?;
        let mut encoded = [0u8; REQUEST_BYTES];
        encoded[..4].copy_from_slice(&REQUEST_MAGIC);
        encode_object(request.object, &mut encoded[4..]);
        io.write_all(&encoded).await
    }

    async fn write_response<T>(
        &mut self,
        _protocol: &Self::Protocol,
        io: &mut T,
        response: Self::Response,
    ) -> io::Result<()>
    where
        T: AsyncWrite + Unpin + Send,
    {
        validate_object(response.object)?;
        if !response.status.is_canonical()
            || (matches!(response.status, DataResponseStatus::Busy { .. })
                && response.data.is_some())
            || response.data.as_ref().is_some_and(|bytes| {
                usize::try_from(response.object.page.encoded_len).ok() != Some(bytes.len())
            })
        {
            return Err(invalid_data("invalid manifest-page response"));
        }
        let mut header = [0u8; RESPONSE_HEADER_BYTES];
        header[..4].copy_from_slice(&RESPONSE_MAGIC);
        if let DataResponseStatus::Busy { retry_after_ms } = response.status {
            header[4] = 1;
            header[6..8].copy_from_slice(&retry_after_ms.to_le_bytes());
        }
        header[5] = if response.data.is_some() {
            AVAILABLE
        } else {
            UNAVAILABLE
        };
        encode_object(response.object, &mut header[8..]);
        io.write_all(&header).await?;
        if let Some(data) = response.data {
            io.write_all(data.as_ref()).await?;
        }
        io.flush().await?;
        drop(response.inbound_memory_permit);
        drop(response.outbound_memory_permit);
        Ok(())
    }
}

fn validate_object(object: SnapshotManifestPageObjectId) -> io::Result<()> {
    if object.snapshot.boundary.height == 0
        || object.snapshot.format_version == 0
        || object.page.descriptor_count == 0
        || usize::from(object.page.descriptor_count) > SNAPSHOT_MANIFEST_DESCRIPTORS_PER_PAGE
        || object.page.encoded_len == 0
        || object.page.encoded_len as usize > MAX_SNAPSHOT_MANIFEST_PAGE_BYTES
    {
        return Err(invalid_data(
            "manifest-page object identity is outside fixed caps",
        ));
    }
    let expected_len = SNAPSHOT_MANIFEST_PAGE_HEADER_BYTES
        + usize::from(object.page.descriptor_count) * SNAPSHOT_MANIFEST_DESCRIPTOR_BYTES;
    if object.page.encoded_len as usize != expected_len {
        return Err(invalid_data("manifest-page object length is noncanonical"));
    }
    Ok(())
}

fn decode_object(encoded: &[u8]) -> io::Result<SnapshotManifestPageObjectId> {
    if encoded.len() != OBJECT_ID_BYTES {
        return Err(invalid_data("invalid manifest-page object frame"));
    }
    let object = SnapshotManifestPageObjectId {
        snapshot: SnapshotId {
            boundary: ChainPoint {
                height: u64::from_le_bytes(encoded[..8].try_into().unwrap()),
                hash: encoded[8..40].try_into().unwrap(),
            },
            state_root: encoded[40..72].try_into().unwrap(),
            manifest_digest: encoded[72..104].try_into().unwrap(),
            format_version: u32::from_le_bytes(encoded[104..108].try_into().unwrap()),
        },
        page: SnapshotManifestPageRef {
            page_index: u16::from_le_bytes(encoded[108..110].try_into().unwrap()),
            byte_digest: encoded[110..142].try_into().unwrap(),
            encoded_len: u32::from_le_bytes(encoded[142..146].try_into().unwrap()),
            descriptor_count: u16::from_le_bytes(encoded[146..148].try_into().unwrap()),
        },
    };
    validate_object(object)?;
    Ok(object)
}

fn encode_object(object: SnapshotManifestPageObjectId, encoded: &mut [u8]) {
    encoded[..8].copy_from_slice(&object.snapshot.boundary.height.to_le_bytes());
    encoded[8..40].copy_from_slice(&object.snapshot.boundary.hash);
    encoded[40..72].copy_from_slice(&object.snapshot.state_root);
    encoded[72..104].copy_from_slice(&object.snapshot.manifest_digest);
    encoded[104..108].copy_from_slice(&object.snapshot.format_version.to_le_bytes());
    encoded[108..110].copy_from_slice(&object.page.page_index.to_le_bytes());
    encoded[110..142].copy_from_slice(&object.page.byte_digest);
    encoded[142..146].copy_from_slice(&object.page.encoded_len.to_le_bytes());
    encoded[146..148].copy_from_slice(&object.page.descriptor_count.to_le_bytes());
}

async fn ensure_eof<T: AsyncRead + Unpin + Send>(io: &mut T) -> io::Result<()> {
    let mut trailing = [0u8; 1];
    if io.read(&mut trailing).await? != 0 {
        return Err(invalid_data("trailing bytes in manifest-page message"));
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

    use super::*;

    fn protocol() -> StreamProtocol {
        StreamProtocol::new("/noid/test/sync/manifest-page/1")
    }

    fn object(bytes: &[u8]) -> SnapshotManifestPageObjectId {
        SnapshotManifestPageObjectId {
            snapshot: SnapshotId {
                boundary: ChainPoint::new(12, [1; 32]),
                state_root: [2; 32],
                manifest_digest: [3; 32],
                format_version: 2,
            },
            page: SnapshotManifestPageRef {
                page_index: 0,
                byte_digest: noid_poseidon2b::native::poseidon2b_hash_bytes(
                    b"PARANO1D/P2P/SNAPSHOT-MANIFEST-PAGE/V1",
                    bytes,
                ),
                encoded_len: bytes.len() as u32,
                descriptor_count: 1,
            },
        }
    }

    #[tokio::test]
    async fn exact_page_round_trip() {
        let mut bytes = Vec::from(*b"NMP1");
        bytes.extend_from_slice(&0u16.to_le_bytes());
        bytes.extend_from_slice(&1u16.to_le_bytes());
        bytes.extend_from_slice(&0u16.to_le_bytes());
        bytes.extend_from_slice(&[4; 32]);
        bytes.extend_from_slice(&59u32.to_le_bytes());
        let object = object(&bytes);
        let mut wire = Cursor::new(Vec::new());
        ManifestPageCodec::default()
            .write_response(
                &protocol(),
                &mut wire,
                GetSnapshotManifestPageResponse {
                    object,
                    status: DataResponseStatus::Ready,
                    data: Some(bytes.clone().into()),
                    inbound_memory_permit: None,
                    outbound_memory_permit: None,
                },
            )
            .await
            .unwrap();
        wire.set_position(0);
        let decoded = ManifestPageCodec::default()
            .read_response(&protocol(), &mut wire)
            .await
            .unwrap();
        assert_eq!(decoded.object, object);
        assert_eq!(decoded.data.as_deref(), Some(bytes.as_slice()));
    }
}
