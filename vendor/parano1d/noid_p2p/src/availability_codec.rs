// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Fixed framing for direct exact-object availability announcements.
//!
//! Gossip remains header-first and never carries a block body or recursive
//! terminal. Once a node has committed the announced tip, this small direct
//! protocol lets it tell its mesh neighbours that the exact objects named by
//! the header announcement are now locally serveable. Availability is only a
//! scheduling hint; receivers still validate the header, authenticate object
//! bytes by content identity, verify the recursive terminal, and commit
//! atomically.

use std::io;

use async_trait::async_trait;
use futures::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use libp2p::{request_response, swarm::StreamProtocol};

use crate::header_protocol::{HeaderAnnouncement, HEADER_ANNOUNCE_BYTES};

const RESPONSE_MAGIC: [u8; 4] = *b"NAA1";
const RESPONSE_BYTES: usize = 5;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AvailabilityRequest {
    pub announcement: HeaderAnnouncement,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AvailabilityResponse {
    Accepted,
    Busy,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct AvailabilityCodec;

#[async_trait]
impl request_response::Codec for AvailabilityCodec {
    type Protocol = StreamProtocol;
    type Request = AvailabilityRequest;
    type Response = AvailabilityResponse;

    async fn read_request<T>(
        &mut self,
        _protocol: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Request>
    where
        T: AsyncRead + Unpin + Send,
    {
        let mut encoded = [0u8; HEADER_ANNOUNCE_BYTES];
        io.read_exact(&mut encoded).await?;
        ensure_eof(io).await?;
        let announcement = HeaderAnnouncement::decode(&encoded)
            .map_err(|_| invalid_data("invalid direct availability announcement"))?;
        Ok(AvailabilityRequest { announcement })
    }

    async fn read_response<T>(
        &mut self,
        _protocol: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Response>
    where
        T: AsyncRead + Unpin + Send,
    {
        let mut encoded = [0u8; RESPONSE_BYTES];
        io.read_exact(&mut encoded).await?;
        ensure_eof(io).await?;
        if encoded[..4] != RESPONSE_MAGIC {
            return Err(invalid_data("invalid availability response magic/version"));
        }
        match encoded[4] {
            0 => Ok(AvailabilityResponse::Accepted),
            1 => Ok(AvailabilityResponse::Busy),
            _ => Err(invalid_data("invalid availability response status")),
        }
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
        let encoded = request
            .announcement
            .encode()
            .map_err(|_| invalid_data("invalid outgoing availability announcement"))?;
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
        let mut encoded = [0u8; RESPONSE_BYTES];
        encoded[..4].copy_from_slice(&RESPONSE_MAGIC);
        encoded[4] = match response {
            AvailabilityResponse::Accepted => 0,
            AvailabilityResponse::Busy => 1,
        };
        io.write_all(&encoded).await
    }
}

fn invalid_data(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

async fn ensure_eof<T>(io: &mut T) -> io::Result<()>
where
    T: AsyncRead + Unpin + Send,
{
    let mut trailing = [0u8; 1];
    match io.read(&mut trailing).await? {
        0 => Ok(()),
        _ => Err(invalid_data("availability frame has trailing bytes")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::{executor::block_on, io::Cursor};
    use libp2p::request_response::Codec as _;
    use noid_chain::{
        block_header::{block_id, semantic_header_id},
        consensus::genesis_header,
    };
    fn announcement() -> HeaderAnnouncement {
        let mut header = genesis_header();
        header.height = 1;
        header.prev_block_hash = block_id(&genesis_header());
        HeaderAnnouncement {
            header,
            body: crate::object_protocol::BlockBodyObjectId {
                claim: crate::object_protocol::BlockBodyClaimId {
                    height: 1,
                    block_hash: block_id(&header),
                },
                byte_digest: [7; 32],
                encoded_len: 64,
            },
            terminal: crate::object_protocol::TerminalObjectId {
                claim: crate::object_protocol::TerminalClaimId {
                    height: 1,
                    semantic_header_id: semantic_header_id(&header),
                    proof_class: 0,
                },
                byte_digest: [8; 32],
                encoded_len: 512,
            },
            providers: crate::header_protocol::ProviderFlags::new(true, true, false),
        }
    }

    #[test]
    fn request_and_response_round_trip() {
        block_on(async {
            let protocol = StreamProtocol::new("/test/availability/1");
            let request = AvailabilityRequest {
                announcement: announcement(),
            };
            let mut encoded = Cursor::new(Vec::new());
            AvailabilityCodec
                .write_request(&protocol, &mut encoded, request)
                .await
                .unwrap();
            encoded.set_position(0);
            let decoded = AvailabilityCodec
                .read_request(&protocol, &mut encoded)
                .await
                .unwrap();
            assert_eq!(decoded, request);

            for response in [AvailabilityResponse::Accepted, AvailabilityResponse::Busy] {
                let mut encoded = Cursor::new(Vec::new());
                AvailabilityCodec
                    .write_response(&protocol, &mut encoded, response)
                    .await
                    .unwrap();
                encoded.set_position(0);
                let decoded = AvailabilityCodec
                    .read_response(&protocol, &mut encoded)
                    .await
                    .unwrap();
                assert_eq!(decoded, response);
            }
        });
    }
}
