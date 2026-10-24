// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! One-time, bounded transport of the certificate selected by a v2 terminal.
//! Its request hash is a lookup key, never proof of validity. Node admission
//! authenticates the complete certificate before using the origin.

use crate::{
    behaviour::NodeBehaviour,
    inbound_budget::process_global_inbound_budget,
    outbound_budget::{OutboundMemoryPermit, OutboundResponseBudget},
};
use async_trait::async_trait;
use futures::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use libp2p::{request_response, PeerId, StreamProtocol};
use std::{collections::HashMap, io, path::PathBuf, sync::Arc};
use tokio::sync::{mpsc, oneshot, Semaphore};

pub const MAX_ORIGIN_BYTES: usize =
    noid_chain::consensus::wire_limits::MAX_V2_FORK_ORIGIN_TRANSPORT_BYTES;
const MAGIC: &[u8; 8] = b"O1ORGET1";
const MAX_PENDING: usize = 4;

#[derive(Debug)]
pub struct ForkOriginResponse {
    pub request: [u8; 32],
    pub bytes: Option<Vec<u8>>,
    _inbound: Option<Arc<tokio::sync::OwnedSemaphorePermit>>,
    _outbound: Option<OutboundMemoryPermit>,
}

impl ForkOriginResponse {
    fn unavailable(request: [u8; 32]) -> Self {
        Self {
            request,
            bytes: None,
            _inbound: None,
            _outbound: None,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct ForkOriginCodec;

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

async fn eof<T: AsyncRead + Unpin>(io: &mut T) -> io::Result<()> {
    let mut byte = [0];
    if io.read(&mut byte).await? != 0 {
        return Err(invalid("fork-origin trailing bytes"));
    }
    Ok(())
}

async fn read_key<T: AsyncRead + Unpin>(io: &mut T) -> io::Result<[u8; 32]> {
    let mut prefix = [0; 40];
    io.read_exact(&mut prefix).await?;
    if &prefix[..8] != MAGIC {
        return Err(invalid("fork-origin protocol magic"));
    }
    Ok(prefix[8..].try_into().unwrap())
}

#[async_trait]
impl request_response::Codec for ForkOriginCodec {
    type Protocol = StreamProtocol;
    type Request = [u8; 32];
    type Response = ForkOriginResponse;

    async fn read_request<T: AsyncRead + Unpin + Send>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Request> {
        let request = read_key(io).await?;
        eof(io).await?;
        Ok(request)
    }
    async fn read_response<T: AsyncRead + Unpin + Send>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Response> {
        let request = read_key(io).await?;
        let mut length = [0; 4];
        io.read_exact(&mut length).await?;
        let length = u32::from_le_bytes(length) as usize;
        if length > MAX_ORIGIN_BYTES {
            return Err(invalid("fork-origin response bound"));
        }
        let mut response = ForkOriginResponse::unavailable(request);
        if length > 0 {
            let permit = process_global_inbound_budget()
                .acquire_many_owned(length as u32)
                .await
                .map_err(|_| invalid("fork-origin inbound budget closed"))?;
            let mut bytes = Vec::new();
            bytes
                .try_reserve_exact(length)
                .map_err(|_| invalid("fork-origin allocation"))?;
            bytes.resize(length, 0);
            io.read_exact(&mut bytes).await?;
            response.bytes = Some(bytes);
            response._inbound = Some(Arc::new(permit));
        }
        eof(io).await?;
        Ok(response)
    }
    async fn write_request<T: AsyncWrite + Unpin + Send>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
        request: Self::Request,
    ) -> io::Result<()> {
        io.write_all(MAGIC).await?;
        io.write_all(&request).await?;
        io.flush().await
    }
    async fn write_response<T: AsyncWrite + Unpin + Send>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
        response: Self::Response,
    ) -> io::Result<()> {
        let bytes = response.bytes.as_deref().unwrap_or_default();
        if bytes.len() > MAX_ORIGIN_BYTES || response.bytes.as_ref().is_some_and(Vec::is_empty) {
            return Err(invalid("fork-origin outbound bound"));
        }
        io.write_all(MAGIC).await?;
        io.write_all(&response.request).await?;
        io.write_all(&(bytes.len() as u32).to_le_bytes()).await?;
        io.write_all(bytes).await?;
        io.flush().await?;
        drop(response);
        Ok(())
    }
}

type Reply = oneshot::Sender<Result<ForkOriginResponse, String>>;
struct Pending {
    peer: PeerId,
    request: [u8; 32],
    reply: Reply,
}
pub(crate) struct PreparedResponse {
    pub channel: request_response::ResponseChannel<ForkOriginResponse>,
    pub response: ForkOriginResponse,
}

pub(crate) struct ForkOriginTransfers {
    pending: HashMap<request_response::OutboundRequestId, Pending>,
    directory: PathBuf,
    serving: Arc<Semaphore>,
    sender: mpsc::Sender<PreparedResponse>,
    pub receiver: mpsc::Receiver<PreparedResponse>,
}

impl ForkOriginTransfers {
    pub fn new(directory: PathBuf) -> Self {
        let (sender, receiver) = mpsc::channel(1);
        Self {
            pending: HashMap::new(),
            directory,
            serving: Arc::new(Semaphore::new(2)),
            sender,
            receiver,
        }
    }
    pub fn request(
        &mut self,
        swarm: &mut libp2p::Swarm<NodeBehaviour>,
        peer: PeerId,
        request: [u8; 32],
        reply: Reply,
        dispatchable: bool,
    ) {
        if !dispatchable
            || self.pending.len() >= MAX_PENDING
            || self.pending.values().any(|p| p.peer == peer)
        {
            let _ = reply.send(Err(
                "fork-origin peer or request capacity unavailable".into()
            ));
            return;
        }
        let id = swarm
            .behaviour_mut()
            .fork_origin_sync
            .send_request(&peer, request);
        self.pending.insert(
            id,
            Pending {
                peer,
                request,
                reply,
            },
        );
    }

    pub fn event(
        &mut self,
        swarm: &mut libp2p::Swarm<NodeBehaviour>,
        event: request_response::Event<[u8; 32], ForkOriginResponse>,
        dispatchable: impl Fn(PeerId) -> bool,
    ) {
        use request_response::{Event, Message};
        match event {
            Event::Message {
                peer,
                message:
                    Message::Request {
                        request, channel, ..
                    },
                ..
            } => {
                let serving = Arc::clone(&self.serving).try_acquire_owned();
                if !dispatchable(peer)
                    || serving.is_err()
                    || noid_chain::consensus::params::V2_ACTIVATION_HEIGHT.is_none()
                {
                    let _ = swarm
                        .behaviour_mut()
                        .fork_origin_sync
                        .send_response(channel, ForkOriginResponse::unavailable(request));
                    return;
                }
                let serving = serving.unwrap();
                let directory = self.directory.clone();
                let sender = self.sender.clone();
                tokio::spawn(async move {
                    let mut response = ForkOriginResponse::unavailable(request);
                    let opened =
                        tokio::task::spawn_blocking(move || open_certificate(directory, request))
                            .await;
                    let opened = opened.ok().and_then(Result::ok).flatten();
                    let length = opened.as_ref().map_or(0, |(_, length)| *length);
                    let budget = OutboundResponseBudget::process_global();
                    let reserved = budget
                        .acquire_with_serving(length.max(44), vec![serving])
                        .await;
                    if let Ok(permit) = reserved {
                        if let Some((file, length)) = opened {
                            let read =
                                tokio::task::spawn_blocking(move || read_certificate(file, length))
                                    .await;
                            if let Ok(Ok(bytes)) = read {
                                response.bytes = Some(bytes);
                            }
                        }
                        response._outbound = permit;
                    }
                    let _ = sender.send(PreparedResponse { channel, response }).await;
                });
            }
            Event::Message {
                peer,
                message:
                    Message::Response {
                        request_id,
                        response,
                    },
                ..
            } => {
                if let Some(pending) = self.pending.remove(&request_id) {
                    let result = if peer == pending.peer
                        && response.request == pending.request
                        && dispatchable(peer)
                    {
                        Ok(response)
                    } else {
                        Err("fork-origin response correlation mismatch".into())
                    };
                    let _ = pending.reply.send(result);
                }
            }
            Event::OutboundFailure {
                request_id, error, ..
            } => {
                if let Some(pending) = self.pending.remove(&request_id) {
                    let _ = pending.reply.send(Err(error.to_string()));
                }
            }
            _ => {}
        }
    }
}

fn open_certificate(
    directory: PathBuf,
    request: [u8; 32],
) -> Result<Option<(std::fs::File, usize)>, io::Error> {
    let name: String = request.iter().map(|byte| format!("{byte:02x}")).collect();
    let path = directory.join(format!("{name}.origin"));
    let metadata = match std::fs::symlink_metadata(&path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error),
    };
    if !metadata.is_file() || metadata.len() == 0 || metadata.len() > MAX_ORIGIN_BYTES as u64 {
        return Err(invalid("fork-origin file bound"));
    }
    let file = std::fs::File::open(path)?;
    let length = file.metadata()?.len();
    if length == 0 || length > MAX_ORIGIN_BYTES as u64 {
        return Err(invalid("fork-origin opened file bound"));
    }
    Ok(Some((file, length as usize)))
}

fn read_certificate(mut file: std::fs::File, length: usize) -> io::Result<Vec<u8>> {
    use std::io::Read;
    if length == 0 || length > MAX_ORIGIN_BYTES {
        return Err(invalid("fork-origin reserved length"));
    }
    // The memory/serving permits are already held for this exact allocation.
    // A changed file is rejected without growing a Vec beyond its allowance.
    let mut bytes = vec![0; length];
    file.read_exact(&mut bytes)?;
    let mut extra = [0];
    if file.read(&mut extra)? != 0 {
        return Err(invalid("fork-origin file grew"));
    }
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::io::Cursor;
    use libp2p::request_response::Codec;

    #[test]
    fn certificate_read_cannot_outgrow_its_reserved_bytes() {
        use std::io::Write;
        let directory = tempfile::tempdir().unwrap();
        let request = [6; 32];
        let name: String = request.iter().map(|byte| format!("{byte:02x}")).collect();
        let path = directory.path().join(format!("{name}.origin"));
        std::fs::write(&path, [8; 71]).unwrap();
        let (file, length) = open_certificate(directory.path().to_owned(), request)
            .unwrap()
            .unwrap();
        assert_eq!(length, 71);
        assert_eq!(read_certificate(file, length).unwrap(), [8; 71]);

        let (file, length) = open_certificate(directory.path().to_owned(), request)
            .unwrap()
            .unwrap();
        std::fs::OpenOptions::new()
            .append(true)
            .open(&path)
            .unwrap()
            .write_all(&[9])
            .unwrap();
        assert!(read_certificate(file, length)
            .unwrap_err()
            .to_string()
            .contains("grew"));

        let (file, length) = open_certificate(directory.path().to_owned(), request)
            .unwrap()
            .unwrap();
        std::fs::File::create(&path).unwrap().set_len(4).unwrap();
        assert_eq!(
            read_certificate(file, length).unwrap_err().kind(),
            io::ErrorKind::UnexpectedEof
        );
        assert!(
            read_certificate(std::fs::File::open(&path).unwrap(), MAX_ORIGIN_BYTES + 1).is_err()
        );
    }

    #[tokio::test]
    async fn certificate_transport_is_bounded_and_request_correlated() {
        let protocol = StreamProtocol::new("/test/fork-origin/1");
        let request = [7; 32];
        let mut encoded = Cursor::new(Vec::new());
        ForkOriginCodec
            .write_response(
                &protocol,
                &mut encoded,
                ForkOriginResponse {
                    request,
                    bytes: Some(vec![9; 543]),
                    _inbound: None,
                    _outbound: None,
                },
            )
            .await
            .unwrap();
        let wire = encoded.into_inner();
        let decoded = ForkOriginCodec
            .read_response(&protocol, &mut Cursor::new(&wire))
            .await
            .unwrap();
        assert_eq!(decoded.request, request);
        assert_eq!(decoded.bytes.as_deref(), Some(vec![9; 543].as_slice()));
        assert!(decoded._inbound.is_some());
        for length in [0, 7, 39, 43, wire.len() - 1] {
            assert!(ForkOriginCodec
                .read_response(&protocol, &mut Cursor::new(&wire[..length]))
                .await
                .is_err());
        }
        let mut over = wire.clone();
        over[40..44].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(ForkOriginCodec
            .read_response(&protocol, &mut Cursor::new(over))
            .await
            .is_err());
        let mut trailing = wire.clone();
        trailing.push(0);
        assert!(ForkOriginCodec
            .read_response(&protocol, &mut Cursor::new(trailing))
            .await
            .is_err());
        let mut request_wire = Cursor::new(Vec::new());
        ForkOriginCodec
            .write_request(&protocol, &mut request_wire, request)
            .await
            .unwrap();
        assert_eq!(
            ForkOriginCodec
                .read_request(&protocol, &mut Cursor::new(request_wire.into_inner()))
                .await
                .unwrap(),
            request
        );
    }

    #[tokio::test]
    async fn unavailable_has_no_payload_and_no_memory_permit() {
        let protocol = StreamProtocol::new("/test/fork-origin/1");
        let mut bytes = Cursor::new(Vec::new());
        ForkOriginCodec
            .write_response(
                &protocol,
                &mut bytes,
                ForkOriginResponse::unavailable([4; 32]),
            )
            .await
            .unwrap();
        assert_eq!(bytes.get_ref().len(), 44);
        let decoded = ForkOriginCodec
            .read_response(&protocol, &mut Cursor::new(bytes.into_inner()))
            .await
            .unwrap();
        assert!(decoded.bytes.is_none());
        assert!(decoded._inbound.is_none());
    }
}
