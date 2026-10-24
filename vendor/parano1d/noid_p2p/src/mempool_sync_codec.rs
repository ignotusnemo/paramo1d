// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Allocation-bounded fixed framing for mempool synchronization.
//!
//! The response declares its complete vector of intent lengths before any
//! intent payload is allocated.  Count, per-intent, aggregate, arithmetic,
//! truncation, and trailing-byte checks therefore happen at the wire boundary,
//! and payload slices are written directly without a second CBOR-sized buffer.

use std::{io, sync::Arc};

use async_trait::async_trait;
use futures::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use libp2p::{request_response, swarm::StreamProtocol};
use noid_chain::consensus::wire_limits::{
    MAX_MEMPOOL_SYNC_BYTES, MAX_MEMPOOL_SYNC_TXS, MAX_MEMPOOL_TXS, MAX_TX_INTENT_BYTES_GLOBAL,
};

use crate::{
    inbound_budget::process_global_inbound_budget,
    outbound_budget::OutboundResponseBudget,
    protocol::{GetMempoolResponse, MempoolRequest},
};

const REQUEST_MAGIC: [u8; 4] = *b"NMR3";
const RESPONSE_MAGIC: [u8; 4] = *b"NMS3";
const REQUEST_PREFIX_BYTES: usize = 12;
const REQUEST_KIND_PULL: u8 = 0;
const REQUEST_KIND_PUSH: u8 = 1;
const REQUEST_KIND_MISSING: u8 = 2;
const RESPONSE_PREFIX_BYTES: usize = 8;
const LENGTH_BYTES: usize = 4;
const MAX_LENGTH_TABLE_BYTES: usize = MAX_MEMPOOL_SYNC_TXS * LENGTH_BYTES;

fn supports_missing(protocol: &StreamProtocol) -> bool {
    protocol.as_ref().ends_with("/sync/mempool/4")
}

fn validate_known(known: &[[u8; 32]]) -> io::Result<()> {
    if known.len() > MAX_MEMPOOL_TXS || known.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(invalid_data(
            "mempool known IDs exceed cap or are not sorted and unique",
        ));
    }
    Ok(())
}

#[derive(Debug, Clone)]
pub struct MempoolSyncCodec {
    inbound_budget: Arc<tokio::sync::Semaphore>,
    outbound_budget: OutboundResponseBudget,
}

impl Default for MempoolSyncCodec {
    fn default() -> Self {
        Self {
            inbound_budget: process_global_inbound_budget(),
            outbound_budget: OutboundResponseBudget::process_global(),
        }
    }
}

impl MempoolSyncCodec {
    #[cfg(test)]
    fn with_budgets(inbound_bytes: usize, outbound_budget: OutboundResponseBudget) -> Self {
        Self {
            inbound_budget: Arc::new(tokio::sync::Semaphore::new(inbound_bytes)),
            outbound_budget,
        }
    }

    async fn acquire_inbound(
        &self,
        bytes: usize,
    ) -> io::Result<Option<Arc<tokio::sync::OwnedSemaphorePermit>>> {
        if bytes == 0 {
            return Ok(None);
        }
        let permits = u32::try_from(bytes)
            .map_err(|_| invalid_data("mempool response byte budget overflow"))?;
        let permit = self
            .inbound_budget
            .clone()
            .acquire_many_owned(permits)
            .await
            .map_err(|_| io::Error::new(io::ErrorKind::BrokenPipe, "mempool budget closed"))?;
        Ok(Some(Arc::new(permit)))
    }
}

#[async_trait]
impl request_response::Codec for MempoolSyncCodec {
    type Protocol = StreamProtocol;
    type Request = MempoolRequest;
    type Response = GetMempoolResponse;

    async fn read_request<T>(
        &mut self,
        protocol: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Request>
    where
        T: AsyncRead + Unpin + Send,
    {
        let mut prefix = [0u8; REQUEST_PREFIX_BYTES];
        io.read_exact(&mut prefix).await?;
        if prefix[..4] != REQUEST_MAGIC {
            return Err(invalid_data("invalid mempool-sync request magic/version"));
        }
        if prefix[5..8] != [0, 0, 0] {
            return Err(invalid_data("non-zero mempool-sync request reserved bytes"));
        }
        let payload_len =
            u32::from_le_bytes(prefix[8..12].try_into().expect("fixed request length")) as usize;
        let request = match prefix[4] {
            REQUEST_KIND_PULL if payload_len == 0 => MempoolRequest::Pull,
            REQUEST_KIND_PULL => {
                return Err(invalid_data("mempool pull request carries a payload"));
            }
            REQUEST_KIND_MISSING if supports_missing(protocol) => {
                if payload_len > MAX_MEMPOOL_TXS * 32 || !payload_len.is_multiple_of(32) {
                    return Err(invalid_data("mempool known-ID length is outside bounds"));
                }
                // Stream limits are per connection. Request metadata must
                // therefore also enter the process-wide byte domain before
                // allocation, rather than scaling unchecked with peer count.
                let inbound_memory_permit = self.acquire_inbound(payload_len).await?;
                let mut known_txids = Vec::with_capacity(payload_len / 32);
                for _ in 0..payload_len / 32 {
                    let mut txid = [0; 32];
                    io.read_exact(&mut txid).await?;
                    known_txids.push(txid);
                }
                validate_known(&known_txids)?;
                MempoolRequest::PullMissing {
                    known_txids,
                    inbound_memory_permit,
                }
            }
            REQUEST_KIND_PUSH => {
                validate_intent_length(payload_len)?;
                let inbound_memory_permit = self.acquire_inbound(payload_len).await?;
                let mut intent_bytes = Vec::new();
                intent_bytes.try_reserve_exact(payload_len).map_err(|_| {
                    io::Error::new(
                        io::ErrorKind::OutOfMemory,
                        "pushed mempool intent allocation failed",
                    )
                })?;
                intent_bytes.resize(payload_len, 0);
                io.read_exact(&mut intent_bytes).await?;
                MempoolRequest::Push {
                    intent_bytes,
                    inbound_memory_permit,
                }
            }
            _ => return Err(invalid_data("unknown mempool-sync request kind")),
        };
        ensure_eof(io).await?;
        Ok(request)
    }

    async fn read_response<T>(
        &mut self,
        protocol: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Response>
    where
        T: AsyncRead + Unpin + Send,
    {
        let mut prefix = [0u8; RESPONSE_PREFIX_BYTES];
        io.read_exact(&mut prefix).await?;
        let count = parse_response_prefix(&prefix)?;

        // The largest valid table is only 512 bytes. Keep it on the stack so
        // an untrusted count cannot itself trigger a heap allocation.
        let table_len = count
            .checked_mul(LENGTH_BYTES)
            .ok_or_else(|| invalid_data("mempool response length-table overflow"))?;
        let mut length_table = [0u8; MAX_LENGTH_TABLE_BYTES];
        io.read_exact(&mut length_table[..table_len]).await?;
        let (lengths, total_bytes) = parse_lengths(count, &length_table[..table_len])?;

        // Admission precedes the first payload Vec allocation and the owned
        // permit follows the decoded response into the node event.
        let inbound_memory_permit = self.acquire_inbound(total_bytes).await?;
        let mut txs = Vec::new();
        txs.try_reserve_exact(count).map_err(|_| {
            io::Error::new(
                io::ErrorKind::OutOfMemory,
                "mempool vector allocation failed",
            )
        })?;
        for &len in &lengths[..count] {
            let mut intent = Vec::new();
            intent.try_reserve_exact(len).map_err(|_| {
                io::Error::new(io::ErrorKind::OutOfMemory, "intent allocation failed")
            })?;
            intent.resize(len, 0);
            io.read_exact(&mut intent).await?;
            txs.push(intent);
        }
        ensure_eof(io).await?;

        Ok(GetMempoolResponse {
            txs,
            supports_missing: supports_missing(protocol),
            inbound_memory_permit,
            outbound_memory_permit: None,
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
        let (kind, intent_bytes) = match request {
            MempoolRequest::Pull => (REQUEST_KIND_PULL, None),
            MempoolRequest::PullMissing {
                known_txids,
                inbound_memory_permit,
            } => {
                drop(inbound_memory_permit);
                validate_known(&known_txids)?;
                if supports_missing(protocol) {
                    let payload = known_txids.into_iter().flatten().collect();
                    (REQUEST_KIND_MISSING, Some(payload))
                } else {
                    // Negotiation with an unupgraded peer preserves the exact
                    // v3 request. Its response will disable continuation.
                    (REQUEST_KIND_PULL, None)
                }
            }
            MempoolRequest::Push {
                intent_bytes,
                inbound_memory_permit,
            } => {
                drop(inbound_memory_permit);
                validate_intent_length(intent_bytes.len())?;
                (REQUEST_KIND_PUSH, Some(intent_bytes))
            }
        };
        let payload_len = intent_bytes.as_ref().map_or(0, Vec::len);
        let payload_len = u32::try_from(payload_len)
            .map_err(|_| invalid_data("mempool request length does not fit u32"))?;
        let mut prefix = [0u8; REQUEST_PREFIX_BYTES];
        prefix[..4].copy_from_slice(&REQUEST_MAGIC);
        prefix[4] = kind;
        prefix[8..12].copy_from_slice(&payload_len.to_le_bytes());
        io.write_all(&prefix).await?;
        if let Some(intent_bytes) = intent_bytes {
            io.write_all(&intent_bytes).await?;
        }
        Ok(())
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
        let GetMempoolResponse {
            txs,
            inbound_memory_permit,
            outbound_memory_permit,
            supports_missing: _,
        } = response;
        let (lengths, total_bytes) = validate_outbound(&txs)?;
        // Production serving acquires the maximum reservation before cloning
        // from the mempool. This fallback keeps future direct call sites inside
        // the same process-wide byte domain.
        let outbound_memory_permit = match outbound_memory_permit {
            Some(permit) => Some(permit),
            None => self.outbound_budget.acquire(total_bytes).await?,
        };
        let _memory_permits = (inbound_memory_permit, outbound_memory_permit);

        let count = u16::try_from(txs.len())
            .map_err(|_| invalid_data("mempool response count does not fit u16"))?;
        let mut header = [0u8; RESPONSE_PREFIX_BYTES + MAX_LENGTH_TABLE_BYTES];
        header[..4].copy_from_slice(&RESPONSE_MAGIC);
        header[4..6].copy_from_slice(&count.to_le_bytes());
        for (index, len) in lengths.iter().enumerate() {
            let offset = RESPONSE_PREFIX_BYTES + index * LENGTH_BYTES;
            header[offset..offset + LENGTH_BYTES].copy_from_slice(&len.to_le_bytes());
        }
        let header_len = RESPONSE_PREFIX_BYTES + txs.len() * LENGTH_BYTES;
        io.write_all(&header[..header_len]).await?;
        for intent in &txs {
            io.write_all(intent).await?;
        }
        Ok(())
    }
}

fn parse_response_prefix(prefix: &[u8; RESPONSE_PREFIX_BYTES]) -> io::Result<usize> {
    if prefix[..4] != RESPONSE_MAGIC {
        return Err(invalid_data("invalid mempool-sync response magic/version"));
    }
    if prefix[6..8] != [0, 0] {
        return Err(invalid_data("non-zero mempool-sync reserved bytes"));
    }
    let count = u16::from_le_bytes(prefix[4..6].try_into().expect("fixed response count")) as usize;
    if count > MAX_MEMPOOL_SYNC_TXS {
        return Err(invalid_data("declared mempool response count exceeds cap"));
    }
    Ok(count)
}

fn parse_lengths(count: usize, table: &[u8]) -> io::Result<([usize; MAX_MEMPOOL_SYNC_TXS], usize)> {
    if table.len() != count * LENGTH_BYTES {
        return Err(invalid_data("mempool response length table is truncated"));
    }
    let mut lengths = [0usize; MAX_MEMPOOL_SYNC_TXS];
    let mut total = 0usize;
    for (index, field) in table.chunks_exact(LENGTH_BYTES).enumerate() {
        let len = u32::from_le_bytes(field.try_into().expect("fixed intent length")) as usize;
        validate_intent_length(len)?;
        total = total
            .checked_add(len)
            .ok_or_else(|| invalid_data("mempool response aggregate length overflow"))?;
        if total > MAX_MEMPOOL_SYNC_BYTES {
            return Err(invalid_data("declared mempool response bytes exceed cap"));
        }
        lengths[index] = len;
    }
    Ok((lengths, total))
}

fn validate_outbound(txs: &[Vec<u8>]) -> io::Result<(Vec<u32>, usize)> {
    if txs.len() > MAX_MEMPOOL_SYNC_TXS {
        return Err(invalid_data("mempool response count exceeds cap"));
    }
    let mut lengths = Vec::with_capacity(txs.len());
    let mut total = 0usize;
    for intent in txs {
        validate_intent_length(intent.len())?;
        total = total
            .checked_add(intent.len())
            .ok_or_else(|| invalid_data("mempool response aggregate length overflow"))?;
        if total > MAX_MEMPOOL_SYNC_BYTES {
            return Err(invalid_data("mempool response bytes exceed cap"));
        }
        lengths.push(
            u32::try_from(intent.len())
                .map_err(|_| invalid_data("intent length does not fit u32"))?,
        );
    }
    Ok((lengths, total))
}

fn validate_intent_length(len: usize) -> io::Result<()> {
    if len == 0 {
        return Err(invalid_data("zero-length mempool intent"));
    }
    if len > MAX_TX_INTENT_BYTES_GLOBAL {
        return Err(invalid_data("declared mempool intent length exceeds cap"));
    }
    Ok(())
}

async fn ensure_eof<T: AsyncRead + Unpin + Send>(io: &mut T) -> io::Result<()> {
    let mut trailing = [0u8; 1];
    if io.read(&mut trailing).await? != 0 {
        return Err(invalid_data("trailing bytes in mempool-sync message"));
    }
    Ok(())
}

fn invalid_data(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.to_owned())
}

#[cfg(test)]
mod tests {
    use std::{
        pin::Pin,
        sync::{
            atomic::{AtomicBool, Ordering},
            Mutex,
        },
        task::{Context, Poll, Waker},
    };

    use futures::io::Cursor;
    use libp2p::request_response::Codec;

    use super::*;

    fn protocol() -> StreamProtocol {
        StreamProtocol::new("/noid/test/sync/mempool/3")
    }

    fn request_wire(kind: u8, payload_len: u32, payload: &[u8]) -> Vec<u8> {
        let mut wire = vec![0u8; REQUEST_PREFIX_BYTES];
        wire[..4].copy_from_slice(&REQUEST_MAGIC);
        wire[4] = kind;
        wire[8..12].copy_from_slice(&payload_len.to_le_bytes());
        wire.extend_from_slice(payload);
        wire
    }

    fn response_wire(lengths: &[u32], payload: &[u8]) -> Vec<u8> {
        let mut wire = vec![0u8; RESPONSE_PREFIX_BYTES];
        wire[..4].copy_from_slice(&RESPONSE_MAGIC);
        wire[4..6].copy_from_slice(&(lengths.len() as u16).to_le_bytes());
        for len in lengths {
            wire.extend_from_slice(&len.to_le_bytes());
        }
        wire.extend_from_slice(payload);
        wire
    }

    fn response(txs: Vec<Vec<u8>>) -> GetMempoolResponse {
        GetMempoolResponse {
            txs,
            supports_missing: false,
            inbound_memory_permit: None,
            outbound_memory_permit: None,
        }
    }

    struct GatedWriter {
        started: Arc<AtomicBool>,
        released: Arc<AtomicBool>,
        waker: Arc<Mutex<Option<Waker>>>,
    }

    impl AsyncWrite for GatedWriter {
        fn poll_write(
            self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            bytes: &[u8],
        ) -> Poll<io::Result<usize>> {
            self.started.store(true, Ordering::SeqCst);
            if !self.released.load(Ordering::SeqCst) {
                *self.waker.lock().unwrap() = Some(cx.waker().clone());
                return Poll::Pending;
            }
            Poll::Ready(Ok(bytes.len()))
        }

        fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            Poll::Ready(Ok(()))
        }

        fn poll_close(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            Poll::Ready(Ok(()))
        }
    }

    #[tokio::test]
    async fn round_trip_preserves_source_order_without_cbor_envelope() {
        let source = vec![vec![0x11; 3], vec![0x22; 7], vec![0x33; 1]];
        let mut wire = Cursor::new(Vec::new());
        MempoolSyncCodec::default()
            .write_response(&protocol(), &mut wire, response(source.clone()))
            .await
            .unwrap();
        assert_eq!(
            wire.get_ref().len(),
            RESPONSE_PREFIX_BYTES + source.len() * LENGTH_BYTES + 11
        );
        wire.set_position(0);
        let decoded = MempoolSyncCodec::default()
            .read_response(&protocol(), &mut wire)
            .await
            .unwrap();
        assert_eq!(decoded.txs, source);
    }

    #[tokio::test]
    async fn pull_request_is_exact_fixed_frame() {
        let mut wire = Cursor::new(Vec::new());
        MempoolSyncCodec::default()
            .write_request(&protocol(), &mut wire, MempoolRequest::Pull)
            .await
            .unwrap();
        assert_eq!(wire.get_ref(), &request_wire(REQUEST_KIND_PULL, 0, &[]));
        wire.set_position(0);
        let decoded = MempoolSyncCodec::default()
            .read_request(&protocol(), &mut wire)
            .await
            .unwrap();
        assert!(matches!(decoded, MempoolRequest::Pull));

        let trailing = request_wire(REQUEST_KIND_PULL, 0, &[0]);
        assert_eq!(
            MempoolSyncCodec::default()
                .read_request(&protocol(), &mut Cursor::new(trailing))
                .await
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidData
        );
    }

    #[tokio::test]
    async fn pushed_intent_round_trips_and_retains_inbound_budget() {
        let source = vec![0x5a; 31];
        let mut wire = Cursor::new(Vec::new());
        MempoolSyncCodec::default()
            .write_request(
                &protocol(),
                &mut wire,
                MempoolRequest::Push {
                    intent_bytes: source.clone(),
                    inbound_memory_permit: None,
                },
            )
            .await
            .unwrap();
        assert_eq!(
            wire.get_ref(),
            &request_wire(REQUEST_KIND_PUSH, source.len() as u32, &source)
        );
        wire.set_position(0);
        let decoded = MempoolSyncCodec::default()
            .read_request(&protocol(), &mut wire)
            .await
            .unwrap();
        let MempoolRequest::Push {
            intent_bytes,
            inbound_memory_permit,
        } = decoded
        else {
            panic!("push decoded as pull");
        };
        assert_eq!(intent_bytes, source);
        assert!(inbound_memory_permit.is_some());
    }

    #[tokio::test]
    async fn pushed_intent_length_is_bounded_before_allocation() {
        let oversized = request_wire(
            REQUEST_KIND_PUSH,
            (MAX_TX_INTENT_BYTES_GLOBAL + 1) as u32,
            &[],
        );
        let error = MempoolSyncCodec::default()
            .read_request(&protocol(), &mut Cursor::new(oversized))
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("intent length"));
    }

    #[tokio::test]
    async fn length_bombs_are_rejected_before_payload_allocation() {
        let count_bomb = response_wire(&vec![1; MAX_MEMPOOL_SYNC_TXS + 1], &[]);
        let error = MempoolSyncCodec::default()
            .read_response(&protocol(), &mut Cursor::new(count_bomb))
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("count"));

        let per_intent = response_wire(&[(MAX_TX_INTENT_BYTES_GLOBAL + 1) as u32], &[]);
        let error = MempoolSyncCodec::default()
            .read_response(&protocol(), &mut Cursor::new(per_intent))
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("intent length"));

        let aggregate_lengths = vec![MAX_TX_INTENT_BYTES_GLOBAL as u32; 65];
        let aggregate = response_wire(&aggregate_lengths, &[]);
        let error = MempoolSyncCodec::default()
            .read_response(&protocol(), &mut Cursor::new(aggregate))
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("bytes"));
    }

    #[tokio::test]
    async fn truncation_and_trailing_bytes_are_rejected() {
        let truncated_table = response_wire(&[3], &[])[..RESPONSE_PREFIX_BYTES + 2].to_vec();
        assert_eq!(
            MempoolSyncCodec::default()
                .read_response(&protocol(), &mut Cursor::new(truncated_table))
                .await
                .unwrap_err()
                .kind(),
            io::ErrorKind::UnexpectedEof
        );

        let truncated_payload = response_wire(&[3], &[1, 2]);
        assert_eq!(
            MempoolSyncCodec::default()
                .read_response(&protocol(), &mut Cursor::new(truncated_payload))
                .await
                .unwrap_err()
                .kind(),
            io::ErrorKind::UnexpectedEof
        );

        let trailing = response_wire(&[2], &[1, 2, 3]);
        let error = MempoolSyncCodec::default()
            .read_response(&protocol(), &mut Cursor::new(trailing))
            .await
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("trailing"));
    }

    #[tokio::test]
    async fn missing_request_negotiates_without_changing_legacy_bytes() {
        let v4 = StreamProtocol::new("/noid/test/sync/mempool/4");
        let v3 = protocol();
        let known_txids = vec![[1; 32], [2; 32]];
        let mut wire = Cursor::new(Vec::new());
        let mut codec = MempoolSyncCodec::default();
        codec
            .write_request(
                &v4,
                &mut wire,
                MempoolRequest::PullMissing {
                    known_txids: known_txids.clone(),
                    inbound_memory_permit: None,
                },
            )
            .await
            .unwrap();
        assert_eq!(wire.get_ref().len(), REQUEST_PREFIX_BYTES + 64);
        wire.set_position(0);
        let MempoolRequest::PullMissing {
            known_txids: restored,
            ..
        } = codec.read_request(&v4, &mut wire).await.unwrap()
        else {
            panic!("not missing")
        };
        assert_eq!(restored, known_txids);
        wire.set_position(0);
        assert!(codec.read_request(&v3, &mut wire).await.is_err());

        let mut fallback = Cursor::new(Vec::new());
        codec
            .write_request(&v3, &mut fallback, MempoolRequest::missing(known_txids))
            .await
            .unwrap();
        let mut legacy = Cursor::new(Vec::new());
        codec
            .write_request(&v3, &mut legacy, MempoolRequest::Pull)
            .await
            .unwrap();
        assert_eq!(fallback.get_ref(), legacy.get_ref());

        let bytes = response_wire(&[], &[]);
        assert!(
            codec
                .read_response(&v4, &mut Cursor::new(&bytes))
                .await
                .unwrap()
                .supports_missing
        );
        assert!(
            !codec
                .read_response(&v3, &mut Cursor::new(&bytes))
                .await
                .unwrap()
                .supports_missing
        );
    }

    #[tokio::test]
    async fn missing_metadata_is_bounded_and_canonical_before_payload_work() {
        let v4 = StreamProtocol::new("/noid/test/sync/mempool/4");
        let mut codec = MempoolSyncCodec::default();
        for len in [1usize, MAX_MEMPOOL_TXS * 32 + 32, u32::MAX as usize] {
            let mut wire = vec![0; REQUEST_PREFIX_BYTES];
            wire[..4].copy_from_slice(&REQUEST_MAGIC);
            wire[4] = REQUEST_KIND_MISSING;
            wire[8..12].copy_from_slice(&(len as u32).to_le_bytes());
            assert_eq!(
                codec
                    .read_request(&v4, &mut Cursor::new(wire))
                    .await
                    .unwrap_err()
                    .kind(),
                io::ErrorKind::InvalidData
            );
        }
        for known in [
            vec![[1; 32], [1; 32]],
            vec![[2; 32], [1; 32]],
            vec![[0; 32]; MAX_MEMPOOL_TXS + 1],
        ] {
            assert!(codec
                .write_request(
                    &v4,
                    &mut Cursor::new(Vec::new()),
                    MempoolRequest::missing(known)
                )
                .await
                .is_err());
        }
        // A valid maximum request remains metadata-only but its allocation
        // must still be charged to the shared 64 MiB inbound domain.
        let known_txids: Vec<_> = (0..MAX_MEMPOOL_TXS as u64)
            .map(|i| {
                let mut id = [0; 32];
                id[..8].copy_from_slice(&i.to_be_bytes());
                id
            })
            .collect();
        let mut wire = Cursor::new(Vec::new());
        codec
            .write_request(&v4, &mut wire, MempoolRequest::missing(known_txids))
            .await
            .unwrap();
        wire.set_position(0);
        assert!(codec.read_request(&v4, &mut wire).await.is_ok());
    }

    #[tokio::test]
    async fn missing_request_metadata_holds_shared_budget_until_serving_finishes() {
        let v4 = StreamProtocol::new("/noid/test/sync/mempool/4");
        let mut codec =
            MempoolSyncCodec::with_budgets(32, OutboundResponseBudget::with_capacity(32));
        let mut wire = Cursor::new(Vec::new());
        codec
            .write_request(&v4, &mut wire, MempoolRequest::missing(vec![[1; 32]]))
            .await
            .unwrap();
        let bytes = wire.into_inner();
        let first = codec
            .read_request(&v4, &mut Cursor::new(&bytes))
            .await
            .unwrap();
        assert_eq!(codec.inbound_budget.available_permits(), 0);
        let mut next_codec = codec.clone();
        let next =
            tokio::spawn(
                async move { next_codec.read_request(&v4, &mut Cursor::new(bytes)).await },
            );
        tokio::task::yield_now().await;
        assert!(!next.is_finished());
        drop(first);
        let second = tokio::time::timeout(std::time::Duration::from_secs(1), next)
            .await
            .unwrap()
            .unwrap()
            .unwrap();
        assert_eq!(codec.inbound_budget.available_permits(), 0);
        drop(second);
        assert_eq!(codec.inbound_budget.available_permits(), 32);
    }

    #[tokio::test]
    async fn second_inbound_response_blocks_until_node_releases_first() {
        let budget = 8;
        let codec =
            MempoolSyncCodec::with_budgets(budget, OutboundResponseBudget::with_capacity(budget));
        let first = codec
            .clone()
            .read_response(&protocol(), &mut Cursor::new(response_wire(&[8], &[1; 8])))
            .await
            .unwrap();
        let mut second_codec = codec.clone();
        let second = tokio::spawn(async move {
            second_codec
                .read_response(&protocol(), &mut Cursor::new(response_wire(&[8], &[2; 8])))
                .await
        });
        tokio::task::yield_now().await;
        assert!(!second.is_finished());
        drop(first);
        let second = tokio::time::timeout(std::time::Duration::from_secs(1), second)
            .await
            .unwrap()
            .unwrap()
            .unwrap();
        assert_eq!(second.txs, vec![vec![2; 8]]);
    }

    #[test]
    fn independent_production_codecs_share_one_inbound_budget() {
        let first = MempoolSyncCodec::default();
        let second = MempoolSyncCodec::default();
        let shared = process_global_inbound_budget();
        assert!(Arc::ptr_eq(&first.inbound_budget, &second.inbound_budget));
        assert!(Arc::ptr_eq(&first.inbound_budget, &shared));
    }

    #[tokio::test]
    async fn outbound_permit_lives_until_direct_slice_write_finishes() {
        let budget = OutboundResponseBudget::with_capacity(8);
        let permit = budget.acquire(8).await.unwrap().unwrap();
        let response = GetMempoolResponse {
            txs: vec![vec![0x44; 8]],
            supports_missing: false,
            inbound_memory_permit: None,
            outbound_memory_permit: Some(permit),
        };
        let started = Arc::new(AtomicBool::new(false));
        let released = Arc::new(AtomicBool::new(false));
        let waker = Arc::new(Mutex::new(None));
        let writer = GatedWriter {
            started: started.clone(),
            released: released.clone(),
            waker: waker.clone(),
        };
        let write = tokio::spawn(async move {
            let mut writer = writer;
            MempoolSyncCodec::default()
                .write_response(&protocol(), &mut writer, response)
                .await
        });
        while !started.load(Ordering::SeqCst) {
            tokio::task::yield_now().await;
        }
        assert_eq!(budget.available_bytes(), 0);
        assert!(!write.is_finished());

        let waiter_budget = budget.clone();
        let waiter = tokio::spawn(async move { waiter_budget.acquire(8).await.unwrap() });
        tokio::task::yield_now().await;
        assert!(!waiter.is_finished());
        released.store(true, Ordering::SeqCst);
        if let Some(waker) = waker.lock().unwrap().take() {
            waker.wake();
        }
        write.await.unwrap().unwrap();
        let second_permit = tokio::time::timeout(std::time::Duration::from_secs(1), waiter)
            .await
            .unwrap()
            .unwrap()
            .unwrap();
        drop(second_permit);
        assert_eq!(budget.available_bytes(), 8);
    }
}
