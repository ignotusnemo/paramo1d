// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Non-blocking priority dispatch from the swarm reactor to the node.

use std::{
    fmt,
    future::{ready, Ready},
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};

use tokio::sync::mpsc;

use crate::network::NetworkEvent;

// Transitional bounds cover the existing request tables. Payload bytes remain
// constrained by the process-wide inbound permits. Exact-object networking
// will later reduce these to the smaller plan-level concurrency limits.
const CONTROL_CAPACITY: usize = 1_024;
const HEADER_REQUIRED_RESERVE: usize = 64;
const HEADER_CAPACITY: usize = HEADER_REQUIRED_RESERVE * 2;
// These bounds cover the sum of the corresponding request registries. A
// required response therefore never needs an unbounded overflow task.
const LIVE_CAPACITY: usize = 336;
const HISTORICAL_CAPACITY: usize = 336;
const BACKGROUND_CAPACITY: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EventClass {
    Control,
    Header,
    Live,
    Historical,
    Background,
}

impl EventClass {
    const fn index(self) -> usize {
        match self {
            Self::Control => 0,
            Self::Header => 1,
            Self::Live => 2,
            Self::Historical => 3,
            Self::Background => 4,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum DispatchError {
    Full(EventClass),
    Closed(EventClass),
}

impl fmt::Display for DispatchError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Full(class) => write!(formatter, "{class:?} event lane is full"),
            Self::Closed(class) => write!(formatter, "{class:?} event lane is closed"),
        }
    }
}

#[derive(Clone)]
pub(crate) struct RequiredEventSender {
    control: mpsc::Sender<NetworkEvent>,
    header: mpsc::Sender<NetworkEvent>,
    live: mpsc::Sender<NetworkEvent>,
    historical: mpsc::Sender<NetworkEvent>,
    background: mpsc::Sender<NetworkEvent>,
    fatal_dispatch_failure: Arc<AtomicBool>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct EventQueueDepths {
    pub control: usize,
    pub header: usize,
    pub live: usize,
    pub historical: usize,
    pub background: usize,
}

impl EventQueueDepths {
    pub const fn total(self) -> usize {
        self.control + self.header + self.live + self.historical + self.background
    }
}

pub(crate) struct RequiredEventReceiver {
    control: mpsc::Receiver<NetworkEvent>,
    header: mpsc::Receiver<NetworkEvent>,
    live: mpsc::Receiver<NetworkEvent>,
    historical: mpsc::Receiver<NetworkEvent>,
    background: mpsc::Receiver<NetworkEvent>,
    closed: [bool; 5],
    schedule_cursor: usize,
}

pub(crate) fn channel() -> (RequiredEventSender, RequiredEventReceiver) {
    let (control_tx, control_rx) = mpsc::channel(CONTROL_CAPACITY);
    let (header_tx, header_rx) = mpsc::channel(HEADER_CAPACITY);
    let (live_tx, live_rx) = mpsc::channel(LIVE_CAPACITY);
    let (historical_tx, historical_rx) = mpsc::channel(HISTORICAL_CAPACITY);
    let (background_tx, background_rx) = mpsc::channel(BACKGROUND_CAPACITY);
    let fatal_dispatch_failure = Arc::new(AtomicBool::new(false));
    (
        RequiredEventSender {
            control: control_tx,
            header: header_tx,
            live: live_tx,
            historical: historical_tx,
            background: background_tx,
            fatal_dispatch_failure,
        },
        RequiredEventReceiver {
            control: control_rx,
            header: header_rx,
            live: live_rx,
            historical: historical_rx,
            background: background_rx,
            closed: [false; 5],
            schedule_cursor: 0,
        },
    )
}

impl RequiredEventSender {
    /// Enqueue an authoritative event without ever awaiting node-side
    /// capacity in the swarm reactor. A full lane is an explicit invariant
    /// failure; it never creates an untracked waiter task.
    pub(crate) fn send(&self, event: NetworkEvent) -> Ready<Result<(), DispatchError>> {
        let class = classify(&event);
        let result = self.try_send_required(event, class);
        if let Err(error) = &result {
            self.fatal_dispatch_failure.store(true, Ordering::Release);
            tracing::error!(?class, %error, "required network event dispatch failed");
        }
        ready(result)
    }

    pub(crate) fn try_send(&self, event: NetworkEvent) -> Result<(), DispatchError> {
        let class = classify(&event);
        // Replaceable gossip can use only the non-reserved half of the header
        // lane. Correlated response/failure events keep a full 64-slot reserve.
        if matches!(event, NetworkEvent::HeaderAnnouncement { .. })
            && self.header.capacity() <= HEADER_REQUIRED_RESERVE
        {
            return Err(DispatchError::Full(EventClass::Header));
        }
        self.try_send_required(event, class)
    }

    fn try_send_required(
        &self,
        event: NetworkEvent,
        class: EventClass,
    ) -> Result<(), DispatchError> {
        let result = match class {
            EventClass::Control => self.control.try_send(event),
            EventClass::Header => self.header.try_send(event),
            EventClass::Live => self.live.try_send(event),
            EventClass::Historical => self.historical.try_send(event),
            EventClass::Background => self.background.try_send(event),
        };
        result.map_err(|error| match error {
            mpsc::error::TrySendError::Full(_) => DispatchError::Full(class),
            mpsc::error::TrySendError::Closed(_) => DispatchError::Closed(class),
        })
    }

    pub(crate) fn queue_depths(&self) -> EventQueueDepths {
        let queued = |sender: &mpsc::Sender<NetworkEvent>| {
            sender.max_capacity().saturating_sub(sender.capacity())
        };
        EventQueueDepths {
            control: queued(&self.control),
            header: queued(&self.header),
            live: queued(&self.live),
            historical: queued(&self.historical),
            background: queued(&self.background),
        }
    }

    pub(crate) fn has_fatal_dispatch_failure(&self) -> bool {
        self.fatal_dispatch_failure.load(Ordering::Acquire)
    }
}

impl RequiredEventReceiver {
    pub(crate) fn is_closed(&self) -> bool {
        self.closed.into_iter().all(|closed| closed)
    }

    pub(crate) async fn recv(&mut self) -> Option<NetworkEvent> {
        loop {
            if let Some(event) = self.try_recv_fair() {
                return Some(event);
            }
            if self.is_closed() {
                return None;
            }

            tokio::select! {
                biased;
                event = self.control.recv(), if !self.closed[EventClass::Control.index()] => {
                    if let Some(event) = event { return Some(event); }
                    self.closed[EventClass::Control.index()] = true;
                }
                event = self.header.recv(), if !self.closed[EventClass::Header.index()] => {
                    if let Some(event) = event { return Some(event); }
                    self.closed[EventClass::Header.index()] = true;
                }
                event = self.live.recv(), if !self.closed[EventClass::Live.index()] => {
                    if let Some(event) = event { return Some(event); }
                    self.closed[EventClass::Live.index()] = true;
                }
                event = self.historical.recv(), if !self.closed[EventClass::Historical.index()] => {
                    if let Some(event) = event { return Some(event); }
                    self.closed[EventClass::Historical.index()] = true;
                }
                event = self.background.recv(), if !self.closed[EventClass::Background.index()] => {
                    if let Some(event) = event { return Some(event); }
                    self.closed[EventClass::Background.index()] = true;
                }
            }
        }
    }

    fn try_recv_fair(&mut self) -> Option<NetworkEvent> {
        // Weighted schedule: control 4/9, headers 2/9, and one lane for each
        // payload class. Scanning the whole schedule also stays work-conserving.
        const SCHEDULE: [EventClass; 9] = [
            EventClass::Control,
            EventClass::Header,
            EventClass::Control,
            EventClass::Live,
            EventClass::Control,
            EventClass::Header,
            EventClass::Historical,
            EventClass::Control,
            EventClass::Background,
        ];
        for offset in 0..SCHEDULE.len() {
            let index = (self.schedule_cursor + offset) % SCHEDULE.len();
            let class = SCHEDULE[index];
            let result = match class {
                EventClass::Control => self.control.try_recv(),
                EventClass::Header => self.header.try_recv(),
                EventClass::Live => self.live.try_recv(),
                EventClass::Historical => self.historical.try_recv(),
                EventClass::Background => self.background.try_recv(),
            };
            match result {
                Ok(event) => {
                    self.schedule_cursor = (index + 1) % SCHEDULE.len();
                    return Some(event);
                }
                Err(mpsc::error::TryRecvError::Disconnected) => {
                    self.closed[class.index()] = true;
                }
                Err(mpsc::error::TryRecvError::Empty) => {}
            }
        }
        None
    }
}

fn classify(event: &NetworkEvent) -> EventClass {
    match event {
        NetworkEvent::PeerConnected { .. } | NetworkEvent::PeerDisconnected(_) => {
            EventClass::Control
        }
        NetworkEvent::HeaderInventoryBatch { .. }
        | NetworkEvent::HeaderAnnouncement { .. }
        | NetworkEvent::HeadersRequestFailed { .. }
        | NetworkEvent::SnapshotHeadersBatch { .. }
        | NetworkEvent::SnapshotHeadersRequestFailed { .. } => EventClass::Header,
        NetworkEvent::HistoryStepTerminal { .. }
        | NetworkEvent::HistoryStepTerminalRequestFailed { .. }
        | NetworkEvent::HistoryStepTerminalRequestBusy { .. }
        | NetworkEvent::ObjectsResponse { .. }
        | NetworkEvent::ObjectsRequestFailed { .. }
        | NetworkEvent::ObjectsRequestBusy { .. } => EventClass::Live,
        NetworkEvent::StateManifest { .. }
        | NetworkEvent::StateManifestRequestFailed { .. }
        | NetworkEvent::StateSegment { .. }
        | NetworkEvent::StateSegmentRequestFailed { .. }
        | NetworkEvent::StateSegmentRequestBusy { .. } => EventClass::Historical,
        NetworkEvent::NewTx { .. } | NetworkEvent::MempoolSyncResponse { .. } => {
            EventClass::Background
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libp2p::PeerId;

    fn live(peer: PeerId, height: u64) -> NetworkEvent {
        NetworkEvent::HistoryStepTerminalRequestFailed {
            token: height,
            from: peer,
            height,
            block_hash: [0; 32],
            kind: crate::network::RequestFailureKind::Timeout,
        }
    }

    #[tokio::test]
    async fn required_send_is_immediate_and_bounded_by_the_lane() {
        let (tx, _rx) = channel();
        let peer = PeerId::random();
        for height in 0..LIVE_CAPACITY {
            tx.try_send(live(peer, height as u64)).unwrap();
        }
        assert_eq!(
            tx.send(live(peer, u64::MAX)).await,
            Err(DispatchError::Full(EventClass::Live))
        );
        assert_eq!(tx.queue_depths().live, LIVE_CAPACITY);
    }

    #[tokio::test]
    async fn control_is_not_queued_behind_saturated_live_payloads() {
        let (tx, mut rx) = channel();
        let peer = PeerId::random();
        for height in 0..LIVE_CAPACITY {
            tx.send(live(peer, height as u64)).await.unwrap();
        }
        tx.send(NetworkEvent::PeerConnected {
            peer,
            locally_selected: true,
            failure_domain: 1,
        })
        .await
        .unwrap();
        assert!(matches!(
            rx.recv().await,
            Some(NetworkEvent::PeerConnected { peer: connected, .. }) if connected == peer
        ));
    }

    #[tokio::test]
    async fn fair_schedule_does_not_starve_historical_work() {
        let (tx, mut rx) = channel();
        let peer = PeerId::random();
        for height in 0..32 {
            tx.send(NetworkEvent::PeerConnected {
                peer: PeerId::random(),
                locally_selected: false,
                failure_domain: height,
            })
            .await
            .unwrap();
            tx.send(live(peer, height)).await.unwrap();
        }
        tx.send(NetworkEvent::StateSegmentRequestFailed {
            from: peer,
            segment_id: 1,
            expected_tip_height: 10,
            expected_tip_hash: [1; 32],
            manifest_digest: [2; 32],
            kind: crate::network::RequestFailureKind::Timeout,
        })
        .await
        .unwrap();

        let mut found = false;
        for _ in 0..9 {
            if matches!(
                rx.recv().await,
                Some(NetworkEvent::StateSegmentRequestFailed { .. })
            ) {
                found = true;
                break;
            }
        }
        assert!(found, "historical lane must receive its weighted turn");
    }

    #[test]
    fn replaceable_header_gossip_cannot_consume_required_response_reserve() {
        let (tx, _rx) = channel();
        let peer = PeerId::random();
        let header = noid_chain::consensus::genesis_header();
        let announcement = crate::header_protocol::HeaderAnnouncement {
            header,
            body: crate::object_protocol::BlockBodyObjectId {
                claim: crate::object_protocol::BlockBodyClaimId {
                    height: header.height,
                    block_hash: noid_chain::block_header::block_id(&header),
                },
                byte_digest: [1; 32],
                encoded_len: 1,
            },
            terminal: crate::object_protocol::TerminalObjectId {
                claim: crate::object_protocol::TerminalClaimId {
                    height: header.height,
                    semantic_header_id: noid_chain::block_header::semantic_header_id(&header),
                    proof_class: 0,
                },
                byte_digest: [2; 32],
                encoded_len: 1,
            },
            providers: crate::header_protocol::ProviderFlags::new(true, true, false),
        };
        for _ in 0..(HEADER_CAPACITY - HEADER_REQUIRED_RESERVE) {
            tx.try_send(NetworkEvent::HeaderAnnouncement {
                from: peer,
                announcement,
                source_has_objects: true,
            })
            .unwrap();
        }
        assert_eq!(
            tx.try_send(NetworkEvent::HeaderAnnouncement {
                from: peer,
                announcement,
                source_has_objects: true,
            }),
            Err(DispatchError::Full(EventClass::Header))
        );
        assert_eq!(tx.queue_depths().header, HEADER_REQUIRED_RESERVE);
        assert!(!tx.has_fatal_dispatch_failure());
    }

    #[tokio::test]
    async fn failed_required_delivery_sets_the_reactor_fatal_flag() {
        let (tx, _rx) = channel();
        let peer = PeerId::random();
        for height in 0..LIVE_CAPACITY {
            tx.send(live(peer, height as u64)).await.unwrap();
        }
        assert!(tx.send(live(peer, u64::MAX)).await.is_err());
        assert!(tx.has_fatal_dispatch_failure());
    }
}
