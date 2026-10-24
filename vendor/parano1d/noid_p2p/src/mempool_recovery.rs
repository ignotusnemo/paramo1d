// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Bounded, consumption-paced recovery of missing pending transactions.
//!
//! One pull/consumption lane for the whole node, at most four selected peers,
//! unchanged 30-second per-peer request spacing, finite failure retries and one
//! finite scan per connection. Completed scans never poll idle peers or seeds.
//! A successful Push is never a Pull completion. No chain state or
//! transaction validity is inferred from this transport bookkeeping.

use libp2p::PeerId;
use noid_chain::consensus::wire_limits::{
    MAX_MEMPOOL_SYNC_BYTES, MAX_MEMPOOL_SYNC_TXS, MAX_MEMPOOL_TXS, MAX_TX_INTENT_BYTES_GLOBAL,
};
use std::{
    collections::{BTreeSet, HashMap},
    time::{Duration, Instant},
};

pub(crate) const MAX_RECOVERY_PEERS: usize = 4;
pub(crate) const REQUEST_SPACING: Duration = Duration::from_secs(30);
const REQUEST_TIMEOUT: Duration = Duration::from_secs(35);
const MAX_FAILURES: u8 = 7;
// Even maximum-size intents permit this many entries per non-final response.
const MIN_FULL_PAGE: usize = {
    let by_bytes = MAX_MEMPOOL_SYNC_BYTES / MAX_TX_INTENT_BYTES_GLOBAL;
    if by_bytes < MAX_MEMPOOL_SYNC_TXS {
        by_bytes
    } else {
        MAX_MEMPOOL_SYNC_TXS
    }
};
const MAX_SCAN_PAGES: usize = MAX_MEMPOOL_TXS.div_ceil(MIN_FULL_PAGE) + 1;

struct PeerRecovery {
    due: Option<Instant>,
    next_request: Instant,
    seen: BTreeSet<[u8; 32]>,
    failures: u8,
    pages: usize,
}

impl PeerRecovery {
    fn stop(&mut self) {
        self.due = None;
        self.seen.clear();
        self.pages = 0;
    }
}

struct Active<R> {
    peer: PeerId,
    request: R,
    issued: Instant,
    // None means waiting for the response. Some(bool) means the node still
    // owns its memory permit and must finish admission before another pull.
    consuming: Option<bool>,
    retired: bool,
}

pub(crate) struct MempoolRecovery<R> {
    local: PeerId,
    peers: HashMap<PeerId, PeerRecovery>,
    active: Option<Active<R>>,
}

impl<R: Copy + Eq> MempoolRecovery<R> {
    pub(crate) fn new(local: PeerId) -> Self {
        Self {
            local,
            peers: HashMap::new(),
            active: None,
        }
    }

    pub(crate) fn register(&mut self, peer: PeerId, now: Instant, connected: bool) {
        // A node command can arrive after the swarm has already handled the
        // disconnect. It must not retain a dead source and consume one of the
        // four recovery slots until another connection happens by chance.
        if connected && self.peers.len() < MAX_RECOVERY_PEERS {
            self.peers.entry(peer).or_insert(PeerRecovery {
                due: Some(now),
                next_request: now,
                seen: BTreeSet::new(),
                failures: 0,
                pages: 0,
            });
        }
    }

    pub(crate) fn disconnect(&mut self, peer: PeerId) {
        self.peers.remove(&peer);
        if let Some(active) = self.active.as_mut().filter(|active| active.peer == peer) {
            if active.consuming.is_some() {
                // Disconnect cannot cancel the node worker or release its
                // payload permit. Preserve the global lane until it finishes.
                active.retired = true;
            } else {
                self.active = None;
            }
        }
    }

    pub(crate) fn stop_full_pool(&mut self, peer: PeerId) {
        if let Some(state) = self.peers.get_mut(&peer) {
            // Catch-up is best effort within the existing admission budget,
            // not an ongoing reconciliation subscription. A full pool must
            // not leave a timer that later starts polling a retained seed.
            state.stop();
        }
    }

    pub(crate) fn next_peer(
        &mut self,
        now: Instant,
        ready: impl Fn(PeerId) -> bool,
    ) -> Option<PeerId> {
        if let Some(active) = &self.active {
            if active.consuming.is_none()
                && now.saturating_duration_since(active.issued) >= REQUEST_TIMEOUT
            {
                let (peer, request) = (active.peer, active.request);
                self.failed(peer, request, now);
            }
        }
        if self.active.is_some() {
            return None;
        }
        self.peers
            .iter()
            .filter_map(|(&peer, state)| {
                state
                    .due
                    .filter(|&due| due <= now && ready(peer))
                    .map(|due| (due, peer))
            })
            .min_by_key(|(due, peer)| (*due, peer.to_bytes()))
            .map(|(_, peer)| peer)
    }

    pub(crate) fn known(
        &mut self,
        peer: PeerId,
        local_ids: impl IntoIterator<Item = [u8; 32]>,
    ) -> Option<Vec<[u8; 32]>> {
        let state = self.peers.get_mut(&peer)?;
        let mut known = state.seen.clone();
        for id in local_ids {
            known.insert(id);
            if known.len() > MAX_MEMPOOL_TXS {
                // The local pool and this scan cover more than one full pool.
                // Stop instead of truncating the exclusion list or resetting
                // the scan budget and fetching the same prefix indefinitely.
                state.stop();
                return None;
            }
        }
        Some(known.into_iter().collect())
    }

    pub(crate) fn issued(&mut self, peer: PeerId, request: R, now: Instant) {
        debug_assert!(self.active.is_none());
        self.active = Some(Active {
            peer,
            request,
            issued: now,
            consuming: None,
            retired: false,
        });
        if let Some(state) = self.peers.get_mut(&peer) {
            state.next_request = now + REQUEST_SPACING;
        }
    }

    /// Accept only the outstanding peer/request pair. A nonempty response
    /// transfers the lane to node admission; an empty one finishes it here.
    /// Empty and legacy completions cannot accidentally schedule a new scan.
    pub(crate) fn response(
        &mut self,
        peer: PeerId,
        request: R,
        supports_missing: bool,
        nonempty: bool,
        now: Instant,
    ) -> bool {
        let Some(active) = &mut self.active else {
            return false;
        };
        if active.peer != peer || active.request != request || active.consuming.is_some() {
            return false;
        }
        active.consuming = Some(supports_missing);
        if !nonempty {
            self.finish(peer, request, &[], true, now);
        }
        true
    }

    pub(crate) fn consumed(
        &mut self,
        peer: PeerId,
        request: R,
        observed: &[[u8; 32]],
        now: Instant,
    ) {
        self.finish(peer, request, observed, false, now);
    }

    fn finish(
        &mut self,
        peer: PeerId,
        request: R,
        observed: &[[u8; 32]],
        empty: bool,
        now: Instant,
    ) {
        let Some(active) = &self.active else {
            return;
        };
        if active.peer != peer || active.request != request {
            return;
        }
        let Some(supports_missing) = active.consuming else {
            return;
        };
        let retired = active.retired;
        self.active = None;
        if retired {
            return;
        }
        let Some(state) = self.peers.get_mut(&peer) else {
            return;
        };
        state.failures = 0;
        if !supports_missing {
            state.stop(); // v3 bootstrap exactly once; no repeated prefix
            return;
        }
        let before = state.seen.len();
        for id in observed.iter().take(MAX_MEMPOOL_SYNC_TXS) {
            if state.seen.len() < MAX_MEMPOOL_TXS {
                state.seen.insert(*id);
            }
        }
        state.pages += 1;
        if empty || state.pages >= MAX_SCAN_PAGES || state.seen.len() >= MAX_MEMPOOL_TXS {
            state.stop();
        } else if state.seen.len() == before {
            // Malformed or repeated data is not progress. Stop this peer's
            // scan, rather than turning it into an unbounded payload loop.
            state.stop();
        } else {
            state.due = Some(now.max(state.next_request) + jitter(self.local, peer));
        }
    }

    pub(crate) fn failed(&mut self, peer: PeerId, request: R, now: Instant) -> bool {
        if !self.active.as_ref().is_some_and(|active| {
            active.peer == peer && active.request == request && active.consuming.is_none()
        }) {
            return false;
        }
        self.active = None;
        let Some(state) = self.peers.get_mut(&peer) else {
            return false;
        };
        state.failures = state.failures.saturating_add(1);
        state.due = if state.failures >= MAX_FAILURES {
            None
        } else {
            Some(
                (now + Duration::from_secs(1 << (state.failures - 1).min(5))
                    + jitter(self.local, peer))
                .max(state.next_request),
            )
        };
        true
    }

    pub(crate) fn response_dropped(&mut self, peer: PeerId, request: R, now: Instant) {
        // Only the local failed event enqueue can release consumption here:
        // no node worker received the payload and its permit is being dropped.
        if let Some(active) = self
            .active
            .as_mut()
            .filter(|active| active.peer == peer && active.request == request)
        {
            active.consuming = None;
            self.failed(peer, request, now);
        }
    }
}

fn jitter(local: PeerId, peer: PeerId) -> Duration {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for byte in local.to_bytes().iter().chain(peer.to_bytes().iter()) {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    Duration::from_millis(hash % 4_000)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup() -> (MempoolRecovery<u64>, PeerId, Instant) {
        let now = Instant::now();
        let peer = PeerId::random();
        let mut recovery = MempoolRecovery::new(PeerId::random());
        recovery.register(peer, now, true);
        (recovery, peer, now)
    }

    #[test]
    fn next_page_waits_for_consumption_and_spacing() {
        let (mut r, peer, now) = setup();
        r.issued(peer, 1, now);
        assert!(r.response(peer, 1, true, true, now));
        assert!(r
            .next_peer(now + Duration::from_secs(300), |_| true)
            .is_none());
        r.consumed(peer, 1, &[[1; 32]], now);
        assert!(r
            .next_peer(now + Duration::from_secs(29), |_| true)
            .is_none());
        assert_eq!(
            r.next_peer(now + Duration::from_secs(34), |_| true),
            Some(peer)
        );
        assert_eq!(
            r.known(peer, [[2; 32], [1; 32]]).unwrap(),
            vec![[1; 32], [2; 32]]
        );
    }

    #[test]
    fn push_wrong_peer_duplicate_and_late_completions_cannot_advance_pull() {
        let (mut r, peer, now) = setup();
        r.issued(peer, 1, now);
        assert!(!r.failed(peer, 2, now));
        assert!(!r.response(peer, 2, true, false, now));
        assert!(!r.response(PeerId::random(), 1, true, false, now));
        r.consumed(peer, 1, &[[1; 32]], now); // before response
        assert!(r.active.is_some());
        assert!(r.response(peer, 1, true, true, now));
        assert!(!r.response(peer, 1, true, true, now));
        assert!(!r.failed(peer, 1, now)); // never release a node-owned payload
        r.disconnect(peer);
        r.consumed(peer, 1, &[[1; 32]], now);
        assert!(r.peers.is_empty());
    }

    #[test]
    fn legacy_nonprogress_and_empty_v4_stop_without_idle_polling() {
        for (supported, empty, observed) in [
            (false, false, vec![[1; 32]]),
            (true, false, vec![]),
            (true, true, vec![]),
        ] {
            let (mut r, peer, now) = setup();
            r.issued(peer, 1, now);
            r.response(peer, 1, supported, !empty, now);
            if !empty {
                r.consumed(peer, 1, &observed, now);
            }
            assert!(r
                .next_peer(now + Duration::from_secs(60), |_| true)
                .is_none());
            let later = now + Duration::from_secs(86_400);
            assert!(r.next_peer(later, |_| true).is_none());
            r.register(peer, later, true);
            assert!(r.next_peer(later, |_| true).is_none());
            r.disconnect(peer);
            r.register(peer, later, true);
            assert_eq!(r.next_peer(later, |_| true), Some(peer));
        }
    }

    #[test]
    fn one_global_lane_finite_retries_and_bounded_peers() {
        let (mut r, peer, now) = setup();
        for _ in 0..100 {
            r.register(PeerId::random(), now, true);
        }
        assert_eq!(r.peers.len(), MAX_RECOVERY_PEERS);
        for i in 0..MAX_FAILURES {
            let at = now + Duration::from_secs(u64::from(i) * 60);
            r.issued(peer, u64::from(i), at);
            assert!(r.next_peer(at + Duration::from_secs(1), |_| true).is_none());
            assert!(r.failed(peer, u64::from(i), at));
        }
        assert!(r.peers[&peer].due.is_none());
        r.register(peer, now, true); // duplicate registration must not reset failures
        assert!(r.peers[&peer].due.is_none());
        r.disconnect(peer);
        r.register(peer, now, true);
        assert!(r.peers[&peer].due.is_some());
    }

    #[test]
    fn empty_peer_does_not_delay_other_bootstrap_sources_by_thirty_seconds() {
        let (mut r, peer, now) = setup();
        let other = PeerId::random();
        r.register(other, now, true);
        r.issued(peer, 1, now);
        r.response(peer, 1, true, false, now);
        assert_eq!(r.next_peer(now, |_| true), Some(other));
    }

    #[test]
    fn silent_source_timeout_releases_healthy_source_and_rejects_late_reply() {
        let (mut r, silent, now) = setup();
        let healthy = PeerId::random();
        r.register(healthy, now, true);
        r.issued(silent, 1, now);
        let expired = now + REQUEST_TIMEOUT;
        assert!(r
            .next_peer(expired - Duration::from_secs(1), |_| true)
            .is_none());
        assert_eq!(r.next_peer(expired, |_| true), Some(healthy));
        r.issued(healthy, 2, expired);
        assert!(!r.response(silent, 1, true, true, expired));
        assert!(!r.failed(silent, 1, expired));
        assert!(r.response(healthy, 2, true, false, expired));
        assert!(!r.response(healthy, 2, true, false, expired));
        // The remaining retry belongs only to the silent peer. Completing
        // the healthy peer cannot cause idle polling or reset its scan.
        assert_eq!(
            r.next_peer(expired + Duration::from_secs(5), |_| true),
            Some(silent)
        );
        assert!(r.peers[&healthy].due.is_none());
    }

    #[test]
    fn late_commands_for_disconnected_peers_cannot_fill_recovery_slots() {
        let (mut r, peer, now) = setup();
        r.disconnect(peer);
        r.register(peer, now, false);
        for _ in 0..100 {
            r.register(PeerId::random(), now, false);
        }
        assert!(r.peers.is_empty());
        assert!(r.next_peer(now, |_| true).is_none());
        r.register(peer, now, true);
        assert_eq!(r.next_peer(now, |_| true), Some(peer));
    }

    #[test]
    fn timeout_and_failed_enqueue_release_only_the_correlated_lane() {
        let (mut r, peer, now) = setup();
        r.issued(peer, 1, now);
        assert!(r
            .next_peer(now + Duration::from_secs(34), |_| true)
            .is_none());
        assert!(r
            .next_peer(now + Duration::from_secs(35), |_| true)
            .is_none());
        assert!(!r.response(peer, 1, true, true, now + Duration::from_secs(36)));
        let retry = now + Duration::from_secs(41);
        assert_eq!(r.next_peer(retry, |_| true), Some(peer));
        r.issued(peer, 2, retry);
        assert!(r.response(peer, 2, true, true, retry));
        r.response_dropped(peer, 1, retry);
        assert!(r
            .next_peer(retry + Duration::from_secs(100), |_| true)
            .is_none());
        r.response_dropped(peer, 2, retry);
        assert!(r
            .next_peer(retry + Duration::from_secs(29), |_| true)
            .is_none());
        assert_eq!(
            r.next_peer(retry + Duration::from_secs(35), |_| true),
            Some(peer)
        );
    }

    #[test]
    fn full_pool_and_inventory_churn_stop_without_truncation_or_idle_polling() {
        let (mut r, peer, now) = setup();
        r.issued(peer, 1, now);
        r.response(peer, 1, true, true, now);
        r.consumed(peer, 1, &[[0xFF; 32]], now);
        let local = (0..MAX_MEMPOOL_TXS).map(|index| {
            let mut id = [0; 32];
            id[..8].copy_from_slice(&(index as u64).to_le_bytes());
            id
        });
        assert!(r.known(peer, local).is_none());
        assert!(r.peers[&peer].seen.is_empty());
        assert!(r
            .next_peer(now + Duration::from_secs(119), |_| true)
            .is_none());
        let later = now + Duration::from_secs(86_400);
        r.register(peer, later, true);
        assert!(r.next_peer(later, |_| true).is_none());
        r.disconnect(peer);
        r.register(peer, later, true);
        r.stop_full_pool(peer);
        r.register(peer, later, true);
        assert!(r.next_peer(later, |_| true).is_none());
        assert!(r
            .next_peer(later + Duration::from_secs(86_400), |_| true)
            .is_none());
    }

    #[test]
    fn tiny_responses_cannot_extend_a_scan_indefinitely() {
        let (mut r, peer, now) = setup();
        for page in 0..MAX_SCAN_PAGES {
            let at = now + Duration::from_secs(page as u64 * 40);
            r.issued(peer, page as u64, at);
            assert!(r.response(peer, page as u64, true, true, at));
            r.consumed(peer, page as u64, &[[page as u8; 32]], at);
        }
        let ended = now + Duration::from_secs((MAX_SCAN_PAGES - 1) as u64 * 40);
        assert!(r.peers[&peer].seen.is_empty());
        assert_eq!(r.peers[&peer].pages, 0);
        assert!(r
            .next_peer(ended + Duration::from_secs(119), |_| true)
            .is_none());
        let later = ended + Duration::from_secs(86_400);
        r.register(peer, later, true);
        assert!(r.next_peer(later, |_| true).is_none());
    }

    #[test]
    fn disconnect_and_reconnect_cannot_overlap_old_node_consumption() {
        let (mut r, peer, now) = setup();
        r.issued(peer, 1, now);
        r.response(peer, 1, true, true, now);
        r.disconnect(peer);
        r.register(peer, now, true);
        assert!(r
            .next_peer(now + Duration::from_secs(300), |_| true)
            .is_none());
        r.consumed(peer, 1, &[[1; 32]], now);
        assert_eq!(r.next_peer(now, |_| true), Some(peer));
        assert!(r.peers[&peer].seen.is_empty());
    }

    #[test]
    fn bytes_limited_1024_entry_scan_fits_finite_page_budget() {
        assert_eq!(MIN_FULL_PAGE, 55);
        assert_eq!(MAX_SCAN_PAGES, 20);
        let (mut r, peer, now) = setup();
        let mut count = 0;
        for page in 0..MAX_SCAN_PAGES {
            let at = now + Duration::from_secs(page as u64 * 40);
            let ids: Vec<_> = (count..(count + MIN_FULL_PAGE).min(1024))
                .map(|i| {
                    let mut id = [0; 32];
                    id[..8].copy_from_slice(&(i as u64).to_be_bytes());
                    id
                })
                .collect();
            r.issued(peer, page as u64, at);
            r.response(peer, page as u64, true, !ids.is_empty(), at);
            r.consumed(peer, page as u64, &ids, at);
            count += ids.len();
            if count == 1024 {
                break;
            }
            assert_eq!(r.known(peer, []).unwrap().len(), count);
        }
        assert_eq!(count, 1024);
        assert!(r.peers[&peer].seen.is_empty());
        assert!(r
            .next_peer(now + Duration::from_secs(86_400), |_| true)
            .is_none());
    }
}
