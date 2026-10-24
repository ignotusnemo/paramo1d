// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Reuse transport digests only when the freshly loaded bytes match exactly.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex, OnceLock};

use crate::object_protocol::{
    BlockBodyClaimId, BlockBodyObjectId, ObjectClaimId, ObjectId, TerminalClaimId,
    TerminalObjectId, MAX_OBJECT_RESPONSE_PAYLOAD_BYTES,
};

const CACHE_ENTRIES: usize = 64;

struct CachedObject {
    bytes: Box<[u8]>,
    object: ObjectId,
}

type Entry = Arc<Mutex<Option<CachedObject>>>;

/// At most 64 retained byte strings, each within the existing response cap.
/// Per-claim locks coalesce concurrent requests without serializing other
/// claims. Evicted entries may finish under the existing serving permits.
#[derive(Default)]
pub(crate) struct RetainedObjectCache {
    entries: Mutex<VecDeque<(ObjectClaimId, Entry)>>,
    #[cfg(test)]
    computations: std::sync::atomic::AtomicUsize,
}

impl RetainedObjectCache {
    pub(crate) fn process_global() -> Arc<Self> {
        static CACHE: OnceLock<Arc<RetainedObjectCache>> = OnceLock::new();
        CACHE.get_or_init(|| Arc::new(Self::default())).clone()
    }

    pub(crate) fn block_body(
        &self,
        claim: BlockBodyClaimId,
        bytes: &[u8],
    ) -> Option<BlockBodyObjectId> {
        match self.get_or_compute(ObjectClaimId::BlockBody(claim), bytes, || {
            BlockBodyObjectId::from_bytes(claim, bytes).map(ObjectId::BlockBody)
        })? {
            ObjectId::BlockBody(object) => Some(object),
            _ => unreachable!("body cache entry has a body claim"),
        }
    }

    pub(crate) fn terminal(
        &self,
        claim: TerminalClaimId,
        bytes: &[u8],
    ) -> Option<TerminalObjectId> {
        match self.get_or_compute(ObjectClaimId::Terminal(claim), bytes, || {
            TerminalObjectId::from_bytes(claim, bytes).map(ObjectId::Terminal)
        })? {
            ObjectId::Terminal(object) => Some(object),
            _ => unreachable!("terminal cache entry has a terminal claim"),
        }
    }

    pub(crate) fn matches_bytes(&self, expected: ObjectId, bytes: &[u8]) -> bool {
        if expected.encoded_len().map(|length| length as usize) != Some(bytes.len()) {
            return false;
        }
        match expected {
            ObjectId::BlockBody(object) => self.block_body(object.claim, bytes) == Some(object),
            ObjectId::Terminal(object) => self.terminal(object.claim, bytes) == Some(object),
            ObjectId::SnapshotManifest(_) | ObjectId::StateSegment(_) => false,
        }
    }

    fn entry(&self, claim: ObjectClaimId) -> Entry {
        let mut entries = self
            .entries
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let entry = match entries.iter().position(|(key, _)| *key == claim) {
            Some(index) => entries.remove(index).expect("entry index was found").1,
            None => {
                if entries.len() == CACHE_ENTRIES {
                    entries.pop_front();
                }
                Arc::new(Mutex::new(None))
            }
        };
        entries.push_back((claim, entry.clone()));
        entry
    }

    fn get_or_compute(
        &self,
        claim: ObjectClaimId,
        bytes: &[u8],
        compute: impl FnOnce() -> Option<ObjectId>,
    ) -> Option<ObjectId> {
        if bytes.len() > MAX_OBJECT_RESPONSE_PAYLOAD_BYTES {
            return compute();
        }
        let entry = self.entry(claim);
        let mut cached = entry.lock().unwrap_or_else(|error| error.into_inner());
        if let Some(value) = cached
            .as_ref()
            .filter(|value| value.bytes.as_ref() == bytes)
        {
            return Some(value.object);
        }
        #[cfg(test)]
        self.computations
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let object = compute()?;
        *cached = Some(CachedObject {
            bytes: bytes.into(),
            object,
        });
        Some(object)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::header_protocol::HeaderInventoryRecord;
    use noid_chain::{
        block_header::semantic_header_id, history_step::HistoryStepTerminalMetadata, Block,
    };
    use std::sync::atomic::Ordering;

    fn terminal_claim(height: u64) -> TerminalClaimId {
        TerminalClaimId {
            height,
            semantic_header_id: [7; 32],
            proof_class: 0,
        }
    }

    #[test]
    fn same_bytes_reuse_digest_and_changed_bytes_recompute() {
        let cache = RetainedObjectCache::default();
        let claim = terminal_claim(7);
        let original = vec![1; 4096];
        let expected = TerminalObjectId::from_bytes(claim, &original).unwrap();
        assert_eq!(cache.terminal(claim, &original), Some(expected));
        assert_eq!(cache.terminal(claim, &original.clone()), Some(expected));
        assert_eq!(cache.computations.load(Ordering::Relaxed), 1);

        let mut changed = original.clone();
        changed[2048] ^= 1;
        assert!(!cache.matches_bytes(ObjectId::Terminal(expected), &changed));
        assert_eq!(
            cache.terminal(claim, &changed),
            TerminalObjectId::from_bytes(claim, &changed)
        );
        assert_eq!(cache.computations.load(Ordering::Relaxed), 2);
        assert!(cache.matches_bytes(ObjectId::Terminal(expected), &original));
        assert_eq!(cache.computations.load(Ordering::Relaxed), 3);

        let mut forged = expected;
        forged.byte_digest[0] ^= 1;
        assert!(!cache.matches_bytes(ObjectId::Terminal(forged), &original));
        forged = expected;
        forged.encoded_len -= 1;
        assert!(!cache.matches_bytes(ObjectId::Terminal(forged), &original));
        assert_eq!(cache.computations.load(Ordering::Relaxed), 3);
    }

    #[test]
    fn claims_and_digest_domains_remain_separate() {
        let cache = RetainedObjectCache::default();
        let bytes = [1; 128];
        let claim = terminal_claim(7);
        let first = cache.terminal(claim, &bytes).unwrap();
        for changed in [
            TerminalClaimId { height: 8, ..claim },
            TerminalClaimId {
                semantic_header_id: [8; 32],
                ..claim
            },
            TerminalClaimId {
                proof_class: 1,
                ..claim
            },
        ] {
            assert_eq!(
                cache.terminal(changed, &bytes),
                TerminalObjectId::from_bytes(changed, &bytes)
            );
        }
        let body_claim = BlockBodyClaimId {
            height: 7,
            block_hash: [7; 32],
        };
        let body = cache.block_body(body_claim, &bytes).unwrap();
        assert_ne!(body.byte_digest, first.byte_digest);
        assert_eq!(cache.computations.load(Ordering::Relaxed), 5);
    }

    #[test]
    fn concurrent_identical_requests_hash_once() {
        let cache = RetainedObjectCache::default();
        let bytes = vec![3; 16 * 1024];
        let barrier = std::sync::Barrier::new(8);
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..8)
                .map(|_| {
                    scope.spawn(|| {
                        barrier.wait();
                        cache.terminal(terminal_claim(7), &bytes).unwrap()
                    })
                })
                .collect();
            let objects: Vec<_> = handles
                .into_iter()
                .map(|handle| handle.join().unwrap())
                .collect();
            assert!(objects.iter().all(|object| *object == objects[0]));
        });
        assert_eq!(cache.computations.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn cache_evicts_old_claims_and_never_retains_oversized_bytes() {
        let cache = RetainedObjectCache::default();
        for height in 0..=CACHE_ENTRIES as u64 {
            cache.terminal(terminal_claim(height), &[1]).unwrap();
        }
        assert_eq!(cache.entries.lock().unwrap().len(), CACHE_ENTRIES);
        assert!(!cache
            .entries
            .lock()
            .unwrap()
            .iter()
            .any(|(claim, _)| *claim == ObjectClaimId::Terminal(terminal_claim(0))));
        let oversized = vec![0; MAX_OBJECT_RESPONSE_PAYLOAD_BYTES + 1];
        let expected = TerminalObjectId::from_bytes(terminal_claim(99), &oversized);
        assert_eq!(cache.terminal(terminal_claim(99), &oversized), expected);
        assert!(!cache
            .entries
            .lock()
            .unwrap()
            .iter()
            .any(|(claim, _)| *claim == ObjectClaimId::Terminal(terminal_claim(99))));
    }

    #[test]
    fn cached_inventory_preserves_wire_bytes_pruning_and_header_checks() {
        let cache = RetainedObjectCache::default();
        let mut header = noid_chain::consensus::genesis_header();
        header.height = noid_chain::consensus::params::V2_ACTIVATION_HEIGHT.unwrap_or(1);
        let body = Block {
            header,
            transactions: Vec::new(),
        }
        .to_bytes();
        let mut terminal =
            HistoryStepTerminalMetadata::new(header.height, semantic_header_id(&header), 0)
                .unwrap()
                .encode_prefix()
                .to_vec();
        terminal.extend([5; 128]);
        let cached = |header, body, terminal| {
            HeaderInventoryRecord::from_retained_objects_with(
                header,
                body,
                terminal,
                |claim, bytes| cache.block_body(claim, bytes),
                |claim, bytes| cache.terminal(claim, bytes),
            )
        };
        for (body_bytes, terminal_bytes) in [
            (Some(body.as_slice()), Some(terminal.as_slice())),
            (Some(body.as_slice()), None),
            (None, Some(terminal.as_slice())),
            (None, None),
        ] {
            let expected =
                HeaderInventoryRecord::from_retained_objects(header, body_bytes, terminal_bytes)
                    .unwrap();
            assert_eq!(
                cached(header, body_bytes, terminal_bytes)
                    .unwrap()
                    .encode()
                    .unwrap(),
                expected.encode().unwrap()
            );
        }
        let mut replacement = header;
        replacement.timestamp += 1;
        assert!(cached(replacement, Some(&body), Some(&terminal)).is_err());
        assert!(cached(replacement, None, Some(&terminal)).is_err());
        let changed_body = Block {
            header: replacement,
            transactions: Vec::new(),
        }
        .to_bytes();
        assert_eq!(
            cached(replacement, Some(&changed_body), None).unwrap(),
            HeaderInventoryRecord::from_retained_objects(replacement, Some(&changed_body), None)
                .unwrap()
        );
    }
}
