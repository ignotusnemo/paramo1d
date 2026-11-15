//! Wallet State discovery and transaction delivery over the existing mainnet protocols.
use crate::peer_wallet_view::{CheckedBody, WalletView};
use anyhow::{bail, ensure, Context, Result};
use futures::{stream, StreamExt};
#[cfg(test)]
use noid_chain::block::native_assets::validate_scheduled_block_page_stream;
#[cfg(test)]
use noid_chain::block::payload::BlockBodyPayload;
use noid_chain::{
    block_header::{block_id, BlockHeader},
    exact_state_hash::{slot_leaf_hash, state_node_hash, zero_slot_roots},
    fri_state::SlotValue,
    sparse_merkle::frontier_sibling_positions,
    storage::native_segment::SnapshotSegmentPayload,
};
use noid_p2p::{
    object_protocol::ObjectId,
    protocol::{
        decode_snapshot_manifest_page, GetSnapshotManifestPageRequest, GetStateSegmentRequest,
        MempoolRequest, SnapshotManifestPageObjectId,
    },
};
use noid_poseidon2b::primitives::Address;
use serde_json::{json, Value};
use sha2::{Digest, Sha512};
use std::{
    cell::{Cell, RefCell},
    collections::{BTreeMap, BTreeSet},
    fs::{self, File},
    io::Write,
    path::{Path, PathBuf},
    sync::atomic::{AtomicBool, Ordering},
    time::{Duration, Instant},
};

const MAX_SLOTS: usize = 1_000_000;
const MAX_STATE_BYTES: usize = 64 * 1024 * 1024;
const MAX_TAIL: u64 = 160;
const MAX_INCREMENTAL_BLOCKS: u64 = 32;
static PARANOID: AtomicBool = AtomicBool::new(false);
thread_local! {
    static WALLET: RefCell<Option<(PathBuf, WalletView)>> = const { RefCell::new(None) };
    static NO_RPC: Cell<bool> = const { Cell::new(false) };
    static PAYLOAD_BYTES: Cell<u64> = const { Cell::new(0) };
    static DOWNLOAD: RefCell<Option<WalletDownload>> = const { RefCell::new(None) };
}

struct PreparedWallet {
    view: WalletView,
    bootstrap_slots: usize,
    applied: u64,
    cached_height: Option<u64>,
    used_cache: bool,
    snapshot_ms: u128,
}
struct WalletDownload {
    directory: PathBuf,
    address: Address,
    prior: Option<WalletView>,
    prepared: Option<(PathBuf, PreparedWallet)>,
}
struct DownloadScope(Option<WalletDownload>);
impl Drop for DownloadScope {
    fn drop(&mut self) {
        DOWNLOAD.with(|slot| slot.replace(self.0.take()));
    }
}

pub(crate) fn record_payload(bytes: usize) {
    PAYLOAD_BYTES.with(|v| v.set(v.get().saturating_add(bytes as u64)));
}

pub(crate) fn rpc_forbidden() -> bool {
    PARANOID.load(Ordering::Acquire) || NO_RPC.with(Cell::get)
}
pub(crate) fn set_mode(enabled: bool) {
    PARANOID.store(enabled, Ordering::Release);
}
pub(crate) fn with_policy<T>(enabled: bool, work: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            NO_RPC.with(|v| v.set(self.0));
        }
    }
    let _restore = Restore(NO_RPC.with(|v| v.replace(enabled || v.get())));
    work()
}
pub(crate) fn enabled(args: &Value) -> bool {
    args["paranoid_mode"].as_bool() == Some(true)
}
fn path(args: &Value, key: &str) -> Result<PathBuf> {
    Ok(PathBuf::from(
        args[key]
            .as_str()
            .with_context(|| format!("Missing {key}"))?,
    ))
}
fn slot_owner(slot: SlotValue) -> Address {
    let mut bytes = [0u8; 32];
    bytes[..16].copy_from_slice(&slot.owner_hi.0.to_le_bytes());
    bytes[16..].copy_from_slice(&slot.owner_lo.0.to_le_bytes());
    Address(bytes)
}

/// Sparse exact-Merkle levels. Construction hashes each occupied parent once.
struct Tree {
    levels: Vec<BTreeMap<u32, [u8; 32]>>,
    zeros: Vec<[u8; 32]>,
}
impl Tree {
    fn join(depth: u32, local_depth: u32, segments: Vec<(u16, Tree)>) -> Result<Self> {
        ensure!(
            local_depth <= depth && depth <= 32,
            "P2P segment tree geometry"
        );
        let zeros = zero_slot_roots(depth as usize);
        let mut levels: Vec<BTreeMap<u32, [u8; 32]>> =
            (0..=depth).map(|_| BTreeMap::new()).collect();
        let mut seen = BTreeSet::new();
        for (id, tree) in segments {
            ensure!(
                tree.depth() == local_depth
                    && u64::from(id) < 1u64 << (depth - local_depth)
                    && seen.insert(id),
                "P2P segment tree identity"
            );
            for (level, nodes) in tree.levels.into_iter().enumerate() {
                let base = u32::from(id) << (local_depth - level as u32);
                levels[level].extend(nodes.into_iter().map(|(index, hash)| (base + index, hash)));
            }
        }
        for level in local_depth as usize..depth as usize {
            let parents: BTreeSet<_> = levels[level].keys().map(|i| i >> 1).collect();
            for parent in parents {
                let left = levels[level]
                    .get(&(parent * 2))
                    .copied()
                    .unwrap_or(zeros[level]);
                let right = levels[level]
                    .get(&(parent * 2 + 1))
                    .copied()
                    .unwrap_or(zeros[level]);
                levels[level + 1].insert(parent, state_node_hash(left, right));
            }
        }
        Ok(Self { levels, zeros })
    }
    fn build(depth: u32, slots: &BTreeMap<u32, SlotValue>) -> Result<Self> {
        ensure!(
            (1..=32).contains(&depth) && slots.len() <= MAX_SLOTS,
            "P2P State exceeds mobile budget"
        );
        use rayon::prelude::*;
        let entries: Vec<_> = slots.iter().map(|(&i, &v)| (i, v)).collect();
        let hashes: Vec<_> = entries
            .par_iter()
            .map(|&(i, v)| (i, slot_leaf_hash(v)))
            .collect();
        let zeros = zero_slot_roots(depth as usize);
        let mut levels: Vec<BTreeMap<u32, [u8; 32]>> = vec![hashes.into_iter().collect()];
        for level in 0..depth as usize {
            crate::mobile_control::check()?;
            let children = &levels[level];
            let parents: BTreeSet<_> = children.keys().map(|i| i >> 1).collect();
            let next: Vec<_> = parents
                .into_iter()
                .collect::<Vec<_>>()
                .par_iter()
                .map(|&parent| {
                    let left = children.get(&(parent * 2)).copied().unwrap_or(zeros[level]);
                    let right = children
                        .get(&(parent * 2 + 1))
                        .copied()
                        .unwrap_or(zeros[level]);
                    (parent, state_node_hash(left, right))
                })
                .collect();
            levels.push(next.into_iter().collect());
        }
        Ok(Self { levels, zeros })
    }
    fn depth(&self) -> u32 {
        self.levels.len() as u32 - 1
    }
    fn node(&self, level: usize, index: u32) -> [u8; 32] {
        self.levels[level]
            .get(&index)
            .copied()
            .unwrap_or(self.zeros[level])
    }
    fn root(&self) -> [u8; 32] {
        self.node(self.depth() as usize, 0)
    }
    #[cfg(test)]
    fn update(&mut self, mut index: u32, value: SlotValue) {
        let mut hash = slot_leaf_hash(value);
        for level in 0..self.levels.len() {
            if hash == self.zeros[level] {
                self.levels[level].remove(&index);
            } else {
                self.levels[level].insert(index, hash);
            }
            if level + 1 == self.levels.len() {
                break;
            }
            let sibling = self.node(level, index ^ 1);
            hash = if index & 1 == 0 {
                state_node_hash(hash, sibling)
            } else {
                state_node_hash(sibling, hash)
            };
            index >>= 1;
        }
    }
    #[cfg(test)]
    fn expand(&mut self) {
        let depth = self.depth() as usize;
        let old = self.root();
        let zero = state_node_hash(self.zeros[depth], self.zeros[depth]);
        self.zeros.push(zero);
        self.levels.push(BTreeMap::from([(
            0,
            state_node_hash(old, self.zeros[depth]),
        )]));
    }
}

struct StateImage {
    header: BlockHeader,
    slots: BTreeMap<u32, SlotValue>,
    tree: Tree,
}
impl StateImage {
    #[cfg(test)]
    fn new(header: BlockHeader, slots: BTreeMap<u32, SlotValue>) -> Result<Self> {
        let tree = Tree::build(header.log_slots, &slots)?;
        Self::with_tree(header, slots, tree)
    }
    fn with_tree(header: BlockHeader, slots: BTreeMap<u32, SlotValue>, tree: Tree) -> Result<Self> {
        ensure!(
            slots.len() as u64 == header.active_slot_count,
            "P2P State live count mismatch"
        );
        ensure!(
            slots
                .iter()
                .all(|(&i, v)| u64::from(i) < 1u64 << header.log_slots
                    && !v.is_empty()
                    && noid_chain::consensus::params::creation_id_within_boundary(
                        v.creation_id(),
                        header.alloc_counter,
                        header.height
                    )),
            "P2P State slot boundary"
        );
        ensure!(
            tree.depth() == header.log_slots && tree.root() == header.state_root,
            "P2P State root mismatch"
        );
        Ok(Self {
            header,
            slots,
            tree,
        })
    }
    fn proofs(&self, address: Address) -> Result<Vec<crate::mobile_wallet::Proof>> {
        let mut indices: Vec<u32> = self
            .slots
            .iter()
            .filter(|(_, v)| {
                slot_owner(**v) == address
                    && noid_tx::native_assets::native_sequence(v.creation_id()).is_err()
            })
            .map(|(&i, _)| i)
            .collect();
        ensure!(
            indices.len() <= 4096,
            "Wallet scan exceeds mobile input budget"
        );
        let mut seed = Sha512::new();
        seed.update(b"Paramo1d/P2P/empty-slots/1");
        seed.update(address.0);
        seed.update(block_id(&self.header));
        let salt = seed.finalize();
        let mut empty = BTreeSet::new();
        for nonce in 0u32..4096 {
            let mut hash = Sha512::new();
            hash.update(salt);
            hash.update(nonce.to_le_bytes());
            let bytes = hash.finalize();
            let index = (u64::from_le_bytes(bytes[..8].try_into()?)
                % (1u64 << self.header.log_slots)) as u32;
            if !self.slots.contains_key(&index) {
                empty.insert(index);
                if empty.len() == 16 {
                    break;
                }
            }
        }
        ensure!(empty.len() >= 2, "P2P State has no available output slots");
        indices.extend(empty);
        indices.sort_unstable();
        indices.dedup();
        indices
            .chunks(8)
            .map(|chunk| {
                let slots = chunk
                    .iter()
                    .map(|&index| {
                        let slot = self.slots.get(&index).copied().unwrap_or(SlotValue::EMPTY);
                        crate::mobile_wallet::Slot {
                            slot_index: index,
                            value: slot.amount(),
                            creation_id: slot.creation_id(),
                            owner: if slot.is_empty() {
                                String::new()
                            } else {
                                slot_owner(slot).to_bech32()
                            },
                            empty: slot.is_empty(),
                        }
                    })
                    .collect();
                let siblings = frontier_sibling_positions(chunk, self.header.log_slots)
                    .map_err(|e| anyhow::anyhow!("P2P slot frontier: {e}"))?
                    .iter()
                    .map(|p| hex::encode(self.tree.node(p.level as usize, p.node_index as u32)))
                    .collect();
                Ok(crate::mobile_wallet::Proof {
                    height: self.header.height,
                    block_hash: hex::encode(block_id(&self.header)),
                    state_root: hex::encode(self.header.state_root),
                    log_slots: self.header.log_slots,
                    slots,
                    siblings,
                })
            })
            .collect()
    }
}

fn authenticated_header(bundle: &Path, height: u64) -> Result<BlockHeader> {
    crate::headers::read_header(&mut File::open(bundle.join("headers.bin"))?, height)
}

fn segment_batches(descriptors: Vec<(u16, [u8; 32], u32)>) -> Vec<Vec<(u16, [u8; 32], u32)>> {
    let mut batches = Vec::new();
    let mut batch = Vec::new();
    let mut bytes = 0usize;
    for descriptor in descriptors {
        let size = descriptor.2 as usize;
        if !batch.is_empty()
            && (batch.len() >= noid_p2p::protocol::MAX_STATE_SEGMENT_BATCH
                || bytes.saturating_add(size) > noid_p2p::protocol::MAX_STATE_SEGMENT_BATCH_BYTES)
        {
            batches.push(std::mem::take(&mut batch));
            bytes = 0;
        }
        bytes += size;
        batch.push(descriptor);
    }
    if !batch.is_empty() {
        batches.push(batch);
    }
    batches
}

async fn snapshot(
    network: &crate::mobile::Network,
    directory: &Path,
    bundle: &Path,
    tip: u64,
) -> Result<(StateImage, Vec<CheckedBody>)> {
    let peers = network.ready().await?;
    let mut pending_manifests = stream::iter(
        peers
            .iter()
            .copied()
            .map(|peer| async move { (peer, network.manifest(peer).await) }),
    )
    .buffer_unordered(4);
    let mut manifests = Vec::new();
    while let Some((peer, result)) = pending_manifests.next().await {
        if let Ok(manifest) = result {
            if manifest.tip_height > 0 && manifest.has_valid_manifest_digest() {
                manifests.push((peer, manifest));
            }
        }
    }
    let mut choices: Vec<_> = manifests
        .iter()
        .filter(|(_, m)| m.tip_height <= tip)
        .cloned()
        .collect();
    choices.sort_by_key(|(_, m)| std::cmp::Reverse(m.tip_height));
    let mut last = anyhow::anyhow!("Peers have no available State snapshot");
    for (peer, manifest) in choices {
        let result = async {
            let header = authenticated_header(bundle, manifest.tip_height)?;
            ensure!(
                block_id(&header) == manifest.tip_hash
                    && header.state_root == manifest.state_root
                    && header.log_slots == manifest.log_slots
                    && header.active_slot_count == manifest.active_slot_count
                    && header.alloc_counter == manifest.alloc_counter
                    && manifest.eff_log == header.log_slots.min(16) as u8,
                "P2P manifest header binding"
            );
            ensure!(
                manifest.active_slot_count as usize <= MAX_SLOTS,
                "P2P State exceeds mobile slot budget"
            );
            ensure!(
                tip.saturating_sub(header.height) <= MAX_TAIL,
                "P2P snapshot tail budget"
            );
            // Retain the short tail before downloading the larger snapshot.
            // Its oldest bodies may be pruned while proof verification runs.
            let tail = collect_bodies(
                network,
                directory,
                bundle,
                header.height + 1,
                tip,
                Some(peer),
            )
            .await?;
            let snapshot_id = manifest.snapshot_id().context("P2P snapshot identity")?;
            let mut descriptors = Vec::new();
            for page in &manifest.descriptor_pages {
                let data = network
                    .page(
                        peer,
                        GetSnapshotManifestPageRequest {
                            object: SnapshotManifestPageObjectId {
                                snapshot: snapshot_id,
                                page: *page,
                            },
                        },
                    )
                    .await?;
                descriptors.extend(
                    decode_snapshot_manifest_page(*page, &data)
                        .context("P2P manifest descriptors")?,
                );
            }
            ensure!(
                descriptors.len() == manifest.segment_count as usize
                    && descriptors.windows(2).all(|p| p[0].0 < p[1].0),
                "P2P descriptor order"
            );
            let declared = descriptors
                .iter()
                .try_fold(0usize, |total, d| total.checked_add(d.2 as usize))
                .context("P2P State byte overflow")?;
            ensure!(
                declared <= MAX_STATE_BYTES,
                "P2P State exceeds mobile download budget"
            );
            let batches = segment_batches(descriptors);
            let mut pending = stream::iter(batches.into_iter().map(|batch| {
                let network = network.clone();
                let manifests = manifests.clone();
                let manifest = manifest.clone();
                async move {
                    let mut sources = manifests;
                    sources.retain(|(p, _)| *p != peer);
                    sources.insert(0, (peer, manifest.clone()));
                    let mut remaining: BTreeMap<_, _> = batch
                        .into_iter()
                        .map(|(id, root, len)| (id, (root, len)))
                        .collect();
                    let mut found = Vec::new();
                    for (source, generation) in sources {
                        crate::mobile_control::check()?;
                        let mut ids = remaining.keys().copied();
                        let Some(first) = ids.next() else {
                            break;
                        };
                        let request = GetStateSegmentRequest {
                            segment_id: first,
                            additional_segments: ids.collect(),
                            expected_tip_height: generation.tip_height,
                            expected_tip_hash: generation.tip_hash,
                            manifest_digest: generation.manifest_digest,
                        };
                        let Ok(parts) = network.segments(source, request).await else {
                            continue;
                        };
                        for (id, bytes) in parts {
                            let Some(&(root, len)) = remaining.get(&id) else {
                                continue;
                            };
                            if bytes.len() != len as usize {
                                continue;
                            }
                            let Some(payload) =
                                SnapshotSegmentPayload::decode(&bytes, generation.tip_height)
                            else {
                                continue;
                            };
                            if payload.sparse().effective_log_segment() != manifest.eff_log {
                                continue;
                            }
                            let slots: Vec<_> = payload.sparse().entries().collect();
                            let local: BTreeMap<_, _> =
                                slots.iter().map(|&(i, v)| (u32::from(i), v)).collect();
                            let tree = Tree::build(manifest.eff_log.into(), &local)?;
                            // Identical committed subtree roots allow a peer's
                            // newer export to fill an older snapshot safely.
                            if local.is_empty() || tree.root() != root {
                                continue;
                            }
                            remaining.remove(&id);
                            found.push((id, slots, bytes.len(), tree));
                        }
                    }
                    ensure!(
                        remaining.is_empty(),
                        "Peers could not supply authenticated State segments {:?}",
                        remaining.keys().collect::<Vec<_>>()
                    );
                    Ok::<_, anyhow::Error>(found)
                }
            }))
            .buffer_unordered(4);
            let mut slots = BTreeMap::new();
            let mut trees = Vec::new();
            while let Some(parts) = pending.next().await {
                for (id, entries, _bytes, tree) in parts? {
                    trees.push((id, tree));
                    for (local, value) in entries {
                        slots.insert(
                            (u32::from(id) << manifest.eff_log) | u32::from(local),
                            value,
                        );
                    }
                    ensure!(
                        slots.len() <= MAX_SLOTS,
                        "P2P State exceeds mobile slot budget"
                    );
                }
            }
            let tree = Tree::join(header.log_slots, manifest.eff_log.into(), trees)?;
            Ok((StateImage::with_tree(header, slots, tree)?, tail))
        }
        .await;
        match result {
            Ok(image) => return Ok(image),
            Err(error) => {
                eprintln!("  P2P STATE  Source retry: {error:#}");
                last = error;
            }
        }
    }
    Err(last)
}

async fn body_with_hint(
    network: &crate::mobile::Network,
    expected: BlockHeader,
    hint: Option<(libp2p::PeerId, noid_p2p::object_protocol::BlockBodyObjectId)>,
) -> Result<(Vec<u8>, CheckedBody)> {
    let mut peers = network.ready().await?;
    if let Some((primary, _)) = hint {
        peers.retain(|peer| *peer != primary);
        peers.insert(0, primary);
    }
    let mut pending = stream::iter(peers.into_iter().enumerate().map(|(position, peer)| {
        async move {
            // Give the advertised source a short head start. Other sources
            // can complete the same committed object without its timeout.
            if position > 0 {
                tokio::time::sleep(std::time::Duration::from_millis(150)).await;
            }
            let object = if let Some((_, object)) = hint.filter(|(source, _)| *source == peer) {
                object
            } else {
                let response = network
                    .headers_with_inventory(peer, expected.height, 1, true)
                    .await?;
                response
                    .records
                    .first()
                    .filter(|r| r.header == expected)
                    .and_then(|r| r.body)
                    .context("Peer block inventory unavailable")?
            };
            let bytes = network.object(peer, ObjectId::BlockBody(object)).await?;
            let checked = CheckedBody::decode(&bytes, expected)?;
            Ok::<_, anyhow::Error>((bytes, checked))
        }
    }))
    .buffer_unordered(4);
    let mut last = "No usable body source".to_string();
    while let Some(result) = pending.next().await {
        crate::mobile_control::check()?;
        match result {
            Ok(bytes) => return Ok(bytes),
            Err(error) => last = error.to_string(),
        }
    }
    bail!("Peers cannot supply block {}: {}", expected.height, last)
}

fn cached_wallet(args: &Value, address: Address) -> Option<WalletView> {
    let file = path(args, "data_dir").ok()?.join("p2p-wallet.json");
    let value: Value =
        serde_json::from_slice(&crate::artifacts::read_bounded(&file, 2 * 1024 * 1024).ok()?)
            .ok()?;
    WalletView::open(args, address, &value).ok()
}

fn save_wallet(args: &Value, view: &WalletView) -> Result<()> {
    if !args["seed_hex"].is_string() {
        return Ok(());
    }
    let directory = path(args, "data_dir")?;
    let mut file = tempfile::NamedTempFile::new_in(&directory)?;
    file.write_all(&serde_json::to_vec(&view.seal(args)?)?)?;
    file.as_file().sync_all()?;
    file.persist(directory.join("p2p-wallet.json"))
        .map_err(|e| e.error)?;
    Ok(())
}

async fn collect_bodies(
    network: &crate::mobile::Network,
    directory: &Path,
    bundle: &Path,
    start: u64,
    tip: u64,
    primary: Option<libp2p::PeerId>,
) -> Result<Vec<CheckedBody>> {
    if start > tip {
        return Ok(Vec::new());
    }
    ensure!(tip - start < MAX_TAIL, "P2P wallet tail budget");
    let headers = (start..=tip)
        .map(|height| authenticated_header(bundle, height))
        .collect::<Result<Vec<_>>>()?;
    let primary = match primary {
        Some(peer) => Some(peer),
        None => network.ready().await?.first().copied(),
    };
    let mut hints = BTreeMap::new();
    if let Some(peer) = primary {
        for chunk in headers.chunks(64) {
            if chunk.iter().all(|h| {
                directory
                    .join("p2p-blocks")
                    .join(format!("{}.body", hex::encode(block_id(h))))
                    .is_file()
            }) {
                continue;
            }
            if let Ok(response) = network
                .headers_with_inventory(peer, chunk[0].height, chunk.len() as u16, true)
                .await
            {
                for record in response.records {
                    if chunk.iter().any(|h| *h == record.header) {
                        if let Some(body) = record.body {
                            hints.insert(record.header.height, (peer, body));
                        }
                    }
                }
            }
        }
    }
    let mut pending = stream::iter(headers.into_iter().map(|header| {
        let hint = hints.get(&header.height).copied();
        async move { cached_body_with_hint(network, directory, header, hint).await }
    }))
    .buffered(4);
    let mut result = Vec::new();
    let mut bytes = 0usize;
    while let Some(body) = pending.next().await {
        let body = body?;
        bytes = bytes
            .checked_add(body.wire_bytes)
            .context("P2P tail byte count")?;
        ensure!(bytes <= MAX_STATE_BYTES, "P2P tail download budget");
        result.push(body);
    }
    Ok(result)
}

async fn advance_wallet(
    network: &crate::mobile::Network,
    directory: &Path,
    bundle: &Path,
    tip: u64,
    view: &mut WalletView,
) -> Result<u64> {
    let bodies = collect_bodies(
        network,
        directory,
        bundle,
        view.header.height + 1,
        tip,
        None,
    )
    .await?;
    let count = bodies.len() as u64;
    for body in bodies {
        view.apply_checked(&body)?;
    }
    Ok(count)
}

async fn download_wallet(
    network: &crate::mobile::Network,
    directory: &Path,
    bundle: &Path,
    tip: u64,
    address: Address,
    prior: Option<WalletView>,
) -> Result<PreparedWallet> {
    let _waiting = crate::mobile_control::waiting_for_network("wallet-data");
    let cached_height = prior.as_ref().map(|v| v.header.height);
    if let Some(mut view) = prior.filter(|v| {
        v.header.height <= tip
            && tip - v.header.height <= MAX_INCREMENTAL_BLOCKS
            && authenticated_header(bundle, v.header.height).is_ok_and(|h| h == v.header)
    }) {
        match advance_wallet(network, directory, bundle, tip, &mut view).await {
            Ok(applied) if view.slots.values().filter(|v| v.is_empty()).count() >= 2 => {
                return Ok(PreparedWallet {
                    view,
                    bootstrap_slots: 0,
                    applied,
                    cached_height,
                    used_cache: true,
                    snapshot_ms: 0,
                });
            }
            _ => {
                crate::mobile_control::check()?;
            }
        }
    }
    crate::mobile_control::finding_coins();
    let began = Instant::now();
    let (image, tail) = snapshot(network, directory, bundle, tip).await?;
    let bootstrap_slots = image.slots.len();
    let proofs = image.proofs(address)?;
    let mut view = WalletView::from_proofs(image.header, address, &proofs)?;
    drop(image);
    let applied = tail.len() as u64;
    for body in tail {
        view.apply_checked(&body)?;
    }
    Ok(PreparedWallet {
        view,
        bootstrap_slots,
        applied,
        cached_height,
        used_cache: false,
        snapshot_ms: began.elapsed().as_millis(),
    })
}

/// Download into an untrusted staging slot. Only fetch_wallet can promote
/// the result after the matching complete recursive proof has been accepted.
pub(crate) async fn prepare_candidate(
    network: &crate::mobile::Network,
    bundle: &Path,
    identity: &Path,
    tip: u64,
) -> Result<()> {
    let context = DOWNLOAD.with(|slot| {
        slot.borrow()
            .as_ref()
            .map(|v| (v.directory.clone(), v.address, v.prior.clone()))
    });
    let Some((directory, address, prior)) = context else {
        return Ok(());
    };
    let prepared = download_wallet(network, &directory, bundle, tip, address, prior).await?;
    DOWNLOAD.with(|slot| {
        if let Some(request) = slot.borrow_mut().as_mut() {
            request.prepared = Some((identity.to_path_buf(), prepared));
        }
    });
    Ok(())
}

fn bind_verified_wallet(view: &WalletView, verified: &Value) -> Result<()> {
    ensure!(
        Some(view.header.height) == verified["height"].as_u64()
            && verified["block_hash"].as_str()
                == Some(hex::encode(block_id(&view.header)).as_str())
            && verified["state_root"].as_str()
                == Some(hex::encode(view.header.state_root).as_str()),
        "P2P wallet verified boundary"
    );
    Ok(())
}

pub(crate) fn fetch_wallet(args: &Value, address: Address) -> Result<WalletView> {
    let artifacts = path(args, "artifacts")?;
    let directory = path(args, "data_dir")?;
    let started = Instant::now();
    let requests = crate::rpc::request_count();
    PAYLOAD_BYTES.with(|v| v.set(0));
    let prior = WALLET
        .with(|slot| {
            slot.borrow()
                .as_ref()
                .filter(|(p, v)| p == &directory && v.address == address)
                .map(|(_, v)| v.clone())
        })
        .or_else(|| cached_wallet(args, address));
    let _scope = DownloadScope(DOWNLOAD.with(|slot| {
        slot.replace(Some(WalletDownload {
            directory: directory.clone(),
            address,
            prior,
            prepared: None,
        }))
    }));
    let sync = crate::mobile::run(artifacts.clone(), directory.clone(), true)?;
    let chain_check_ms = started.elapsed().as_millis();
    let tip = sync["verified"]["height"]
        .as_u64()
        .context("Verified P2P tip")?;
    let bundle = crate::courier_api::accepted_bundle(&directory)?;
    let prepared = DOWNLOAD
        .with(|slot| slot.borrow_mut().as_mut().and_then(|v| v.prepared.take()))
        .filter(|(p, _)| p == &bundle);
    let data_before_proof = prepared.is_some();
    let prepared = if let Some((_, prepared)) = prepared {
        prepared
    } else {
        crate::mobile::with_peers(&artifacts, |executor, network| {
            executor.block_on(crate::mobile_control::cancellable(async {
                prepare_candidate(&network, &bundle, &bundle, tip).await?;
                DOWNLOAD
                    .with(|slot| slot.borrow_mut().as_mut().and_then(|v| v.prepared.take()))
                    .map(|(_, v)| v)
                    .context("P2P wallet preparation")
            }))
        })?
    };
    let view = prepared.view;
    bind_verified_wallet(&view, &sync["verified"])?;
    save_wallet(args, &view)?;
    let bytes = PAYLOAD_BYTES.with(Cell::get);
    let requests = crate::rpc::request_count().saturating_sub(requests);
    ensure!(requests == 0, "P2P wallet used server RPC");
    let metrics = json!({"height":tip,"bootstrap_live_slots":prepared.bootstrap_slots,
        "retained_wallet_slots":view.slots.len(),"p2p_decoded_data_bytes":bytes,
        "elapsed_ms":started.elapsed().as_millis(),"rpc_requests":requests,
        "applied_blocks":prepared.applied,"reused_wallet_view":prepared.used_cache,
        "cached_wallet_height":prepared.cached_height,"transport":"direct-p2p",
        "snapshot_ms":prepared.snapshot_ms,"data_before_proof":data_before_proof,
        "chain_check_ms":chain_check_ms,"header_ms":sync["verified"]["header_ms"],
        "proof_ms":sync["verified"]["proof_ms"],"origin_ms":sync["verified"]["origin_ms"],
        "proof_class":sync["verified"]["proof_class"],"reused_headers":sync["verified"]["reused_headers"],
        "runtime_load_ms":sync["runtime_load_ms"],"resume_ms":sync["resume_ms"],
        "discovery_ms":sync["discovery_ms"],"transfer_ms":sync["transfer_ms"]});
    fs::write(
        directory.join("p2p-metrics.json"),
        serde_json::to_vec(&metrics)?,
    )?;
    WALLET.with(|slot| slot.replace(Some((directory, view.clone()))));
    Ok(view)
}

pub(crate) fn probe(args: &Value) -> Result<Value> {
    let address = Address::parse(args["address"].as_str().context("Probe address")?)
        .map_err(|e| anyhow::anyhow!("Probe address: {e}"))?;
    let view = fetch_wallet(args, address)?;
    let mut metrics: Value =
        serde_json::from_slice(&fs::read(path(args, "data_dir")?.join("p2p-metrics.json"))?)?;
    let balance = view
        .slots
        .values()
        .filter(|v| !v.is_empty())
        .try_fold(0u64, |sum, v| sum.checked_add(v.amount()))
        .context("Probe balance overflow")?;
    metrics["balance_micronoid"] = json!(balance.to_string());
    Ok(metrics)
}

type WatchHeaders = (
    libp2p::PeerId,
    Vec<noid_p2p::header_protocol::HeaderInventoryRecord>,
    bool,
);

fn continuation_records(
    anchor: &BlockHeader,
    mut records: Vec<noid_p2p::header_protocol::HeaderInventoryRecord>,
) -> Result<(Vec<noid_p2p::header_protocol::HeaderInventoryRecord>, bool)> {
    ensure!(
        !records.is_empty() && records.len() <= 65 && records[0].header == *anchor,
        "P2P watch anchor"
    );
    ensure!(
        records
            .windows(2)
            .all(|p| p[1].header.height == p[0].header.height + 1
                && p[1].header.prev_block_hash == block_id(&p[0].header)),
        "P2P watch header continuity"
    );
    let count = records.len();
    let available = records
        .iter()
        .rposition(|r| r.terminal.is_some())
        .unwrap_or(0);
    ensure!(
        count == 1 || available > 0,
        "P2P watch proof is unavailable"
    );
    records.truncate(available + 1);
    records.remove(0);
    Ok((records, count == 65 && available > 0))
}

async fn watch_headers(
    network: &crate::mobile::Network,
    anchor: &BlockHeader,
) -> Result<Option<WatchHeaders>> {
    let peers = network.ready().await?;
    let pending = stream::iter(peers.into_iter().map(|peer| async move {
        (
            peer,
            network
                .headers_with_inventory(peer, anchor.height, 65, true)
                .await,
        )
    }))
    .buffer_unordered(8);
    collect_watch_headers(anchor, pending, Duration::from_millis(400)).await
}

async fn collect_watch_headers(
    anchor: &BlockHeader,
    mut pending: impl futures::Stream<
            Item = (
                libp2p::PeerId,
                Result<noid_p2p::protocol::GetHeadersResponse>,
            ),
        > + Unpin,
    settle: Duration,
) -> Result<Option<WatchHeaders>> {
    let mut best: Option<WatchHeaders> = None;
    let mut conflicting = false;
    let mut unavailable_extension = false;
    let mut deadline = tokio::time::Instant::now() + Duration::from_secs(8);
    while let Ok(Some((peer, result))) = tokio::time::timeout_at(deadline, pending.next()).await {
        let Ok(response) = result else {
            continue;
        };
        if response
            .records
            .first()
            .is_some_and(|r| r.header.height == anchor.height && r.header != *anchor)
        {
            conflicting = true;
            continue;
        }
        let advanced = response.records.len() > 1;
        match continuation_records(anchor, response.records) {
            Ok((records, more)) => {
                let height = records.last().map_or(anchor.height, |r| r.header.height);
                if best.is_none() {
                    // Watch responses only schedule a verified refresh. Let other
                    // responsive peers contribute without waiting for every timeout.
                    deadline = deadline.min(tokio::time::Instant::now() + settle);
                }
                if best.as_ref().is_none_or(|(_, r, _)| {
                    height > r.last().map_or(anchor.height, |r| r.header.height)
                }) {
                    best = Some((peer, records, more));
                }
            }
            Err(_) => {
                unavailable_extension |= advanced;
            }
        }
    }
    if conflicting || unavailable_extension && best.as_ref().is_none_or(|(_, r, _)| r.is_empty()) {
        return Ok(None);
    }
    Ok(Some(best.context("P2P wallet continuation unavailable")?))
}

pub(crate) fn watch(
    args: &Value,
    address: Address,
) -> Result<Option<crate::mobile_wallet::WalletHint>> {
    let directory = path(args, "data_dir")?;
    let file = directory.join("wallet-view.json");
    if !file.is_file() {
        return Ok(None);
    }
    let saved: Value =
        serde_json::from_slice(&crate::artifacts::read_bounded(&file, 2 * 1024 * 1024)?)?;
    if saved["source"].as_str() != Some("direct-p2p") || saved["projection"].is_null() {
        return Ok(None);
    }
    let (verified, proof_header, _) = crate::wallet_checkpoint::open(args, &saved["checkpoint"])?;
    let old = WalletView::open(args, address, &saved["projection"])?;
    ensure!(old.header == proof_header, "Wallet projection checkpoint");
    let artifacts = path(args, "artifacts")?;
    WALLET.with(|cache| {
        let mut view = match cache
            .borrow_mut()
            .take()
            .filter(|(p, v)| p == &directory && v.address == address)
            .map(|(_, v)| v)
            .or_else(|| cached_wallet(args, address))
        {
            Some(view) => view,
            None => return Ok(None),
        };
        let result = crate::mobile::with_peers(&artifacts, |executor, network| {
            executor.block_on(crate::mobile_control::cancellable(async {
                let _waiting = crate::mobile_control::waiting_for_network("wallet-watch");
                tokio::time::timeout(Duration::from_secs(20), async {
                    let began = view.header.height;
                    loop {
                        let Some((source, records, more)) =
                            watch_headers(&network, &view.header).await?
                        else {
                            return Ok(None);
                        };
                        if records.last().is_some_and(|r| {
                            r.header.height.saturating_sub(began) > MAX_INCREMENTAL_BLOCKS
                        }) {
                            return Ok(None);
                        }
                        let mut bodies = stream::iter(records.into_iter().map(|record| {
                            let network = &network;
                            let directory = &directory;
                            async move {
                                cached_body_with_hint(
                                    network,
                                    directory,
                                    record.header,
                                    record.body.map(|body| (source, body)),
                                )
                                .await
                            }
                        }))
                        .buffered(4);
                        while let Some(bytes) = bodies.next().await {
                            crate::mobile_control::check()?;
                            view.apply_checked(&bytes?)?;
                        }
                        if !more {
                            break;
                        }
                    }
                    let same_epoch = old.coin_set().is_empty()
                        || noid_chain::consensus::tx_epoch_anchor_height_for_child(
                            verified.height + 1,
                        ) == noid_chain::consensus::tx_epoch_anchor_height_for_child(
                            view.header.height + 1,
                        );
                    Ok(Some(if view.coin_set() != old.coin_set() {
                        crate::mobile_wallet::WalletHint::CoinsChanged
                    } else if !same_epoch {
                        crate::mobile_wallet::WalletHint::EpochChanged
                    } else {
                        crate::mobile_wallet::WalletHint::Unchanged
                    }))
                })
                .await
                .unwrap_or(Ok(None))
            }))
        });
        match result {
            Ok(same) => {
                *cache.borrow_mut() = Some((directory, view));
                Ok(same)
            }
            Err(error) => {
                crate::mobile_control::check()?;
                eprintln!("  P2P WATCH Refresh: {error:#}");
                Ok(None)
            }
        }
    })
}

#[cfg(test)]
fn coins(slots: &BTreeMap<u32, SlotValue>, address: Address) -> BTreeMap<u32, (u64, u64)> {
    slots
        .iter()
        .filter(|(_, v)| {
            !v.is_empty()
                && slot_owner(**v) == address
                && noid_tx::native_assets::native_sequence(v.creation_id()).is_err()
        })
        .map(|(&i, v)| (i, (v.amount(), v.creation_id())))
        .collect()
}

async fn cached_body(
    network: &crate::mobile::Network,
    directory: &Path,
    header: BlockHeader,
) -> Result<CheckedBody> {
    cached_body_with_hint(network, directory, header, None).await
}

async fn cached_body_with_hint(
    network: &crate::mobile::Network,
    directory: &Path,
    header: BlockHeader,
    hint: Option<(libp2p::PeerId, noid_p2p::object_protocol::BlockBodyObjectId)>,
) -> Result<CheckedBody> {
    let folder = directory.join("p2p-blocks");
    fs::create_dir_all(&folder)?;
    let file = folder.join(format!("{}.body", hex::encode(block_id(&header))));
    let cap = noid_chain::block::payload::block_body_payload_bytes_limit(header.height) as u64;
    if let Ok(bytes) = crate::artifacts::read_bounded(&file, cap) {
        if let Ok(checked) = CheckedBody::decode(&bytes, header) {
            return Ok(checked);
        }
    }
    let (bytes, checked) = body_with_hint(network, header, hint).await?;
    let mut temporary = tempfile::NamedTempFile::new_in(&folder)?;
    temporary.write_all(&bytes)?;
    temporary.persist(&file).map_err(|e| e.error)?;
    let mut files = Vec::new();
    let mut total = 0u64;
    for entry in fs::read_dir(&folder)?.take(512) {
        let entry = entry?;
        if entry.path().extension().is_some_and(|v| v == "body") {
            let metadata = entry.metadata()?;
            total = total.saturating_add(metadata.len());
            files.push((metadata.modified()?, entry.path(), metadata.len()));
        }
    }
    files.sort_by_key(|f| f.0);
    let mut count = files.len();
    for (_, path, len) in files {
        if count <= 192 && total <= 64 * 1024 * 1024 {
            break;
        }
        fs::remove_file(path)?;
        count -= 1;
        total = total.saturating_sub(len);
    }
    Ok(checked)
}

pub(crate) fn transaction_status(args: &Value, txid: &str) -> Result<Value> {
    let artifacts = path(args, "artifacts")?;
    crate::mobile::with_peers(&artifacts, |executor, mut network| {
        executor.block_on(async {
        let candidates=crate::mobile::discover(&mut network).await?;
        let (source,point)=candidates.first().context("P2P tip unavailable")?;
        let start=point.height.saturating_sub(noid_chain::consensus::params::RECENT_BLOCK_RETENTION_DEPTH);
        let records=network.headers_with_inventory(*source,start,(point.height-start+1) as u16,true).await?.records;
        for record in records.into_iter().rev() {
            crate::mobile_control::check()?;
            if let Ok(checked)=cached_body(&network,&path(args,"data_dir")?,record.header).await {
                if let Some(mut receipt)=crate::courier_api::receipt_for_body(checked.payload(),txid)? {
                    receipt["transport"]=json!("direct-p2p");return Ok(receipt);
                }
            }
        }
        for peer in network.ready().await?.into_iter().take(2) {
            if let Ok(pool)=network.pool(peer,MempoolRequest::Pull).await {
                if pool.txs.iter().any(|bytes|noid_tx::PagedSpendIntent::from_bytes(bytes).is_ok_and(|intent|hex::encode(intent.logical_txid().0)==txid)) {
                    return Ok(json!({"txid":txid,"stage":"in_mempool","receipt_hex":null,"transport":"direct-p2p"}));
                }
            }
        }
        Ok(json!({"txid":txid,"stage":"unknown","receipt_hex":null,"transport":"direct-p2p"}))
    })
    })
}

pub(crate) fn broadcast(args: &Value, intent: Vec<u8>, txid: &str) -> Result<Value> {
    let artifacts = path(args, "artifacts")?;
    crate::mobile::with_peers(&artifacts, |executor, network| {
        executor.block_on(async {
        let peers=network.ready().await?;let mut pending=stream::iter(peers.into_iter().take(4).map(|peer| {
            let network=network.clone();let bytes=intent.clone();async move {network.pool(peer,MempoolRequest::Push { intent_bytes:bytes,inbound_memory_permit:None }).await}
        })).buffer_unordered(4);
        let mut delivered=0;
        while let Some(result)=pending.next().await {if result.is_ok(){delivered+=1;}}
        ensure!(delivered>0,"P2P peers could not receive the payment");
        Ok(json!({"submitted":true,"confirmed":false,"txid":txid,"transport":"direct-p2p","peer_deliveries":delivered}))
    })
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_chain::sparse_merkle::SparseMerkleCache;

    fn fixture() -> StateImage {
        let owner = Address([17; 32]);
        let slots = BTreeMap::from([
            (
                3,
                SlotValue::with_owner_fields(100_000, 1, owner.as_fields()),
            ),
            (
                93,
                SlotValue::with_owner_fields(
                    400_000,
                    noid_tx::native_assets::native_creation_id(2).unwrap(),
                    owner.as_fields(),
                ),
            ),
            (
                200,
                SlotValue::with_owner_fields(
                    50_000,
                    noid_chain::consensus::params::coinbase_creation_id(299999),
                    Address([18; 32]).as_fields(),
                ),
            ),
        ]);
        let mut header = noid_chain::consensus::genesis::genesis_header();
        header.height = 300000;
        header.log_slots = 8;
        header.active_slot_count = 3;
        header.alloc_counter = 7;
        header.state_root = Tree::build(8, &slots).unwrap().root();
        StateImage::new(header, slots).unwrap()
    }

    #[test]
    fn prefetched_wallet_requires_the_matching_verified_boundary() {
        let image = fixture();
        let owner = Address([17; 32]);
        let view =
            WalletView::from_proofs(image.header, owner, &image.proofs(owner).unwrap()).unwrap();
        let valid = json!({"height":view.header.height,"block_hash":hex::encode(block_id(&view.header)),
            "state_root":hex::encode(view.header.state_root)});
        assert!(bind_verified_wallet(&view, &valid).is_ok());
        for (field, value) in [
            ("height", json!(view.header.height + 1)),
            ("block_hash", json!("00".repeat(32))),
            ("state_root", json!("00".repeat(32))),
        ] {
            let mut changed = valid.clone();
            changed[field] = value;
            assert!(bind_verified_wallet(&view, &changed).is_err());
        }
    }

    #[tokio::test]
    async fn wallet_watch_uses_responsive_peers_and_preserves_conflict_fallback() {
        use noid_p2p::{
            header_protocol::HeaderInventoryRecord as Record,
            object_protocol::{DataResponseStatus, TerminalClaimId, TerminalObjectId},
            protocol::GetHeadersResponse,
        };
        let anchor = noid_chain::consensus::genesis::genesis_header();
        let next = BlockHeader {
            height: anchor.height + 1,
            prev_block_hash: block_id(&anchor),
            ..anchor
        };
        let terminal = TerminalObjectId::from_bytes(
            TerminalClaimId {
                height: next.height,
                semantic_header_id: noid_chain::block_header::semantic_header_id(&next),
                proof_class: 0,
            },
            b"hint",
        )
        .unwrap();
        let response = |records| GetHeadersResponse {
            status: DataResponseStatus::Ready,
            records,
            snapshot_boundary: None,
        };
        let first = libp2p::PeerId::random();
        let second = libp2p::PeerId::random();
        let old = response(vec![Record::header_only(anchor)]);
        let fresh = response(vec![
            Record::header_only(anchor),
            Record {
                header: next,
                body: None,
                terminal: Some(terminal),
            },
        ]);
        let pending =
            stream::iter(vec![(first, Ok(old)), (second, Ok(fresh))]).chain(stream::pending());
        let result = tokio::time::timeout(
            Duration::from_secs(1),
            collect_watch_headers(&anchor, pending, Duration::from_millis(10)),
        )
        .await
        .expect("a stalled peer must not hold a completed watch")
        .unwrap()
        .unwrap();
        assert_eq!(result.0, second);
        assert_eq!(result.1.last().unwrap().header, next);

        let mut conflict = anchor;
        conflict.state_root[0] ^= 1;
        let pending = stream::iter(vec![
            (first, Ok(response(vec![Record::header_only(anchor)]))),
            (second, Ok(response(vec![Record::header_only(conflict)]))),
        ]);
        assert!(
            collect_watch_headers(&anchor, pending, Duration::from_millis(10))
                .await
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn wallet_watch_binds_the_known_header_and_requires_a_complete_available_extension() {
        use noid_p2p::{
            header_protocol::HeaderInventoryRecord as Record,
            object_protocol::{TerminalClaimId, TerminalObjectId},
        };
        let anchor = noid_chain::consensus::genesis::genesis_header();
        let next = BlockHeader {
            height: anchor.height + 1,
            prev_block_hash: block_id(&anchor),
            ..anchor
        };
        let last = BlockHeader {
            height: next.height + 1,
            prev_block_hash: block_id(&next),
            ..next
        };
        let proof = TerminalObjectId::from_bytes(
            TerminalClaimId {
                height: next.height,
                semantic_header_id: noid_chain::block_header::semantic_header_id(&next),
                proof_class: 0,
            },
            b"hint",
        )
        .unwrap();
        let linked = Record {
            header: next,
            body: None,
            terminal: Some(proof),
        };
        let (records, more) = continuation_records(
            &anchor,
            vec![
                Record::header_only(anchor),
                linked,
                Record::header_only(last),
            ],
        )
        .unwrap();
        assert_eq!(records, vec![linked]);
        assert!(!more);
        assert!(continuation_records(
            &anchor,
            vec![Record::header_only(anchor), Record::header_only(next)]
        )
        .is_err());
        assert!(continuation_records(
            &anchor,
            vec![
                Record::header_only(anchor),
                Record {
                    header: last,
                    ..linked
                }
            ]
        )
        .is_err());
        assert!(continuation_records(&next, vec![Record::header_only(anchor), linked]).is_err());
        assert!(continuation_records(&anchor, vec![]).is_err());
        let (records, more) =
            continuation_records(&anchor, vec![Record::header_only(anchor)]).unwrap();
        assert!(records.is_empty() && !more);
    }

    #[test]
    fn segment_batches_preserve_order_and_transport_budgets() {
        let descriptors = (0..140u16)
            .map(|i| (i, [i as u8; 32], if i == 70 { 200_000 } else { 1600 }))
            .collect::<Vec<_>>();
        let batches = segment_batches(descriptors.clone());
        assert!(batches.len() < descriptors.len() / 10);
        for batch in &batches {
            assert!(batch.len() <= noid_p2p::protocol::MAX_STATE_SEGMENT_BATCH);
            assert!(
                batch.len() == 1
                    || batch.iter().map(|d| d.2 as usize).sum::<usize>()
                        <= noid_p2p::protocol::MAX_STATE_SEGMENT_BATCH_BYTES
            );
        }
        assert_eq!(
            batches.into_iter().flatten().collect::<Vec<_>>(),
            descriptors
        );
    }

    #[test]
    fn segment_join_matches_global_tree_and_rejects_duplicate_segments() {
        let image = fixture();
        let parts: Vec<_> = (0u16..16)
            .filter_map(|segment| {
                let local: BTreeMap<_, _> = image
                    .slots
                    .iter()
                    .filter(|(i, _)| **i >> 4 == u32::from(segment))
                    .map(|(&i, &v)| (i & 15, v))
                    .collect();
                (!local.is_empty()).then(|| (segment, Tree::build(4, &local).unwrap()))
            })
            .collect();
        let joined = Tree::join(8, 4, parts).unwrap();
        assert_eq!(joined.root(), image.tree.root());
        for level in 0..=8 {
            for i in 0..(1u32 << (8 - level)) {
                assert_eq!(joined.node(level, i), image.tree.node(level, i));
            }
        }
        assert!(Tree::join(
            8,
            4,
            vec![
                (0, Tree::build(4, &BTreeMap::new()).unwrap()),
                (0, Tree::build(4, &BTreeMap::new()).unwrap())
            ]
        )
        .is_err());
    }

    #[test]
    fn wallet_projection_matches_complete_state_after_payment_and_reward() {
        use noid_tx::{
            output_bitmap_bit, Transaction, TxBody, TxInput, TxOutput, PAGED_SPEND_END_BIT,
            PAGED_SPEND_START_BIT,
        };
        let image = fixture();
        let owner = Address([17; 32]);
        let proofs = image.proofs(owner).unwrap();
        let mut view = WalletView::from_proofs(image.header, owner, &proofs).unwrap();
        let reward = Transaction::new(TxBody {
            epoch_anchor: [7; 32],
            fee: 0,
            input_owner: Address([0; 32]),
            inputs: [TxInput::dummy(); 8],
            outputs: [
                TxOutput {
                    slot_index: 201,
                    amount: 1,
                    owner: Address([22; 32]),
                },
                TxOutput::dummy(),
            ],
            validity_bitmap: output_bitmap_bit(0),
            is_coinbase: true,
        });
        let mut inputs = [TxInput::dummy(); 8];
        inputs[0] = TxInput {
            slot_index: 3,
            amount: 100_000,
            creation_id: 1,
        };
        let payment = Transaction::new(TxBody {
            epoch_anchor: [7; 32],
            fee: 9_000,
            input_owner: owner,
            inputs,
            outputs: [
                TxOutput {
                    slot_index: 7,
                    amount: 1_000,
                    owner: Address([22; 32]),
                },
                TxOutput {
                    slot_index: 8,
                    amount: 90_000,
                    owner,
                },
            ],
            validity_bitmap: 1
                | output_bitmap_bit(0)
                | output_bitmap_bit(1)
                | PAGED_SPEND_START_BIT
                | PAGED_SPEND_END_BIT,
            is_coinbase: false,
        });
        let transactions = vec![reward, payment];
        let mut expected = image.slots.clone();
        expected.remove(&3);
        expected.insert(
            201,
            SlotValue::with_owner_fields(
                1,
                noid_chain::consensus::params::coinbase_creation_id(image.header.height + 1),
                Address([22; 32]).as_fields(),
            ),
        );
        expected.insert(
            7,
            SlotValue::with_owner_fields(1_000, 9, Address([22; 32]).as_fields()),
        );
        expected.insert(
            8,
            SlotValue::with_owner_fields(90_000, 10, owner.as_fields()),
        );
        let mut header = image.header;
        header.height += 1;
        header.prev_block_hash = block_id(&image.header);
        header.alloc_counter = 10;
        header.active_slot_count = expected.len() as u64;
        header.state_root = Tree::build(8, &expected).unwrap().root();
        let stream = validate_scheduled_block_page_stream(&transactions, header.height).unwrap();
        header.tx_root = noid_chain::tx_tree::root_from_hashes(
            &stream
                .logical_txids(&transactions)
                .into_iter()
                .map(|v| v.0)
                .collect::<Vec<_>>(),
        );
        let payload = BlockBodyPayload::new(
            noid_chain::block::Block {
                header,
                transactions,
            },
            vec![],
        )
        .unwrap();
        let checked = CheckedBody::decode(&payload.encode(), header).unwrap();
        assert!(CheckedBody::decode(
            &payload.encode(),
            BlockHeader {
                tx_root: [1; 32],
                ..header
            }
        )
        .is_err());
        let mut changed = payload.block().clone();
        changed.transactions[1].body.outputs[1].owner = Address([33; 32]);
        assert!(CheckedBody::decode(
            &BlockBodyPayload::new(changed, vec![]).unwrap().encode(),
            header
        )
        .is_err());
        assert!(view
            .clone()
            .apply(
                &BlockBodyPayload::new(
                    noid_chain::block::Block {
                        header: BlockHeader {
                            prev_block_hash: [2; 32],
                            ..header
                        },
                        transactions: payload.block().transactions.clone()
                    },
                    vec![]
                )
                .unwrap()
            )
            .is_err());
        let mut canonical = noid_chain::state::ChainState::with_log_slots(8);
        for (&i, &v) in &image.slots {
            canonical.state.set_slot(i, v).unwrap();
        }
        canonical.active_slot_count = image.header.active_slot_count;
        canonical.alloc_counter = image.header.alloc_counter;
        canonical.circulating_supply_micronoid =
            image.slots.values().map(|v| u128::from(v.amount())).sum();
        for transaction in &payload.block().transactions {
            noid_chain::state::apply_tx_at(&mut canonical, &transaction.body, header.height)
                .unwrap();
        }
        assert_eq!(canonical.state_root(), header.state_root);
        let canonical_slots: BTreeMap<_, _> = (0..256)
            .map(|i| (i, canonical.state.slot(i)))
            .filter(|(_, v)| !v.is_empty())
            .collect();
        view.apply_checked(&checked).unwrap();
        assert_eq!(view.coin_set(), coins(&canonical_slots, owner));
        assert_eq!(view.header, header);
        assert!(view
            .slots
            .iter()
            .all(|(i, v)| canonical.state.slot(*i) == *v));
        assert!(view
            .slots
            .values()
            .all(|v| v.is_empty() || slot_owner(*v) == owner));
        assert!(!view.slots.contains_key(&93));
        assert_eq!(view.coin_set().get(&8), Some(&(90_000, 10)));
        let args = json!({"seed_hex":hex::encode([9u8;32])});
        let sealed = view.seal(&args).unwrap();
        assert_eq!(
            WalletView::open(&args, owner, &sealed).unwrap().slots,
            view.slots
        );
        assert!(
            WalletView::open(&json!({"seed_hex":hex::encode([8u8;32])}), owner, &sealed).is_err()
        );
        assert!(WalletView::open(&args, Address([44; 32]), &sealed).is_err());
        let mut corrupt = sealed.clone();
        corrupt["record"]["slots"][0]["value"] = json!(123);
        assert!(WalletView::open(&args, owner, &corrupt).is_err());
        let mut omitted = sealed;
        omitted["record"]["slots"].as_array_mut().unwrap().pop();
        assert!(WalletView::open(&args, owner, &omitted).is_err());
    }

    #[test]
    fn parallel_state_tree_matches_canonical_tree_and_expansion() {
        let mut image = fixture();
        let leaves: Vec<_> = image
            .slots
            .iter()
            .map(|(&i, &v)| (i, slot_leaf_hash(v)))
            .collect();
        let mut reference = SparseMerkleCache::from_leaves(8, &leaves).unwrap();
        assert_eq!(image.tree.root(), reference.root());
        let value = SlotValue::with_owner_fields(123, 4, Address([21; 32]).as_fields());
        image.tree.update(5, value);
        reference.set_leaf(5, slot_leaf_hash(value)).unwrap();
        assert_eq!(image.tree.root(), reference.root());
        image.tree.update(3, SlotValue::EMPTY);
        reference
            .set_leaf(3, slot_leaf_hash(SlotValue::EMPTY))
            .unwrap();
        assert_eq!(image.tree.root(), reference.root());
        let old = image.tree.root();
        image.tree.expand();
        assert_eq!(
            image.tree.root(),
            state_node_hash(old, zero_slot_roots(8)[8])
        );
        image.tree.update(400, value);
        let expanded = SparseMerkleCache::from_leaves(
            9,
            &[
                (5, slot_leaf_hash(value)),
                (93, leaves[1].1),
                (200, leaves[2].1),
                (400, slot_leaf_hash(value)),
            ],
        )
        .unwrap();
        assert_eq!(image.tree.root(), expanded.root());
    }

    #[test]
    fn locally_discovered_coins_and_empty_slots_have_independent_membership_proofs() {
        let image = fixture();
        let owner = Address([17; 32]);
        let proofs = image.proofs(owner).unwrap();
        let mut verified = BTreeMap::new();
        for proof in &proofs {
            verified.extend(crate::mobile_wallet::verify_proof(&image.header, proof).unwrap());
        }
        assert_eq!(verified.get(&3).unwrap().amount(), 100_000);
        assert!(
            !verified.contains_key(&93),
            "Native assets are excluded from ordinary NOID discovery"
        );
        assert!(verified.values().filter(|slot| slot.is_empty()).count() >= 2);
        let mut altered = proofs
            .iter()
            .find(|p| p.slots.iter().any(|s| s.slot_index == 3))
            .unwrap()
            .clone();
        altered
            .slots
            .iter_mut()
            .find(|s| s.slot_index == 3)
            .unwrap()
            .value += 1;
        assert!(crate::mobile_wallet::verify_proof(&image.header, &altered).is_err());
    }

    #[test]
    fn complete_snapshot_rejects_omitted_and_corrupted_slots() {
        let image = fixture();
        let mut corrupt = image.slots.clone();
        corrupt.insert(
            3,
            SlotValue::with_owner_fields(123, 1, Address([17; 32]).as_fields()),
        );
        assert!(StateImage::new(image.header, corrupt).is_err());
        let mut omitted = image.slots.clone();
        omitted.remove(&3);
        assert!(StateImage::new(image.header, omitted.clone()).is_err());
        let mut forged = image.header;
        forged.active_slot_count -= 1;
        assert!(StateImage::new(forged, omitted).is_err());
    }

    #[test]
    fn paranoid_scope_forbids_rpc_and_restores_its_previous_policy() {
        assert!(!rpc_forbidden());
        with_policy(true, || {
            assert!(crate::rpc::Rpc::new("http://127.0.0.1:1")
                .err()
                .unwrap()
                .to_string()
                .contains("RPC is disabled"));
            with_policy(false, || assert!(rpc_forbidden()));
            assert!(rpc_forbidden());
        });
        assert!(!rpc_forbidden());
    }
}
