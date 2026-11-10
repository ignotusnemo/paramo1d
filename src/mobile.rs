use crate::{
    artifacts::{self},
    Verifier,
};
use anyhow::{bail, ensure, Context, Result};
use futures::{stream::FuturesUnordered, StreamExt};
use libp2p::{
    identify, ping,
    request_response::{self as rr, Message, ProtocolSupport},
    swarm::{NetworkBehaviour, SwarmEvent},
    Multiaddr, PeerId, StreamProtocol, SwarmBuilder,
};
use noid_chain::{
    block_header::{block_id, semantic_header_id},
    consensus::{network::NetworkConfig, params},
    history_step::HistoryStepTerminalMetadata,
};
use noid_p2p::{
    fork_origin::{ForkOriginCodec, ForkOriginResponse},
    header_sync_codec::HeaderSyncCodec,
    history_step_codec::HistoryStepTerminalCodec,
    manifest_page_codec::ManifestPageCodec,
    network_profile::{
        NetworkProfile, NetworkProfileCodec, NetworkProfileRequest, NetworkProfileResponse,
    },
    object_codec::ObjectCodec,
    object_protocol::{DataResponseStatus, GetObjectsResponse},
    protocol::{
        GetHeadersRequest, GetHeadersResponse, GetHistoryStepTerminalRequest,
        GetHistoryStepTerminalResponse, GetSnapshotManifestPageResponse, GetStateManifestHeader,
    },
    state_manifest_codec::StateManifestCodec,
};
use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap, HashSet},
    fs::{self, File},
    io::{Seek, SeekFrom, Write},
    path::{Path, PathBuf},
    time::{Duration, Instant},
};
use tokio::sync::{mpsc, oneshot, watch};

const HEADER_BATCH: u16 = 4096;
const HEADER_WINDOW: usize = 16;
const MAX_HEIGHT: u64 = 40_000_000;

#[derive(NetworkBehaviour)]
struct Behaviour {
    profile: rr::Behaviour<NetworkProfileCodec>,
    headers: rr::Behaviour<HeaderSyncCodec>,
    terminal: rr::Behaviour<HistoryStepTerminalCodec>,
    origin: rr::Behaviour<ForkOriginCodec>,
    objects: rr::Behaviour<ObjectCodec>,
    manifest: rr::Behaviour<StateManifestCodec>,
    manifest_page: rr::Behaviour<ManifestPageCodec>,
    identify: identify::Behaviour,
    ping: ping::Behaviour,
}

type Reply<T> = oneshot::Sender<Result<T>>;
enum Command {
    Dial(Multiaddr),
    Headers(PeerId, GetHeadersRequest, Reply<GetHeadersResponse>),
    Terminal(
        PeerId,
        GetHistoryStepTerminalRequest,
        Reply<GetHistoryStepTerminalResponse>,
    ),
    Origin(PeerId, [u8; 32], Reply<ForkOriginResponse>),
}

#[derive(Clone)]
struct Network {
    commands: mpsc::Sender<Command>,
    peers: watch::Receiver<Vec<PeerId>>,
    lifecycle: Option<tokio_util::sync::CancellationToken>,
}

struct Connection {
    bank: [u8; 32],
    route: Option<crate::network_route::Route>,
    network: Network,
    executor: tokio::runtime::Runtime,
}
thread_local! { static CONNECTION: RefCell<Option<Connection>> = const { RefCell::new(None) }; }
fn with_connection<T>(
    bank: [u8; 32],
    profile: NetworkProfile,
    work: impl FnOnce(&tokio::runtime::Runtime, Network) -> Result<T>,
) -> Result<T> {
    CONNECTION.with(|slot| {
        let mut slot = slot
            .try_borrow_mut()
            .map_err(|_| anyhow::anyhow!("Node connection is busy"))?;
        let route = crate::network_route::current();
        let usable = slot.as_ref().is_some_and(|c| {
            c.bank == bank
                && c.route == route
                && !c.network.commands.is_closed()
                && !c
                    .network
                    .lifecycle
                    .as_ref()
                    .is_some_and(|t| t.is_cancelled())
        });
        if !usable {
            *slot = None;
            let executor = tokio::runtime::Builder::new_multi_thread()
                .enable_all()
                .build()?;
            let network = executor.block_on(Network::start(profile))?;
            *slot = Some(Connection {
                bank,
                route,
                network,
                executor,
            });
        }
        let connection = slot.as_ref().expect("node connection initialized");
        work(&connection.executor, connection.network.clone())
    })
}

fn protocols(suffix: &str, support: ProtocolSupport) -> Vec<(StreamProtocol, ProtocolSupport)> {
    vec![(
        StreamProtocol::try_from_owned(format!(
            "{}{suffix}",
            NetworkConfig::mainnet().p2p_protocol_id
        ))
        .expect("compiled network protocol"),
        support,
    )]
}

fn peak_memory_kib() -> Option<u64> {
    fs::read_to_string("/proc/self/status")
        .ok()?
        .lines()
        .find_map(|line| {
            line.strip_prefix("VmHWM:")?
                .split_whitespace()
                .next()?
                .parse()
                .ok()
        })
}

impl Network {
    async fn start(profile: NetworkProfile) -> Result<Self> {
        let lifecycle = crate::mobile_control::token();
        let stop = lifecycle.clone();
        let identity = libp2p::identity::Keypair::generate_ed25519();
        let transport = crate::network_route::transport(&identity)?;
        let mut swarm = SwarmBuilder::with_existing_identity(identity)
            .with_tokio()
            .with_other_transport(|_| transport)?
            .with_behaviour(|key| Behaviour {
                profile: rr::Behaviour::new(
                    protocols("/sync/profile/6", ProtocolSupport::Full),
                    rr::Config::default().with_request_timeout(Duration::from_secs(15)),
                ),
                headers: rr::Behaviour::new(
                    [
                        protocols("/sync/headers/5", ProtocolSupport::Full),
                        protocols("/sync/headers/4", ProtocolSupport::Full),
                    ]
                    .concat(),
                    rr::Config::default()
                        .with_request_timeout(Duration::from_secs(30))
                        .with_max_concurrent_streams(16),
                ),
                terminal: rr::Behaviour::new(
                    protocols("/sync/history-step/1", ProtocolSupport::Outbound),
                    rr::Config::default().with_request_timeout(Duration::from_secs(60)),
                ),
                origin: rr::Behaviour::new(
                    protocols("/sync/fork-origin/1", ProtocolSupport::Outbound),
                    rr::Config::default().with_request_timeout(Duration::from_secs(60)),
                ),
                objects: rr::Behaviour::new(
                    protocols("/sync/objects/2", ProtocolSupport::Full),
                    rr::Config::default().with_max_concurrent_streams(2),
                ),
                manifest: rr::Behaviour::new(
                    protocols("/sync/manifest/7", ProtocolSupport::Full),
                    rr::Config::default().with_max_concurrent_streams(2),
                ),
                manifest_page: rr::Behaviour::new(
                    protocols("/sync/manifest-page/1", ProtocolSupport::Full),
                    rr::Config::default().with_max_concurrent_streams(2),
                ),
                identify: identify::Behaviour::new(
                    identify::Config::new("/noid/1.0.0".into(), key.public())
                        .with_agent_version("paramo1d/0.1.0".into()),
                ),
                ping: ping::Behaviour::new(ping::Config::new()),
            })?
            .with_swarm_config(|c| c.with_idle_connection_timeout(Duration::from_secs(180)))
            .build();
        let (commands, mut receive) = mpsc::channel(32);
        let (peer_sender, peers) = watch::channel(Vec::new());
        let discovery_commands = commands.clone();
        let protected = crate::network_route::current().is_some();
        tokio::spawn(async move {
            if protected {
                for host in NetworkConfig::mainnet().dns_seeds {
                    if let Ok(address) = format!("/dns4/{host}/tcp/9600").parse() {
                        let _ = discovery_commands.send(Command::Dial(address)).await;
                    }
                }
                return;
            }
            let mut lookups = FuturesUnordered::new();
            for host in NetworkConfig::mainnet().dns_seeds {
                lookups.push(async move {
                    let resolved = tokio::time::timeout(
                        Duration::from_secs(5),
                        tokio::net::lookup_host((*host, 9600)),
                    )
                    .await;
                    (host, resolved)
                });
            }
            while let Some((host, resolved)) = lookups.next().await {
                match resolved {
                    Ok(Ok(found)) => {
                        for address in found.take(2) {
                            let addr: Multiaddr = match address.ip() {
                                std::net::IpAddr::V4(ip) => {
                                    format!("/ip4/{ip}/tcp/{}", address.port())
                                        .parse()
                                        .expect("typed socket multiaddress")
                                }
                                std::net::IpAddr::V6(ip) => {
                                    format!("/ip6/{ip}/tcp/{}", address.port())
                                        .parse()
                                        .expect("typed socket multiaddress")
                                }
                            };
                            let _ = discovery_commands.send(Command::Dial(addr)).await;
                        }
                    }
                    _ => eprintln!("  Discovery: {host} unavailable"),
                }
            }
        });
        tokio::spawn(async move {
            let mut identified = HashSet::new();
            let mut compatible = HashSet::new();
            let mut handshakes = HashSet::new();
            let mut pending_headers: HashMap<
                rr::OutboundRequestId,
                (PeerId, GetHeadersRequest, Reply<GetHeadersResponse>),
            > = HashMap::new();
            let mut pending_terminal: HashMap<
                rr::OutboundRequestId,
                (
                    PeerId,
                    GetHistoryStepTerminalRequest,
                    Reply<GetHistoryStepTerminalResponse>,
                ),
            > = HashMap::new();
            let mut pending_origin: HashMap<
                rr::OutboundRequestId,
                (PeerId, [u8; 32], Reply<ForkOriginResponse>),
            > = HashMap::new();
            loop {
                tokio::select! {
                    _=async {match &stop {Some(t)=>t.cancelled().await,None=>std::future::pending::<()>().await}}=>break,
                    command = receive.recv() => match command {
                        Some(Command::Dial(address)) => { let _ = swarm.dial(address); }
                        Some(Command::Headers(peer, request, reply)) => {
                            let id = swarm.behaviour_mut().headers.send_request(&peer, request.clone());
                            pending_headers.insert(id, (peer, request, reply));
                        }
                        Some(Command::Terminal(peer, request, reply)) => {
                            let id = swarm.behaviour_mut().terminal.send_request(&peer, request.clone());
                            pending_terminal.insert(id, (peer, request, reply));
                        }
                        Some(Command::Origin(peer, request, reply)) => {
                            let id = swarm.behaviour_mut().origin.send_request(&peer, request);
                            pending_origin.insert(id, (peer, request, reply));
                        }
                        None => break,
                    },
                    event = swarm.select_next_some() => match event {
                        SwarmEvent::ConnectionEstablished { peer_id, .. } => {
                            let short = peer_id.to_string();
                            eprintln!("  P2P        Connected to ...{}", &short[short.len().saturating_sub(8)..]);
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::Identify(identify::Event::Received { peer_id, .. })) => {
                            identified.insert(peer_id);
                            if handshakes.insert(peer_id) {
                                swarm.behaviour_mut().profile.send_request(&peer_id, NetworkProfileRequest { expected_profile_id: profile.profile_id });
                            }
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::Profile(rr::Event::Message { peer, message, .. })) => match message {
                            Message::Request { request, channel, .. } => {
                                if request.expected_profile_id == profile.profile_id {
                                    let _ = swarm.behaviour_mut().profile.send_response(channel, NetworkProfileResponse { profile });
                                    compatible.insert(peer);
                                } else { eprintln!("  PROFILE    Peer uses different verification parameters"); let _ = swarm.disconnect_peer_id(peer); }
                            }
                            Message::Response { response, .. } => {
                                if response.profile == profile { compatible.insert(peer); eprintln!("  PROFILE    Compatible peers: {}", compatible.len()); }
                                else { eprintln!("  PROFILE    Peer uses different verification parameters"); let _ = swarm.disconnect_peer_id(peer); }
                            }
                        },
                        SwarmEvent::Behaviour(BehaviourEvent::Profile(rr::Event::OutboundFailure { error, .. })) => {
                            eprintln!("  PROFILE    Handshake: {error}");
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::Headers(rr::Event::Message { message: Message::Request { channel, .. }, .. })) => {
                            let _ = swarm.behaviour_mut().headers.send_response(channel, GetHeadersResponse { status: DataResponseStatus::Ready, records: Vec::new(), snapshot_boundary: None });
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::Objects(rr::Event::Message { message: Message::Request { request, channel, .. }, .. })) => {
                            let _ = swarm.behaviour_mut().objects.send_response(channel, GetObjectsResponse::unavailable(request.objects));
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::Manifest(rr::Event::Message { message: Message::Request { channel, .. }, .. })) => {
                            let _ = swarm.behaviour_mut().manifest.send_response(channel, GetStateManifestHeader::default());
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::ManifestPage(rr::Event::Message { message: Message::Request { request, channel, .. }, .. })) => {
                            let _ = swarm.behaviour_mut().manifest_page.send_response(channel, GetSnapshotManifestPageResponse::unavailable(request.object));
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::Headers(rr::Event::Message { peer, message: Message::Response { request_id, response }, .. })) => {
                            if let Some((expected, request, reply)) = pending_headers.remove(&request_id) {
                                let result = (|| -> Result<_> {
                                    ensure!(peer == expected, "header response peer");
                                    ensure!(response.records.len() <= request.count as usize, "header response count");
                                    for (i, record) in response.records.iter().enumerate() {
                                        ensure!(record.header.height == request.start_height + i as u64, "header response range");
                                    }
                                    Ok(response)
                                })();
                                let _ = reply.send(result);
                            }
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::Terminal(rr::Event::Message { peer, message: Message::Response { request_id, response }, .. })) => {
                            if let Some((expected, request, reply)) = pending_terminal.remove(&request_id) {
                                let result = (|| -> Result<_> {
                                    ensure!(peer == expected && response.height == request.height && response.block_hash == request.block_hash, "terminal response identity");
                                    Ok(response)
                                })();
                                let _ = reply.send(result);
                            }
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::Origin(rr::Event::Message { peer, message: Message::Response { request_id, response }, .. })) => {
                            if let Some((expected, request, reply)) = pending_origin.remove(&request_id) {
                                let result = (|| -> Result<_> {
                                    ensure!(peer == expected && response.request == request, "origin response identity");
                                    Ok(response)
                                })();
                                let _ = reply.send(result);
                            }
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::Headers(rr::Event::OutboundFailure { request_id, error, .. })) => {
                            if let Some((_, _, reply)) = pending_headers.remove(&request_id) { let _ = reply.send(Err(anyhow::anyhow!("header transfer: {error}"))); }
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::Terminal(rr::Event::OutboundFailure { request_id, error, .. })) => {
                            if let Some((_, _, reply)) = pending_terminal.remove(&request_id) { let _ = reply.send(Err(anyhow::anyhow!("terminal transfer: {error}"))); }
                        }
                        SwarmEvent::Behaviour(BehaviourEvent::Origin(rr::Event::OutboundFailure { request_id, error, .. })) => {
                            if let Some((_, _, reply)) = pending_origin.remove(&request_id) { let _ = reply.send(Err(anyhow::anyhow!("origin transfer: {error}"))); }
                        }
                        SwarmEvent::ConnectionClosed { peer_id, num_established: 0, .. } => {
                            identified.remove(&peer_id); compatible.remove(&peer_id); handshakes.remove(&peer_id);
                        }
                        _ => {}
                    }
                }
                let mut ready: Vec<_> = compatible.intersection(&identified).copied().collect();
                ready.sort();
                let changed = { *peer_sender.borrow() != ready };
                if changed {
                    let _ = peer_sender.send(ready);
                }
            }
        });
        Ok(Self {
            commands,
            peers,
            lifecycle,
        })
    }

    async fn headers(&self, peer: PeerId, first: u64, count: u16) -> Result<GetHeadersResponse> {
        self.headers_with_inventory(peer, first, count, false).await
    }

    async fn headers_with_inventory(
        &self,
        peer: PeerId,
        first: u64,
        count: u16,
        inventory: bool,
    ) -> Result<GetHeadersResponse> {
        for _ in 0..8 {
            let (reply, result) = oneshot::channel();
            self.commands
                .send(Command::Headers(
                    peer,
                    GetHeadersRequest {
                        start_height: first,
                        count,
                        include_inventory: inventory,
                    },
                    reply,
                ))
                .await?;
            let response = result.await??;
            if let DataResponseStatus::Busy { retry_after_ms } = response.status {
                tokio::time::sleep(Duration::from_millis(retry_after_ms as u64)).await;
                continue;
            }
            return Ok(response);
        }
        bail!("peer header serving remained busy")
    }

    async fn terminal(&self, peer: PeerId, height: u64, hash: [u8; 32]) -> Result<Vec<u8>> {
        for _ in 0..3 {
            let (reply, result) = oneshot::channel();
            self.commands
                .send(Command::Terminal(
                    peer,
                    GetHistoryStepTerminalRequest {
                        height,
                        block_hash: hash,
                    },
                    reply,
                ))
                .await?;
            let response = result.await??;
            if let DataResponseStatus::Busy { retry_after_ms } = response.status {
                tokio::time::sleep(Duration::from_millis(retry_after_ms as u64)).await;
                continue;
            }
            return response.terminal_bytes.context("peer terminal unavailable");
        }
        bail!("peer terminal serving remained busy")
    }

    async fn first_terminal(
        &self,
        primary: PeerId,
        height: u64,
        hash: [u8; 32],
    ) -> Result<Vec<u8>> {
        let mut peers = self.peers.borrow().clone();
        peers.retain(|peer| *peer != primary);
        peers.insert(0, primary);
        let mut transfers = FuturesUnordered::new();
        eprintln!("  SOURCES    Requesting proof from {} peers", peers.len());
        for peer in peers.into_iter().take(8) {
            let network = self.clone();
            transfers.push(async move { (peer, network.terminal(peer, height, hash).await) });
        }
        let received = async {
            while let Some((_, result)) = transfers.next().await {
                match result {
                    Ok(bytes) => return Ok(bytes),
                    Err(error) => eprintln!("  SOURCE     Proof response: {error:#}"),
                }
            }
            bail!("mainnet peers could not supply the selected proof")
        };
        tokio::time::timeout(Duration::from_secs(15), received)
            .await
            .context("proof-source response deadline")?
    }

    async fn origin(&self, peer: PeerId, key: [u8; 32]) -> Result<Vec<u8>> {
        let (reply, result) = oneshot::channel();
        self.commands
            .send(Command::Origin(peer, key, reply))
            .await?;
        result.await??.bytes.context("peer origin unavailable")
    }
}

async fn discover(
    network: &mut Network,
) -> Result<Vec<(PeerId, noid_p2p::object_protocol::ChainPoint)>> {
    let start = Instant::now();
    let starting = network.peers.borrow().is_empty();
    loop {
        let waiting = { network.peers.borrow().is_empty() };
        if !waiting {
            break;
        }
        tokio::time::timeout(Duration::from_secs(20), network.peers.changed()).await??;
    }
    // Let independent startup dials finish before selecting a source.
    if starting {
        tokio::time::sleep(Duration::from_millis(500)).await;
    }
    let peers = network.peers.borrow().clone();
    let mut queries = FuturesUnordered::new();
    for peer in peers {
        let network = network.clone();
        queries.push(async move { (peer, network.headers(peer, 0, 1).await) });
    }
    let mut candidates = Vec::new();
    while let Some((peer, response)) = queries.next().await {
        if let Ok(response) = response {
            if response
                .records
                .first()
                .is_some_and(|r| r.header == noid_chain::consensus::genesis::genesis_header())
            {
                if let Some(mut boundary) = response.snapshot_boundary {
                    if boundary.height < MAX_HEIGHT {
                        if let Ok(tail) = network
                            .headers_with_inventory(peer, boundary.height + 1, 64, true)
                            .await
                        {
                            if let Some(record) = tail
                                .records
                                .iter()
                                .rev()
                                .find(|record| record.terminal.is_some())
                            {
                                boundary = noid_p2p::object_protocol::ChainPoint::new(
                                    record.header.height,
                                    block_id(&record.header),
                                );
                            }
                        }
                        candidates.push((peer, boundary));
                    }
                }
            }
        }
    }
    ensure!(
        !candidates.is_empty(),
        "mainnet peers have no usable proof boundary"
    );
    candidates.sort_by_key(|(_, point)| std::cmp::Reverse(point.height));
    eprintln!(
        "  PEERS      {} compatible sources in {:.2}s",
        candidates.len(),
        start.elapsed().as_secs_f64()
    );
    Ok(candidates)
}

async fn fetch_bundle(
    network: &Network,
    peer: PeerId,
    boundary: noid_p2p::object_protocol::ChainPoint,
    output: &Path,
    verifier: &Verifier,
    previous: Option<&Path>,
) -> Result<()> {
    ensure!(!output.exists(), "sync bundle already exists");
    let temporary = tempfile::Builder::new()
        .prefix(".receiving-")
        .tempdir_in(output.parent().context("sync directory")?)?;
    let began = Instant::now();
    eprintln!("  DOWNLOAD   Mainnet block {}", boundary.height);
    let terminal = network
        .first_terminal(peer, boundary.height, boundary.hash)
        .await?;
    let metadata = HistoryStepTerminalMetadata::decode_prefix(&terminal)?;
    ensure!(
        metadata.terminal_height() == boundary.height,
        "terminal boundary height"
    );
    fs::write(temporary.path().join("terminal.bin"), &terminal)?;
    let mut files = BTreeMap::new();
    let current = params::v2_1_active(boundary.height);
    let key = verifier.claimed_origin_request(&terminal)?;
    let origin_network = network.clone();
    let cache_name = if current {
        "current-origin.bin"
    } else {
        "origin.bin"
    };
    let cached_origin = previous.and_then(|directory| {
        let same_key = artifacts::read_bounded(&directory.join("origin-key.bin"), 32)
            .ok()
            .is_some_and(|saved| saved == key);
        same_key
            .then(|| {
                artifacts::read_bounded(&directory.join(cache_name), artifacts::MAX_ORIGIN_BYTES)
                    .ok()
            })
            .flatten()
    });
    let origin_reused = cached_origin.is_some();
    let origin_task = tokio::spawn(async move {
        if let Some(bytes) = cached_origin {
            Ok(bytes)
        } else {
            origin_network.origin(peer, key).await
        }
    });
    let mut headers = File::create(temporary.path().join("headers.bin"))?;
    let mut first = 0;
    if let Some(previous) = previous {
        let mut accepted = File::open(previous.join("headers.bin"))?;
        let length = accepted.metadata()?.len();
        ensure!(
            length % 212 == 0 && length <= (boundary.height + 1) * 212,
            "accepted header prefix length"
        );
        std::io::copy(&mut accepted, &mut headers)?;
        first = length / 212;
    }
    let mut pending = FuturesUnordered::new();
    let header_peers = network.peers.borrow().clone();
    let mut batch_index = 0;
    let mut total = 0u64;
    while first <= boundary.height || !pending.is_empty() {
        while first <= boundary.height && pending.len() < HEADER_WINDOW {
            let count = (boundary.height + 1 - first).min(HEADER_BATCH as u64) as u16;
            let network = network.clone();
            let source = header_peers
                .get(batch_index % header_peers.len().max(1))
                .copied()
                .unwrap_or(peer);
            batch_index += 1;
            pending.push(async move {
                let response = network.headers(source, first, count).await;
                let response = if source != peer
                    && response
                        .as_ref()
                        .map_or(true, |r| r.records.len() != count as usize)
                {
                    network.headers(peer, first, count).await
                } else {
                    response
                };
                (first, count, response)
            });
            first += count as u64;
        }
        let (at, count, result) = pending.next().await.context("header transfer wave")?;
        let response = result?;
        if let DataResponseStatus::Busy { retry_after_ms } = response.status {
            tokio::time::sleep(Duration::from_millis(retry_after_ms as u64)).await;
            let response = network.headers(peer, at, count).await?;
            ensure!(
                response.records.len() == count as usize,
                "incomplete retried header range"
            );
            headers.seek(SeekFrom::Start(at * 212))?;
            for record in response.records {
                headers.write_all(&record.header.to_bytes())?;
            }
        } else {
            ensure!(
                response.records.len() == count as usize,
                "incomplete header range"
            );
            headers.seek(SeekFrom::Start(at * 212))?;
            for record in response.records {
                headers.write_all(&record.header.to_bytes())?;
            }
        }
        total += count as u64;
        eprint!("\r  HEADERS    {total}/{} received", boundary.height + 1);
    }
    headers.sync_all()?;
    let origin = origin_task.await??;
    fs::write(temporary.path().join("origin-key.bin"), key)?;
    if current {
        let certificate = noid_recursive::acceptance::history_step::v2::capacity_banked::AuthorizationOriginCertificate::from_bytes(&origin)
            .map_err(|e| anyhow::anyhow!("current origin codec: {e}"))?;
        let previous = if certificate.previous_origin_bytes().is_empty() {
            network
                .origin(peer, certificate.previous_origin_request())
                .await?
        } else {
            certificate.previous_origin_bytes().to_vec()
        };
        fs::write(temporary.path().join("origin.bin"), &previous)?;
        files.insert("origin.bin", previous.len());
        fs::write(temporary.path().join("current-origin.bin"), &origin)?;
    } else {
        fs::write(temporary.path().join("origin.bin"), &origin)?;
    }
    files.insert(
        if current {
            "current-origin.bin"
        } else {
            "origin.bin"
        },
        origin.len(),
    );
    let mut header_file = File::open(temporary.path().join("headers.bin"))?;
    let header = crate::headers::read_header(&mut header_file, boundary.height)?;
    ensure!(
        block_id(&header) == boundary.hash
            && semantic_header_id(&header) == metadata.terminal_hash(),
        "downloaded proof boundary identity"
    );
    let manifest = serde_json::json!({"schema":1,"network":artifacts::profile().network,"height":boundary.height,"block_hash":hex::encode(boundary.hash),"headers":boundary.height+1,"header_bytes":(boundary.height+1)*212,"proof_bytes":terminal.len(),"origin_bytes":files.values().sum::<usize>(),"transport":"direct-p2p"});
    fs::write(
        temporary.path().join("bundle.json"),
        serde_json::to_vec_pretty(&manifest)?,
    )?;
    fs::rename(temporary.path(), output)?;
    eprintln!(
        "\n  RECEIVED   {:.2} MiB in {:.2}s",
        (total * 212
            + terminal.len() as u64
            + if origin_reused {
                0
            } else {
                files.values().sum::<usize>() as u64
            }) as f64
            / 1048576.0,
        began.elapsed().as_secs_f64()
    );
    Ok(())
}

pub(crate) fn observed_height(artifact_directory: &Path) -> Result<u64> {
    let legacy=artifacts::pinned(artifact_directory,"legacy")?;
    let bank=legacy[legacy.len()-32..].try_into()?;
    with_connection(bank,NetworkProfile::for_proof_bank(bank),|executor,mut network| {
        executor.block_on(crate::mobile_control::cancellable(async move {
            while network.peers.borrow().is_empty() {
                tokio::time::timeout(Duration::from_secs(10),network.peers.changed()).await??;
            }
            let peers=network.peers.borrow().clone();
            let mut replies=FuturesUnordered::new();
            for peer in peers.into_iter().take(2) {
                let network=network.clone();
                replies.push(async move {(peer,network.headers(peer,0,1).await)});
            }
            while let Some((peer,reply))=tokio::time::timeout(Duration::from_secs(3),replies.next()).await? {
                if let Ok(reply)=reply {
                    if reply.records.first().is_some_and(|r|r.header==noid_chain::consensus::genesis::genesis_header()) {
                        if let Some(point)=reply.snapshot_boundary.filter(|p|p.height<MAX_HEIGHT) {
                            let tail=tokio::time::timeout(Duration::from_secs(3),network.headers_with_inventory(peer,point.height+1,64,false)).await;
                            let observed=tail.ok().and_then(Result::ok).and_then(|r|r.records.into_iter().filter(|r|r.header.height>point.height && r.header.height<=point.height+64 && r.header.height<MAX_HEIGHT).map(|r|r.header.height).max());
                            return Ok(observed.unwrap_or(point.height));
                        }
                    }
                }
            }
            anyhow::bail!("Mainnet peer is unavailable")
        }))
    })
}

pub fn run(
    artifact_directory: PathBuf,
    data_directory: PathBuf,
    once: bool,
) -> Result<serde_json::Value> {
    ensure!(
        artifacts::profile().network == "mainnet",
        "run requires the mainnet build"
    );
    fs::create_dir_all(&data_directory)?;
    let started = Instant::now();
    eprintln!("\n\x1b[1;32m  PARAMO1D  ·  MAINNET\x1b[0m\n");
    eprintln!(
        "  CPU        {} automatic verification workers",
        rayon::current_num_threads()
    );
    eprintln!("  RUNTIME    Loading released verification parameters");
    let legacy = artifacts::read_bounded(&artifact_directory.join("legacy"), 4 * 1024 * 1024)?;
    let bank = legacy[legacy.len() - 32..].try_into()?;
    let profile = NetworkProfile::for_proof_bank(bank);
    eprintln!("  NETWORK    Discovering mainnet peers over device internet");
    with_connection(bank, profile, |executor, mut network| {
        crate::verifier_session::with(&artifact_directory, |verifier| {
            executor.block_on(crate::mobile_control::cancellable(async move {
        let mut round = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_millis() as u64;
        let mut previous: Option<PathBuf> = None;
        let mut accepted_height = None;
        let mut resumed = None;
        if let Ok(bytes) = artifacts::read_bounded(&data_directory.join("accepted.json"), 1024 * 1024) {
            if let Ok(saved) = serde_json::from_slice::<serde_json::Value>(&bytes) {
                if let Some(name) = saved["bundle"].as_str().filter(|name| name.starts_with("candidate-") && name.len()<128 && !name.contains('/') && !name.contains('\\')) {
                    let directory=data_directory.join(name);
                    // Check the stored header work first. A newer recursive
                    // proof authenticates the resulting State and history.
                    if let Ok((height,state))=verifier.prepare_resume(&directory) {
                        accepted_height=Some(height);
                        resumed=state.map(|state|serde_json::json!({"transport":"direct-p2p","bundle":name,"verified":state,"reused_boundary":true}));
                        previous=Some(directory);
                    }
                }
            }
        }
        let mut initial_sync_ms = None;
        loop {
            let candidates = discover(&mut network).await?;
            if accepted_height.is_some_and(|height| candidates.iter().all(|(_, point)| point.height <= height)) {
                // Returning the saved State itself requires its full proof.
                if resumed.is_none() {
                    if let Some(directory) = previous.as_ref() {
                        match verifier.verify_bundle(directory) {
                            Ok(state) => resumed=Some(serde_json::json!({"transport":"direct-p2p","bundle":directory.file_name().and_then(|v|v.to_str()),"verified":state,"reused_boundary":true})),
                            Err(error) => {
                                verifier.discard_resume_headers();
                                previous=None; accepted_height=None;
                                eprintln!("  RECOVER    Stored proof: {error:#}");
                                continue;
                            }
                        }
                    }
                }
                if once { return resumed.context("accepted boundary unavailable"); }
                tokio::time::sleep(Duration::from_secs(5)).await;
                continue;
            }
            let mut accepted = None;
            let update_started = Instant::now();
            for (peer, boundary) in candidates {
                round += 1;
                let output = data_directory.join(format!("candidate-{round}-{}", boundary.height));
                if accepted_height.is_some_and(|height| boundary.height <= height) { continue; }
                crate::mobile_control::verifying();
                match fetch_bundle(&network, peer, boundary, &output, &verifier, previous.as_deref()).await {
                    Ok(()) => {
                        eprintln!("  VERIFY     Header work, fork certificate and recursive State proof");
                        let checked = verifier.verify_bundle(&output);
                        match checked {
                            Ok(state) => { accepted = Some((state, output)); break; }
                            Err(error) => eprintln!("  RETRY      Candidate verification: {error:#}"),
                        }
                    }
                    Err(error) => eprintln!("  RETRY      Peer transfer: {error:#}"),
                }
            }
            // A damaged saved bundle must not pin an unusable header hint.
            // Authenticate the old proof before retaining its floor after a
            // failed update. Only the provisional cold-start hint is cleared.
            if accepted.is_none() && verifier.discard_resume_headers() {
                let old_is_valid = previous.as_ref().is_some_and(|directory|verifier.verify_bundle(directory).is_ok());
                if !old_is_valid {
                    previous=None; accepted_height=None; resumed=None;
                    continue;
                }
            }
            let (state, directory) = accepted.context("no mainnet candidate passed verification")?;
            eprintln!("\n\x1b[1;32m  SYNCED     MAINNET · BLOCK {}\x1b[0m", state.height());
            eprintln!("  STATE      {}", state.state_root());
            if initial_sync_ms.is_none() { eprintln!("  TOTAL      {:.2} seconds from process startup\n", started.elapsed().as_secs_f64()); }
            else { eprintln!("  UPDATE     {:.2} seconds\n", update_started.elapsed().as_secs_f64()); }
            let startup_ms = *initial_sync_ms.get_or_insert_with(|| started.elapsed().as_millis());
            let peak = peak_memory_kib();
            if let Some(kib) = peak { eprintln!("  RAM        {:.1} MiB peak", kib as f64/1024.0); }
            let result = serde_json::json!({"transport":"direct-p2p","bundle":directory.file_name().and_then(|v|v.to_str()),"startup_ms":startup_ms,"update_ms":update_started.elapsed().as_millis(),"peak_rss_kib":peak,"verified":state});
            let mut record=tempfile::NamedTempFile::new_in(&data_directory)?;
            record.write_all(&serde_json::to_vec_pretty(&result)?)?;
            record.as_file().sync_all()?;
            record.persist(data_directory.join("accepted.json")).map_err(|e|e.error)?;
            if once {
                if let Some(old)=previous.filter(|old|old!=&directory) { fs::remove_dir_all(old)?; }
                return Ok(result);
            }
            accepted_height = Some(state.height());
            if let Some(old) = previous.replace(directory) { fs::remove_dir_all(old)?; }
            tokio::time::sleep(Duration::from_secs(5)).await;
        }
    }))
        })
    })
}
