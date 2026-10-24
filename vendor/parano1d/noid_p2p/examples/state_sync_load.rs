// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Bounded transport load clients for an isolated local cluster.
//!
//! These clients exercise real profile, manifest/page, segment, header and
//! exact-object codecs. They do not verify recursive consensus proofs and are
//! deliberately paired with real full-node receivers in the live scenario.

use std::path::PathBuf;
use std::time::{Duration, Instant};

use futures::StreamExt;
use libp2p::{
    identity, noise, request_response as rr,
    swarm::{NetworkBehaviour, StreamProtocol, SwarmEvent},
    tcp, yamux, Multiaddr, SwarmBuilder,
};
use noid_p2p::{
    header_sync_codec::HeaderSyncCodec,
    manifest_page_codec::ManifestPageCodec,
    network_profile::{NetworkProfileCodec, NetworkProfileRequest, NetworkProfileResponse},
    object_codec::ObjectCodec,
    object_protocol::{ChainPoint, DataResponseStatus, GetObjectsRequest, ObjectId, SnapshotId},
    protocol::{
        decode_snapshot_manifest_page, GetHeadersRequest, GetSnapshotManifestPageRequest,
        GetStateManifestHeader, GetStateManifestRequest, GetStateSegmentRequest,
        SnapshotManifestPageObjectId,
    },
    state_manifest_codec::StateManifestCodec,
    state_segment_codec::StateSegmentCodec,
};
use serde::Serialize;

#[derive(NetworkBehaviour)]
struct ProbeBehaviour {
    identify: libp2p::identify::Behaviour,
    profiles: rr::Behaviour<NetworkProfileCodec>,
    manifests: rr::Behaviour<StateManifestCodec>,
    pages: rr::Behaviour<ManifestPageCodec>,
    segments: rr::Behaviour<StateSegmentCodec>,
    headers: rr::Behaviour<HeaderSyncCodec>,
    objects: rr::Behaviour<ObjectCodec>,
}

#[derive(Default, Serialize)]
struct Stats {
    client: usize,
    profile_verified: bool,
    state_ready: u64,
    state_busy: u64,
    state_unavailable: u64,
    state_failures: u64,
    canonical_bytes: u64,
    wire_payload_bytes: u64,
    v5_segments: u64,
    v6_segments: u64,
    header_ready: u64,
    header_busy: u64,
    live_ready: u64,
    live_busy: u64,
    live_bytes: u64,
    control_failures: u64,
    connection_failures: u64,
    header_latency_ms: Vec<u64>,
    live_latency_ms: Vec<u64>,
    inventory_digest: Option<String>,
    exact_objects: Vec<ObjectId>,
}

fn protocols(versions: &[&str]) -> Vec<(StreamProtocol, rr::ProtocolSupport)> {
    let prefix = noid_chain::consensus::NetworkConfig::mainnet().p2p_protocol_id;
    versions
        .iter()
        .map(|version| {
            (
                StreamProtocol::try_from_owned(format!("{prefix}/{version}")).unwrap(),
                rr::ProtocolSupport::Full,
            )
        })
        .collect()
}

fn config() -> rr::Config {
    rr::Config::default()
        .with_request_timeout(Duration::from_secs(20))
        .with_max_concurrent_streams(2)
}

async fn client(
    address: Multiaddr,
    index: usize,
    seconds: u64,
    height: u64,
    legacy: bool,
    activation: Option<PathBuf>,
    scenario: String,
) -> anyhow::Result<Stats> {
    let identity = identity::Keypair::generate_ed25519();
    let behaviour = ProbeBehaviour {
        identify: libp2p::identify::Behaviour::new(libp2p::identify::Config::new(
            "/ipfs/id/1.0.0".into(),
            identity.public(),
        )),
        profiles: rr::Behaviour::with_codec(
            NetworkProfileCodec,
            protocols(&["sync/profile/6"]),
            config(),
        ),
        manifests: rr::Behaviour::with_codec(
            StateManifestCodec::default(),
            protocols(&["sync/manifest/7"]),
            config(),
        ),
        pages: rr::Behaviour::with_codec(
            ManifestPageCodec::default(),
            protocols(&["sync/manifest-page/1"]),
            config(),
        ),
        segments: rr::Behaviour::with_codec(
            StateSegmentCodec::default(),
            protocols(if legacy {
                &["sync/segment/5"]
            } else {
                &["sync/segment/6", "sync/segment/5"]
            }),
            config(),
        ),
        headers: rr::Behaviour::with_codec(
            HeaderSyncCodec::default(),
            protocols(&["sync/headers/5", "sync/headers/4"]),
            config(),
        ),
        objects: rr::Behaviour::with_codec(
            ObjectCodec::default(),
            protocols(&["sync/objects/2"]),
            config(),
        ),
    };
    let mut swarm = SwarmBuilder::with_existing_identity(identity)
        .with_tokio()
        .with_tcp(
            tcp::Config::default(),
            noise::Config::new,
            yamux::Config::default,
        )?
        .with_behaviour(|_| behaviour)?
        .with_swarm_config(|config| {
            config.with_idle_connection_timeout(Duration::from_secs(seconds + 30))
        })
        .build();
    swarm.dial(address)?;
    let mut stats = Stats {
        client: index,
        ..Default::default()
    };
    let mut peer = None;
    let mut profile = None;
    let mut pending_profile_channel = None;
    let mut manifest: Option<GetStateManifestHeader> = None;
    let mut descriptor = None;
    let mut inventory = Vec::new();
    let mut state_pending = false;
    let mut header_pending = false;
    let mut live_pending = false;
    let mut live_cursor = 0usize;
    let mut manifest_pending = false;
    let mut header_started = None;
    let mut live_started = None;
    let mut next_state = Instant::now();
    let mut next_header = Instant::now();
    let mut next_live = Instant::now();
    let mut next_manifest = Instant::now();
    let mut active = activation.is_none();
    let deadline = tokio::time::sleep(Duration::from_secs(seconds + if active { 0 } else { 120 }));
    tokio::pin!(deadline);
    let mut tick = tokio::time::interval(Duration::from_millis(25));
    loop {
        tokio::select! {
            _ = &mut deadline => break,
            _ = tick.tick() => {
                let Some(peer) = peer.filter(|_| stats.profile_verified) else { continue; };
                let now = Instant::now();
                if scenario == "state" && descriptor.is_none() && !manifest_pending && now >= next_manifest {
                    swarm.behaviour_mut().manifests.send_request(&peer, GetStateManifestRequest {
                        requester_height: 0, requested_manifest_digest: [0; 32],
                    });
                    manifest_pending = true;
                    next_manifest = now + Duration::from_secs(2);
                }
                if !active && activation.as_ref().is_some_and(|path| path.exists()) {
                    active = true;
                    deadline.as_mut().reset(tokio::time::Instant::now() + Duration::from_secs(seconds));
                }
                if !active { continue; }
                if scenario == "state" {
                  if let (Some(manifest), Some((segment_id, _, _))) = (&manifest, descriptor) {
                    if !state_pending && now >= next_state {
                        swarm.behaviour_mut().segments.send_request(&peer, GetStateSegmentRequest {
                            segment_id, additional_segments: Vec::new(), expected_tip_height: manifest.tip_height,
                            expected_tip_hash: manifest.tip_hash, manifest_digest: manifest.manifest_digest,
                        });
                        state_pending = true;
                    }
                  }
                }
                if !header_pending && now >= next_header {
                    swarm.behaviour_mut().headers.send_request(&peer, GetHeadersRequest {
                        start_height: height, count: 1, include_inventory: true,
                    });
                    header_pending = true;
                    header_started = Some(now);
                    next_header = now + Duration::from_secs(2);
                }
                if scenario != "inventory" && !live_pending && !inventory.is_empty() && now >= next_live {
                    // Recursive terminals must be requested alone. Alternate
                    // exact bodies and terminals while keeping one Live lease.
                    let object = inventory[live_cursor % inventory.len()];
                    live_cursor += 1;
                    swarm.behaviour_mut().objects.send_request(&peer, GetObjectsRequest { objects: vec![object] });
                    live_pending = true;
                    live_started = Some(now);
                    next_live = now + Duration::from_secs(2);
                }
            }
            event = swarm.select_next_some() => match event {
                SwarmEvent::ConnectionEstablished { peer_id, .. } => {
                    peer = Some(peer_id);
                    swarm.behaviour_mut().profiles.send_request(&peer_id, NetworkProfileRequest { expected_profile_id: [0; 32] });
                }
                SwarmEvent::OutgoingConnectionError { error, .. } => {
                    stats.connection_failures += 1;
                    eprintln!("client {index}: connection failed: {error}");
                }
                SwarmEvent::Behaviour(ProbeBehaviourEvent::Profiles(rr::Event::OutboundFailure { error, .. })) => {
                    stats.control_failures += 1;
                    eprintln!("client {index}: profile failed: {error}");
                }
                SwarmEvent::Behaviour(ProbeBehaviourEvent::Profiles(rr::Event::Message { peer, message, .. })) => match message {
                    rr::Message::Response { response, .. } => {
                        if profile == Some(response.profile) {
                            stats.profile_verified = true;
                        } else {
                            profile = Some(response.profile);
                            if let Some(channel) = pending_profile_channel.take() {
                                let _ = swarm.behaviour_mut().profiles.send_response(channel, NetworkProfileResponse { profile: response.profile });
                            }
                            swarm.behaviour_mut().profiles.send_request(&peer, NetworkProfileRequest { expected_profile_id: response.profile.profile_id });
                        }
                    }
                    rr::Message::Request { channel, .. } => {
                        if let Some(profile) = profile {
                            let _ = swarm.behaviour_mut().profiles.send_response(channel, NetworkProfileResponse { profile });
                        } else {
                            pending_profile_channel = Some(channel);
                        }
                    }
                },
                SwarmEvent::Behaviour(ProbeBehaviourEvent::Manifests(rr::Event::Message {
                    peer, message: rr::Message::Response { response, .. }, ..
                })) => {
                    manifest_pending = false;
                    if response.tip_height > 0 {
                        anyhow::ensure!(response.computed_manifest_digest() == Some(response.manifest_digest), "manifest digest mismatch");
                        if let Some(page) = response.descriptor_pages.first().copied() {
                            let snapshot = SnapshotId { boundary: ChainPoint::new(response.tip_height, response.tip_hash),
                                state_root: response.state_root, manifest_digest: response.manifest_digest, format_version: response.format_version };
                            swarm.behaviour_mut().pages.send_request(&peer, GetSnapshotManifestPageRequest {
                                object: SnapshotManifestPageObjectId { snapshot, page },
                            });
                            manifest = Some(response);
                            manifest_pending = true;
                        }
                    }
                }
                SwarmEvent::Behaviour(ProbeBehaviourEvent::Pages(rr::Event::Message {
                    message: rr::Message::Response { response, .. }, ..
                })) => {
                    manifest_pending = false;
                    if let Some(data) = &response.data {
                        let entries = decode_snapshot_manifest_page(response.object.page, data)
                            .ok_or_else(|| anyhow::anyhow!("manifest page digest mismatch"))?;
                        descriptor = entries.into_iter().max_by_key(|(_, _, length)| *length);
                        eprintln!("client {index}: prepared");
                    }
                }
                SwarmEvent::Behaviour(ProbeBehaviourEvent::Segments(rr::Event::Message {
                    message: rr::Message::Response { response, .. }, ..
                })) => {
                    state_pending = false;
                    if let DataResponseStatus::Busy { retry_after_ms } = response.status {
                        stats.state_busy += 1;
                        next_state = Instant::now() + Duration::from_millis(u64::from(retry_after_ms) + (index as u64 * 37) % 250);
                    } else if let Some(bytes) = &response.data {
                        let expected = manifest.as_ref().unwrap();
                        let (segment_id, _, length) = descriptor.unwrap();
                        anyhow::ensure!(response.segment_id == segment_id && response.expected_tip_height == expected.tip_height
                            && response.expected_tip_hash == expected.tip_hash && response.manifest_digest == expected.manifest_digest
                            && response.eff_log == expected.eff_log && bytes.len() == length as usize, "State response correlation mismatch");
                        anyhow::ensure!(noid_chain::storage::decode_sparse_segment(bytes).is_some(), "invalid canonical SGS1 data");
                        stats.state_ready += 1;
                        stats.canonical_bytes += bytes.len() as u64;
                        stats.wire_payload_bytes += response.transport.payload_bytes;
                        stats.v5_segments += u64::from(response.transport.version == 5);
                        stats.v6_segments += u64::from(response.transport.version == 6);
                    } else {
                        stats.state_unavailable += 1;
                        next_state = Instant::now() + Duration::from_secs(1);
                    }
                }
                SwarmEvent::Behaviour(ProbeBehaviourEvent::Headers(rr::Event::Message {
                    message: rr::Message::Response { response, .. }, ..
                })) => {
                    header_pending = false;
                    if matches!(response.status, DataResponseStatus::Busy { .. }) { stats.header_busy += 1; }
                    else {
                        stats.header_ready += 1;
                        if let Some(started) = header_started.take() {
                            stats.header_latency_ms.push(started.elapsed().as_millis() as u64);
                        }
                        if let Some(record) = response.records.first() {
                            anyhow::ensure!(record.header.height == height, "header correlation mismatch");
                            inventory = record.body.map(ObjectId::BlockBody).into_iter()
                                .chain(record.terminal.map(ObjectId::Terminal)).collect();
                            let digest = blake3::hash(&record.encode()?).to_hex().to_string();
                            if let Some(expected) = &stats.inventory_digest {
                                anyhow::ensure!(expected == &digest, "fixed inventory bytes changed during the workload");
                            }
                            stats.inventory_digest = Some(digest);
                            stats.exact_objects = inventory.clone();
                        }
                    }
                }
                SwarmEvent::Behaviour(ProbeBehaviourEvent::Objects(rr::Event::Message {
                    message: rr::Message::Response { response, .. }, ..
                })) => {
                    live_pending = false;
                    if matches!(response.status, DataResponseStatus::Busy { .. }) { stats.live_busy += 1; }
                    else {
                        if let Some(started) = live_started.take() {
                            stats.live_latency_ms.push(started.elapsed().as_millis() as u64);
                        }
                        for payload in &response.objects {
                            if let Some(bytes) = &payload.bytes {
                                anyhow::ensure!(inventory.contains(&payload.object) && payload.object.matches_bytes(bytes), "Live object digest mismatch");
                                stats.live_ready += 1;
                                stats.live_bytes += bytes.len() as u64;
                            }
                        }
                    }
                }
                SwarmEvent::Behaviour(ProbeBehaviourEvent::Segments(rr::Event::OutboundFailure { .. })) => {
                    stats.state_failures += 1;
                    state_pending = false;
                    next_state = Instant::now() + Duration::from_secs(1);
                }
                SwarmEvent::Behaviour(ProbeBehaviourEvent::Manifests(rr::Event::OutboundFailure { .. }))
                | SwarmEvent::Behaviour(ProbeBehaviourEvent::Pages(rr::Event::OutboundFailure { .. })) => {
                    manifest_pending = false; stats.control_failures += 1;
                }
                SwarmEvent::Behaviour(ProbeBehaviourEvent::Headers(rr::Event::OutboundFailure { .. })) => {
                    header_pending = false; stats.control_failures += 1;
                }
                SwarmEvent::Behaviour(ProbeBehaviourEvent::Objects(rr::Event::OutboundFailure { .. })) => {
                    live_pending = false; stats.control_failures += 1;
                }
                _ => {}
            }
        }
    }
    Ok(stats)
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    anyhow::ensure!(
        (6..=8).contains(&args.len()),
        "usage: state_sync_load MULTIADDR CLIENTS SECONDS TIP_HEIGHT LEGACY_CLIENTS [ACTIVATION_FILE|-] [state|inventory|mixed]"
    );
    let address: Multiaddr = args[1].replace("{client}", "0").parse()?;
    anyhow::ensure!(
        address
            .iter()
            .any(|part| matches!(part, libp2p::multiaddr::Protocol::Ip4(ip) if ip.is_loopback())),
        "load clients require an isolated loopback target"
    );
    let clients: usize = args[2].parse()?;
    anyhow::ensure!((1..=192).contains(&clients), "client count must be 1..192");
    let seconds: u64 = args[3].parse()?;
    anyhow::ensure!(
        (1..=600).contains(&seconds),
        "duration must be 1..600 seconds"
    );
    let height: u64 = args[4].parse()?;
    let legacy_clients: usize = args[5].parse()?;
    let scenario = args.get(7).map(String::as_str).unwrap_or("state");
    anyhow::ensure!(
        matches!(scenario, "state" | "inventory" | "mixed"),
        "unknown workload scenario"
    );
    let mut tasks = Vec::new();
    for index in 0..clients {
        // Namespace routes can give every client a distinct source IP without
        // changing production diversity limits. A fixed address also works.
        let address: Multiaddr = args[1].replace("{client}", &index.to_string()).parse()?;
        tasks.push(tokio::spawn(client(
            address,
            index,
            seconds,
            height,
            index < legacy_clients,
            args.get(6)
                .filter(|path| path.as_str() != "-")
                .map(PathBuf::from),
            scenario.to_owned(),
        )));
        // Exercise steady serving pressure without exceeding the separate
        // production ceiling for simultaneous unauthenticated handshakes.
        tokio::time::sleep(Duration::from_millis(30)).await;
    }
    let mut results = Vec::new();
    for task in tasks {
        results.push(task.await??);
    }
    println!("{}", serde_json::to_string(&results)?);
    Ok(())
}
