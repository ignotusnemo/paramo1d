// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Small, transport-level neighbour diversity policy.
//!
//! A `PeerId` proves key continuity, not operator diversity: one host can mint
//! arbitrarily many identities.  Public automatic outbound connections are
//! therefore spread across coarse network groups (IPv4 /16, IPv6 /32), while
//! inbound fan-in is bounded both per address and per group.  Private/LAN
//! addresses are deliberately outside this policy so local clusters and
//! multiple nodes behind a development NAT remain usable.

use std::collections::{HashMap, HashSet};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

use libp2p::{multiaddr::Protocol, swarm::ConnectionId, Multiaddr, PeerId};

// Bitcoin Core uses distinct automatic outbound netgroups, while production
// Ethereum clients tolerate several co-located peers. Two paths per coarse
// group preserve provider/NAT usability without letting one cheap prefix fill
// a 64-connection outbound budget.
const MAX_PUBLIC_OUTBOUND_PEERS_PER_GROUP: usize = 2;
// Shared VPN exits, carrier-grade NAT and enterprise gateways routinely place
// many unrelated wallets behind one public address. Permit a useful cohort,
// while retaining a hard per-address bound against one-source exhaustion.
const MAX_PUBLIC_INBOUND_PEERS_PER_IP: usize = 32;
const MAX_PUBLIC_INBOUND_CONNECTIONS_PER_GROUP: usize = 96;
// The connection layer permits 128 inbound sessions. Once the first 96 public
// identities are occupied, the final quarter is reserved for network groups
// that are not already well represented. This is softer than rejecting every
// ninth wallet behind a shared gateway and still prevents one /16 from taking
// the entire node.
const INBOUND_UNRESERVED_PEERS: usize = 96;
const INBOUND_RESERVED_GROUP_PEERS: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum PublicNetworkGroup {
    Ipv4([u8; 2]),
    Ipv6([u8; 4]),
}

impl PublicNetworkGroup {
    fn from_ip(ip: IpAddr) -> Self {
        match ip {
            IpAddr::V4(ip) => {
                let octets = ip.octets();
                Self::Ipv4([octets[0], octets[1]])
            }
            IpAddr::V6(ip) => {
                let octets = ip.octets();
                Self::Ipv6([octets[0], octets[1], octets[2], octets[3]])
            }
        }
    }
}

pub(crate) fn public_network_group(addr: &Multiaddr) -> Option<PublicNetworkGroup> {
    public_ip(addr).map(PublicNetworkGroup::from_ip)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DiversityRejection {
    OutboundGroupFull { group: PublicNetworkGroup },
    InboundIpFull { ip: IpAddr },
    InboundGroupFull { group: PublicNetworkGroup },
    InboundDiversityReserve { group: PublicNetworkGroup },
    InboundUnclassifiedReserve,
}

#[derive(Clone, Copy, Debug)]
enum TrackedDirection {
    Outbound,
    Inbound,
}

#[derive(Clone, Copy, Debug)]
struct TrackedConnection {
    peer: PeerId,
    ip: IpAddr,
    group: PublicNetworkGroup,
    direction: TrackedDirection,
}

/// Tracks admitted public connections so limits are released exactly when the
/// corresponding libp2p connection closes.
#[derive(Default)]
pub(crate) struct PeerDiversity {
    // `None` records an admitted LAN/private connection. Keeping it here lets
    // the close path distinguish a deliberately rejected public connection
    // (which must not emit a phantom PeerDisconnected event).
    connections: HashMap<ConnectionId, Option<TrackedConnection>>,
    outbound_groups: HashMap<PublicNetworkGroup, HashMap<PeerId, usize>>,
    inbound_ips: HashMap<IpAddr, HashMap<PeerId, usize>>,
    inbound_groups: HashMap<PublicNetworkGroup, HashMap<PeerId, usize>>,
    unclassified_inbound: HashSet<ConnectionId>,
}

impl PeerDiversity {
    pub(crate) fn public_group_for_peer(&self, peer: PeerId) -> Option<PublicNetworkGroup> {
        self.connections
            .values()
            .filter_map(|connection| connection.as_ref())
            .filter(|connection| connection.peer == peer)
            .map(|connection| connection.group)
            .min_by_key(|group| match group {
                PublicNetworkGroup::Ipv4(prefix) => (0u8, u32::from(u16::from_be_bytes(*prefix))),
                PublicNetworkGroup::Ipv6(prefix) => (1u8, u32::from_be_bytes(*prefix)),
            })
    }

    /// Stable coarse domain used by higher-level source scheduling. Public
    /// peers share their admitted IPv4 /16 or IPv6 /32; private/LAN peers fall
    /// back to their authenticated identity so local test clusters still
    /// provide independent sources.
    pub(crate) fn failure_domain(&self, peer: PeerId) -> u64 {
        let public = self.public_group_for_peer(peer).map(|group| match group {
            PublicNetworkGroup::Ipv4(prefix) => {
                0x1000_0000_0000_0000u64 | u64::from(u16::from_be_bytes(prefix))
            }
            PublicNetworkGroup::Ipv6(prefix) => {
                0x2000_0000_0000_0000u64 | u64::from(u32::from_be_bytes(prefix))
            }
        });
        public.unwrap_or_else(|| {
            // FNV-1a is sufficient here: this is scheduling diversity, not a
            // cryptographic identity. PeerId authentication happens earlier.
            peer.to_bytes()
                .iter()
                .fold(0xcbf2_9ce4_8422_2325u64, |hash, byte| {
                    (hash ^ u64::from(*byte)).wrapping_mul(0x1000_0000_01b3)
                })
                | 0x8000_0000_0000_0000
        })
    }

    pub(crate) fn try_admit(
        &mut self,
        connection_id: ConnectionId,
        peer: PeerId,
        remote_addr: &Multiaddr,
        outbound: bool,
    ) -> Result<(), DiversityRejection> {
        let Some(ip) = public_ip(remote_addr) else {
            // Local/private transports are useful for LAN discovery and test
            // clusters. Inbound sessions still consume the unreserved pool:
            // otherwise relayed or unclassified connections could fill the
            // hard swarm limit while the diversity reserve appeared empty.
            if !outbound && self.inbound_connection_count() >= INBOUND_UNRESERVED_PEERS {
                return Err(DiversityRejection::InboundUnclassifiedReserve);
            }
            self.connections.insert(connection_id, None);
            if !outbound {
                self.unclassified_inbound.insert(connection_id);
            }
            return Ok(());
        };
        let group = PublicNetworkGroup::from_ip(ip);

        if outbound {
            if distinct_peer_count(&self.outbound_groups, &group, peer)
                >= MAX_PUBLIC_OUTBOUND_PEERS_PER_GROUP
            {
                return Err(DiversityRejection::OutboundGroupFull { group });
            }
        } else {
            if distinct_peer_count(&self.inbound_ips, &ip, peer) >= MAX_PUBLIC_INBOUND_PEERS_PER_IP
            {
                return Err(DiversityRejection::InboundIpFull { ip });
            }
            let group_connections = connection_count(&self.inbound_groups, &group);
            if group_connections >= MAX_PUBLIC_INBOUND_CONNECTIONS_PER_GROUP {
                return Err(DiversityRejection::InboundGroupFull { group });
            }
            if self.inbound_connection_count() >= INBOUND_UNRESERVED_PEERS
                && group_connections >= INBOUND_RESERVED_GROUP_PEERS
            {
                return Err(DiversityRejection::InboundDiversityReserve { group });
            }
        }

        let direction = if outbound {
            increment_peer_count(&mut self.outbound_groups, group, peer);
            TrackedDirection::Outbound
        } else {
            increment_peer_count(&mut self.inbound_ips, ip, peer);
            increment_peer_count(&mut self.inbound_groups, group, peer);
            TrackedDirection::Inbound
        };
        let previous = self.connections.insert(
            connection_id,
            Some(TrackedConnection {
                peer,
                ip,
                group,
                direction,
            }),
        );
        debug_assert!(previous.is_none(), "libp2p connection IDs are unique");
        Ok(())
    }

    pub(crate) fn remove(&mut self, connection_id: ConnectionId) -> bool {
        self.unclassified_inbound.remove(&connection_id);
        let Some(connection) = self.connections.remove(&connection_id) else {
            return false;
        };
        let Some(connection) = connection else {
            return true;
        };
        match connection.direction {
            TrackedDirection::Outbound => {
                decrement_peer_count(&mut self.outbound_groups, connection.group, connection.peer);
            }
            TrackedDirection::Inbound => {
                decrement_peer_count(&mut self.inbound_ips, connection.ip, connection.peer);
                decrement_peer_count(&mut self.inbound_groups, connection.group, connection.peer);
            }
        }
        true
    }

    pub(crate) fn outbound_candidate_allowed_with_pending(
        &self,
        peer: PeerId,
        remote_addr: &Multiaddr,
        pending_same_group: usize,
    ) -> bool {
        let Some(group) = public_network_group(remote_addr) else {
            return false;
        };
        distinct_peer_count(&self.outbound_groups, &group, peer).saturating_add(pending_same_group)
            < MAX_PUBLIC_OUTBOUND_PEERS_PER_GROUP
    }

    /// DNS transports may surface `/dns4/...` at ConnectionEstablished and
    /// only reveal the peer's public listen address through Identify. Upgrade
    /// that already-admitted outbound connection once without double-counting
    /// connections whose endpoint was an IP from the start.
    pub(crate) fn classify_outbound_dns_connection(
        &mut self,
        connection_id: ConnectionId,
        peer: PeerId,
        remote_addr: &Multiaddr,
    ) -> Result<(), DiversityRejection> {
        let Some(existing) = self.connections.get(&connection_id) else {
            return Ok(());
        };
        if existing.is_some() {
            return Ok(());
        }
        let Some(ip) = public_ip(remote_addr) else {
            return Ok(());
        };
        let group = PublicNetworkGroup::from_ip(ip);
        if distinct_peer_count(&self.outbound_groups, &group, peer)
            >= MAX_PUBLIC_OUTBOUND_PEERS_PER_GROUP
        {
            return Err(DiversityRejection::OutboundGroupFull { group });
        }
        increment_peer_count(&mut self.outbound_groups, group, peer);
        self.connections.insert(
            connection_id,
            Some(TrackedConnection {
                peer,
                ip,
                group,
                direction: TrackedDirection::Outbound,
            }),
        );
        Ok(())
    }

    fn inbound_connection_count(&self) -> usize {
        self.connections
            .values()
            .filter(|connection| {
                matches!(
                    connection,
                    Some(TrackedConnection {
                        direction: TrackedDirection::Inbound,
                        ..
                    })
                )
            })
            .count()
            .saturating_add(self.unclassified_inbound.len())
    }
}

fn distinct_peer_count<K: Eq + std::hash::Hash>(
    groups: &HashMap<K, HashMap<PeerId, usize>>,
    key: &K,
    candidate: PeerId,
) -> usize {
    groups.get(key).map_or(0, |peers| {
        peers.len() - usize::from(peers.contains_key(&candidate))
    })
}

fn increment_peer_count<K: Eq + std::hash::Hash>(
    groups: &mut HashMap<K, HashMap<PeerId, usize>>,
    key: K,
    peer: PeerId,
) {
    *groups.entry(key).or_default().entry(peer).or_default() += 1;
}

fn connection_count<K: Eq + std::hash::Hash>(
    groups: &HashMap<K, HashMap<PeerId, usize>>,
    key: &K,
) -> usize {
    groups
        .get(key)
        .map_or(0, |peers| peers.values().copied().sum())
}

fn decrement_peer_count<K: Eq + std::hash::Hash>(
    groups: &mut HashMap<K, HashMap<PeerId, usize>>,
    key: K,
    peer: PeerId,
) {
    let remove_group = if let Some(peers) = groups.get_mut(&key) {
        if let Some(count) = peers.get_mut(&peer) {
            *count -= 1;
            if *count == 0 {
                peers.remove(&peer);
            }
        }
        peers.is_empty()
    } else {
        false
    };
    if remove_group {
        groups.remove(&key);
    }
}

/// Returns the first globally-routable IP in a transport address. DNS is
/// resolved by libp2p before the underlying TCP dial, so successful public
/// connection endpoints normally contain the resolved IP.
pub(crate) fn public_ip(addr: &Multiaddr) -> Option<IpAddr> {
    addr.iter().find_map(|protocol| match protocol {
        Protocol::Ip4(ip) if is_public_ipv4(ip) => Some(IpAddr::V4(ip)),
        Protocol::Ip6(ip) if is_public_ipv6(ip) => Some(IpAddr::V6(ip)),
        _ => None,
    })
}

pub(crate) fn contains_public_ip(addr: &Multiaddr) -> bool {
    public_ip(addr).is_some()
}

fn is_public_ipv4(ip: Ipv4Addr) -> bool {
    let [a, b, c, _] = ip.octets();
    !(a == 0
        || a == 10
        || a == 127
        || a >= 224
        || (a == 100 && (64..=127).contains(&b))
        || (a == 169 && b == 254)
        || (a == 172 && (16..=31).contains(&b))
        || (a == 192 && b == 0 && c == 0)
        || (a == 192 && b == 0 && c == 2)
        || (a == 192 && b == 168)
        || (a == 198 && (b == 18 || b == 19))
        || (a == 198 && b == 51 && c == 100)
        || (a == 203 && b == 0 && c == 113))
}

fn is_public_ipv6(ip: Ipv6Addr) -> bool {
    let octets = ip.octets();
    let global_unicast = octets[0] & 0xe0 == 0x20;
    let documentation = octets[0..4] == [0x20, 0x01, 0x0d, 0xb8];
    global_unicast && !documentation
}

#[cfg(test)]
mod tests {
    use super::*;

    fn addr(value: &str) -> Multiaddr {
        value.parse().unwrap()
    }

    #[test]
    fn public_network_groups_are_coarse_and_non_public_addresses_are_exempt() {
        assert_eq!(
            public_ip(&addr("/ip4/8.8.4.4/tcp/9500")).map(PublicNetworkGroup::from_ip),
            Some(PublicNetworkGroup::Ipv4([8, 8]))
        );
        assert_eq!(
            public_ip(&addr("/ip6/2606:4700:4700::1111/tcp/9500")).map(PublicNetworkGroup::from_ip),
            Some(PublicNetworkGroup::Ipv6([0x26, 0x06, 0x47, 0x00]))
        );
        for non_public in [
            "/ip4/127.0.0.1/tcp/9500",
            "/ip4/10.1.2.3/tcp/9500",
            "/ip4/192.0.2.1/tcp/9500",
            "/ip6/::1/tcp/9500",
            "/ip6/fd00::1/tcp/9500",
            "/ip6/2001:db8::1/tcp/9500",
        ] {
            assert_eq!(public_ip(&addr(non_public)), None, "{non_public}");
        }
    }

    #[test]
    fn outbound_admission_requires_distinct_public_groups_but_allows_second_path() {
        let mut diversity = PeerDiversity::default();
        let first = PeerId::random();
        let second = PeerId::random();
        let third = PeerId::random();
        let id1 = ConnectionId::new_unchecked(1);
        let id2 = ConnectionId::new_unchecked(2);
        let id3 = ConnectionId::new_unchecked(3);
        let id4 = ConnectionId::new_unchecked(4);
        let id5 = ConnectionId::new_unchecked(5);

        diversity
            .try_admit(id1, first, &addr("/ip4/8.8.1.1/tcp/9500"), true)
            .unwrap();
        diversity
            .try_admit(id2, first, &addr("/ip4/8.8.2.2/tcp/9500"), true)
            .expect("direct plus relay path for one identity stays usable");
        diversity
            .try_admit(id3, second, &addr("/ip4/8.8.3.3/tcp/9500"), true)
            .expect("a second identity in one provider group is tolerated");
        assert!(matches!(
            diversity.try_admit(id4, third, &addr("/ip4/8.8.4.4/tcp/9500"), true),
            Err(DiversityRejection::OutboundGroupFull { .. })
        ));
        diversity
            .try_admit(id4, third, &addr("/ip4/9.9.3.3/tcp/9500"), true)
            .expect("a distinct /16 is independent");

        diversity.remove(id1);
        assert!(matches!(
            diversity.try_admit(id5, third, &addr("/ip4/8.8.5.5/tcp/9500"), true),
            Err(DiversityRejection::OutboundGroupFull { .. })
        ));
        diversity.remove(id2);
        diversity
            .try_admit(id5, third, &addr("/ip4/8.8.5.5/tcp/9500"), true)
            .expect("the group is released after the final path closes");
    }

    #[test]
    fn inbound_admission_bounds_peer_ids_from_one_public_ip() {
        let mut diversity = PeerDiversity::default();
        let public = addr("/ip4/8.8.8.8/tcp/50000");
        for id in 0..MAX_PUBLIC_INBOUND_PEERS_PER_IP {
            diversity
                .try_admit(
                    ConnectionId::new_unchecked(id),
                    PeerId::random(),
                    &public,
                    false,
                )
                .unwrap();
        }
        assert!(matches!(
            diversity.try_admit(
                ConnectionId::new_unchecked(100),
                PeerId::random(),
                &public,
                false,
            ),
            Err(DiversityRejection::InboundIpFull { .. })
        ));
    }

    #[test]
    fn inbound_reserve_stays_open_for_underrepresented_networks() {
        let mut diversity = PeerDiversity::default();
        let mut connection = 1u64;
        for first_octet in 20u8..32 {
            let group_addr = addr(&format!("/ip4/{first_octet}.1.1.1/tcp/50000"));
            for _ in 0..INBOUND_RESERVED_GROUP_PEERS {
                diversity
                    .try_admit(
                        ConnectionId::new_unchecked(connection as usize),
                        PeerId::random(),
                        &group_addr,
                        false,
                    )
                    .unwrap();
                connection += 1;
            }
        }
        assert_eq!(connection - 1, INBOUND_UNRESERVED_PEERS as u64);
        assert!(matches!(
            diversity.try_admit(
                ConnectionId::new_unchecked(connection as usize),
                PeerId::random(),
                &addr("/ip4/20.1.2.3/tcp/50000"),
                false,
            ),
            Err(DiversityRejection::InboundDiversityReserve { .. })
        ));
        diversity
            .try_admit(
                ConnectionId::new_unchecked((connection + 1) as usize),
                PeerId::random(),
                &addr("/ip4/40.1.2.3/tcp/50000"),
                false,
            )
            .expect("reserved capacity admits a new network group");
    }

    #[test]
    fn second_paths_cannot_fill_the_inbound_budget_from_one_public_group() {
        let mut diversity = PeerDiversity::default();
        let mut connection = 1usize;
        for host in 1..=48u8 {
            let peer = PeerId::random();
            let remote = addr(&format!("/ip4/8.8.1.{host}/tcp/50000"));
            for _ in 0..2 {
                diversity
                    .try_admit(
                        ConnectionId::new_unchecked(connection),
                        peer,
                        &remote,
                        false,
                    )
                    .unwrap();
                connection += 1;
            }
        }
        assert_eq!(diversity.inbound_connection_count(), 96);
        assert!(matches!(
            diversity.try_admit(
                ConnectionId::new_unchecked(connection),
                PeerId::random(),
                &addr("/ip4/8.8.2.1/tcp/50000"),
                false,
            ),
            Err(DiversityRejection::InboundGroupFull { .. })
        ));

        diversity.remove(ConnectionId::new_unchecked(2));
        diversity
            .try_admit(
                ConnectionId::new_unchecked(connection + 1),
                PeerId::random(),
                &addr("/ip4/8.8.2.2/tcp/50000"),
                false,
            )
            .expect("removing one path releases exactly one group slot");
    }

    #[test]
    fn shared_ip_limit_counts_identities_but_every_path_consumes_capacity() {
        let mut diversity = PeerDiversity::default();
        let remote = addr("/ip4/9.9.9.9/tcp/50000");
        let mut connection = 1usize;
        for _ in 0..MAX_PUBLIC_INBOUND_PEERS_PER_IP {
            let peer = PeerId::random();
            for _ in 0..2 {
                diversity
                    .try_admit(
                        ConnectionId::new_unchecked(connection),
                        peer,
                        &remote,
                        false,
                    )
                    .unwrap();
                connection += 1;
            }
        }
        assert_eq!(diversity.inbound_connection_count(), 64);
        assert!(matches!(
            diversity.try_admit(
                ConnectionId::new_unchecked(connection),
                PeerId::random(),
                &remote,
                false,
            ),
            Err(DiversityRejection::InboundIpFull { .. })
        ));
    }

    #[test]
    fn unclassified_inbound_cannot_consume_the_diversity_reserve() {
        let mut diversity = PeerDiversity::default();
        let private = addr("/ip4/10.0.0.1/tcp/50000");
        for connection in 1..=INBOUND_UNRESERVED_PEERS {
            diversity
                .try_admit(
                    ConnectionId::new_unchecked(connection),
                    PeerId::random(),
                    &private,
                    false,
                )
                .unwrap();
        }
        assert!(matches!(
            diversity.try_admit(
                ConnectionId::new_unchecked(INBOUND_UNRESERVED_PEERS + 1),
                PeerId::random(),
                &private,
                false,
            ),
            Err(DiversityRejection::InboundUnclassifiedReserve)
        ));
    }

    #[test]
    fn public_failure_domains_follow_network_groups() {
        let first = PeerId::random();
        let second = PeerId::random();
        let mut diversity = PeerDiversity::default();
        diversity
            .try_admit(
                ConnectionId::new_unchecked(101),
                first,
                &addr("/ip4/8.8.1.1/tcp/9500"),
                true,
            )
            .unwrap();
        diversity
            .try_admit(
                ConnectionId::new_unchecked(102),
                second,
                &addr("/ip4/8.8.2.2/tcp/9500"),
                true,
            )
            .unwrap();
        assert_eq!(
            diversity.failure_domain(first),
            diversity.failure_domain(second)
        );
        assert_ne!(
            diversity.failure_domain(first),
            diversity.failure_domain(PeerId::random())
        );
    }

    #[test]
    fn dns_outbound_is_classified_after_identify() {
        let mut diversity = PeerDiversity::default();
        let first = PeerId::random();
        let second = PeerId::random();
        let third = PeerId::random();
        let id1 = ConnectionId::new_unchecked(1);
        let id2 = ConnectionId::new_unchecked(2);
        let id3 = ConnectionId::new_unchecked(3);
        let dns = addr("/dns4/seed.example/tcp/9500");

        diversity.try_admit(id1, first, &dns, true).unwrap();
        diversity
            .classify_outbound_dns_connection(id1, first, &addr("/ip4/8.8.1.1/tcp/9500"))
            .unwrap();
        diversity.try_admit(id2, second, &dns, true).unwrap();
        diversity
            .classify_outbound_dns_connection(id2, second, &addr("/ip4/8.8.2.2/tcp/9500"))
            .unwrap();
        diversity.try_admit(id3, third, &dns, true).unwrap();
        assert!(matches!(
            diversity.classify_outbound_dns_connection(id3, third, &addr("/ip4/8.8.3.3/tcp/9500"),),
            Err(DiversityRejection::OutboundGroupFull { .. })
        ));
    }
}
