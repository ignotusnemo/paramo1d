// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! # noid_p2p — libp2p Networking for Paranoid
//!
//! Implements:
//! - GossipSub broadcast: blocks (/paranoid/blocks/1), txs (/paranoid/txs/1)
//! - Request-Response: headers, complete recent-block bundles, and HistoryStep terminals
//! - Identify + Ping for peer management

pub mod availability_codec;
pub mod behaviour;
mod command_dispatch;
mod event_dispatch;
pub mod header_protocol;
pub mod header_sync_codec;
pub mod history_step_codec;
mod identity_store;
mod inbound_budget;
pub mod manifest_page_codec;
mod mempool_recovery;
pub mod mempool_sync_codec;
pub mod network;
pub mod network_profile;
pub mod object_codec;
pub mod object_protocol;
mod outbound_budget;
mod peer_diversity;
pub mod peer_store;
pub mod protocol;
mod resource_profile;
mod retained_object_cache;
mod tx_delivery;
pub use tx_delivery::TxDelivery;
pub mod state_manifest_codec;
pub mod state_segment_codec;

pub use command_dispatch::NetworkCommandSender;
pub use network::{
    NetworkCommand, NetworkEvent, NetworkEventReceiver, NetworkEventRecvError, P2PHealthSnapshot,
    P2PNetwork, RequestFailureKind,
};
pub use protocol::{NetworkTopics, Topics};
pub use resource_profile::BackgroundCapacity;
pub mod fork_origin;
