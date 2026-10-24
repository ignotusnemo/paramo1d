// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Lightweight process memory snapshots for opt-in profiling.
//!
//! Linux exposes current RSS and peak RSS in `/proc/self/status` as KiB values.
//! The helper intentionally returns `None` instead of failing on non-Linux hosts
//! or restricted environments. Callers should only use this on cold/profile
//! paths, not in hot proof loops.

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MemSnapshot {
    pub rss_kib: u64,
    pub hwm_kib: u64,
}

impl MemSnapshot {
    #[inline]
    pub fn rss_mb(self) -> f64 {
        self.rss_kib as f64 / 1024.0
    }

    #[inline]
    pub fn hwm_mb(self) -> f64 {
        self.hwm_kib as f64 / 1024.0
    }

    #[inline]
    pub fn delta_rss_mb(self, previous: MemSnapshot) -> f64 {
        (self.rss_kib as i128 - previous.rss_kib as i128) as f64 / 1024.0
    }
}

pub fn current_mem_snapshot() -> Option<MemSnapshot> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let mut rss_kib = None;
    let mut hwm_kib = None;

    for line in status.lines() {
        if let Some(rest) = line.strip_prefix("VmRSS:") {
            rss_kib = parse_proc_status_kib(rest);
        } else if let Some(rest) = line.strip_prefix("VmHWM:") {
            hwm_kib = parse_proc_status_kib(rest);
        }

        if rss_kib.is_some() && hwm_kib.is_some() {
            break;
        }
    }

    Some(MemSnapshot {
        rss_kib: rss_kib?,
        hwm_kib: hwm_kib?,
    })
}

fn parse_proc_status_kib(rest: &str) -> Option<u64> {
    rest.split_whitespace().next()?.parse().ok()
}
