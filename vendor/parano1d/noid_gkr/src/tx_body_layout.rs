// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical 31-permutation flattened Tx8x2 body topology.

pub const TXBODY_N_TREE_LEAVES: usize = noid_tx::body_hash::BODY_HASH_LEAVES;
pub const TXBODY_TREE_DEPTH: usize = 4;
pub const PERMS_PER_COMPRESS: usize = 2;
pub const PERMS_PER_WRAP: usize = 1;
pub const N_SPINE_SLOTS: usize = (TXBODY_N_TREE_LEAVES - 1) * PERMS_PER_COMPRESS + PERMS_PER_WRAP;
pub const N_SPINE_SLOTS_PADDED: usize = N_SPINE_SLOTS.next_power_of_two();

const _: () = assert!(N_SPINE_SLOTS == 31);
const _: () = assert!(N_SPINE_SLOTS_PADDED == 32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstanceRole {
    CompressPermA { level: u8, pos: u8 },
    CompressPermB { level: u8, pos: u8 },
    WrapPerm,
}

impl InstanceRole {
    pub const fn is_head(self) -> bool {
        matches!(self, Self::CompressPermA { .. } | Self::WrapPerm)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InstanceMeta {
    pub role: InstanceRole,
    pub is_head: bool,
    /// `None` denotes a raw external leaf and is legal only at level one.
    pub children: Option<[Option<usize>; 2]>,
}

pub fn build_instance_layout() -> Vec<InstanceMeta> {
    let mut out = Vec::with_capacity(N_SPINE_SLOTS);
    let mut previous_level = vec![None; TXBODY_N_TREE_LEAVES];

    for level in 1..=TXBODY_TREE_DEPTH {
        let node_count = 1 << (TXBODY_TREE_DEPTH - level);
        let mut this_level = Vec::with_capacity(node_count);
        for pos in 0..node_count {
            let children = [previous_level[2 * pos], previous_level[2 * pos + 1]];
            out.push(meta_with_children(
                InstanceRole::CompressPermA {
                    level: level as u8,
                    pos: pos as u8,
                },
                children,
            ));
            let perm_b = out.len();
            out.push(meta_with_children(
                InstanceRole::CompressPermB {
                    level: level as u8,
                    pos: pos as u8,
                },
                children,
            ));
            this_level.push(Some(perm_b));
        }
        previous_level = this_level;
    }

    out.push(meta_with_children(
        InstanceRole::WrapPerm,
        [previous_level[0], None],
    ));

    debug_assert_eq!(out.len(), N_SPINE_SLOTS);
    out
}

#[inline]
fn meta_with_children(role: InstanceRole, children: [Option<usize>; 2]) -> InstanceMeta {
    InstanceMeta {
        role,
        is_head: role.is_head(),
        children: Some(children),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_topology_is_thirty_compressions_plus_wrap() {
        let layout = build_instance_layout();
        assert_eq!(N_SPINE_SLOTS, 31);
        assert_eq!(N_SPINE_SLOTS_PADDED, 32);
        assert_eq!(layout.len(), 31);
        assert_eq!(
            layout
                .iter()
                .filter(|meta| matches!(meta.role, InstanceRole::CompressPermA { .. }))
                .count(),
            15
        );
        assert_eq!(
            layout
                .iter()
                .filter(|meta| matches!(meta.role, InstanceRole::CompressPermB { .. }))
                .count(),
            15
        );
        assert!(matches!(layout[30].role, InstanceRole::WrapPerm));
    }

    #[test]
    fn level_slot_ranges_and_postorder_are_exact() {
        for (level, positions, base) in [(1, 8, 0), (2, 4, 16), (3, 2, 24), (4, 1, 28)] {
            for pos in 0..positions {
                assert!(matches!(
                    build_instance_layout()[base + 2 * pos].role,
                    InstanceRole::CompressPermA { level: l, pos: p }
                        if usize::from(l) == level && usize::from(p) == pos
                ));
                assert!(matches!(
                    build_instance_layout()[base + 2 * pos + 1].role,
                    InstanceRole::CompressPermB { level: l, pos: p }
                        if usize::from(l) == level && usize::from(p) == pos
                ));
            }
        }
        let layout = build_instance_layout();
        for (parent, meta) in layout.iter().enumerate() {
            if let Some(children) = meta.children {
                for child in children.into_iter().flatten() {
                    assert!(child < parent);
                }
            }
        }
        assert_eq!(layout[30].children, Some([Some(29), None]));
    }

    #[test]
    fn level_one_children_are_the_sixteen_raw_leaves() {
        let layout = build_instance_layout();
        for meta in &layout[..16] {
            assert_eq!(meta.children, Some([None, None]));
        }
    }
}
