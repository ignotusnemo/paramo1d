// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical exact sparse Merkle multiproofs.
//!
//! The proof contains only missing frontier hashes. Indices, directions and
//! topology are verifier-derived from the canonical touched set.

use std::collections::{BTreeMap, BTreeSet};

use crate::exact_state_hash::{state_node_hash, zero_slot_roots, StateHash};

/// Canonical Merkle multiproof with implicit topology.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CanonicalMerkleMultiProof {
    pub siblings: Vec<StateHash>,
}

/// Verifier-derived coordinate of one missing structural-frontier node.
///
/// `level = 0` addresses a leaf sibling and `node_index` is the node's index
/// within that level.  Coordinates are never supplied by the proof witness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FrontierSiblingPosition {
    pub level: u8,
    pub node_index: u64,
}

/// Reference to one value in a verifier-derived structural-frontier plan.
///
/// The numeric payload is an ordinal in the corresponding verifier-owned
/// vector.  It is not a witness-supplied tree coordinate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StructuralNodeRef {
    TouchedLeaf(usize),
    FrontierSibling(usize),
    Combine(usize),
}

/// One binary hash operation in a verifier-derived structural-frontier plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructuralCombine {
    pub left: StructuralNodeRef,
    pub right: StructuralNodeRef,
}

/// Hash-independent structural-frontier topology for one touched set.
///
/// This value is derived locally from the sorted touched indices and tree
/// depth.  It is deliberately not serializable: a proof carries only the live
/// sibling digests, never node coordinates or topology.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuralFrontierPlan {
    touched_leaf_count: usize,
    frontier_positions: Vec<FrontierSiblingPosition>,
    combines: Vec<StructuralCombine>,
    root: StructuralNodeRef,
}

impl StructuralFrontierPlan {
    #[inline]
    pub fn touched_leaf_count(&self) -> usize {
        self.touched_leaf_count
    }

    #[inline]
    pub fn frontier_positions(&self) -> &[FrontierSiblingPosition] {
        &self.frontier_positions
    }

    #[inline]
    pub fn combines(&self) -> &[StructuralCombine] {
        &self.combines
    }

    #[inline]
    pub fn root_ref(&self) -> StructuralNodeRef {
        self.root
    }
}

/// Hashes materialized by evaluating a [`StructuralFrontierPlan`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuralFrontierEvaluation {
    pub root: StateHash,
    /// Parent hashes in the same order as [`StructuralFrontierPlan::combines`].
    pub combines: Vec<StateHash>,
}

/// Fixed value occupying every unused row after a class's live frontier.
pub const STRUCTURAL_FRONTIER_PAD: StateHash = [0u8; 32];

/// One directed full path derived from a canonical multiproof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpandedMerklePath {
    pub index: u32,
    pub leaf: StateHash,
    pub siblings: Vec<StateHash>,
    /// `false`: current node is left child. `true`: current node is right child.
    pub directions: Vec<bool>,
}

/// One collision-binding update step derived from a canonical multiproof.
///
/// The same `siblings` authenticate `old_leaf` against `root_before` and
/// `new_leaf` against `root_after`.  Chaining these steps in sorted touched
/// order proves that no slot outside `indices` changed, without carrying two
/// independent full-path families in the proof payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SequentialMerkleUpdatePath {
    pub index: u32,
    pub old_leaf: StateHash,
    pub new_leaf: StateHash,
    pub siblings: Vec<StateHash>,
    pub directions: Vec<bool>,
    pub root_before: StateHash,
    pub root_after: StateHash,
}

/// Two-level projection of a canonical update frontier at a fixed segment
/// boundary.
///
/// `local_updates` contains one update per touched slot, truncated at
/// `local_depth`. `segment_updates` contains one update per distinct segment
/// and chains those segment roots through the remaining `upper_depth` levels.
/// Both vectors are sorted and use shared-before/after sibling paths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SegmentedSequentialMerkleUpdates {
    pub local_depth: u32,
    pub upper_depth: u32,
    pub local_updates: Vec<SequentialMerkleUpdatePath>,
    pub segment_updates: Vec<SequentialMerkleUpdatePath>,
}

/// Sparse non-default node cache for exact-state proofs.
#[derive(Debug, Clone)]
pub struct SparseMerkleCache {
    depth: u32,
    zero_roots: Vec<StateHash>,
    nodes: BTreeMap<(u32, u64), StateHash>,
}

/// Errors returned by sparse Merkle proof helpers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SparseMerkleError {
    InvalidDepth {
        depth: u32,
    },
    EmptyIndices,
    LeafCountMismatch {
        indices: usize,
        leaves: usize,
    },
    UnsortedIndices,
    DuplicateIndex {
        index: u32,
    },
    IndexOutOfRange {
        index: u32,
        depth: u32,
    },
    ProofLengthMismatch {
        expected: usize,
        actual: usize,
    },
    FrontierCapacityExceeded {
        required: usize,
        capacity: usize,
    },
    PaddedProofLengthMismatch {
        expected: usize,
        actual: usize,
    },
    NonCanonicalPadding {
        index: usize,
    },
    CacheDepthMismatch {
        cache_depth: u32,
        requested_depth: u32,
    },
}

impl core::fmt::Display for SparseMerkleError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidDepth { depth } => write!(f, "invalid sparse Merkle depth {depth}"),
            Self::EmptyIndices => write!(f, "sparse Merkle proof requires at least one index"),
            Self::LeafCountMismatch { indices, leaves } => {
                write!(
                    f,
                    "leaf count {leaves} does not match index count {indices}"
                )
            }
            Self::UnsortedIndices => write!(f, "indices must be strictly sorted"),
            Self::DuplicateIndex { index } => write!(f, "duplicate index {index}"),
            Self::IndexOutOfRange { index, depth } => {
                write!(f, "index {index} is out of range for depth {depth}")
            }
            Self::ProofLengthMismatch { expected, actual } => {
                write!(f, "proof has {actual} siblings, expected {expected}")
            }
            Self::FrontierCapacityExceeded { required, capacity } => write!(
                f,
                "frontier requires {required} siblings, class capacity is {capacity}"
            ),
            Self::PaddedProofLengthMismatch { expected, actual } => write!(
                f,
                "padded frontier has {actual} rows, expected class capacity {expected}"
            ),
            Self::NonCanonicalPadding { index } => {
                write!(f, "frontier padding row {index} is not canonical PAD")
            }
            Self::CacheDepthMismatch {
                cache_depth,
                requested_depth,
            } => write!(
                f,
                "cache depth {cache_depth} does not match requested depth {requested_depth}"
            ),
        }
    }
}

impl std::error::Error for SparseMerkleError {}

impl SparseMerkleCache {
    /// Create an empty exact sparse Merkle cache at `depth`.
    pub fn new(depth: u32) -> Result<Self, SparseMerkleError> {
        validate_depth(depth)?;
        Ok(Self {
            depth,
            zero_roots: zero_slot_roots(depth as usize),
            nodes: BTreeMap::new(),
        })
    }

    /// Create a cache and apply leaf updates.
    pub fn from_leaves(depth: u32, leaves: &[(u32, StateHash)]) -> Result<Self, SparseMerkleError> {
        let mut cache = Self::new(depth)?;
        for &(index, leaf) in leaves {
            cache.set_leaf(index, leaf)?;
        }
        Ok(cache)
    }

    #[inline]
    pub fn depth(&self) -> u32 {
        self.depth
    }

    /// Return the exact Merkle root represented by this cache.
    pub fn root(&self) -> StateHash {
        self.node_hash(self.depth, 0)
    }

    /// Read one cached node or the canonical zero node for its level.
    pub fn node_hash(&self, level: u32, index: u64) -> StateHash {
        self.nodes
            .get(&(level, index))
            .copied()
            .unwrap_or_else(|| self.zero_roots[level as usize])
    }

    /// Set one leaf and update only its ancestor path.
    pub fn set_leaf(&mut self, index: u32, leaf: StateHash) -> Result<(), SparseMerkleError> {
        validate_index(index, self.depth)?;
        let mut idx = index as u64;
        let mut hash = leaf;
        self.set_node(0, idx, hash);
        for level in 0..self.depth {
            let sibling_idx = idx ^ 1;
            let base = idx & !1;
            let (left, right) = if idx == base {
                (hash, self.node_hash(level, sibling_idx))
            } else {
                (self.node_hash(level, sibling_idx), hash)
            };
            hash = state_node_hash(left, right);
            idx = base / 2;
            self.set_node(level + 1, idx, hash);
        }
        Ok(())
    }

    fn set_node(&mut self, level: u32, index: u64, hash: StateHash) {
        if hash == self.zero_roots[level as usize] {
            self.nodes.remove(&(level, index));
        } else {
            self.nodes.insert((level, index), hash);
        }
    }
}

/// Maximum number of canonical frontier siblings for `touched` leaves in a
/// binary tree of `depth`.
///
/// The maximum is attained by spreading leaves as evenly as possible across
/// the tree.  If `c = ceil(log2(touched))`, the first `depth - c` levels can
/// keep every touched node separate; the remaining complete top tree accounts
/// for the final `2^c - touched` siblings.
///
/// # Panics
///
/// Panics when `depth > 32` or `touched` exceeds the tree domain.
pub const fn maximum_sibling_count(touched: usize, depth: u32) -> usize {
    assert!(depth <= 32);
    if touched == 0 {
        return 0;
    }
    assert!((touched as u64) <= (1u64 << depth));

    let touched_u64 = touched as u64;
    let mut covering_power = 1u64;
    let mut covering_depth = 0u32;
    while covering_power < touched_u64 {
        covering_power <<= 1;
        covering_depth += 1;
    }
    let maximum = (depth - covering_depth) as u64 * touched_u64 + covering_power - touched_u64;
    assert!(maximum <= usize::MAX as u64);
    maximum as usize
}

/// Maximum canonical frontier size when touched leaves may occupy at most
/// `max_segments` subtrees of depth `log_segment_size`.
///
/// For a fixed number of used segments, the local maximum is attained by a
/// balanced distribution of touched leaves because [`maximum_sibling_count`]
/// is concave between successive powers of two.  The function checks every
/// legal used-segment count and adds the upper segment-tree frontier.  This is
/// the analytical capacity used by the exact-state proof instead of the loose
/// `touched * depth` bound.
///
/// # Panics
///
/// Panics for an invalid geometry or when the capped segments cannot contain
/// `touched` leaves.
pub const fn maximum_sibling_count_with_segment_cap(
    touched: usize,
    depth: u32,
    log_segment_size: u32,
    max_segments: usize,
) -> usize {
    assert!(depth <= 32);
    assert!(log_segment_size <= depth);
    if touched == 0 {
        return 0;
    }
    assert!(max_segments > 0);

    let segment_capacity = 1u64 << log_segment_size;
    let segment_tree_depth = depth - log_segment_size;
    let domain_segments = 1u64 << segment_tree_depth;
    let capped_segments = if (max_segments as u64) < domain_segments {
        max_segments as u64
    } else {
        domain_segments
    };
    assert!((touched as u64) <= segment_capacity * capped_segments);

    let mut used_segments = 1usize;
    let max_used_segments = if touched < capped_segments as usize {
        touched
    } else {
        capped_segments as usize
    };
    let mut maximum = 0usize;
    while used_segments <= max_used_segments {
        let quotient = touched / used_segments;
        let remainder = touched % used_segments;
        if quotient as u64 <= segment_capacity
            && (remainder == 0 || (quotient + 1) as u64 <= segment_capacity)
        {
            let smaller_segments = used_segments - remainder;
            let local = smaller_segments * maximum_sibling_count(quotient, log_segment_size)
                + if remainder == 0 {
                    0
                } else {
                    remainder * maximum_sibling_count(quotient + 1, log_segment_size)
                };
            let upper = maximum_sibling_count(used_segments, segment_tree_depth);
            let total = local + upper;
            if total > maximum {
                maximum = total;
            }
        }
        used_segments += 1;
    }
    maximum
}

/// Return the exact number of sibling hashes needed for sorted `indices`.
pub fn expected_sibling_count(indices: &[u32], depth: u32) -> Result<usize, SparseMerkleError> {
    let mut known = validate_indices(indices, depth)?;
    let mut count = 0usize;
    for _level in 0..depth {
        let mut next = BTreeSet::new();
        let mut processed = BTreeSet::new();
        for &pos in &known {
            let base = pos & !1;
            if !processed.insert(base) {
                continue;
            }
            let left_known = known.contains(&base);
            let right_known = known.contains(&(base + 1));
            if left_known ^ right_known {
                count += 1;
            }
            next.insert(base / 2);
        }
        known = next;
    }
    Ok(count)
}

/// Derive the canonical missing-frontier coordinates for sorted touched slots.
///
/// The traversal order is level-major and, within each level, increasing
/// parent position.  [`build_multiproof`] and [`reconstruct_root`] consume
/// sibling digests in exactly this order.
pub fn frontier_sibling_positions(
    indices: &[u32],
    depth: u32,
) -> Result<Vec<FrontierSiblingPosition>, SparseMerkleError> {
    let mut known = validate_indices(indices, depth)?;
    let mut positions = Vec::new();
    for level in 0..depth {
        let mut next = BTreeSet::new();
        let mut processed = BTreeSet::new();
        for &pos in &known {
            let base = pos & !1;
            if !processed.insert(base) {
                continue;
            }
            let left_known = known.contains(&base);
            let right_known = known.contains(&(base + 1));
            match (left_known, right_known) {
                (true, false) => positions.push(FrontierSiblingPosition {
                    level: level as u8,
                    node_index: base + 1,
                }),
                (false, true) => positions.push(FrontierSiblingPosition {
                    level: level as u8,
                    node_index: base,
                }),
                (true, true) => {}
                (false, false) => unreachable!("processed parent must have one known child"),
            }
            next.insert(base / 2);
        }
        known = next;
    }
    Ok(positions)
}

/// Derive the complete structural-frontier hash plan for sorted touched slots.
///
/// Leaves are referenced by their ordinal in `indices`; frontier siblings are
/// referenced in the same canonical order as [`frontier_sibling_positions`].
/// Every combine references only leaves, frontier siblings, or an earlier
/// combine.  The returned root reference therefore fully describes the
/// verifier-owned topology without placing coordinates in the proof witness.
pub fn derive_structural_frontier_plan(
    indices: &[u32],
    depth: u32,
) -> Result<StructuralFrontierPlan, SparseMerkleError> {
    validate_indices(indices, depth)?;

    let mut known: BTreeMap<u64, StructuralNodeRef> = indices
        .iter()
        .enumerate()
        .map(|(ordinal, &index)| (index as u64, StructuralNodeRef::TouchedLeaf(ordinal)))
        .collect();
    let mut frontier_positions = Vec::new();
    let mut combines = Vec::new();

    for level in 0..depth {
        let mut next = BTreeMap::new();
        let mut processed = BTreeSet::new();
        for &pos in known.keys() {
            let base = pos & !1;
            if !processed.insert(base) {
                continue;
            }

            let left = known.get(&base).copied();
            let right = known.get(&(base + 1)).copied();
            let (left, right) = match (left, right) {
                (Some(left), Some(right)) => (left, right),
                (Some(left), None) => {
                    let sibling = StructuralNodeRef::FrontierSibling(frontier_positions.len());
                    frontier_positions.push(FrontierSiblingPosition {
                        level: level as u8,
                        node_index: base + 1,
                    });
                    (left, sibling)
                }
                (None, Some(right)) => {
                    let sibling = StructuralNodeRef::FrontierSibling(frontier_positions.len());
                    frontier_positions.push(FrontierSiblingPosition {
                        level: level as u8,
                        node_index: base,
                    });
                    (sibling, right)
                }
                (None, None) => unreachable!("processed parent must have one known child"),
            };

            let combine = StructuralNodeRef::Combine(combines.len());
            combines.push(StructuralCombine { left, right });
            next.insert(base / 2, combine);
        }
        known = next;
    }

    let root = match known.into_iter().next() {
        Some((0, root)) => root,
        _ => return Err(SparseMerkleError::InvalidDepth { depth }),
    };
    debug_assert_eq!(combines.len(), indices.len() + frontier_positions.len() - 1);

    Ok(StructuralFrontierPlan {
        touched_leaf_count: indices.len(),
        frontier_positions,
        combines,
        root,
    })
}

/// Evaluate a verifier-derived structural-frontier plan.
///
/// `siblings` is the exact live frontier, not a padded class-width vector.  Its
/// length is topology-derived, so an all-zero digest is accepted as ordinary
/// live data and cannot be confused with an unused PAD row.
pub fn evaluate_structural_frontier(
    plan: &StructuralFrontierPlan,
    leaves: &[StateHash],
    siblings: &[StateHash],
) -> Result<StructuralFrontierEvaluation, SparseMerkleError> {
    if leaves.len() != plan.touched_leaf_count {
        return Err(SparseMerkleError::LeafCountMismatch {
            indices: plan.touched_leaf_count,
            leaves: leaves.len(),
        });
    }
    if siblings.len() != plan.frontier_positions.len() {
        return Err(SparseMerkleError::ProofLengthMismatch {
            expected: plan.frontier_positions.len(),
            actual: siblings.len(),
        });
    }

    let mut combine_hashes = Vec::with_capacity(plan.combines.len());
    for combine in &plan.combines {
        let left = structural_node_hash(combine.left, leaves, siblings, &combine_hashes);
        let right = structural_node_hash(combine.right, leaves, siblings, &combine_hashes);
        combine_hashes.push(state_node_hash(left, right));
    }
    let root = structural_node_hash(plan.root, leaves, siblings, &combine_hashes);

    Ok(StructuralFrontierEvaluation {
        root,
        combines: combine_hashes,
    })
}

fn structural_node_hash(
    node: StructuralNodeRef,
    leaves: &[StateHash],
    siblings: &[StateHash],
    combines: &[StateHash],
) -> StateHash {
    match node {
        StructuralNodeRef::TouchedLeaf(ordinal) => leaves[ordinal],
        StructuralNodeRef::FrontierSibling(ordinal) => siblings[ordinal],
        StructuralNodeRef::Combine(ordinal) => combines[ordinal],
    }
}

/// Pad a live canonical frontier to a proof-class capacity.
pub fn pad_frontier_siblings(
    indices: &[u32],
    siblings: &[StateHash],
    depth: u32,
    capacity: usize,
) -> Result<Vec<StateHash>, SparseMerkleError> {
    let required = expected_sibling_count(indices, depth)?;
    if siblings.len() != required {
        return Err(SparseMerkleError::ProofLengthMismatch {
            expected: required,
            actual: siblings.len(),
        });
    }
    if required > capacity {
        return Err(SparseMerkleError::FrontierCapacityExceeded { required, capacity });
    }
    let mut padded = Vec::with_capacity(capacity);
    padded.extend_from_slice(siblings);
    padded.resize(capacity, STRUCTURAL_FRONTIER_PAD);
    Ok(padded)
}

/// Validate class-width frontier rows and return their derived live prefix.
pub fn unpad_frontier_siblings<'a>(
    indices: &[u32],
    padded: &'a [StateHash],
    depth: u32,
    capacity: usize,
) -> Result<&'a [StateHash], SparseMerkleError> {
    if padded.len() != capacity {
        return Err(SparseMerkleError::PaddedProofLengthMismatch {
            expected: capacity,
            actual: padded.len(),
        });
    }
    let required = expected_sibling_count(indices, depth)?;
    if required > capacity {
        return Err(SparseMerkleError::FrontierCapacityExceeded { required, capacity });
    }
    if let Some((offset, _)) = padded[required..]
        .iter()
        .enumerate()
        .find(|(_, digest)| **digest != STRUCTURAL_FRONTIER_PAD)
    {
        return Err(SparseMerkleError::NonCanonicalPadding {
            index: required + offset,
        });
    }
    Ok(&padded[..required])
}

/// Reconstruct the Merkle root for sorted `indices` and index-aligned `leaves`.
pub fn reconstruct_root(
    indices: &[u32],
    leaves: &[StateHash],
    siblings: &[StateHash],
    depth: u32,
) -> Result<StateHash, SparseMerkleError> {
    if indices.len() != leaves.len() {
        return Err(SparseMerkleError::LeafCountMismatch {
            indices: indices.len(),
            leaves: leaves.len(),
        });
    }
    let expected = expected_sibling_count(indices, depth)?;
    if siblings.len() != expected {
        return Err(SparseMerkleError::ProofLengthMismatch {
            expected,
            actual: siblings.len(),
        });
    }

    let mut known: BTreeMap<u64, StateHash> = indices
        .iter()
        .copied()
        .zip(leaves.iter().copied())
        .map(|(index, leaf)| (index as u64, leaf))
        .collect();
    let mut cursor = 0usize;

    for _level in 0..depth {
        let mut next = BTreeMap::new();
        let mut processed = BTreeSet::new();
        for &pos in known.keys() {
            let base = pos & !1;
            if !processed.insert(base) {
                continue;
            }
            let left = known.get(&base).copied();
            let right = known.get(&(base + 1)).copied();
            let parent = match (left, right) {
                (Some(left), Some(right)) => state_node_hash(left, right),
                (Some(left), None) => {
                    let right = siblings[cursor];
                    cursor += 1;
                    state_node_hash(left, right)
                }
                (None, Some(right)) => {
                    let left = siblings[cursor];
                    cursor += 1;
                    state_node_hash(left, right)
                }
                (None, None) => unreachable!("processed parent must have one known child"),
            };
            next.insert(base / 2, parent);
        }
        known = next;
    }

    debug_assert_eq!(cursor, siblings.len());
    match known.into_iter().next() {
        Some((0, root)) => Ok(root),
        _ => Err(SparseMerkleError::InvalidDepth { depth }),
    }
}

/// Expand a canonical implicit multiproof into one directed full path per leaf.
///
/// This is a deterministic verifier-side projection of the same proof consumed
/// by [`reconstruct_root`]. Sibling hashes may come either from the explicit
/// proof vector or from another known touched subtree.
pub fn expand_multiproof_paths(
    indices: &[u32],
    leaves: &[StateHash],
    siblings: &[StateHash],
    depth: u32,
) -> Result<Vec<ExpandedMerklePath>, SparseMerkleError> {
    if indices.len() != leaves.len() {
        return Err(SparseMerkleError::LeafCountMismatch {
            indices: indices.len(),
            leaves: leaves.len(),
        });
    }
    let expected = expected_sibling_count(indices, depth)?;
    if siblings.len() != expected {
        return Err(SparseMerkleError::ProofLengthMismatch {
            expected,
            actual: siblings.len(),
        });
    }

    #[derive(Clone)]
    struct Node {
        hash: StateHash,
        leaves: Vec<usize>,
    }

    let path_depth = depth as usize;
    let mut out: Vec<ExpandedMerklePath> = indices
        .iter()
        .copied()
        .zip(leaves.iter().copied())
        .map(|(index, leaf)| ExpandedMerklePath {
            index,
            leaf,
            siblings: vec![[0u8; 32]; path_depth],
            directions: vec![false; path_depth],
        })
        .collect();
    let mut known: BTreeMap<u64, Node> = indices
        .iter()
        .copied()
        .zip(leaves.iter().copied())
        .enumerate()
        .map(|(leaf_pos, (index, leaf))| {
            (
                index as u64,
                Node {
                    hash: leaf,
                    leaves: vec![leaf_pos],
                },
            )
        })
        .collect();
    let mut cursor = 0usize;

    for level in 0..depth {
        let mut next = BTreeMap::new();
        let mut processed = BTreeSet::new();
        for &pos in known.keys() {
            let base = pos & !1;
            if !processed.insert(base) {
                continue;
            }
            let left = known.get(&base).cloned();
            let right = known.get(&(base + 1)).cloned();
            let (left, right) = match (left, right) {
                (Some(left), Some(right)) => (left, right),
                (Some(left), None) => {
                    let right = Node {
                        hash: siblings[cursor],
                        leaves: Vec::new(),
                    };
                    cursor += 1;
                    (left, right)
                }
                (None, Some(right)) => {
                    let left = Node {
                        hash: siblings[cursor],
                        leaves: Vec::new(),
                    };
                    cursor += 1;
                    (left, right)
                }
                (None, None) => unreachable!("processed parent must have one known child"),
            };

            for &leaf_pos in &left.leaves {
                out[leaf_pos].siblings[level as usize] = right.hash;
                out[leaf_pos].directions[level as usize] = false;
            }
            for &leaf_pos in &right.leaves {
                out[leaf_pos].siblings[level as usize] = left.hash;
                out[leaf_pos].directions[level as usize] = true;
            }

            let mut parent_leaves = left.leaves;
            parent_leaves.extend(right.leaves);
            next.insert(
                base / 2,
                Node {
                    hash: state_node_hash(left.hash, right.hash),
                    leaves: parent_leaves,
                },
            );
        }
        known = next;
    }

    debug_assert_eq!(cursor, siblings.len());
    Ok(out)
}

/// Derive a sorted sequence of collision-binding Merkle updates from one
/// canonical sibling frontier.
///
/// The proof payload remains the canonical `siblings` vector.  This helper is
/// only a verifier/prover-side projection used by fixed-shape recursive
/// traces: step `i` authenticates the current value at `indices[i]`, replaces
/// it, and hands its resulting root to step `i + 1`.  Consequently every
/// sibling is read from the tree state produced by the preceding steps rather
/// than from an independently supplied full path.
pub fn expand_multiproof_sequential_updates(
    indices: &[u32],
    old_leaves: &[StateHash],
    new_leaves: &[StateHash],
    siblings: &[StateHash],
    depth: u32,
) -> Result<Vec<SequentialMerkleUpdatePath>, SparseMerkleError> {
    if indices.len() != old_leaves.len() {
        return Err(SparseMerkleError::LeafCountMismatch {
            indices: indices.len(),
            leaves: old_leaves.len(),
        });
    }
    if indices.len() != new_leaves.len() {
        return Err(SparseMerkleError::LeafCountMismatch {
            indices: indices.len(),
            leaves: new_leaves.len(),
        });
    }

    let frontier_positions = frontier_sibling_positions(indices, depth)?;
    if siblings.len() != frontier_positions.len() {
        return Err(SparseMerkleError::ProofLengthMismatch {
            expected: frontier_positions.len(),
            actual: siblings.len(),
        });
    }

    // Materialize exactly the verifier-owned partial tree: touched leaves,
    // missing frontier nodes, and every ancestor on their union of paths.
    // Coordinates are local derivations, never proof witness data.
    let mut nodes: BTreeMap<(u32, u64), StateHash> = indices
        .iter()
        .copied()
        .zip(old_leaves.iter().copied())
        .map(|(index, leaf)| ((0, index as u64), leaf))
        .collect();
    for (position, sibling) in frontier_positions.iter().zip(siblings.iter().copied()) {
        let previous = nodes.insert((u32::from(position.level), position.node_index), sibling);
        debug_assert!(previous.is_none(), "frontier cannot overlap a known node");
    }

    let mut current: BTreeMap<u64, StateHash> = indices
        .iter()
        .copied()
        .zip(old_leaves.iter().copied())
        .map(|(index, leaf)| (index as u64, leaf))
        .collect();
    for level in 0..depth {
        let mut next = BTreeMap::new();
        let mut processed = BTreeSet::new();
        for &position in current.keys() {
            let base = position & !1;
            if !processed.insert(base) {
                continue;
            }
            let left = *nodes
                .get(&(level, base))
                .expect("canonical frontier supplies the left child");
            let right = *nodes
                .get(&(level, base + 1))
                .expect("canonical frontier supplies the right child");
            let parent = state_node_hash(left, right);
            next.insert(base / 2, parent);
            nodes.insert((level + 1, base / 2), parent);
        }
        current = next;
    }
    let mut rolling_root = *nodes
        .get(&(depth, 0))
        .expect("validated non-empty touched set has one root");

    let mut out = Vec::with_capacity(indices.len());
    for ((&index, &old_leaf), &new_leaf) in
        indices.iter().zip(old_leaves.iter()).zip(new_leaves.iter())
    {
        debug_assert_eq!(
            nodes.get(&(0, index as u64)),
            Some(&old_leaf),
            "a sorted unique slot is updated exactly once"
        );
        let root_before = rolling_root;
        let mut current_hash = new_leaf;
        let mut path_siblings = Vec::with_capacity(depth as usize);
        let mut directions = Vec::with_capacity(depth as usize);
        nodes.insert((0, index as u64), new_leaf);
        for level in 0..depth {
            let position = (index as u64) >> level;
            let sibling = *nodes
                .get(&(level, position ^ 1))
                .expect("partial tree contains every update sibling");
            let is_right = position & 1 == 1;
            path_siblings.push(sibling);
            directions.push(is_right);
            current_hash = if is_right {
                state_node_hash(sibling, current_hash)
            } else {
                state_node_hash(current_hash, sibling)
            };
            nodes.insert((level + 1, position / 2), current_hash);
        }
        rolling_root = current_hash;
        out.push(SequentialMerkleUpdatePath {
            index,
            old_leaf,
            new_leaf,
            siblings: path_siblings,
            directions,
            root_before,
            root_after: rolling_root,
        });
    }

    let simultaneous_new_root = reconstruct_root(indices, new_leaves, siblings, depth)?;
    debug_assert_eq!(
        rolling_root, simultaneous_new_root,
        "sequential and canonical simultaneous updates are equivalent"
    );
    Ok(out)
}

/// Split [`expand_multiproof_sequential_updates`] at `log_segment_size`.
///
/// This preserves the exact old/new roots while reducing the recursive hash
/// schedule from one full-depth update per touched slot to one bounded local
/// update per slot plus one upper update per distinct segment.  No segment
/// roots or paths are added to the proof wire format; they are deterministically
/// reconstructed from the canonical sibling frontier.
pub fn expand_multiproof_segmented_updates(
    indices: &[u32],
    old_leaves: &[StateHash],
    new_leaves: &[StateHash],
    siblings: &[StateHash],
    depth: u32,
    log_segment_size: u32,
) -> Result<SegmentedSequentialMerkleUpdates, SparseMerkleError> {
    let full =
        expand_multiproof_sequential_updates(indices, old_leaves, new_leaves, siblings, depth)?;
    let local_depth = depth.min(log_segment_size);
    let upper_depth = depth - local_depth;
    let local_len = local_depth as usize;

    let mut local_updates = Vec::with_capacity(full.len());
    for step in &full {
        let siblings = step.siblings[..local_len].to_vec();
        let directions = step.directions[..local_len].to_vec();
        let root_before = fold_directed_path(step.old_leaf, &siblings, &directions);
        let root_after = fold_directed_path(step.new_leaf, &siblings, &directions);
        local_updates.push(SequentialMerkleUpdatePath {
            index: step.index,
            old_leaf: step.old_leaf,
            new_leaf: step.new_leaf,
            siblings,
            directions,
            root_before,
            root_after,
        });
    }

    let segment_of = |index: u32| {
        if local_depth == 32 {
            0
        } else {
            index >> local_depth
        }
    };
    let mut segment_updates = Vec::new();
    let mut start = 0usize;
    while start < full.len() {
        let segment = segment_of(full[start].index);
        let mut end = start + 1;
        while end < full.len() && segment_of(full[end].index) == segment {
            end += 1;
        }

        for pair in local_updates[start..end].windows(2) {
            debug_assert_eq!(
                pair[0].root_after, pair[1].root_before,
                "local updates in one segment must chain"
            );
        }
        let first_full = &full[start];
        let last_full = &full[end - 1];
        let old_segment_root = local_updates[start].root_before;
        let new_segment_root = local_updates[end - 1].root_after;
        let upper_siblings = first_full.siblings[local_len..].to_vec();
        let upper_directions = first_full.directions[local_len..].to_vec();
        debug_assert_eq!(upper_siblings.len(), upper_depth as usize);
        debug_assert_eq!(
            fold_directed_path(old_segment_root, &upper_siblings, &upper_directions),
            first_full.root_before,
            "upper path must start at the pre-update global root"
        );
        debug_assert_eq!(
            fold_directed_path(new_segment_root, &upper_siblings, &upper_directions),
            last_full.root_after,
            "one segment update equals all of its local updates"
        );
        segment_updates.push(SequentialMerkleUpdatePath {
            index: segment,
            old_leaf: old_segment_root,
            new_leaf: new_segment_root,
            siblings: upper_siblings,
            directions: upper_directions,
            root_before: first_full.root_before,
            root_after: last_full.root_after,
        });
        start = end;
    }
    for pair in segment_updates.windows(2) {
        debug_assert_eq!(
            pair[0].root_after, pair[1].root_before,
            "sorted segment updates must chain globally"
        );
    }

    Ok(SegmentedSequentialMerkleUpdates {
        local_depth,
        upper_depth,
        local_updates,
        segment_updates,
    })
}

fn fold_directed_path(leaf: StateHash, siblings: &[StateHash], directions: &[bool]) -> StateHash {
    debug_assert_eq!(siblings.len(), directions.len());
    siblings
        .iter()
        .zip(directions)
        .fold(leaf, |current, (&sibling, &is_right)| {
            if is_right {
                state_node_hash(sibling, current)
            } else {
                state_node_hash(current, sibling)
            }
        })
}

/// Build a canonical multiproof from a sparse cache.
pub fn build_multiproof(
    cache: &SparseMerkleCache,
    indices: &[u32],
    depth: u32,
) -> Result<CanonicalMerkleMultiProof, SparseMerkleError> {
    if cache.depth != depth {
        return Err(SparseMerkleError::CacheDepthMismatch {
            cache_depth: cache.depth,
            requested_depth: depth,
        });
    }
    let positions = frontier_sibling_positions(indices, depth)?;
    let siblings = positions
        .iter()
        .map(|position| cache.node_hash(u32::from(position.level), position.node_index))
        .collect();
    Ok(CanonicalMerkleMultiProof { siblings })
}

fn validate_depth(depth: u32) -> Result<(), SparseMerkleError> {
    if depth > 32 {
        return Err(SparseMerkleError::InvalidDepth { depth });
    }
    Ok(())
}

fn validate_index(index: u32, depth: u32) -> Result<(), SparseMerkleError> {
    validate_depth(depth)?;
    let limit = 1u64 << depth;
    if (index as u64) >= limit {
        return Err(SparseMerkleError::IndexOutOfRange { index, depth });
    }
    Ok(())
}

fn validate_indices(indices: &[u32], depth: u32) -> Result<BTreeSet<u64>, SparseMerkleError> {
    validate_depth(depth)?;
    if indices.is_empty() {
        return Err(SparseMerkleError::EmptyIndices);
    }
    let mut prev = None;
    let mut out = BTreeSet::new();
    for &index in indices {
        validate_index(index, depth)?;
        if let Some(prev) = prev {
            if index < prev {
                return Err(SparseMerkleError::UnsortedIndices);
            }
            if index == prev {
                return Err(SparseMerkleError::DuplicateIndex { index });
            }
        }
        prev = Some(index);
        out.insert(index as u64);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact_state_hash::{slot_leaf_hash, zero_slot_roots};
    use crate::fri_state::SlotValue;
    use noid_core::Block128;

    fn leaf(seed: u128) -> StateHash {
        slot_leaf_hash(SlotValue {
            value: Block128::from(seed as u64),
            owner_hi: Block128::from(seed.wrapping_mul(17)),
            owner_lo: Block128::from(seed.wrapping_mul(29)),
        })
    }

    fn naive_root(depth: u32, leaves: &[(u32, StateHash)]) -> StateHash {
        let zero = zero_slot_roots(depth as usize)[0];
        let mut level = vec![zero; 1usize << depth];
        for &(idx, leaf) in leaves {
            level[idx as usize] = leaf;
        }
        for _ in 0..depth {
            level = level
                .chunks_exact(2)
                .map(|pair| state_node_hash(pair[0], pair[1]))
                .collect();
        }
        level[0]
    }

    #[test]
    fn cache_root_matches_naive_full_tree() {
        let leaves = [(0, leaf(1)), (3, leaf(2)), (11, leaf(3)), (15, leaf(4))];
        let cache = SparseMerkleCache::from_leaves(4, &leaves).unwrap();
        assert_eq!(cache.root(), naive_root(4, &leaves));
    }

    #[test]
    fn multiproof_roundtrips_old_and_new_roots_with_shared_siblings() {
        let old_leaves = [(0, leaf(1)), (3, leaf(2)), (11, leaf(3)), (15, leaf(4))];
        let cache = SparseMerkleCache::from_leaves(4, &old_leaves).unwrap();
        let indices = [0, 11, 15];
        let old_touched = [leaf(1), leaf(3), leaf(4)];
        let proof = build_multiproof(&cache, &indices, 4).unwrap();

        let old_root = reconstruct_root(&indices, &old_touched, &proof.siblings, 4).unwrap();
        assert_eq!(old_root, cache.root());

        let new_touched = [leaf(21), leaf(23), leaf(24)];
        let mut new_all = old_leaves;
        new_all[0] = (0, new_touched[0]);
        new_all[2] = (11, new_touched[1]);
        new_all[3] = (15, new_touched[2]);
        let new_root = reconstruct_root(&indices, &new_touched, &proof.siblings, 4).unwrap();
        assert_eq!(new_root, naive_root(4, &new_all));
    }

    #[test]
    fn canonical_frontier_derives_a_chained_update_sequence() {
        let old_all = [
            (0, leaf(1)),
            (1, leaf(2)),
            (7, leaf(3)),
            (11, leaf(4)),
            (15, leaf(5)),
        ];
        let cache = SparseMerkleCache::from_leaves(4, &old_all).unwrap();
        let indices = [0, 1, 11];
        let old_touched = [leaf(1), leaf(2), leaf(4)];
        let new_touched = [leaf(21), leaf(22), leaf(24)];
        let proof = build_multiproof(&cache, &indices, 4).unwrap();
        let steps = expand_multiproof_sequential_updates(
            &indices,
            &old_touched,
            &new_touched,
            &proof.siblings,
            4,
        )
        .unwrap();

        let path_root = |leaf: StateHash, step: &SequentialMerkleUpdatePath| {
            step.siblings.iter().zip(&step.directions).fold(
                leaf,
                |current, (&sibling, &is_right)| {
                    if is_right {
                        state_node_hash(sibling, current)
                    } else {
                        state_node_hash(current, sibling)
                    }
                },
            )
        };
        assert_eq!(steps[0].root_before, cache.root());
        for step in &steps {
            assert_eq!(path_root(step.old_leaf, step), step.root_before);
            assert_eq!(path_root(step.new_leaf, step), step.root_after);
        }
        for pair in steps.windows(2) {
            assert_eq!(pair[0].root_after, pair[1].root_before);
        }

        // Slot 0 was already updated when slot 1 is opened, so its new leaf
        // must be the latter step's level-zero sibling. This distinguishes a
        // genuine sequential projection from two independent old/new paths.
        assert_eq!(steps[1].siblings[0], new_touched[0]);

        let mut new_all = old_all;
        new_all[0].1 = new_touched[0];
        new_all[1].1 = new_touched[1];
        new_all[3].1 = new_touched[2];
        assert_eq!(steps.last().unwrap().root_after, naive_root(4, &new_all));
        assert_eq!(
            steps.last().unwrap().root_after,
            reconstruct_root(&indices, &new_touched, &proof.siblings, 4).unwrap()
        );
    }

    #[test]
    fn segmented_projection_chains_locals_then_distinct_segments() {
        let old_all = [
            (0, leaf(1)),
            (1, leaf(2)),
            (6, leaf(3)),
            (7, leaf(4)),
            (9, leaf(5)),
            (12, leaf(6)),
        ];
        let cache = SparseMerkleCache::from_leaves(4, &old_all).unwrap();
        let indices = [0, 1, 6, 7, 12];
        let old_touched = [leaf(1), leaf(2), leaf(3), leaf(4), leaf(6)];
        let new_touched = [leaf(21), leaf(22), leaf(23), leaf(24), leaf(26)];
        let proof = build_multiproof(&cache, &indices, 4).unwrap();
        let segmented = expand_multiproof_segmented_updates(
            &indices,
            &old_touched,
            &new_touched,
            &proof.siblings,
            4,
            2,
        )
        .unwrap();

        assert_eq!(segmented.local_depth, 2);
        assert_eq!(segmented.upper_depth, 2);
        assert_eq!(segmented.local_updates.len(), indices.len());
        assert_eq!(
            segmented
                .segment_updates
                .iter()
                .map(|step| step.index)
                .collect::<Vec<_>>(),
            [0, 1, 3]
        );
        for group in [0..2, 2..4] {
            let local = &segmented.local_updates[group];
            assert_eq!(local[0].root_after, local[1].root_before);
        }
        for pair in segmented.segment_updates.windows(2) {
            assert_eq!(pair[0].root_after, pair[1].root_before);
        }
        assert_eq!(segmented.segment_updates[0].root_before, cache.root());

        let mut new_all = old_all;
        new_all[0].1 = new_touched[0];
        new_all[1].1 = new_touched[1];
        new_all[2].1 = new_touched[2];
        new_all[3].1 = new_touched[3];
        new_all[5].1 = new_touched[4];
        assert_eq!(
            segmented.segment_updates.last().unwrap().root_after,
            naive_root(4, &new_all)
        );

        let segmented_hashes = 2
            * (segmented.local_updates.len() * segmented.local_depth as usize
                + segmented.segment_updates.len() * segmented.upper_depth as usize);
        let full_hashes = 2 * indices.len() * 4;
        assert!(segmented_hashes < full_hashes);
    }

    #[test]
    fn sequential_projection_rejects_noncanonical_shapes() {
        let indices = [1, 6];
        let old = [leaf(1), leaf(2)];
        let new = [leaf(11), leaf(12)];
        let cache = SparseMerkleCache::from_leaves(3, &[(1, old[0]), (6, old[1])]).unwrap();
        let proof = build_multiproof(&cache, &indices, 3).unwrap();

        assert_eq!(
            expand_multiproof_sequential_updates(&indices, &old[..1], &new, &proof.siblings, 3),
            Err(SparseMerkleError::LeafCountMismatch {
                indices: 2,
                leaves: 1,
            })
        );
        assert!(matches!(
            expand_multiproof_sequential_updates(&[6, 1], &old, &new, &proof.siblings, 3),
            Err(SparseMerkleError::UnsortedIndices)
        ));
        assert!(matches!(
            expand_multiproof_sequential_updates(
                &indices,
                &old,
                &new,
                &proof.siblings[..proof.siblings.len() - 1],
                3
            ),
            Err(SparseMerkleError::ProofLengthMismatch { .. })
        ));
    }

    #[test]
    fn sibling_count_deduplicates_neighboring_leaves() {
        assert_eq!(expected_sibling_count(&[0], 4).unwrap(), 4);
        assert_eq!(expected_sibling_count(&[0, 1], 4).unwrap(), 3);
        assert_eq!(expected_sibling_count(&[0, 1, 2, 3], 4).unwrap(), 2);
        assert_eq!(
            expected_sibling_count(&(0u32..16).collect::<Vec<_>>(), 4).unwrap(),
            0
        );
    }

    #[test]
    fn frontier_coordinates_are_verifier_derived_and_padding_is_canonical() {
        let indices = [2, 5, 14];
        let positions = frontier_sibling_positions(&indices, 4).unwrap();
        assert_eq!(
            positions.len(),
            expected_sibling_count(&indices, 4).unwrap()
        );
        assert_eq!(
            positions,
            vec![
                FrontierSiblingPosition {
                    level: 0,
                    node_index: 3,
                },
                FrontierSiblingPosition {
                    level: 0,
                    node_index: 4,
                },
                FrontierSiblingPosition {
                    level: 0,
                    node_index: 15,
                },
                FrontierSiblingPosition {
                    level: 1,
                    node_index: 0,
                },
                FrontierSiblingPosition {
                    level: 1,
                    node_index: 3,
                },
                FrontierSiblingPosition {
                    level: 1,
                    node_index: 6,
                },
                FrontierSiblingPosition {
                    level: 2,
                    node_index: 2,
                },
            ]
        );

        let cache = SparseMerkleCache::new(4).unwrap();
        let proof = build_multiproof(&cache, &indices, 4).unwrap();
        let padded = pad_frontier_siblings(&indices, &proof.siblings, 4, 8).unwrap();
        assert_eq!(padded.len(), 8);
        assert!(padded[proof.siblings.len()..]
            .iter()
            .all(|digest| *digest == STRUCTURAL_FRONTIER_PAD));
        assert_eq!(
            unpad_frontier_siblings(&indices, &padded, 4, 8).unwrap(),
            proof.siblings
        );

        let mut bad = padded;
        bad[7][0] = 1;
        assert_eq!(
            unpad_frontier_siblings(&indices, &bad, 4, 8),
            Err(SparseMerkleError::NonCanonicalPadding { index: 7 })
        );
        assert_eq!(
            pad_frontier_siblings(&indices, &proof.siblings, 4, 6),
            Err(SparseMerkleError::FrontierCapacityExceeded {
                required: 7,
                capacity: 6,
            })
        );
        assert_eq!(
            unpad_frontier_siblings(&indices, &bad[..7], 4, 8),
            Err(SparseMerkleError::PaddedProofLengthMismatch {
                expected: 8,
                actual: 7,
            })
        );
    }

    #[test]
    fn structural_frontier_plan_matches_reconstruction_for_every_small_subset() {
        use rayon::prelude::*;

        fn digest(seed: usize) -> StateHash {
            let mut out = [0u8; 32];
            out[..8].copy_from_slice(&(seed as u64).to_le_bytes());
            out[8..16].copy_from_slice(&(seed as u64).wrapping_mul(17).to_le_bytes());
            out
        }

        for depth in 1..=4u32 {
            let domain = 1usize << depth;
            (1usize..(1usize << domain))
                .into_par_iter()
                .for_each(|mask| {
                    let indices: Vec<_> = (0..domain)
                        .filter(|index| mask & (1usize << index) != 0)
                        .map(|index| index as u32)
                        .collect();
                    let leaves: Vec<_> = indices
                        .iter()
                        .enumerate()
                        .map(|(ordinal, index)| digest(mask ^ ordinal ^ (*index as usize + 1)))
                        .collect();
                    let plan = derive_structural_frontier_plan(&indices, depth).unwrap();
                    let positions = frontier_sibling_positions(&indices, depth).unwrap();
                    assert_eq!(plan.frontier_positions(), positions);

                    let siblings: Vec<_> = (0..positions.len())
                        .map(|ordinal| digest(mask.wrapping_mul(31).wrapping_add(ordinal + 1)))
                        .collect();
                    let evaluation =
                        evaluate_structural_frontier(&plan, &leaves, &siblings).unwrap();
                    let reconstructed =
                        reconstruct_root(&indices, &leaves, &siblings, depth).unwrap();

                    assert_eq!(evaluation.root, reconstructed, "depth={depth}, mask={mask}");
                    assert_eq!(evaluation.combines.len(), plan.combines().len());
                    assert_eq!(
                        plan.combines().len(),
                        indices.len() + siblings.len() - 1,
                        "depth={depth}, mask={mask}"
                    );
                });
        }
    }

    #[test]
    fn live_zero_frontier_digest_is_data_not_padding() {
        let indices = [0];
        let leaves = [leaf(1)];
        let live_zero = [[0u8; 32]];
        let plan = derive_structural_frontier_plan(&indices, 1).unwrap();
        assert_eq!(plan.frontier_positions().len(), 1);

        let evaluation = evaluate_structural_frontier(&plan, &leaves, &live_zero).unwrap();
        assert_eq!(
            evaluation.root,
            reconstruct_root(&indices, &leaves, &live_zero, 1).unwrap()
        );

        let padded = pad_frontier_siblings(&indices, &live_zero, 1, 2).unwrap();
        assert_eq!(
            unpad_frontier_siblings(&indices, &padded, 1, 2).unwrap(),
            live_zero
        );
    }

    #[test]
    fn zero_depth_one_leaf_and_empty_genesis_contract_are_explicit() {
        assert_eq!(maximum_sibling_count(0, 0), 0);
        assert_eq!(maximum_sibling_count(1, 0), 0);
        assert_eq!(expected_sibling_count(&[0], 0), Ok(0));
        assert_eq!(pad_frontier_siblings(&[0], &[], 0, 0), Ok(Vec::new()));
        assert_eq!(
            expected_sibling_count(&[], 0),
            Err(SparseMerkleError::EmptyIndices)
        );
    }

    #[test]
    fn analytical_maximum_matches_every_small_tree() {
        for depth in 1..=4u32 {
            let domain = 1usize << depth;
            let mut observed = vec![0usize; domain + 1];
            for mask in 1usize..(1usize << domain) {
                let indices: Vec<_> = (0..domain)
                    .filter(|index| mask & (1usize << index) != 0)
                    .map(|index| index as u32)
                    .collect();
                let siblings = expected_sibling_count(&indices, depth).unwrap();
                observed[indices.len()] = observed[indices.len()].max(siblings);
            }
            for (touched, &observed_maximum) in observed.iter().enumerate().skip(1) {
                assert_eq!(
                    observed_maximum,
                    maximum_sibling_count(touched, depth),
                    "depth={depth}, touched={touched}"
                );
            }
        }
    }

    #[test]
    fn segmented_maximum_matches_every_small_capped_tree() {
        const DEPTH: u32 = 4;
        const LOG_SEGMENT: u32 = 2;
        const MAX_SEGMENTS: usize = 2;
        let domain = 1usize << DEPTH;
        let capacity = MAX_SEGMENTS * (1usize << LOG_SEGMENT);
        let mut observed = vec![0usize; capacity + 1];
        for mask in 1usize..(1usize << domain) {
            let indices: Vec<_> = (0..domain)
                .filter(|index| mask & (1usize << index) != 0)
                .map(|index| index as u32)
                .collect();
            if indices.len() > capacity {
                continue;
            }
            let segments: BTreeSet<_> = indices.iter().map(|index| index >> LOG_SEGMENT).collect();
            if segments.len() > MAX_SEGMENTS {
                continue;
            }
            let siblings = expected_sibling_count(&indices, DEPTH).unwrap();
            observed[indices.len()] = observed[indices.len()].max(siblings);
        }
        for (touched, &observed_maximum) in observed.iter().enumerate().skip(1) {
            assert_eq!(
                observed_maximum,
                maximum_sibling_count_with_segment_cap(touched, DEPTH, LOG_SEGMENT, MAX_SEGMENTS,),
                "touched={touched}"
            );
        }
    }

    #[test]
    fn production_frontier_capacity_is_attainable() {
        const TOUCHED: usize = 1_531;
        const DEPTH: u32 = 32;
        const LOG_SEGMENT: u32 = 16;
        const MAX_SEGMENTS: usize = 256;

        // Bit reversal spreads both segment ids and local leaves maximally at
        // every level.  251 segments carry six leaves and five carry five.
        let mut indices = Vec::with_capacity(TOUCHED);
        for segment_rank in 0..MAX_SEGMENTS {
            let segment = (segment_rank as u32).reverse_bits() >> 16;
            let local_count = if segment_rank < 251 { 6 } else { 5 };
            for local_rank in 0..local_count {
                let local = (local_rank as u32).reverse_bits() >> 16;
                indices.push((segment << LOG_SEGMENT) | local);
            }
        }
        indices.sort_unstable();
        assert_eq!(indices.len(), TOUCHED);
        assert_eq!(
            indices
                .iter()
                .map(|index| index >> LOG_SEGMENT)
                .collect::<BTreeSet<_>>()
                .len(),
            MAX_SEGMENTS
        );
        let analytical =
            maximum_sibling_count_with_segment_cap(TOUCHED, DEPTH, LOG_SEGMENT, MAX_SEGMENTS);
        assert_eq!(analytical, 22_468);
        assert_eq!(expected_sibling_count(&indices, DEPTH).unwrap(), analytical);
        assert_eq!(maximum_sibling_count(TOUCHED, DEPTH), 32_668);
    }

    #[test]
    fn rejects_missing_extra_reordered_and_duplicate_topology() {
        let cache = SparseMerkleCache::from_leaves(4, &[(2, leaf(1)), (9, leaf(2))]).unwrap();
        let indices = [2, 9];
        let leaves = [leaf(1), leaf(2)];
        let proof = build_multiproof(&cache, &indices, 4).unwrap();
        assert!(matches!(
            reconstruct_root(
                &indices,
                &leaves,
                &proof.siblings[..proof.siblings.len() - 1],
                4
            ),
            Err(SparseMerkleError::ProofLengthMismatch { .. })
        ));
        let mut extra = proof.siblings.clone();
        extra.push([7u8; 32]);
        assert!(matches!(
            reconstruct_root(&indices, &leaves, &extra, 4),
            Err(SparseMerkleError::ProofLengthMismatch { .. })
        ));
        assert_eq!(
            expected_sibling_count(&[9, 2], 4),
            Err(SparseMerkleError::UnsortedIndices)
        );
        assert_eq!(
            expected_sibling_count(&[2, 2], 4),
            Err(SparseMerkleError::DuplicateIndex { index: 2 })
        );
    }

    #[test]
    fn bit_flip_or_wrong_leaf_changes_root() {
        let cache = SparseMerkleCache::from_leaves(4, &[(2, leaf(1)), (9, leaf(2))]).unwrap();
        let indices = [2, 9];
        let leaves = [leaf(1), leaf(2)];
        let proof = build_multiproof(&cache, &indices, 4).unwrap();
        let root = reconstruct_root(&indices, &leaves, &proof.siblings, 4).unwrap();
        assert_eq!(root, cache.root());

        let mut bad_siblings = proof.siblings.clone();
        bad_siblings[0][0] ^= 1;
        assert_ne!(
            reconstruct_root(&indices, &leaves, &bad_siblings, 4).unwrap(),
            root
        );

        let bad_leaves = [leaf(1), leaf(99)];
        assert_ne!(
            reconstruct_root(&indices, &bad_leaves, &proof.siblings, 4).unwrap(),
            root
        );
    }

    #[test]
    fn leaf_cannot_move_to_another_index_with_same_frontier() {
        let cache = SparseMerkleCache::from_leaves(4, &[(2, leaf(1))]).unwrap();
        let proof = build_multiproof(&cache, &[2], 4).unwrap();
        let root_at_two = reconstruct_root(&[2], &[leaf(1)], &proof.siblings, 4).unwrap();
        assert_eq!(root_at_two, cache.root());
        let root_at_three = reconstruct_root(&[3], &[leaf(1)], &proof.siblings, 4).unwrap();
        assert_ne!(root_at_three, cache.root());
    }

    #[test]
    fn expanded_paths_match_multiproof_root_with_directions() {
        let leaves = [(2, leaf(1)), (5, leaf(2)), (14, leaf(3))];
        let cache = SparseMerkleCache::from_leaves(4, &leaves).unwrap();
        let indices = [2, 5, 14];
        let touched = [leaf(1), leaf(2), leaf(3)];
        let proof = build_multiproof(&cache, &indices, 4).unwrap();
        let paths = expand_multiproof_paths(&indices, &touched, &proof.siblings, 4).unwrap();
        assert_eq!(paths.len(), 3);

        for path in paths {
            let mut current = path.leaf;
            for level in 0..4 {
                current = if path.directions[level] {
                    state_node_hash(path.siblings[level], current)
                } else {
                    state_node_hash(current, path.siblings[level])
                };
            }
            assert_eq!(current, cache.root(), "index {}", path.index);
        }
    }
}
