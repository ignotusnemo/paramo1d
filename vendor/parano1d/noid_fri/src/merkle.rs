// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Merkle tree with `CryptographicHasher`-based commitment.

use crate::hasher::{CryptographicHasher, HashOutput};

use rayon::prelude::*;

/// Minimum number of leaves to justify parallel Merkle build.
const MERKLE_PARALLEL_THRESHOLD: usize = 256;

/// Minimum number of hashes to justify batch hashing.
const BATCH_HASH_THRESHOLD: usize = 16;

/// Merkle tree backed by contiguous layers (index 0 = root, last = leaves).
///
/// Nodes are stored in a single flat buffer laid out bottom-up:
/// `[leaves (n), parent_layer (n/2), ..., root (1)]`.
/// `layer_offsets[d]` = offset (in `nodes`) of the layer at depth `d`
/// from the ROOT (depth 0 = root; depth `tree_depth` = leaves).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerkleTree {
    nodes: Vec<HashOutput>,
    layer_offsets: Vec<usize>,
    layer_lens: Vec<usize>,
}

/// Commitment that stores the Merkle root and tree depth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VectorCommitment {
    pub root: HashOutput,
    pub depth: usize,
}

impl VectorCommitment {
    pub fn root(&self) -> HashOutput {
        self.root
    }
    pub fn depth(&self) -> usize {
        self.depth
    }
}

impl MerkleTree {
    /// Build a Merkle tree from a power-of-two set of leaf hashes.
    pub fn new(leaf_hashes: Vec<HashOutput>, hasher: &dyn CryptographicHasher) -> Self {
        Self::build(leaf_hashes, hasher, false)
    }

    /// Build a Merkle tree with parallel, allocation-free layer hashing.
    ///
    /// All 2N-1 nodes are allocated once in a single buffer; each level is
    /// then filled in place by parallel batched hashing over adjacent pairs.
    pub fn new_parallel(leaf_hashes: Vec<HashOutput>, hasher: &dyn CryptographicHasher) -> Self {
        Self::build(leaf_hashes, hasher, true)
    }

    fn build(
        leaf_hashes: Vec<HashOutput>,
        hasher: &dyn CryptographicHasher,
        parallel: bool,
    ) -> Self {
        let n = leaf_hashes.len();
        assert!(n.is_power_of_two(), "Leaf hashes must be a power of two");

        let tree_depth = n.trailing_zeros() as usize;
        let total = 2 * n - 1;

        let mut nodes: Vec<HashOutput> = Vec::with_capacity(total);
        nodes.extend_from_slice(&leaf_hashes);
        nodes.resize(total, [0u8; 32]);

        let mut level_start = 0usize;
        let mut level_len = n;
        while level_len > 1 {
            let next_start = level_start + level_len;
            let next_len = level_len / 2;

            let (src_part, dst_part) = nodes.split_at_mut(next_start);
            let src = &src_part[level_start..level_start + level_len];
            let dst = &mut dst_part[..next_len];

            if parallel && next_len >= MERKLE_PARALLEL_THRESHOLD / 2 {
                hash_layer_par_into(src, dst, hasher);
            } else if next_len >= BATCH_HASH_THRESHOLD {
                hasher.batch_compress(src, dst);
            } else {
                for (pair, out) in src.chunks_exact(2).zip(dst.iter_mut()) {
                    *out = hasher.compress(&pair[0], &pair[1]);
                }
            }

            level_start = next_start;
            level_len = next_len;
        }

        // Build top-down offset index: depth 0 = root, depth `tree_depth` = leaves.
        let mut layer_offsets = Vec::with_capacity(tree_depth + 1);
        let mut layer_lens = Vec::with_capacity(tree_depth + 1);
        // Nodes are laid out bottom-up in `nodes`; compute offsets top-down.
        let mut bottom_up_offsets = Vec::with_capacity(tree_depth + 1);
        let mut bottom_up_lens = Vec::with_capacity(tree_depth + 1);
        {
            let mut off = 0usize;
            let mut len = n;
            loop {
                bottom_up_offsets.push(off);
                bottom_up_lens.push(len);
                if len == 1 {
                    break;
                }
                off += len;
                len /= 2;
            }
        }
        for i in (0..bottom_up_offsets.len()).rev() {
            layer_offsets.push(bottom_up_offsets[i]);
            layer_lens.push(bottom_up_lens[i]);
        }

        MerkleTree {
            nodes,
            layer_offsets,
            layer_lens,
        }
    }

    pub fn get_root(&self) -> HashOutput {
        let off = self.layer_offsets[0];
        self.nodes[off]
    }

    /// Number of layers (depth + 1). Matches the serialized `data.len()`.
    pub fn num_layers(&self) -> usize {
        self.layer_offsets.len()
    }

    /// Number of nodes at layer `depth` (0 = root, last = leaves).
    pub fn layer_len(&self, depth: usize) -> usize {
        self.layer_lens[depth]
    }

    /// Get the hash of a node at a given depth and index.
    /// Depth 0 = root, depth `num_layers()-1` = leaves.
    pub fn get_node_at_depth(&self, depth: usize, index: usize) -> HashOutput {
        assert!(depth < self.layer_offsets.len());
        assert!(index < self.layer_lens[depth]);
        self.nodes[self.layer_offsets[depth] + index]
    }

    pub fn get_merkle_path(&self, leaf_index: usize) -> Vec<HashOutput> {
        let leaf_depth = self.num_layers() - 1;
        assert!(
            leaf_index < self.layer_lens[leaf_depth],
            "Leaf index out of bounds"
        );

        let mut index = leaf_index;
        let mut path = Vec::with_capacity(leaf_depth);

        for depth in (1..=leaf_depth).rev() {
            let sibling = index ^ 1;
            let off = self.layer_offsets[depth];
            path.push(self.nodes[off + sibling]);
            index >>= 1;
        }

        path
    }
}

/// Recompute the Merkle root from a leaf hash and its path.
pub fn verify_merkle_path(
    commitment: &VectorCommitment,
    leaf_hash: HashOutput,
    leaf_index: usize,
    merkle_path: &[HashOutput],
    hasher: &dyn CryptographicHasher,
) -> bool {
    if merkle_path.len() != commitment.depth {
        return false;
    }

    let mut hash = leaf_hash;
    for (d, sibling) in merkle_path.iter().enumerate() {
        let is_left_child = ((leaf_index >> d) & 1) == 0;
        hash = if is_left_child {
            hasher.compress(&hash, sibling)
        } else {
            hasher.compress(sibling, &hash)
        };
    }

    hash == commitment.root
}

/// Parallel batched layer hashing writing directly into `dst`.
///
/// `src` is a slice of 2N children; `dst` is the N-entry parent layer.
/// Dispatches per-chunk through `hasher.batch_compress` so each backend
/// can use its own SIMD / multi-lane kernel.
fn hash_layer_par_into(
    src: &[HashOutput],
    dst: &mut [HashOutput],
    hasher: &dyn CryptographicHasher,
) {
    assert_eq!(src.len(), dst.len() * 2);
    let threads = rayon::current_num_threads().max(1);
    let mut chunk_pairs = ((src.len() / threads).max(BATCH_HASH_THRESHOLD * 2)) & !1;
    if chunk_pairs == 0 {
        chunk_pairs = 2;
    }
    let chunk_dst = chunk_pairs / 2;

    src.par_chunks(chunk_pairs)
        .zip(dst.par_chunks_mut(chunk_dst))
        .for_each(|(src_chunk, dst_chunk)| {
            hasher.batch_compress(src_chunk, dst_chunk);
        });
}

/// Hash a slice of Block128 element pairs into leaf hashes using `hash_pair`.
///
/// Uses rayon-parallel batched hashing on large inputs; batched-but-serial
/// for medium; scalar for small. No de-interleaving allocation — the batch
/// kernel reads the interleaved slice directly.
pub fn compute_leaf_hashes(
    vals: &[noid_core::Block128],
    hasher: &dyn CryptographicHasher,
) -> Vec<HashOutput> {
    assert_eq!(
        vals.len() & 1,
        0,
        "Leaf construction requires an even number of elements"
    );
    let n = vals.len() / 2;
    let mut out = vec![[0u8; 32]; n];

    if n >= MERKLE_PARALLEL_THRESHOLD / 2 {
        let threads = rayon::current_num_threads().max(1);
        // pair-count chunks must be a multiple of PACKED_LANES and at least
        // BATCH_HASH_THRESHOLD to amortise the batched kernel.
        let mut chunk_pairs = ((n / threads).max(BATCH_HASH_THRESHOLD))
            & !((noid_core::packed::PACKED_LANES.max(1)) - 1);
        if chunk_pairs == 0 {
            chunk_pairs = BATCH_HASH_THRESHOLD;
        }
        let chunk_vals = chunk_pairs * 2;

        vals.par_chunks(chunk_vals)
            .zip(out.par_chunks_mut(chunk_pairs))
            .for_each(|(vals_chunk, out_chunk)| {
                hasher.batch_hash_pair(vals_chunk, out_chunk);
            });
    } else if n >= BATCH_HASH_THRESHOLD {
        hasher.batch_hash_pair(vals, &mut out);
    } else {
        for (pair, slot) in vals.chunks_exact(2).zip(out.iter_mut()) {
            *slot = hasher.hash_pair(&pair[0], &pair[1]);
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    use noid_poseidon2b::Poseidon2bSponge;

    #[test]
    fn test_merkle_tree_basic() {
        let hasher = Poseidon2bSponge::new();
        let leaves: Vec<HashOutput> = (0..8)
            .map(|i| {
                let mut buf = [0u8; 32];
                buf[0] = i as u8;
                buf
            })
            .collect();

        let tree = MerkleTree::new(leaves.clone(), &hasher);
        let commitment = VectorCommitment {
            root: tree.get_root(),
            depth: 3,
        };

        for (i, &leaf) in leaves.iter().enumerate() {
            let path = tree.get_merkle_path(i);
            assert!(verify_merkle_path(&commitment, leaf, i, &path, &hasher));
        }
    }
}
