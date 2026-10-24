// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical sharing of repeated siblings, not a new Merkle verifier.
//!
//! Keys are (level counted upward from leaves, sibling index at that level).
//! Their sorted order and count are derived from the encoded query positions.
//! No offsets, counts, keys, reference indices, or tree topology come from the
//! wire. The decoder reconstructs the original full paths, which remain subject
//! to the unchanged transcript-derived position and Merkle-root checks.

use std::collections::{BTreeMap, BTreeSet};

use super::{decode_hash_vec, put_hash, HistoryStepError, Reader, HASH_BYTES};

type Key = (usize, usize);
type Hash = [u8; HASH_BYTES];

fn keys(positions: &[usize], depth: usize) -> Result<BTreeSet<Key>, HistoryStepError> {
    if depth >= usize::BITS as usize || positions.iter().any(|&p| p >= (1usize << depth)) {
        return Err(HistoryStepError::WireEncoding);
    }
    Ok(positions
        .iter()
        .flat_map(|&p| (0..depth).map(move |level| (level, (p >> level) ^ 1)))
        .collect())
}

pub(super) fn encode(
    out: &mut Vec<u8>,
    positions: &[usize],
    depth: usize,
    paths: &[&[Hash]],
) -> Result<(), HistoryStepError> {
    let order = keys(positions, depth)?;
    if positions.len() != paths.len() || paths.iter().any(|p| p.len() != depth) {
        return Err(HistoryStepError::WireEncoding);
    }
    let mut nodes = BTreeMap::new();
    for (&position, path) in positions.iter().zip(paths) {
        for (level, &hash) in path.iter().enumerate() {
            let key = (level, (position >> level) ^ 1);
            if let Some(previous) = nodes.insert(key, hash) {
                if previous != hash {
                    // A valid opening of the same tree cannot give two different
                    // digests to one node. Do not silently choose either value.
                    return Err(HistoryStepError::WireEncoding);
                }
            }
        }
    }
    for key in order {
        put_hash(out, nodes.get(&key).ok_or(HistoryStepError::WireEncoding)?);
    }
    Ok(())
}

pub(super) fn decode(
    reader: &mut Reader<'_>,
    positions: &[usize],
    depth: usize,
) -> Result<Vec<Vec<Hash>>, HistoryStepError> {
    let order = keys(positions, depth)?;
    let bytes = order
        .len()
        .checked_mul(HASH_BYTES)
        .ok_or(HistoryStepError::WireEncoding)?;
    // Check the entire dictionary before allocating digest vectors. Every
    // remaining allocation is bounded by the fixed protocol class's q * depth.
    let mut hashes = Reader::new(reader.take(bytes)?);
    let values = decode_hash_vec(&mut hashes, order.len())?;
    hashes.finish()?;
    let nodes: BTreeMap<_, _> = order.into_iter().zip(values).collect();
    positions
        .iter()
        .map(|&p| {
            (0..depth)
                .map(|level| {
                    nodes
                        .get(&(level, (p >> level) ^ 1))
                        .copied()
                        .ok_or(HistoryStepError::WireEncoding)
                })
                .collect()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_ivc_core::merkle;

    #[test]
    fn real_merkle_paths_roundtrip_with_repeated_and_colliding_queries() {
        for depth in 0..=10 {
            let n = 1usize << depth;
            let data: Vec<u8> = (0..n)
                .flat_map(|i| (0..32).map(move |j| (i.rotate_left(j) as u8).wrapping_add(j as u8)))
                .collect();
            let tree = merkle::merkle_tree_sequential(&data, n);
            let positions: Vec<_> = (0..133).map(|i| (i * 37 / 3) % n).collect();
            let paths: Vec<_> = positions
                .iter()
                .map(|&p| merkle::merkle_proof(&tree, n, p))
                .collect();
            let refs: Vec<_> = paths.iter().map(Vec::as_slice).collect();
            let mut bytes = Vec::new();
            encode(&mut bytes, &positions, depth, &refs).unwrap();
            assert!(bytes.len() <= positions.len() * depth * HASH_BYTES);
            let mut reader = Reader::new(&bytes);
            let restored = decode(&mut reader, &positions, depth).unwrap();
            reader.finish().unwrap();
            assert_eq!(restored, paths);
            for (&p, path) in positions.iter().zip(restored) {
                assert!(merkle::verify_merkle_proof(
                    tree.last().unwrap(),
                    &tree[p],
                    p,
                    &path
                ));
            }
        }
    }

    #[test]
    fn conflicting_duplicate_nodes_and_bad_shapes_are_rejected() {
        let a = [[1; 32], [2; 32]];
        let b = [[3; 32], [2; 32]];
        assert!(encode(&mut Vec::new(), &[0, 0], 2, &[&a, &b]).is_err());
        assert!(encode(&mut Vec::new(), &[4], 2, &[&a]).is_err());
        assert!(encode(&mut Vec::new(), &[0], 1, &[&a]).is_err());
        assert!(encode(&mut Vec::new(), &[0], 2, &[]).is_err());
        assert!(decode(&mut Reader::new(&[]), &[0], usize::MAX).is_err());
    }

    #[test]
    fn truncation_is_rejected_and_digest_mutation_is_left_to_the_real_verifier() {
        let data = [7u8; 256];
        let tree = merkle::merkle_tree_sequential(&data, 8);
        let path = merkle::merkle_proof(&tree, 8, 0);
        let mut bytes = Vec::new();
        encode(&mut bytes, &[0], 3, &[&path]).unwrap();
        for len in 0..bytes.len() {
            assert!(decode(&mut Reader::new(&bytes[..len]), &[0], 3).is_err());
        }
        bytes[0] ^= 1;
        let restored = decode(&mut Reader::new(&bytes), &[0], 3).unwrap();
        assert!(!merkle::verify_merkle_proof(
            tree.last().unwrap(),
            &tree[0],
            0,
            &restored[0]
        ));
    }
}
