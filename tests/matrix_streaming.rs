use noid_ivc_core::{
    field::{F128, F256},
    field_r1cs::{synthetic_satisfiable, SeekableFieldR1csArtifact},
    matrix_claim::c1::{
        fresh_claim_value_c1, stacked_matrix_mle_eval_c1, C1FreshLincheckClaim, C1MatrixAccClaim,
        C1MatrixClaimEvaluator,
    },
    proof::FieldShape,
};
use sha2::{Digest, Sha256};
use std::io::Cursor;

fn value(seed: u64) -> F256 {
    F256::new(
        F128::new(seed.wrapping_mul(91), seed ^ 0x1234),
        F128::new(seed.rotate_left(11), !seed),
    )
}

#[test]
fn streaming_extension_claims_match_resident_arithmetic() {
    for (size, seed) in [(8, 0), (8, 1), (13, 9), (8, 65537)] {
        let (mut matrix, _) = synthetic_satisfiable(size, size, seed);
        if seed == 65537 {
            let mut rows = vec![Vec::new(); 1 << size];
            for (row, count) in [(0, 33001), (7, 17003)] {
                rows[row] = (0..count)
                    .map(|i| {
                        (
                            (i * 83 % (1 << size)) as u32,
                            F128::new(1 + (i % 3) as u64, 0),
                        )
                    })
                    .collect();
            }
            matrix.a_0 = noid_ivc_core::field_r1cs::SparseFieldMatrix::from_rows(1 << size, rows);
        }
        let shape = FieldShape::of(&matrix);
        let digest = matrix.structural_statement_digest();
        let mut bytes = Vec::new();
        matrix.write_artifact(&mut bytes).unwrap();
        for workers in [1, paramo1d::available_workers()] {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(workers)
                .build()
                .unwrap();
            pool.install(|| {
                let mut stream = SeekableFieldR1csArtifact::preflight_for_c1(
                    Cursor::new(bytes.clone()),
                    shape,
                    digest,
                    1 << 20,
                )
                .unwrap();
                let mut fresh = C1FreshLincheckClaim {
                    alpha: value(seed + 1),
                    z_skip: value(seed + 2),
                    x_inner_rest: (0..shape.k_log - shape.k_skip)
                        .map(|i| value(i as u64 + 4))
                        .collect(),
                    r_inner_rest: (0..shape.k_log - shape.k_skip)
                        .map(|i| value(i as u64 + 17))
                        .collect(),
                    z_partial: (0..1 << shape.k_skip)
                        .map(|i| value(i as u64 + 32))
                        .collect(),
                    value: F256::ZERO,
                };
                fresh.value = fresh_claim_value_c1(&matrix, &fresh);
                let mut accumulated = C1MatrixAccClaim {
                    point: (0..2 * shape.k_log + 1)
                        .map(|i| value(i as u64 + seed))
                        .collect(),
                    value: F256::ZERO,
                };
                accumulated.value = stacked_matrix_mle_eval_c1(&matrix, &accumulated);
                for (f, a) in [
                    (None, None),
                    (Some(&fresh), None),
                    (None, Some(&accumulated)),
                    (Some(&fresh), Some(&accumulated)),
                ] {
                    let result = stream.evaluate_matrix_claims_c1(f, a).unwrap();
                    assert_eq!(result.structural_digest(), digest);
                    assert_eq!(result.fresh_value(), f.map(|c| c.value));
                    assert_eq!(result.accumulated_value(), a.map(|c| c.value));
                    assert!(result.is_bound_to(f, a));
                }
                let mut other = accumulated.clone();
                other.value += F256::ONE;
                let result = stream
                    .evaluate_matrix_claims_c1(Some(&fresh), Some(&accumulated))
                    .unwrap();
                assert!(!result.is_bound_to(Some(&fresh), Some(&other)));
            });
        }
    }
}

#[test]
fn disk_mutation_and_wrong_matrix_identity_reject() {
    let (matrix, _) = synthetic_satisfiable(8, 8, 77);
    let shape = FieldShape::of(&matrix);
    let digest = matrix.structural_statement_digest();
    let mut bytes = Vec::new();
    matrix.write_artifact(&mut bytes).unwrap();
    let mut stream = SeekableFieldR1csArtifact::preflight_for_c1(
        Cursor::new(bytes.clone()),
        shape,
        digest,
        1 << 20,
    )
    .unwrap();
    stream.evaluate_matrix_claims_c1(None, None).unwrap();
    let at = bytes.len() - 1;
    stream.reader_mut().get_mut()[at] ^= 1;
    assert!(stream.evaluate_matrix_claims_c1(None, None).is_err());
    stream.reader_mut().get_mut()[at] ^= 1;
    assert!(stream.evaluate_matrix_claims_c1(None, None).is_ok());
    let mut wrong = digest;
    wrong[0] ^= 1;
    let mut stream =
        SeekableFieldR1csArtifact::preflight_for_c1(Cursor::new(bytes), shape, wrong, 1 << 20)
            .unwrap();
    assert!(stream.evaluate_matrix_claims_c1(None, None).is_err());
}

#[test]
fn extension_claim_widths_are_checked_before_evaluation() {
    let (matrix, _) = synthetic_satisfiable(8, 8, 42);
    let mut bytes = Vec::new();
    matrix.write_artifact(&mut bytes).unwrap();
    let mut stream = SeekableFieldR1csArtifact::preflight_for_c1(
        Cursor::new(bytes),
        FieldShape::of(&matrix),
        matrix.structural_statement_digest(),
        1 << 20,
    )
    .unwrap();
    let bad = C1MatrixAccClaim {
        point: vec![F256::ONE],
        value: F256::ZERO,
    };
    assert!(stream.evaluate_matrix_claims_c1(None, Some(&bad)).is_err());
}

#[test]
fn pinned_span_preparation_preserves_claims_and_rejects_changes() {
    let (matrix, _) = synthetic_satisfiable(13, 13, 912);
    let shape = FieldShape::of(&matrix);
    let digest = matrix.structural_statement_digest();
    let mut bytes = Vec::new();
    matrix.write_artifact(&mut bytes).unwrap();
    let mut source = SeekableFieldR1csArtifact::preflight_for_c1(
        Cursor::new(bytes.clone()),
        shape,
        digest,
        1 << 20,
    )
    .unwrap();
    assert!(source.export_c1_span_cache().is_none());
    source.evaluate_matrix_claims_c1(None, None).unwrap();
    let cache = source.export_c1_span_cache().unwrap();
    let pin: [u8; 32] = Sha256::digest(&cache).into();
    let mut claim = C1MatrixAccClaim {
        point: (0..2 * shape.k_log + 1)
            .map(|i| value(i as u64 + 3))
            .collect(),
        value: F256::ZERO,
    };
    claim.value = stacked_matrix_mle_eval_c1(&matrix, &claim);
    for workers in [1, paramo1d::available_workers()] {
        rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .build()
            .unwrap()
            .install(|| {
                let mut restored = SeekableFieldR1csArtifact::preflight_for_c1(
                    Cursor::new(bytes.clone()),
                    shape,
                    digest,
                    1 << 20,
                )
                .unwrap();
                restored.restore_c1_span_cache(&cache, pin).unwrap();
                let result = restored
                    .evaluate_matrix_claims_c1(None, Some(&claim))
                    .unwrap();
                assert_eq!(result.structural_digest(), digest);
                assert_eq!(result.accumulated_value(), Some(claim.value));
                let last = bytes.len() - 1;
                restored.reader_mut().get_mut()[last] ^= 1;
                assert!(restored
                    .evaluate_matrix_claims_c1(None, Some(&claim))
                    .is_err());
                restored.reader_mut().get_mut()[last] ^= 1;
                assert_eq!(
                    restored
                        .evaluate_matrix_claims_c1(None, Some(&claim))
                        .unwrap()
                        .accumulated_value(),
                    Some(claim.value)
                );
                let mut changed_cache = cache.clone();
                let last = changed_cache.len() - 1;
                changed_cache[last] ^= 1;
                assert!(restored.restore_c1_span_cache(&changed_cache, pin).is_err());
                assert!(restored
                    .restore_c1_span_cache(&cache[..cache.len() - 1], pin)
                    .is_err());
            });
    }
}
