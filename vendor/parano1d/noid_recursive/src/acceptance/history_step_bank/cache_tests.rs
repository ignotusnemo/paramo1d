use super::*;
use noid_ivc_core::field_r1cs::SparseFieldMatrix;

// Small actual matrices exercise the same authenticated decision path without
// constructing two production-sized proof banks for every mutation test.
fn matrices() -> [Arc<FieldR1cs>; 2] {
    std::array::from_fn(|index| {
        let m = 7 + index;
        Arc::new(FieldR1cs {
            m,
            k_log: m,
            k_skip: 6,
            useful_rows: 1,
            a_0: SparseFieldMatrix::zero(1 << m),
            b_0: SparseFieldMatrix::zero(1 << m),
            const_pin: None,
            digest_cache: Default::default(),
            csc_cache: Default::default(),
        })
    })
}

fn pending(matrices: &[Arc<FieldR1cs>; 2], point: u64) -> PendingHistoryStepBankDecision {
    PendingHistoryStepBankDecision {
        tip_class: CanonicalHistoryStepClassId::new(0).unwrap(),
        tip_fresh: Some(C1FreshLincheckClaim {
            alpha: F256::ONE,
            z_skip: F256::ONE,
            x_inner_rest: vec![F256::ONE],
            r_inner_rest: vec![F256::ONE],
            z_partial: vec![F256::ZERO; 64],
            value: F256::ZERO,
        }),
        lanes: [
            PendingBankLane::Dead,
            PendingBankLane::Pending(C1MatrixAccClaim {
                point: vec![F256::from_base(F128::new(point, 0)); 17],
                value: F256::ZERO,
            }),
        ],
        requirements: std::array::from_fn(|index| MatrixRequirement {
            shape: FieldShape::of(&matrices[index]),
            digest: matrices[index].structural_statement_digest(),
        }),
        bank_digest: [0x55; 32],
        base: false,
        block_accumulator: block_acc_lanes(&crate::accumulator::genesis_accumulator()),
    }
}

fn decide(
    pending: PendingHistoryStepBankDecision,
    matrices: &[Arc<FieldR1cs>; 2],
    cache: &HistoryStepMatrixClaimCache,
    loads: &mut Vec<usize>,
) -> Result<AcceptedHistoryStepBankTip, HistoryStepBankError> {
    pending.finish_with_matrix_loader_cached(
        |class| {
            loads.push(class.index());
            Ok::<_, ()>(HistoryStepMatrixLease::Resident(Arc::clone(
                &matrices[class.index()],
            )))
        },
        cache,
    )
}

#[test]
fn carried_claim_scans_once_but_fresh_claim_is_always_checked() {
    let matrices = matrices();
    let cache = HistoryStepMatrixClaimCache::default();
    let mut loads = Vec::new();
    let _ = decide(pending(&matrices, 1), &matrices, &cache, &mut loads).unwrap();
    assert_eq!(loads, [0, 1]);
    // Model many new small tips, each with a new small accumulated claim,
    // while the one carried large claim stays unchanged. The large result
    // must survive well beyond the cache's capacity despite this churn.
    for point in 0..4 * HistoryStepMatrixClaimCache::CAPACITY {
        loads.clear();
        let mut next = pending(&matrices, 1);
        next.lanes[0] = PendingBankLane::Pending(C1MatrixAccClaim {
            point: vec![F256::from_base(F128::new(point as u64, 0)); 15],
            value: F256::ZERO,
        });
        let _ = decide(next, &matrices, &cache, &mut loads).unwrap();
        assert_eq!(loads, [0]);
    }
    assert_eq!(
        cache.entries.lock().unwrap().len(),
        HistoryStepMatrixClaimCache::CAPACITY
    );
    loads.clear();
    let mut false_fresh = pending(&matrices, 1);
    false_fresh.tip_fresh.as_mut().unwrap().value = F256::ONE;
    assert!(matches!(
        decide(false_fresh, &matrices, &cache, &mut loads),
        Err(HistoryStepBankError::FreshClaimValue(_))
    ));
    assert_eq!(loads, [0]);
}

#[test]
fn changed_point_is_rechecked_and_fork_return_reuses_only_exact_claim() {
    let matrices = matrices();
    let cache = HistoryStepMatrixClaimCache::default();
    let mut loads = Vec::new();
    for (point, expected) in [(1, vec![0, 1]), (2, vec![0, 1]), (1, vec![0]), (2, vec![0])] {
        loads.clear();
        let _ = decide(pending(&matrices, point), &matrices, &cache, &mut loads).unwrap();
        assert_eq!(loads, expected);
    }
}

#[test]
fn false_accumulated_value_is_never_remembered() {
    let matrices = matrices();
    let cache = HistoryStepMatrixClaimCache::default();
    let mut loads = Vec::new();
    let _ = decide(pending(&matrices, 1), &matrices, &cache, &mut loads).unwrap();
    for _ in 0..2 {
        loads.clear();
        let mut bad = pending(&matrices, 1);
        let PendingBankLane::Pending(claim) = &mut bad.lanes[1] else {
            unreachable!()
        };
        claim.value = F256::ONE;
        assert!(matches!(
            decide(bad, &matrices, &cache, &mut loads),
            Err(HistoryStepBankError::AccumulatedClaimValue(_))
        ));
        assert_eq!(loads, [0, 1]);
    }
    assert_eq!(cache.entries.lock().unwrap().len(), 1);
}

#[test]
fn cache_binds_bank_class_shape_and_matrix_identity() {
    let matrices = matrices();
    let cache = HistoryStepMatrixClaimCache::default();
    let _ = decide(pending(&matrices, 1), &matrices, &cache, &mut Vec::new()).unwrap();
    let request = pending(&matrices, 1);
    let class = CanonicalHistoryStepClassId::new(1).unwrap();
    let PendingBankLane::Pending(claim) = &request.lanes[1] else {
        unreachable!()
    };
    let requirement = request.requirements[1];
    assert!(cache.contains(request.bank_digest, class, requirement, claim));
    assert!(!cache.contains([0x56; 32], class, requirement, claim));
    assert!(!cache.contains(request.bank_digest, request.tip_class, requirement, claim));
    let mut altered = requirement;
    altered.shape.k_skip += 1;
    assert!(!cache.contains(request.bank_digest, class, altered, claim));
    altered = requirement;
    altered.digest[0] ^= 1;
    assert!(!cache.contains(request.bank_digest, class, altered, claim));
    let mut wrong_matrix = pending(&matrices, 1);
    wrong_matrix.requirements[1] = altered;
    assert!(matches!(
        decide(wrong_matrix, &matrices, &cache, &mut Vec::new()),
        Err(HistoryStepBankError::MatrixDigest(_))
    ));
}

#[test]
fn restart_and_eviction_fall_back_to_both_real_matrix_checks() {
    let matrices = matrices();
    let cache = HistoryStepMatrixClaimCache::default();
    let mut loads = Vec::new();
    for point in 0..12 {
        let _ = decide(pending(&matrices, point), &matrices, &cache, &mut loads).unwrap();
    }
    assert_eq!(
        cache.entries.lock().unwrap().len(),
        HistoryStepMatrixClaimCache::CAPACITY
    );
    loads.clear();
    let _ = decide(pending(&matrices, 11), &matrices, &cache, &mut loads).unwrap();
    assert_eq!(loads, [0]);
    loads.clear();
    let _ = decide(pending(&matrices, 0), &matrices, &cache, &mut loads).unwrap();
    assert_eq!(loads, [0, 1]);
    loads.clear();
    let _ = decide(
        pending(&matrices, 11),
        &matrices,
        &Default::default(),
        &mut loads,
    )
    .unwrap();
    assert_eq!(loads, [0, 1]);
}

#[test]
fn poisoned_cache_falls_back_to_authenticated_scans() {
    let matrices = matrices();
    let cache = HistoryStepMatrixClaimCache::default();
    let _ = std::panic::catch_unwind(|| {
        let _guard = cache.entries.lock().unwrap();
        panic!("test poisoned cache");
    });
    let mut loads = Vec::new();
    let _ = decide(pending(&matrices, 1), &matrices, &cache, &mut loads).unwrap();
    assert_eq!(loads, [0, 1]);
}
