// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

use super::*;
use noid_ivc_core::matrix_claim::c1::{fresh_claim_value_c1, stacked_matrix_mle_eval_c1};
use std::{collections::VecDeque, sync::Mutex};

/// Only this verifier can add entries, after an authenticated matrix scan.
/// It stores exact accumulated claims, never acceptance of a whole terminal.
#[derive(Default)]
pub(super) struct ClaimCache(Mutex<VecDeque<CheckedClaim>>);
struct CheckedClaim {
    bank: [u8; 32],
    class: Class,
    matrix: [u8; 32],
    shape: FieldShape,
    claim: C1MatrixAccClaim,
}
impl ClaimCache {
    fn contains(&self, bank: &Bank, class: Class, claim: &C1MatrixAccClaim) -> bool {
        let Ok(mut entries) = self.0.lock() else {
            return false;
        };
        let Some(index) = entries.iter().position(|e| {
            e.bank == bank.digest()
                && e.class == class
                && e.matrix == bank.matrix_digest(class)
                && e.shape == bank.config().class(class).shape()
                && e.claim == *claim
        }) else {
            return false;
        };
        let found = entries.remove(index).expect("located checked claim");
        entries.push_back(found);
        true
    }
    fn remember(&self, bank: &Bank, class: Class, claim: C1MatrixAccClaim) {
        let Ok(mut entries) = self.0.lock() else {
            return;
        };
        if entries.len() == 8 {
            entries.pop_front();
        }
        entries.push_back(CheckedClaim {
            bank: bank.digest(),
            class,
            matrix: bank.matrix_digest(class),
            shape: bank.config().class(class).shape(),
            claim,
        });
    }
}

fn check_claims(
    matrix: &HistoryStepMatrixLease,
    fresh: Option<&C1FreshLincheckClaim>,
    accumulated: Option<&C1MatrixAccClaim>,
) -> Result<(), V2Error> {
    let (fv, av) = match matrix {
        HistoryStepMatrixLease::Resident(matrix) => (
            fresh.map(|claim| fresh_claim_value_c1(matrix, claim)),
            accumulated.map(|claim| stacked_matrix_mle_eval_c1(matrix, claim)),
        ),
        HistoryStepMatrixLease::Compact(matrix) => {
            let evaluated = matrix
                .evaluate_matrix_claims_c1_authenticated(fresh, accumulated)
                .map_err(|_| V2Error::Matrix)?;
            if !evaluated.is_bound_to(fresh, accumulated) {
                return Err(V2Error::Matrix);
            }
            (evaluated.fresh_value(), evaluated.accumulated_value())
        }
    };
    if fv != fresh.map(|c| c.value) || av != accumulated.map(|c| c.value) {
        return Err(V2Error::Matrix);
    }
    Ok(())
}

#[must_use = "verified v2 authority must be consumed by block application"]
pub struct AcceptedTerminal {
    class: Class,
    accumulator: ChainAccumulator,
    origin: Origin,
}
impl AcceptedTerminal {
    pub fn class(&self) -> Class {
        self.class
    }
    pub fn accumulator(&self) -> &ChainAccumulator {
        &self.accumulator
    }
    pub fn origin(&self) -> &Origin {
        &self.origin
    }
}

pub fn verify_terminal(
    runtime: &Runtime,
    origin: &VerifiedOrigin,
    terminal: &Terminal,
    header: &BlockHeader,
    epoch_header: &BlockHeader,
) -> Result<AcceptedTerminal, V2Error> {
    origin.0.check(&runtime.bank)?;
    let parsed = runtime.bank.parse(&terminal.proof.io)?;
    if parsed.origin != origin.0 || parsed.class != terminal.class {
        return Err(V2Error::Origin);
    }
    parsed
        .accumulator
        .validate_local_header_boundary(header, epoch_header)
        .map_err(|_| V2Error::Boundary)?;
    let (fresh, _) = parent::replay(runtime, terminal.class, &terminal.proof)?;
    for class in Class::ALL {
        let current_fresh = (class == terminal.class).then_some(&fresh);
        let accumulated = parsed.claims[class.index()].as_ref();
        if current_fresh.is_none() {
            let Some(claim) = accumulated else {
                continue;
            };
            if runtime.cache.contains(&runtime.bank, class, claim) {
                continue;
            }
        }
        // Fresh claims are always scanned. Only an unchanged carried lane can
        // avoid reloading and scanning its matrix after an earlier success.
        if let Some(source) = &runtime.verifier_matrices {
            let evaluated = source.evaluate(class, current_fresh, accumulated)?;
            if evaluated.structural_digest() != runtime.bank.matrix_digest(class)
                || !evaluated.is_bound_to(current_fresh, accumulated)
                || evaluated.fresh_value() != current_fresh.map(|claim| claim.value)
                || evaluated.accumulated_value() != accumulated.map(|claim| claim.value)
            {
                return Err(V2Error::Matrix);
            }
        } else {
            let matrix = runtime.load_matrix(class)?;
            check_claims(&matrix, current_fresh, accumulated)?;
        }
        if let Some(claim) = accumulated {
            runtime.cache.remember(&runtime.bank, class, claim.clone());
        }
    }
    Ok(AcceptedTerminal {
        class: parsed.class,
        accumulator: parsed.accumulator,
        origin: parsed.origin,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn carried_cache_is_exact_bounded_and_runtime_local() {
        let (bank, _, _) = bank::fixture();
        let cache = ClaimCache::default();
        let lane = Lane::for_class(Class::Large);
        let claim = C1MatrixAccClaim {
            point: vec![F256::ONE; lane.point_len()],
            value: F256::ONE,
        };
        assert!(!cache.contains(&bank, Class::Large, &claim));
        cache.remember(&bank, Class::Large, claim.clone());
        assert!(cache.contains(&bank, Class::Large, &claim));
        assert!(!cache.contains(&bank, Class::Small, &claim));
        for field in 0..4 {
            {
                let mut entries = cache.0.lock().unwrap();
                let entry = entries.back_mut().unwrap();
                match field {
                    0 => entry.bank[0] ^= 1,
                    1 => entry.matrix[0] ^= 1,
                    2 => entry.shape.m += 1,
                    _ => entry.class = Class::Small,
                }
            }
            assert!(!cache.contains(&bank, Class::Large, &claim));
            cache.0.lock().unwrap().clear();
            cache.remember(&bank, Class::Large, claim.clone());
        }
        let mut changed = claim.clone();
        changed.point[0] = F256::ZERO;
        assert!(!cache.contains(&bank, Class::Large, &changed));
        changed = claim.clone();
        changed.value = F256::ZERO;
        assert!(!cache.contains(&bank, Class::Large, &changed));
        assert!(!ClaimCache::default().contains(&bank, Class::Large, &claim));
        for _ in 0..16 {
            cache.remember(&bank, Class::Large, changed.clone());
        }
        assert_eq!(cache.0.lock().unwrap().len(), 8);
        assert!(!cache.contains(&bank, Class::Large, &claim));
    }
}
