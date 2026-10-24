// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Experimental closure of the reduction's matrix evaluations. This does not
//! authenticate a new runtime, install a bank or accept a HistoryStep.

use super::{HistoryStepRetirementTarget, PendingHistoryStepRetirement};
use crate::acceptance::history_step_bank::{CanonicalHistoryStepClassId, HISTORY_STEP_CLASS_COUNT};
use crate::accumulator::ChainAccumulator;
use noid_ivc_core::matrix_claim::sparse_c1::{
    Error as SparseEvaluationError, SparseMatrixEvaluationKey, SparseMatrixEvaluationProof,
};

/// Canonically ordered proof for one live legacy class. The key is public
/// preprocessing authenticated from the matrix, never a root supplied by a
/// peer under an unverified matrix-hash label.
pub struct HistoryStepRetirementEvaluation<'a> {
    pub class_id: CanonicalHistoryStepClassId,
    pub key: &'a SparseMatrixEvaluationKey,
    pub proof: &'a SparseMatrixEvaluationProof,
}

/// Every matrix claim returned by one fork-bound reduction has an evaluation
/// proof. The remaining cross-bank statement and v2 boundary relation are
/// outside this capability. It has no terminal or State-application conversion.
pub struct CheckedHistoryStepRetirementMatrices {
    request_binding: [u8; 32],
    target: HistoryStepRetirementTarget,
    boundary: ChainAccumulator,
    evaluation_key_digests: [Option<[u8; 32]>; HISTORY_STEP_CLASS_COUNT],
}

impl CheckedHistoryStepRetirementMatrices {
    pub const fn request_binding(&self) -> [u8; 32] {
        self.request_binding
    }
    pub const fn target(&self) -> &HistoryStepRetirementTarget {
        &self.target
    }
    pub fn boundary(&self) -> &ChainAccumulator {
        &self.boundary
    }
    pub const fn evaluation_key_digests(&self) -> &[Option<[u8; 32]>; HISTORY_STEP_CLASS_COUNT] {
        &self.evaluation_key_digests
    }
}

impl PendingHistoryStepRetirement {
    pub fn verify_matrix_evaluations(
        self,
        evaluations: &[HistoryStepRetirementEvaluation<'_>],
    ) -> Result<CheckedHistoryStepRetirementMatrices, RetirementEvaluationError> {
        if evaluations.len() != self.obligations().count() {
            return Err(RetirementEvaluationError::Coverage);
        }
        // Check all identities before doing any PCS verification. Ordering
        // rejects duplicates, an omitted non-selected lane and extra proofs.
        for (obligation, evaluation) in self.obligations().zip(evaluations) {
            if obligation.class_id != evaluation.class_id
                || obligation.shape != evaluation.key.shape()
                || obligation.matrix_digest != evaluation.key.matrix_digest()
            {
                return Err(RetirementEvaluationError::Identity);
            }
        }
        let mut evaluation_key_digests = [None; HISTORY_STEP_CLASS_COUNT];
        for (obligation, evaluation) in self.obligations().zip(evaluations) {
            evaluation
                .key
                .verify(self.request_binding, &obligation.claim, evaluation.proof)
                .map_err(RetirementEvaluationError::Proof)?;
            evaluation_key_digests[evaluation.class_id.index()] = Some(evaluation.key.digest());
        }
        Ok(CheckedHistoryStepRetirementMatrices {
            request_binding: self.request_binding,
            target: self.target,
            boundary: self.boundary,
            evaluation_key_digests,
        })
    }
}

#[derive(Debug)]
pub enum RetirementEvaluationError {
    Coverage,
    Identity,
    Proof(SparseEvaluationError),
}
impl core::fmt::Display for RetirementEvaluationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Coverage => {
                f.write_str("every live retirement lane requires exactly one evaluation proof")
            }
            Self::Identity => {
                f.write_str("retirement evaluation class, shape or matrix identity mismatch")
            }
            Self::Proof(error) => write!(f, "retirement matrix evaluation: {error}"),
        }
    }
}
impl std::error::Error for RetirementEvaluationError {}
