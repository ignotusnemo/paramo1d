//! Shared-row tuple permutation adapter.
//!
//! A scalar [`crate::permutation`] argument can prove a permutation of a tuple
//! without random linear compression by flattening each tuple lane into a
//! separate block and repeating one row permutation in every block.  The
//! This module only defines the exact native flattening and its algebraic
//! tests. A proof integration must additionally prove that `s_sigma` really
//! has the lifted form `lane * rows + sigma_base[row]`. Opening an arbitrary
//! committed `s_sigma` evaluation is insufficient: adding a lane-tag offset
//! can shift whole lane cosets. A post-commitment tuple compression repeated
//! identically in every lane block avoids that ambiguity, but still needs a
//! verifier-authoritative base row permutation.
//!
//! This adapter is **not** a standalone Fiat--Shamir protocol. Callers must
//! commit/bind the source lanes, demand lanes, and shared base permutation
//! before invoking `permutation::prove`, prove the lifted-permutation form,
//! then open their reduced evaluations.

use crate::field::F128;

/// Scalar permutation instance obtained by lane-block flattening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlattenedTuplePermutation {
    /// Number of real tuple lanes. Remaining lane blocks are canonical zero.
    pub tuple_lanes: usize,
    /// Dyadic number of lane blocks in the flattened table.
    pub lane_blocks: usize,
    /// Source tuple lanes, lane-major (`lane * rows + row`).
    pub source: Vec<F128>,
    /// Demand tuple lanes in the same layout.
    pub demand: Vec<F128>,
    /// `lane * rows + sigma[row]`, repeating one row permutation in every
    /// lane block.
    pub permutation: Vec<usize>,
}

impl FlattenedTuplePermutation {
    #[inline]
    pub fn rows(&self) -> usize {
        self.source.len() / self.lane_blocks
    }

    #[inline]
    pub fn log_size(&self) -> usize {
        self.source.len().trailing_zeros() as usize
    }
}

/// Flatten `LANES`-wide source/demand records under one shared row
/// permutation.
///
/// `row_permutation[x]` uses [`crate::permutation`]'s orientation:
/// `source[row_permutation[x]] == demand[x]` for an honest instance.
/// `LANES` is padded to its next power of two with all-zero lane blocks, so the
/// scalar table remains dyadic without giving padding a prover-controlled
/// value.
pub fn flatten_shared_row_permutation<const LANES: usize>(
    source_rows: &[[F128; LANES]],
    demand_rows: &[[F128; LANES]],
    row_permutation: &[usize],
) -> FlattenedTuplePermutation {
    assert!(LANES > 0, "tuple must have at least one lane");
    let rows = source_rows.len();
    assert_eq!(demand_rows.len(), rows);
    assert_eq!(row_permutation.len(), rows);
    assert!(
        rows >= 2 && rows.is_power_of_two(),
        "row count must be dyadic"
    );
    let mut seen = vec![false; rows];
    for &target in row_permutation {
        assert!(target < rows, "row permutation target out of range");
        assert!(!seen[target], "row permutation target repeated");
        seen[target] = true;
    }

    let lane_blocks = LANES.next_power_of_two();
    let len = lane_blocks * rows;
    let mut source = vec![F128::ZERO; len];
    let mut demand = vec![F128::ZERO; len];
    let mut permutation = vec![0usize; len];
    for lane in 0..lane_blocks {
        let base = lane * rows;
        for row in 0..rows {
            if lane < LANES {
                source[base + row] = source_rows[row][lane];
                demand[base + row] = demand_rows[row][lane];
            }
            permutation[base + row] = base + row_permutation[row];
        }
    }
    FlattenedTuplePermutation {
        tuple_lanes: LANES,
        lane_blocks,
        source,
        demand,
        permutation,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::{Challenger, FsChallenger};
    use crate::permutation::{VerifyError, prove, verify};

    const LANES: usize = 5;

    fn source_rows(rows: usize) -> Vec<[F128; LANES]> {
        (0..rows)
            .map(|row| {
                std::array::from_fn(|lane| {
                    F128::new(
                        (10_000 * lane + 101 * row + 7) as u64,
                        (30_000 * lane + 211 * row + 19) as u64,
                    )
                })
            })
            .collect()
    }

    fn demand_for(source: &[[F128; LANES]], sigma: &[usize]) -> Vec<[F128; LANES]> {
        sigma.iter().map(|&source_row| source[source_row]).collect()
    }

    fn bind(ch: &mut impl Challenger, instance: &FlattenedTuplePermutation) {
        // Test-only stand-in for the production precommit + reduced opening.
        ch.observe_f128_slice(&instance.source);
        ch.observe_f128_slice(&instance.demand);
        for &target in &instance.permutation {
            ch.observe_f128(F128::new(target as u64, 0));
        }
    }

    fn prove_and_verify(instance: &FlattenedTuplePermutation) -> Result<(), VerifyError> {
        let mut prover = FsChallenger::new(b"tuple-permutation-test");
        bind(&mut prover, instance);
        let (proof, _) = prove(
            &instance.source,
            &instance.demand,
            &instance.permutation,
            &mut prover,
        );
        let mut verifier = FsChallenger::new(b"tuple-permutation-test");
        bind(&mut verifier, instance);
        verify(instance.log_size(), &proof, &mut verifier).map(|_| ())
    }

    fn mle_eval(table: &[F128], point: &[F128]) -> F128 {
        assert_eq!(table.len(), 1usize << point.len());
        let mut values = table.to_vec();
        for &r in point {
            for index in 0..values.len() / 2 {
                values[index] = values[2 * index] * (F128::ONE + r) + values[2 * index + 1] * r;
            }
            values.truncate(values.len() / 2);
        }
        values[0]
    }

    #[test]
    fn one_scalar_argument_proves_all_tuple_lanes_under_one_row_permutation() {
        let source = source_rows(8);
        let sigma = [5, 2, 7, 0, 6, 1, 3, 4];
        let demand = demand_for(&source, &sigma);
        let instance = flatten_shared_row_permutation(&source, &demand, &sigma);

        assert_eq!(instance.tuple_lanes, LANES);
        assert_eq!(instance.lane_blocks, 8);
        assert_eq!(instance.rows(), 8);
        assert!(instance.source[LANES * 8..].iter().all(|v| v.is_zero()));
        assert!(instance.demand[LANES * 8..].iter().all(|v| v.is_zero()));
        prove_and_verify(&instance).unwrap();
    }

    #[test]
    fn reduced_evals_decompose_into_row_columns_and_one_shared_sigma() {
        let source = source_rows(8);
        let sigma = [5, 2, 7, 0, 6, 1, 3, 4];
        let demand = demand_for(&source, &sigma);
        let instance = flatten_shared_row_permutation(&source, &demand, &sigma);
        let mut prover = FsChallenger::new(b"tuple-permutation-test");
        bind(&mut prover, &instance);
        let (_proof, claim) = prove(
            &instance.source,
            &instance.demand,
            &instance.permutation,
            &mut prover,
        );

        let row_log = instance.rows().trailing_zeros() as usize;
        let (rho_row, rho_lane) = claim.rho.split_at(row_log);
        let lane_weight = |lane: usize| {
            rho_lane
                .iter()
                .enumerate()
                .fold(F128::ONE, |weight, (bit, &r)| {
                    weight
                        * if lane >> bit & 1 == 1 {
                            r
                        } else {
                            F128::ONE + r
                        }
                })
        };
        let source_eval = (0..LANES).fold(F128::ZERO, |sum, lane| {
            let column: Vec<_> = source.iter().map(|row| row[lane]).collect();
            sum + lane_weight(lane) * mle_eval(&column, rho_row)
        });
        let demand_eval = (0..LANES).fold(F128::ZERO, |sum, lane| {
            let column: Vec<_> = demand.iter().map(|row| row[lane]).collect();
            sum + lane_weight(lane) * mle_eval(&column, rho_row)
        });
        assert_eq!(claim.f_eval, source_eval);
        assert_eq!(claim.g_eval, demand_eval);

        let sigma_column: Vec<_> = sigma.iter().map(|&row| F128::new(row as u64, 0)).collect();
        let mut expected_sigma = mle_eval(&sigma_column, rho_row);
        for (lane_bit, &rho) in rho_lane.iter().enumerate() {
            expected_sigma += F128::new(1u64 << (row_log + lane_bit), 0) * rho;
        }
        assert_eq!(claim.s_sigma_eval, expected_sigma);
    }

    #[test]
    fn independently_permuting_one_lane_is_not_a_shared_tuple_permutation() {
        let source = source_rows(8);
        let sigma = [5, 2, 7, 0, 6, 1, 3, 4];
        let other = [1, 6, 0, 4, 3, 7, 5, 2];
        let mut demand = demand_for(&source, &sigma);
        for row in 0..8 {
            demand[row][3] = source[other[row]][3];
        }
        let instance = flatten_shared_row_permutation(&source, &demand, &sigma);
        assert!(prove_and_verify(&instance).is_err());
    }

    #[test]
    fn changed_tuple_value_and_lane_swap_are_rejected() {
        let source = source_rows(8);
        let sigma = [5, 2, 7, 0, 6, 1, 3, 4];
        let mut changed = demand_for(&source, &sigma);
        changed[4][2] += F128::ONE;
        let changed_instance = flatten_shared_row_permutation(&source, &changed, &sigma);
        assert!(prove_and_verify(&changed_instance).is_err());

        let mut swapped = demand_for(&source, &sigma);
        for row in 0..8 {
            swapped[row].swap(0, 1);
        }
        let swapped_instance = flatten_shared_row_permutation(&source, &swapped, &sigma);
        assert!(prove_and_verify(&swapped_instance).is_err());
    }

    #[test]
    #[should_panic(expected = "row permutation target repeated")]
    fn malformed_base_permutation_is_rejected_before_flattening() {
        let source = source_rows(8);
        let demand = source.clone();
        let _ = flatten_shared_row_permutation(&source, &demand, &[0, 0, 2, 3, 4, 5, 6, 7]);
    }
}
