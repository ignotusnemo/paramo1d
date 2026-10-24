use crate::mle::eq::eq_ind_partial_eval;
use crate::{Block128, TowerField};

/// Split an MLE of length 2^full_log into 2^(full_log - base_log) slices of length 2^base_log.
///
/// The split is along the high-order variables: slice index `s` contains evaluations
/// at points (low, s) where `low` ranges over {0,1}^base_log.
pub fn split_mle_into_slices(
    mle: &[Block128],
    full_log: usize,
    base_log: usize,
) -> Vec<Vec<Block128>> {
    assert!(base_log <= full_log);
    assert_eq!(mle.len(), 1 << full_log);

    let num_slices = 1usize << (full_log - base_log);
    let slice_len = 1usize << base_log;

    (0..num_slices)
        .map(|s_idx| mle[s_idx * slice_len..(s_idx + 1) * slice_len].to_vec())
        .collect()
}

/// Reconstruct the value of the original MLE at point (r_low, r_high) from per-slice
/// evaluations at r_low.
///
/// Given `slice_values[b]` = f_b(r_low) for each b in {0,1}^k, computes:
///   f(r_low, r_high) = sum_{b} eq(r_high, b) * f_b(r_low)
pub fn reconstruct_from_slices(slice_values: &[Block128], r_high: &[Block128]) -> Block128 {
    let k = r_high.len();
    assert_eq!(slice_values.len(), 1 << k);

    let eq_weights = eq_ind_partial_eval(r_high);

    let mut result = Block128::ZERO;
    for (val, weight) in slice_values.iter().zip(eq_weights.iter()) {
        result += *weight * *val;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mle::evaluate::evaluate_slice;
    use rand::Rng;

    #[test]
    fn test_split_roundtrip() {
        let mut rng = rand::thread_rng();
        let full_log = 8;
        let base_log = 5;
        let mle: Vec<Block128> = (0..(1 << full_log))
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect();

        let r_low: Vec<Block128> = (0..base_log)
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect();
        let r_high: Vec<Block128> = (0..(full_log - base_log))
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect();

        let slices = split_mle_into_slices(&mle, full_log, base_log);
        assert_eq!(slices.len(), 1 << (full_log - base_log));
        assert_eq!(slices[0].len(), 1 << base_log);

        let slice_values: Vec<Block128> =
            slices.iter().map(|s| evaluate_slice(s, &r_low)).collect();

        let reconstructed = reconstruct_from_slices(&slice_values, &r_high);

        let mut full_point = r_low.clone();
        full_point.extend_from_slice(&r_high);
        let expected = evaluate_slice(&mle, &full_point);

        assert_eq!(reconstructed, expected);
    }

    #[test]
    fn test_split_single_slice() {
        let mut rng = rand::thread_rng();
        let log = 6;
        let mle: Vec<Block128> = (0..(1 << log))
            .map(|_| Block128::from(rng.gen::<u128>()))
            .collect();

        let slices = split_mle_into_slices(&mle, log, log);
        assert_eq!(slices.len(), 1);
        assert_eq!(slices[0], mle);
    }
}
