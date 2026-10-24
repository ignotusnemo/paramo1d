// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Atomic self-recursive `HistoryStep` relation and its verifier traces.

pub mod block_slots;
pub mod history_step;
pub mod history_step_bank;
pub mod shape;
pub mod trace;
pub mod zk_auth_capsule_schedule;

/// Optional row-accounting checkpoint used while freezing the four relation
/// shapes. It has no effect unless explicitly enabled by release tooling.
pub(crate) fn row_ledger_mark(
    builder: &noid_ivc_core::field_circuit::FieldR1csBuilder,
    last: &mut usize,
    label: &str,
) {
    if std::env::var_os("NOID_ROW_LEDGER").is_some() {
        let now = builder.num_wires();
        eprintln!(
            "[ledger] {label:<32} +{:>9}  (total {:>9})",
            now - *last,
            now
        );
        *last = now;
    }
}

/// Expand a naturally dyadic one-block Field trace to its frozen protocol
/// shape without adding constraints to the zero tail.
pub(crate) fn expand_empty_field_tail(
    mut r1cs: noid_ivc_core::field_r1cs::FieldR1cs,
    mut witness: Vec<noid_ivc_core::field::F128>,
    shape: noid_ivc_core::proof::FieldShape,
) -> (
    noid_ivc_core::field_r1cs::FieldR1cs,
    Vec<noid_ivc_core::field::F128>,
) {
    use noid_ivc_core::field::F128;

    assert_eq!(r1cs.m, r1cs.k_log, "builder emits one base block");
    assert_eq!(shape.m, shape.k_log, "class must use one base block");
    assert_eq!(r1cs.k_skip, shape.k_skip, "class k_skip drift");
    assert_eq!(r1cs.const_pin, shape.const_pin, "class const pin drift");
    assert!(r1cs.m <= shape.m, "cannot shrink a built Field class");
    assert!(
        r1cs.digest_cache.get().is_none() && r1cs.csc_cache.get().is_none(),
        "padding must precede matrix digest/CSC caching"
    );
    let natural_rows = 1usize << r1cs.k_log;
    let target_rows = 1usize << shape.k_log;
    assert_eq!(witness.len(), natural_rows, "natural witness size");
    assert!(
        witness[r1cs.useful_rows..]
            .iter()
            .all(|value| *value == F128::ZERO),
        "natural builder padding witness must be zero"
    );
    for matrix in [&r1cs.a_0, &r1cs.b_0] {
        assert!(
            matrix.row_offsets[r1cs.useful_rows..]
                .windows(2)
                .all(|pair| pair[0] == pair[1]),
            "natural builder padding rows must be empty"
        );
    }
    let expand = |matrix: &mut noid_ivc_core::field_r1cs::SparseFieldMatrix| {
        let terminal = *matrix.row_offsets.last().expect("CSR terminal offset");
        matrix.row_offsets.resize(target_rows + 1, terminal);
        matrix.num_rows = target_rows;
        matrix.num_cols = target_rows;
    };
    expand(&mut r1cs.a_0);
    expand(&mut r1cs.b_0);
    witness.resize(target_rows, F128::ZERO);
    r1cs.m = shape.m;
    r1cs.k_log = shape.k_log;
    r1cs.validate_shape();
    assert!(
        witness[r1cs.useful_rows..]
            .iter()
            .all(|value| *value == F128::ZERO),
        "expanded Field padding witness must be zero"
    );
    (r1cs, witness)
}
