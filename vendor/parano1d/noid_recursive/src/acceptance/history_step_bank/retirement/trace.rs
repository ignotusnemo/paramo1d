//! Constraint twin of the retirement reduction, not a complete fork relation.
//!
//! The caller must derive and bind the request digest to the scheduled banks,
//! exact parent header, boundary and every legacy obligation. It must obtain
//! `fresh` and `incoming` from the verified parent, carry non-selected lanes,
//! and close all resulting matrix claims. This gadget does none of that glue.

use super::FOLD_DOMAIN;
use crate::acceptance::trace::matrix_fold::{
    verify_matrix_claim_fold_c1_trace, C1FreshLincheckClaimTrace, C1MatrixAccClaimTrace,
    C1MatrixFoldProofTrace,
};
use crate::acceptance::trace::{mul, pin_eq};
use noid_ivc_core::field::F128;
use noid_ivc_core::field_circuit::{FieldR1csBuilder, FsChannelTrace, LinExpr};

/// Bind the existing C1 matrix fold to the retirement request. Digest lanes
/// use `fs_pack_bytes_lanes`: raw 16-byte little-endian halves, matching the
/// native `observe_bytes` call. They are not tower-to-flat digest limbs.
pub fn verify_retirement_fold_trace(
    builder: &mut FieldR1csBuilder,
    k_log: usize,
    k_skip: usize,
    request_digest: &[LinExpr; 2],
    fresh: &C1FreshLincheckClaimTrace,
    incoming: &C1MatrixAccClaimTrace,
    incoming_live: &LinExpr,
    proof: &C1MatrixFoldProofTrace,
) -> C1MatrixAccClaimTrace {
    let dead = incoming_live.add_const(F128::ONE);
    let boolean = mul(builder, incoming_live, &dead);
    pin_eq(builder, &boolean, &LinExpr::zero());
    for coordinate in incoming
        .point
        .iter()
        .chain(core::iter::once(&incoming.value))
    {
        for limb in [&coordinate.lo, &coordinate.hi] {
            let unused = mul(builder, &dead, limb);
            pin_eq(builder, &unused, &LinExpr::zero());
        }
    }
    let mut channel = FsChannelTrace::new_c1(builder, FOLD_DOMAIN);
    channel.observe_lanes(builder, 32, request_digest);
    verify_matrix_claim_fold_c1_trace(
        builder,
        &mut channel,
        k_log,
        k_skip,
        fresh,
        incoming,
        incoming_live,
        proof,
    )
}
