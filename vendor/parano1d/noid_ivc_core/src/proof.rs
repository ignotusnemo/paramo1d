//! Shared R1CS proof types and the Fiat-Shamir statement binding.
//!
//! These live in a backend-neutral module (rather than in `prover`) so the
//! verifier can name them without depending on the prove path. The prover
//! produces these structs; the verifier consumes them.

use crate::challenger::Challenger;
use crate::field::{F128, F256};
use crate::lincheck::{self, QuirkyPoint};
use crate::pcs::{self, Commitment};
use crate::r1cs::BlockR1cs;
use crate::zerocheck;
use serde::{Deserialize, Serialize};

/// Top-level R1CS proof: zerocheck + lincheck transcripts, plus two PCS
/// opening proofs (one per ZClaim). BaseFold backend.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct R1csProof {
    pub zerocheck: zerocheck::ZerocheckProof,
    pub lincheck: lincheck::LincheckProof,
    /// Batched PCS opening covering both the `ab` and `c` z-claims via one
    /// shared BaseFold sumcheck + FRI.
    pub pcs_open: pcs::BatchOpeningProof,
}

/// Top-level R1CS proof with the **Ligerito** PCS backend. Same zerocheck +
/// lincheck transcripts; pcs_open uses Ligerito instead of BaseFold.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct R1csProofLigerito {
    pub zerocheck: zerocheck::ZerocheckProof,
    pub lincheck: lincheck::LincheckProof,
    pub pcs_open: pcs::BatchOpeningProofLigerito,
}

/// Top-level **FieldR1cs** proof: field zerocheck + lincheck
/// transcripts, plus one batched quirky-direct PCS opening (BaseFold, no
/// ring-switch — the committed vector IS the F128-element witness).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FieldR1csProof {
    pub zerocheck: zerocheck::ZerocheckProof,
    pub lincheck: lincheck::LincheckProof,
    /// Batched quirky-direct opening covering the `ab` and `c` z-claims.
    pub pcs_open: pcs::BaseFoldProof,
}

/// Complete native proof for the C1 History algebraic profile.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct C1FieldR1csProof {
    pub zerocheck: zerocheck::field_c1::C1ZerocheckProof,
    pub lincheck: lincheck::c1::C1LincheckProof,
    pub pcs_open: pcs::C1BaseFoldProof,
}

/// Canonical statement byte encoding of the PCS parameters — shared by the
/// native statement bindings below and their in-trace twins, so the two can
/// never drift on serialization details.
pub fn pcs_params_statement_bytes(params: &pcs::PcsParams) -> Vec<u8> {
    bincode::serialize(params).expect("PcsParams serializes")
}

/// FieldR1cs statement binding — mirror of [`bind_statement`] with the field
/// instance digest and a distinct label.
pub fn bind_statement_field<Ch: Challenger>(
    challenger: &mut Ch,
    r1cs: &crate::field_r1cs::FieldR1cs,
    commitment: &Commitment,
) {
    bind_statement_field_parts(challenger, &r1cs.statement_digest(), commitment);
}

/// [`bind_statement_field`] with the instance digest supplied directly —
/// the entry the self-verification chain uses, where the digest of the
/// verified instance is data (an IO lane), not a baked constant.
pub fn bind_statement_field_parts<Ch: Challenger>(
    challenger: &mut Ch,
    statement_digest: &[u8; 32],
    commitment: &Commitment,
) {
    challenger.observe_label(b"history-field-r1cs");
    challenger.observe_bytes(statement_digest);
    challenger.observe_bytes(&pcs_params_statement_bytes(&commitment.params));
    challenger.observe_bytes(&commitment.root);
}

/// C1 statement binding. The distinct label prevents either algebraic
/// challenge schedule from replaying under the other profile.
pub fn bind_statement_field_c1<Ch: Challenger>(
    challenger: &mut Ch,
    r1cs: &crate::field_r1cs::FieldR1cs,
    commitment: &Commitment,
) {
    bind_statement_field_parts_c1(challenger, &r1cs.statement_digest(), commitment);
}

pub fn bind_statement_field_parts_c1<Ch: Challenger>(
    challenger: &mut Ch,
    statement_digest: &[u8; 32],
    commitment: &Commitment,
) {
    challenger.observe_label(b"history-field-r1cs-c1");
    challenger.observe_bytes(statement_digest);
    challenger.observe_bytes(&pcs_params_statement_bytes(&commitment.params));
    challenger.observe_bytes(&commitment.root);
}

/// The structural parameters of a FieldR1cs class — everything a
/// matrix-free verifier needs besides the statement digest.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldShape {
    pub m: usize,
    pub k_log: usize,
    pub k_skip: usize,
    pub const_pin: Option<usize>,
}

impl FieldShape {
    pub fn of(r1cs: &crate::field_r1cs::FieldR1cs) -> Self {
        Self {
            m: r1cs.m,
            k_log: r1cs.k_log,
            k_skip: r1cs.k_skip,
            const_pin: r1cs.const_pin,
        }
    }
}

/// A claim of the form `ẑ(point) = value` for the witness `z`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZClaim {
    pub point: QuirkyPoint,
    pub value: F128,
}

/// Two MLE evaluation claims on `z` that the PCS layer must verify.
///
/// Both `point.x_outer` parts differ; both `point.z_skip` and
/// `point.x_inner_rest` shapes match (one univariate-skip coord + multilinear
/// inner-rest), so this is "two quirky-shaped openings of `z`."
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R1csClaim {
    /// From lincheck: `ẑ(ab.point) = ab.value` — covers both `â` and `b̂` at
    /// the same point (their lincheck claims collapsed to a shared z-claim
    /// at a fresh quirky inner point).
    pub ab: ZClaim,
    /// From the zerocheck's extract_c interpolation: `ẑ(c.point) = c.value`.
    /// Bypasses lincheck because `C = I` ⇒ ĉ-claim is a direct z-claim.
    pub c: ZClaim,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct C1ZClaim {
    pub point: lincheck::c1::C1QuirkyPoint,
    pub value: F256,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct C1R1csClaim {
    pub ab: C1ZClaim,
    pub c: C1ZClaim,
}

/// Bind the Fiat-Shamir transcript to the statement: the R1CS instance digest
/// + the PCS commitment root. Call once at the top of every R1CS prove/verify
/// path, before any sub-protocol challenge is drawn. RandomChallenger ignores
/// these observations; FsChallenger uses them to defeat statement substitution.
pub fn bind_statement<Ch: Challenger>(
    challenger: &mut Ch,
    r1cs: &BlockR1cs,
    commitment: &Commitment,
) {
    challenger.observe_label(b"history-r1cs");
    challenger.observe_bytes(&r1cs.statement_digest());
    challenger.observe_bytes(&pcs_params_statement_bytes(&commitment.params));
    challenger.observe_bytes(&commitment.root);
}
