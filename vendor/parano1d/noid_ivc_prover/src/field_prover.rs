//! Top-level **FieldR1cs** prover: commit → bind → field zerocheck →
//! field lincheck → batched quirky-direct PCS open. Structural mirror of
//! [`crate::prover::prove`] on the F128-element witness; the verifier is
//! `noid_ivc_core::verifier::verify_field`.

use noid_ivc_core::challenger::Challenger;
use noid_ivc_core::field::{F128, F256};
use noid_ivc_core::field_r1cs::{CompactFieldR1cs, FieldProverRelation, FieldR1cs};
use noid_ivc_core::lincheck::{self, LocallyAuthoredFreshLincheckCapture, QuirkyPoint};
use noid_ivc_core::pcs::{self, C1QuirkyDirectClaim, Commitment, PcsParams, QuirkyDirectClaim};
use noid_ivc_core::proof::{
    C1FieldR1csProof, C1R1csClaim, C1ZClaim, FieldR1csProof, R1csClaim, ZClaim,
    bind_statement_field_parts, bind_statement_field_parts_c1,
};
use noid_ivc_core::public_io::{
    PublicIoSpec, assert_witness_matches_io, bind_post_commit_class, bind_public_io,
    bind_public_io_c1,
};
use noid_ivc_core::zerocheck;
use std::sync::atomic::{AtomicBool, Ordering};

/// Cooperative cancellation of a locally authored proof. Cancellation is
/// checked only between transcript phases, so a phase is either completed or
/// its partial values are dropped before control returns to the caller.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProverCancelled;

impl core::fmt::Display for ProverCancelled {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str("prover cancelled")
    }
}

impl std::error::Error for ProverCancelled {}

#[derive(Clone, Copy)]
enum FreshLincheckCaptureRequest {
    Disabled,
    Enabled,
}

/// Resident set size in MiB (Linux `/proc/self/status`) for the env-gated
/// per-phase memory column: `(current VmRSS, peak VmHWM)`. VmHWM is the
/// high-water mark since process start — monotone, so a jump between two lap
/// prints reveals an intra-phase transient (e.g. the lincheck parallel fold's
/// per-thread combs) that the lap-boundary VmRSS misses. Returns `(0, 0)` where
/// unavailable.
fn vmrss_mb() -> (u64, u64) {
    let field = |s: &str, key: &str| -> u64 {
        s.lines()
            .find(|l| l.starts_with(key))
            .and_then(|l| l.split_whitespace().nth(1))
            .and_then(|kb| kb.parse::<u64>().ok())
            .map(|kb| kb / 1024)
            .unwrap_or(0)
    };
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .map(|s| (field(&s, "VmRSS:"), field(&s, "VmHWM:")))
        .unwrap_or((0, 0))
}

/// Opaque capability handed only to a causally post-commit prover callback.
///
/// It delegates the exact enclosing challenger and owns an internal PCS claim
/// sink.  The constructor and sink extraction stay private, so callers cannot
/// manufacture the capability or forget to return the accumulated claims to
/// the enclosing proof.
pub struct FieldPostCommitProverContext<'a, Ch> {
    witness: &'a [F128],
    commitment: &'a Commitment,
    total_vars: usize,
    challenger: &'a mut Ch,
    claims: Vec<QuirkyDirectClaim>,
    c1_claims: Vec<C1QuirkyDirectClaim>,
}

impl<'a, Ch> FieldPostCommitProverContext<'a, Ch> {
    fn new(
        witness: &'a [F128],
        commitment: &'a Commitment,
        total_vars: usize,
        challenger: &'a mut Ch,
    ) -> Self {
        Self {
            witness,
            commitment,
            total_vars,
            challenger,
            claims: Vec::new(),
            c1_claims: Vec::new(),
        }
    }

    fn finish(self) -> Vec<QuirkyDirectClaim> {
        assert!(
            self.c1_claims.is_empty(),
            "extension-field claims require a C1 enclosing proof"
        );
        self.claims
    }

    fn finish_c1(self) -> (Vec<QuirkyDirectClaim>, Vec<C1QuirkyDirectClaim>) {
        (self.claims, self.c1_claims)
    }

    pub fn witness(&self) -> &'a [F128] {
        self.witness
    }

    pub fn commitment(&self) -> &'a Commitment {
        self.commitment
    }

    pub fn total_vars(&self) -> usize {
        self.total_vars
    }

    pub fn append_claim(&mut self, claim: QuirkyDirectClaim) {
        self.claims.push(claim);
    }

    pub fn append_claims(&mut self, claims: impl IntoIterator<Item = QuirkyDirectClaim>) {
        self.claims.extend(claims);
    }

    pub fn append_c1_claim(&mut self, claim: C1QuirkyDirectClaim) {
        self.c1_claims.push(claim);
    }

    pub fn append_c1_claims(&mut self, claims: impl IntoIterator<Item = C1QuirkyDirectClaim>) {
        self.c1_claims.extend(claims);
    }

    pub fn claim_count(&self) -> usize {
        self.claims.len()
    }

    pub fn c1_claim_count(&self) -> usize {
        self.c1_claims.len()
    }
}

impl<Ch: Challenger> Challenger for FieldPostCommitProverContext<'_, Ch> {
    fn observe_label(&mut self, label: &[u8]) {
        self.challenger.observe_label(label);
    }

    fn observe_f128(&mut self, value: F128) {
        self.challenger.observe_f128(value);
    }

    fn observe_f128_slice(&mut self, values: &[F128]) {
        self.challenger.observe_f128_slice(values);
    }

    fn observe_f256(&mut self, value: F256) {
        self.challenger.observe_f256(value);
    }

    fn observe_f256_slice(&mut self, values: &[F256]) {
        self.challenger.observe_f256_slice(values);
    }

    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.challenger.observe_bytes(bytes);
    }

    fn sample_f128(&mut self) -> F128 {
        self.challenger.sample_f128()
    }

    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        self.challenger.sample_f128_vec(n)
    }

    fn sample_f256(&mut self) -> F256 {
        self.challenger.sample_f256()
    }

    fn sample_f256_vec(&mut self, n: usize) -> Vec<F256> {
        self.challenger.sample_f256_vec(n)
    }

    fn grind_pow(&mut self, bits: u32) -> u64 {
        self.challenger.grind_pow(bits)
    }

    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        self.challenger.verify_pow(nonce, bits)
    }
}

/// Prove a FieldR1cs instance on a witness of `2^m` F128 elements.
///
/// `pcs_params.m` counts **bits** (the PCS packing convention), so it must be
/// `r1cs.m + LOG_PACKING`: the committed vector is the witness itself, one
/// F128 element per packed slot, no repacking.
///
/// Returns the proof bundle, the witness commitment, and the two z-claims
/// (`ab` from lincheck, `c` from the zerocheck's extract_c — both quirky
/// points over the element variables).
pub fn prove_field<Ch: Challenger>(
    r1cs: &FieldR1cs,
    z: &[F128],
    pcs_params: &PcsParams,
    challenger: &mut Ch,
) -> (FieldR1csProof, Commitment, R1csClaim) {
    let (proof, (), commitment, claim, capture) = prove_field_inner(
        r1cs,
        z,
        pcs_params,
        None,
        FreshLincheckCaptureRequest::Disabled,
        challenger,
        |_, _, _| ((), Vec::new()),
    );
    debug_assert!(capture.is_none());
    (proof, commitment, claim)
}

/// Closed native C1 History proof path. This deliberately has no legacy
/// profile selector: callers choose the C1 entry point and receive only the
/// wide proof type.
pub fn prove_field_c1<Ch: Challenger>(
    r1cs: &FieldR1cs,
    witness: &[F128],
    pcs_params: &PcsParams,
    challenger: &mut Ch,
) -> (C1FieldR1csProof, Commitment, C1R1csClaim) {
    let (proof, (), commitment, claim, capture) = prove_field_c1_inner(
        r1cs,
        witness,
        pcs_params,
        None,
        false,
        None,
        challenger,
        |_, _, _| ((), (Vec::new(), Vec::new())),
    )
    .expect("an uncancellable C1 proof cannot be cancelled");
    debug_assert!(capture.is_none());
    (proof, commitment, claim)
}

/// [`prove_field`] over an immutable canonical artifact authenticated by
/// [`CompactFieldR1cs::open`].  The statement and proof transcript are
/// byte-identical to the resident-CSR path; only A/B application and the
/// lincheck row fold read the compact backing directly.
pub fn prove_field_compact<Ch: Challenger>(
    r1cs: &CompactFieldR1cs,
    z: &[F128],
    pcs_params: &PcsParams,
    challenger: &mut Ch,
) -> (FieldR1csProof, Commitment, R1csClaim) {
    let (proof, (), commitment, claim, capture) = prove_field_inner(
        r1cs,
        z,
        pcs_params,
        None,
        FreshLincheckCaptureRequest::Disabled,
        challenger,
        |_, _, _| ((), Vec::new()),
    );
    debug_assert!(capture.is_none());
    (proof, commitment, claim)
}

pub fn prove_field_compact_c1<Ch: Challenger>(
    r1cs: &CompactFieldR1cs,
    witness: &[F128],
    pcs_params: &PcsParams,
    challenger: &mut Ch,
) -> (C1FieldR1csProof, Commitment, C1R1csClaim) {
    let (proof, (), commitment, claim, capture) = prove_field_c1_inner(
        r1cs,
        witness,
        pcs_params,
        None,
        false,
        None,
        challenger,
        |_, _, _| ((), (Vec::new(), Vec::new())),
    )
    .expect("an uncancellable compact C1 proof cannot be cancelled");
    debug_assert!(capture.is_none());
    (proof, commitment, claim)
}

pub fn prove_field_c1_capturing_fresh<Ch: Challenger>(
    r1cs: &FieldR1cs,
    witness: &[F128],
    pcs_params: &PcsParams,
    challenger: &mut Ch,
) -> (
    C1FieldR1csProof,
    Commitment,
    C1R1csClaim,
    lincheck::c1::C1LocallyAuthoredFreshLincheckCapture,
) {
    let (proof, (), commitment, claim, capture) = prove_field_c1_inner(
        r1cs,
        witness,
        pcs_params,
        None,
        true,
        None,
        challenger,
        |_, _, _| ((), (Vec::new(), Vec::new())),
    )
    .expect("an uncancellable captured C1 proof cannot be cancelled");
    (
        proof,
        commitment,
        claim,
        capture.expect("capturing C1 field prover returns its lincheck claim"),
    )
}

pub fn prove_field_compact_c1_capturing_fresh<Ch: Challenger>(
    r1cs: &CompactFieldR1cs,
    witness: &[F128],
    pcs_params: &PcsParams,
    challenger: &mut Ch,
) -> (
    C1FieldR1csProof,
    Commitment,
    C1R1csClaim,
    lincheck::c1::C1LocallyAuthoredFreshLincheckCapture,
) {
    let (proof, (), commitment, claim, capture) = prove_field_c1_inner(
        r1cs,
        witness,
        pcs_params,
        None,
        true,
        None,
        challenger,
        |_, _, _| ((), (Vec::new(), Vec::new())),
    )
    .expect("an uncancellable captured compact C1 proof cannot be cancelled");
    (
        proof,
        commitment,
        claim,
        capture.expect("capturing compact C1 field prover returns its lincheck claim"),
    )
}

/// Production C1 proof with a public-IO envelope and a causally post-commit
/// auxiliary protocol. Auxiliary F128 witness claims are embedded into the
/// same extension-field PCS batch; the callback retains its existing typed
/// sidecar API and exact transcript order.
#[allow(clippy::too_many_arguments)]
pub fn prove_field_c1_with_public_io_and_post_commit_context<Ch, Aux, PostCommit>(
    r1cs: &FieldR1cs,
    witness: &[F128],
    pcs_params: &PcsParams,
    spec: &PublicIoSpec,
    io: &[F128],
    post_commit_class_digest: &[u8; 32],
    challenger: &mut Ch,
    post_commit: PostCommit,
) -> (C1FieldR1csProof, Aux, Commitment, C1R1csClaim)
where
    Ch: Challenger,
    PostCommit: FnOnce(&mut FieldPostCommitProverContext<'_, Ch>) -> Aux,
{
    let (proof, auxiliary, commitment, claim, capture) = prove_field_c1_inner(
        r1cs,
        witness,
        pcs_params,
        Some((spec, io)),
        false,
        None,
        challenger,
        |witness, commitment, challenger| {
            bind_post_commit_class(challenger, post_commit_class_digest);
            let mut context =
                FieldPostCommitProverContext::new(witness, commitment, r1cs.m, challenger);
            let auxiliary = post_commit(&mut context);
            (auxiliary, context.finish_c1())
        },
    )
    .expect("an uncancellable public-IO C1 proof cannot be cancelled");
    debug_assert!(capture.is_none());
    (proof, auxiliary, commitment, claim)
}

/// Compact authenticated-relation twin of
/// [`prove_field_c1_with_public_io_and_post_commit_context`].
#[allow(clippy::too_many_arguments)]
pub fn prove_field_compact_c1_with_public_io_and_post_commit_context<Ch, Aux, PostCommit>(
    r1cs: &CompactFieldR1cs,
    witness: &[F128],
    pcs_params: &PcsParams,
    spec: &PublicIoSpec,
    io: &[F128],
    post_commit_class_digest: &[u8; 32],
    challenger: &mut Ch,
    post_commit: PostCommit,
) -> (C1FieldR1csProof, Aux, Commitment, C1R1csClaim)
where
    Ch: Challenger,
    PostCommit: FnOnce(&mut FieldPostCommitProverContext<'_, Ch>) -> Aux,
{
    let total_vars = r1cs.shape().m;
    let (proof, auxiliary, commitment, claim, capture) = prove_field_c1_inner(
        r1cs,
        witness,
        pcs_params,
        Some((spec, io)),
        false,
        None,
        challenger,
        |witness, commitment, challenger| {
            bind_post_commit_class(challenger, post_commit_class_digest);
            let mut context =
                FieldPostCommitProverContext::new(witness, commitment, total_vars, challenger);
            let auxiliary = post_commit(&mut context);
            (auxiliary, context.finish_c1())
        },
    )
    .expect("an uncancellable public-IO compact C1 proof cannot be cancelled");
    debug_assert!(capture.is_none());
    (proof, auxiliary, commitment, claim)
}

/// Cancellable production twin of
/// [`prove_field_c1_with_public_io_and_post_commit_context`]. The transcript
/// and returned proof are identical when the cancellation flag stays clear.
#[allow(clippy::too_many_arguments)]
pub fn prove_field_c1_with_public_io_and_post_commit_context_cancellable<Ch, Aux, PostCommit>(
    r1cs: &FieldR1cs,
    witness: &[F128],
    pcs_params: &PcsParams,
    spec: &PublicIoSpec,
    io: &[F128],
    post_commit_class_digest: &[u8; 32],
    cancellation: &AtomicBool,
    challenger: &mut Ch,
    post_commit: PostCommit,
) -> Result<(C1FieldR1csProof, Aux, Commitment, C1R1csClaim), ProverCancelled>
where
    Ch: Challenger,
    PostCommit: FnOnce(&mut FieldPostCommitProverContext<'_, Ch>) -> Aux,
{
    let (proof, auxiliary, commitment, claim, capture) = prove_field_c1_inner(
        r1cs,
        witness,
        pcs_params,
        Some((spec, io)),
        false,
        Some(cancellation),
        challenger,
        |witness, commitment, challenger| {
            bind_post_commit_class(challenger, post_commit_class_digest);
            let mut context =
                FieldPostCommitProverContext::new(witness, commitment, r1cs.m, challenger);
            let auxiliary = post_commit(&mut context);
            (auxiliary, context.finish_c1())
        },
    )?;
    debug_assert!(capture.is_none());
    Ok((proof, auxiliary, commitment, claim))
}

/// Compact-matrix cancellable twin of
/// [`prove_field_compact_c1_with_public_io_and_post_commit_context`].
#[allow(clippy::too_many_arguments)]
pub fn prove_field_compact_c1_with_public_io_and_post_commit_context_cancellable<
    Ch,
    Aux,
    PostCommit,
>(
    r1cs: &CompactFieldR1cs,
    witness: &[F128],
    pcs_params: &PcsParams,
    spec: &PublicIoSpec,
    io: &[F128],
    post_commit_class_digest: &[u8; 32],
    cancellation: &AtomicBool,
    challenger: &mut Ch,
    post_commit: PostCommit,
) -> Result<(C1FieldR1csProof, Aux, Commitment, C1R1csClaim), ProverCancelled>
where
    Ch: Challenger,
    PostCommit: FnOnce(&mut FieldPostCommitProverContext<'_, Ch>) -> Aux,
{
    let total_vars = r1cs.shape().m;
    let (proof, auxiliary, commitment, claim, capture) = prove_field_c1_inner(
        r1cs,
        witness,
        pcs_params,
        Some((spec, io)),
        false,
        Some(cancellation),
        challenger,
        |witness, commitment, challenger| {
            bind_post_commit_class(challenger, post_commit_class_digest);
            let mut context =
                FieldPostCommitProverContext::new(witness, commitment, total_vars, challenger);
            let auxiliary = post_commit(&mut context);
            (auxiliary, context.finish_c1())
        },
    )?;
    debug_assert!(capture.is_none());
    Ok((proof, auxiliary, commitment, claim))
}

fn prove_field_c1_inner<R, Ch, Aux, PostCommit>(
    r1cs: &R,
    witness: &[F128],
    pcs_params: &PcsParams,
    public_io: Option<(&PublicIoSpec, &[F128])>,
    capture_fresh: bool,
    cancellation: Option<&AtomicBool>,
    challenger: &mut Ch,
    post_commit: PostCommit,
) -> Result<
    (
        C1FieldR1csProof,
        Aux,
        Commitment,
        C1R1csClaim,
        Option<lincheck::c1::C1LocallyAuthoredFreshLincheckCapture>,
    ),
    ProverCancelled,
>
where
    R: FieldProverRelation,
    Ch: Challenger,
    PostCommit: FnOnce(
        &[F128],
        &Commitment,
        &mut Ch,
    ) -> (Aux, (Vec<QuirkyDirectClaim>, Vec<C1QuirkyDirectClaim>)),
{
    let check_cancelled = || {
        if cancellation.is_some_and(|flag| flag.load(Ordering::Acquire)) {
            Err(ProverCancelled)
        } else {
            Ok(())
        }
    };
    check_cancelled()?;
    let timing = std::env::var_os("NOIDH_FIELD_PROVE_TIMING").is_some();
    let mut phase = std::time::Instant::now();
    let lap = |label: &str, phase: &mut std::time::Instant| {
        if timing {
            eprintln!(
                "[field-c1-prover] {label}: {:.1} ms",
                phase.elapsed().as_secs_f64() * 1e3
            );
        }
        *phase = std::time::Instant::now();
    };
    let shape = r1cs.field_shape();
    let useful_rows = r1cs.useful_rows();
    let width = 1usize << shape.k_log;
    assert!(shape.m >= shape.k_log);
    assert!(shape.k_skip <= shape.k_log);
    assert!(useful_rows <= width);
    assert_eq!(shape.k_skip, zerocheck::K_SKIP);
    assert_eq!(witness.len(), 1usize << shape.m);
    assert_eq!(pcs_params.m, shape.m + pcs::LOG_PACKING);

    let (commitment, prover_data) = pcs::commit(witness, pcs_params);
    lap("PCS commit", &mut phase);
    check_cancelled()?;
    bind_statement_field_parts_c1(challenger, &r1cs.field_statement_digest(), &commitment);

    let io_claims = match public_io {
        Some((spec, io)) => {
            assert_witness_matches_io(witness, spec, io);
            bind_public_io_c1(challenger, spec, io, shape.m)
        }
        None => Vec::new(),
    };
    lap("statement and public IO", &mut phase);
    check_cancelled()?;
    let (auxiliary, (auxiliary_claims, auxiliary_c1_claims)) =
        post_commit(witness, &commitment, challenger);
    lap("post-commit auxiliary", &mut phase);
    check_cancelled()?;

    let a = r1cs.apply_a_relation(witness);
    let b = r1cs.apply_b_relation(witness);
    lap("apply A/B", &mut phase);
    check_cancelled()?;
    let (zerocheck_proof, zerocheck_claim) =
        zerocheck::field_c1::prove(&a, &b, witness, shape.m, challenger);
    drop(a);
    drop(b);
    lap("zerocheck", &mut phase);
    check_cancelled()?;

    let inner_rest_len = shape.k_log - shape.k_skip;
    let lincheck_point = lincheck::c1::C1QuirkyPoint {
        z_skip: zerocheck_claim.z,
        x_inner_rest: zerocheck_claim.mlv_challenges[..inner_rest_len].to_vec(),
        x_outer: zerocheck_claim.mlv_challenges[inner_rest_len..].to_vec(),
    };
    let (lincheck_proof, lincheck_claim, fresh_capture) = if capture_fresh {
        let (proof, claim, capture) = lincheck::c1::prove_field_capturing_fresh(
            witness,
            shape.m,
            shape.k_log,
            shape.k_skip,
            useful_rows,
            r1cs,
            &lincheck_point,
            zerocheck_claim.a_eval,
            zerocheck_claim.b_eval,
            challenger,
        );
        (proof, claim, Some(capture))
    } else {
        let (proof, claim) = lincheck::c1::prove_field(
            witness,
            shape.m,
            shape.k_log,
            shape.k_skip,
            useful_rows,
            r1cs,
            &lincheck_point,
            challenger,
        );
        (proof, claim, None)
    };
    lap("lincheck", &mut phase);
    check_cancelled()?;

    let ab = C1ZClaim {
        point: lincheck::c1::C1QuirkyPoint {
            z_skip: lincheck_claim.r_inner_skip,
            x_inner_rest: lincheck_claim.r_inner_rest.clone(),
            x_outer: lincheck_point.x_outer.clone(),
        },
        value: lincheck_claim.w,
    };
    let c = C1ZClaim {
        point: lincheck::c1::C1QuirkyPoint {
            z_skip: zerocheck_claim.z,
            x_inner_rest: zerocheck_claim.r_rest[..inner_rest_len].to_vec(),
            x_outer: zerocheck_claim.r_rest[inner_rest_len..].to_vec(),
        },
        value: zerocheck_claim.c_eval,
    };
    let direct_claim = |claim: &C1ZClaim| {
        let mut x_rest = claim.point.x_inner_rest.clone();
        x_rest.extend_from_slice(&claim.point.x_outer);
        C1QuirkyDirectClaim {
            z_skip: claim.point.z_skip,
            k_skip: shape.k_skip,
            x_rest,
            value: claim.value,
        }
    };
    let mut claims = vec![direct_claim(&ab), direct_claim(&c)];
    claims.extend(io_claims);
    claims.extend(
        auxiliary_claims
            .into_iter()
            .map(|claim| C1QuirkyDirectClaim {
                z_skip: F256::from_base(claim.z_skip),
                k_skip: claim.k_skip,
                x_rest: claim.x_rest.into_iter().map(F256::from_base).collect(),
                value: F256::from_base(claim.value),
            }),
    );
    claims.extend(auxiliary_c1_claims);
    let pcs_open =
        pcs::open_batch_quirky_direct_c1(witness, &prover_data, &commitment, &claims, challenger);
    lap("PCS open", &mut phase);
    check_cancelled()?;

    Ok((
        C1FieldR1csProof {
            zerocheck: zerocheck_proof,
            lincheck: lincheck_proof,
            pcs_open,
        },
        auxiliary,
        commitment,
        C1R1csClaim { ab, c },
        fresh_capture,
    ))
}

/// [`prove_field`] with a public-IO envelope: right after the statement
/// binding, absorb the spec + envelope lanes, sample the binding point, and
/// append the IO claims to the batched PCS opening (see
/// `noid_ivc_core::public_io`). The witness must hold the envelope lanes in
/// the spec's IO slice (zero-padded) — asserted here.
pub fn prove_field_with_public_io<Ch: Challenger>(
    r1cs: &FieldR1cs,
    z: &[F128],
    pcs_params: &PcsParams,
    spec: &PublicIoSpec,
    io: &[F128],
    challenger: &mut Ch,
) -> (FieldR1csProof, Commitment, R1csClaim) {
    let (proof, (), commitment, claim, capture) = prove_field_inner(
        r1cs,
        z,
        pcs_params,
        Some((spec, io)),
        FreshLincheckCaptureRequest::Disabled,
        challenger,
        |_, _, _| ((), Vec::new()),
    );
    debug_assert!(capture.is_none());
    (proof, commitment, claim)
}

/// [`prove_field_with_public_io`] plus a post-commit auxiliary protocol.
///
/// `post_commit` is invoked only after the witness commitment, statement,
/// and public-IO envelope have been absorbed.  It may sample challenges,
/// return an auxiliary proof object, and append evaluation claims on the SAME
/// committed witness to the final BaseFold batch.  This is the sound entry
/// point for protocols whose challenge must be causally downstream of the
/// witness commitment (for example, a column-relation sidecar); building such
/// a proof while assembling `z` would make its Fiat--Shamir challenges
/// pre-commit and is not equivalent.
pub fn prove_field_with_public_io_and_post_commit<Ch, Aux, PostCommit>(
    r1cs: &FieldR1cs,
    z: &[F128],
    pcs_params: &PcsParams,
    spec: &PublicIoSpec,
    io: &[F128],
    challenger: &mut Ch,
    post_commit: PostCommit,
) -> (FieldR1csProof, Aux, Commitment, R1csClaim)
where
    Ch: Challenger,
    PostCommit: FnOnce(&[F128], &Commitment, &mut Ch) -> (Aux, Vec<QuirkyDirectClaim>),
{
    let (proof, auxiliary, commitment, claim, capture) = prove_field_inner(
        r1cs,
        z,
        pcs_params,
        Some((spec, io)),
        FreshLincheckCaptureRequest::Disabled,
        challenger,
        post_commit,
    );
    debug_assert!(capture.is_none());
    (proof, auxiliary, commitment, claim)
}

/// Typestate variant of [`prove_field_with_public_io_and_post_commit`].
///
/// After commitment/statement/public-IO binding, this API additionally binds
/// `post_commit_class_digest`, then gives the callback an opaque context that
/// is both the SAME challenger and an append-only PCS claim sink.  Claims are
/// appended to the enclosing batch automatically when the callback returns.
#[allow(clippy::too_many_arguments)]
pub fn prove_field_with_public_io_and_post_commit_context<Ch, Aux, PostCommit>(
    r1cs: &FieldR1cs,
    z: &[F128],
    pcs_params: &PcsParams,
    spec: &PublicIoSpec,
    io: &[F128],
    post_commit_class_digest: &[u8; 32],
    challenger: &mut Ch,
    post_commit: PostCommit,
) -> (FieldR1csProof, Aux, Commitment, R1csClaim)
where
    Ch: Challenger,
    PostCommit: FnOnce(&mut FieldPostCommitProverContext<'_, Ch>) -> Aux,
{
    let (proof, auxiliary, commitment, claim, capture) = prove_field_inner(
        r1cs,
        z,
        pcs_params,
        Some((spec, io)),
        FreshLincheckCaptureRequest::Disabled,
        challenger,
        |witness, commitment, challenger| {
            bind_post_commit_class(challenger, post_commit_class_digest);
            let mut context =
                FieldPostCommitProverContext::new(witness, commitment, r1cs.m, challenger);
            let auxiliary = post_commit(&mut context);
            (auxiliary, context.finish())
        },
    );
    debug_assert!(capture.is_none());
    (proof, auxiliary, commitment, claim)
}

/// Compact authenticated-relation twin of
/// [`prove_field_with_public_io_and_post_commit_context`].
///
/// `CompactFieldR1cs` can only be created by a complete canonical scan and
/// structural-digest check.  Binding its established digest here therefore
/// preserves the resident path's matrix/shape authority without retaining or
/// rebuilding CSR arrays.
#[allow(clippy::too_many_arguments)]
pub fn prove_field_compact_with_public_io_and_post_commit_context<Ch, Aux, PostCommit>(
    r1cs: &CompactFieldR1cs,
    z: &[F128],
    pcs_params: &PcsParams,
    spec: &PublicIoSpec,
    io: &[F128],
    post_commit_class_digest: &[u8; 32],
    challenger: &mut Ch,
    post_commit: PostCommit,
) -> (FieldR1csProof, Aux, Commitment, R1csClaim)
where
    Ch: Challenger,
    PostCommit: FnOnce(&mut FieldPostCommitProverContext<'_, Ch>) -> Aux,
{
    let total_vars = r1cs.shape().m;
    let (proof, auxiliary, commitment, claim, capture) = prove_field_inner(
        r1cs,
        z,
        pcs_params,
        Some((spec, io)),
        FreshLincheckCaptureRequest::Disabled,
        challenger,
        |witness, commitment, challenger| {
            bind_post_commit_class(challenger, post_commit_class_digest);
            let mut context =
                FieldPostCommitProverContext::new(witness, commitment, total_vars, challenger);
            let auxiliary = post_commit(&mut context);
            (auxiliary, context.finish())
        },
    );
    debug_assert!(capture.is_none());
    (proof, auxiliary, commitment, claim)
}

/// Opt-in locally-authored-capture twin of
/// [`prove_field_with_public_io_and_post_commit_context`].
///
/// The first four return values and the complete proof transcript are
/// byte-identical to the legacy entry point.  The fifth value is an opaque,
/// one-shot capture of the fresh deferred lincheck claim derived while the
/// prover already owns the exact transcript state.  An enclosing recursive
/// layer must bind it to its exact class, envelope and commitment before use.
#[allow(clippy::too_many_arguments)]
pub fn prove_field_with_public_io_and_post_commit_context_capturing_fresh_lincheck<
    Ch,
    Aux,
    PostCommit,
>(
    r1cs: &FieldR1cs,
    z: &[F128],
    pcs_params: &PcsParams,
    spec: &PublicIoSpec,
    io: &[F128],
    post_commit_class_digest: &[u8; 32],
    challenger: &mut Ch,
    post_commit: PostCommit,
) -> (
    FieldR1csProof,
    Aux,
    Commitment,
    R1csClaim,
    LocallyAuthoredFreshLincheckCapture,
)
where
    Ch: Challenger,
    PostCommit: FnOnce(&mut FieldPostCommitProverContext<'_, Ch>) -> Aux,
{
    let (proof, auxiliary, commitment, claim, capture) = prove_field_inner(
        r1cs,
        z,
        pcs_params,
        Some((spec, io)),
        FreshLincheckCaptureRequest::Enabled,
        challenger,
        |witness, commitment, challenger| {
            bind_post_commit_class(challenger, post_commit_class_digest);
            let mut context =
                FieldPostCommitProverContext::new(witness, commitment, r1cs.m, challenger);
            let auxiliary = post_commit(&mut context);
            (auxiliary, context.finish())
        },
    );
    (
        proof,
        auxiliary,
        commitment,
        claim,
        capture.expect("capturing field prover returns its lincheck capability"),
    )
}

/// Compact authenticated-relation twin of
/// [`prove_field_with_public_io_and_post_commit_context_capturing_fresh_lincheck`].
#[allow(clippy::too_many_arguments)]
pub fn prove_field_compact_with_public_io_and_post_commit_context_capturing_fresh_lincheck<
    Ch,
    Aux,
    PostCommit,
>(
    r1cs: &CompactFieldR1cs,
    z: &[F128],
    pcs_params: &PcsParams,
    spec: &PublicIoSpec,
    io: &[F128],
    post_commit_class_digest: &[u8; 32],
    challenger: &mut Ch,
    post_commit: PostCommit,
) -> (
    FieldR1csProof,
    Aux,
    Commitment,
    R1csClaim,
    LocallyAuthoredFreshLincheckCapture,
)
where
    Ch: Challenger,
    PostCommit: FnOnce(&mut FieldPostCommitProverContext<'_, Ch>) -> Aux,
{
    let total_vars = r1cs.shape().m;
    let (proof, auxiliary, commitment, claim, capture) = prove_field_inner(
        r1cs,
        z,
        pcs_params,
        Some((spec, io)),
        FreshLincheckCaptureRequest::Enabled,
        challenger,
        |witness, commitment, challenger| {
            bind_post_commit_class(challenger, post_commit_class_digest);
            let mut context =
                FieldPostCommitProverContext::new(witness, commitment, total_vars, challenger);
            let auxiliary = post_commit(&mut context);
            (auxiliary, context.finish())
        },
    );
    (
        proof,
        auxiliary,
        commitment,
        claim,
        capture.expect("capturing compact field prover returns its lincheck capability"),
    )
}

fn prove_field_inner<R, Ch, Aux, PostCommit>(
    r1cs: &R,
    z: &[F128],
    pcs_params: &PcsParams,
    public_io: Option<(&PublicIoSpec, &[F128])>,
    capture_fresh_lincheck: FreshLincheckCaptureRequest,
    challenger: &mut Ch,
    post_commit: PostCommit,
) -> (
    FieldR1csProof,
    Aux,
    Commitment,
    R1csClaim,
    Option<LocallyAuthoredFreshLincheckCapture>,
)
where
    R: FieldProverRelation,
    Ch: Challenger,
    PostCommit: FnOnce(&[F128], &Commitment, &mut Ch) -> (Aux, Vec<QuirkyDirectClaim>),
{
    let shape = r1cs.field_shape();
    let useful_rows = r1cs.useful_rows();
    let k = 1usize << shape.k_log;
    assert!(shape.m >= shape.k_log, "field relation m must cover k_log");
    assert!(shape.k_skip <= shape.k_log, "field relation k_skip drift");
    assert!(useful_rows <= k, "field relation useful_rows exceeds k");
    assert!(shape.const_pin.is_none_or(|column| column < k));
    assert_eq!(z.len(), 1usize << shape.m);
    assert_eq!(
        pcs_params.m,
        shape.m + pcs::LOG_PACKING,
        "pcs_params.m must be r1cs.m + LOG_PACKING (bit-log of the commitment)"
    );
    assert_eq!(
        shape.k_skip,
        zerocheck::K_SKIP,
        "the field zerocheck is hardwired to K_SKIP"
    );

    // Phase timings + resident-set size, env-gated (mirrors NOIDH_ZC_TIMING's
    // pattern). The RSS column shows where the prover's memory grows — commit
    // (codeword + Merkle tree), lincheck (constraint matrix), open — so the
    // dominant buffer is visible without an external profiler.
    let timing = std::env::var_os("NOIDH_FIELD_PROVE_TIMING").is_some();
    let mut t = std::time::Instant::now();
    let lap = move |label: &str, t: &mut std::time::Instant| {
        if timing {
            let (rss, peak) = vmrss_mb();
            eprintln!(
                "[field-prove] {label}: {:.2} ms, RSS {rss} MB (peak {peak} MB)",
                t.elapsed().as_secs_f64() * 1e3,
            );
        }
        *t = std::time::Instant::now();
    };

    if timing {
        let (rss, peak) = vmrss_mb();
        eprintln!(
            "[field-prove] relation @entry: m={} k_log={} useful_rows={} RSS {rss}MB (peak {peak}MB)",
            shape.m, shape.k_log, useful_rows,
        );
    }

    // ---- PCS commit to the element witness (no repacking).
    let (commitment, prover_data) = pcs::commit(z, pcs_params);
    lap("pcs commit", &mut t);

    // ---- Bind the FS transcript to the statement.
    bind_statement_field_parts(challenger, &r1cs.field_statement_digest(), &commitment);
    lap("statement bind", &mut t);

    // ---- Public-IO envelope binding (before any sub-protocol challenge).
    let io_claims: Vec<QuirkyDirectClaim> = match public_io {
        Some((spec, io)) => {
            assert_witness_matches_io(z, spec, io);
            bind_public_io(challenger, spec, io, shape.m)
        }
        None => Vec::new(),
    };
    lap("public IO bind", &mut t);

    // The commitment root is already transcript-bound here. Auxiliary proof
    // messages and every challenge they induce are therefore post-commit.
    let (auxiliary, auxiliary_claims) = post_commit(z, &commitment, challenger);
    lap("post-commit aux", &mut t);

    // ---- a = A·z, b = B·z over F128; c aliases z (C = I).
    let a = r1cs.apply_a_relation(z);
    let b = r1cs.apply_b_relation(z);
    lap("apply A/B", &mut t);

    // ---- Field zerocheck.
    let (zc_proof, zc_claim) = zerocheck::field::prove(&a, &b, z, shape.m, challenger);
    drop(a);
    drop(b);
    lap("zerocheck", &mut t);

    // ---- Zerocheck output → lincheck input (same quirky layout as the
    // boolean path).
    let inner_rest_len = shape.k_log - shape.k_skip;
    let x_ab = QuirkyPoint {
        z_skip: zc_claim.z,
        x_inner_rest: zc_claim.mlv_challenges[..inner_rest_len].to_vec(),
        x_outer: zc_claim.mlv_challenges[inner_rest_len..].to_vec(),
    };

    // ---- Field lincheck against the coefficient-carrying circuit.
    let (lc_proof, lc_claim, fresh_lincheck_capture) = match capture_fresh_lincheck {
        FreshLincheckCaptureRequest::Disabled => {
            let (proof, claim) = lincheck::prove_field(
                z,
                shape.m,
                shape.k_log,
                shape.k_skip,
                useful_rows,
                r1cs,
                &x_ab,
                challenger,
            );
            (proof, claim, None)
        }
        FreshLincheckCaptureRequest::Enabled => {
            let (proof, claim, capture) = lincheck::prove_field_capturing_fresh(
                z,
                shape.m,
                shape.k_log,
                shape.k_skip,
                useful_rows,
                r1cs,
                &x_ab,
                zc_claim.a_eval,
                zc_claim.b_eval,
                challenger,
            );
            (proof, claim, Some(capture))
        }
    };
    lap("lincheck", &mut t);

    // ---- The two z-claims.
    let ab = ZClaim {
        point: QuirkyPoint {
            z_skip: lc_claim.r_inner_skip,
            x_inner_rest: lc_claim.r_inner_rest.clone(),
            x_outer: x_ab.x_outer.clone(),
        },
        value: lc_claim.w,
    };
    let c = ZClaim {
        point: QuirkyPoint {
            z_skip: zc_claim.z,
            x_inner_rest: zc_claim.r_rest[..inner_rest_len].to_vec(),
            x_outer: zc_claim.r_rest[inner_rest_len..].to_vec(),
        },
        value: zc_claim.c_eval,
    };

    // ---- Batched quirky-direct PCS open over both claims.
    let x_rest_of = |zc: &ZClaim| -> Vec<F128> {
        let mut v = zc.point.x_inner_rest.clone();
        v.extend_from_slice(&zc.point.x_outer);
        v
    };
    let mut claims = vec![
        QuirkyDirectClaim {
            z_skip: ab.point.z_skip,
            k_skip: shape.k_skip,
            x_rest: x_rest_of(&ab),
            value: ab.value,
        },
        QuirkyDirectClaim {
            z_skip: c.point.z_skip,
            k_skip: shape.k_skip,
            x_rest: x_rest_of(&c),
            value: c.value,
        },
    ];
    claims.extend(io_claims);
    claims.extend(auxiliary_claims);
    let pcs_open = pcs::open_batch_quirky_direct(z, &prover_data, &commitment, &claims, challenger);
    lap("pcs open", &mut t);

    let proof = FieldR1csProof {
        zerocheck: zc_proof,
        lincheck: lc_proof,
        pcs_open,
    };
    (
        proof,
        auxiliary,
        commitment,
        R1csClaim { ab, c },
        fresh_lincheck_capture,
    )
}
