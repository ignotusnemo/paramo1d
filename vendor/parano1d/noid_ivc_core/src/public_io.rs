//! Public-IO binding for FieldR1cs proofs.
//!
//! A FieldR1cs coefficient matrix is a protocol constant (the statement
//! digest covers it), so runtime public values — statement lanes, sumcheck
//! claim endpoints — cannot live in matrix coefficients. Instead they live
//! in a designated dyadic slice of the committed witness, and the proof
//! envelope carries the same values publicly. Right after the statement
//! binding, both sides absorb the envelope, sample one fresh point `y`, and
//! add ONE extra claim to the batched PCS opening: the witness restricted
//! to the IO slice, evaluated at `y`, must equal the same evaluation of the
//! envelope vector — which the verifier computes itself in O(|IO|).
//! Schwartz–Zippel at `y` (sampled after both the witness commitment and
//! the envelope are fixed) forces witness-IO = envelope-IO up to a
//! `log2_len / 2^128` soundness loss per proof.
//!
//! The spec may additionally derive WITNESS CLAIMS from the IO lanes: a
//! claim spec names a target witness slice, the IO positions holding the
//! claim point's coordinates, and the IO position holding the claimed
//! value. This discharges sumcheck-terminal claims on witness-resident
//! columns through the same batched opening, without re-deriving the
//! columns in-circuit: the sub-protocol that produced the endpoint pins the
//! same lanes inside the circuit, the envelope exposes them to the
//! verifier, and the opening checks them against the commitment.
//!
//! The spec itself is a per-shape-class verification-key constant. Both
//! sides absorb its parameters before the lanes, so two different specs can
//! never share a transcript.

use crate::challenger::Challenger;
use crate::field::{F128, F256};
use crate::lincheck::build_eq_table;
use crate::pcs::{C1QuirkyDirectClaim, QuirkyDirectClaim};

/// Domain separator for the verification-key/class identity of a post-commit
/// auxiliary protocol.  Context-based APIs absorb this after public IO and
/// before giving the callback access to the shared challenger.
pub const POST_COMMIT_CLASS_BINDING_LABEL: &[u8] = b"history-post-commit-class-v1";

/// Bind the exact auxiliary proof class at the post-commit transcript
/// boundary.  Prover, full verifier, deferred verifier, and recursive trace
/// twins must call this at the same position.
pub fn bind_post_commit_class<Ch: Challenger>(challenger: &mut Ch, class_digest: &[u8; 32]) {
    challenger.observe_label(POST_COMMIT_CLASS_BINDING_LABEL);
    challenger.observe_bytes(class_digest);
}

/// A dyadic block of the committed element space: element indices
/// `[index · 2^log2_len, (index + 1) · 2^log2_len)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WitnessSlice {
    pub log2_len: usize,
    pub index: usize,
}

impl WitnessSlice {
    pub fn start(&self) -> usize {
        self.index << self.log2_len
    }

    pub fn len(&self) -> usize {
        1usize << self.log2_len
    }

    /// Check the slice fits a `2^total_vars`-element space.
    pub fn fits(&self, total_vars: usize) -> bool {
        total_vars < usize::BITS as usize
            && self.log2_len <= total_vars
            && self.index < (1usize << (total_vars - self.log2_len))
    }

    /// The boolean coordinates of the slice-selecting high variables,
    /// LSB-first — the tail of a claim's `x_rest` after the slice's own
    /// `log2_len` free coordinates.
    pub fn prefix_coords(&self, total_vars: usize) -> Vec<F128> {
        assert!(self.fits(total_vars), "slice out of range");
        (0..total_vars - self.log2_len)
            .map(|bit| {
                if (self.index >> bit) & 1 == 1 {
                    F128::ONE
                } else {
                    F128::ZERO
                }
            })
            .collect()
    }
}

/// One derived witness claim, read out of the IO lanes.
#[derive(Clone, Debug)]
pub struct IoClaimSpec {
    /// The witness slice the claim targets (e.g. a chain-killshot column).
    pub slice: WitnessSlice,
    /// IO lane positions holding the claim point's coordinates, LSB-first;
    /// length must equal `slice.log2_len`.
    pub point: std::ops::Range<usize>,
    /// IO lane position holding the claimed evaluation.
    pub value: usize,
}

/// Per-shape-class public-IO specification.
#[derive(Clone, Debug)]
pub struct PublicIoSpec {
    /// Where the IO lanes live in the committed witness.
    pub io_slice: WitnessSlice,
    /// Number of meaningful IO lanes (≤ `io_slice.len()`); the slice tail
    /// beyond `io_len` is constrained to zero by the same binding claim.
    pub io_len: usize,
    /// Derived witness claims.
    pub claims: Vec<IoClaimSpec>,
}

impl PublicIoSpec {
    /// Structural validation against a `2^total_vars`-element witness.
    pub fn validate(&self, total_vars: usize) {
        assert!(self.io_slice.fits(total_vars), "io slice out of range");
        assert!(
            self.io_len <= self.io_slice.len(),
            "io_len exceeds the io slice"
        );
        for c in &self.claims {
            assert!(c.slice.fits(total_vars), "claim slice out of range");
            assert_eq!(
                c.point.len(),
                c.slice.log2_len,
                "claim point arity must match its slice"
            );
            assert!(c.point.end <= self.io_len, "claim point outside io lanes");
            assert!(c.value < self.io_len, "claim value outside io lanes");
        }
    }

    /// The spec parameters as transcript lanes (a verification-key constant
    /// absorbed by both sides so distinct specs never share a transcript).
    pub fn transcript_lanes(&self) -> Vec<F128> {
        let lane = |v: usize| F128 {
            lo: v as u64,
            hi: 0,
        };
        let mut lanes = vec![
            lane(self.io_slice.log2_len),
            lane(self.io_slice.index),
            lane(self.io_len),
            lane(self.claims.len()),
        ];
        for c in &self.claims {
            lanes.push(lane(c.slice.log2_len));
            lanes.push(lane(c.slice.index));
            lanes.push(lane(c.point.start));
            lanes.push(lane(c.point.end));
            lanes.push(lane(c.value));
        }
        lanes
    }
}

/// Shared prover/verifier transcript walk: absorb the spec and the envelope
/// lanes, sample the binding point, and derive the claim list to append to
/// the batched PCS opening. Runs immediately after `bind_statement_field`.
///
/// `total_vars` is the element-space log (`r1cs.m`, = `pcs_params.m −
/// LOG_PACKING`). Returned claims are in deterministic order: the IO
/// binding claim first, then the derived claims in spec order.
pub fn bind_public_io<Ch: Challenger>(
    challenger: &mut Ch,
    spec: &PublicIoSpec,
    io: &[F128],
    total_vars: usize,
) -> Vec<QuirkyDirectClaim> {
    spec.validate(total_vars);
    assert_eq!(io.len(), spec.io_len, "envelope length must match the spec");

    challenger.observe_label(b"history-public-io-v0");
    challenger.observe_f128_slice(&spec.transcript_lanes());
    challenger.observe_f128_slice(io);
    let y = challenger.sample_f128_vec(spec.io_slice.log2_len);

    // The binding claim: witness over the io slice at y == Σ_t eq(y,t)·io[t]
    // (zero-padded past io_len, so the witness tail is forced to zero too).
    let eq = build_eq_table(&y);
    let mut io_value = F128::ZERO;
    for (v, e) in io.iter().zip(eq.iter()) {
        io_value += *v * *e;
    }
    let mut x_rest = y;
    x_rest.extend(spec.io_slice.prefix_coords(total_vars));
    let mut claims = vec![QuirkyDirectClaim {
        z_skip: F128::ZERO,
        k_skip: 0,
        x_rest,
        value: io_value,
    }];

    for c in &spec.claims {
        let mut x_rest: Vec<F128> = io[c.point.clone()].to_vec();
        x_rest.extend(c.slice.prefix_coords(total_vars));
        claims.push(QuirkyDirectClaim {
            z_skip: F128::ZERO,
            k_skip: 0,
            x_rest,
            value: io[c.value],
        });
    }
    claims
}

/// C1 twin of [`bind_public_io`]. Public lanes remain elements of the
/// committed F128 witness, while the binding point, equality polynomial and
/// resulting PCS claims live in the C1 extension field.
pub fn bind_public_io_c1<Ch: Challenger>(
    challenger: &mut Ch,
    spec: &PublicIoSpec,
    io: &[F128],
    total_vars: usize,
) -> Vec<C1QuirkyDirectClaim> {
    spec.validate(total_vars);
    assert_eq!(io.len(), spec.io_len, "envelope length must match the spec");

    challenger.observe_label(b"history-public-io-c1");
    challenger.observe_f128_slice(&spec.transcript_lanes());
    challenger.observe_f128_slice(io);
    let y = challenger.sample_f256_vec(spec.io_slice.log2_len);

    let eq = crate::zerocheck::field_c1::build_eq_table(&y);
    let io_value = io
        .iter()
        .zip(eq.iter())
        .fold(F256::ZERO, |sum, (&value, &weight)| {
            sum + weight.scale_base(value)
        });
    let prefix = |slice: &WitnessSlice| {
        slice
            .prefix_coords(total_vars)
            .into_iter()
            .map(F256::from_base)
            .collect::<Vec<_>>()
    };
    let mut x_rest = y;
    x_rest.extend(prefix(&spec.io_slice));
    let mut claims = vec![C1QuirkyDirectClaim {
        z_skip: F256::ZERO,
        k_skip: 0,
        x_rest,
        value: io_value,
    }];

    for claim in &spec.claims {
        let mut x_rest = io[claim.point.clone()]
            .iter()
            .copied()
            .map(F256::from_base)
            .collect::<Vec<_>>();
        x_rest.extend(prefix(&claim.slice));
        claims.push(C1QuirkyDirectClaim {
            z_skip: F256::ZERO,
            k_skip: 0,
            x_rest,
            value: F256::from_base(io[claim.value]),
        });
    }
    claims
}

/// Prover-side sanity: the witness IO slice must hold exactly the envelope
/// lanes (zero-padded). A mismatch means the caller assembled the witness
/// and the envelope from different data — the resulting proof would be
/// rejected, so fail fast here.
pub fn assert_witness_matches_io(z: &[F128], spec: &PublicIoSpec, io: &[F128]) {
    let start = spec.io_slice.start();
    for t in 0..spec.io_slice.len() {
        let expected = io.get(t).copied().unwrap_or(F128::ZERO);
        assert_eq!(
            z[start + t],
            expected,
            "witness io lane {t} disagrees with the envelope"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::FsChallenger;

    #[test]
    fn slice_prefix_coords_select_the_block() {
        let s = WitnessSlice {
            log2_len: 3,
            index: 5,
        };
        assert_eq!(s.start(), 40);
        assert_eq!(s.len(), 8);
        let coords = s.prefix_coords(6);
        // index 5 = 101b over 3 high vars, LSB-first.
        assert_eq!(coords, vec![F128::ONE, F128::ZERO, F128::ONE]);
    }

    #[test]
    fn slice_fit_rejects_unrepresentable_total_log_without_panicking() {
        let slice = WitnessSlice {
            log2_len: 0,
            index: 0,
        };
        assert!(!slice.fits(usize::BITS as usize));
        assert!(!slice.fits(usize::MAX));
    }

    #[test]
    fn binding_claim_value_matches_direct_mle() {
        let spec = PublicIoSpec {
            io_slice: WitnessSlice {
                log2_len: 2,
                index: 3,
            },
            io_len: 3,
            claims: vec![],
        };
        let io = [
            F128 { lo: 7, hi: 1 },
            F128 { lo: 9, hi: 2 },
            F128 { lo: 11, hi: 3 },
        ];
        let mut ch = FsChallenger::new(b"public-io-test");
        let claims = bind_public_io(&mut ch, &spec, &io, 5);
        assert_eq!(claims.len(), 1);
        assert_eq!(claims[0].x_rest.len(), 5);

        // Recompute the MLE over the zero-padded slice directly.
        let y = &claims[0].x_rest[..2];
        let eq = build_eq_table(y);
        let mut expected = F128::ZERO;
        for t in 0..3 {
            expected += io[t] * eq[t];
        }
        assert_eq!(claims[0].value, expected);
        // Prefix selects block 3 of 8: 11b LSB-first.
        assert_eq!(claims[0].x_rest[2..], [F128::ONE, F128::ONE, F128::ZERO]);
    }

    #[test]
    fn derived_claims_read_point_and_value_lanes() {
        let spec = PublicIoSpec {
            io_slice: WitnessSlice {
                log2_len: 3,
                index: 0,
            },
            io_len: 4,
            claims: vec![IoClaimSpec {
                slice: WitnessSlice {
                    log2_len: 2,
                    index: 1,
                },
                point: 0..2,
                value: 2,
            }],
        };
        let io = [
            F128 { lo: 100, hi: 0 },
            F128 { lo: 200, hi: 0 },
            F128 { lo: 300, hi: 0 },
            F128 { lo: 400, hi: 0 },
        ];
        let mut ch = FsChallenger::new(b"public-io-test");
        let claims = bind_public_io(&mut ch, &spec, &io, 4);
        assert_eq!(claims.len(), 2);
        let derived = &claims[1];
        assert_eq!(derived.x_rest[..2], io[..2]);
        assert_eq!(derived.x_rest[2..], [F128::ONE, F128::ZERO]);
        assert_eq!(derived.value, io[2]);
    }

    #[test]
    #[should_panic(expected = "claim point arity")]
    fn spec_rejects_point_arity_mismatch() {
        let spec = PublicIoSpec {
            io_slice: WitnessSlice {
                log2_len: 3,
                index: 0,
            },
            io_len: 4,
            claims: vec![IoClaimSpec {
                slice: WitnessSlice {
                    log2_len: 2,
                    index: 1,
                },
                point: 0..3,
                value: 3,
            }],
        };
        spec.validate(4);
    }

    #[test]
    fn transcript_binds_spec_and_lanes() {
        let spec_a = PublicIoSpec {
            io_slice: WitnessSlice {
                log2_len: 2,
                index: 0,
            },
            io_len: 2,
            claims: vec![],
        };
        let spec_b = PublicIoSpec {
            io_slice: WitnessSlice {
                log2_len: 2,
                index: 1,
            },
            io_len: 2,
            claims: vec![],
        };
        let io = [F128::ONE, F128 { lo: 2, hi: 0 }];
        let sample = |spec: &PublicIoSpec, io: &[F128]| {
            let mut ch = FsChallenger::new(b"public-io-test");
            let _ = bind_public_io(&mut ch, spec, io, 4);
            ch.sample_f128()
        };
        // Different slice index → different transcript.
        assert_ne!(sample(&spec_a, &io), sample(&spec_b, &io));
        // Different lane content → different transcript.
        let io2 = [F128::ONE, F128 { lo: 3, hi: 0 }];
        assert_ne!(sample(&spec_a, &io), sample(&spec_a, &io2));
    }
}
