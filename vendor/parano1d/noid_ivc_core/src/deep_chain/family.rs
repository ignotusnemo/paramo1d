//! The reference chain family — a miniature Merkle-path-like family that
//! exercises the COMPLETE region-layer claim DAG (booleanity, selector
//! products, selection, output exposure, the 66-layer walk, wiring
//! substitution, shift discharge). It is the prototype every production
//! chain-family schedule follows: committed columns + relation term lists
//! + a native prove/verify driver that returns the pending
//! committed-column claims for the batched PCS opening.
//!
//! Family shape: chains of [`CHAIN_LEN`] permutations. A chain's first
//! slot hashes two fresh leaf lanes; later slots hash the carried lane-0
//! output against a sibling lane, ordered by a witness direction bit.

use crate::challenger::Challenger;
use crate::deep_chain::relations::{
    ColRef, ColumnRelationProof, RelationColumns, RelationTerm, ShiftDischargeProof, distinct_refs,
    prove_column_relation, prove_shift_discharge, verify_column_relation, verify_shift_discharge,
};
use crate::deep_chain::{
    DeepChainWalkProof, LaneClaimGroup, apply_round, initial_mds, prove_deep_chain_walk,
    verify_deep_chain_walk,
};
use crate::field::F128;
use crate::lincheck::build_eq_table;
use noid_poseidon2b::native::permutation::{N_ROUNDS, STATE_SIZE};

pub const W_LOG: usize = 4;
pub const W: usize = 1 << W_LOG;
pub const CHAIN_LEN: usize = 4;

pub(crate) struct Rng(pub u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn f128(&mut self) -> F128 {
        F128 {
            lo: self.next_u64(),
            hi: self.next_u64(),
        }
    }
    fn bit(&mut self) -> F128 {
        if self.next_u64() & 1 == 1 {
            F128::ONE
        } else {
            F128::ZERO
        }
    }
}

pub fn mle_eval(col: &[F128], point: &[F128]) -> F128 {
    let eq = build_eq_table(point);
    let mut acc = F128::ZERO;
    for (v, e) in col.iter().zip(eq.iter()) {
        acc += *v * *e;
    }
    acc
}

pub fn shifted(col: &[F128]) -> Vec<F128> {
    let mut s = vec![F128::ZERO; col.len()];
    s[1..].copy_from_slice(&col[..col.len() - 1]);
    s
}

/// The family's committed columns plus the internal walk columns.
pub struct Family {
    // Committed (region/carry/selector) columns, by index:
    // 0=A0, 1=A1, 2=SIB, 3=D, 4=START, 5=END, 6=G0, 7=G1, 8=C, 9=O.
    pub committed: Vec<Vec<F128>>,
    /// Walk layer-0 columns (after the initial MDS).
    pub s0: [Vec<F128>; STATE_SIZE],
    /// Walk layer-66 columns.
    pub s_out: [Vec<F128>; STATE_SIZE],
}

pub const A0: usize = 0;
pub const A1: usize = 1;
pub const SIB: usize = 2;
pub const D: usize = 3;
pub const START: usize = 4;
pub const END: usize = 5;
pub const G0: usize = 6;
pub const G1: usize = 7;
pub const C: usize = 8;
pub const O: usize = 9;

/// Build an honest family: 4 chains of 4 slots. Slot 0 of a chain hashes
/// two fresh leaf lanes; slots 1..3 hash the carried lane-0 output against
/// a sibling, ordered by the direction bit.
pub fn build_family(seed: u64) -> Family {
    let mut rng = Rng(seed);
    let mut cols: Vec<Vec<F128>> = (0..10).map(|_| vec![F128::ZERO; W]).collect();
    let mut s0: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; W]);
    let mut s_out: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; W]);

    let mut carry_prev = F128::ZERO;
    for w in 0..W {
        let start = w % CHAIN_LEN == 0;
        let end = w % CHAIN_LEN == CHAIN_LEN - 1;
        cols[START][w] = if start { F128::ONE } else { F128::ZERO };
        cols[END][w] = if end { F128::ONE } else { F128::ZERO };
        let d = if start { F128::ZERO } else { rng.bit() };
        cols[D][w] = d;
        cols[G0][w] = (F128::ONE + cols[START][w]) * (F128::ONE + d);
        cols[G1][w] = (F128::ONE + cols[START][w]) * d;

        let raw: [F128; STATE_SIZE] = if start {
            let a0 = rng.f128();
            let a1 = rng.f128();
            cols[A0][w] = a0;
            cols[A1][w] = a1;
            [a0, a1, F128::ZERO, F128::ZERO]
        } else {
            let sib = rng.f128();
            cols[SIB][w] = sib;
            let (x, y) = if d == F128::ONE {
                (sib, carry_prev)
            } else {
                (carry_prev, sib)
            };
            [x, y, F128::ZERO, F128::ZERO]
        };

        let mut state = initial_mds(raw);
        for j in 0..STATE_SIZE {
            s0[j][w] = state[j];
        }
        for q in 0..N_ROUNDS {
            state = apply_round(q, state);
        }
        for j in 0..STATE_SIZE {
            s_out[j][w] = state[j];
        }
        cols[C][w] = state[0];
        cols[O][w] = cols[END][w] * state[0];
        carry_prev = state[0];
    }

    Family {
        committed: cols,
        s0,
        s_out,
    }
}

/// Wiring terms of the substitution relation for the α-batched target
/// `Σ_e α^{e+1}·S_in,e~(τ)`: with `m_j = Σ_e α^{e+1}·MDS_FULL[e][j]`,
///
///   Σ_j m_j·raw_j,  raw_0 = START·A0 + G0·C(w−1) + G1·SIB,
///                   raw_1 = START·A1 + G1·C(w−1) + G0·SIB,
///                   raw_2 = raw_3 = 0.
pub fn substitution_terms(alpha: F128) -> Vec<RelationTerm> {
    use noid_poseidon2b::native::permutation::MDS_FULL;
    let flat = |v: u128| -> F128 {
        let f = noid_core::hardware::tower_to_flat_u128(v);
        F128 {
            lo: f as u64,
            hi: (f >> 64) as u64,
        }
    };
    let mut alphas = [F128::ZERO; STATE_SIZE];
    let mut p = F128::ONE;
    for a in alphas.iter_mut() {
        p = p * alpha;
        *a = p;
    }
    let m: [F128; STATE_SIZE] = std::array::from_fn(|j| {
        let mut acc = F128::ZERO;
        for e in 0..STATE_SIZE {
            acc += alphas[e] * flat(MDS_FULL[e][j]);
        }
        acc
    });
    vec![
        RelationTerm {
            coeff: m[0],
            factors: vec![ColRef::Committed(START), ColRef::Committed(A0)],
        },
        RelationTerm {
            coeff: m[0],
            factors: vec![ColRef::Committed(G0), ColRef::CommittedShift(C)],
        },
        RelationTerm {
            coeff: m[0],
            factors: vec![ColRef::Committed(G1), ColRef::Committed(SIB)],
        },
        RelationTerm {
            coeff: m[1],
            factors: vec![ColRef::Committed(START), ColRef::Committed(A1)],
        },
        RelationTerm {
            coeff: m[1],
            factors: vec![ColRef::Committed(G1), ColRef::CommittedShift(C)],
        },
        RelationTerm {
            coeff: m[1],
            factors: vec![ColRef::Committed(G0), ColRef::Committed(SIB)],
        },
    ]
}

/// Selector-consistency terms: `0 = Σ eq·[G0 + 1 + START + D + START·D]`
/// and `0 = Σ eq·[G1 + D + START·D]` (G1 = (1+START)·D).
pub fn g0_terms() -> Vec<RelationTerm> {
    vec![
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(G0)],
        },
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![],
        },
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(START)],
        },
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(D)],
        },
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(START), ColRef::Committed(D)],
        },
    ]
}

pub fn g1_terms() -> Vec<RelationTerm> {
    vec![
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(G1)],
        },
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(D)],
        },
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(START), ColRef::Committed(D)],
        },
    ]
}

/// One committed-column claim to discharge at the end (the stand-in for a
/// public-IO PCS claim).
pub struct PendingClaim {
    pub col: usize,
    pub point: Vec<F128>,
    pub value: F128,
    pub what: &'static str,
}

/// Run the whole family protocol; returns the pending committed-column
/// claims (verifier view) for the caller to discharge.
pub fn run_family<Ch: Challenger>(
    fam: &Family,
    prove: bool,
    transcript: &mut Ch,
    proofs: &mut FamilyProofs,
) -> Result<Vec<PendingClaim>, String> {
    let committed_refs: Vec<&[F128]> = fam.committed.iter().map(|c| c.as_slice()).collect();
    let mut pending = Vec::new();

    // ---- Booleanity of D.
    let bool_terms = vec![
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(D), ColRef::Committed(D)],
        },
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(D)],
        },
    ];
    let rho = transcript.sample_f128_vec(W_LOG);
    let point = if prove {
        let cols = RelationColumns {
            committed: &committed_refs,
            internal: &[],
            fixed: &[],
        };
        let (p, pt, _) = prove_column_relation(F128::ZERO, &rho, &bool_terms, &cols, transcript);
        proofs.booleanity = Some(p);
        pt
    } else {
        let p = proofs.booleanity.as_ref().ok_or("missing booleanity")?;
        verify_column_relation(W_LOG, F128::ZERO, &rho, &bool_terms, &[], p, transcript)
            .map_err(|e| format!("booleanity: {e}"))?
    };
    let bool_proof = proofs.booleanity.as_ref().unwrap();
    pending.push(PendingClaim {
        col: D,
        point: point.clone(),
        value: bool_proof.final_values[0],
        what: "booleanity D",
    });

    // ---- Selector-consistency for G0/G1.
    for (terms, name) in [(g0_terms(), "G0"), (g1_terms(), "G1")] {
        let rho = transcript.sample_f128_vec(W_LOG);
        let slot = if name == "G0" {
            &mut proofs.g0
        } else {
            &mut proofs.g1
        };
        let point = if prove {
            let cols = RelationColumns {
                committed: &committed_refs,
                internal: &[],
                fixed: &[],
            };
            let (p, pt, _) = prove_column_relation(F128::ZERO, &rho, &terms, &cols, transcript);
            *slot = Some(p);
            pt
        } else {
            let p = slot.as_ref().ok_or("missing selector proof")?;
            verify_column_relation(W_LOG, F128::ZERO, &rho, &terms, &[], p, transcript)
                .map_err(|e| format!("{name}: {e}"))?
        };
        let proof = slot.as_ref().unwrap();
        let refs = distinct_refs(&terms);
        for (r, v) in refs.iter().zip(proof.final_values.iter()) {
            if let ColRef::Committed(c) = r {
                pending.push(PendingClaim {
                    col: *c,
                    point: point.clone(),
                    value: *v,
                    what: "selector consistency",
                });
            }
        }
    }

    // ---- Selection: 0 = Σ eq·[C + S_out_0] → S_out lane-0 claim.
    let sel_terms = vec![
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(C)],
        },
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Internal(0)],
        },
    ];
    let rho_sel = transcript.sample_f128_vec(W_LOG);
    let sel_point = if prove {
        let internal: Vec<&[F128]> = vec![&fam.s_out[0]];
        let cols = RelationColumns {
            committed: &committed_refs,
            internal: &internal,
            fixed: &[],
        };
        let (p, pt, _) = prove_column_relation(F128::ZERO, &rho_sel, &sel_terms, &cols, transcript);
        proofs.selection = Some(p);
        pt
    } else {
        let p = proofs.selection.as_ref().ok_or("missing selection")?;
        verify_column_relation(W_LOG, F128::ZERO, &rho_sel, &sel_terms, &[], p, transcript)
            .map_err(|e| format!("selection: {e}"))?
    };
    let sel_proof = proofs.selection.as_ref().unwrap();
    pending.push(PendingClaim {
        col: C,
        point: sel_point.clone(),
        value: sel_proof.final_values[0],
        what: "selection C",
    });
    let s_out0_at_sel = sel_proof.final_values[1];

    // ---- Output exposure: 0 = Σ eq·[O + END·S_out_0].
    let out_terms = vec![
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(O)],
        },
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Committed(END), ColRef::Internal(0)],
        },
    ];
    let rho_out = transcript.sample_f128_vec(W_LOG);
    let out_point = if prove {
        let internal: Vec<&[F128]> = vec![&fam.s_out[0]];
        let cols = RelationColumns {
            committed: &committed_refs,
            internal: &internal,
            fixed: &[],
        };
        let (p, pt, _) = prove_column_relation(F128::ZERO, &rho_out, &out_terms, &cols, transcript);
        proofs.output = Some(p);
        pt
    } else {
        let p = proofs.output.as_ref().ok_or("missing output")?;
        verify_column_relation(W_LOG, F128::ZERO, &rho_out, &out_terms, &[], p, transcript)
            .map_err(|e| format!("output: {e}"))?
    };
    let out_proof = proofs.output.as_ref().unwrap();
    let refs = distinct_refs(&out_terms);
    for (r, v) in refs.iter().zip(out_proof.final_values.iter()) {
        if let ColRef::Committed(c) = r {
            pending.push(PendingClaim {
                col: *c,
                point: out_point.clone(),
                value: *v,
                what: "output exposure",
            });
        }
    }
    let s_out0_at_out = *out_proof
        .final_values
        .last()
        .expect("output relation has values");

    // ---- The walk. Start groups carry the two S_out lane-0 claims; lanes
    // 1..3 are prover-supplied (they are absorbed, and a lie shifts the
    // terminal claim off the committed wiring).
    let groups: Vec<LaneClaimGroup> = if prove {
        let g = |pt: &Vec<F128>, lane0: F128| LaneClaimGroup {
            point: pt.clone(),
            values: [
                lane0,
                mle_eval(&fam.s_out[1], pt),
                mle_eval(&fam.s_out[2], pt),
                mle_eval(&fam.s_out[3], pt),
            ],
        };
        let groups = vec![g(&sel_point, s_out0_at_sel), g(&out_point, s_out0_at_out)];
        proofs.walk_groups = Some(groups.clone());
        groups
    } else {
        let groups = proofs.walk_groups.as_ref().ok_or("missing groups")?.clone();
        // Lane-0 values MUST equal the relation-produced claims.
        if groups.len() != 2
            || groups[0].point != sel_point
            || groups[0].values[0] != s_out0_at_sel
            || groups[1].point != out_point
            || groups[1].values[0] != s_out0_at_out
        {
            return Err("walk start groups desync".into());
        }
        groups
    };
    let terminal = if prove {
        let (p, t) = prove_deep_chain_walk(&fam.s0, &groups, transcript);
        proofs.walk = Some(p);
        t
    } else {
        let p = proofs.walk.as_ref().ok_or("missing walk")?;
        verify_deep_chain_walk(W_LOG, &groups, p, transcript).map_err(|e| format!("walk: {e}"))?
    };

    // ---- Substitution: the walk terminal through the wiring.
    let alpha = transcript.sample_f128();
    let sub_terms = substitution_terms(alpha);
    let mut target = F128::ZERO;
    let mut p = F128::ONE;
    for e in 0..STATE_SIZE {
        p = p * alpha;
        target += p * terminal.values[e];
    }
    let sub_point = if prove {
        let cols = RelationColumns {
            committed: &committed_refs,
            internal: &[],
            fixed: &[],
        };
        let (pr, pt, _) =
            prove_column_relation(target, &terminal.point, &sub_terms, &cols, transcript);
        proofs.substitution = Some(pr);
        pt
    } else {
        let pr = proofs.substitution.as_ref().ok_or("missing substitution")?;
        verify_column_relation(
            W_LOG,
            target,
            &terminal.point,
            &sub_terms,
            &[],
            pr,
            transcript,
        )
        .map_err(|e| format!("substitution: {e}"))?
    };
    let sub_proof = proofs.substitution.as_ref().unwrap();
    let refs = distinct_refs(&sub_terms);
    let mut shift_target = None;
    for (r, v) in refs.iter().zip(sub_proof.final_values.iter()) {
        match r {
            ColRef::Committed(c) => pending.push(PendingClaim {
                col: *c,
                point: sub_point.clone(),
                value: *v,
                what: "substitution",
            }),
            ColRef::CommittedShift(c) => {
                assert_eq!(*c, C);
                shift_target = Some(*v);
            }
            ColRef::Internal(_)
            | ColRef::Fixed(_)
            | ColRef::CommittedShift2(_)
            | ColRef::Window { .. } => {
                unreachable!("substitution touches committed data only")
            }
        }
    }

    // ---- Shift discharge for the carried column claim.
    let shift_target = shift_target.expect("wiring references the carry shift");
    let shift_point = if prove {
        let (pr, pt) =
            prove_shift_discharge(&fam.committed[C], &sub_point, shift_target, transcript);
        proofs.shift = Some(pr);
        pt
    } else {
        let pr = proofs.shift.as_ref().ok_or("missing shift")?;
        verify_shift_discharge(W_LOG, &sub_point, shift_target, pr, transcript)
            .map_err(|e| format!("shift: {e}"))?
    };
    pending.push(PendingClaim {
        col: C,
        point: shift_point,
        value: proofs.shift.as_ref().unwrap().final_value,
        what: "shift discharge C",
    });

    Ok(pending)
}

#[derive(Default)]
pub struct FamilyProofs {
    pub booleanity: Option<ColumnRelationProof>,
    pub g0: Option<ColumnRelationProof>,
    pub g1: Option<ColumnRelationProof>,
    pub selection: Option<ColumnRelationProof>,
    pub output: Option<ColumnRelationProof>,
    pub walk_groups: Option<Vec<LaneClaimGroup>>,
    pub walk: Option<DeepChainWalkProof>,
    pub substitution: Option<ColumnRelationProof>,
    pub shift: Option<ShiftDischargeProof>,
}

/// Discharge every pending claim directly against the columns — the
/// stand-in for the batched PCS opening.
pub fn discharge(fam: &Family, pending: &[PendingClaim]) -> Result<(), String> {
    for c in pending {
        let got = mle_eval(&fam.committed[c.col], &c.point);
        if got != c.value {
            return Err(format!("claim '{}' on column {} is false", c.what, c.col));
        }
    }
    Ok(())
}
