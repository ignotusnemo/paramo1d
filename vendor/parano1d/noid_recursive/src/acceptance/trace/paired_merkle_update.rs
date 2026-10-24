// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Fixed-depth paired Merkle-update columns for the exact-state region.
//!
//! One update hashes an old and a new leaf through the SAME sibling and
//! direction vector.  Every level occupies four permutation slots:
//!
//! ```text
//! old-even, old-odd, new-even, new-odd
//! ```
//!
//! The nine logical committed columns are, in order,
//! `C0..C3, E0, E1, SIB0, SIB1, D`. Each level repeats `SIB/D` across its
//! four slots, and a predecessor-shift consistency relation ties the three
//! adjacent copies to the old-even source. The two independent digest chains
//! avoid a shift-3 by using otherwise idle odd `E` cells as bridges:
//!
//! - `new-odd.E = old-odd.C` carries the old parent to the next old level;
//! - the next `old-odd.E = previous new-odd.C` carries the new parent to
//!   the next new level.
//!
//! Both bridge equations are `E(w) = C(w-2)`.  Consequently this primitive
//! uses only the already supported one- and two-slot column shifts.

use noid_ivc_core::deep_chain::relations::{ColRef, FixedPattern, RelationTerm};
use noid_ivc_core::deep_chain::schedule::flat_of_tower_u128;
use noid_ivc_core::deep_chain::{apply_round, initial_mds};
use noid_ivc_core::field::F128;
use noid_poseidon2b::native::permutation::{MDS_FULL, N_ROUNDS, STATE_SIZE};

/// Production segment depth.  Each update always occupies exactly 64 slots.
pub const PAIRED_UPDATE_DEPTH: usize = 16;
pub const PAIRED_UPDATE_SLOTS_PER_LEVEL: usize = 4;
pub const PAIRED_UPDATE_STRIDE: usize = PAIRED_UPDATE_DEPTH * PAIRED_UPDATE_SLOTS_PER_LEVEL;

/// Exact active slot geometry before dyadic domain padding.
pub const fn paired_update_slots(updates: usize) -> usize {
    updates * PAIRED_UPDATE_STRIDE
}

/// One shared-sibling old/new update witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairedMerkleUpdateWitness {
    pub old_entry: [F128; 2],
    pub new_entry: [F128; 2],
    pub siblings: [[F128; 2]; PAIRED_UPDATE_DEPTH],
    /// `true`: the carried digest is the right child.
    pub directions: [bool; PAIRED_UPDATE_DEPTH],
}

impl PairedMerkleUpdateWitness {
    /// Canonical padding used by the honest native builder.  Its roots are
    /// computed normally; they are not assumed to be zero because
    /// `H(0, 0) != 0`.
    ///
    /// The paired-walk relations do not themselves zero-pin a dead update.
    /// A caller that consumes padding endpoints must separately bind the live
    /// prefix or constrain the dead suffix to this value.
    pub const fn canonical_ghost() -> Self {
        Self {
            old_entry: [F128::ZERO; 2],
            new_entry: [F128::ZERO; 2],
            siblings: [[F128::ZERO; 2]; PAIRED_UPDATE_DEPTH],
            directions: [false; PAIRED_UPDATE_DEPTH],
        }
    }
}

/// Native committed columns plus the prover-side walk endpoints.
pub struct PairedMerkleUpdateColumns {
    pub c: [Vec<F128>; STATE_SIZE],
    pub e: [Vec<F128>; 2],
    pub sib: [Vec<F128>; 2],
    pub d: Vec<F128>,
    pub s0: [Vec<F128>; STATE_SIZE],
    pub s_out: [Vec<F128>; STATE_SIZE],
    /// Full-16-level roots, including the honest builder's canonical padding
    /// updates filling the dyadic domain.  Use [`Self::update_roots_at_depth`]
    /// for a shorter upper path.  These native values are not proof-level pins.
    pub roots_before: Vec<[F128; 2]>,
    /// Full-16-level roots, including the honest builder's canonical padding
    /// updates filling the dyadic domain.  Use [`Self::update_roots_at_depth`]
    /// for a shorter upper path.  These native values are not proof-level pins.
    pub roots_after: Vec<[F128; 2]>,
    pub live_updates: usize,
}

impl PairedMerkleUpdateColumns {
    /// The required logical commitment order: `C0..C3,E0,E1,SIB0,SIB1,D`.
    pub fn committed_columns(&self) -> Vec<&[F128]> {
        vec![
            &self.c[0],
            &self.c[1],
            &self.c[2],
            &self.c[3],
            &self.e[0],
            &self.e[1],
            &self.sib[0],
            &self.sib[1],
            &self.d,
        ]
    }

    /// Read one update's native before/after roots after `depth` levels.
    ///
    /// This is an extraction helper, not an authentication relation.  A proof
    /// consumer must still pin the returned `C` cells to the endpoint wires it
    /// uses elsewhere.  In particular, a depth-8 upper path uses slots 29/31
    /// even though the fixed walk continues through all 16 levels.
    pub fn update_roots_at_depth(&self, update: usize, depth: usize) -> ([F128; 2], [F128; 2]) {
        let capacity = self.c[0].len() / PAIRED_UPDATE_STRIDE;
        assert!(update < capacity, "paired-update index outside the domain");
        let [before_offset, after_offset] = paired_update_root_offsets(depth);
        let base = update * PAIRED_UPDATE_STRIDE;
        (
            [
                self.c[0][base + before_offset],
                self.c[1][base + before_offset],
            ],
            [
                self.c[0][base + after_offset],
                self.c[1][base + after_offset],
            ],
        )
    }
}

/// Root-cell offsets inside one 64-slot update after `depth` levels.
///
/// The before root is the old odd slot and the after root is the new odd slot:
/// `4 * (depth - 1) + 1` and `4 * (depth - 1) + 3`, respectively.
pub fn paired_update_root_offsets(depth: usize) -> [usize; 2] {
    assert!(
        (1..=PAIRED_UPDATE_DEPTH).contains(&depth),
        "paired-update root depth must be in 1..=16"
    );
    let level_base = PAIRED_UPDATE_SLOTS_PER_LEVEL * (depth - 1);
    [level_base + 1, level_base + 3]
}

/// Build a complete dyadic family.  Missing updates use canonical honest-
/// builder padding, so fixed patterns cover the entire domain and never depend
/// on live content.  The relations alone do not prove that the padding cells
/// are zero; callers must either ignore them behind a bound live prefix or add
/// explicit dead-suffix constraints.
pub fn build_paired_merkle_update_columns(
    updates: &[PairedMerkleUpdateWitness],
    iv_flat: [F128; 2],
    w_log: usize,
) -> PairedMerkleUpdateColumns {
    let w = 1usize << w_log;
    assert_eq!(
        w % PAIRED_UPDATE_STRIDE,
        0,
        "paired-update domain must contain whole 64-slot updates"
    );
    let capacity = w / PAIRED_UPDATE_STRIDE;
    assert!(
        updates.len() <= capacity,
        "paired-update witnesses exceed the dyadic domain"
    );

    let mut c: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut e: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut sib: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut d = vec![F128::ZERO; w];
    let mut s0: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut s_out: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);

    for update in 0..capacity {
        let witness = updates
            .get(update)
            .cloned()
            .unwrap_or_else(PairedMerkleUpdateWitness::canonical_ghost);
        let base = update * PAIRED_UPDATE_STRIDE;
        e[0][base] = witness.old_entry[0];
        e[1][base] = witness.old_entry[1];
        e[0][base + 2] = witness.new_entry[0];
        e[1][base + 2] = witness.new_entry[1];
        for level in 0..PAIRED_UPDATE_DEPTH {
            let old_even = base + PAIRED_UPDATE_SLOTS_PER_LEVEL * level;
            for lane in 0..2 {
                for slot in old_even..old_even + PAIRED_UPDATE_SLOTS_PER_LEVEL {
                    sib[lane][slot] = witness.siblings[level][lane];
                }
            }
            let direction = if witness.directions[level] {
                F128::ONE
            } else {
                F128::ZERO
            };
            for slot in old_even..old_even + PAIRED_UPDATE_SLOTS_PER_LEVEL {
                d[slot] = direction;
            }
        }
    }

    let mut carry = [F128::ZERO; STATE_SIZE];
    for slot in 0..w {
        let local = slot & (PAIRED_UPDATE_STRIDE - 1);
        let level = local / PAIRED_UPDATE_SLOTS_PER_LEVEL;
        let role = local % PAIRED_UPDATE_SLOTS_PER_LEVEL;

        // Odd E cells are bridge cells only.  Level-zero old-odd has no
        // predecessor inside its update and remains canonical zero.
        if role == 1 && level > 0 {
            for lane in 0..2 {
                e[lane][slot] = c[lane][slot - 2];
            }
        } else if role == 3 {
            for lane in 0..2 {
                e[lane][slot] = c[lane][slot - 2];
            }
        }

        let raw = match role {
            0 | 2 => {
                let current_at = if level == 0 { slot } else { slot - 1 };
                let direction = d[slot];
                let left = |lane: usize| {
                    (F128::ONE + direction) * e[lane][current_at] + direction * sib[lane][slot]
                };
                [left(0), left(1), iv_flat[0], iv_flat[1]]
            }
            1 | 3 => {
                let even = slot - 1;
                let current_at = if level == 0 { even } else { slot - 2 };
                let direction = d[even];
                let right = |lane: usize| {
                    direction * e[lane][current_at] + (F128::ONE + direction) * sib[lane][even]
                };
                [carry[0] + right(0), carry[1] + right(1), carry[2], carry[3]]
            }
            _ => unreachable!(),
        };

        let mut state = initial_mds(raw);
        for lane in 0..STATE_SIZE {
            s0[lane][slot] = state[lane];
        }
        for round in 0..N_ROUNDS {
            state = apply_round(round, state);
        }
        for lane in 0..STATE_SIZE {
            s_out[lane][slot] = state[lane];
            c[lane][slot] = state[lane];
        }
        carry = state;
    }

    let mut roots_before = Vec::with_capacity(capacity);
    let mut roots_after = Vec::with_capacity(capacity);
    let [before_offset, after_offset] = paired_update_root_offsets(PAIRED_UPDATE_DEPTH);
    for update in 0..capacity {
        let base = update * PAIRED_UPDATE_STRIDE;
        roots_before.push([c[0][base + before_offset], c[1][base + before_offset]]);
        roots_after.push([c[0][base + after_offset], c[1][base + after_offset]]);
    }

    PairedMerkleUpdateColumns {
        c,
        e,
        sib,
        d,
        s0,
        s_out,
        roots_before,
        roots_after,
        live_updates: updates.len(),
    }
}

/// Fixed-pattern references used by the two relations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PairedMerkleUpdateRefs {
    pub c: [usize; STATE_SIZE],
    pub e: [usize; 2],
    pub sib: [usize; 2],
    pub d: usize,
    pub even: usize,
    pub even_start: usize,
    pub even_nonstart: usize,
    pub odd: usize,
    pub odd_start: usize,
    pub odd_nonstart: usize,
    pub old_even: usize,
    pub copy_step: usize,
    pub bridge: usize,
    pub iv: [usize; 2],
}

/// Map the required nine-column order and the eleven fixed patterns.
pub fn paired_merkle_update_refs(
    committed_base: usize,
    fixed_base: usize,
) -> PairedMerkleUpdateRefs {
    PairedMerkleUpdateRefs {
        c: std::array::from_fn(|lane| committed_base + lane),
        e: [committed_base + 4, committed_base + 5],
        sib: [committed_base + 6, committed_base + 7],
        d: committed_base + 8,
        even: fixed_base,
        even_start: fixed_base + 1,
        even_nonstart: fixed_base + 2,
        odd: fixed_base + 3,
        odd_start: fixed_base + 4,
        odd_nonstart: fixed_base + 5,
        old_even: fixed_base + 6,
        copy_step: fixed_base + 7,
        bridge: fixed_base + 8,
        iv: [fixed_base + 9, fixed_base + 10],
    }
}

/// Period-64 fixed patterns.  Their shape is independent of update contents
/// and of how many leading updates are live.
pub fn paired_merkle_update_fixed_patterns(iv_flat: [F128; 2]) -> Vec<FixedPattern> {
    let mut even = vec![F128::ZERO; PAIRED_UPDATE_STRIDE];
    let mut even_start = vec![F128::ZERO; PAIRED_UPDATE_STRIDE];
    let mut even_nonstart = vec![F128::ZERO; PAIRED_UPDATE_STRIDE];
    let mut odd = vec![F128::ZERO; PAIRED_UPDATE_STRIDE];
    let mut odd_start = vec![F128::ZERO; PAIRED_UPDATE_STRIDE];
    let mut odd_nonstart = vec![F128::ZERO; PAIRED_UPDATE_STRIDE];
    let mut old_even = vec![F128::ZERO; PAIRED_UPDATE_STRIDE];
    let mut copy_step = vec![F128::ZERO; PAIRED_UPDATE_STRIDE];
    let mut bridge = vec![F128::ZERO; PAIRED_UPDATE_STRIDE];
    let mut iv0 = vec![F128::ZERO; PAIRED_UPDATE_STRIDE];
    let mut iv1 = vec![F128::ZERO; PAIRED_UPDATE_STRIDE];

    for level in 0..PAIRED_UPDATE_DEPTH {
        let base = PAIRED_UPDATE_SLOTS_PER_LEVEL * level;
        for at in [base, base + 2] {
            even[at] = F128::ONE;
            iv0[at] = iv_flat[0];
            iv1[at] = iv_flat[1];
            if level == 0 {
                even_start[at] = F128::ONE;
            } else {
                even_nonstart[at] = F128::ONE;
            }
        }
        for at in [base + 1, base + 3] {
            odd[at] = F128::ONE;
            if level == 0 {
                odd_start[at] = F128::ONE;
            } else {
                odd_nonstart[at] = F128::ONE;
            }
        }
        old_even[base] = F128::ONE;
        for at in base + 1..base + PAIRED_UPDATE_SLOTS_PER_LEVEL {
            copy_step[at] = F128::ONE;
        }
        bridge[base + 3] = F128::ONE;
        if level > 0 {
            bridge[base + 1] = F128::ONE;
        }
    }

    let pattern = |table| FixedPattern::new(6, table);
    vec![
        pattern(even),
        pattern(even_start),
        pattern(even_nonstart),
        pattern(odd),
        pattern(odd_start),
        pattern(odd_nonstart),
        pattern(old_even),
        pattern(copy_step),
        pattern(bridge),
        pattern(iv0),
        pattern(iv1),
    ]
}

/// Zero relation for direction booleanity, odd-E bridges, and the adjacent
/// sibling/direction copy chain within each four-slot level. Independent
/// equations use powers of a post-commitment mixing challenge.
///
/// Soundness requires all nine committed columns to be committed and absorbed
/// into the Fiat-Shamir transcript before `mix` is sampled.  If the witness can
/// depend on `mix`, residuals from independent equations can be chosen to
/// cancel.  The native algebraic test harness below checks the resulting
/// relation but intentionally does not prove this transcript ordering.
pub fn paired_merkle_update_consistency_terms(
    refs: &PairedMerkleUpdateRefs,
    mix: F128,
) -> Vec<RelationTerm> {
    let mut terms = Vec::new();
    let mut weight = F128::ONE;
    let mut equation = |left: Vec<ColRef>, right: Vec<ColRef>| {
        terms.push(RelationTerm {
            coeff: weight,
            factors: left,
        });
        terms.push(RelationTerm {
            coeff: weight,
            factors: right,
        });
        weight = weight * mix;
    };

    equation(
        vec![
            ColRef::Fixed(refs.old_even),
            ColRef::Committed(refs.d),
            ColRef::Committed(refs.d),
        ],
        vec![ColRef::Fixed(refs.old_even), ColRef::Committed(refs.d)],
    );
    for lane in 0..2 {
        equation(
            vec![ColRef::Fixed(refs.bridge), ColRef::Committed(refs.e[lane])],
            vec![
                ColRef::Fixed(refs.bridge),
                ColRef::CommittedShift2(refs.c[lane]),
            ],
        );
    }
    for lane in 0..2 {
        equation(
            vec![
                ColRef::Fixed(refs.copy_step),
                ColRef::Committed(refs.sib[lane]),
            ],
            vec![
                ColRef::Fixed(refs.copy_step),
                ColRef::CommittedShift(refs.sib[lane]),
            ],
        );
    }
    equation(
        vec![ColRef::Fixed(refs.copy_step), ColRef::Committed(refs.d)],
        vec![
            ColRef::Fixed(refs.copy_step),
            ColRef::CommittedShift(refs.d),
        ],
    );
    terms
}

/// Substitution relation tying the walk layer-0 columns to the paired
/// two-permutation compression schedule.
pub fn paired_merkle_update_substitution_terms(
    refs: &PairedMerkleUpdateRefs,
    alpha: F128,
) -> Vec<RelationTerm> {
    let flat = |value: u128| flat_of_tower_u128(value);
    let mut alpha_powers = [F128::ZERO; STATE_SIZE];
    let mut power = F128::ONE;
    for value in &mut alpha_powers {
        power = power * alpha;
        *value = power;
    }
    let m: [F128; STATE_SIZE] = std::array::from_fn(|raw_lane| {
        let mut value = F128::ZERO;
        for output_lane in 0..STATE_SIZE {
            value += alpha_powers[output_lane] * flat(MDS_FULL[output_lane][raw_lane]);
        }
        value
    });

    let mut terms = Vec::new();
    for lane in 0..2 {
        let c_shift = ColRef::CommittedShift(refs.c[lane]);
        let e = ColRef::Committed(refs.e[lane]);
        let e_shift = ColRef::CommittedShift(refs.e[lane]);
        let e_shift2 = ColRef::CommittedShift2(refs.e[lane]);
        let sib = ColRef::Committed(refs.sib[lane]);
        let sib_shift = ColRef::CommittedShift(refs.sib[lane]);
        let d = ColRef::Committed(refs.d);
        let d_shift = ColRef::CommittedShift(refs.d);
        for factors in [
            vec![c_shift],
            vec![ColRef::Fixed(refs.even), c_shift],
            vec![ColRef::Fixed(refs.even_start), e],
            vec![ColRef::Fixed(refs.even_start), d, e],
            vec![ColRef::Fixed(refs.even_nonstart), e_shift],
            vec![ColRef::Fixed(refs.even_nonstart), d, e_shift],
            vec![ColRef::Fixed(refs.even), d, sib],
            vec![ColRef::Fixed(refs.odd), sib_shift],
            vec![ColRef::Fixed(refs.odd), d_shift, sib_shift],
            vec![ColRef::Fixed(refs.odd_start), d_shift, e_shift],
            vec![ColRef::Fixed(refs.odd_nonstart), d_shift, e_shift2],
        ] {
            terms.push(RelationTerm {
                coeff: m[lane],
                factors,
            });
        }
    }
    for lane in 2..STATE_SIZE {
        let c_shift = ColRef::CommittedShift(refs.c[lane]);
        terms.push(RelationTerm {
            coeff: m[lane],
            factors: vec![c_shift],
        });
        terms.push(RelationTerm {
            coeff: m[lane],
            factors: vec![ColRef::Fixed(refs.even), c_shift],
        });
        terms.push(RelationTerm {
            coeff: m[lane],
            factors: vec![ColRef::Fixed(refs.iv[lane - 2])],
        });
    }
    terms
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_chain::exact_state_hash::{slot_leaf_hash, state_node_hash, StateHash};
    use noid_chain::fri_state::SlotValue;
    use noid_chain::sparse_merkle::{
        build_multiproof, expand_multiproof_sequential_updates, SparseMerkleCache,
    };
    use noid_core::Block128;
    use noid_ivc_core::challenger::{Challenger, FsLaneChallenger};
    use noid_ivc_core::deep_chain::relations::{
        claimed_refs, prove_column_relation, prove_shift_discharge, prove_shift_discharge_pow2,
        verify_column_relation, verify_shift_discharge, verify_shift_discharge_pow2,
        RelationColumns,
    };
    use noid_ivc_core::deep_chain::schedule::carry_selection_terms;
    use noid_ivc_core::deep_chain::{
        prove_deep_chain_walk, verify_deep_chain_walk, LaneClaimGroup,
    };
    use noid_ivc_core::lincheck::build_eq_table;
    use noid_poseidon2b::native::domain::{capacity_iv, TAG_EXSTNOD};

    struct Rng(u64);

    impl Rng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        fn digest(&mut self) -> StateHash {
            let mut digest = [0u8; 32];
            for chunk in digest.chunks_exact_mut(8) {
                chunk.copy_from_slice(&self.next_u64().to_le_bytes());
            }
            digest
        }
    }

    fn iv_flat() -> [F128; 2] {
        let iv = capacity_iv(TAG_EXSTNOD);
        [flat_of_tower_u128(iv[0].0), flat_of_tower_u128(iv[1].0)]
    }

    fn digest_fields(digest: StateHash) -> [F128; 2] {
        [
            flat_of_tower_u128(u128::from_le_bytes(digest[..16].try_into().unwrap())),
            flat_of_tower_u128(u128::from_le_bytes(digest[16..].try_into().unwrap())),
        ]
    }

    fn witness(
        old_entry: StateHash,
        new_entry: StateHash,
        siblings: &[StateHash],
        directions: &[bool],
    ) -> PairedMerkleUpdateWitness {
        assert_eq!(siblings.len(), PAIRED_UPDATE_DEPTH);
        assert_eq!(directions.len(), PAIRED_UPDATE_DEPTH);
        PairedMerkleUpdateWitness {
            old_entry: digest_fields(old_entry),
            new_entry: digest_fields(new_entry),
            siblings: std::array::from_fn(|level| digest_fields(siblings[level])),
            directions: std::array::from_fn(|level| directions[level]),
        }
    }

    fn fold_path(mut current: StateHash, siblings: &[StateHash], directions: &[bool]) -> StateHash {
        for (&sibling, &right) in siblings.iter().zip(directions) {
            current = if right {
                state_node_hash(sibling, current)
            } else {
                state_node_hash(current, sibling)
            };
        }
        current
    }

    fn mle_eval(column: &[F128], point: &[F128]) -> F128 {
        let eq = build_eq_table(point);
        column
            .iter()
            .zip(eq)
            .fold(F128::ZERO, |acc, (&value, weight)| acc + value * weight)
    }

    fn discharge_relation_claims(
        committed: &[&[F128]],
        refs: &[ColRef],
        values: &[F128],
        point: &[F128],
        w_log: usize,
        prover: &mut FsLaneChallenger,
        verifier: &mut FsLaneChallenger,
        pending: &mut Vec<(usize, Vec<F128>, F128)>,
    ) -> Result<(), String> {
        for (reference, &value) in refs.iter().zip(values) {
            match reference {
                ColRef::Committed(column) => {
                    pending.push((*column, point.to_vec(), value));
                }
                ColRef::CommittedShift(column) => {
                    let (proof, _) =
                        prove_shift_discharge(committed[*column], point, value, prover);
                    let plain_point = verify_shift_discharge(w_log, point, value, &proof, verifier)
                        .map_err(|error| format!("shift: {error}"))?;
                    pending.push((*column, plain_point, proof.final_value));
                }
                ColRef::CommittedShift2(column) => {
                    let (proof, _) =
                        prove_shift_discharge_pow2(committed[*column], point, value, 1, prover);
                    let plain_point =
                        verify_shift_discharge_pow2(w_log, point, value, 1, &proof, verifier)
                            .map_err(|error| format!("shift2: {error}"))?;
                    pending.push((*column, plain_point, proof.final_value));
                }
                ColRef::Internal(_) | ColRef::Fixed(_) | ColRef::Window { .. } => {
                    return Err("unexpected paired-update terminal reference".into());
                }
            }
        }
        Ok(())
    }

    fn verify_native_dag(columns: &PairedMerkleUpdateColumns) -> Result<(), String> {
        let w = columns.c[0].len();
        let w_log = w.trailing_zeros() as usize;
        let fixed = paired_merkle_update_fixed_patterns(iv_flat());
        let refs = paired_merkle_update_refs(0, 0);
        let committed = columns.committed_columns();
        let internal: Vec<&[F128]> = columns.s_out.iter().map(Vec::as_slice).collect();
        let mut prover = FsLaneChallenger::new(b"paired-update-dag-test");
        let mut verifier = FsLaneChallenger::new(b"paired-update-dag-test");
        let mut pending = Vec::new();

        // Algebraic harness only: unlike the production protocol, this test
        // does not commit and absorb `committed` before drawing `mix`.
        let mix = prover.sample_f128();
        assert_eq!(mix, verifier.sample_f128());
        let consistency = paired_merkle_update_consistency_terms(&refs, mix);
        let rho_consistency = prover.sample_f128_vec(w_log);
        assert_eq!(rho_consistency, verifier.sample_f128_vec(w_log));
        let relation_columns = RelationColumns {
            committed: &committed,
            internal: &[],
            fixed: &fixed,
        };
        let (proof, _, _) = prove_column_relation(
            F128::ZERO,
            &rho_consistency,
            &consistency,
            &relation_columns,
            &mut prover,
        );
        let point = verify_column_relation(
            w_log,
            F128::ZERO,
            &rho_consistency,
            &consistency,
            &fixed,
            &proof,
            &mut verifier,
        )
        .map_err(|error| format!("consistency: {error}"))?;
        discharge_relation_claims(
            &committed,
            &claimed_refs(&consistency),
            &proof.final_values,
            &point,
            w_log,
            &mut prover,
            &mut verifier,
            &mut pending,
        )?;

        let beta = prover.sample_f128();
        assert_eq!(beta, verifier.sample_f128());
        let selection = carry_selection_terms(&refs.c, beta);
        let rho_selection = prover.sample_f128_vec(w_log);
        assert_eq!(rho_selection, verifier.sample_f128_vec(w_log));
        let (proof, _, _) = prove_column_relation(
            F128::ZERO,
            &rho_selection,
            &selection,
            &RelationColumns {
                committed: &committed,
                internal: &internal,
                fixed: &fixed,
            },
            &mut prover,
        );
        let selection_point = verify_column_relation(
            w_log,
            F128::ZERO,
            &rho_selection,
            &selection,
            &fixed,
            &proof,
            &mut verifier,
        )
        .map_err(|error| format!("selection: {error}"))?;
        let mut group_values = [F128::ZERO; STATE_SIZE];
        for (reference, &value) in claimed_refs(&selection).iter().zip(&proof.final_values) {
            match reference {
                ColRef::Committed(column) => {
                    pending.push((*column, selection_point.clone(), value));
                }
                ColRef::Internal(lane) => group_values[*lane] = value,
                _ => return Err("unexpected selection terminal reference".into()),
            }
        }

        let groups = vec![LaneClaimGroup {
            point: selection_point,
            values: group_values,
        }];
        let (walk, _) = prove_deep_chain_walk(&columns.s0, &groups, &mut prover);
        let terminal = verify_deep_chain_walk(w_log, &groups, &walk, &mut verifier)
            .map_err(|error| format!("walk: {error}"))?;

        let alpha = prover.sample_f128();
        assert_eq!(alpha, verifier.sample_f128());
        let substitution = paired_merkle_update_substitution_terms(&refs, alpha);
        let mut target = F128::ZERO;
        let mut alpha_power = F128::ONE;
        for lane in 0..STATE_SIZE {
            alpha_power = alpha_power * alpha;
            target += alpha_power * terminal.values[lane];
        }
        let (proof, _, _) = prove_column_relation(
            target,
            &terminal.point,
            &substitution,
            &RelationColumns {
                committed: &committed,
                internal: &[],
                fixed: &fixed,
            },
            &mut prover,
        );
        let point = verify_column_relation(
            w_log,
            target,
            &terminal.point,
            &substitution,
            &fixed,
            &proof,
            &mut verifier,
        )
        .map_err(|error| format!("substitution: {error}"))?;
        discharge_relation_claims(
            &committed,
            &claimed_refs(&substitution),
            &proof.final_values,
            &point,
            w_log,
            &mut prover,
            &mut verifier,
            &mut pending,
        )?;

        assert_eq!(prover.sample_f128(), verifier.sample_f128());
        for (column, point, value) in pending {
            if mle_eval(committed[column], &point) != value {
                return Err(format!("false terminal claim on column {column}"));
            }
        }
        Ok(())
    }

    fn consistency_relation_holds(columns: &PairedMerkleUpdateColumns) -> bool {
        let w = columns.c[0].len();
        let committed = columns.committed_columns();
        let fixed = paired_merkle_update_fixed_patterns(iv_flat());
        let fixed_columns: Vec<_> = fixed.iter().map(|pattern| pattern.materialize(w)).collect();
        let refs = paired_merkle_update_refs(0, 0);
        let mix = F128 {
            lo: 0x91D2_4B7A_6E31_5C0F,
            hi: 0x2874_C9A0_B35E_16D1,
        };
        let terms = paired_merkle_update_consistency_terms(&refs, mix);
        for row in 0..w {
            let mut residual = F128::ZERO;
            for term in &terms {
                let mut value = term.coeff;
                for factor in &term.factors {
                    value = value
                        * match factor {
                            ColRef::Committed(column) => committed[*column][row],
                            ColRef::CommittedShift(column) => row
                                .checked_sub(1)
                                .map_or(F128::ZERO, |at| committed[*column][at]),
                            ColRef::CommittedShift2(column) => row
                                .checked_sub(2)
                                .map_or(F128::ZERO, |at| committed[*column][at]),
                            ColRef::Fixed(pattern) => fixed_columns[*pattern][row],
                            ColRef::Internal(_) | ColRef::Window { .. } => {
                                panic!("unexpected consistency factor")
                            }
                        };
                }
                residual += value;
            }
            if residual != F128::ZERO {
                return false;
            }
        }
        true
    }

    #[test]
    fn paired_roots_match_exact_state_node_hash_paths() {
        let mut rng = Rng(0xA11C_E001);
        let old = rng.digest();
        let new = rng.digest();
        let siblings: Vec<_> = (0..PAIRED_UPDATE_DEPTH).map(|_| rng.digest()).collect();
        let directions: Vec<_> = (0..PAIRED_UPDATE_DEPTH)
            .map(|_| rng.next_u64() & 1 == 1)
            .collect();
        let update = witness(old, new, &siblings, &directions);
        let columns = build_paired_merkle_update_columns(&[update], iv_flat(), 6);

        assert_eq!(
            columns.roots_before[0],
            digest_fields(fold_path(old, &siblings, &directions))
        );
        assert_eq!(
            columns.roots_after[0],
            digest_fields(fold_path(new, &siblings, &directions))
        );
        assert!(consistency_relation_holds(&columns));
        verify_native_dag(&columns).expect("honest paired-update DAG");
    }

    #[test]
    fn root_extraction_supports_upper_depth_eight_and_full_sixteen() {
        let mut rng = Rng(0xA11C_E005);
        let old = rng.digest();
        let new = rng.digest();
        let siblings: Vec<_> = (0..PAIRED_UPDATE_DEPTH).map(|_| rng.digest()).collect();
        let directions: Vec<_> = (0..PAIRED_UPDATE_DEPTH)
            .map(|_| rng.next_u64() & 1 == 1)
            .collect();
        let columns = build_paired_merkle_update_columns(
            &[witness(old, new, &siblings, &directions)],
            iv_flat(),
            6,
        );

        assert_eq!(paired_update_root_offsets(8), [29, 31]);
        assert_eq!(paired_update_root_offsets(16), [61, 63]);
        for depth in [8, PAIRED_UPDATE_DEPTH] {
            let (before, after) = columns.update_roots_at_depth(0, depth);
            assert_eq!(
                before,
                digest_fields(fold_path(old, &siblings[..depth], &directions[..depth]))
            );
            assert_eq!(
                after,
                digest_fields(fold_path(new, &siblings[..depth], &directions[..depth]))
            );
        }
    }

    #[test]
    fn sibling_and_direction_copies_are_algebraically_required() {
        let mut rng = Rng(0xA11C_E002);
        let siblings: Vec<_> = (0..PAIRED_UPDATE_DEPTH).map(|_| rng.digest()).collect();
        let directions: Vec<_> = (0..PAIRED_UPDATE_DEPTH)
            .map(|_| rng.next_u64() & 1 == 1)
            .collect();
        let update = witness(rng.digest(), rng.digest(), &siblings, &directions);
        let columns = build_paired_merkle_update_columns(&[update], iv_flat(), 6);
        assert!(consistency_relation_holds(&columns));

        let mut bad_sibling = build_paired_merkle_update_columns(
            &[witness(rng.digest(), rng.digest(), &siblings, &directions)],
            iv_flat(),
            6,
        );
        bad_sibling.sib[0][2] += F128::ONE;
        assert!(!consistency_relation_holds(&bad_sibling));

        let mut bad_direction = columns;
        bad_direction.d[2] += F128::ONE;
        assert!(!consistency_relation_holds(&bad_direction));
    }

    #[test]
    fn bridge_cells_and_old_direction_booleanity_are_required() {
        let mut rng = Rng(0xA11C_E006);
        let siblings: Vec<_> = (0..PAIRED_UPDATE_DEPTH).map(|_| rng.digest()).collect();
        let directions: Vec<_> = (0..PAIRED_UPDATE_DEPTH)
            .map(|_| rng.next_u64() & 1 == 1)
            .collect();
        let update = witness(rng.digest(), rng.digest(), &siblings, &directions);

        // Level-zero new-odd carries the old parent toward the next old-even.
        let mut bad_old_bridge =
            build_paired_merkle_update_columns(&[update.clone()], iv_flat(), 6);
        bad_old_bridge.e[0][3] += F128::ONE;
        assert!(!consistency_relation_holds(&bad_old_bridge));

        // Level-one old-odd carries the preceding new parent to new-even.
        let mut bad_new_bridge =
            build_paired_merkle_update_columns(&[update.clone()], iv_flat(), 6);
        bad_new_bridge.e[1][5] += F128::ONE;
        assert!(!consistency_relation_holds(&bad_new_bridge));

        // Keep the direction-copy chain equal so this failure isolates the
        // old-even booleanity equation.
        let mut non_boolean = build_paired_merkle_update_columns(&[update], iv_flat(), 6);
        let value = flat_of_tower_u128(2);
        assert_ne!(value, F128::ZERO);
        assert_ne!(value, F128::ONE);
        non_boolean.d[..PAIRED_UPDATE_SLOTS_PER_LEVEL].fill(value);
        assert!(!consistency_relation_holds(&non_boolean));
    }

    #[test]
    fn two_sequential_updates_chain_end_to_end() {
        let old_a = slot_leaf_hash(SlotValue::with_owner_fields(
            11,
            1,
            [Block128::from(2u128), Block128::from(3u128)],
        ));
        let old_b = slot_leaf_hash(SlotValue::with_owner_fields(
            17,
            2,
            [Block128::from(4u128), Block128::from(5u128)],
        ));
        let new_a = slot_leaf_hash(SlotValue::EMPTY);
        let new_b = slot_leaf_hash(SlotValue::with_owner_fields(
            19,
            3,
            [Block128::from(6u128), Block128::from(7u128)],
        ));
        let indices = [7, 32_769];
        let cache = SparseMerkleCache::from_leaves(16, &[(indices[0], old_a), (indices[1], old_b)])
            .unwrap();
        let proof = build_multiproof(&cache, &indices, 16).unwrap();
        let steps = expand_multiproof_sequential_updates(
            &indices,
            &[old_a, old_b],
            &[new_a, new_b],
            &proof.siblings,
            16,
        )
        .unwrap();
        let updates: Vec<_> = steps
            .iter()
            .map(|step| {
                witness(
                    step.old_leaf,
                    step.new_leaf,
                    &step.siblings,
                    &step.directions,
                )
            })
            .collect();
        let columns = build_paired_merkle_update_columns(&updates, iv_flat(), 7);

        assert_eq!(columns.roots_before[0], digest_fields(steps[0].root_before));
        assert_eq!(columns.roots_after[0], columns.roots_before[1]);
        assert_eq!(columns.roots_after[1], digest_fields(steps[1].root_after));
        verify_native_dag(&columns).expect("two chained paired updates");
    }

    #[test]
    fn patterns_and_shape_are_content_invariant_and_honest_padding_is_valid() {
        let mut rng = Rng(0xA11C_E003);
        let make_update = |rng: &mut Rng| {
            let siblings: Vec<_> = (0..PAIRED_UPDATE_DEPTH).map(|_| rng.digest()).collect();
            let directions: Vec<_> = (0..PAIRED_UPDATE_DEPTH)
                .map(|_| rng.next_u64() & 1 == 1)
                .collect();
            witness(rng.digest(), rng.digest(), &siblings, &directions)
        };
        let first = build_paired_merkle_update_columns(&[make_update(&mut rng)], iv_flat(), 7);
        let second = build_paired_merkle_update_columns(
            &[make_update(&mut rng), make_update(&mut rng)],
            iv_flat(),
            7,
        );
        assert_eq!(first.c[0].len(), second.c[0].len());
        assert_eq!(first.committed_columns().len(), 9);
        assert_eq!(second.committed_columns().len(), 9);
        assert_eq!(
            paired_merkle_update_fixed_patterns(iv_flat()),
            paired_merkle_update_fixed_patterns(iv_flat())
        );
        assert_eq!(first.roots_before.len(), 2);
        assert_eq!(first.roots_before[1], first.roots_after[1]);
        verify_native_dag(&first).expect("canonical ghost is a valid paired update");
    }

    #[test]
    fn live_zero_sibling_is_not_padding() {
        let mut rng = Rng(0xA11C_E004);
        let mut siblings: Vec<_> = (0..PAIRED_UPDATE_DEPTH).map(|_| rng.digest()).collect();
        siblings[7] = [0u8; 32];
        let directions: Vec<_> = (0..PAIRED_UPDATE_DEPTH)
            .map(|_| rng.next_u64() & 1 == 1)
            .collect();
        let update = witness(rng.digest(), rng.digest(), &siblings, &directions);
        let columns = build_paired_merkle_update_columns(&[update], iv_flat(), 6);
        assert_eq!(columns.sib[0][4 * 7], F128::ZERO);
        assert_eq!(columns.sib[1][4 * 7], F128::ZERO);
        verify_native_dag(&columns).expect("zero digest is a live sibling value");
    }

    #[test]
    fn b255_structural_geometry_is_exact() {
        assert_eq!(
            paired_update_slots(1_531) + paired_update_slots(256),
            114_368
        );
    }
}
