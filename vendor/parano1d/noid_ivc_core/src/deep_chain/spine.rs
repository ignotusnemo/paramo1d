//! Flat-basis replay of the final 31-permutation Tx8x2 body spine.
//!
//! The sixteen body leaves are already canonical public field pairs.  They
//! enter the `KID` columns directly: there is no record-leaf sponge,
//! intermediate chain, or padding absorb.  The region contains exactly the permutations
//! used by the native body hash:
//!
//! - a 32-slot tree family: slots 2..31 are the fifteen two-permutation
//!   `COMPRESS` nodes, while slots 0 and 1 are ghost;
//! - a separate one-slot `TAG_TX8X2` wrap family.
//!
//! The tree uses the source-tree heap convention.  Internal node `h` occupies
//! slots `2h` and `2h+1`; raw leaf `i` is the external child at KID position
//! `16+i`.  Internal KID values are tied to `C(2w+1)` by the gated exposure,
//! while raw leaves are tied to statement wires by cell pins in the recursive
//! assembly.  The tree root at `C[3]` is pinned to the wrap input, and the
//! wrap output is pinned to the transaction hash.
//!
//! All columns use the flat basis.  The tower permutation is
//! `flat→tower ∘ permute_flat ∘ tower→flat`, and the basis conversion is
//! F2-linear, so only the statement boundary needs an explicit conversion.

use crate::deep_chain::relations::{ColRef, FixedPattern, RelationTerm};
use crate::deep_chain::schedule::flat_of_tower_u128;
use crate::deep_chain::source_tree::run_perm;
use crate::field::F128;
use noid_poseidon2b::native::domain::{DomainTag, TAG_COMPRESS, TAG_TX8X2, capacity_iv_flat};
use noid_poseidon2b::native::permutation::STATE_SIZE;

/// Number of raw, two-lane body leaves.
pub const SPINE_TREE_LEAVES: usize = noid_poseidon2b::primitives::TX8X2_LEAF_COUNT;
/// Two slots per possible internal heap node.  Slots 2..31 are active, so
/// this is the minimal power-of-two region containing all 30 COMPRESS
/// permutations.
pub const SPINE_TREE_SLOTS: usize = 2 * SPINE_TREE_LEAVES;
/// KID positions `[16, 32)` carry the sixteen raw body leaves.
pub const SPINE_TREE_KID_LEAF_BASE: usize = SPINE_TREE_LEAVES;
/// Original one-permutation V1 body wrap.
pub const SPINE_WRAP_SLOTS: usize = 1;
/// The construction-specific wrap and the fixed v2 feasibility tail share one
/// thirty-two-slot sponge family. Slot zero is the existing Tx8x2 wrap. Slots
/// one through twenty-eight authenticate a sixteen-instruction program, its timed
/// authority policy, and the old and successor object records. The remaining
/// slots stay canonical padding. Together with the 32-slot body tree this
/// still occupies the existing 64-slot Meta-A allocation per transaction.
pub const SPINE_V2_WRAP_SLOTS: usize = 32;
pub const SPINE_WRAP_SLOT: usize = 0;
pub const SPINE_CONTRACT_PROGRAM_STEPS: usize = 16;
pub const SPINE_CONTRACT_CODE_BASE: usize = 1;
pub const SPINE_CONTRACT_POLICY_BASE: usize =
    SPINE_CONTRACT_CODE_BASE + SPINE_CONTRACT_PROGRAM_STEPS;
pub const SPINE_CONTRACT_OLD_OBJECT_BASE: usize = SPINE_CONTRACT_POLICY_BASE + 8;
pub const SPINE_CONTRACT_NEW_OBJECT_BASE: usize = SPINE_CONTRACT_OLD_OBJECT_BASE + 2;
pub const SPINE_CONTRACT_END: usize = SPINE_CONTRACT_NEW_OBJECT_BASE + 2;
const _: () = assert!(SPINE_CONTRACT_END <= SPINE_V2_WRAP_SLOTS);

pub const SPINE_CONTRACT_CODE_DOMAIN: DomainTag = DomainTag::new(b"CNTCODE_");
pub const SPINE_CONTRACT_POLICY_DOMAIN: DomainTag = DomainTag::new(b"CNTPOL__");
pub const SPINE_CONTRACT_OBJECT_DOMAIN: DomainTag = DomainTag::new(b"CNTOBJ__");

/// Canonical object-format version expressed in the flat circuit basis.
pub fn spine_contract_object_version_flat() -> F128 {
    flat_of_tower_u128(3)
}

fn iv_flat(tag: noid_poseidon2b::native::domain::DomainTag) -> [F128; 2] {
    let iv = capacity_iv_flat(tag);
    [
        F128 {
            lo: iv[0] as u64,
            hi: (iv[0] >> 64) as u64,
        },
        F128 {
            lo: iv[1] as u64,
            hi: (iv[1] >> 64) as u64,
        },
    ]
}

pub fn tx8x2_iv_flat() -> [F128; 2] {
    iv_flat(TAG_TX8X2)
}

pub fn spine_compress_iv_flat() -> [F128; 2] {
    iv_flat(TAG_COMPRESS)
}

/// One transaction's canonical raw body leaves in the flat basis.  The order
/// is exactly `noid_tx::body_hash::body_hash_leaves`:
///
/// - L0 epoch anchor; L1 fee; L2 input owner;
/// - L3..L10 fixed inputs;
/// - L11/L12 output 0 record/owner; L13/L14 output 1 record/owner;
/// - L15 validity bitmap and coinbase flag.
#[derive(Clone, Debug)]
pub struct SpineInstanceFlat {
    pub leaves: [[F128; 2]; SPINE_TREE_LEAVES],
}

/// Research-only contract boundary carried beside one ordinary body spine.
/// These values are not a new transaction body. The enclosing HistoryStep
/// binds them to the existing body fields and authorization transcript.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpineContractInstanceFlat {
    pub program: [[F128; 2]; SPINE_CONTRACT_PROGRAM_STEPS],
    pub current: F128,
    pub next: F128,
    /// Claim authority. At or after `deadline`, authorization switches to
    /// `refund_authority`.
    pub controller: [F128; 2],
    pub refund_authority: [F128; 2],
    pub deadline: F128,
    pub claim_recipient: [F128; 2],
    pub refund_recipient: [F128; 2],
    /// Fee cap, retained-value floor, payout cap and mode bits.
    pub rules: [F128; 4],
}

impl SpineContractInstanceFlat {
    pub const fn ghost() -> Self {
        Self {
            program: [[F128::ZERO; 2]; SPINE_CONTRACT_PROGRAM_STEPS],
            current: F128::ZERO,
            next: F128::ZERO,
            controller: [F128::ZERO; 2],
            refund_authority: [F128::ZERO; 2],
            deadline: F128::ZERO,
            claim_recipient: [F128::ZERO; 2],
            refund_recipient: [F128::ZERO; 2],
            rules: [F128::ZERO; 4],
        }
    }
}

impl SpineInstanceFlat {
    /// Canonical ghost instance used only to fill class capacity.  No
    /// downstream statement reads its digest.
    pub fn ghost() -> Self {
        Self {
            leaves: [[F128::ZERO; 2]; SPINE_TREE_LEAVES],
        }
    }
}

/// Filled columns for one final body-spine instance.
pub struct SpineInstanceColumns {
    // Tree (`SPINE_TREE_SLOTS` slots).
    pub tree_c: [Vec<F128>; STATE_SIZE],
    pub tree_s0: [Vec<F128>; STATE_SIZE],
    pub tree_s_out: [Vec<F128>; STATE_SIZE],
    /// Internal child digests at positions 2..15 and raw leaves at 16..31.
    pub tree_kid: [Vec<F128>; 2],
    // One-slot TAG_TX8X2 wrap.
    pub wrap_c: [Vec<F128>; STATE_SIZE],
    pub wrap_s0: [Vec<F128>; STATE_SIZE],
    pub wrap_s_out: [Vec<F128>; STATE_SIZE],
    pub wrap_in: [Vec<F128>; 2],
    /// Recomputed tree root (`C0/C1` at tree slot 3).
    pub root: [F128; 2],
    /// Wrap digest, equal to the canonical Tx8x2 body hash under φ.
    pub tx_hash: [F128; 2],
    pub contract_code_digest: [F128; 2],
    pub contract_policy_digest: [F128; 2],
    pub contract_old_object_root: [F128; 2],
    pub contract_new_object_root: [F128; 2],
}

/// Replay the fifteen COMPRESS nodes and the final TAG_TX8X2 wrap.
pub fn build_spine_instance_columns(inst: &SpineInstanceFlat) -> SpineInstanceColumns {
    build_spine_instance_columns_profile(inst, None, SPINE_WRAP_SLOTS)
}

/// Replay the body spine and the fixed contract-commitment tail. A missing
/// contract uses the canonical all-zero opening, but occupies the same walk
/// slots and therefore the same matrix.
pub fn build_spine_instance_columns_with_contract(
    inst: &SpineInstanceFlat,
    contract: Option<&SpineContractInstanceFlat>,
) -> SpineInstanceColumns {
    build_spine_instance_columns_profile(inst, contract, SPINE_V2_WRAP_SLOTS)
}

fn build_spine_instance_columns_profile(
    inst: &SpineInstanceFlat,
    contract: Option<&SpineContractInstanceFlat>,
    wrap_slots: usize,
) -> SpineInstanceColumns {
    let iv_comp = spine_compress_iv_flat();
    let iv_wrap = tx8x2_iv_flat();
    let (ghost_s0, ghost_out) = run_perm([F128::ZERO; STATE_SIZE]);

    let mut tree_c: [Vec<F128>; STATE_SIZE] =
        std::array::from_fn(|_| vec![F128::ZERO; SPINE_TREE_SLOTS]);
    let mut tree_s0: [Vec<F128>; STATE_SIZE] =
        std::array::from_fn(|_| vec![F128::ZERO; SPINE_TREE_SLOTS]);
    let mut tree_s_out: [Vec<F128>; STATE_SIZE] =
        std::array::from_fn(|_| vec![F128::ZERO; SPINE_TREE_SLOTS]);
    let mut store_tree = |slot: usize,
                          s0v: [F128; STATE_SIZE],
                          outv: [F128; STATE_SIZE],
                          c: &mut [Vec<F128>; STATE_SIZE]| {
        for lane in 0..STATE_SIZE {
            tree_s0[lane][slot] = s0v[lane];
            tree_s_out[lane][slot] = outv[lane];
            c[lane][slot] = outv[lane];
        }
    };
    for slot in 0..SPINE_TREE_SLOTS {
        store_tree(slot, ghost_s0, ghost_out, &mut tree_c);
    }

    // Heap digests: raw leaves occupy nodes 16..31.  Descending internal
    // indices ensure both children are available before their parent.
    let mut node_digest = [[F128::ZERO; 2]; 2 * SPINE_TREE_LEAVES];
    node_digest[SPINE_TREE_LEAVES..].copy_from_slice(&inst.leaves);
    for h in (1..SPINE_TREE_LEAVES).rev() {
        let left = node_digest[2 * h];
        let right = node_digest[2 * h + 1];
        let (even_s0, even_out) = run_perm([left[0], left[1], iv_comp[0], iv_comp[1]]);
        store_tree(2 * h, even_s0, even_out, &mut tree_c);
        let (odd_s0, odd_out) = run_perm([
            even_out[0] + right[0],
            even_out[1] + right[1],
            even_out[2],
            even_out[3],
        ]);
        store_tree(2 * h + 1, odd_s0, odd_out, &mut tree_c);
        node_digest[h] = [odd_out[0], odd_out[1]];
    }

    // At active tree slot w, KID[w] is exactly the child digest absorbed by
    // that permutation.  Positions 16..31 are the raw statement leaves.
    let mut tree_kid: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; SPINE_TREE_SLOTS]);
    for w in 2..2 * SPINE_TREE_LEAVES {
        tree_kid[0][w] = node_digest[w][0];
        tree_kid[1][w] = node_digest[w][1];
    }
    let root = node_digest[1];

    let (_, wrap_out) = run_perm([root[0], root[1], iv_wrap[0], iv_wrap[1]]);
    let mut wrap_c: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; wrap_slots]);
    let mut wrap_s0: [Vec<F128>; STATE_SIZE] =
        std::array::from_fn(|_| vec![F128::ZERO; wrap_slots]);
    let mut wrap_s_out: [Vec<F128>; STATE_SIZE] =
        std::array::from_fn(|_| vec![F128::ZERO; wrap_slots]);
    for slot in 0..wrap_slots {
        for lane in 0..STATE_SIZE {
            wrap_c[lane][slot] = ghost_out[lane];
            wrap_s0[lane][slot] = ghost_s0[lane];
            wrap_s_out[lane][slot] = ghost_out[lane];
        }
    }
    let mut wrap_in: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; wrap_slots]);
    let mut store_wrap =
        |slot: usize, absorbed: [F128; 2], previous: Option<[F128; 4]>, iv: [F128; 2]| {
            let raw = previous.map_or([absorbed[0], absorbed[1], iv[0], iv[1]], |prior| {
                [
                    prior[0] + absorbed[0],
                    prior[1] + absorbed[1],
                    prior[2],
                    prior[3],
                ]
            });
            let (state_in, state_out) = run_perm(raw);
            wrap_in[0][slot] = absorbed[0];
            wrap_in[1][slot] = absorbed[1];
            for lane in 0..STATE_SIZE {
                wrap_c[lane][slot] = state_out[lane];
                wrap_s0[lane][slot] = state_in[lane];
                wrap_s_out[lane][slot] = state_out[lane];
            }
            state_out
        };
    let body_wrap = store_wrap(SPINE_WRAP_SLOT, root, None, iv_wrap);
    debug_assert_eq!(body_wrap, wrap_out);

    if wrap_slots == SPINE_WRAP_SLOTS {
        return SpineInstanceColumns {
            tree_c,
            tree_s0,
            tree_s_out,
            tree_kid,
            wrap_c,
            wrap_s0,
            wrap_s_out,
            wrap_in,
            root,
            tx_hash: [wrap_out[0], wrap_out[1]],
            contract_code_digest: [F128::ZERO; 2],
            contract_policy_digest: [F128::ZERO; 2],
            contract_old_object_root: [F128::ZERO; 2],
            contract_new_object_root: [F128::ZERO; 2],
        };
    }

    let contract = contract
        .copied()
        .unwrap_or_else(SpineContractInstanceFlat::ghost);
    let code_iv = iv_flat(SPINE_CONTRACT_CODE_DOMAIN);
    let policy_iv = iv_flat(SPINE_CONTRACT_POLICY_DOMAIN);
    let object_iv = iv_flat(SPINE_CONTRACT_OBJECT_DOMAIN);
    let mut previous = None;
    for (step, fields) in contract.program.into_iter().enumerate() {
        previous = Some(store_wrap(
            SPINE_CONTRACT_CODE_BASE + step,
            fields,
            previous,
            code_iv,
        ));
    }
    let code_state = previous.expect("fixed contract program is nonempty");
    let contract_code_digest = [code_state[0], code_state[1]];

    let policy0 = store_wrap(
        SPINE_CONTRACT_POLICY_BASE,
        contract_code_digest,
        None,
        policy_iv,
    );
    let policy1 = store_wrap(
        SPINE_CONTRACT_POLICY_BASE + 1,
        [contract.deadline, contract.controller[0]],
        Some(policy0),
        policy_iv,
    );
    let policy2 = store_wrap(
        SPINE_CONTRACT_POLICY_BASE + 2,
        [contract.controller[1], contract.refund_authority[0]],
        Some(policy1),
        policy_iv,
    );
    let policy3 = store_wrap(
        SPINE_CONTRACT_POLICY_BASE + 3,
        [contract.refund_authority[1], contract.claim_recipient[0]],
        Some(policy2),
        policy_iv,
    );
    let policy4 = store_wrap(
        SPINE_CONTRACT_POLICY_BASE + 4,
        [contract.claim_recipient[1], contract.refund_recipient[0]],
        Some(policy3),
        policy_iv,
    );
    let policy5 = store_wrap(
        SPINE_CONTRACT_POLICY_BASE + 5,
        [
            contract.refund_recipient[1],
            spine_contract_object_version_flat(),
        ],
        Some(policy4),
        policy_iv,
    );
    let policy6 = store_wrap(
        SPINE_CONTRACT_POLICY_BASE + 6,
        [contract.rules[0], contract.rules[1]],
        Some(policy5),
        policy_iv,
    );
    let policy7 = store_wrap(
        SPINE_CONTRACT_POLICY_BASE + 7,
        [contract.rules[2], contract.rules[3]],
        Some(policy6),
        policy_iv,
    );
    let contract_policy_digest = [policy7[0], policy7[1]];

    let old0 = store_wrap(
        SPINE_CONTRACT_OLD_OBJECT_BASE,
        contract_policy_digest,
        None,
        object_iv,
    );
    let old1 = store_wrap(
        SPINE_CONTRACT_OLD_OBJECT_BASE + 1,
        [contract.current, F128::ZERO],
        Some(old0),
        object_iv,
    );
    let contract_old_object_root = [old1[0], old1[1]];

    let new0 = store_wrap(
        SPINE_CONTRACT_NEW_OBJECT_BASE,
        contract_policy_digest,
        None,
        object_iv,
    );
    let new1 = store_wrap(
        SPINE_CONTRACT_NEW_OBJECT_BASE + 1,
        [contract.next, F128::ZERO],
        Some(new0),
        object_iv,
    );
    let contract_new_object_root = [new1[0], new1[1]];

    wrap_in[0][SPINE_WRAP_SLOT] = root[0];
    wrap_in[1][SPINE_WRAP_SLOT] = root[1];
    let tx_hash = [wrap_out[0], wrap_out[1]];

    SpineInstanceColumns {
        tree_c,
        tree_s0,
        tree_s_out,
        tree_kid,
        wrap_c,
        wrap_s0,
        wrap_s_out,
        wrap_in,
        root,
        tx_hash,
        contract_code_digest,
        contract_policy_digest,
        contract_old_object_root,
        contract_new_object_root,
    }
}

// ---------------------------------------------------------------------------
// Region wiring: fixed patterns and gated internal-child exposure
// ---------------------------------------------------------------------------

/// Tree patterns in source-tree order `[EVEN_INT, ODD_INT, LEAFODD, IV0,
/// IV1]`.  `LEAFODD` is identically zero because all sixteen leaves are raw
/// boundary values, not permutations.
pub fn spine_tree_fixed_patterns() -> Vec<FixedPattern> {
    let low_log = SPINE_TREE_SLOTS.trailing_zeros() as usize;
    let iv = spine_compress_iv_flat();
    let mut even = vec![F128::ZERO; SPINE_TREE_SLOTS];
    let mut odd = vec![F128::ZERO; SPINE_TREE_SLOTS];
    let leafodd = vec![F128::ZERO; SPINE_TREE_SLOTS];
    let mut iv0 = vec![F128::ZERO; SPINE_TREE_SLOTS];
    let mut iv1 = vec![F128::ZERO; SPINE_TREE_SLOTS];
    for h in 1..SPINE_TREE_LEAVES {
        even[2 * h] = F128::ONE;
        odd[2 * h + 1] = F128::ONE;
        iv0[2 * h] = iv[0];
        iv1[2 * h] = iv[1];
    }
    vec![
        FixedPattern::new(low_log, even),
        FixedPattern::new(low_log, odd),
        FixedPattern::new(low_log, leafodd),
        FixedPattern::new(low_log, iv0),
        FixedPattern::new(low_log, iv1),
    ]
}

/// Fixed wrap/contract patterns in sponge-family order `[REGION, CHAIN, IV0,
/// IV1]`. Slot zero is the Tx8x2 wrap. The four contract chains start at
/// slots 1, 9, 15 and 17.
pub fn spine_wrap_fixed_patterns() -> Vec<FixedPattern> {
    let iv = tx8x2_iv_flat();
    vec![
        FixedPattern::new(0, vec![F128::ONE]),
        FixedPattern::new(0, vec![F128::ZERO]),
        FixedPattern::new(0, vec![iv[0]]),
        FixedPattern::new(0, vec![iv[1]]),
    ]
}

/// V2 uses its own descriptor and authenticated fixed tables; the V1 recipe
/// above remains byte-for-byte stable for existing recursive proofs.
pub fn spine_contract_wrap_fixed_patterns() -> Vec<FixedPattern> {
    let low_log = SPINE_V2_WRAP_SLOTS.trailing_zeros() as usize;
    let tx_iv = tx8x2_iv_flat();
    let code_iv = iv_flat(SPINE_CONTRACT_CODE_DOMAIN);
    let policy_iv = iv_flat(SPINE_CONTRACT_POLICY_DOMAIN);
    let object_iv = iv_flat(SPINE_CONTRACT_OBJECT_DOMAIN);
    let mut region = vec![F128::ZERO; SPINE_V2_WRAP_SLOTS];
    let mut chain = vec![F128::ZERO; SPINE_V2_WRAP_SLOTS];
    let mut iv0 = vec![F128::ZERO; SPINE_V2_WRAP_SLOTS];
    let mut iv1 = vec![F128::ZERO; SPINE_V2_WRAP_SLOTS];
    region[..SPINE_CONTRACT_END].fill(F128::ONE);
    chain[SPINE_CONTRACT_CODE_BASE + 1..SPINE_CONTRACT_POLICY_BASE].fill(F128::ONE);
    chain[SPINE_CONTRACT_POLICY_BASE + 1..SPINE_CONTRACT_OLD_OBJECT_BASE].fill(F128::ONE);
    chain[SPINE_CONTRACT_OLD_OBJECT_BASE + 1..SPINE_CONTRACT_NEW_OBJECT_BASE].fill(F128::ONE);
    chain[SPINE_CONTRACT_NEW_OBJECT_BASE + 1..SPINE_CONTRACT_END].fill(F128::ONE);
    for (slot, iv) in [
        (SPINE_WRAP_SLOT, tx_iv),
        (SPINE_CONTRACT_CODE_BASE, code_iv),
        (SPINE_CONTRACT_POLICY_BASE, policy_iv),
        (SPINE_CONTRACT_OLD_OBJECT_BASE, object_iv),
        (SPINE_CONTRACT_NEW_OBJECT_BASE, object_iv),
    ] {
        iv0[slot] = iv[0];
        iv1[slot] = iv[1];
    }
    vec![
        FixedPattern::new(low_log, region),
        FixedPattern::new(low_log, chain),
        FixedPattern::new(low_log, iv0),
        FixedPattern::new(low_log, iv1),
    ]
}

/// Gate for the half-domain exposure.  Positions 2..15 are digests of
/// internal children and must equal `C(2w+1)`; positions 0 and 1 are unused.
/// Raw-leaf positions 16..31 live outside this half-domain and are cell-pinned
/// directly to statement wires.
pub fn spine_tree_internal_child_pattern() -> FixedPattern {
    let period = SPINE_TREE_SLOTS / 2;
    let low_log = period.trailing_zeros() as usize;
    let mut gate = vec![F128::ZERO; period];
    for w in 2..SPINE_TREE_LEAVES {
        gate[w] = F128::ONE;
    }
    FixedPattern::new(low_log, gate)
}

/// Gated exposure
/// `KID_i(w) + C_i(2w+1) = 0` for internal child positions.
pub fn spine_tree_exposure_terms(
    kid_lo: [usize; 2],
    c: [usize; 2],
    gate: usize,
    gamma: F128,
) -> Vec<RelationTerm> {
    let mut terms = Vec::new();
    let mut power = F128::ONE;
    for lane in 0..2 {
        power = power * gamma;
        terms.push(RelationTerm {
            coeff: power,
            factors: vec![ColRef::Fixed(gate), ColRef::Committed(kid_lo[lane])],
        });
        terms.push(RelationTerm {
            coeff: power,
            factors: vec![
                ColRef::Fixed(gate),
                ColRef::Window {
                    col: c[lane],
                    stride_log: 1,
                    offset: 1,
                },
            ],
        });
    }
    terms
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::deep_chain::leaf_hash::{SpongeLeafRefs, sponge_leaf_substitution_terms};
    use crate::deep_chain::relations::{
        RelationColumns, claimed_refs, prove_column_relation, prove_shift_discharge,
        verify_column_relation, verify_shift_discharge, window_discharge_point,
    };
    use crate::deep_chain::schedule::carry_selection_terms;
    use crate::deep_chain::source_tree::{SourceTreeRefs, source_tree_substitution_terms};
    use crate::deep_chain::{LaneClaimGroup, prove_deep_chain_walk, verify_deep_chain_walk};
    use crate::lincheck::build_eq_table;
    use noid_core::{Block128, TowerField};
    use noid_poseidon2b::native::domain::capacity_iv;
    use noid_poseidon2b::native::permutation::Poseidon2bPermutation;

    struct Rng(u64);
    impl Rng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            z ^ (z >> 31)
        }

        fn block(&mut self) -> Block128 {
            Block128::from(((self.next_u64() as u128) << 64) | self.next_u64() as u128)
        }
    }

    fn phi(value: Block128) -> F128 {
        let flat = noid_core::hardware::tower_to_flat_u128(value.0);
        F128 {
            lo: flat as u64,
            hi: (flat >> 64) as u64,
        }
    }

    fn mle(col: &[F128], point: &[F128]) -> F128 {
        let eq = build_eq_table(point);
        col.iter()
            .zip(eq.iter())
            .fold(F128::ZERO, |acc, (value, weight)| acc + *value * *weight)
    }

    fn perm(mut state: [Block128; STATE_SIZE]) -> [Block128; STATE_SIZE] {
        Poseidon2bPermutation.permute_mut(&mut state);
        state
    }

    fn tower_reference(
        leaves: &[[Block128; 2]; SPINE_TREE_LEAVES],
    ) -> ([Block128; 2], [Block128; 2]) {
        let [compress_hi, compress_lo] = capacity_iv(TAG_COMPRESS);
        let [wrap_hi, wrap_lo] = capacity_iv(TAG_TX8X2);
        let mut nodes = [[Block128::ZERO; 2]; 2 * SPINE_TREE_LEAVES];
        nodes[SPINE_TREE_LEAVES..].copy_from_slice(leaves);
        for h in (1..SPINE_TREE_LEAVES).rev() {
            let left = nodes[2 * h];
            let right = nodes[2 * h + 1];
            let even = perm([left[0], left[1], compress_hi, compress_lo]);
            let odd = perm([even[0] + right[0], even[1] + right[1], even[2], even[3]]);
            nodes[h] = [odd[0], odd[1]];
        }
        let root = nodes[1];
        let wrapped = perm([root[0], root[1], wrap_hi, wrap_lo]);
        (root, [wrapped[0], wrapped[1]])
    }

    fn random_instance(rng: &mut Rng) -> ([[Block128; 2]; SPINE_TREE_LEAVES], SpineInstanceFlat) {
        let leaves = std::array::from_fn(|_| [rng.block(), rng.block()]);
        let flat = SpineInstanceFlat {
            leaves: std::array::from_fn(|leaf| [phi(leaves[leaf][0]), phi(leaves[leaf][1])]),
        };
        (leaves, flat)
    }

    #[test]
    fn final_spine_matches_independent_tower_reference() {
        let mut rng = Rng(0x59147E);
        for _ in 0..4 {
            let (leaves, flat) = random_instance(&mut rng);
            let (root, tx_hash) = tower_reference(&leaves);
            let native = noid_poseidon2b::primitives::hash_tx8x2_leaves(&leaves);
            let native_hash = [
                Block128::from(u128::from_le_bytes(native.0[..16].try_into().unwrap())),
                Block128::from(u128::from_le_bytes(native.0[16..].try_into().unwrap())),
            ];
            assert_eq!(
                native_hash, tx_hash,
                "native helper vs independent reference"
            );
            let cols = build_spine_instance_columns(&flat);
            assert_eq!(cols.root, [phi(root[0]), phi(root[1])]);
            assert_eq!(cols.tx_hash, [phi(tx_hash[0]), phi(tx_hash[1])]);
            for leaf in 0..SPINE_TREE_LEAVES {
                assert_eq!(
                    [
                        cols.tree_kid[0][SPINE_TREE_KID_LEAF_BASE + leaf],
                        cols.tree_kid[1][SPINE_TREE_KID_LEAF_BASE + leaf],
                    ],
                    flat.leaves[leaf],
                    "raw leaf {leaf}"
                );
            }
        }
    }

    #[test]
    fn final_spine_geometry_is_thirty_compress_plus_fixed_wrap_tail() {
        let patterns = spine_tree_fixed_patterns();
        let active_tree = patterns[0]
            .table
            .iter()
            .chain(patterns[1].table.iter())
            .filter(|&&v| v == F128::ONE)
            .count();
        assert_eq!(SPINE_TREE_SLOTS, 32);
        assert_eq!(active_tree, 30);
        assert_eq!(SPINE_WRAP_SLOTS, 1);
        assert_eq!(SPINE_V2_WRAP_SLOTS, 32);
        let wrap = spine_contract_wrap_fixed_patterns();
        assert_eq!(
            wrap[0]
                .table
                .iter()
                .filter(|&&value| value == F128::ONE)
                .count(),
            SPINE_CONTRACT_END
        );
        assert_eq!(wrap[0].table[SPINE_CONTRACT_END], F128::ZERO);
        assert!(patterns[2].table.iter().all(|&v| v == F128::ZERO));
    }

    /// Full native region DAG plus the assembly's cell-pin equalities.
    /// Corruptions cover internal exposure, a raw leaf, the wrap input and
    /// the wrap output.
    #[test]
    fn final_spine_region_dag_roundtrip_and_negatives() {
        use crate::challenger::{Challenger, FsLaneChallenger};

        // [tree 32 | fixed wrap/contract tail 32] = 64 slots.
        let tree_base = 0usize;
        let wrap_base = SPINE_TREE_SLOTS;
        let w_log = 6usize;
        let p = 1usize << w_log;

        let mut rng = Rng(0xDA6);
        let (_, flat) = random_instance(&mut rng);
        let built = build_spine_instance_columns(&flat);

        let zero_col = vec![F128::ZERO; p];
        let mut kid: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; p]);
        let mut in_: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; p]);
        let mut c: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; p]);
        let mut s0: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; p]);
        let mut s_out: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; p]);
        let (ghost_s0, ghost_out) = run_perm([F128::ZERO; STATE_SIZE]);
        for slot in 0..p {
            for lane in 0..STATE_SIZE {
                s0[lane][slot] = ghost_s0[lane];
                s_out[lane][slot] = ghost_out[lane];
                c[lane][slot] = ghost_out[lane];
            }
        }
        for lane in 0..STATE_SIZE {
            c[lane][tree_base..tree_base + SPINE_TREE_SLOTS].copy_from_slice(&built.tree_c[lane]);
            s0[lane][tree_base..tree_base + SPINE_TREE_SLOTS].copy_from_slice(&built.tree_s0[lane]);
            s_out[lane][tree_base..tree_base + SPINE_TREE_SLOTS]
                .copy_from_slice(&built.tree_s_out[lane]);
            c[lane][wrap_base..wrap_base + SPINE_WRAP_SLOTS].copy_from_slice(&built.wrap_c[lane]);
            s0[lane][wrap_base..wrap_base + SPINE_WRAP_SLOTS].copy_from_slice(&built.wrap_s0[lane]);
            s_out[lane][wrap_base..wrap_base + SPINE_WRAP_SLOTS]
                .copy_from_slice(&built.wrap_s_out[lane]);
        }
        for lane in 0..2 {
            kid[lane][tree_base..tree_base + SPINE_TREE_SLOTS]
                .copy_from_slice(&built.tree_kid[lane]);
            in_[lane][wrap_base..wrap_base + SPINE_WRAP_SLOTS]
                .copy_from_slice(&built.wrap_in[lane]);
        }

        let localize = |table: &[F128], offset: usize| -> FixedPattern {
            let mut values = vec![F128::ZERO; p];
            values[offset..offset + table.len()].copy_from_slice(table);
            FixedPattern::new(w_log, values)
        };
        let mut fixed = Vec::new();
        for pattern in spine_tree_fixed_patterns() {
            fixed.push(localize(&pattern.table, tree_base));
        }
        for pattern in spine_wrap_fixed_patterns() {
            fixed.push(localize(&pattern.table, wrap_base));
        }
        // Structural sanity: the union's substitution tables reconstruct the
        // exact pre-MDS state used to build every walk slot.
        for slot in 0..p {
            let prev = if slot == 0 { p - 1 } else { slot - 1 };
            let mut raw = [F128::ZERO; STATE_SIZE];
            for lane in 0..2 {
                raw[lane] = (fixed[0].table[slot] + fixed[1].table[slot]) * kid[lane][slot]
                    + fixed[1].table[slot] * c[lane][prev]
                    + fixed[5].table[slot] * in_[lane][slot]
                    + fixed[6].table[slot] * c[lane][prev];
            }
            for lane in 2..STATE_SIZE {
                raw[lane] = fixed[3 + lane - 2].table[slot]
                    + fixed[1].table[slot] * c[lane][prev]
                    + fixed[7 + lane - 2].table[slot]
                    + fixed[6].table[slot] * c[lane][prev];
            }
            assert_eq!(
                crate::deep_chain::initial_mds(raw),
                std::array::from_fn(|lane| s0[lane][slot]),
                "substitution raw mismatch at slot {slot}"
            );
        }
        let tree_refs = SourceTreeRefs {
            code: [0, 1],
            kid: [2, 3],
            c: std::array::from_fn(|lane| 6 + lane),
            even_int: 0,
            odd_int: 1,
            leafodd: 2,
            iv: [3, 4],
        };
        let wrap_refs = SpongeLeafRefs {
            in_: [4, 5],
            c: std::array::from_fn(|lane| 6 + lane),
            odd: 6,
            iv: [7, 8],
        };
        let wrap_region = 5;

        let run = |kid0: &[F128],
                   kid1: &[F128],
                   in0: &[F128],
                   in1: &[F128],
                   c: &[Vec<F128>; STATE_SIZE]|
         -> Result<(), String> {
            let committed: Vec<&[F128]> = vec![
                &zero_col, &zero_col, kid0, kid1, in0, in1, &c[0], &c[1], &c[2], &c[3],
            ];
            // Deterministic assembly/exposure checks run before creating a
            // sumcheck proof.  This keeps negative fixtures from tripping the
            // prover's honest-witness debug assertion.
            for w in 2..SPINE_TREE_LEAVES {
                for lane in 0..2 {
                    let kid_col = if lane == 0 { kid0 } else { kid1 };
                    if kid_col[tree_base + w] != c[lane][tree_base + 2 * w + 1] {
                        return Err(format!("internal KID {w} lane {lane} not exposed"));
                    }
                }
            }
            for leaf in 0..SPINE_TREE_LEAVES {
                for lane in 0..2 {
                    let kid_col = if lane == 0 { kid0 } else { kid1 };
                    if kid_col[tree_base + SPINE_TREE_KID_LEAF_BASE + leaf]
                        != flat.leaves[leaf][lane]
                    {
                        return Err(format!("raw leaf {leaf} lane {lane} not pinned"));
                    }
                }
            }
            for lane in 0..2 {
                let in_col = if lane == 0 { in0 } else { in1 };
                if in_col[wrap_base + SPINE_WRAP_SLOT] != c[lane][tree_base + 3] {
                    return Err(format!("wrap input lane {lane} != tree root"));
                }
                if c[lane][wrap_base + SPINE_WRAP_SLOT] != built.tx_hash[lane] {
                    return Err(format!("wrap output lane {lane} != tx hash"));
                }
            }
            let internal: Vec<&[F128]> = s_out.iter().map(Vec::as_slice).collect();
            let mut prover = FsLaneChallenger::new(b"final-spine-dag");
            let mut verifier = FsLaneChallenger::new(b"final-spine-dag");
            let mut pending = Vec::new();

            let beta = prover.sample_f128();
            assert_eq!(beta, verifier.sample_f128());
            let selection_terms = carry_selection_terms(&tree_refs.c, beta);
            let rho = prover.sample_f128_vec(w_log);
            let _ = verifier.sample_f128_vec(w_log);
            let (selection, _, _) = prove_column_relation(
                F128::ZERO,
                &rho,
                &selection_terms,
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
                &rho,
                &selection_terms,
                &fixed,
                &selection,
                &mut verifier,
            )
            .map_err(|err| format!("selection: {err}"))?;
            let mut group_values = [F128::ZERO; STATE_SIZE];
            for (reference, value) in claimed_refs(&selection_terms)
                .iter()
                .zip(selection.final_values.iter())
            {
                match reference {
                    ColRef::Committed(col) => {
                        pending.push((*col, selection_point.clone(), *value));
                    }
                    ColRef::Internal(lane) => group_values[*lane] = *value,
                    _ => unreachable!(),
                }
            }
            let groups = vec![LaneClaimGroup {
                point: selection_point,
                values: group_values,
            }];
            let (walk, _) = prove_deep_chain_walk(&s0, &groups, &mut prover);
            let terminal = verify_deep_chain_walk(w_log, &groups, &walk, &mut verifier)
                .map_err(|err| format!("walk: {err}"))?;

            let alpha = prover.sample_f128();
            assert_eq!(alpha, verifier.sample_f128());
            let mut substitution = source_tree_substitution_terms(&tree_refs, alpha);
            let mut wrap_terms = sponge_leaf_substitution_terms(&wrap_refs, alpha);
            for term in &mut wrap_terms {
                if !term
                    .factors
                    .iter()
                    .any(|factor| matches!(factor, ColRef::Fixed(_)))
                {
                    term.factors.insert(0, ColRef::Fixed(wrap_region));
                }
            }
            substitution.extend(wrap_terms);
            let mut target = F128::ZERO;
            let mut power = F128::ONE;
            for value in terminal.values {
                power = power * alpha;
                target += power * value;
            }
            for lane in 0..STATE_SIZE {
                assert_eq!(
                    mle(&s0[lane], &terminal.point),
                    terminal.values[lane],
                    "walk terminal lane {lane}"
                );
            }
            let (substitution_proof, _, _) = prove_column_relation(
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
            let substitution_point = verify_column_relation(
                w_log,
                target,
                &terminal.point,
                &substitution,
                &fixed,
                &substitution_proof,
                &mut verifier,
            )
            .map_err(|err| format!("substitution: {err}"))?;
            for (reference, value) in claimed_refs(&substitution)
                .iter()
                .zip(substitution_proof.final_values.iter())
            {
                match reference {
                    ColRef::Committed(col) => {
                        pending.push((*col, substitution_point.clone(), *value));
                    }
                    ColRef::CommittedShift(col) => {
                        let (proof, _) = prove_shift_discharge(
                            committed[*col],
                            &substitution_point,
                            *value,
                            &mut prover,
                        );
                        let point = verify_shift_discharge(
                            w_log,
                            &substitution_point,
                            *value,
                            &proof,
                            &mut verifier,
                        )
                        .map_err(|err| format!("shift: {err}"))?;
                        pending.push((*col, point, proof.final_value));
                    }
                    _ => unreachable!("spine union has plain and shift refs only"),
                }
            }

            // Exposure uses precisely KID[0..16] and C[0..32].
            let kid_half = SPINE_TREE_SLOTS / 2;
            let kid_lo0 = &kid0[tree_base..tree_base + kid_half];
            let kid_lo1 = &kid1[tree_base..tree_base + kid_half];
            let tree_c0 = &c[0][tree_base..tree_base + SPINE_TREE_SLOTS];
            let tree_c1 = &c[1][tree_base..tree_base + SPINE_TREE_SLOTS];
            let exposure_cols: Vec<&[F128]> = vec![kid_lo0, kid_lo1, tree_c0, tree_c1];
            let gamma = prover.sample_f128();
            assert_eq!(gamma, verifier.sample_f128());
            let exposure_terms = spine_tree_exposure_terms([0, 1], [2, 3], 0, gamma);
            let exposure_log = kid_half.trailing_zeros() as usize;
            let rho_exposure = prover.sample_f128_vec(exposure_log);
            let _ = verifier.sample_f128_vec(exposure_log);
            let exposure_fixed = vec![spine_tree_internal_child_pattern()];
            let (exposure, _, _) = prove_column_relation(
                F128::ZERO,
                &rho_exposure,
                &exposure_terms,
                &RelationColumns {
                    committed: &exposure_cols,
                    internal: &[],
                    fixed: &exposure_fixed,
                },
                &mut prover,
            );
            let exposure_point = verify_column_relation(
                exposure_log,
                F128::ZERO,
                &rho_exposure,
                &exposure_terms,
                &exposure_fixed,
                &exposure,
                &mut verifier,
            )
            .map_err(|err| format!("exposure: {err}"))?;
            for (reference, value) in claimed_refs(&exposure_terms)
                .iter()
                .zip(exposure.final_values.iter())
            {
                match reference {
                    ColRef::Committed(0) if mle(kid_lo0, &exposure_point) == *value => {}
                    ColRef::Committed(1) if mle(kid_lo1, &exposure_point) == *value => {}
                    ColRef::Window {
                        col,
                        stride_log,
                        offset,
                    } => {
                        let point = window_discharge_point(*offset, *stride_log, &exposure_point);
                        let column = if *col == 2 { tree_c0 } else { tree_c1 };
                        if mle(column, &point) != *value {
                            return Err(format!("window C{} claim false", *col - 2));
                        }
                    }
                    ColRef::Committed(col) => {
                        return Err(format!("KID{} low claim false", col));
                    }
                    _ => unreachable!(),
                }
            }
            assert_eq!(prover.sample_f128(), verifier.sample_f128());

            for (col, point, value) in pending {
                if mle(committed[col], &point) != value {
                    return Err(format!("claim on column {col} is false"));
                }
            }

            Ok(())
        };

        run(&kid[0], &kid[1], &in_[0], &in_[1], &c).expect("honest final spine");

        let mut bad_internal = kid[0].clone();
        bad_internal[tree_base + 5] += F128::ONE;
        assert!(run(&bad_internal, &kid[1], &in_[0], &in_[1], &c).is_err());

        let mut bad_leaf = kid[0].clone();
        bad_leaf[tree_base + SPINE_TREE_KID_LEAF_BASE + 7] += F128::ONE;
        assert!(run(&bad_leaf, &kid[1], &in_[0], &in_[1], &c).is_err());

        let mut bad_wrap_input = in_[0].clone();
        bad_wrap_input[wrap_base + SPINE_WRAP_SLOT] += F128::ONE;
        assert!(run(&kid[0], &kid[1], &bad_wrap_input, &in_[1], &c).is_err());

        let mut bad_wrap_output = c.clone();
        bad_wrap_output[0][wrap_base + SPINE_WRAP_SLOT] += F128::ONE;
        assert!(run(&kid[0], &kid[1], &in_[0], &in_[1], &bad_wrap_output).is_err());
    }
}
