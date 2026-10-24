//! Chain-schedule compiler for duplex Fiat–Shamir channels.
//!
//! A transcript channel (rate-2 Poseidon2b duplex) is a linear chain of
//! permutations whose absorb lanes come from proof/statement data and
//! whose squeeze outputs are the challenges the surrounding verifier
//! algebra consumes. This module compiles an OP LIST — the class-fixed
//! absorb/squeeze schedule of one channel — into:
//!
//! - a per-permutation slot layout ([`DuplexLayout`]): which rate lanes
//!   are XOR-absorbed at each slot (witness data, or protocol constants
//!   like padding/domain-tag/depth lanes), and which slot's output lanes
//!   carry each squeezed challenge;
//! - the committed region columns of the family ([`DuplexColumns`]): two
//!   absorb-lane columns `A0/A1` and four carry columns `C0..C3` holding
//!   every slot's output state — challenge and digest values are read
//!   straight out of carry cells by the surrounding gadgets, no exposure
//!   claims needed;
//! - the [`FixedPattern`] selector/constant columns and the wiring term
//!   lists that let the generic column relations + the 66-layer walk
//!   verify every permutation of the chain at once.
//!
//! The compiler mirrors the byte-level duplex discipline of the sponge
//! transcript channels exactly (16-byte lanes, one permutation per two
//! absorbed lanes, a `0x80…01` pad lane when an odd lane count is flushed
//! to squeeze, an eager permutation after each two-challenge read, a
//! dropped pending challenge when an absorb interrupts squeezing). Slot
//! roles depend only on the op list — a protocol constant per shape
//! class — never on witness values.
//!
//! Wiring of slot `w` (walk layer-0 input before the initial MDS):
//!
//! ```text
//!   raw_j(w) = (1 + START(w))·C_j(w−1) + ABS_j(w)·A_j(w) + CONST_j(w)
//! ```
//!
//! with `START`/`ABS_j` 0/1 selector patterns and `CONST_j` the constant
//! value pattern (pad lanes, domain tags, tree depths, capacity IV lanes
//! at chain starts). All are [`FixedPattern`]s: when the layout tiles one
//! schedule per transaction at a power-of-two stride, their MLEs depend
//! only on the low in-schedule coordinates, so ONE relation covers every
//! transaction and the verifier's evaluation cost is transaction-count
//! independent.

use crate::deep_chain::relations::{ColRef, FixedPattern, RelationTerm};
use crate::deep_chain::{apply_round, initial_mds};
use crate::field::F128;
use noid_poseidon2b::native::permutation::{MDS_FULL, N_ROUNDS, STATE_SIZE};

/// The `0x80…01` pad lane a flush inserts when one absorbed lane is
/// pending: byte 0 = 0x80, byte 15 = 0x01, little-endian u128, read in
/// the flat basis (byte patterns are basis-invariant lane bits, and the
/// deep-chain columns carry flat values).
pub fn pad_lane_flat() -> F128 {
    let mut bytes = [0u8; 16];
    bytes[0] = 0x80;
    bytes[15] |= 0x01;
    let v = u128::from_le_bytes(bytes);
    flat_of_tower_u128(v)
}

/// Flat-basis F128 of a tower-basis u128 bit pattern (transcript lanes
/// are tower bytes; region columns are flat).
pub fn flat_of_tower_u128(v: u128) -> F128 {
    let f = noid_core::hardware::tower_to_flat_u128(v);
    F128 {
        lo: f as u64,
        hi: (f >> 64) as u64,
    }
}

/// One absorbed rate lane: witness data (indexed into the family's data
/// stream) or a protocol constant (given as the tower-basis u128 bit
/// pattern of the absorbed 16 bytes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneSource {
    Data(usize),
    Const(u128),
}

/// One channel operation of the class-fixed schedule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscriptOp {
    /// Absorb lanes in order; `None` = next witness-data lane, `Some(c)` =
    /// a protocol-constant lane (tower bit pattern).
    Absorb(Vec<Option<u128>>),
    /// Squeeze this many 16-byte challenges.
    Squeeze(usize),
}

/// Per-slot rate-lane sources after compilation (`None` = nothing
/// absorbed on that lane at that slot).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DuplexSlot {
    pub lanes: [Option<LaneSource>; 2],
}

/// Compiled slot layout of one duplex channel.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DuplexLayout {
    pub slots: Vec<DuplexSlot>,
    /// `(slot, lane)` whose output state carries the k-th challenge.
    pub challenges: Vec<(usize, usize)>,
    /// Number of witness-data lanes consumed.
    pub n_data: usize,
}

/// Compile an op list into the slot layout. Panics if the schedule
/// squeezes before any permutation ran (no transcript does).
pub fn compile_duplex(ops: &[TranscriptOp]) -> DuplexLayout {
    let pad = pad_const();
    let mut slots: Vec<DuplexSlot> = Vec::new();
    let mut challenges: Vec<(usize, usize)> = Vec::new();
    let mut n_data = 0usize;

    let mut buf: [Option<LaneSource>; 2] = [None, None];
    let mut filled = 0usize;
    let mut squeezing = false;
    // A buffered second challenge lane: Some((slot, lane)).
    let mut pending: Option<(usize, usize)> = None;

    for op in ops {
        match op {
            TranscriptOp::Absorb(lanes) => {
                if squeezing {
                    squeezing = false;
                    pending = None;
                }
                for lane in lanes {
                    let src = match lane {
                        None => {
                            let s = LaneSource::Data(n_data);
                            n_data += 1;
                            s
                        }
                        Some(c) => LaneSource::Const(*c),
                    };
                    buf[filled] = Some(src);
                    filled += 1;
                    if filled == 2 {
                        slots.push(DuplexSlot {
                            lanes: [buf[0], buf[1]],
                        });
                        buf = [None, None];
                        filled = 0;
                    }
                }
            }
            TranscriptOp::Squeeze(m) => {
                if !squeezing {
                    if filled == 1 {
                        // Pad flush: one pending lane + the pad constant.
                        slots.push(DuplexSlot {
                            lanes: [buf[0], Some(LaneSource::Const(pad))],
                        });
                        buf = [None, None];
                        filled = 0;
                    }
                    squeezing = true;
                    pending = None;
                }
                for _ in 0..*m {
                    if let Some(ch) = pending.take() {
                        challenges.push(ch);
                    } else {
                        assert!(
                            !slots.is_empty(),
                            "duplex schedule squeezes before any absorb"
                        );
                        let read_slot = slots.len() - 1;
                        challenges.push((read_slot, 0));
                        pending = Some((read_slot, 1));
                        // The eager permutation after the two-lane read.
                        slots.push(DuplexSlot {
                            lanes: [None, None],
                        });
                    }
                }
            }
        }
    }
    if filled == 1 {
        // Trailing partial absorb with no following squeeze: the lane is
        // still buffered in the native channel (its permutation never ran),
        // but the layout must place it so its data lane exists. Give it a
        // slot with the second lane empty — the chain performs the flush
        // permutation; no challenge is ever read past this point.
        slots.push(DuplexSlot {
            lanes: [buf[0], None],
        });
    }
    DuplexLayout {
        slots,
        challenges,
        n_data,
    }
}

fn pad_const() -> u128 {
    let mut bytes = [0u8; 16];
    bytes[0] = 0x80;
    bytes[15] |= 0x01;
    u128::from_le_bytes(bytes)
}

/// The committed columns of one duplex family instance plus the walk
/// endpoint columns, all flat-basis over `2^w_log` slots (schedule slots
/// first, then pure ghost permutations continuing the chain).
pub struct DuplexColumns {
    /// Absorb-lane data columns (zero where no witness lane is absorbed).
    pub a: [Vec<F128>; 2],
    /// Carry columns: the full output state of every slot.
    pub c: [Vec<F128>; STATE_SIZE],
    /// Walk layer-0 columns (after the initial MDS) — prover side.
    pub s0: [Vec<F128>; STATE_SIZE],
    /// Walk layer-66 columns (equal to `c` by construction) — prover side.
    pub s_out: [Vec<F128>; STATE_SIZE],
    /// Squeezed challenges in schedule order (flat values).
    pub challenges: Vec<F128>,
}

/// Replay the chain natively: XOR-wire each slot's raw state from the
/// carry of the previous slot, the absorb lanes and the constants, then
/// run the 66 rounds. `iv_flat` seeds the capacity lanes at slot 0; the
/// `data` stream supplies the witness lanes (flat basis).
pub fn build_duplex_columns(
    layout: &DuplexLayout,
    iv_flat: [F128; 2],
    data: &[F128],
    w_log: usize,
) -> DuplexColumns {
    let w = 1usize << w_log;
    assert!(layout.slots.len() <= w, "slot domain below schedule length");
    assert_eq!(data.len(), layout.n_data, "data stream length");

    let mut a: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut c: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut s0: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut s_out: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);

    let mut carry = [F128::ZERO; STATE_SIZE];
    for slot in 0..w {
        let mut raw = if slot == 0 {
            [F128::ZERO, F128::ZERO, iv_flat[0], iv_flat[1]]
        } else {
            carry
        };
        if let Some(ds) = layout.slots.get(slot) {
            for (j, lane) in ds.lanes.iter().enumerate() {
                match lane {
                    Some(LaneSource::Data(k)) => {
                        a[j][slot] = data[*k];
                        raw[j] += data[*k];
                    }
                    Some(LaneSource::Const(cv)) => {
                        raw[j] += flat_of_tower_u128(*cv);
                    }
                    None => {}
                }
            }
        }
        let mut state = initial_mds(raw);
        for j in 0..STATE_SIZE {
            s0[j][slot] = state[j];
        }
        for q in 0..N_ROUNDS {
            state = apply_round(q, state);
        }
        for j in 0..STATE_SIZE {
            s_out[j][slot] = state[j];
            c[j][slot] = state[j];
        }
        carry = state;
    }

    let challenges = layout
        .challenges
        .iter()
        .map(|&(slot, lane)| c[lane][slot])
        .collect();

    DuplexColumns {
        a,
        c,
        s0,
        s_out,
        challenges,
    }
}

/// Column indices of one duplex family inside a caller-managed committed
/// table, and fixed-pattern indices inside the caller's pattern table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DuplexFamilyRefs {
    /// Committed indices of `A0, A1`.
    pub a: [usize; 2],
    /// Committed indices of `C0..C3`.
    pub c: [usize; STATE_SIZE],
    /// Fixed index of the chain-start selector.
    pub start: usize,
    /// Fixed indices of the absorb selectors for lanes 0/1.
    pub abs: [usize; 2],
    /// Fixed indices of the constant-value patterns per raw lane.
    pub consts: [usize; STATE_SIZE],
}

/// Build the family's fixed patterns over a `2^low_log` period: chain
/// start, absorb selectors, per-lane constant values (pad/domain lanes on
/// the rate, capacity IV on lanes 2/3). Order matches
/// [`DuplexFamilyRefs`] with `start, abs0, abs1, const0..const3` at
/// offsets `0..7`.
pub fn duplex_fixed_patterns(
    layout: &DuplexLayout,
    iv_flat: [F128; 2],
    low_log: usize,
) -> Vec<FixedPattern> {
    let period = 1usize << low_log;
    assert!(
        layout.slots.len() <= period,
        "schedule longer than the pattern period"
    );
    let mut start = vec![F128::ZERO; period];
    start[0] = F128::ONE;
    let mut abs: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; period]);
    let mut consts: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; period]);
    consts[2][0] = iv_flat[0];
    consts[3][0] = iv_flat[1];
    for (slot, ds) in layout.slots.iter().enumerate() {
        for (j, lane) in ds.lanes.iter().enumerate() {
            match lane {
                Some(LaneSource::Data(_)) => abs[j][slot] = F128::ONE,
                Some(LaneSource::Const(cv)) => consts[j][slot] = flat_of_tower_u128(*cv),
                None => {}
            }
        }
    }
    let mut out = Vec::with_capacity(3 + STATE_SIZE);
    out.push(FixedPattern::new(low_log, start));
    for pat in abs {
        out.push(FixedPattern::new(low_log, pat));
    }
    for pat in consts {
        out.push(FixedPattern::new(low_log, pat));
    }
    out
}

/// [`DuplexFamilyRefs`] for patterns emitted by [`duplex_fixed_patterns`]
/// at `fixed_base` and columns laid out `A0, A1, C0..C3` at `col_base`.
pub fn duplex_family_refs(col_base: usize, fixed_base: usize) -> DuplexFamilyRefs {
    DuplexFamilyRefs {
        a: [col_base, col_base + 1],
        c: std::array::from_fn(|i| col_base + 2 + i),
        start: fixed_base,
        abs: [fixed_base + 1, fixed_base + 2],
        consts: std::array::from_fn(|i| fixed_base + 3 + i),
    }
}

/// Wiring substitution terms for the α-batched walk terminal claim
/// `Σ_j α^{j+1}·S_in,j~(σ)` of a duplex family: with
/// `m_j = Σ_e α^{e+1}·MDS_FULL[e][j]`,
///
/// ```text
///   Σ_j m_j·[ C_j(w−1) + START·C_j(w−1) + ABS_j·A_j + CONST_j ]
/// ```
///
/// (the last two only on rate lanes j ∈ {0,1}; CONST includes the IV
/// lanes on j ∈ {2,3}).
pub fn duplex_substitution_terms(refs: &DuplexFamilyRefs, alpha: F128) -> Vec<RelationTerm> {
    let flat = |v: u128| flat_of_tower_u128(v);
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
    let mut terms = Vec::new();
    for j in 0..STATE_SIZE {
        terms.push(RelationTerm {
            coeff: m[j],
            factors: vec![ColRef::CommittedShift(refs.c[j])],
        });
        terms.push(RelationTerm {
            coeff: m[j],
            factors: vec![ColRef::Fixed(refs.start), ColRef::CommittedShift(refs.c[j])],
        });
        if j < 2 {
            terms.push(RelationTerm {
                coeff: m[j],
                factors: vec![ColRef::Fixed(refs.abs[j]), ColRef::Committed(refs.a[j])],
            });
        }
        terms.push(RelationTerm {
            coeff: m[j],
            factors: vec![ColRef::Fixed(refs.consts[j])],
        });
    }
    terms
}

/// Selection terms tying carry columns to the walk output state:
/// `0 = Σ_w eq·Σ_j β^{j+1}·[C_j(w) + S_out,j(w)]` with `Internal(j)`
/// standing for the walk's j-th output-state column. The relation's
/// terminal values give all four carry claims and one walk start group.
/// Every chain family defines its carries as the full output state, so
/// ONE such relation covers the whole slot domain at assembly.
pub fn carry_selection_terms(c: &[usize; STATE_SIZE], beta: F128) -> Vec<RelationTerm> {
    let mut terms = Vec::new();
    let mut p = F128::ONE;
    for j in 0..STATE_SIZE {
        p = p * beta;
        terms.push(RelationTerm {
            coeff: p,
            factors: vec![ColRef::Committed(c[j])],
        });
        terms.push(RelationTerm {
            coeff: p,
            factors: vec![ColRef::Internal(j)],
        });
    }
    terms
}

/// [`carry_selection_terms`] for a duplex family.
pub fn duplex_selection_terms(refs: &DuplexFamilyRefs, beta: F128) -> Vec<RelationTerm> {
    carry_selection_terms(&refs.c, beta)
}

// ---------------------------------------------------------------------------
// Merkle path chains (two-permutation compress nodes)
// ---------------------------------------------------------------------------

/// A Merkle path family: `n_paths` chains of `depth` compress nodes each.
/// Node `k` of a chain occupies two consecutive slots — an EVEN slot (the
/// first compress permutation, capacity reset to the tree's IV) and an
/// ODD slot (the second permutation, feeding the left digest forward and
/// absorbing the right digest). The node's inputs are the carried digest
/// (previous node's output, or the entry digest at node 0) and a sibling,
/// ordered by a witness direction bit; the chain's final output digest is
/// the recomputed root.
///
/// Slot layout: chain `p` occupies `[p·stride, p·stride + 2·depth)` with
/// `stride = (2·depth).next_power_of_two()`; the tail of each stride and
/// any slots past the last chain are ghost permutations that simply carry
/// the state forward. All selector patterns are periodic in `stride`, so
/// one relation covers every path of every query of every transaction in
/// a class-fixed layout.
///
/// Per-slot wiring (walk layer-0 input before the initial MDS), with
/// `D/SIB/E` stored at the node's EVEN slot and read at the ODD slot
/// through one-step shifts, and the node-to-node digest carry read
/// through a two-step shift:
///
/// ```text
/// rate lane i ∈ {0,1}:
///   raw_i = C_i(w−1)
///         + EVENSTART·C_i(w−1)              (cancel the carry at node 0)
///         + EVENNS·D·C_i(w−1)               ((1+D)·carried on even slots)
///         + EVEN·D·SIB_i
///         + EVENSTART·(1+D)·E_i
///         + ODD·(1+D(w−1))·SIB_i(w−1)       (right side of the node)
///         + ODDNS·D(w−1)·C_i(w−2)
///         + ODDSTART·D(w−1)·E_i(w−1)
/// capacity lane j ∈ {2,3}:
///   raw_j = C_j(w−1) + EVEN·C_j(w−1) + IV_{j−2}·EVEN
/// ```
#[derive(Clone, Copy, Debug)]
pub struct MerklePathFamily {
    pub depth: usize,
    pub n_paths: usize,
}

impl MerklePathFamily {
    pub fn stride(&self) -> usize {
        (2 * self.depth).next_power_of_two()
    }
    pub fn stride_log(&self) -> usize {
        self.stride().trailing_zeros() as usize
    }
    pub fn n_slots(&self) -> usize {
        self.n_paths * self.stride()
    }
}

/// One path's witness: the entry digest (leaf hash lanes), per-level
/// sibling digests and direction bits (`true` = the carried digest is the
/// RIGHT child, sibling on the left). All lanes flat-basis.
#[derive(Clone, Debug)]
pub struct MerklePathWitness {
    pub entry: [F128; 2],
    pub siblings: Vec<[F128; 2]>,
    pub directions: Vec<bool>,
}

/// Committed columns of one Merkle path family (plus prover-side walk
/// endpoints): `E0, E1, SIB0, SIB1, D, C0..C3` in
/// [`merkle_family_refs`] order.
pub struct MerklePathColumns {
    pub e: [Vec<F128>; 2],
    pub sib: [Vec<F128>; 2],
    pub d: Vec<F128>,
    pub c: [Vec<F128>; STATE_SIZE],
    pub s0: [Vec<F128>; STATE_SIZE],
    pub s_out: [Vec<F128>; STATE_SIZE],
    /// Per path: the recomputed root digest lanes (C0/C1 at the last
    /// node's odd slot).
    pub roots: Vec<[F128; 2]>,
}

/// Replay every path chain natively and fill the family columns.
pub fn build_merkle_path_columns(
    family: &MerklePathFamily,
    iv_flat: [F128; 2],
    paths: &[MerklePathWitness],
    w_log: usize,
) -> MerklePathColumns {
    let w = 1usize << w_log;
    let stride = family.stride();
    assert_eq!(paths.len(), family.n_paths);
    assert!(family.n_slots() <= w, "slot domain below the family");

    let mut e: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut sib: [Vec<F128>; 2] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut d = vec![F128::ZERO; w];
    let mut c: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut s0: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut s_out: [Vec<F128>; STATE_SIZE] = std::array::from_fn(|_| vec![F128::ZERO; w]);
    let mut roots = Vec::with_capacity(family.n_paths);

    // Populate the witness cells first.
    for (p, path) in paths.iter().enumerate() {
        assert_eq!(path.siblings.len(), family.depth);
        assert_eq!(path.directions.len(), family.depth);
        let base = p * stride;
        e[0][base] = path.entry[0];
        e[1][base] = path.entry[1];
        for k in 0..family.depth {
            sib[0][base + 2 * k] = path.siblings[k][0];
            sib[1][base + 2 * k] = path.siblings[k][1];
            d[base + 2 * k] = if path.directions[k] {
                F128::ONE
            } else {
                F128::ZERO
            };
        }
    }

    // Chain replay: exactly the wiring documented on the family type.
    let mut carry = [F128::ZERO; STATE_SIZE];
    for slot in 0..w {
        let local = slot & (stride - 1);
        let in_family = slot < family.n_slots();
        let node = local / 2;
        let is_even_node = in_family && local % 2 == 0 && node < family.depth;
        let is_odd_node = in_family && local % 2 == 1 && node < family.depth;

        let raw: [F128; STATE_SIZE] = if is_even_node {
            let d_w = d[slot];
            let carried = if node == 0 {
                [e[0][slot], e[1][slot]]
            } else {
                [carry[0], carry[1]]
            };
            let left = |i: usize| (F128::ONE + d_w) * carried[i] + d_w * sib[i][slot];
            [left(0), left(1), iv_flat[0], iv_flat[1]]
        } else if is_odd_node {
            let d_prev = d[slot - 1];
            let carried = if node == 0 {
                [e[0][slot - 1], e[1][slot - 1]]
            } else {
                // The previous node's output digest, two slots back.
                [c[0][slot - 2], c[1][slot - 2]]
            };
            let right = |i: usize| d_prev * carried[i] + (F128::ONE + d_prev) * sib[i][slot - 1];
            [carry[0] + right(0), carry[1] + right(1), carry[2], carry[3]]
        } else {
            carry
        };

        let mut state = initial_mds(raw);
        for j in 0..STATE_SIZE {
            s0[j][slot] = state[j];
        }
        for q in 0..N_ROUNDS {
            state = apply_round(q, state);
        }
        for j in 0..STATE_SIZE {
            s_out[j][slot] = state[j];
            c[j][slot] = state[j];
        }
        carry = state;

        if is_odd_node && node == family.depth - 1 {
            roots.push([state[0], state[1]]);
        }
    }

    MerklePathColumns {
        e,
        sib,
        d,
        c,
        s0,
        s_out,
        roots,
    }
}

/// Column/pattern indices of one Merkle family inside caller-managed
/// tables. Column order `E0, E1, SIB0, SIB1, D, C0..C3`; pattern order
/// `EVEN, EVENNS, EVENSTART, ODD, ODDNS, ODDSTART, IV2, IV3`.
#[derive(Clone, Copy, Debug)]
pub struct MerkleFamilyRefs {
    pub e: [usize; 2],
    pub sib: [usize; 2],
    pub d: usize,
    pub c: [usize; STATE_SIZE],
    pub even: usize,
    pub evenns: usize,
    pub evenstart: usize,
    pub odd: usize,
    pub oddns: usize,
    pub oddstart: usize,
    pub iv: [usize; 2],
}

pub fn merkle_family_refs(col_base: usize, fixed_base: usize) -> MerkleFamilyRefs {
    MerkleFamilyRefs {
        e: [col_base, col_base + 1],
        sib: [col_base + 2, col_base + 3],
        d: col_base + 4,
        c: std::array::from_fn(|i| col_base + 5 + i),
        even: fixed_base,
        evenns: fixed_base + 1,
        evenstart: fixed_base + 2,
        odd: fixed_base + 3,
        oddns: fixed_base + 4,
        oddstart: fixed_base + 5,
        iv: [fixed_base + 6, fixed_base + 7],
    }
}

/// The family's fixed patterns over one `stride` period (see
/// [`merkle_family_refs`] for the order).
pub fn merkle_fixed_patterns(family: &MerklePathFamily, iv_flat: [F128; 2]) -> Vec<FixedPattern> {
    let low_log = family.stride_log();
    let period = family.stride();
    let mut even = vec![F128::ZERO; period];
    let mut evenns = vec![F128::ZERO; period];
    let mut evenstart = vec![F128::ZERO; period];
    let mut odd = vec![F128::ZERO; period];
    let mut oddns = vec![F128::ZERO; period];
    let mut oddstart = vec![F128::ZERO; period];
    let mut iv0 = vec![F128::ZERO; period];
    let mut iv1 = vec![F128::ZERO; period];
    for k in 0..family.depth {
        even[2 * k] = F128::ONE;
        odd[2 * k + 1] = F128::ONE;
        iv0[2 * k] = iv_flat[0];
        iv1[2 * k] = iv_flat[1];
        if k == 0 {
            evenstart[0] = F128::ONE;
            oddstart[1] = F128::ONE;
        } else {
            evenns[2 * k] = F128::ONE;
            oddns[2 * k + 1] = F128::ONE;
        }
    }
    vec![
        FixedPattern::new(low_log, even),
        FixedPattern::new(low_log, evenns),
        FixedPattern::new(low_log, evenstart),
        FixedPattern::new(low_log, odd),
        FixedPattern::new(low_log, oddns),
        FixedPattern::new(low_log, oddstart),
        FixedPattern::new(low_log, iv0),
        FixedPattern::new(low_log, iv1),
    ]
}

/// Booleanity of the direction bits at node slots:
/// `0 = Σ_w eq·EVEN·(D² + D)`.
pub fn merkle_booleanity_terms(refs: &MerkleFamilyRefs) -> Vec<RelationTerm> {
    vec![
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![
                ColRef::Fixed(refs.even),
                ColRef::Committed(refs.d),
                ColRef::Committed(refs.d),
            ],
        },
        RelationTerm {
            coeff: F128::ONE,
            factors: vec![ColRef::Fixed(refs.even), ColRef::Committed(refs.d)],
        },
    ]
}

/// Wiring substitution terms for the α-batched walk terminal claim of a
/// Merkle path family (see the wiring table on [`MerklePathFamily`]).
pub fn merkle_substitution_terms(refs: &MerkleFamilyRefs, alpha: F128) -> Vec<RelationTerm> {
    let flat = |v: u128| flat_of_tower_u128(v);
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

    let mut terms = Vec::new();
    for i in 0..2 {
        let c_sh = ColRef::CommittedShift(refs.c[i]);
        let c_sh2 = ColRef::CommittedShift2(refs.c[i]);
        let sib = ColRef::Committed(refs.sib[i]);
        let sib_sh = ColRef::CommittedShift(refs.sib[i]);
        let e_col = ColRef::Committed(refs.e[i]);
        let e_sh = ColRef::CommittedShift(refs.e[i]);
        let d_col = ColRef::Committed(refs.d);
        let d_sh = ColRef::CommittedShift(refs.d);
        for factors in [
            vec![c_sh],
            vec![ColRef::Fixed(refs.evenstart), c_sh],
            vec![ColRef::Fixed(refs.evenns), d_col, c_sh],
            vec![ColRef::Fixed(refs.even), d_col, sib],
            vec![ColRef::Fixed(refs.evenstart), e_col],
            vec![ColRef::Fixed(refs.evenstart), d_col, e_col],
            vec![ColRef::Fixed(refs.odd), sib_sh],
            vec![ColRef::Fixed(refs.odd), d_sh, sib_sh],
            vec![ColRef::Fixed(refs.oddns), d_sh, c_sh2],
            vec![ColRef::Fixed(refs.oddstart), d_sh, e_sh],
        ] {
            terms.push(RelationTerm {
                coeff: m[i],
                factors,
            });
        }
    }
    for j in 2..STATE_SIZE {
        let c_sh = ColRef::CommittedShift(refs.c[j]);
        terms.push(RelationTerm {
            coeff: m[j],
            factors: vec![c_sh],
        });
        terms.push(RelationTerm {
            coeff: m[j],
            factors: vec![ColRef::Fixed(refs.even), c_sh],
        });
        terms.push(RelationTerm {
            coeff: m[j],
            factors: vec![ColRef::Fixed(refs.iv[j - 2])],
        });
    }
    terms
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::{Challenger, FsLaneChallenger};
    use crate::deep_chain::relations::{
        RelationColumns, claimed_refs, prove_column_relation, prove_shift_discharge,
        prove_shift_discharge_pow2, verify_column_relation, verify_shift_discharge,
        verify_shift_discharge_pow2,
    };
    use crate::deep_chain::{LaneClaimGroup, prove_deep_chain_walk, verify_deep_chain_walk};
    use crate::lincheck::build_eq_table;

    struct Rng(u64);
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
    }

    fn mle_eval(col: &[F128], point: &[F128]) -> F128 {
        let eq = build_eq_table(point);
        let mut acc = F128::ZERO;
        for (v, e) in col.iter().zip(eq.iter()) {
            acc += *v * *e;
        }
        acc
    }

    #[test]
    fn compile_matches_duplex_discipline() {
        // absorb 3 lanes (one const), squeeze 3, absorb 2, squeeze 1.
        let ops = vec![
            TranscriptOp::Absorb(vec![None, Some(42), None]),
            TranscriptOp::Squeeze(3),
            TranscriptOp::Absorb(vec![None, None]),
            TranscriptOp::Squeeze(1),
        ];
        let layout = compile_duplex(&ops);
        // Slots: [d0, c42], [d1, PAD], pure (eager after ch0/1), pure
        // (eager after ch2), [d2, d3], pure (eager after ch3).
        assert_eq!(layout.slots.len(), 6);
        assert_eq!(layout.n_data, 4);
        assert_eq!(
            layout.slots[0].lanes,
            [Some(LaneSource::Data(0)), Some(LaneSource::Const(42)),]
        );
        assert_eq!(layout.slots[1].lanes[0], Some(LaneSource::Data(1)));
        assert!(matches!(
            layout.slots[1].lanes[1],
            Some(LaneSource::Const(_))
        ));
        assert_eq!(layout.slots[2].lanes, [None, None]);
        assert_eq!(layout.slots[3].lanes, [None, None]);
        assert_eq!(
            layout.slots[4].lanes,
            [Some(LaneSource::Data(2)), Some(LaneSource::Data(3))]
        );
        assert_eq!(layout.slots[5].lanes, [None, None]);
        // Challenges: pair from slot 1 (post-pad state), then lane 0 of the
        // eager slot 2; after the absorb, lane 0 of slot 4's output.
        assert_eq!(layout.challenges, vec![(1, 0), (1, 1), (2, 0), (4, 0)]);
    }

    /// Full native region DAG over a compiled duplex family: selection →
    /// walk → substitution → shift discharges; every terminal claim is
    /// true against the columns, and a corrupted carry lane is caught.
    #[test]
    fn duplex_region_dag_roundtrip_and_negative() {
        let mut rng = Rng(0xD0B1E);
        let ops = vec![
            TranscriptOp::Absorb(vec![None, None, None, Some(7), None]),
            TranscriptOp::Squeeze(2),
            TranscriptOp::Absorb(vec![None, None]),
            TranscriptOp::Squeeze(3),
            TranscriptOp::Absorb(vec![None]),
            TranscriptOp::Squeeze(1),
        ];
        let layout = compile_duplex(&ops);
        let w_log = 4;
        assert!(layout.slots.len() <= 1 << w_log);
        let data: Vec<F128> = (0..layout.n_data).map(|_| rng.f128()).collect();
        let iv = [rng.f128(), rng.f128()];
        let cols = build_duplex_columns(&layout, iv, &data, w_log);
        let fixed = duplex_fixed_patterns(&layout, iv, w_log);
        let refs = duplex_family_refs(0, 0);

        // Prover + verifier in lockstep over one challenger each.
        let run = |cols: &DuplexColumns| -> Result<(), String> {
            let committed: Vec<&[F128]> = vec![
                &cols.a[0], &cols.a[1], &cols.c[0], &cols.c[1], &cols.c[2], &cols.c[3],
            ];
            let internal: Vec<&[F128]> = cols.s_out.iter().map(|c| c.as_slice()).collect();
            let mut ch_p = FsLaneChallenger::new(b"duplex-dag-test");
            let mut ch_v = FsLaneChallenger::new(b"duplex-dag-test");
            let mut pending: Vec<(usize, Vec<F128>, F128)> = Vec::new();

            // Selection.
            let beta = ch_p.sample_f128();
            assert_eq!(beta, ch_v.sample_f128());
            let sel_terms = duplex_selection_terms(&refs, beta);
            let rho: Vec<F128> = ch_p.sample_f128_vec(w_log);
            let _ = ch_v.sample_f128_vec(w_log);
            let (sel_proof, _, _) = prove_column_relation(
                F128::ZERO,
                &rho,
                &sel_terms,
                &RelationColumns {
                    committed: &committed,
                    internal: &internal,
                    fixed: &fixed,
                },
                &mut ch_p,
            );
            let sel_point = verify_column_relation(
                w_log,
                F128::ZERO,
                &rho,
                &sel_terms,
                &fixed,
                &sel_proof,
                &mut ch_v,
            )
            .map_err(|e| format!("selection: {e}"))?;
            let sel_claimed = claimed_refs(&sel_terms);
            let mut group_values = [F128::ZERO; STATE_SIZE];
            for (r, v) in sel_claimed.iter().zip(sel_proof.final_values.iter()) {
                if let ColRef::Committed(c) = r {
                    pending.push((*c, sel_point.clone(), *v));
                }
            }
            // Internal refs carry the walk group values; their claimed
            // positions interleave with the committed ones.
            let mut internal_seen = 0usize;
            for (r, v) in sel_claimed.iter().zip(sel_proof.final_values.iter()) {
                if let ColRef::Internal(j) = r {
                    group_values[*j] = *v;
                    internal_seen += 1;
                }
            }
            assert_eq!(internal_seen, STATE_SIZE);

            // Walk.
            let groups = vec![LaneClaimGroup {
                point: sel_point.clone(),
                values: group_values,
            }];
            let (walk_proof, terminal_p) = prove_deep_chain_walk(&cols.s0, &groups, &mut ch_p);
            let terminal = verify_deep_chain_walk(w_log, &groups, &walk_proof, &mut ch_v)
                .map_err(|e| format!("walk: {e}"))?;
            assert_eq!(terminal_p.values, terminal.values);

            // Substitution.
            let alpha = ch_p.sample_f128();
            assert_eq!(alpha, ch_v.sample_f128());
            let sub_terms = duplex_substitution_terms(&refs, alpha);
            let mut target = F128::ZERO;
            let mut p = F128::ONE;
            for e in 0..STATE_SIZE {
                p = p * alpha;
                target += p * terminal.values[e];
            }
            let (sub_proof, _, _) = prove_column_relation(
                target,
                &terminal.point,
                &sub_terms,
                &RelationColumns {
                    committed: &committed,
                    internal: &[],
                    fixed: &fixed,
                },
                &mut ch_p,
            );
            let sub_point = verify_column_relation(
                w_log,
                target,
                &terminal.point,
                &sub_terms,
                &fixed,
                &sub_proof,
                &mut ch_v,
            )
            .map_err(|e| format!("substitution: {e}"))?;

            // Shift discharges for the four carry shifts.
            let sub_claimed = claimed_refs(&sub_terms);
            for (r, v) in sub_claimed.iter().zip(sub_proof.final_values.iter()) {
                match r {
                    ColRef::Committed(c) => pending.push((*c, sub_point.clone(), *v)),
                    ColRef::CommittedShift(c) => {
                        let (shift_proof, _) =
                            prove_shift_discharge(committed[*c], &sub_point, *v, &mut ch_p);
                        let pt =
                            verify_shift_discharge(w_log, &sub_point, *v, &shift_proof, &mut ch_v)
                                .map_err(|e| format!("shift: {e}"))?;
                        pending.push((*c, pt, shift_proof.final_value));
                    }
                    _ => unreachable!(),
                }
            }
            assert_eq!(ch_p.sample_f128(), ch_v.sample_f128(), "lockstep");

            // Discharge everything against the columns (the outer PCS
            // commitment binds these in production).
            for (c, pt, v) in &pending {
                if mle_eval(committed[*c], pt) != *v {
                    return Err(format!("claim on column {c} is false"));
                }
            }
            Ok(())
        };

        run(&cols).expect("honest duplex DAG verifies");

        // Negative: corrupt one carry lane (the prover then folds the
        // corrupted tables; the walk/wiring must push a false claim).
        let mut bad = build_duplex_columns(&layout, iv, &data, w_log);
        bad.c[0][3] += F128::ONE;
        assert!(
            crate::dishonest_fixture_rejected(|| run(&bad)),
            "corrupted carry lane slipped through the duplex DAG"
        );
    }

    /// Structural anchor: the family's per-path root digests equal the
    /// REAL sponge-mode compress chain (`noid_poseidon2b::native::
    /// compress`) folded over the same leaf/siblings/directions — the
    /// even/odd wiring is byte-for-byte the two-permutation compress.
    #[test]
    fn merkle_family_matches_native_compress_chain() {
        use noid_poseidon2b::native::compression::compress;
        use noid_poseidon2b::native::domain::{TAG_COMPRESS, capacity_iv};

        let mut rng = Rng(0x3E7A);
        let depth = 3;
        let family = MerklePathFamily { depth, n_paths: 2 };
        let iv_tower = capacity_iv(TAG_COMPRESS);
        let iv_flat = [
            flat_of_tower_u128(iv_tower[0].0),
            flat_of_tower_u128(iv_tower[1].0),
        ];

        let rnd_digest = |rng: &mut Rng| {
            let mut d = [0u8; 32];
            for k in 0..4 {
                d[8 * k..8 * (k + 1)].copy_from_slice(&rng.next_u64().to_le_bytes());
            }
            d
        };
        let lanes = |d: &[u8; 32]| {
            [
                flat_of_tower_u128(u128::from_le_bytes(d[..16].try_into().unwrap())),
                flat_of_tower_u128(u128::from_le_bytes(d[16..].try_into().unwrap())),
            ]
        };

        let mut paths = Vec::new();
        let mut expected_roots = Vec::new();
        for p in 0..family.n_paths {
            let entry = rnd_digest(&mut rng);
            let sibs: Vec<[u8; 32]> = (0..depth).map(|_| rnd_digest(&mut rng)).collect();
            let dirs: Vec<bool> = (0..depth).map(|k| (rng.next_u64() >> k) & 1 == 1).collect();
            // Native fold: carried is LEFT iff the direction bit is 0.
            let mut hash = entry;
            for k in 0..depth {
                hash = if dirs[k] {
                    compress(&sibs[k], &hash)
                } else {
                    compress(&hash, &sibs[k])
                };
            }
            expected_roots.push(lanes(&hash));
            paths.push(MerklePathWitness {
                entry: lanes(&entry),
                siblings: sibs.iter().map(&lanes).collect(),
                directions: dirs,
            });
            let _ = p;
        }

        let w_log = family.n_slots().next_power_of_two().trailing_zeros() as usize;
        let cols = build_merkle_path_columns(&family, iv_flat, &paths, w_log);
        assert_eq!(cols.roots, expected_roots, "family diverged from compress");
    }

    /// Full native region DAG over a Merkle path family: booleanity +
    /// selection + walk + substitution + shift/shift2 discharges; all
    /// claims true against the columns; corrupted sibling and flipped
    /// direction bit rejected.
    #[test]
    fn merkle_region_dag_roundtrip_and_negatives() {
        use noid_poseidon2b::native::domain::{TAG_COMPRESS, capacity_iv};

        let mut rng = Rng(0x3E7B);
        let depth = 3;
        let family = MerklePathFamily { depth, n_paths: 2 };
        let iv_tower = capacity_iv(TAG_COMPRESS);
        let iv_flat = [
            flat_of_tower_u128(iv_tower[0].0),
            flat_of_tower_u128(iv_tower[1].0),
        ];
        let mut paths = Vec::new();
        for _ in 0..family.n_paths {
            paths.push(MerklePathWitness {
                entry: [rng.f128(), rng.f128()],
                siblings: (0..depth).map(|_| [rng.f128(), rng.f128()]).collect(),
                directions: (0..depth).map(|_| rng.next_u64() & 1 == 1).collect(),
            });
        }
        let w_log = family.n_slots().next_power_of_two().trailing_zeros() as usize;
        let fixed = merkle_fixed_patterns(&family, iv_flat);
        let refs = merkle_family_refs(0, 0);

        let run = |cols: &MerklePathColumns| -> Result<(), String> {
            let committed: Vec<&[F128]> = vec![
                &cols.e[0],
                &cols.e[1],
                &cols.sib[0],
                &cols.sib[1],
                &cols.d,
                &cols.c[0],
                &cols.c[1],
                &cols.c[2],
                &cols.c[3],
            ];
            let internal: Vec<&[F128]> = cols.s_out.iter().map(|c| c.as_slice()).collect();
            let mut ch_p = FsLaneChallenger::new(b"merkle-dag-test");
            let mut ch_v = FsLaneChallenger::new(b"merkle-dag-test");
            let mut pending: Vec<(usize, Vec<F128>, F128)> = Vec::new();

            // Booleanity of the gated direction bits.
            let bool_terms = merkle_booleanity_terms(&refs);
            let rho_b: Vec<F128> = ch_p.sample_f128_vec(w_log);
            let _ = ch_v.sample_f128_vec(w_log);
            let (bool_proof, _, _) = prove_column_relation(
                F128::ZERO,
                &rho_b,
                &bool_terms,
                &RelationColumns {
                    committed: &committed,
                    internal: &[],
                    fixed: &fixed,
                },
                &mut ch_p,
            );
            let bool_point = verify_column_relation(
                w_log,
                F128::ZERO,
                &rho_b,
                &bool_terms,
                &fixed,
                &bool_proof,
                &mut ch_v,
            )
            .map_err(|e| format!("booleanity: {e}"))?;
            pending.push((refs.d, bool_point, bool_proof.final_values[0]));

            // Selection → walk group.
            let beta = ch_p.sample_f128();
            assert_eq!(beta, ch_v.sample_f128());
            let sel_terms = carry_selection_terms(&refs.c, beta);
            let rho: Vec<F128> = ch_p.sample_f128_vec(w_log);
            let _ = ch_v.sample_f128_vec(w_log);
            let (sel_proof, _, _) = prove_column_relation(
                F128::ZERO,
                &rho,
                &sel_terms,
                &RelationColumns {
                    committed: &committed,
                    internal: &internal,
                    fixed: &fixed,
                },
                &mut ch_p,
            );
            let sel_point = verify_column_relation(
                w_log,
                F128::ZERO,
                &rho,
                &sel_terms,
                &fixed,
                &sel_proof,
                &mut ch_v,
            )
            .map_err(|e| format!("selection: {e}"))?;
            let sel_claimed = claimed_refs(&sel_terms);
            let mut group_values = [F128::ZERO; STATE_SIZE];
            for (r, v) in sel_claimed.iter().zip(sel_proof.final_values.iter()) {
                match r {
                    ColRef::Committed(c) => pending.push((*c, sel_point.clone(), *v)),
                    ColRef::Internal(j) => group_values[*j] = *v,
                    _ => unreachable!(),
                }
            }

            let groups = vec![LaneClaimGroup {
                point: sel_point.clone(),
                values: group_values,
            }];
            let (walk_proof, _) = prove_deep_chain_walk(&cols.s0, &groups, &mut ch_p);
            let terminal = verify_deep_chain_walk(w_log, &groups, &walk_proof, &mut ch_v)
                .map_err(|e| format!("walk: {e}"))?;

            // Substitution through the compress wiring.
            let alpha = ch_p.sample_f128();
            assert_eq!(alpha, ch_v.sample_f128());
            let sub_terms = merkle_substitution_terms(&refs, alpha);
            let mut target = F128::ZERO;
            let mut p = F128::ONE;
            for e in 0..STATE_SIZE {
                p = p * alpha;
                target += p * terminal.values[e];
            }
            let (sub_proof, _, _) = prove_column_relation(
                target,
                &terminal.point,
                &sub_terms,
                &RelationColumns {
                    committed: &committed,
                    internal: &[],
                    fixed: &fixed,
                },
                &mut ch_p,
            );
            let sub_point = verify_column_relation(
                w_log,
                target,
                &terminal.point,
                &sub_terms,
                &fixed,
                &sub_proof,
                &mut ch_v,
            )
            .map_err(|e| format!("substitution: {e}"))?;

            // Discharge: plain claims directly; shifted claims through the
            // 1-step / 2-step reductions.
            let sub_claimed = claimed_refs(&sub_terms);
            for (r, v) in sub_claimed.iter().zip(sub_proof.final_values.iter()) {
                match r {
                    ColRef::Committed(c) => pending.push((*c, sub_point.clone(), *v)),
                    ColRef::CommittedShift(c) => {
                        let (pr, _) =
                            prove_shift_discharge(committed[*c], &sub_point, *v, &mut ch_p);
                        let pt = verify_shift_discharge(w_log, &sub_point, *v, &pr, &mut ch_v)
                            .map_err(|e| format!("shift: {e}"))?;
                        pending.push((*c, pt, pr.final_value));
                    }
                    ColRef::CommittedShift2(c) => {
                        let (pr, _) =
                            prove_shift_discharge_pow2(committed[*c], &sub_point, *v, 1, &mut ch_p);
                        let pt =
                            verify_shift_discharge_pow2(w_log, &sub_point, *v, 1, &pr, &mut ch_v)
                                .map_err(|e| format!("shift2: {e}"))?;
                        pending.push((*c, pt, pr.final_value));
                    }
                    _ => unreachable!(),
                }
            }
            assert_eq!(ch_p.sample_f128(), ch_v.sample_f128(), "lockstep");

            for (c, pt, v) in &pending {
                if mle_eval(committed[*c], pt) != *v {
                    return Err(format!("claim on column {c} is false"));
                }
            }
            Ok(())
        };

        let cols = build_merkle_path_columns(&family, iv_flat, &paths, w_log);
        run(&cols).expect("honest merkle DAG verifies");

        // Corrupted sibling lane.
        let mut bad = build_merkle_path_columns(&family, iv_flat, &paths, w_log);
        bad.sib[0][2] += F128::ONE;
        assert!(
            crate::dishonest_fixture_rejected(|| run(&bad)),
            "corrupted sibling slipped through"
        );

        // Flipped direction bit (column only — the chains no longer match
        // the wiring).
        let mut bad = build_merkle_path_columns(&family, iv_flat, &paths, w_log);
        bad.d[0] += F128::ONE;
        assert!(
            crate::dishonest_fixture_rejected(|| run(&bad)),
            "flipped direction slipped through"
        );

        // Corrupted carry (root forgery attempt).
        let mut bad = build_merkle_path_columns(&family, iv_flat, &paths, w_log);
        let last = 2 * depth - 1;
        bad.c[0][last] += F128::ONE;
        assert!(
            crate::dishonest_fixture_rejected(|| run(&bad)),
            "forged root digest slipped through"
        );
    }

    /// Challenge cells read from the carry columns equal the values the
    /// schedule's chain actually squeezes (self-consistency of the layout
    /// challenge map).
    #[test]
    fn challenge_cells_match_chain_replay() {
        let mut rng = Rng(0xC4A11);
        let ops = vec![
            TranscriptOp::Absorb(vec![None, None, None]),
            TranscriptOp::Squeeze(4),
            TranscriptOp::Absorb(vec![Some(5)]),
            TranscriptOp::Squeeze(2),
        ];
        let layout = compile_duplex(&ops);
        let data: Vec<F128> = (0..layout.n_data).map(|_| rng.f128()).collect();
        let iv = [rng.f128(), rng.f128()];
        let cols = build_duplex_columns(&layout, iv, &data, 4);
        assert_eq!(cols.challenges.len(), 6);
        for (k, &(slot, lane)) in layout.challenges.iter().enumerate() {
            assert_eq!(cols.challenges[k], cols.c[lane][slot]);
        }
        // Distinct challenges (whp) — the chain is actually mixing.
        for i in 0..cols.challenges.len() {
            for j in 0..i {
                assert_ne!(cols.challenges[i], cols.challenges[j]);
            }
        }
    }
}
