//! Verifier-randomness abstraction.
//!
//! A [`Challenger`] is the source of verifier challenges in the protocol.
//! The prover writes its messages into the challenger (`observe_*`) and reads
//! challenges back out (`sample_*`). The verifier mirrors this exactly — as
//! it walks through the proof, it observes each prover message and samples
//! the same challenges, so both sides derive the same randomness in lockstep.
//!
//! Two implementations:
//! - `RandomChallenger` — seeded pseudo-random, ignores observed messages.
//!   Kept around for bench isolation (measure prover cost without FS overhead)
//!   and soundness mutation tests. **Not sound for real proofs**, and to make
//!   that structural it is compiled *only* under `cfg(test)` or the
//!   `unsound-challenger` feature — a normal (real-proof) build has no insecure
//!   challenger to reach for.
//! - [`FsChallenger`] — Fiat-Shamir transcript backed by the production
//!   Poseidon2b sponge domain.

use crate::field::{F128, F256};
use noid_poseidon2b::native::{
    Poseidon2bSponge, TAG_FSCH256, TAG_FSCHALNG, TAG_LANE256, TAG_LANECHAL, capacity_iv,
    poseidon2b_hash_byte_slices,
};

// `Send` supertrait: the verifier runs its PIOP/PCS replay inside a dedicated
// single-thread rayon pool (see `verifier::verifier_pool`), so the challenger
// it threads through must be able to cross into that pool. Both concrete
// challengers (`RandomChallenger`, `FsChallenger`) are trivially `Send`.
pub trait Challenger: Send {
    /// Absorb a domain-separation label (e.g. `b"history-zerocheck-v0"`). Each
    /// protocol entry should call this once on entry so a transcript from
    /// one protocol cannot be replayed as another.
    fn observe_label(&mut self, _label: &[u8]) {
        // default no-op — RandomChallenger inherits this.
    }

    /// Absorb a single F128 prover message.
    fn observe_f128(&mut self, value: F128);

    /// Absorb a slice of F128 prover messages (e.g. the round-1 vector).
    fn observe_f128_slice(&mut self, values: &[F128]) {
        for v in values {
            self.observe_f128(*v);
        }
    }

    /// Absorb one C1 extension-field prover message.
    ///
    /// Production C1 challengers override this with an explicit wide op
    /// frame. The coordinate-wise default keeps test and forwarding
    /// challengers source-compatible, but it is not the canonical C1 wire
    /// schedule.
    fn observe_f256(&mut self, value: F256) {
        self.observe_f128(value.lo);
        self.observe_f128(value.hi);
    }

    /// Absorb a slice of C1 extension-field prover messages.
    fn observe_f256_slice(&mut self, values: &[F256]) {
        for value in values {
            self.observe_f256(*value);
        }
    }

    /// Absorb arbitrary bytes (e.g. a Merkle root or a statement digest).
    fn observe_bytes(&mut self, _bytes: &[u8]) {
        // default no-op — RandomChallenger inherits this.
    }

    /// Produce one F128 challenge.
    fn sample_f128(&mut self) -> F128;

    /// Produce `n` F128 challenges, in order.
    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.sample_f128()).collect()
    }

    /// Produce one C1 extension-field algebraic challenge.
    ///
    /// The canonical C1 implementations override this so the pair is one
    /// framed wide squeeze. The fallback is suitable for test challengers.
    fn sample_f256(&mut self) -> F256 {
        let lanes = self.sample_f128_vec(2);
        F256::from_raw_challenge_lanes(lanes[0], lanes[1])
    }

    /// Produce `n` C1 extension-field algebraic challenges.
    fn sample_f256_vec(&mut self, n: usize) -> Vec<F256> {
        (0..n).map(|_| self.sample_f256()).collect()
    }

    /// Prover-side transcript grinding: snapshot the current transcript state,
    /// search for a `u64` nonce such that the Poseidon2b proof hash over
    /// `(state, nonce)` has at least `bits` leading zero bits, then absorb the
    /// nonce into the transcript so subsequent challenges bind to it.
    ///
    /// Default implementation is a no-op (returns 0). Real implementations
    /// — e.g. [`FsChallenger`] — do the actual grind work and absorb the
    /// nonce. `bits = 0` means "no PoW required"; still absorbs the 0 nonce
    /// so the verifier mirror is byte-identical.
    fn grind_pow(&mut self, _bits: u32) -> u64 {
        0
    }

    /// Verifier-side mirror of [`Self::grind_pow`]: check that `nonce`
    /// satisfies the `bits`-leading-zeros PoW against the current transcript
    /// state, then absorb the nonce so the running state stays in lockstep
    /// with the prover.
    ///
    /// Default implementation accepts unconditionally (no-op). Real
    /// implementations must check the PoW; an honest verifier rejects the
    /// proof if this returns `false`.
    fn verify_pow(&mut self, _nonce: u64, _bits: u32) -> bool {
        true
    }
}

// ---------------------------------------------------------------------------
// RandomChallenger — seeded SplitMix64 pseudo-random source.
//
// Ignores observed messages (no Fiat-Shamir binding). Keep for bench isolation
// and soundness mutation tests; real proofs MUST use FsChallenger.
//
// Gated behind `cfg(test)` / `feature = "unsound-challenger"`: a real-proof
// build does not compile this type at all, so no production code path can
// accidentally instantiate an unsound challenger. See the module docs.
// ---------------------------------------------------------------------------

#[cfg(any(test, feature = "unsound-challenger"))]
#[derive(Clone, Debug)]
pub struct RandomChallenger {
    state: u64,
}

#[cfg(any(test, feature = "unsound-challenger"))]
impl RandomChallenger {
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }
}

#[cfg(any(test, feature = "unsound-challenger"))]
impl Challenger for RandomChallenger {
    #[inline]
    fn observe_f128(&mut self, _value: F128) {
        // intentional no-op: random challenger is independent of prover state
    }

    fn sample_f128(&mut self) -> F128 {
        let lo = splitmix64(&mut self.state);
        let hi = splitmix64(&mut self.state);
        F128 { lo, hi }
    }
}

#[cfg(any(test, feature = "unsound-challenger"))]
#[inline]
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E3779B97F4A7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}

// ---------------------------------------------------------------------------
// FsChallenger — Fiat-Shamir transcript.
//
// Tag bytes (one-byte op + one-byte kind) encode the operation type so that
// e.g. an `observe_f128_slice` of length 1 cannot collide with `observe_f128`,
// and a slice observation cannot collide with two scalar observations of the
// same total length.
//
// Sampling clones the live transcript state, squeezes challenge bytes, and
// absorbs the squeezed output back into the live state. This "duplex" pattern
// binds each subsequent challenge/observation to all prior squeezed output.
// ---------------------------------------------------------------------------

const OP_DOMAIN: u8 = 0x01;
const OP_LABEL: u8 = 0x02;
const OP_OBSERVE: u8 = 0x03;
const OP_SQUEEZE: u8 = 0x04;
const OP_BYTES: u8 = 0x05;

const KIND_SCALAR: u8 = 0x01;
const KIND_SLICE: u8 = 0x02;
const KIND_WIDE_SCALAR: u8 = 0x03;
const KIND_WIDE_SLICE: u8 = 0x04;

/// Global Fiat-Shamir hash counters, enabled with `--features hash-count`.
/// Tracks proof-core squeeze count and PoW hash checks; absorbed
/// transcript bytes are tracked via [`FsChallenger::absorbed_bytes`].
#[cfg(feature = "hash-count")]
pub mod fs_count {
    use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

    /// Number of XOF finalizations (one per `sample_f128` /
    /// `sample_f128_vec` / PoW state-digest extraction).
    pub static SQUEEZES: AtomicU64 = AtomicU64::new(0);
    /// Number of PoW hash evaluations.
    pub static POW_HASH: AtomicU64 = AtomicU64::new(0);

    pub fn reset() {
        SQUEEZES.store(0, Relaxed);
        POW_HASH.store(0, Relaxed);
    }

    /// (squeezes, pow_hash_calls)
    pub fn snapshot() -> (u64, u64) {
        (SQUEEZES.load(Relaxed), POW_HASH.load(Relaxed))
    }
}

#[derive(Clone)]
pub struct FsChallenger {
    sponge: Poseidon2bSponge,
    /// Running total of absorbed transcript bytes, for the `hash-count`
    /// instrumentation (read only under that feature).
    #[allow(dead_code)]
    n_absorbed: u64,
    c1: bool,
}

impl FsChallenger {
    /// New challenger seeded with a domain-separation tag (e.g.
    /// `b"history-r1cs-v0"`). The domain is length-prefixed before being
    /// absorbed so two domains where one is a prefix of the other cannot
    /// produce the same initial state.
    pub fn new(domain: &[u8]) -> Self {
        Self::with_profile(domain, TAG_FSCHALNG, false)
    }

    /// C1 byte-oriented challenger with a domain-separated capacity IV and
    /// canonical extension-field op framing.
    pub fn new_c1(domain: &[u8]) -> Self {
        Self::with_profile(domain, TAG_FSCH256, true)
    }

    fn with_profile(domain: &[u8], tag: noid_poseidon2b::native::DomainTag, c1: bool) -> Self {
        let mut c = Self {
            sponge: Poseidon2bSponge::with_iv(capacity_iv(tag)),
            n_absorbed: 0,
            c1,
        };
        c.absorb(&[OP_DOMAIN]);
        c.absorb(&(domain.len() as u64).to_le_bytes());
        c.absorb(domain);
        c
    }

    /// Absorb bytes into the running transcript state.
    #[inline]
    fn absorb(&mut self, bytes: &[u8]) {
        self.sponge.update(bytes);
        self.n_absorbed = self.n_absorbed.wrapping_add(bytes.len() as u64);
    }

    #[inline]
    fn absorb_f128(&mut self, v: F128) {
        self.absorb(&v.lo.to_le_bytes());
        self.absorb(&v.hi.to_le_bytes());
    }

    #[inline]
    fn absorb_f256(&mut self, value: F256) {
        self.absorb_f128(value.lo);
        self.absorb_f128(value.hi);
    }

    /// Squeeze `out.len()` pseudorandom bytes from a cloned Poseidon2b
    /// transcript state without mutating the live transcript.
    fn squeeze_into(&self, out: &mut [u8]) {
        let mut sponge = self.sponge.clone();
        sponge.flush_to_squeeze();

        let mut off = 0usize;
        while off < out.len() {
            let pair = sponge.squeeze();
            let mut block = [0u8; 32];
            block[..16].copy_from_slice(&pair[0].to_u128().to_le_bytes());
            block[16..].copy_from_slice(&pair[1].to_u128().to_le_bytes());
            let take = (out.len() - off).min(32);
            out[off..off + take].copy_from_slice(&block[..take]);
            off += take;
        }
    }

    /// Total bytes absorbed into the transcript so far. Used by the
    /// `hash-count` instrumentation.
    #[cfg(feature = "hash-count")]
    pub fn absorbed_bytes(&self) -> u64 {
        self.n_absorbed
    }
}

impl Challenger for FsChallenger {
    fn observe_label(&mut self, label: &[u8]) {
        self.absorb(&[OP_LABEL]);
        self.absorb(&(label.len() as u64).to_le_bytes());
        self.absorb(label);
    }

    fn observe_f128(&mut self, value: F128) {
        self.absorb(&[OP_OBSERVE, KIND_SCALAR]);
        self.absorb_f128(value);
    }

    fn observe_f128_slice(&mut self, values: &[F128]) {
        self.absorb(&[OP_OBSERVE, KIND_SLICE]);
        self.absorb(&(values.len() as u64).to_le_bytes());
        for v in values {
            self.absorb_f128(*v);
        }
    }

    fn observe_f256(&mut self, value: F256) {
        assert!(
            self.c1,
            "wide transcript operation requires FsChallenger::new_c1"
        );
        self.absorb(&[OP_OBSERVE, KIND_WIDE_SCALAR]);
        self.absorb_f256(value);
    }

    fn observe_f256_slice(&mut self, values: &[F256]) {
        assert!(
            self.c1,
            "wide transcript operation requires FsChallenger::new_c1"
        );
        self.absorb(&[OP_OBSERVE, KIND_WIDE_SLICE]);
        self.absorb(&(values.len() as u64).to_le_bytes());
        for value in values {
            self.absorb_f256(*value);
        }
    }

    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.absorb(&[OP_BYTES]);
        self.absorb(&(bytes.len() as u64).to_le_bytes());
        self.absorb(bytes);
    }

    fn sample_f128(&mut self) -> F128 {
        #[cfg(feature = "hash-count")]
        fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.absorb(&[OP_SQUEEZE, KIND_SCALAR]);
        let mut buf = [0u8; 16];
        self.squeeze_into(&mut buf);
        // Re-absorb the squeezed bytes so subsequent ops bind to this challenge.
        self.absorb(&buf);
        let lo = u64::from_le_bytes(buf[..8].try_into().unwrap());
        let hi = u64::from_le_bytes(buf[8..].try_into().unwrap());
        F128 { lo, hi }
    }

    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        #[cfg(feature = "hash-count")]
        fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.absorb(&[OP_SQUEEZE, KIND_SLICE]);
        self.absorb(&(n as u64).to_le_bytes());
        let mut buf = vec![0u8; n * 16];
        self.squeeze_into(&mut buf);
        self.absorb(&buf);
        buf.chunks_exact(16)
            .map(|c| F128 {
                lo: u64::from_le_bytes(c[..8].try_into().unwrap()),
                hi: u64::from_le_bytes(c[8..].try_into().unwrap()),
            })
            .collect()
    }

    fn sample_f256(&mut self) -> F256 {
        assert!(
            self.c1,
            "wide transcript operation requires FsChallenger::new_c1"
        );
        #[cfg(feature = "hash-count")]
        fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.absorb(&[OP_SQUEEZE, KIND_WIDE_SCALAR]);
        let mut bytes = [0u8; 32];
        self.squeeze_into(&mut bytes);
        self.absorb(&bytes);
        let raw = F256::from_le_bytes(bytes);
        F256::from_raw_challenge_lanes(raw.lo, raw.hi)
    }

    fn sample_f256_vec(&mut self, n: usize) -> Vec<F256> {
        assert!(
            self.c1,
            "wide transcript operation requires FsChallenger::new_c1"
        );
        #[cfg(feature = "hash-count")]
        fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.absorb(&[OP_SQUEEZE, KIND_WIDE_SLICE]);
        self.absorb(&(n as u64).to_le_bytes());
        let mut bytes = vec![0u8; n * 32];
        self.squeeze_into(&mut bytes);
        self.absorb(&bytes);
        bytes
            .chunks_exact(32)
            .map(|chunk| {
                let mut encoded = [0u8; 32];
                encoded.copy_from_slice(chunk);
                let raw = F256::from_le_bytes(encoded);
                F256::from_raw_challenge_lanes(raw.lo, raw.hi)
            })
            .collect()
    }

    fn grind_pow(&mut self, bits: u32) -> u64 {
        let state_digest = self.pow_state_digest();
        // Aggregate-aware parallelism: decide on the grind's *expected hash
        // work* (`2^bits`), not a raw bit threshold. Fold-challenge grinds are
        // individually modest — e.g. 2^15 at L0 under the per-round profiles —
        // but the prover issues one per lane fold (6× at L0, 3× per recursive
        // level), so the per-level aggregate (~2^17–2^18 hashes) lands on the
        // multi-threaded critical path. We go parallel once a single grind
        // clears the rayon dispatch break-even (~2^13 hashes); the genuinely
        // tiny deep-level grinds (2^3–2^11) stay sequential, where the serial
        // loop beats parallel-dispatch overhead. `find_first` returns the
        // globally smallest satisfying nonce, so the result is identical to the
        // sequential search (deterministic proofs) regardless of this choice.
        const PARALLEL_GRIND_MIN_HASHES: u64 = 1 << 13;
        let nonce = if bits == 0 {
            0
        } else if (1u64 << bits.min(63)) < PARALLEL_GRIND_MIN_HASHES {
            // Sequential search: try u64 nonces until the Poseidon2b proof
            // hash has `bits` leading zeros.
            let mut nonce: u64 = 0;
            loop {
                if proof_hash_has_leading_zero_bits(&state_digest, nonce, bits) {
                    break nonce;
                }
                nonce = nonce.wrapping_add(1);
            }
        } else {
            // Block-parallel search. Blocks are scanned in order and
            // `find_first` returns the smallest match within a block, so the
            // result is deterministic (the globally smallest satisfying nonce).
            // Block ≈ 2× the expected attempts: large enough that the match
            // usually falls inside one block (so all threads do useful
            // pre-match work), small enough to avoid the 4× over-scan the old
            // `+2` block caused (which left ~¾ of threads doing cancelled work).
            use rayon::prelude::*;
            let block: u64 = 1 << (bits.min(24) + 1);
            let mut start: u64 = 0;
            loop {
                if let Some(n) = (start..start.saturating_add(block))
                    .into_par_iter()
                    .find_first(|&n| proof_hash_has_leading_zero_bits(&state_digest, n, bits))
                {
                    break n;
                }
                start = start.saturating_add(block);
            }
        };
        // Absorb the nonce so subsequent transcript state binds to it.
        // Verifier mirrors via verify_pow.
        self.observe_bytes(&nonce.to_le_bytes());
        nonce
    }

    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        let state_digest = self.pow_state_digest();
        let ok = if bits == 0 {
            // No PoW required here. An honest prover emits the canonical nonce
            // 0 (see `grind_pow`), so reject any non-zero value: it can only be
            // a re-grinding knob, and accepting it would leave proofs malleable
            // (a proof and its nonce-mutated twin would both verify). This
            // closes no soundness gap — when grinding_bits = 0 the query phase
            // already carries the full security target, and the FS soundness
            // accounting assumes free re-grinding regardless — it just keeps
            // proofs canonical / non-malleable at zero-bit grinding sites.
            nonce == 0
        } else {
            proof_hash_has_leading_zero_bits(&state_digest, nonce, bits)
        };
        // Absorb regardless of `ok` so the transcript stays byte-identical to
        // the prover's (an honest prover always reaches this with the same
        // nonce); a failed check rejects the proof at the call site anyway.
        self.observe_bytes(&nonce.to_le_bytes());
        ok
    }
}

impl FsChallenger {
    /// Extract a 32-byte digest from the current challenger state to use as the
    /// PoW base, without mutating the live transcript.
    #[inline]
    fn pow_state_digest(&self) -> [u8; 32] {
        #[cfg(feature = "hash-count")]
        fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

        let mut out = [0u8; 32];
        self.squeeze_into(&mut out);
        out
    }
}

/// Check whether the proof-core PoW hash over `(state_digest, nonce)` has at
/// least `bits` leading zero bits.
#[inline]
fn proof_hash_has_leading_zero_bits(state_digest: &[u8; 32], nonce: u64, bits: u32) -> bool {
    #[cfg(feature = "hash-count")]
    fs_count::POW_HASH.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

    let h: [u8; 32] = {
        let nonce_bytes = nonce.to_le_bytes();
        poseidon2b_hash_byte_slices(b"NOID/IVC/FS-POW", &[state_digest, &nonce_bytes])
    };

    digest_has_leading_zero_bits(&h, bits)
}

#[inline]
fn digest_has_leading_zero_bits(h: &[u8; 32], bits: u32) -> bool {
    let full_bytes = (bits / 8) as usize;
    let extra = bits % 8;
    for &b in h.iter().take(full_bytes) {
        if b != 0 {
            return false;
        }
    }
    if extra > 0 && (h[full_bytes] >> (8 - extra)) != 0 {
        return false;
    }
    true
}

// ---------------------------------------------------------------------------
// FsLaneChallenger — lane-oriented Fiat-Shamir transcript (the FieldR1cs /
// trace-facing challenger).
//
// The byte-oriented FsChallenger above absorbs 1–2-byte op tags, so its lane
// packing is never 16-byte aligned and an in-circuit replay would need
// bit-splitting with range checks. This challenger absorbs whole 16-byte
// LANES only: every op is one constant header lane (op, kind, length)
// followed by value/byte lanes, so an absorbed lane is an *affine* function
// of the observed field elements — exactly what the in-circuit trace gadget
// (`crate::field_circuit::FsChannelTrace`) replays, and the same shape as
// the killshot channel (`Poseidon2bChannel`) that the killshot traces
// replay.
//
// State is kept in the FLAT (GCM) basis — bit-identical to the circuit's
// F128 wires; the permutation runs through the tower-basis production
// `Poseidon2bPermutation` via the `noid_core::hardware` basis isomorphism.
// Duplex semantics mirror `Poseidon2bSponge` + `Poseidon2bChannel`:
// rate-2 pair buffering, `0x80…01` pad block on odd flush, squeeze emits
// `state[0]` and holds `state[1]` pending, then permutes.
// ---------------------------------------------------------------------------

pub const FS_OP_DOMAIN: u8 = 0x01;
pub const FS_OP_LABEL: u8 = 0x02;
pub const FS_OP_OBSERVE: u8 = 0x03;
pub const FS_OP_SQUEEZE: u8 = 0x04;
pub const FS_OP_BYTES: u8 = 0x05;
pub const FS_OP_POW: u8 = 0x06;
pub const FS_KIND_SCALAR: u8 = 0x01;
pub const FS_KIND_SLICE: u8 = 0x02;
pub const FS_KIND_WIDE_SCALAR: u8 = 0x03;
pub const FS_KIND_WIDE_SLICE: u8 = 0x04;

#[inline]
fn f128_of_u128(v: u128) -> F128 {
    F128 {
        lo: v as u64,
        hi: (v >> 64) as u64,
    }
}

#[inline]
fn u128_of_f128(v: F128) -> u128 {
    (v.lo as u128) | ((v.hi as u128) << 64)
}

/// Canonical op-header lane: `lo = op | kind << 8`, `hi = len`.
#[inline]
pub fn fs_op_lane(op: u8, kind: u8, len: u64) -> F128 {
    F128 {
        lo: op as u64 | ((kind as u64) << 8),
        hi: len,
    }
}

/// Pack a byte string into 16-byte little-endian lanes, zero-padding the
/// last lane. Unambiguous because every op header carries the byte length.
pub fn fs_pack_bytes_lanes(bytes: &[u8]) -> Vec<F128> {
    bytes
        .chunks(16)
        .map(|chunk| {
            let mut buf = [0u8; 16];
            buf[..chunk.len()].copy_from_slice(chunk);
            f128_of_u128(u128::from_le_bytes(buf))
        })
        .collect()
}

/// Capacity IV lanes of a domain tag in the flat basis:
/// `[state[2], state[3]]` as circuit-wire bit patterns.
pub fn capacity_iv_flat_lanes(tag: noid_poseidon2b::native::DomainTag) -> [F128; 2] {
    let [hi, lo] = capacity_iv(tag);
    [
        f128_of_u128(noid_core::hardware::tower_to_flat_u128(hi.0)),
        f128_of_u128(noid_core::hardware::tower_to_flat_u128(lo.0)),
    ]
}

/// Capacity IV (`TAG_LANECHAL`) lanes of the lane-oriented challenger, in
/// the flat basis. Each Fiat-Shamir family gets its own capacity IV so no
/// transcript state is replayable across constructions.
pub fn fs_lane_iv_flat() -> [F128; 2] {
    capacity_iv_flat_lanes(TAG_LANECHAL)
}

/// Capacity IV of the C1 lane challenger in the flat basis.
pub fn fs_c1_lane_iv_flat() -> [F128; 2] {
    capacity_iv_flat_lanes(TAG_LANE256)
}

/// Capacity IV (`TAG_KSCHANNL`) lanes of the killshot channel
/// (`Poseidon2bChannel`), in the flat basis — the seed of its in-trace
/// replay ([`crate::field_circuit::RawChannelTrace`]).
pub fn ks_channel_iv_flat() -> [F128; 2] {
    capacity_iv_flat_lanes(noid_poseidon2b::native::TAG_KSCHANNL)
}

/// The sponge pad block (`0x80 … 0x01` over one lane) in the flat basis.
pub fn fs_pad_lane_flat() -> F128 {
    let mut bytes = [0u8; 16];
    bytes[0] = 0x80;
    bytes[15] = 0x01;
    let tower = u128::from_le_bytes(bytes);
    f128_of_u128(noid_core::hardware::tower_to_flat_u128(tower))
}

/// Lane-oriented Fiat-Shamir challenger (see module section above).
#[derive(Clone)]
pub struct FsLaneChallenger {
    /// Sponge state in the FLAT basis (bit-identical to circuit wires).
    state: [F128; 4],
    buffered: Option<F128>,
    pending: Option<F128>,
    perms: usize,
    c1: bool,
}

/// Run the production Poseidon2b permutation on a flat-basis state.
fn permute_flat(state: &mut [F128; 4]) {
    use noid_core::Block128;
    use noid_core::hardware::{flat_to_tower_u128, tower_to_flat_u128};
    let mut tower: [Block128; 4] =
        std::array::from_fn(|i| Block128(flat_to_tower_u128(u128_of_f128(state[i]))));
    noid_poseidon2b::native::permutation::Poseidon2bPermutation.permute_mut(&mut tower);
    for i in 0..4 {
        state[i] = f128_of_u128(tower_to_flat_u128(tower[i].0));
    }
}

impl FsLaneChallenger {
    pub fn new(domain: &[u8]) -> Self {
        Self::with_profile(domain, fs_lane_iv_flat(), false)
    }

    /// C1 lane challenger. Raw F128 operations remain available for query
    /// indices and grinding; algebraic protocol moves use the explicit F256
    /// methods on [`Challenger`].
    pub fn new_c1(domain: &[u8]) -> Self {
        Self::with_profile(domain, fs_c1_lane_iv_flat(), true)
    }

    fn with_profile(domain: &[u8], [iv0, iv1]: [F128; 2], c1: bool) -> Self {
        let mut c = Self {
            state: [F128::ZERO, F128::ZERO, iv0, iv1],
            buffered: None,
            pending: None,
            perms: 0,
            c1,
        };
        c.absorb_lane(fs_op_lane(FS_OP_DOMAIN, 0, domain.len() as u64));
        for lane in fs_pack_bytes_lanes(domain) {
            c.absorb_lane(lane);
        }
        c
    }

    /// Permutations executed so far (lockstep pin for the trace gadget).
    pub fn perms(&self) -> usize {
        self.perms
    }

    /// Current flat-basis sponge state, excluding the at-most-one buffered
    /// absorb lane.  Recorded recursive channels finish at a transcript
    /// boundary; exposing the state lets a layout-checked recording wrapper
    /// prove that its native verifier pass and the later trace pass ended in
    /// exact lockstep without replaying the verifier on a scratch builder.
    pub fn post_state(&self) -> [F128; 4] {
        self.state
    }

    fn permute(&mut self) {
        permute_flat(&mut self.state);
        self.perms += 1;
    }

    fn absorb_lane(&mut self, lane: F128) {
        self.pending = None;
        if let Some(first) = self.buffered.take() {
            self.state[0] += first;
            self.state[1] += lane;
            self.permute();
        } else {
            self.buffered = Some(lane);
        }
    }

    fn flush(&mut self) {
        if let Some(first) = self.buffered.take() {
            self.state[0] += first;
            self.state[1] += fs_pad_lane_flat();
            self.permute();
        }
    }

    fn squeeze_lane(&mut self) -> F128 {
        if let Some(p) = self.pending.take() {
            return p;
        }
        self.flush();
        let out = self.state[0];
        self.pending = Some(self.state[1]);
        self.permute();
        out
    }

    /// Canonical C1 scalar draw together with the two raw sponge lanes that
    /// determine it. The raw lanes are exposed within this crate so the
    /// recursive duplex recorder can bind the actual sponge outputs before
    /// applying the trace-one map.
    pub(crate) fn sample_f256_with_raw(&mut self) -> (F256, [F128; 2]) {
        assert!(
            self.c1,
            "wide transcript operation requires FsLaneChallenger::new_c1"
        );
        #[cfg(feature = "hash-count")]
        fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.absorb_lane(fs_op_lane(FS_OP_SQUEEZE, FS_KIND_WIDE_SCALAR, 0));
        let raw = [self.squeeze_lane(), self.squeeze_lane()];
        (F256::from_raw_challenge_lanes(raw[0], raw[1]), raw)
    }

    /// Canonical C1 vector draw plus the raw sponge-lane pairs, with one
    /// vector frame for the whole draw.
    pub(crate) fn sample_f256_vec_with_raw(&mut self, n: usize) -> Vec<(F256, [F128; 2])> {
        assert!(
            self.c1,
            "wide transcript operation requires FsLaneChallenger::new_c1"
        );
        #[cfg(feature = "hash-count")]
        fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.absorb_lane(fs_op_lane(FS_OP_SQUEEZE, FS_KIND_WIDE_SLICE, n as u64));
        (0..n)
            .map(|_| {
                let raw = [self.squeeze_lane(), self.squeeze_lane()];
                (F256::from_raw_challenge_lanes(raw[0], raw[1]), raw)
            })
            .collect()
    }

    /// PoW predicate under the GRIND-BY-SQUEEZE rule: absorb the
    /// `[FS_OP_POW header, nonce]` pair with the ORDINARY lane discipline
    /// (a buffered lane pairs with the header), then run `sample_f128`
    /// (squeeze header absorb + pad flush) and require the squeezed lane's
    /// top `bits` flat bits to be zero. The pow rides the TRANSCRIPT
    /// sponge itself — no separate PoW instance, no flush, no
    /// mid-transcript state peek — so it is expressible entirely in
    /// transcript ops: the in-trace mirror is an observe + sample + bit
    /// pin, and a walk-C recording carries it as plain schedule lanes.
    /// Two to three permutations per trial.
    fn pow_ok(state: &[F128; 4], buffered: Option<F128>, nonce: u64, bits: u32) -> bool {
        debug_assert!(bits <= 64);
        let mut s = *state;
        let mut buf = buffered;
        let lanes = [
            fs_op_lane(FS_OP_POW, 0, bits as u64),
            F128 { lo: nonce, hi: 0 },
            fs_op_lane(FS_OP_SQUEEZE, FS_KIND_SCALAR, 0),
        ];
        for lane in lanes {
            if let Some(first) = buf.take() {
                s[0] += first;
                s[1] += lane;
                permute_flat(&mut s);
            } else {
                buf = Some(lane);
            }
        }
        // squeeze_lane: pad-flush the odd lane, read lane 0.
        if let Some(first) = buf.take() {
            s[0] += first;
            s[1] += fs_pad_lane_flat();
            permute_flat(&mut s);
        }
        bits == 0 || (s[0].hi >> (64 - bits)) == 0
    }
}

impl Challenger for FsLaneChallenger {
    fn observe_label(&mut self, label: &[u8]) {
        self.absorb_lane(fs_op_lane(FS_OP_LABEL, 0, label.len() as u64));
        for lane in fs_pack_bytes_lanes(label) {
            self.absorb_lane(lane);
        }
    }

    fn observe_f128(&mut self, value: F128) {
        self.absorb_lane(fs_op_lane(FS_OP_OBSERVE, FS_KIND_SCALAR, 0));
        self.absorb_lane(value);
    }

    fn observe_f128_slice(&mut self, values: &[F128]) {
        self.absorb_lane(fs_op_lane(
            FS_OP_OBSERVE,
            FS_KIND_SLICE,
            values.len() as u64,
        ));
        for v in values {
            self.absorb_lane(*v);
        }
    }

    fn observe_f256(&mut self, value: F256) {
        assert!(
            self.c1,
            "wide transcript operation requires FsLaneChallenger::new_c1"
        );
        self.absorb_lane(fs_op_lane(FS_OP_OBSERVE, FS_KIND_WIDE_SCALAR, 0));
        self.absorb_lane(value.lo);
        self.absorb_lane(value.hi);
    }

    fn observe_f256_slice(&mut self, values: &[F256]) {
        assert!(
            self.c1,
            "wide transcript operation requires FsLaneChallenger::new_c1"
        );
        self.absorb_lane(fs_op_lane(
            FS_OP_OBSERVE,
            FS_KIND_WIDE_SLICE,
            values.len() as u64,
        ));
        for value in values {
            self.absorb_lane(value.lo);
            self.absorb_lane(value.hi);
        }
    }

    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.absorb_lane(fs_op_lane(FS_OP_BYTES, 0, bytes.len() as u64));
        for lane in fs_pack_bytes_lanes(bytes) {
            self.absorb_lane(lane);
        }
    }

    fn sample_f128(&mut self) -> F128 {
        #[cfg(feature = "hash-count")]
        fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.absorb_lane(fs_op_lane(FS_OP_SQUEEZE, FS_KIND_SCALAR, 0));
        self.squeeze_lane()
    }

    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        #[cfg(feature = "hash-count")]
        fs_count::SQUEEZES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.absorb_lane(fs_op_lane(FS_OP_SQUEEZE, FS_KIND_SLICE, n as u64));
        (0..n).map(|_| self.squeeze_lane()).collect()
    }

    fn sample_f256(&mut self) -> F256 {
        self.sample_f256_with_raw().0
    }

    fn sample_f256_vec(&mut self, n: usize) -> Vec<F256> {
        self.sample_f256_vec_with_raw(n)
            .into_iter()
            .map(|(challenge, _)| challenge)
            .collect()
    }

    fn grind_pow(&mut self, bits: u32) -> u64 {
        let snapshot = self.state;
        let buffered = self.buffered;
        // Same parallel-dispatch policy and determinism argument as
        // `FsChallenger::grind_pow`: block-parallel `find_first` returns the
        // globally smallest satisfying nonce, identical to the sequential
        // search; tiny grinds stay serial below the rayon break-even.
        const PARALLEL_GRIND_MIN_HASHES: u64 = 1 << 13;
        let nonce = if bits == 0 {
            0
        } else if (1u64 << bits.min(63)) < PARALLEL_GRIND_MIN_HASHES {
            let mut n = 0u64;
            loop {
                if Self::pow_ok(&snapshot, buffered, n, bits) {
                    break n;
                }
                n = n.wrapping_add(1);
            }
        } else {
            use rayon::prelude::*;
            let block: u64 = 1 << (bits.min(24) + 1);
            let mut start: u64 = 0;
            loop {
                if let Some(n) = (start..start.saturating_add(block))
                    .into_par_iter()
                    .find_first(|&n| Self::pow_ok(&snapshot, buffered, n, bits))
                {
                    break n;
                }
                start = start.saturating_add(block);
            }
        };
        // Replay the winning trial on the live transcript: absorb the pow
        // header + nonce, then the scalar squeeze whose output carried the
        // zeros. Subsequent challenges bind to the nonce through it.
        self.absorb_lane(fs_op_lane(FS_OP_POW, 0, bits as u64));
        self.absorb_lane(F128 { lo: nonce, hi: 0 });
        let _pt = self.sample_f128();
        nonce
    }

    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        self.absorb_lane(fs_op_lane(FS_OP_POW, 0, bits as u64));
        self.absorb_lane(F128 { lo: nonce, hi: 0 });
        let pt = self.sample_f128();
        if bits == 0 {
            // Canonical zero nonce at zero-bit sites (same non-malleability
            // rule as FsChallenger).
            nonce == 0
        } else {
            (pt.hi >> (64 - bits)) == 0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Prover-side PoW grinding produces a nonce that the verifier-side
    /// `verify_pow` accepts at the same transcript position. State binding
    /// is preserved — sampling after PoW gives identical challenges on both
    /// sides.
    #[test]
    fn fs_challenger_pow_roundtrip() {
        for bits in [0u32, 5, 10, 14] {
            let mut prover = FsChallenger::new(b"pow-test");
            prover.observe_label(b"history-pow-test");
            prover.observe_bytes(b"some root data");
            let nonce = prover.grind_pow(bits);

            let mut verifier = FsChallenger::new(b"pow-test");
            verifier.observe_label(b"history-pow-test");
            verifier.observe_bytes(b"some root data");
            assert!(
                verifier.verify_pow(nonce, bits),
                "verify failed at bits={bits}"
            );

            // Subsequent challenges must agree.
            for _ in 0..4 {
                assert_eq!(prover.sample_f128(), verifier.sample_f128());
            }
        }
    }

    /// `verify_pow` rejects a wrong nonce when grinding bits > 0.
    #[test]
    fn fs_challenger_pow_rejects_wrong_nonce() {
        let mut prover = FsChallenger::new(b"pow-test");
        prover.observe_bytes(b"root");
        let nonce = prover.grind_pow(10);
        let bad_nonce = nonce.wrapping_add(1);

        let mut verifier = FsChallenger::new(b"pow-test");
        verifier.observe_bytes(b"root");
        assert!(
            !verifier.verify_pow(bad_nonce, 10),
            "should reject wrong nonce"
        );
    }

    /// At a zero-bit grinding site `verify_pow` accepts the canonical nonce 0
    /// (what `grind_pow(0)` emits) but rejects any non-zero nonce, so a proof
    /// can't be made malleable by swapping in an arbitrary nonce.
    #[test]
    fn fs_challenger_pow_zero_bits_requires_canonical_nonce() {
        let mk = || {
            let mut ch = FsChallenger::new(b"pow-test");
            ch.observe_bytes(b"root");
            ch
        };
        assert_eq!(mk().grind_pow(0), 0, "honest zero-bit grind is the 0 nonce");
        assert!(mk().verify_pow(0, 0), "canonical 0 nonce must verify");
        for bad in [1u64, 42, u64::MAX] {
            assert!(
                !mk().verify_pow(bad, 0),
                "non-zero nonce {bad} must be rejected at zero-bit grinding"
            );
        }
    }

    /// Default Challenger impl (RandomChallenger) is a no-op for PoW.
    #[test]
    fn random_challenger_pow_is_noop() {
        let mut ch = RandomChallenger::new(0);
        assert_eq!(ch.grind_pow(16), 0);
        assert!(ch.verify_pow(0, 16));
    }

    #[test]
    fn random_challenger_is_deterministic_per_seed() {
        let mut c1 = RandomChallenger::new(42);
        let mut c2 = RandomChallenger::new(42);
        for _ in 0..16 {
            assert_eq!(c1.sample_f128(), c2.sample_f128());
        }
    }

    #[test]
    fn random_challenger_observe_is_noop() {
        // Observing arbitrary messages does not change the sampled values.
        let mut c1 = RandomChallenger::new(7);
        let mut c2 = RandomChallenger::new(7);
        c2.observe_f128(F128 {
            lo: 0xDEADBEEF,
            hi: 0xCAFEBABE,
        });
        c2.observe_f128_slice(&[F128::ONE, F128::ZERO]);
        c2.observe_label(b"ignored");
        c2.observe_bytes(b"also ignored");
        for _ in 0..8 {
            assert_eq!(c1.sample_f128(), c2.sample_f128());
        }
    }

    #[test]
    fn sample_f128_vec_matches_individual_samples() {
        let mut c1 = RandomChallenger::new(99);
        let mut c2 = RandomChallenger::new(99);
        let batch = c1.sample_f128_vec(5);
        let individual: Vec<F128> = (0..5).map(|_| c2.sample_f128()).collect();
        assert_eq!(batch, individual);
    }

    // ---- FsChallenger ------------------------------------------------------

    #[test]
    fn fs_challenger_identical_scripts_produce_identical_output() {
        let mut c1 = FsChallenger::new(b"history-test");
        let mut c2 = FsChallenger::new(b"history-test");
        let msg = F128 {
            lo: 0x1234,
            hi: 0x5678,
        };
        c1.observe_f128(msg);
        c2.observe_f128(msg);
        let r1 = c1.sample_f128_vec(8);
        let r2 = c2.sample_f128_vec(8);
        assert_eq!(r1, r2);
    }

    #[test]
    fn fs_challenger_different_domains_diverge() {
        let mut c1 = FsChallenger::new(b"history-a");
        let mut c2 = FsChallenger::new(b"history-b");
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }

    #[test]
    fn fs_challenger_different_observations_diverge() {
        let mut c1 = FsChallenger::new(b"history");
        let mut c2 = FsChallenger::new(b"history");
        c1.observe_f128(F128::ONE);
        c2.observe_f128(F128::ZERO);
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }

    #[test]
    fn fs_challenger_label_changes_output() {
        let mut c1 = FsChallenger::new(b"history");
        let mut c2 = FsChallenger::new(b"history");
        c1.observe_label(b"phase-A");
        // c2 omits the label entirely.
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }

    #[test]
    fn fs_challenger_scalar_vs_slice_dont_collide() {
        // observe_f128_slice(&[v]) must NOT produce the same state as
        // observe_f128(v) — the length prefix and kind tag must defeat this.
        let v = F128 { lo: 0xAB, hi: 0xCD };
        let mut c1 = FsChallenger::new(b"history");
        let mut c2 = FsChallenger::new(b"history");
        c1.observe_f128(v);
        c2.observe_f128_slice(&[v]);
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }

    #[test]
    fn fs_challenger_two_scalars_dont_collide_with_one_slice_of_two() {
        let a = F128 { lo: 1, hi: 2 };
        let b = F128 { lo: 3, hi: 4 };
        let mut c1 = FsChallenger::new(b"history");
        let mut c2 = FsChallenger::new(b"history");
        c1.observe_f128(a);
        c1.observe_f128(b);
        c2.observe_f128_slice(&[a, b]);
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }

    #[test]
    fn fs_challenger_sample_one_vs_sample_vec_one_differ() {
        // Squeeze tag differs (KIND_SCALAR vs KIND_SLICE+len), so a single
        // sample_f128 must not equal sample_f128_vec(1)[0].
        let mut c1 = FsChallenger::new(b"history");
        let mut c2 = FsChallenger::new(b"history");
        assert_ne!(c1.sample_f128(), c2.sample_f128_vec(1)[0]);
    }

    #[test]
    fn fs_challenger_sample_advances_state() {
        // After a sample, the next observation should not collapse to the
        // pre-sample state (the squeezed bytes are re-absorbed).
        let mut c1 = FsChallenger::new(b"history");
        let mut c2 = FsChallenger::new(b"history");
        let _ = c1.sample_f128();
        // c2 skips the sample.
        c1.observe_f128(F128::ONE);
        c2.observe_f128(F128::ONE);
        assert_ne!(c1.sample_f128(), c2.sample_f128());
    }

    #[test]
    fn c1_byte_challenger_wide_roundtrip_and_subfield_exclusion() {
        let message = F256::new(F128::new(1, 2), F128::new(3, 4));
        let mut prover = FsChallenger::new_c1(b"history-c1");
        let mut verifier = FsChallenger::new_c1(b"history-c1");
        prover.observe_f256(message);
        verifier.observe_f256(message);
        for _ in 0..8 {
            let p = prover.sample_f256();
            let v = verifier.sample_f256();
            assert_eq!(p, v);
            assert!(!p.is_in_base_subfield());
        }
        assert_eq!(prover.sample_f128_vec(4), verifier.sample_f128_vec(4));
    }

    #[test]
    fn c1_lane_challenger_wide_roundtrip_and_subfield_exclusion() {
        let messages = [
            F256::new(F128::new(5, 6), F128::new(7, 8)),
            F256::new(F128::new(9, 10), F128::new(11, 12)),
        ];
        let mut prover = FsLaneChallenger::new_c1(b"history-c1");
        let mut verifier = FsLaneChallenger::new_c1(b"history-c1");
        prover.observe_f256_slice(&messages);
        verifier.observe_f256_slice(&messages);
        let p = prover.sample_f256_vec(9);
        let v = verifier.sample_f256_vec(9);
        assert_eq!(p, v);
        assert!(p.iter().all(|challenge| !challenge.is_in_base_subfield()));
        assert_eq!(prover.sample_f128_vec(23), verifier.sample_f128_vec(23));
        assert_eq!(prover.perms(), verifier.perms());
        assert_eq!(prover.post_state(), verifier.post_state());
    }

    #[test]
    fn c1_wide_scalar_and_slice_frames_are_distinct() {
        let value = F256::new(F128::new(13, 14), F128::new(15, 16));
        let mut scalar = FsLaneChallenger::new_c1(b"history-c1");
        let mut slice = FsLaneChallenger::new_c1(b"history-c1");
        scalar.observe_f256(value);
        slice.observe_f256_slice(&[value]);
        assert_ne!(scalar.sample_f256(), slice.sample_f256());

        let mut one = FsLaneChallenger::new_c1(b"history-c1");
        let mut vector = FsLaneChallenger::new_c1(b"history-c1");
        assert_ne!(one.sample_f256(), vector.sample_f256_vec(1)[0]);
    }

    #[test]
    fn c1_capacity_domain_is_distinct_from_legacy_lane_channel() {
        let mut legacy = FsLaneChallenger::new(b"same-inner-domain");
        let mut c1 = FsLaneChallenger::new_c1(b"same-inner-domain");
        assert_ne!(legacy.sample_f128(), c1.sample_f128());
    }

    #[test]
    #[should_panic(expected = "requires FsLaneChallenger::new_c1")]
    fn legacy_lane_channel_rejects_wide_operations() {
        let mut legacy = FsLaneChallenger::new(b"legacy");
        let _ = legacy.sample_f256();
    }
}
