// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Typed cryptographic primitives for the transparent UTXO layer.
//!
//! Paranoid is a transparent, Bitcoin-style chain: every UTXO discloses
//! value and owner address on-chain. Authorization is still signatureless
//! — a spend is authorized by an owner proof bound to the canonical
//! transaction statement transcript. All privacy
//! primitives (stealth addresses, view keys, scan tags, commitment
//! blinding, legacy privacy tags) have been removed.
//!
//! Every primitive is a thin wrapper over a Poseidon2b sponge seeded
//! with a capacity IV derived from a domain tag (CRYPTO.md §3). Newtype
//! wrappers prevent cross-domain digest mix-ups at the type level.

use noid_core::Block128;
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use crate::batch::compress_batch_interleaved_into;
use crate::native::compression::Poseidon2bSponge;
use crate::native::domain::{capacity_iv, DomainTag, TAG_ADDRFIX, TAG_COMMIT, TAG_LEAF, TAG_TX8X2};
use crate::native::permutation::Poseidon2bPermutation;
use noid_core::CanonicalSerialize;

/// Generic 32-byte Poseidon2b digest.
pub type Digest = [u8; 32];

macro_rules! newtype_digest {
    ($(#[$m:meta])* $name:ident) => {
        $(#[$m])*
        #[derive(Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
        pub struct $name(pub [u8; 32]);

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}(", stringify!($name))?;
                for byte in &self.0 {
                    write!(f, "{:02x}", byte)?;
                }
                f.write_str(")")
            }
        }

        impl $name {
            #[inline]
            pub const fn as_bytes(&self) -> &[u8; 32] {
                &self.0
            }
            #[inline]
            pub const fn into_bytes(self) -> [u8; 32] {
                self.0
            }
            /// Interpret the 32-byte digest as two little-endian
            /// `Block128` words.
            #[inline]
            pub fn as_fields(&self) -> [Block128; 2] {
                let mut a = [0u8; 16];
                let mut b = [0u8; 16];
                a.copy_from_slice(&self.0[..16]);
                b.copy_from_slice(&self.0[16..]);
                [
                    Block128::from(u128::from_le_bytes(a)),
                    Block128::from(u128::from_le_bytes(b)),
                ]
            }
        }
    };
}

newtype_digest!(
    /// A 256-bit transparent wallet address. Derived from a 256-bit
    /// `spend_secret` via `H_ADDR = Poseidon2b(ADDRESS_, secret)`.
    Address
);

// ---------------------------------------------------------------------------
// Bech32m encoding for Address
// ---------------------------------------------------------------------------

/// Human-readable part for Paranoid bech32m addresses.
/// Produces addresses of the form `o1q...` (~60 chars).
pub const ADDRESS_HRP: &str = "o";

/// Error returned when decoding a bech32m address fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddressError {
    /// String is not a valid bech32m address.
    InvalidFormat,
    /// Bech32m decoded OK but HRP is not `o`.
    WrongHrp(String),
    /// Decoded payload is not exactly 32 bytes.
    WrongLength(usize),
}

impl std::fmt::Display for AddressError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidFormat => write!(f, "invalid address format (expected bech32m o1…)"),
            Self::WrongHrp(h) => write!(f, "wrong address network: got '{h}', expected 'o'"),
            Self::WrongLength(n) => write!(f, "wrong address length: got {n} bytes, expected 32"),
        }
    }
}
impl std::error::Error for AddressError {}

impl Address {
    /// Encode this address as a bech32m string (`o1…`).
    ///
    /// This is the canonical display format. All user-facing output should
    /// call this or use the `Display` impl.
    pub fn to_bech32(&self) -> String {
        use bech32::{Bech32m, Hrp};
        let hrp = Hrp::parse(ADDRESS_HRP).expect("o is a valid HRP");
        bech32::encode::<Bech32m>(hrp, &self.0).expect("32 bytes always encodes")
    }

    /// Decode an address from canonical bech32m (`o1…`).
    pub fn parse(s: &str) -> Result<Self, AddressError> {
        parse_address(s)
    }
}

impl std::str::FromStr for Address {
    type Err = AddressError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_address(s)
    }
}

fn parse_address(s: &str) -> Result<Address, AddressError> {
    let s = s.trim();
    let (hrp, data) = bech32::decode(s).map_err(|_| AddressError::InvalidFormat)?;
    // HRP comparison is case-insensitive (bech32 spec: HRP is lowercased).
    if hrp.as_str().to_ascii_lowercase() != ADDRESS_HRP {
        return Err(AddressError::WrongHrp(hrp.as_str().to_ascii_lowercase()));
    }
    if data.len() != 32 {
        return Err(AddressError::WrongLength(data.len()));
    }
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&data);
    Ok(Address(bytes))
}

/// Display an `Address` as a bech32m string.
/// This means `tracing::info!(addr = %my_addr, …)` and `format!("{}", addr)`
/// both produce the human-readable form automatically.
impl std::fmt::Display for Address {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_bech32())
    }
}

newtype_digest!(
    /// A coin / UTXO leaf digest binding `(value, owner)`. The leaf is
    /// also the payload stored in the on-chain state tree.
    Commitment
);
newtype_digest!(
    /// Canonical transaction-body hash.
    TxBodyHash
);

impl std::fmt::Display for Commitment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for byte in &self.0 {
            write!(f, "{:02x}", byte)?;
        }
        Ok(())
    }
}

impl std::fmt::Display for TxBodyHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for byte in &self.0 {
            write!(f, "{:02x}", byte)?;
        }
        Ok(())
    }
}

/// The 256-bit wallet spend secret. Preimage of `Address`. It is derived from
/// the wallet master secret and never serialized by transaction code. The
/// current daemon keystore stores its master secret in plaintext behind
/// owner-only filesystem permissions; it does not claim encryption at rest.
///
/// SECURITY: the byte field is private and this type is neither `Copy`,
/// `Clone`, comparable, hashable, nor serializable. This prevents the common
/// accidental copies and public-container insertion paths. Its explicit
/// `Debug` implementation is redacted. Use [`derive_address`] to derive the
/// public address without exposing the raw bytes.
///
/// ```compile_fail
/// use noid_poseidon2b::primitives::SpendSecret;
/// fn require_copy<T: Copy>() {}
/// require_copy::<SpendSecret>();
/// ```
///
/// ```compile_fail
/// use noid_poseidon2b::primitives::SpendSecret;
/// fn require_clone<T: Clone>() {}
/// require_clone::<SpendSecret>();
/// ```
///
/// ```compile_fail
/// use noid_poseidon2b::primitives::SpendSecret;
/// fn require_serialize<T: serde::Serialize>() {}
/// require_serialize::<SpendSecret>();
/// ```
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct SpendSecret([u8; 32]);

impl SpendSecret {
    /// Import 32 bytes into the zeroizing secret owner.
    ///
    /// There is deliberately no inverse raw-byte accessor. Callers importing
    /// a secret already own the source bytes and remain responsible for
    /// clearing that source after this constructor returns.
    #[inline]
    pub const fn from_bytes(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    #[inline]
    fn prover_fields(&self) -> Zeroizing<[Block128; 2]> {
        let mut a = [0u8; 16];
        let mut b = [0u8; 16];
        a.copy_from_slice(&self.0[..16]);
        b.copy_from_slice(&self.0[16..]);
        let fields = Zeroizing::new([
            Block128::from(u128::from_le_bytes(a)),
            Block128::from(u128::from_le_bytes(b)),
        ]);
        a.zeroize();
        b.zeroize();
        fields
    }

    /// Run one prover-side operation with the two secret field limbs.
    ///
    /// This is the sole intentional cross-crate exposure seam. It does not
    /// return raw bytes or a reusable field owner: the temporary limbs are
    /// zeroized immediately after the closure returns. The closure must not
    /// copy, log, serialize, or persist either limb.
    #[doc(hidden)]
    #[inline]
    pub fn with_exposed_prover_fields<R>(&self, use_fields: impl FnOnce(&[Block128; 2]) -> R) -> R {
        let fields = self.prover_fields();
        use_fields(&fields)
    }
}

/// Redacted Debug: never print the raw secret bytes.
impl std::fmt::Debug for SpendSecret {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("SpendSecret([REDACTED])")
    }
}

#[inline]
fn sponge(tag: DomainTag) -> Poseidon2bSponge {
    Poseidon2bSponge::with_iv(capacity_iv(tag))
}

#[inline]
fn absorb_fields(s: &mut Poseidon2bSponge, fields: &[Block128]) {
    let mut iter = fields.chunks_exact(2);
    for pair in iter.by_ref() {
        s.absorb_pair(pair[0], pair[1]);
    }
    for rem in iter.remainder() {
        s.absorb(*rem);
    }
}

/// Hash a list of field elements as a Merkle-tree leaf payload.
/// Sponge-mode, capacity IV = `LEAF____`.
pub fn hash_leaf(fields: &[Block128]) -> Digest {
    let mut s = sponge(TAG_LEAF);
    absorb_fields(&mut s, fields);
    s.finalize()
}

/// Transparent UTXO leaf. Binds `(value, owner)` with IV `COMMIT__`.
/// Three field inputs: `value` (little-endian u128) and the two 128-bit
/// halves of the 256-bit owner address.
pub fn hash_utxo_leaf(value: u128, owner: &Address) -> Commitment {
    let [owner_hi, owner_lo] = owner.as_fields();
    let mut s = sponge(TAG_COMMIT);
    s.absorb(Block128::from(value));
    s.absorb(owner_hi);
    s.absorb(owner_lo);
    Commitment(s.finalize())
}

/// Derive a transparent address from a 256-bit spend secret.
/// `H_ADDR = Poseidon2b_fixed(ADDRFIX_, secret_hi, secret_lo)`.
pub fn derive_address(secret: &SpendSecret) -> Address {
    let mut s = sponge(TAG_ADDRFIX);
    let fields = secret.prover_fields();
    s.absorb_pair(fields[0], fields[1]);
    Address(s.finalize_no_pad())
}

/// Number of raw two-field leaves in the sole Tx8x2 body construction.
pub const TX8X2_LEAF_COUNT: usize = 16;
pub const TX8X2_TREE_DEPTH: usize = 4;

#[inline]
fn fields_to_digest(fields: [Block128; 2]) -> Digest {
    let mut out = [0u8; 32];
    out[..16].copy_from_slice(&fields[0].to_bytes());
    out[16..].copy_from_slice(&fields[1].to_bytes());
    out
}

#[inline]
fn tx8x2_wrap(root: Digest) -> TxBodyHash {
    let r0 = Block128::from(u128::from_le_bytes(root[..16].try_into().unwrap()));
    let r1 = Block128::from(u128::from_le_bytes(root[16..].try_into().unwrap()));
    let [iv_hi, iv_lo] = capacity_iv(TAG_TX8X2);
    let mut state = [r0, r1, iv_hi, iv_lo];
    Poseidon2bPermutation.permute_mut(&mut state);
    let mut out = [0u8; 32];
    out[..16].copy_from_slice(&state[0].to_bytes());
    out[16..].copy_from_slice(&state[1].to_bytes());
    TxBodyHash(out)
}

/// Hash the canonical sixteen raw Tx8x2 leaves.
///
/// The leaves are reduced by fifteen canonical two-permutation `COMPRESS`
/// nodes, then wrapped by one permutation under `TAG_TX8X2`: exactly 31
/// Poseidon2b permutations in total. This function deliberately knows only
/// the fixed leaf array; `noid_tx` owns the field-to-leaf mapping.
pub fn hash_tx8x2_leaves(leaves: &[[Block128; 2]; TX8X2_LEAF_COUNT]) -> TxBodyHash {
    let mut level: Vec<Digest> = leaves.iter().copied().map(fields_to_digest).collect();
    for _ in 0..TX8X2_TREE_DEPTH {
        let mut next = vec![[0u8; 32]; level.len() / 2];
        compress_batch_interleaved_into(&level, &mut next);
        level = next;
    }
    debug_assert_eq!(level.len(), 1);
    tx8x2_wrap(level[0])
}

#[cfg(test)]
mod tests {
    #![allow(clippy::needless_range_loop)]
    use super::*;

    const SS: SpendSecret = SpendSecret::from_bytes([7u8; 32]);

    #[test]
    fn determinism_all_primitives() {
        let addr = derive_address(&SS);
        assert_eq!(addr, derive_address(&SS));

        let c = hash_utxo_leaf(100, &addr);
        assert_eq!(c, hash_utxo_leaf(100, &addr));
    }

    #[test]
    fn cross_domain_no_collision() {
        let a = Block128::from(1u128);
        let b = Block128::from(2u128);
        let c = Block128::from(3u128);
        let d = Block128::from(4u128);

        let mut leaf = sponge(TAG_LEAF);
        leaf.absorb_pair(a, b);
        leaf.absorb_pair(c, d);
        let d_leaf = leaf.finalize();

        let mut commit = sponge(TAG_COMMIT);
        commit.absorb_pair(a, b);
        commit.absorb_pair(c, d);
        let d_commit = commit.finalize();

        let mut addr = sponge(TAG_ADDRFIX);
        addr.absorb_pair(a, b);
        let d_addr = addr.finalize_no_pad();

        let all = [d_leaf, d_commit, d_addr];
        for i in 0..all.len() {
            for j in (i + 1)..all.len() {
                assert_ne!(all[i], all[j]);
            }
        }
    }

    #[test]
    fn address_changes_per_secret() {
        let s1 = SpendSecret::from_bytes([1u8; 32]);
        let s2 = SpendSecret::from_bytes([2u8; 32]);
        assert_ne!(derive_address(&s1), derive_address(&s2));
    }

    #[test]
    fn spend_secret_traits_and_redaction_are_pinned() {
        static_assertions::assert_not_impl_any!(
            SpendSecret: Copy,
            Clone,
            PartialEq,
            Eq,
            std::hash::Hash,
            serde::Serialize,
            serde::de::DeserializeOwned
        );
        fn assert_zeroize<T: Zeroize + ZeroizeOnDrop>() {}
        assert_zeroize::<SpendSecret>();

        let secret = SpendSecret::from_bytes([0xA7; 32]);
        let rendered = format!("{secret:?}");
        assert_eq!(rendered, "SpendSecret([REDACTED])");
        assert!(!rendered.contains("a7"));
    }

    #[test]
    fn explicit_zeroize_clears_owned_secret_bytes() {
        let mut secret = SpendSecret::from_bytes([0x5C; 32]);
        secret.zeroize();
        assert_eq!(secret.0, [0u8; 32]);
    }

    #[test]
    fn spend_secret_source_has_no_raw_output_surface() {
        let source = include_str!("primitives.rs");
        let secret_section = source
            .split("pub struct SpendSecret")
            .nth(1)
            .expect("SpendSecret declaration")
            .split("#[inline]\nfn sponge")
            .next()
            .expect("SpendSecret implementation section");
        assert!(!secret_section.starts_with("(pub "));
        assert!(!secret_section.contains("pub fn as_bytes"));
        assert!(!secret_section.contains("pub fn into_bytes"));
        assert_eq!(
            secret_section
                .matches("pub fn with_exposed_prover_fields")
                .count(),
            1,
            "the reviewed closure seam is the only prover exposure"
        );
    }

    // -----------------------------------------------------------------------
    // Bech32m address encoding tests
    // -----------------------------------------------------------------------

    #[test]
    fn bech32_roundtrip() {
        let addr = Address([
            0xec, 0x7c, 0x7a, 0x9a, 0x4d, 0xff, 0xf0, 0x2d, 0xf4, 0x27, 0x5b, 0x1d, 0xeb, 0xf5,
            0xd8, 0xfd, 0xc3, 0x36, 0x30, 0x7d, 0x8e, 0x89, 0x51, 0x08, 0xb7, 0x3f, 0x05, 0x99,
            0x23, 0xaf, 0xcd, 0xb2,
        ]);
        let encoded = addr.to_bech32();
        // Must start with o1
        assert!(
            encoded.starts_with("o1"),
            "expected o1 prefix, got {encoded}"
        );
        // Must be exactly 60 chars (1 HRP + 52 data + 6 checksum + separator)
        assert_eq!(
            encoded.len(),
            60,
            "expected 60 chars, got {}",
            encoded.len()
        );
        // Round-trip
        let decoded = Address::parse(&encoded).expect("decode own bech32");
        assert_eq!(decoded, addr, "round-trip failed");
    }

    #[test]
    fn bech32_display_matches_to_bech32() {
        let addr = Address([0xab; 32]);
        assert_eq!(format!("{}", addr), addr.to_bech32());
    }

    #[test]
    fn bech32_case_insensitive() {
        let addr = Address([
            0x52, 0x39, 0x3e, 0x22, 0x79, 0x08, 0xb1, 0xbb, 0x10, 0x3a, 0xa8, 0xd9, 0x28, 0x93,
            0x63, 0x86, 0xc8, 0x7c, 0xd9, 0x4f, 0x94, 0x6f, 0xdd, 0xd6, 0xd0, 0xc8, 0xb9, 0x1f,
            0xe9, 0x34, 0xee, 0x43,
        ]);
        let lower = addr.to_bech32();
        let upper = lower.to_uppercase();
        let from_upper = Address::parse(&upper).expect("uppercase bech32 must parse");
        assert_eq!(from_upper, addr);
    }

    #[test]
    fn hex_address_string_is_rejected() {
        let addr = Address([
            0xde, 0xad, 0xbe, 0xef, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99,
            0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
            0x09, 0x0a, 0x0b, 0x0c,
        ]);
        let hex = hex::encode(addr.0);
        assert!(matches!(
            Address::parse(&hex),
            Err(AddressError::InvalidFormat)
        ));
    }

    #[test]
    fn wrong_hrp_rejected() {
        // Build a valid bech32m but with hrp "btc" instead of "o"
        use bech32::{Bech32m, Hrp};
        let hrp = Hrp::parse("btc").unwrap();
        let fake = bech32::encode::<Bech32m>(hrp, &[0u8; 32]).unwrap();
        assert!(matches!(
            Address::parse(&fake),
            Err(AddressError::WrongHrp(_))
        ));
    }

    #[test]
    fn invalid_format_rejected() {
        assert!(Address::parse("notanaddress").is_err());
        assert!(Address::parse("").is_err());
        assert!(Address::parse("o1").is_err());
        // 62-char hex (too short)
        assert!(Address::parse(&"ab".repeat(31)).is_err());
    }
}
