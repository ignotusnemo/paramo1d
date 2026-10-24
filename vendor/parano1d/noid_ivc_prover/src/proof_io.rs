//! Minimal serialization for IVC R1CS proof bundles.
//!
//! The production recursive path only needs to carry a witness commitment plus
//! the R1CS proof. Comparator/hash-chain bundles belonged to the old laboratory
//! harness and are intentionally absent here.

use serde::{Deserialize, Serialize};

use noid_ivc_core::pcs::Commitment;
use noid_ivc_core::proof::R1csProof;

pub const MAGIC: [u8; 5] = *b"NOIDI";

const HEADER_LEN: usize = MAGIC.len();

#[derive(Debug)]
pub enum DeserializeError {
    BadMagic,
    Truncated,
    Bincode(bincode::Error),
}

impl std::fmt::Display for DeserializeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BadMagic => write!(f, "bad magic: not a NOIDI IVC proof bundle"),
            Self::Truncated => write!(f, "IVC proof bundle shorter than header"),
            Self::Bincode(error) => write!(f, "IVC proof bundle bincode error: {error}"),
        }
    }
}

impl std::error::Error for DeserializeError {}

impl From<bincode::Error> for DeserializeError {
    fn from(error: bincode::Error) -> Self {
        Self::Bincode(error)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct R1csProofBundle {
    pub commitment: Commitment,
    pub proof: R1csProof,
}

impl R1csProofBundle {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(HEADER_LEN + 1024);
        out.extend_from_slice(&MAGIC);
        bincode::serialize_into(&mut out, self).expect("R1csProofBundle serializes");
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DeserializeError> {
        let payload = parse_header(bytes)?;
        Ok(bincode::deserialize(payload)?)
    }
}

fn parse_header(bytes: &[u8]) -> Result<&[u8], DeserializeError> {
    if bytes.len() < HEADER_LEN {
        return Err(DeserializeError::Truncated);
    }
    if bytes[..HEADER_LEN] != MAGIC {
        return Err(DeserializeError::BadMagic);
    }
    Ok(&bytes[HEADER_LEN..])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_truncated() {
        assert!(matches!(
            R1csProofBundle::from_bytes(&[0u8; 3]),
            Err(DeserializeError::Truncated)
        ));
    }

    #[test]
    fn rejects_bad_magic() {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(b"NOIDH");
        assert!(matches!(
            R1csProofBundle::from_bytes(&bytes),
            Err(DeserializeError::BadMagic)
        ));
    }
}
