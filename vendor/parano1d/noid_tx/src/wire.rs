// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Exact canonical wire encoding for Tx8x2.

use noid_poseidon2b::primitives::{Address, Digest};

use crate::{Transaction, TxBody, TxInput, TxOutput, TX_INPUTS, TX_OUTPUTS};

pub const TX_INPUT_WIRE_SIZE: usize = 4 + 8 + 8;
pub const TX_OUTPUT_WIRE_SIZE: usize = 4 + 8 + 32;
pub const TX_BODY_WIRE_SIZE: usize =
    32 + 8 + 32 + TX_INPUTS * TX_INPUT_WIRE_SIZE + TX_OUTPUTS * TX_OUTPUT_WIRE_SIZE + 2 + 1;
pub const TRANSACTION_WIRE_SIZE: usize = TX_BODY_WIRE_SIZE;

const _: () = assert!(TX_BODY_WIRE_SIZE == 323);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WireError {
    Truncated,
    TrailingBytes,
    InvalidBool,
    BadMarker,
    NonCanonicalBody,
    LengthOverflow,
}

#[inline]
fn put_u16(buf: &mut Vec<u8>, value: u16) {
    buf.extend_from_slice(&value.to_le_bytes());
}

#[inline]
fn put_u32(buf: &mut Vec<u8>, value: u32) {
    buf.extend_from_slice(&value.to_le_bytes());
}

#[inline]
fn put_u64(buf: &mut Vec<u8>, value: u64) {
    buf.extend_from_slice(&value.to_le_bytes());
}

#[inline]
fn take<'a>(src: &mut &'a [u8], len: usize) -> Result<&'a [u8], WireError> {
    if src.len() < len {
        return Err(WireError::Truncated);
    }
    let (head, tail) = src.split_at(len);
    *src = tail;
    Ok(head)
}

#[inline]
fn take_u16(src: &mut &[u8]) -> Result<u16, WireError> {
    Ok(u16::from_le_bytes(take(src, 2)?.try_into().unwrap()))
}

#[inline]
fn take_u32(src: &mut &[u8]) -> Result<u32, WireError> {
    Ok(u32::from_le_bytes(take(src, 4)?.try_into().unwrap()))
}

#[inline]
fn take_u64(src: &mut &[u8]) -> Result<u64, WireError> {
    Ok(u64::from_le_bytes(take(src, 8)?.try_into().unwrap()))
}

#[inline]
fn take_digest(src: &mut &[u8]) -> Result<Digest, WireError> {
    Ok(take(src, 32)?.try_into().unwrap())
}

#[inline]
fn take_bool(src: &mut &[u8]) -> Result<bool, WireError> {
    match *take(src, 1)?.first().unwrap() {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(WireError::InvalidBool),
    }
}

impl TxInput {
    pub fn encode(&self, buf: &mut Vec<u8>) {
        put_u32(buf, self.slot_index);
        put_u64(buf, self.amount);
        put_u64(buf, self.creation_id);
    }

    pub fn decode(src: &mut &[u8]) -> Result<Self, WireError> {
        Ok(Self {
            slot_index: take_u32(src)?,
            amount: take_u64(src)?,
            creation_id: take_u64(src)?,
        })
    }
}

impl TxOutput {
    pub fn encode(&self, buf: &mut Vec<u8>) {
        put_u32(buf, self.slot_index);
        put_u64(buf, self.amount);
        buf.extend_from_slice(&self.owner.0);
    }

    pub fn decode(src: &mut &[u8]) -> Result<Self, WireError> {
        Ok(Self {
            slot_index: take_u32(src)?,
            amount: take_u64(src)?,
            owner: Address(take_digest(src)?),
        })
    }
}

impl TxBody {
    pub fn encode(&self, buf: &mut Vec<u8>) {
        assert!(
            self.validate_canonical().is_ok(),
            "cannot encode non-canonical Tx8x2 body"
        );
        buf.extend_from_slice(&self.epoch_anchor);
        put_u64(buf, self.fee);
        buf.extend_from_slice(&self.input_owner.0);
        for input in &self.inputs {
            input.encode(buf);
        }
        for output in &self.outputs {
            output.encode(buf);
        }
        put_u16(buf, self.validity_bitmap);
        buf.push(self.is_coinbase as u8);
    }

    pub fn to_bytes(&self) -> [u8; TX_BODY_WIRE_SIZE] {
        let mut bytes = Vec::with_capacity(TX_BODY_WIRE_SIZE);
        self.encode(&mut bytes);
        bytes.try_into().expect("Tx8x2 encoder has fixed length")
    }

    pub fn decode(src: &mut &[u8]) -> Result<Self, WireError> {
        let epoch_anchor = take_digest(src)?;
        let fee = take_u64(src)?;
        let input_owner = Address(take_digest(src)?);
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        for input in &mut inputs {
            *input = TxInput::decode(src)?;
        }
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        for output in &mut outputs {
            *output = TxOutput::decode(src)?;
        }
        let body = Self {
            epoch_anchor,
            fee,
            input_owner,
            inputs,
            outputs,
            validity_bitmap: take_u16(src)?,
            is_coinbase: take_bool(src)?,
        };
        body.validate_canonical()
            .map_err(|_| WireError::NonCanonicalBody)?;
        Ok(body)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, WireError> {
        let mut src = bytes;
        let body = Self::decode(&mut src)?;
        if !src.is_empty() {
            return Err(WireError::TrailingBytes);
        }
        Ok(body)
    }
}

impl Transaction {
    #[inline]
    pub fn encode(&self, buf: &mut Vec<u8>) {
        self.body.encode(buf);
    }

    #[inline]
    pub fn to_bytes(&self) -> [u8; TRANSACTION_WIRE_SIZE] {
        self.body.to_bytes()
    }

    #[inline]
    pub fn decode(src: &mut &[u8]) -> Result<Self, WireError> {
        Ok(Self::new(TxBody::decode(src)?))
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, WireError> {
        let mut src = bytes;
        let tx = Self::decode(&mut src)?;
        if !src.is_empty() {
            return Err(WireError::TrailingBytes);
        }
        Ok(tx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{output_bitmap_bit, TX_VALIDITY_MASK};

    fn body() -> TxBody {
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        inputs[0] = TxInput {
            slot_index: 7,
            amount: 12,
            creation_id: 3,
        };
        inputs[7] = TxInput {
            slot_index: 8,
            amount: 9,
            creation_id: 4,
        };
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[1] = TxOutput {
            slot_index: 10,
            amount: 20,
            owner: Address([0x22; 32]),
        };
        TxBody {
            epoch_anchor: [0x11; 32],
            fee: 1,
            input_owner: Address([0x33; 32]),
            inputs,
            outputs,
            validity_bitmap: (1 << 0) | (1 << 7) | output_bitmap_bit(1),
            is_coinbase: false,
        }
    }

    #[test]
    fn exact_323_byte_roundtrip_and_offsets() {
        let body = body();
        let bytes = body.to_bytes();
        assert_eq!(bytes.len(), 323);
        assert_eq!(&bytes[0..32], &body.epoch_anchor);
        assert_eq!(&bytes[32..40], &body.fee.to_le_bytes());
        assert_eq!(&bytes[40..72], &body.input_owner.0);
        assert_eq!(
            u16::from_le_bytes(bytes[320..322].try_into().unwrap()),
            body.validity_bitmap
        );
        assert_eq!(bytes[322], 0);
        assert_eq!(TxBody::from_bytes(&bytes), Ok(body.clone()));
        assert_eq!(Transaction::from_bytes(&bytes), Ok(Transaction::new(body)));
    }

    #[test]
    fn every_truncation_and_append_rejects() {
        let bytes = body().to_bytes();
        for cut in 0..bytes.len() {
            assert_eq!(TxBody::from_bytes(&bytes[..cut]), Err(WireError::Truncated));
        }
        let mut appended = bytes.to_vec();
        appended.push(0);
        assert_eq!(TxBody::from_bytes(&appended), Err(WireError::TrailingBytes));
    }

    #[test]
    fn invalid_bool_and_bitmap_high_bits_reject() {
        let mut bytes = body().to_bytes();
        bytes[322] = 2;
        assert_eq!(TxBody::from_bytes(&bytes), Err(WireError::InvalidBool));

        let mut bytes = body().to_bytes();
        let bad = TX_VALIDITY_MASK | (1 << 10);
        bytes[320..322].copy_from_slice(&bad.to_le_bytes());
        assert_eq!(TxBody::from_bytes(&bytes), Err(WireError::NonCanonicalBody));
    }

    #[test]
    fn dead_nonzero_record_rejects() {
        let mut bytes = body().to_bytes();
        // Input 1 starts at 72 + 20.
        bytes[92] = 1;
        assert_eq!(TxBody::from_bytes(&bytes), Err(WireError::NonCanonicalBody));
    }
}
