//! Boolean circuit gadgets for the existing `BlockR1cs` backend.
//!
//! The field laws come from `noid_core`; this module only materializes those
//! laws as Boolean R1CS constraints.

use noid_core::{Block8, Block16, Block32, Block64, Block128, TowerField};
use noid_poseidon2b::native::permutation::{
    F_ROUNDS, MDS_FULL, MDS_PARTIAL, N_ROUNDS, P_ROUNDS, ROUND_CONSTANTS, STATE_SIZE,
};

use crate::r1cs::{BlockR1cs, SparseBinaryMatrix};

pub const CIRCUIT_CONST_ONE: usize = 0;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitError {
    OutOfWires,
    BadWidth,
}

#[derive(Debug, Clone)]
pub struct BinaryR1csBuilder {
    m: usize,
    next_wire: usize,
    witness: Vec<bool>,
    a_rows: Vec<Vec<usize>>,
    b_rows: Vec<Vec<usize>>,
}

impl BinaryR1csBuilder {
    pub fn new(m: usize) -> Self {
        let n = 1usize << m;
        let mut builder = Self {
            m,
            next_wire: 1,
            witness: vec![false; n],
            a_rows: vec![Vec::new(); n],
            b_rows: vec![vec![CIRCUIT_CONST_ONE]; n],
        };
        builder.witness[CIRCUIT_CONST_ONE] = true;
        builder.a_rows[CIRCUIT_CONST_ONE] = vec![CIRCUIT_CONST_ONE];
        builder.b_rows[CIRCUIT_CONST_ONE] = vec![CIRCUIT_CONST_ONE];
        builder
    }

    pub fn used_wires(&self) -> usize {
        self.next_wire
    }

    pub fn witness(&self) -> &[bool] {
        &self.witness
    }

    pub fn alloc_private_bit(&mut self, value: bool) -> Result<usize, CircuitError> {
        let wire = self.alloc_raw(value)?;
        self.a_rows[wire] = vec![wire];
        self.b_rows[wire] = vec![wire];
        Ok(wire)
    }

    pub fn alloc_public_bit(&mut self, value: bool) -> Result<usize, CircuitError> {
        let wire = self.alloc_raw(value)?;
        if value {
            self.a_rows[wire] = vec![CIRCUIT_CONST_ONE];
        } else {
            self.a_rows[wire].clear();
        }
        self.b_rows[wire] = vec![CIRCUIT_CONST_ONE];
        Ok(wire)
    }

    pub fn alloc_block128(&mut self, value: Block128) -> Result<[usize; 128], CircuitError> {
        let raw = value.to_u128();
        let mut bits = [0usize; 128];
        for (bit, wire) in bits.iter_mut().enumerate() {
            *wire = self.alloc_private_bit((raw >> bit) & 1 == 1)?;
        }
        Ok(bits)
    }

    pub fn alloc_public_block128(&mut self, value: Block128) -> Result<[usize; 128], CircuitError> {
        let raw = value.to_u128();
        let mut bits = [0usize; 128];
        for (bit, wire) in bits.iter_mut().enumerate() {
            *wire = self.alloc_public_bit((raw >> bit) & 1 == 1)?;
        }
        Ok(bits)
    }

    pub fn block128_value(&self, bits: &[usize; 128]) -> Block128 {
        let mut raw = 0u128;
        for (bit, &wire) in bits.iter().enumerate() {
            if self.witness[wire] {
                raw |= 1u128 << bit;
            }
        }
        Block128::from(raw)
    }

    pub fn xor_bit(&mut self, left: usize, right: usize) -> Result<usize, CircuitError> {
        self.alloc_linear([left, right], false)
    }

    pub fn and_bit(&mut self, left: usize, right: usize) -> Result<usize, CircuitError> {
        let wire = self.alloc_raw(self.witness[left] & self.witness[right])?;
        self.a_rows[wire] = vec![left];
        self.b_rows[wire] = vec![right];
        Ok(wire)
    }

    pub fn alloc_linear<I>(&mut self, terms: I, constant: bool) -> Result<usize, CircuitError>
    where
        I: IntoIterator<Item = usize>,
    {
        let mut normalized = normalize_terms(terms);
        let value = normalized
            .iter()
            .fold(constant, |acc, &wire| acc ^ self.witness[wire]);
        if constant {
            normalized.push(CIRCUIT_CONST_ONE);
            normalized = normalize_terms(normalized);
        }
        let wire = self.alloc_raw(value)?;
        self.a_rows[wire] = normalized;
        self.b_rows[wire] = vec![CIRCUIT_CONST_ONE];
        Ok(wire)
    }

    pub fn assert_bit_eq_const(&mut self, wire: usize, value: bool) -> Result<(), CircuitError> {
        self.assert_linear_zero([wire], value)
    }

    pub fn assert_bit_eq(&mut self, left: usize, right: usize) -> Result<(), CircuitError> {
        self.assert_linear_zero([left, right], false)
    }

    pub fn assert_linear_zero<I>(&mut self, terms: I, constant: bool) -> Result<(), CircuitError>
    where
        I: IntoIterator<Item = usize>,
    {
        let mut normalized = normalize_terms(terms);
        if constant {
            normalized.push(CIRCUIT_CONST_ONE);
            normalized = normalize_terms(normalized);
        }
        let wire = self.alloc_raw(false)?;
        self.a_rows[wire] = normalized;
        self.b_rows[wire] = vec![CIRCUIT_CONST_ONE];
        Ok(())
    }

    pub fn pin_block128(
        &mut self,
        bits: &[usize; 128],
        expected: Block128,
    ) -> Result<(), CircuitError> {
        let raw = expected.to_u128();
        for (bit, &wire) in bits.iter().enumerate() {
            self.assert_bit_eq_const(wire, (raw >> bit) & 1 == 1)?;
        }
        Ok(())
    }

    pub fn build(self) -> (BlockR1cs, Vec<bool>) {
        let total_m = self.m;
        self.build_with_m(total_m)
    }

    pub fn build_with_m(self, total_m: usize) -> (BlockR1cs, Vec<bool>) {
        assert!(
            total_m >= self.m,
            "total R1CS m must be at least the base block m"
        );
        let n = 1usize << self.m;
        let c_rows = (0..n).map(|wire| vec![wire]).collect::<Vec<_>>();
        let outer = 1usize << (total_m - self.m);
        let mut witness = Vec::with_capacity(1usize << total_m);
        for _ in 0..outer {
            witness.extend_from_slice(&self.witness);
        }
        (
            BlockR1cs {
                m: total_m,
                k_log: self.m,
                k_skip: 6,
                useful_bits: n,
                a_0: SparseBinaryMatrix {
                    num_rows: n,
                    num_cols: n,
                    rows: self.a_rows,
                },
                b_0: SparseBinaryMatrix {
                    num_rows: n,
                    num_cols: n,
                    rows: self.b_rows,
                },
                c_0: SparseBinaryMatrix {
                    num_rows: n,
                    num_cols: n,
                    rows: c_rows,
                },
                const_pin: Some(CIRCUIT_CONST_ONE),
                digest_cache: std::sync::OnceLock::new(),
                csc_cache: std::sync::OnceLock::new(),
            },
            witness,
        )
    }

    fn alloc_raw(&mut self, value: bool) -> Result<usize, CircuitError> {
        if self.next_wire >= self.witness.len() {
            return Err(CircuitError::OutOfWires);
        }
        let wire = self.next_wire;
        self.next_wire += 1;
        self.witness[wire] = value;
        Ok(wire)
    }
}

pub fn xor_field_bits(
    builder: &mut BinaryR1csBuilder,
    left: &[usize],
    right: &[usize],
) -> Result<Vec<usize>, CircuitError> {
    if left.len() != right.len() || !is_supported_width(left.len()) {
        return Err(CircuitError::BadWidth);
    }
    left.iter()
        .zip(right)
        .map(|(&a, &b)| builder.xor_bit(a, b))
        .collect()
}

pub fn xor_block128_bits(
    builder: &mut BinaryR1csBuilder,
    left: &[usize; 128],
    right: &[usize; 128],
) -> Result<[usize; 128], CircuitError> {
    Ok(xor_field_bits(builder, left, right)?
        .try_into()
        .expect("128-bit xor gadget length"))
}

pub fn add_const_block128_bits(
    builder: &mut BinaryR1csBuilder,
    input: &[usize; 128],
    constant: Block128,
) -> Result<[usize; 128], CircuitError> {
    let raw = constant.to_u128();
    let mut out = [0usize; 128];
    for (bit, out_wire) in out.iter_mut().enumerate() {
        *out_wire = builder.alloc_linear([input[bit]], (raw >> bit) & 1 == 1)?;
    }
    Ok(out)
}

pub fn square_field_bits(
    builder: &mut BinaryR1csBuilder,
    width: usize,
    input: &[usize],
) -> Result<Vec<usize>, CircuitError> {
    if input.len() != width || !is_supported_width(width) {
        return Err(CircuitError::BadWidth);
    }
    linear_field_map(builder, width, input, |basis| {
        native_square_width(width, basis)
    })
}

pub fn mul_const_field_bits(
    builder: &mut BinaryR1csBuilder,
    width: usize,
    input: &[usize],
    constant: u128,
) -> Result<Vec<usize>, CircuitError> {
    if input.len() != width || !is_supported_width(width) {
        return Err(CircuitError::BadWidth);
    }
    linear_field_map(builder, width, input, |basis| {
        native_mul_width(width, basis, constant)
    })
}

pub fn mul_const_block128_bits(
    builder: &mut BinaryR1csBuilder,
    input: &[usize; 128],
    constant: Block128,
) -> Result<[usize; 128], CircuitError> {
    Ok(
        mul_const_field_bits(builder, 128, input, constant.to_u128())?
            .try_into()
            .expect("128-bit const mul gadget length"),
    )
}

pub fn mul_field_bits(
    builder: &mut BinaryR1csBuilder,
    width: usize,
    left: &[usize],
    right: &[usize],
) -> Result<Vec<usize>, CircuitError> {
    if left.len() != width || right.len() != width || !is_supported_width(width) {
        return Err(CircuitError::BadWidth);
    }
    if width == 8 {
        return mul_block8_bits(builder, left, right);
    }

    let half = width / 2;
    let (a0, a1) = left.split_at(half);
    let (b0, b1) = right.split_at(half);
    let v0 = mul_field_bits(builder, half, a0, b0)?;
    let v1 = mul_field_bits(builder, half, a1, b1)?;
    let a_sum = xor_field_bits(builder, a0, a1)?;
    let b_sum = xor_field_bits(builder, b0, b1)?;
    let v_sum = mul_field_bits(builder, half, &a_sum, &b_sum)?;
    let v1_tau = mul_const_field_bits(builder, half, &v1, tau_for_extension_width(width))?;
    let lo = xor_field_bits(builder, &v0, &v1_tau)?;
    let hi = xor_field_bits(builder, &v0, &v_sum)?;
    Ok([lo, hi].concat())
}

pub fn mul_block128_bits(
    builder: &mut BinaryR1csBuilder,
    left: &[usize; 128],
    right: &[usize; 128],
) -> Result<[usize; 128], CircuitError> {
    Ok(mul_field_bits(builder, 128, left, right)?
        .try_into()
        .expect("128-bit product gadget length"))
}

pub fn pow7_block128_bits(
    builder: &mut BinaryR1csBuilder,
    input: &[usize; 128],
) -> Result<[usize; 128], CircuitError> {
    let x2 = square_field_bits(builder, 128, input)?;
    let x4 = square_field_bits(builder, 128, &x2)?;
    let x6 = mul_field_bits(builder, 128, input, &x2)?;
    let x7 = mul_field_bits(builder, 128, &x6, &x4)?;
    Ok(x7.try_into().expect("128-bit x^7 gadget length"))
}

pub fn poseidon2b_permute_bits(
    builder: &mut BinaryR1csBuilder,
    state: &mut [[usize; 128]; STATE_SIZE],
) -> Result<(), CircuitError> {
    *state = poseidon2b_mds_bits(builder, state, MDS_FULL)?;
    for round in 0..N_ROUNDS {
        if !(F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&round) {
            for lane in 0..STATE_SIZE {
                state[lane] = add_const_block128_bits(
                    builder,
                    &state[lane],
                    Block128::from(ROUND_CONSTANTS[lane][round]),
                )?;
                state[lane] = pow7_block128_bits(builder, &state[lane])?;
            }
            *state = poseidon2b_mds_bits(builder, state, MDS_FULL)?;
        } else {
            state[0] = add_const_block128_bits(
                builder,
                &state[0],
                Block128::from(ROUND_CONSTANTS[0][round]),
            )?;
            state[0] = pow7_block128_bits(builder, &state[0])?;
            *state = poseidon2b_mds_bits(builder, state, MDS_PARTIAL)?;
        }
    }
    Ok(())
}

pub fn poseidon2b_sponge_fixed_rate2_bits(
    builder: &mut BinaryR1csBuilder,
    fields: &[[usize; 128]],
    capacity: [Block128; 2],
) -> Result<[usize; 256], CircuitError> {
    let zero = builder.alloc_public_block128(Block128::ZERO)?;
    let cap0 = builder.alloc_public_block128(capacity[0])?;
    let cap1 = builder.alloc_public_block128(capacity[1])?;
    let mut state = [zero, zero, cap0, cap1];
    for chunk in fields.chunks(2) {
        state[0] = xor_block128_bits(builder, &state[0], &chunk[0])?;
        if let Some(second) = chunk.get(1) {
            state[1] = xor_block128_bits(builder, &state[1], second)?;
        }
        poseidon2b_permute_bits(builder, &mut state)?;
    }
    let mut out = [0usize; 256];
    out[..128].copy_from_slice(&state[0]);
    out[128..].copy_from_slice(&state[1]);
    Ok(out)
}

fn poseidon2b_mds_bits(
    builder: &mut BinaryR1csBuilder,
    state: &[[usize; 128]; STATE_SIZE],
    mds: [[u128; STATE_SIZE]; STATE_SIZE],
) -> Result<[[usize; 128]; STATE_SIZE], CircuitError> {
    let mut out: [[usize; 128]; STATE_SIZE] = [[0usize; 128]; STATE_SIZE];
    for row in 0..STATE_SIZE {
        let mut terms_by_bit: [Vec<usize>; 128] = std::array::from_fn(|_| Vec::new());
        for (col, lane_bits) in state.iter().enumerate() {
            let coeff = Block128::from(mds[row][col]);
            let product = if coeff == Block128::ONE {
                lane_bits.to_vec()
            } else {
                mul_const_field_bits(builder, 128, lane_bits, coeff.to_u128())?
            };
            for bit in 0..128 {
                terms_by_bit[bit].push(product[bit]);
            }
        }
        for (bit, out_wire) in out[row].iter_mut().enumerate() {
            *out_wire = builder.alloc_linear(terms_by_bit[bit].iter().copied(), false)?;
        }
    }
    Ok(out)
}

fn mul_block8_bits(
    builder: &mut BinaryR1csBuilder,
    left: &[usize],
    right: &[usize],
) -> Result<Vec<usize>, CircuitError> {
    debug_assert_eq!(left.len(), 8);
    debug_assert_eq!(right.len(), 8);
    let mut pair_products = [[0usize; 8]; 8];
    for i in 0..8 {
        for (j, &right_wire) in right.iter().enumerate() {
            pair_products[i][j] = builder.and_bit(left[i], right_wire)?;
        }
    }

    let mut out = Vec::with_capacity(8);
    for bit in 0..8 {
        let mut terms = Vec::new();
        for (i, row) in pair_products.iter().enumerate() {
            for (j, &product_wire) in row.iter().enumerate() {
                let basis_product = native_mul_width(8, 1u128 << i, 1u128 << j);
                if (basis_product >> bit) & 1 == 1 {
                    terms.push(product_wire);
                }
            }
        }
        out.push(builder.alloc_linear(terms, false)?);
    }
    Ok(out)
}

fn linear_field_map<F>(
    builder: &mut BinaryR1csBuilder,
    width: usize,
    input: &[usize],
    map_basis: F,
) -> Result<Vec<usize>, CircuitError>
where
    F: Fn(u128) -> u128,
{
    let mut out = Vec::with_capacity(width);
    for bit in 0..width {
        let mut terms = Vec::new();
        for (input_bit, &wire) in input.iter().enumerate() {
            let mapped = map_basis(1u128 << input_bit);
            if (mapped >> bit) & 1 == 1 {
                terms.push(wire);
            }
        }
        out.push(builder.alloc_linear(terms, false)?);
    }
    Ok(out)
}

fn normalize_terms<I>(terms: I) -> Vec<usize>
where
    I: IntoIterator<Item = usize>,
{
    let mut terms = terms.into_iter().collect::<Vec<_>>();
    terms.sort_unstable();
    let mut out = Vec::with_capacity(terms.len());
    for term in terms {
        if out.last().copied() == Some(term) {
            out.pop();
        } else {
            out.push(term);
        }
    }
    out
}

fn is_supported_width(width: usize) -> bool {
    matches!(width, 8 | 16 | 32 | 64 | 128)
}

fn tau_for_extension_width(width: usize) -> u128 {
    match width {
        16 => Block8::EXTENSION_TAU.0 as u128,
        32 => Block16::TAU.0 as u128,
        64 => Block32::TAU.0 as u128,
        128 => Block64::TAU.0 as u128,
        _ => panic!("unsupported tower extension width {width}"),
    }
}

fn native_square_width(width: usize, value: u128) -> u128 {
    match width {
        8 => Block8(value as u8).square().0 as u128,
        16 => Block16(value as u16).square().0 as u128,
        32 => Block32(value as u32).square().0 as u128,
        64 => Block64(value as u64).square().0 as u128,
        128 => Block128(value).square().0,
        _ => panic!("unsupported field width {width}"),
    }
}

fn native_mul_width(width: usize, left: u128, right: u128) -> u128 {
    match width {
        8 => (Block8(left as u8) * Block8(right as u8)).0 as u128,
        16 => (Block16(left as u16) * Block16(right as u16)).0 as u128,
        32 => (Block32(left as u32) * Block32(right as u32)).0 as u128,
        64 => (Block64(left as u64) * Block64(right as u64)).0 as u128,
        128 => (Block128(left) * Block128(right)).0,
        _ => panic!("unsupported field width {width}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::native::permutation::Poseidon2bPermutation;

    #[test]
    fn block128_mul_gadget_matches_noid_core() {
        let left = Block128::from(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210u128);
        let right = Block128::from(0xfedc_ba98_7654_3210_0123_4567_89ab_cdefu128);
        let mut builder = BinaryR1csBuilder::new(15);
        let left_bits = builder.alloc_block128(left).expect("left");
        let right_bits = builder.alloc_block128(right).expect("right");
        let product = mul_block128_bits(&mut builder, &left_bits, &right_bits).expect("mul");
        let expected = left * right;
        assert_eq!(builder.block128_value(&product), expected);
        builder.pin_block128(&product, expected).expect("pin");
        let (r1cs, witness) = builder.build();
        assert!(r1cs.satisfies(&witness));
    }

    #[test]
    fn poseidon2b_permutation_gadget_matches_native() {
        let initial = [
            Block128::from(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210u128),
            Block128::from(0xffff_0000_ffff_0000_aaaa_5555_aaaa_5555u128),
            Block128::from(0x1111_2222_3333_4444_5555_6666_7777_8888u128),
            Block128::from(0xdead_beef_cafe_babe_0123_4567_89ab_cdefu128),
        ];
        let mut expected = initial;
        Poseidon2bPermutation.permute_mut(&mut expected);

        let mut builder = BinaryR1csBuilder::new(21);
        let mut state = [
            builder.alloc_block128(initial[0]).expect("s0"),
            builder.alloc_block128(initial[1]).expect("s1"),
            builder.alloc_block128(initial[2]).expect("s2"),
            builder.alloc_block128(initial[3]).expect("s3"),
        ];
        poseidon2b_permute_bits(&mut builder, &mut state).expect("permute");
        for lane in 0..STATE_SIZE {
            assert_eq!(builder.block128_value(&state[lane]), expected[lane]);
            builder
                .pin_block128(&state[lane], expected[lane])
                .expect("pin");
        }
        let (r1cs, witness) = builder.build();
        assert!(r1cs.satisfies(&witness));
    }
}
