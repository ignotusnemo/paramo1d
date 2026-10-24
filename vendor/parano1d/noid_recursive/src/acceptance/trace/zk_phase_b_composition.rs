// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Production composition of one complete authorization
//! capsule Phase B.
//!
//! This region consumes the exact aliases owned by the surrounding
//! transcript and FF-Merkle regions.  It allocates no duplicate query bits,
//! fold points, tail cells, or terminal value:
//!
//! - seven packed seeds are rebound to the two depth-eight path direction
//!   families and the one shared `q12` cap selector;
//! - one shared `upper[256]`/`tail16` linkage binds both `v` and the surviving
//!   `h8` table;
//! - 65 fixed query units consume the returned query-bit aliases, the shared
//!   `gamma`, `beta`, and `tail`, and the authenticated source/mid leaves;
//! - both two-lane caps are selected with those same query aliases and pinned
//!   directly to caller-supplied FF path-root expressions.
//!
//! The FF path-root expressions themselves are intentionally constructed by
//! the Wallet-B Merkle region: at depth eight they are the final composite
//! node expressions, not root-copy cells.  This module only proves that each
//! expression equals the transcript-committed cap entry selected by the
//! exact same 13-bit query.

use noid_fri_binius::zk_capsule::ZK_AUTH_CAPSULE_GEOMETRY;
use noid_fri_binius::zk_capsule_algebra::{
    JOINT_SOURCE_LEAF_SYMBOLS, MID_STANDARD_FOLDS, OWNER_BANK_POINT_VARS, PHASE_B_LOW_VARS,
    SOURCE_QUERY_BITS, SOURCE_STANDARD_FOLDS, TAIL_SYMBOLS, UPPER_SYMBOLS,
};

use super::fri_pcs::mle_evaluate_small_trace;
use super::zk_phase_b_query::{
    verify_zk_phase_b_query_trace, ZkPhaseBQueryTraceError, ZkPhaseBQueryTraceInput,
    ZkPhaseBQueryTraceOutput, ZK_PHASE_B_QUERY_TRACE_ROWS,
};
use super::zk_phase_b_upper_link::{
    verify_zk_phase_b_upper_link_trace, ZkPhaseBUpperLinkTraceError, ZkPhaseBUpperLinkTraceInput,
    ZkPhaseBUpperLinkTraceOutput, ZK_PHASE_B_UPPER_LINK_TRACE_ROWS,
};
use super::zk_query_carriers::{
    bind_zk_capsule_query_carriers, BoundZkCapsuleQueries, ZK_MID_PATH_DIRECTION_BITS,
    ZK_QUERY_CARRIER_ROWS, ZK_QUERY_COUNT, ZK_QUERY_SEED_COUNT, ZK_SOURCE_PATH_DIRECTION_BITS,
};
use super::{pin_eq, ExtExpr, FieldR1csBuilder, LinExpr};

/// Two F128 lanes in every selected Merkle digest.
pub const ZK_PHASE_B_CAP_DIGEST_LANES: usize = 2;
pub const ZK_PHASE_B_SOURCE_CAP_NODES: usize = 1 << ZK_AUTH_CAPSULE_GEOMETRY.source_cap_depth;
pub const ZK_PHASE_B_MID_CAP_NODES: usize = 1 << ZK_AUTH_CAPSULE_GEOMETRY.mid_cap_depth;

/// An eight-way cap MLE costs seven products plus one root pin per digest lane.
pub const ZK_PHASE_B_SOURCE_CAP_ROWS_PER_QUERY: usize =
    ZK_PHASE_B_CAP_DIGEST_LANES * ((ZK_PHASE_B_SOURCE_CAP_NODES - 1) + 1);
/// An eight-way cap MLE costs seven products plus one root pin per digest lane.
pub const ZK_PHASE_B_MID_CAP_ROWS_PER_QUERY: usize =
    ZK_PHASE_B_CAP_DIGEST_LANES * ((ZK_PHASE_B_MID_CAP_NODES - 1) + 1);

/// Exact incremental ledger after all caller-owned aliases are allocated.
pub const ZK_PHASE_B_COMPOSITION_TRACE_ROWS: usize = ZK_QUERY_CARRIER_ROWS
    + ZK_PHASE_B_UPPER_LINK_TRACE_ROWS
    + ZK_QUERY_COUNT
        * (ZK_PHASE_B_QUERY_TRACE_ROWS
            + ZK_PHASE_B_SOURCE_CAP_ROWS_PER_QUERY
            + ZK_PHASE_B_MID_CAP_ROWS_PER_QUERY);

const _: () = assert!(ZK_QUERY_COUNT == 65);
const _: () = assert!(ZK_QUERY_SEED_COUNT == 7);
const _: () = assert!(SOURCE_QUERY_BITS == 13);
const _: () = assert!(ZK_SOURCE_PATH_DIRECTION_BITS == 10);
const _: () = assert!(ZK_MID_PATH_DIRECTION_BITS == 6);
const _: () = assert!(ZK_PHASE_B_SOURCE_CAP_NODES == 8);
const _: () = assert!(ZK_PHASE_B_MID_CAP_NODES == 8);
const _: () = assert!(ZK_PHASE_B_SOURCE_CAP_ROWS_PER_QUERY == 16);
const _: () = assert!(ZK_PHASE_B_MID_CAP_ROWS_PER_QUERY == 16);
const _: () = assert!(ZK_PHASE_B_COMPOSITION_TRACE_ROWS == 13_926);

/// Caller-owned dynamic input family.  `index` in the error is the natural
/// flattened index within the named family, never a proof-controlled shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkPhaseBCompositionDynamicInput {
    QuerySeed,
    SourcePathDirection,
    MidPathDirection,
    JointSourceLeaf,
    MidLeaf,
    SourceCap,
    MidCap,
    SourcePathRoot,
    MidPathRoot,
    Upper,
    PhaseATerminalPoint,
    Beta,
    TerminalOracleValue,
    Tail,
    Gamma,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkPhaseBCompositionTraceError {
    /// A proof/transcript value was embedded as a matrix constant rather than
    /// entering through a caller-owned dynamic expression.
    DynamicInputIsConstant {
        input: ZkPhaseBCompositionDynamicInput,
        index: usize,
    },
    UpperLink(ZkPhaseBUpperLinkTraceError),
    Query {
        query: usize,
        source: ZkPhaseBQueryTraceError,
    },
}

impl From<ZkPhaseBUpperLinkTraceError> for ZkPhaseBCompositionTraceError {
    fn from(value: ZkPhaseBUpperLinkTraceError) -> Self {
        Self::UpperLink(value)
    }
}

/// Complete fixed-shape Phase-B aliases for one authorization.
#[derive(Clone, Debug)]
pub struct ZkPhaseBCompositionTraceInput {
    /// Seven Main-channel query squeezes.
    pub query_seeds: [LinExpr; ZK_QUERY_SEED_COUNT],
    /// Existing FF source-path `D[0..10]` cells, `[query][depth]`.
    pub source_path_directions: [[LinExpr; ZK_SOURCE_PATH_DIRECTION_BITS]; ZK_QUERY_COUNT],
    /// Existing FF mid-path `D[0..6]` cells, `[query][depth]`.
    pub mid_path_directions: [[LinExpr; ZK_MID_PATH_DIRECTION_BITS]; ZK_QUERY_COUNT],
    /// Authenticated adjacent source leaves `[B0,C0,...,B7,C7]`.
    pub joint_source_leaves: [[LinExpr; JOINT_SOURCE_LEAF_SYMBOLS]; ZK_QUERY_COUNT],
    /// Authenticated contiguous 16-cell mid leaves.
    pub mid_leaves: [[ExtExpr; 1 << MID_STANDARD_FOLDS]; ZK_QUERY_COUNT],
    /// Source cap in transcript order, `[digest_lane][cap_index]`.
    pub source_cap: [[LinExpr; ZK_PHASE_B_SOURCE_CAP_NODES]; ZK_PHASE_B_CAP_DIGEST_LANES],
    /// Mid cap in transcript order, `[digest_lane][cap_index]`.
    pub mid_cap: [[LinExpr; ZK_PHASE_B_MID_CAP_NODES]; ZK_PHASE_B_CAP_DIGEST_LANES],
    /// Final source FF root expressions, `[query][digest_lane]`.
    pub source_path_roots: [[LinExpr; ZK_PHASE_B_CAP_DIGEST_LANES]; ZK_QUERY_COUNT],
    /// Final mid FF root expressions, `[query][digest_lane]`.
    pub mid_path_roots: [[LinExpr; ZK_PHASE_B_CAP_DIGEST_LANES]; ZK_QUERY_COUNT],
    /// Published high-three contraction in natural low-eight table order.
    pub upper: [ExtExpr; UPPER_SYMBOLS],
    /// Shared Phase-A terminal point `s0..s10`, LOW-to-HIGH.
    pub phase_a_terminal_point: [ExtExpr; OWNER_BANK_POINT_VARS],
    /// Shared Phase-B folds `beta0..beta7`, LOW-to-HIGH.
    pub beta: [ExtExpr; PHASE_B_LOW_VARS],
    /// Exact `v` alias consumed by Phase A.
    pub terminal_oracle_value: ExtExpr,
    /// Shared revealed coefficient tail after folds `beta0..beta6`.
    pub tail: [ExtExpr; TAIL_SYMBOLS],
    /// Shared masking-line challenge.
    pub gamma: ExtExpr,
}

#[derive(Clone, Debug)]
pub struct ZkPhaseBCompositionTraceOutput {
    pub bound_queries: BoundZkCapsuleQueries,
    pub upper_link: ZkPhaseBUpperLinkTraceOutput,
    pub queries: Vec<ZkPhaseBQueryTraceOutput>,
    /// Cap values selected and pinned to each source FF root expression.
    pub selected_source_cap_roots: Vec<[LinExpr; ZK_PHASE_B_CAP_DIGEST_LANES]>,
    /// Cap values selected and pinned to each mid FF root expression.
    pub selected_mid_cap_roots: Vec<[LinExpr; ZK_PHASE_B_CAP_DIGEST_LANES]>,
}

fn check_dynamic(
    expression: &LinExpr,
    input: ZkPhaseBCompositionDynamicInput,
    index: usize,
) -> Result<(), ZkPhaseBCompositionTraceError> {
    if expression.is_const() {
        Err(ZkPhaseBCompositionTraceError::DynamicInputIsConstant { input, index })
    } else {
        Ok(())
    }
}

fn check_dynamic_ext(
    expression: &ExtExpr,
    input: ZkPhaseBCompositionDynamicInput,
    index: usize,
) -> Result<(), ZkPhaseBCompositionTraceError> {
    if expression.is_const() {
        Err(ZkPhaseBCompositionTraceError::DynamicInputIsConstant { input, index })
    } else {
        Ok(())
    }
}

fn preflight_dynamic_inputs(
    input: &ZkPhaseBCompositionTraceInput,
) -> Result<(), ZkPhaseBCompositionTraceError> {
    for (index, expression) in input.query_seeds.iter().enumerate() {
        check_dynamic(
            expression,
            ZkPhaseBCompositionDynamicInput::QuerySeed,
            index,
        )?;
    }
    for query in 0..ZK_QUERY_COUNT {
        for bit in 0..ZK_SOURCE_PATH_DIRECTION_BITS {
            check_dynamic(
                &input.source_path_directions[query][bit],
                ZkPhaseBCompositionDynamicInput::SourcePathDirection,
                query * ZK_SOURCE_PATH_DIRECTION_BITS + bit,
            )?;
        }
        for bit in 0..ZK_MID_PATH_DIRECTION_BITS {
            check_dynamic(
                &input.mid_path_directions[query][bit],
                ZkPhaseBCompositionDynamicInput::MidPathDirection,
                query * ZK_MID_PATH_DIRECTION_BITS + bit,
            )?;
        }
        for symbol in 0..JOINT_SOURCE_LEAF_SYMBOLS {
            check_dynamic(
                &input.joint_source_leaves[query][symbol],
                ZkPhaseBCompositionDynamicInput::JointSourceLeaf,
                query * JOINT_SOURCE_LEAF_SYMBOLS + symbol,
            )?;
        }
        for symbol in 0..(1 << MID_STANDARD_FOLDS) {
            check_dynamic_ext(
                &input.mid_leaves[query][symbol],
                ZkPhaseBCompositionDynamicInput::MidLeaf,
                query * (1 << MID_STANDARD_FOLDS) + symbol,
            )?;
        }
        for lane in 0..ZK_PHASE_B_CAP_DIGEST_LANES {
            check_dynamic(
                &input.source_path_roots[query][lane],
                ZkPhaseBCompositionDynamicInput::SourcePathRoot,
                query * ZK_PHASE_B_CAP_DIGEST_LANES + lane,
            )?;
            check_dynamic(
                &input.mid_path_roots[query][lane],
                ZkPhaseBCompositionDynamicInput::MidPathRoot,
                query * ZK_PHASE_B_CAP_DIGEST_LANES + lane,
            )?;
        }
    }
    for lane in 0..ZK_PHASE_B_CAP_DIGEST_LANES {
        for node in 0..ZK_PHASE_B_SOURCE_CAP_NODES {
            check_dynamic(
                &input.source_cap[lane][node],
                ZkPhaseBCompositionDynamicInput::SourceCap,
                lane * ZK_PHASE_B_SOURCE_CAP_NODES + node,
            )?;
        }
        for node in 0..ZK_PHASE_B_MID_CAP_NODES {
            check_dynamic(
                &input.mid_cap[lane][node],
                ZkPhaseBCompositionDynamicInput::MidCap,
                lane * ZK_PHASE_B_MID_CAP_NODES + node,
            )?;
        }
    }
    for (index, expression) in input.upper.iter().enumerate() {
        check_dynamic_ext(expression, ZkPhaseBCompositionDynamicInput::Upper, index)?;
    }
    for (index, expression) in input.phase_a_terminal_point.iter().enumerate() {
        check_dynamic_ext(
            expression,
            ZkPhaseBCompositionDynamicInput::PhaseATerminalPoint,
            index,
        )?;
    }
    for (index, expression) in input.beta.iter().enumerate() {
        check_dynamic_ext(expression, ZkPhaseBCompositionDynamicInput::Beta, index)?;
    }
    check_dynamic_ext(
        &input.terminal_oracle_value,
        ZkPhaseBCompositionDynamicInput::TerminalOracleValue,
        0,
    )?;
    for (index, expression) in input.tail.iter().enumerate() {
        check_dynamic_ext(expression, ZkPhaseBCompositionDynamicInput::Tail, index)?;
    }
    check_dynamic_ext(&input.gamma, ZkPhaseBCompositionDynamicInput::Gamma, 0)?;
    Ok(())
}

fn select_and_pin_cap<const N: usize>(
    b: &mut FieldR1csBuilder,
    cap: &[[LinExpr; N]; ZK_PHASE_B_CAP_DIGEST_LANES],
    selector: &[LinExpr],
    path_root: &[LinExpr; ZK_PHASE_B_CAP_DIGEST_LANES],
) -> [LinExpr; ZK_PHASE_B_CAP_DIGEST_LANES] {
    assert_eq!(N, 1usize << selector.len(), "cap selector width");
    std::array::from_fn(|lane| {
        let selected = mle_evaluate_small_trace(b, &cap[lane], selector);
        pin_eq(b, &selected, &path_root[lane]);
        selected
    })
}

/// Compose the complete fixed-64 Phase-B arithmetic and cap linkage.
///
/// All proof/transcript inputs are preflighted before any row is appended.
/// Query directions and FF path roots are existing caller-owned expressions;
/// their booleanity/hash arithmetic is not charged here.  An honest call
/// appends exactly [`ZK_PHASE_B_COMPOSITION_TRACE_ROWS`] rows.
pub fn verify_zk_phase_b_composition_trace(
    b: &mut FieldR1csBuilder,
    input: &ZkPhaseBCompositionTraceInput,
) -> Result<ZkPhaseBCompositionTraceOutput, ZkPhaseBCompositionTraceError> {
    preflight_dynamic_inputs(input)?;
    let trace_start = b.num_wires();

    let seed_aliases = input.query_seeds.to_vec();
    let source_direction_aliases = input
        .source_path_directions
        .iter()
        .map(|directions| directions.to_vec())
        .collect::<Vec<_>>();
    let mid_direction_aliases = input
        .mid_path_directions
        .iter()
        .map(|directions| directions.to_vec())
        .collect::<Vec<_>>();
    let bound_queries = bind_zk_capsule_query_carriers(
        b,
        &seed_aliases,
        &source_direction_aliases,
        &mid_direction_aliases,
    );
    debug_assert_eq!(b.num_wires() - trace_start, ZK_QUERY_CARRIER_ROWS);

    let upper_link = verify_zk_phase_b_upper_link_trace(
        b,
        &ZkPhaseBUpperLinkTraceInput {
            upper: input.upper.clone(),
            phase_a_terminal_point: input.phase_a_terminal_point.clone(),
            beta: input.beta.clone(),
            terminal_oracle_value: input.terminal_oracle_value.clone(),
            tail: input.tail.clone(),
        },
    )?;
    debug_assert_eq!(
        b.num_wires() - trace_start,
        ZK_QUERY_CARRIER_ROWS + ZK_PHASE_B_UPPER_LINK_TRACE_ROWS
    );

    let source_challenges: [ExtExpr; SOURCE_STANDARD_FOLDS] =
        std::array::from_fn(|round| upper_link.beta[round].clone());
    let mid_challenges: [ExtExpr; MID_STANDARD_FOLDS] =
        std::array::from_fn(|round| upper_link.beta[SOURCE_STANDARD_FOLDS + round].clone());

    let mut queries = Vec::with_capacity(ZK_QUERY_COUNT);
    let mut selected_source_cap_roots = Vec::with_capacity(ZK_QUERY_COUNT);
    let mut selected_mid_cap_roots = Vec::with_capacity(ZK_QUERY_COUNT);
    for query in 0..ZK_QUERY_COUNT {
        let query_bits: [LinExpr; SOURCE_QUERY_BITS] = bound_queries.bits[query]
            .clone()
            .try_into()
            .expect("fixed 13-bit bound query");
        let output = verify_zk_phase_b_query_trace(
            b,
            &ZkPhaseBQueryTraceInput {
                query_bits,
                joint_source_leaf: input.joint_source_leaves[query].clone(),
                mid_leaf: input.mid_leaves[query].clone(),
                tail: input.tail.clone(),
                gamma: input.gamma.clone(),
                source_challenges: source_challenges.clone(),
                mid_challenges: mid_challenges.clone(),
            },
        )
        .map_err(|source| ZkPhaseBCompositionTraceError::Query { query, source })?;
        queries.push(output);

        selected_source_cap_roots.push(select_and_pin_cap(
            b,
            &input.source_cap,
            &bound_queries.source_cap_bits[query],
            &input.source_path_roots[query],
        ));
        selected_mid_cap_roots.push(select_and_pin_cap(
            b,
            &input.mid_cap,
            &bound_queries.mid_cap_bits[query],
            &input.mid_path_roots[query],
        ));
    }

    debug_assert_eq!(
        b.num_wires() - trace_start,
        ZK_PHASE_B_COMPOSITION_TRACE_ROWS
    );
    Ok(ZkPhaseBCompositionTraceOutput {
        bound_queries,
        upper_link,
        queries,
        selected_source_cap_roots,
        selected_mid_cap_roots,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acceptance::trace::{alloc_block, alloc_block256, const_block256, flat_of, F128};
    use noid_core::mle::evaluate::evaluate_slice;
    use noid_core::mle::fold::fold_variable_inplace;
    use noid_core::{Block128, Block256, TowerField};
    use noid_fri_binius::capsule::capsule_query_bit_location;
    use noid_fri_binius::zk_affine_code::{ZkAffineLchCode, AFFINE_CODE_MESSAGE_LEN};
    use noid_fri_binius::zk_capsule_algebra::{
        build_fold_normal_joint_source_leaf, build_fold_normal_mid_leaf,
        contract_high3_for_each_low8, evaluate_upper_at_low8, PHASE_B_HIGH_VARS,
    };
    use noid_ivc_core::field_r1cs::FieldR1cs;

    #[derive(Clone)]
    struct NativeCase {
        query_seeds: [Block128; ZK_QUERY_SEED_COUNT],
        queries: [usize; ZK_QUERY_COUNT],
        joint_source_leaves: [[Block128; JOINT_SOURCE_LEAF_SYMBOLS]; ZK_QUERY_COUNT],
        mid_leaves: [[Block256; 1 << MID_STANDARD_FOLDS]; ZK_QUERY_COUNT],
        source_cap: [[Block128; ZK_PHASE_B_SOURCE_CAP_NODES]; ZK_PHASE_B_CAP_DIGEST_LANES],
        mid_cap: [[Block128; ZK_PHASE_B_MID_CAP_NODES]; ZK_PHASE_B_CAP_DIGEST_LANES],
        source_path_roots: [[Block128; ZK_PHASE_B_CAP_DIGEST_LANES]; ZK_QUERY_COUNT],
        mid_path_roots: [[Block128; ZK_PHASE_B_CAP_DIGEST_LANES]; ZK_QUERY_COUNT],
        upper: [Block256; UPPER_SYMBOLS],
        phase_a_terminal_point: [Block256; OWNER_BANK_POINT_VARS],
        beta: [Block256; PHASE_B_LOW_VARS],
        terminal_oracle_value: Block256,
        tail: [Block256; TAIL_SYMBOLS],
        gamma: Block256,
    }

    fn elem(index: usize, domain: u128, salt: u128) -> Block128 {
        let mut value = Block128::from(
            domain
                .wrapping_mul(index as u128 + 1)
                .rotate_left(((17 * index + 5) % 127) as u32)
                ^ salt.rotate_left(((11 * index + 3) % 127) as u32)
                ^ (index as u128 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15),
        );
        if value == Block128::ZERO || value == Block128::ONE {
            value += Block128::from(2u128);
        }
        value
    }

    fn message(domain: u128, salt: u128) -> [Block128; AFFINE_CODE_MESSAGE_LEN] {
        std::array::from_fn(|index| elem(index, domain, salt))
    }

    fn ext_elem(index: usize, domain: u128, salt: u128) -> Block256 {
        Block256::new(
            elem(index, domain, salt),
            elem(index + 113, domain ^ 0xC1_256, salt.rotate_left(43)),
        )
    }

    fn ext_message(domain: u128, salt: u128) -> [Block256; AFFINE_CODE_MESSAGE_LEN] {
        std::array::from_fn(|index| ext_elem(index, domain, salt))
    }

    fn packed_queries(seeds: &[Block128; ZK_QUERY_SEED_COUNT]) -> [usize; ZK_QUERY_COUNT] {
        std::array::from_fn(|query| {
            (0..SOURCE_QUERY_BITS).fold(0usize, |index, query_bit| {
                let (seed, bit) = capsule_query_bit_location(query, query_bit, SOURCE_QUERY_BITS);
                index | ((((seeds[seed].0 >> bit) & 1) as usize) << query_bit)
            })
        })
    }

    fn native_case(salt: u128) -> NativeCase {
        let code = ZkAffineLchCode::selected().expect("selected affine code");
        let bank = message(0xB4A9, salt ^ 0x11);
        let companion = ext_message(0xC09A, salt ^ 0x22);
        let mut gamma = ext_elem(17, 0x6A77A, salt ^ 0x33);
        if gamma == Block256::ZERO || gamma == Block256::ONE {
            gamma += Block256::from(2u128);
        }
        let beta: [Block256; PHASE_B_LOW_VARS] =
            std::array::from_fn(|index| ext_elem(index + 31, 0xBE7A, salt ^ 0x44));
        let phase_a_terminal_point: [Block256; OWNER_BANK_POINT_VARS] =
            std::array::from_fn(|index| ext_elem(index + 47, 0x5A11, salt ^ 0x55));
        let query_seeds: [Block128; ZK_QUERY_SEED_COUNT] =
            std::array::from_fn(|index| elem(index + 71, 0x5EED, salt ^ 0x66));
        let queries = packed_queries(&query_seeds);

        let virtual_bank: [Block256; AFFINE_CODE_MESSAGE_LEN] = std::array::from_fn(|index| {
            Block256::from(bank[index]) + gamma * (Block256::from(bank[index]) + companion[index])
        });
        let bank_code = code.encode(&bank).expect("bank codeword");
        let companion_code = code
            .encode_extension_after_low_folds(&companion, 0)
            .expect("companion codeword");
        let mut mid_code = code
            .encode_extension_after_low_folds(&virtual_bank, 0)
            .expect("virtual codeword");
        for round in 0..SOURCE_STANDARD_FOLDS {
            mid_code = code
                .fold_codeword_once_extension(&mid_code, round, beta[round])
                .expect("source fold");
        }
        let joint_source_leaves = std::array::from_fn(|query| {
            build_fold_normal_joint_source_leaf(&code, &bank_code, &companion_code, queries[query])
                .expect("fold-normal joint source leaf")
        });
        let mid_leaves = std::array::from_fn(|query| {
            build_fold_normal_mid_leaf(&code, &mid_code, queries[query] >> MID_STANDARD_FOLDS)
                .expect("fold-normal mid leaf")
        });

        for round in 0..MID_STANDARD_FOLDS {
            mid_code = code
                .fold_codeword_once_extension(
                    &mid_code,
                    SOURCE_STANDARD_FOLDS + round,
                    beta[SOURCE_STANDARD_FOLDS + round],
                )
                .expect("mid fold");
        }
        let mut tail_vec = virtual_bank.to_vec();
        for challenge in &beta[..SOURCE_STANDARD_FOLDS + MID_STANDARD_FOLDS] {
            fold_variable_inplace(&mut tail_vec, *challenge, 0);
        }
        let tail: [Block256; TAIL_SYMBOLS] = tail_vec.try_into().expect("seven folds leave 16");
        assert_eq!(
            code.encode_extension_after_low_folds(
                &tail,
                SOURCE_STANDARD_FOLDS + MID_STANDARD_FOLDS,
            )
            .expect("tail codeword"),
            mid_code
        );

        let high_point: &[Block256; PHASE_B_HIGH_VARS] = phase_a_terminal_point[PHASE_B_LOW_VARS..]
            .try_into()
            .expect("11-variable point has three HIGH coordinates");
        let low_point: &[Block256; PHASE_B_LOW_VARS] = phase_a_terminal_point[..PHASE_B_LOW_VARS]
            .try_into()
            .expect("11-variable point has eight LOW coordinates");
        let upper = contract_high3_for_each_low8(&virtual_bank, high_point);
        let terminal_oracle_value = evaluate_upper_at_low8(&upper, low_point);
        assert_eq!(
            terminal_oracle_value,
            evaluate_slice(&virtual_bank, &phase_a_terminal_point)
        );

        let source_cap = std::array::from_fn(|lane| {
            std::array::from_fn(|node| elem(node + 101 * lane, 0x5CA9, salt ^ 0x77))
        });
        let mid_cap = std::array::from_fn(|lane| {
            std::array::from_fn(|node| elem(node + 13 * lane, 0x1DC4, salt ^ 0x88))
        });
        let source_path_roots = std::array::from_fn(|query| {
            let cap_index = queries[query] >> ZK_AUTH_CAPSULE_GEOMETRY.source_path_depth;
            std::array::from_fn(|lane| source_cap[lane][cap_index])
        });
        let mid_path_roots = std::array::from_fn(|query| {
            let cap_index =
                (queries[query] >> MID_STANDARD_FOLDS) >> ZK_AUTH_CAPSULE_GEOMETRY.mid_path_depth;
            std::array::from_fn(|lane| mid_cap[lane][cap_index])
        });

        NativeCase {
            query_seeds,
            queries,
            joint_source_leaves,
            mid_leaves,
            source_cap,
            mid_cap,
            source_path_roots,
            mid_path_roots,
            upper,
            phase_a_terminal_point,
            beta,
            terminal_oracle_value,
            tail,
            gamma,
        }
    }

    fn alloc_bool_expr(b: &mut FieldR1csBuilder, value: bool) -> LinExpr {
        LinExpr::from_wire(b.alloc_bool(value))
    }

    fn alloc_input(b: &mut FieldR1csBuilder, native: &NativeCase) -> ZkPhaseBCompositionTraceInput {
        ZkPhaseBCompositionTraceInput {
            query_seeds: std::array::from_fn(|index| alloc_block(b, native.query_seeds[index])),
            source_path_directions: std::array::from_fn(|query| {
                std::array::from_fn(|bit| {
                    alloc_bool_expr(b, (native.queries[query] >> bit) & 1 == 1)
                })
            }),
            mid_path_directions: std::array::from_fn(|query| {
                std::array::from_fn(|bit| {
                    alloc_bool_expr(b, (native.queries[query] >> (4 + bit)) & 1 == 1)
                })
            }),
            joint_source_leaves: std::array::from_fn(|query| {
                std::array::from_fn(|symbol| {
                    alloc_block(b, native.joint_source_leaves[query][symbol])
                })
            }),
            mid_leaves: std::array::from_fn(|query| {
                std::array::from_fn(|symbol| alloc_block256(b, native.mid_leaves[query][symbol]))
            }),
            source_cap: std::array::from_fn(|lane| {
                std::array::from_fn(|node| alloc_block(b, native.source_cap[lane][node]))
            }),
            mid_cap: std::array::from_fn(|lane| {
                std::array::from_fn(|node| alloc_block(b, native.mid_cap[lane][node]))
            }),
            source_path_roots: std::array::from_fn(|query| {
                std::array::from_fn(|lane| alloc_block(b, native.source_path_roots[query][lane]))
            }),
            mid_path_roots: std::array::from_fn(|query| {
                std::array::from_fn(|lane| alloc_block(b, native.mid_path_roots[query][lane]))
            }),
            upper: std::array::from_fn(|index| alloc_block256(b, native.upper[index])),
            phase_a_terminal_point: std::array::from_fn(|index| {
                alloc_block256(b, native.phase_a_terminal_point[index])
            }),
            beta: std::array::from_fn(|index| alloc_block256(b, native.beta[index])),
            terminal_oracle_value: alloc_block256(b, native.terminal_oracle_value),
            tail: std::array::from_fn(|index| alloc_block256(b, native.tail[index])),
            gamma: alloc_block256(b, native.gamma),
        }
    }

    fn input_wire(expression: &LinExpr) -> usize {
        assert_eq!(expression.terms.len(), 1);
        assert_eq!(expression.terms[0].1, F128::ONE);
        assert_eq!(expression.constant, F128::ZERO);
        expression.terms[0].0 as usize
    }

    struct BuiltCase {
        r1cs: FieldR1cs,
        witness: Vec<F128>,
        trace_rows: usize,
        indices: Vec<usize>,
        digest: [u8; 32],
        source_direction_wire: usize,
        source_leaf_wire: usize,
        mid_leaf_wire: usize,
        source_cap_wire: usize,
        source_path_root_wire: usize,
        mid_path_root_wire: usize,
        tail_wire: usize,
        upper_wire: usize,
        terminal_value_wire: usize,
    }

    fn build_case(native: &NativeCase) -> BuiltCase {
        let mut b = FieldR1csBuilder::new();
        let input = alloc_input(&mut b, native);
        let source_direction_wire = input_wire(&input.source_path_directions[3][2]);
        let source_leaf_wire = input_wire(&input.joint_source_leaves[5][3]);
        let mid_leaf_wire = input_wire(&input.mid_leaves[7][native.queries[7] & 0xf].lo);
        let source_cap_index = native.queries[11] >> ZK_AUTH_CAPSULE_GEOMETRY.source_path_depth;
        let source_cap_wire = input_wire(&input.source_cap[1][source_cap_index]);
        let source_path_root_wire = input_wire(&input.source_path_roots[11][1]);
        let mid_path_root_wire = input_wire(&input.mid_path_roots[13][0]);
        let tail_wire = input_wire(&input.tail[7].lo);
        let upper_wire = input_wire(&input.upper[37].lo);
        let terminal_value_wire = input_wire(&input.terminal_oracle_value.lo);
        let before = b.num_wires();
        let output = verify_zk_phase_b_composition_trace(&mut b, &input)
            .expect("honest Phase-B composition");
        let trace_rows = b.num_wires() - before;
        assert_eq!(output.upper_link.beta, input.beta);
        assert_eq!(
            output.upper_link.phase_a_terminal_point,
            input.phase_a_terminal_point
        );
        assert_eq!(
            output.upper_link.terminal_oracle_value,
            input.terminal_oracle_value
        );
        assert_eq!(output.queries.len(), ZK_QUERY_COUNT);
        assert_eq!(output.selected_source_cap_roots.len(), ZK_QUERY_COUNT);
        assert_eq!(output.selected_mid_cap_roots.len(), ZK_QUERY_COUNT);
        for query in 0..ZK_QUERY_COUNT {
            for lane in 0..ZK_PHASE_B_CAP_DIGEST_LANES {
                assert_eq!(
                    output.selected_source_cap_roots[query][lane].eval(b.values()),
                    flat_of(native.source_path_roots[query][lane])
                );
                assert_eq!(
                    output.selected_mid_cap_roots[query][lane].eval(b.values()),
                    flat_of(native.mid_path_roots[query][lane])
                );
            }
        }
        let indices = output.bound_queries.indices;
        let (r1cs, witness) = b.build();
        let digest = r1cs.structural_statement_digest();
        BuiltCase {
            r1cs,
            witness,
            trace_rows,
            indices,
            digest,
            source_direction_wire,
            source_leaf_wire,
            mid_leaf_wire,
            source_cap_wire,
            source_path_root_wire,
            mid_path_root_wire,
            tail_wire,
            upper_wire,
            terminal_value_wire,
        }
    }

    #[test]
    fn complete_phase_b_matches_native_affine_code_caps_and_exact_ledger() {
        let native = native_case(0xA11C_EB01);
        let built = build_case(&native);
        assert!(built.r1cs.satisfies(&built.witness));
        assert_eq!(built.indices, native.queries);

        assert_eq!(ZK_QUERY_CARRIER_ROWS, 257);
        assert_eq!(ZK_PHASE_B_UPPER_LINK_TRACE_ROWS, 1_579);
        assert_eq!(ZK_PHASE_B_QUERY_TRACE_ROWS, 154);
        assert_eq!(ZK_PHASE_B_SOURCE_CAP_ROWS_PER_QUERY, 16);
        assert_eq!(ZK_PHASE_B_MID_CAP_ROWS_PER_QUERY, 16);
        assert_eq!(ZK_PHASE_B_COMPOSITION_TRACE_ROWS, 13_926);
        assert_eq!(built.trace_rows, ZK_PHASE_B_COMPOSITION_TRACE_ROWS);
    }

    #[test]
    fn query_path_root_cap_tail_and_every_cross_layer_splice_tamper_reject() {
        let built = build_case(&native_case(0xA11C_EB02));
        assert!(built.r1cs.satisfies(&built.witness));

        for (name, wire) in [
            ("transcript query carrier", built.source_direction_wire),
            ("source-to-mid splice", built.source_leaf_wire),
            ("mid-to-tail splice", built.mid_leaf_wire),
            ("selected source cap", built.source_cap_wire),
            ("source path root", built.source_path_root_wire),
            ("mid path root", built.mid_path_root_wire),
            ("shared tail", built.tail_wire),
            ("upper table", built.upper_wire),
            ("upper-to-Phase-A v splice", built.terminal_value_wire),
        ] {
            let mut tampered = built.witness.clone();
            tampered[wire] += F128::ONE;
            assert!(!built.r1cs.satisfies(&tampered), "accepted {name} tamper");
        }
    }

    #[test]
    fn complete_phase_b_shape_is_content_and_query_invariant() {
        let left = build_case(&native_case(0xA11C_EB03));
        let right = build_case(&native_case(0xA11C_EB04));
        assert!(left.r1cs.satisfies(&left.witness));
        assert!(right.r1cs.satisfies(&right.witness));
        assert_ne!(left.indices, right.indices);
        assert_eq!(left.trace_rows, right.trace_rows);
        assert_eq!(left.r1cs.useful_rows, right.r1cs.useful_rows);
        assert_eq!(
            left.digest, right.digest,
            "proof contents changed the matrix"
        );
    }

    #[test]
    fn composition_dynamic_preflight_is_complete_and_atomic() {
        let native = native_case(0xA11C_EB05);
        let mut b = FieldR1csBuilder::new();
        let mut input = alloc_input(&mut b, &native);
        input.gamma = const_block256(native.gamma);
        let before = b.num_wires();
        assert!(matches!(
            verify_zk_phase_b_composition_trace(&mut b, &input),
            Err(ZkPhaseBCompositionTraceError::DynamicInputIsConstant {
                input: ZkPhaseBCompositionDynamicInput::Gamma,
                index: 0,
            })
        ));
        assert_eq!(b.num_wires(), before);
    }
}
