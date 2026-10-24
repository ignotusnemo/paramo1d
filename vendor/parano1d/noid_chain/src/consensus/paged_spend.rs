// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Paranoid Zero.

//! Canonical native accounting for an ordered block stream of PagedSpend pages.
//!
//! Proof class and action geometry count physical Tx8x2 pages. Fees, txids and
//! authorizations count complete START..END groups. This module is the single
//! production boundary between those two quantities.

use std::collections::HashSet;

use noid_tx::{validate_paged_spend, PagedSpendError, PagedSpendFacts, Transaction, TxPage};

use super::params::{
    BLOCK_MAX_LIVE_INPUTS, BLOCK_MAX_USER_OUTPUTS, BLOCK_MAX_USER_PAGES, BLOCK_PAGE_CLASS_TIERS,
    MAX_INPUTS, MAX_OUTPUTS,
};

/// The complete launch proof-class ladder, indexed by physical user pages.
pub const BLOCK_PROOF_CLASS_TIERS: [usize; 2] = BLOCK_PAGE_CLASS_TIERS;

/// The only two block proof classes accepted by the launch protocol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockProofClass {
    B25,
    B255,
}

impl BlockProofClass {
    /// Select the unique smallest proof class that holds `page_count` pages.
    pub const fn for_page_count(page_count: usize) -> Option<Self> {
        if page_count <= BLOCK_PROOF_CLASS_TIERS[0] {
            Some(Self::B25)
        } else if page_count <= BLOCK_PROOF_CLASS_TIERS[1] {
            Some(Self::B255)
        } else {
            None
        }
    }

    pub const fn page_capacity(self) -> usize {
        match self {
            Self::B25 => BLOCK_PROOF_CLASS_TIERS[0],
            Self::B255 => BLOCK_PROOF_CLASS_TIERS[1],
        }
    }

    /// Maximum live logical groups/capsules.
    pub const fn live_authorization_capacity(self) -> usize {
        self.page_capacity()
    }

    pub const fn authorization_tile_capacity(self) -> usize {
        match self {
            Self::B25 => 32,
            Self::B255 => 256,
        }
    }

    pub const fn input_capacity(self) -> usize {
        match self {
            Self::B25 => 25 * MAX_INPUTS,
            Self::B255 => BLOCK_MAX_LIVE_INPUTS,
        }
    }

    pub const fn output_capacity(self) -> usize {
        match self {
            Self::B25 => 25 * MAX_OUTPUTS,
            Self::B255 => BLOCK_MAX_USER_OUTPUTS,
        }
    }

    pub const fn outer_m(self) -> usize {
        match self {
            Self::B25 => 22,
            Self::B255 => 24,
        }
    }
}

/// One validated logical group and its exact location in the physical stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PagedSpendGroupFacts {
    pub start_page: u16,
    pub page_count: u16,
    pub spend: PagedSpendFacts,
}

impl PagedSpendGroupFacts {
    #[inline]
    pub fn end_page_exclusive(self) -> usize {
        usize::from(self.start_page) + usize::from(self.page_count)
    }
}

/// Checked class selection and aggregate resource facts for one block stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PagedSpendStreamFacts {
    pub proof_class: BlockProofClass,
    pub groups: Vec<PagedSpendGroupFacts>,
    pub page_count: u16,
    pub logical_count: u16,
    pub live_inputs: u16,
    pub live_outputs: u16,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PagedSpendStreamError {
    Group(PagedSpendError),
    BlockPageLimit {
        actual: usize,
        capacity: usize,
    },
    ProofClassMismatch {
        expected: BlockProofClass,
        actual: BlockProofClass,
    },
    UnterminatedGroup {
        start_page: usize,
    },
    TooManyGroups {
        actual: usize,
        capacity: usize,
    },
    BlockInputLimit {
        actual: usize,
        capacity: usize,
    },
    BlockOutputLimit {
        actual: usize,
        capacity: usize,
    },
    DuplicateInputSlot {
        slot: u32,
    },
    DuplicateOutputSlot {
        slot: u32,
    },
    InputOutputSlotOverlap {
        slot: u32,
    },
}

impl From<PagedSpendError> for PagedSpendStreamError {
    fn from(error: PagedSpendError) -> Self {
        Self::Group(error)
    }
}

impl std::fmt::Display for PagedSpendStreamError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for PagedSpendStreamError {}

trait PageBody {
    fn tx_page(&self) -> TxPage;
    fn page_body(&self) -> &noid_tx::TxBody;
}

impl PageBody for TxPage {
    #[inline]
    fn tx_page(&self) -> TxPage {
        self.clone()
    }

    #[inline]
    fn page_body(&self) -> &noid_tx::TxBody {
        &self.body
    }
}

impl PageBody for Transaction {
    #[inline]
    fn tx_page(&self) -> TxPage {
        TxPage {
            body: self.body.clone(),
        }
    }

    #[inline]
    fn page_body(&self) -> &noid_tx::TxBody {
        &self.body
    }
}

/// Validate a block-facing stream stored in the current fixed-record
/// `Transaction` container. Every element is interpreted as one physical
/// user page, never as an independently balanced transaction.
pub fn validate_paged_spend_transaction_stream(
    pages: &[Transaction],
) -> Result<PagedSpendStreamFacts, PagedSpendStreamError> {
    let class = BlockProofClass::for_page_count(pages.len()).ok_or(
        PagedSpendStreamError::BlockPageLimit {
            actual: pages.len(),
            capacity: BLOCK_MAX_USER_PAGES,
        },
    )?;
    validate_stream_for_class(pages, class)
}

pub fn validate_paged_spend_transaction_stream_for_class(
    pages: &[Transaction],
    proof_class: BlockProofClass,
) -> Result<PagedSpendStreamFacts, PagedSpendStreamError> {
    validate_stream_for_class(pages, proof_class)
}

/// Validate the same canonical stream directly from wallet/mempool pages.
pub fn validate_paged_spend_tx_page_stream(
    pages: &[TxPage],
) -> Result<PagedSpendStreamFacts, PagedSpendStreamError> {
    let class = BlockProofClass::for_page_count(pages.len()).ok_or(
        PagedSpendStreamError::BlockPageLimit {
            actual: pages.len(),
            capacity: BLOCK_MAX_USER_PAGES,
        },
    )?;
    validate_stream_for_class(pages, class)
}

pub fn validate_paged_spend_tx_page_stream_for_class(
    pages: &[TxPage],
    proof_class: BlockProofClass,
) -> Result<PagedSpendStreamFacts, PagedSpendStreamError> {
    validate_stream_for_class(pages, proof_class)
}

fn validate_stream_for_class<T: PageBody>(
    pages: &[T],
    proof_class: BlockProofClass,
) -> Result<PagedSpendStreamFacts, PagedSpendStreamError> {
    if pages.len() > proof_class.page_capacity() {
        return Err(PagedSpendStreamError::BlockPageLimit {
            actual: pages.len(),
            capacity: proof_class.page_capacity(),
        });
    }
    let expected = BlockProofClass::for_page_count(pages.len()).ok_or(
        PagedSpendStreamError::BlockPageLimit {
            actual: pages.len(),
            capacity: BLOCK_MAX_USER_PAGES,
        },
    )?;
    if expected != proof_class {
        return Err(PagedSpendStreamError::ProofClassMismatch {
            expected,
            actual: proof_class,
        });
    }

    let mut groups = Vec::with_capacity(pages.len());
    let mut cursor = 0usize;
    while cursor < pages.len() {
        let start = cursor;
        let Some(relative_end) = pages[start..]
            .iter()
            .position(|page| page.page_body().validity_bitmap & noid_tx::PAGED_SPEND_END_BIT != 0)
        else {
            return Err(PagedSpendStreamError::UnterminatedGroup { start_page: start });
        };
        let end = start + relative_end + 1;
        let group_pages: Vec<_> = pages[start..end].iter().map(PageBody::tx_page).collect();
        let spend = validate_paged_spend(&group_pages)?;
        groups.push(PagedSpendGroupFacts {
            start_page: start as u16,
            page_count: (end - start) as u16,
            spend,
        });
        if groups.len() > proof_class.live_authorization_capacity() {
            return Err(PagedSpendStreamError::TooManyGroups {
                actual: groups.len(),
                capacity: proof_class.live_authorization_capacity(),
            });
        }
        cursor = end;
    }

    let live_inputs = checked_group_sum(&groups, |group| group.spend.live_inputs as usize).ok_or(
        PagedSpendStreamError::BlockInputLimit {
            actual: usize::MAX,
            capacity: proof_class.input_capacity(),
        },
    )?;
    if live_inputs > proof_class.input_capacity() {
        return Err(PagedSpendStreamError::BlockInputLimit {
            actual: live_inputs,
            capacity: proof_class.input_capacity(),
        });
    }

    let live_outputs = checked_group_sum(&groups, |group| group.spend.live_outputs as usize)
        .ok_or(PagedSpendStreamError::BlockOutputLimit {
            actual: usize::MAX,
            capacity: proof_class.output_capacity(),
        })?;
    if live_outputs > proof_class.output_capacity() {
        return Err(PagedSpendStreamError::BlockOutputLimit {
            actual: live_outputs,
            capacity: proof_class.output_capacity(),
        });
    }

    let mut input_slots = HashSet::with_capacity(live_inputs);
    let mut output_slots = HashSet::with_capacity(live_outputs);
    for page in pages {
        for (_, input) in page.page_body().live_inputs() {
            if !input_slots.insert(input.slot_index) {
                return Err(PagedSpendStreamError::DuplicateInputSlot {
                    slot: input.slot_index,
                });
            }
        }
        for (_, output) in page.page_body().live_outputs() {
            if !output_slots.insert(output.slot_index) {
                return Err(PagedSpendStreamError::DuplicateOutputSlot {
                    slot: output.slot_index,
                });
            }
        }
    }
    if let Some(slot) = input_slots.intersection(&output_slots).next() {
        return Err(PagedSpendStreamError::InputOutputSlotOverlap { slot: *slot });
    }

    Ok(PagedSpendStreamFacts {
        proof_class,
        page_count: pages.len() as u16,
        logical_count: groups.len() as u16,
        live_inputs: live_inputs as u16,
        live_outputs: live_outputs as u16,
        groups,
    })
}

fn checked_group_sum(
    groups: &[PagedSpendGroupFacts],
    value: impl Fn(&PagedSpendGroupFacts) -> usize,
) -> Option<usize> {
    groups
        .iter()
        .try_fold(0usize, |sum, group| sum.checked_add(value(group)))
}

const _: () = assert!(BLOCK_PROOF_CLASS_TIERS[0] == 25);
const _: () = assert!(BLOCK_PROOF_CLASS_TIERS[1] == 255);
const _: () = assert!(25 * MAX_INPUTS == 200);
const _: () = assert!(25 * MAX_OUTPUTS == 50);
const _: () = assert!(BLOCK_MAX_LIVE_INPUTS == 1_020);
const _: () = assert!(BLOCK_MAX_USER_OUTPUTS == 510);

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::primitives::Address;
    use noid_tx::{
        output_bitmap_bit, TxBody, TxInput, TxOutput, MAX_PAGED_SPEND_PAGES, PAGED_SPEND_START_BIT,
        TX_INPUTS, TX_OUTPUTS,
    };

    fn one_page(index: usize) -> TxPage {
        let mut inputs = [TxInput::dummy(); TX_INPUTS];
        inputs[0] = TxInput {
            slot_index: index as u32 + 1,
            amount: 10,
            creation_id: index as u64 + 1,
        };
        let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
        outputs[0] = TxOutput {
            slot_index: 10_000 + index as u32,
            amount: 9,
            owner: Address([index as u8; 32]),
        };
        TxPage::new(TxBody {
            epoch_anchor: [index as u8; 32],
            fee: 1,
            input_owner: Address([0x42; 32]),
            inputs,
            outputs,
            validity_bitmap: 1
                | output_bitmap_bit(0)
                | PAGED_SPEND_START_BIT
                | noid_tx::PAGED_SPEND_END_BIT,
            is_coinbase: false,
        })
        .unwrap()
    }

    fn independent_stream(count: usize) -> Vec<TxPage> {
        (0..count).map(one_page).collect()
    }

    fn maximum_group() -> Vec<TxPage> {
        const INPUTS: usize = 1_020;
        const INPUT_AMOUNT: u64 = 1_000;
        const FEE: u64 = 5;
        let owner = Address([0xA5; 32]);
        (0..MAX_PAGED_SPEND_PAGES)
            .map(|page_index| {
                let mut inputs = [TxInput::dummy(); TX_INPUTS];
                let mut outputs = [TxOutput::dummy(); TX_OUTPUTS];
                let mut bitmap = 0u16;
                for (slot, input) in inputs.iter_mut().enumerate() {
                    let index = page_index * TX_INPUTS + slot;
                    if index < INPUTS {
                        *input = TxInput {
                            slot_index: index as u32 + 1,
                            amount: INPUT_AMOUNT,
                            creation_id: index as u64 + 1,
                        };
                        bitmap |= 1 << slot;
                    }
                }
                if page_index == 0 {
                    outputs[0] = TxOutput {
                        slot_index: 1_000_000,
                        amount: INPUTS as u64 * INPUT_AMOUNT - FEE,
                        owner,
                    };
                    bitmap |= output_bitmap_bit(0) | PAGED_SPEND_START_BIT;
                }
                if page_index + 1 == MAX_PAGED_SPEND_PAGES {
                    bitmap |= noid_tx::PAGED_SPEND_END_BIT;
                }
                TxPage::new(TxBody {
                    epoch_anchor: [0x5A; 32],
                    fee: if page_index == 0 { FEE } else { 0 },
                    input_owner: owner,
                    inputs,
                    outputs,
                    validity_bitmap: bitmap,
                    is_coinbase: false,
                })
                .unwrap()
            })
            .collect()
    }

    #[test]
    fn class_boundary_is_exact_at_25_26_and_255() {
        for (count, class) in [
            (0, BlockProofClass::B25),
            (25, BlockProofClass::B25),
            (26, BlockProofClass::B255),
            (255, BlockProofClass::B255),
        ] {
            let facts = validate_paged_spend_tx_page_stream(&independent_stream(count)).unwrap();
            assert_eq!(facts.proof_class, class);
            assert_eq!(facts.page_count as usize, count);
            assert_eq!(facts.logical_count as usize, count);
        }

        assert_eq!(
            validate_paged_spend_tx_page_stream_for_class(
                &independent_stream(25),
                BlockProofClass::B255,
            ),
            Err(PagedSpendStreamError::ProofClassMismatch {
                expected: BlockProofClass::B25,
                actual: BlockProofClass::B255,
            })
        );
        assert_eq!(
            validate_paged_spend_tx_page_stream_for_class(
                &independent_stream(26),
                BlockProofClass::B25,
            ),
            Err(PagedSpendStreamError::BlockPageLimit {
                actual: 26,
                capacity: 25,
            })
        );
        assert_eq!(
            validate_paged_spend_tx_page_stream(&independent_stream(256)),
            Err(PagedSpendStreamError::BlockPageLimit {
                actual: 256,
                capacity: 255,
            })
        );
    }

    #[test]
    fn partial_groups_and_cross_group_conflicts_reject() {
        let mut partial = independent_stream(1);
        partial[0].body.validity_bitmap &= !noid_tx::PAGED_SPEND_END_BIT;
        assert_eq!(
            validate_paged_spend_tx_page_stream(&partial),
            Err(PagedSpendStreamError::UnterminatedGroup { start_page: 0 })
        );

        let mut conflict = independent_stream(2);
        conflict[1].body.inputs[0].slot_index = conflict[0].body.inputs[0].slot_index;
        assert_eq!(
            validate_paged_spend_tx_page_stream(&conflict),
            Err(PagedSpendStreamError::DuplicateInputSlot { slot: 1 })
        );
    }

    #[test]
    fn maximum_group_is_indivisible_and_requires_b255() {
        let group = maximum_group();
        assert_eq!(
            validate_paged_spend_tx_page_stream_for_class(&group, BlockProofClass::B25),
            Err(PagedSpendStreamError::BlockPageLimit {
                actual: 128,
                capacity: 25,
            })
        );
        let facts =
            validate_paged_spend_tx_page_stream_for_class(&group, BlockProofClass::B255).unwrap();
        assert_eq!(facts.logical_count, 1);
        assert_eq!(facts.live_inputs, 1_020);
        assert_eq!(facts.live_outputs, 1);
        assert_eq!(facts.groups[0].start_page, 0);
        assert_eq!(facts.groups[0].page_count, 128);
        assert_eq!(facts.groups[0].end_page_exclusive(), 128);
    }

    #[test]
    fn fixed_transaction_container_has_identical_semantics() {
        let pages = independent_stream(65);
        let transactions: Vec<_> = pages
            .iter()
            .map(|page| Transaction::new(page.body.clone()))
            .collect();
        assert_eq!(
            validate_paged_spend_transaction_stream(&transactions).unwrap(),
            validate_paged_spend_tx_page_stream(&pages).unwrap(),
        );
    }
}
