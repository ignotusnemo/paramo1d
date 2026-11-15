//! An exact wallet projection of a verified State and its subsequent block bodies.
use anyhow::{ensure, Context, Result};
use noid_chain::{
    block::{
        native_assets::{validate_scheduled_block_page_stream, ScheduledSpendKind},
        payload::BlockBodyPayload,
    },
    block_header::{block_id, BlockHeader},
    fri_state::SlotValue,
};
use noid_poseidon2b::primitives::Address;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::collections::BTreeMap;

const DOMAIN: &[u8] = b"Paramo1d/verified-p2p-wallet/1";
const MAX_COINS: usize = 4096;
const EMPTY_RESERVE: usize = 32;

/// A body whose exact header, scheduled layout and transaction root agree.
pub(crate) struct CheckedBody {
    payload: BlockBodyPayload,
    pub(crate) wire_bytes: usize,
}

impl CheckedBody {
    pub(crate) fn decode(bytes: &[u8], expected: BlockHeader) -> Result<Self> {
        let payload = BlockBodyPayload::decode(bytes)
            .map_err(|e| anyhow::anyhow!("P2P block decode: {e:?}"))?;
        ensure!(
            payload.block().header == expected,
            "P2P block header mismatch"
        );
        Self::check_root(&payload)?;
        Ok(Self {
            payload,
            wire_bytes: bytes.len(),
        })
    }
    fn check_root(payload: &BlockBodyPayload) -> Result<()> {
        let block = payload.block();
        let stream = validate_scheduled_block_page_stream(&block.transactions, block.header.height)
            .map_err(|e| anyhow::anyhow!("Wallet block layout: {e}"))?;
        let hashes = stream
            .logical_txids(&block.transactions)
            .into_iter()
            .map(|v| v.0)
            .collect::<Vec<_>>();
        ensure!(
            noid_chain::tx_tree::root_from_hashes(&hashes) == block.header.tx_root,
            "Wallet block transaction root"
        );
        Ok(())
    }
    pub(crate) fn payload(&self) -> &BlockBodyPayload {
        &self.payload
    }
}

#[derive(Clone)]
pub(crate) struct WalletView {
    pub(crate) header: BlockHeader,
    pub(crate) address: Address,
    pub(crate) slots: BTreeMap<u32, SlotValue>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Record {
    version: u8,
    address: String,
    header: String,
    slots: Vec<crate::mobile_wallet::Slot>,
}

pub(crate) fn owner(value: SlotValue) -> Address {
    let mut a = [0; 32];
    a[..16].copy_from_slice(&value.owner_hi.0.to_le_bytes());
    a[16..].copy_from_slice(&value.owner_lo.0.to_le_bytes());
    Address(a)
}

fn ordinary(value: SlotValue) -> bool {
    !value.is_empty() && noid_tx::native_assets::native_sequence(value.creation_id()).is_err()
}

impl WalletView {
    pub(crate) fn from_proofs(
        header: BlockHeader,
        address: Address,
        proofs: &[crate::mobile_wallet::Proof],
    ) -> Result<Self> {
        let mut slots = BTreeMap::new();
        for proof in proofs {
            for (index, slot) in crate::mobile_wallet::verify_proof(&header, proof)? {
                if slot.is_empty() || ordinary(slot) && owner(slot) == address {
                    slots.insert(index, slot);
                }
            }
        }
        let result = Self {
            header,
            address,
            slots,
        };
        result.validate()?;
        Ok(result)
    }

    pub(crate) fn coin_set(&self) -> BTreeMap<u32, (u64, u64)> {
        self.slots
            .iter()
            .filter(|(_, v)| !v.is_empty())
            .map(|(&i, v)| (i, (v.amount(), v.creation_id())))
            .collect()
    }

    fn validate(&self) -> Result<()> {
        ensure!(
            (1..=32).contains(&self.header.log_slots),
            "Wallet State depth"
        );
        ensure!(
            self.slots.len() <= MAX_COINS + EMPTY_RESERVE && self.coin_set().len() <= MAX_COINS,
            "Wallet State input budget"
        );
        ensure!(
            self.slots
                .iter()
                .all(|(&i, v)| u64::from(i) < (1u64 << self.header.log_slots)
                    && (v.is_empty()
                        || ordinary(*v)
                            && owner(*v) == self.address
                            && noid_chain::consensus::params::creation_id_within_boundary(
                                v.creation_id(),
                                self.header.alloc_counter,
                                self.header.height
                            ))),
            "Wallet State slot boundary"
        );
        Ok(())
    }

    /// The caller binds every body to the accepted header prefix and verifies
    /// its terminal State proof before persisting or displaying this projection.
    /// Watching an unverified extension may only schedule that verification.
    pub(crate) fn apply_checked(&mut self, body: &CheckedBody) -> Result<()> {
        self.apply_payload(body.payload())
    }

    #[cfg(test)]
    pub(crate) fn apply(&mut self, payload: &BlockBodyPayload) -> Result<()> {
        CheckedBody::check_root(payload)?;
        self.apply_payload(payload)
    }

    fn apply_payload(&mut self, payload: &BlockBodyPayload) -> Result<()> {
        let block = payload.block();
        let header = block.header;
        ensure!(
            header.height == self.header.height + 1
                && header.prev_block_hash == block_id(&self.header),
            "Wallet block continuity"
        );
        ensure!(
            header.log_slots == self.header.log_slots
                || header.log_slots == self.header.log_slots + 1,
            "Wallet State depth transition"
        );
        let stream = validate_scheduled_block_page_stream(&block.transactions, header.height)
            .map_err(|e| anyhow::anyhow!("Wallet block layout: {e}"))?;
        let mut allocator = self.header.alloc_counter;
        let mut live = self.header.active_slot_count;
        for tx in &block.transactions[..stream.user_start_index()] {
            self.body(
                &tx.body,
                None,
                header.height,
                header.log_slots,
                &mut allocator,
                &mut live,
                &mut 0,
            )?;
        }
        for group in stream.groups() {
            let (start, facts) = match group.kind {
                ScheduledSpendKind::Ordinary(_) => (group.body_start, None),
                ScheduledSpendKind::Native(facts) => (group.body_start + 1, Some(facts)),
            };
            let mut output = 0;
            for tx in &block.transactions[start..group.body_start + group.page_count] {
                self.body(
                    &tx.body,
                    facts,
                    header.height,
                    header.log_slots,
                    &mut allocator,
                    &mut live,
                    &mut output,
                )?;
            }
        }
        ensure!(
            allocator == header.alloc_counter && live == header.active_slot_count,
            "Wallet State counters"
        );
        self.header = header;
        self.validate()
    }

    #[allow(clippy::too_many_arguments)]
    fn body(
        &mut self,
        body: &noid_tx::TxBody,
        native: Option<&noid_tx::native_assets::wire::NativePageFacts>,
        height: u64,
        depth: u32,
        allocator: &mut u64,
        live: &mut u64,
        output_index: &mut usize,
    ) -> Result<()> {
        for (_, input) in body.live_inputs() {
            ensure!(
                u64::from(input.slot_index) < (1u64 << depth),
                "Wallet input domain"
            );
            *live = live.checked_sub(1).context("Wallet live count underflow")?;
            let ordinary_input =
                noid_tx::native_assets::native_sequence(input.creation_id).is_err();
            if ordinary_input && body.input_owner == self.address {
                let old = self
                    .slots
                    .remove(&input.slot_index)
                    .context("Wallet input absent from complete view")?;
                ensure!(
                    !old.is_empty()
                        && old.amount() == input.amount
                        && old.creation_id() == input.creation_id
                        && owner(old) == body.input_owner,
                    "Wallet input identity"
                );
            } else {
                ensure!(
                    self.slots
                        .get(&input.slot_index)
                        .is_none_or(|s| s.is_empty()),
                    "Wallet input owner conflict"
                );
            }
            if self.slots.values().filter(|v| v.is_empty()).count() < EMPTY_RESERVE {
                self.slots.insert(input.slot_index, SlotValue::EMPTY);
            }
        }
        for (_, output) in body.live_outputs() {
            ensure!(
                u64::from(output.slot_index) < (1u64 << depth),
                "Wallet output domain"
            );
            ensure!(
                self.slots
                    .get(&output.slot_index)
                    .is_none_or(|s| s.is_empty()),
                "Wallet output occupied"
            );
            self.slots.remove(&output.slot_index);
            *allocator = allocator
                .checked_add(1)
                .context("Wallet allocator overflow")?;
            *live = live.checked_add(1).context("Wallet live count overflow")?;
            let native_output = native.is_some_and(|f| f.output_is_native(*output_index));
            let id = if native_output {
                noid_tx::native_assets::native_creation_id(*allocator)
                    .map_err(|e| anyhow::anyhow!("Wallet native incarnation: {e}"))?
            } else if body.is_primary_coinbase_shape() {
                noid_chain::consensus::params::coinbase_creation_id(height)
            } else {
                *allocator
            };
            *output_index += 1;
            if !native_output && output.owner == self.address {
                self.slots.insert(
                    output.slot_index,
                    SlotValue::with_owner_fields(output.amount, id, output.owner.as_fields()),
                );
                ensure!(
                    self.slots.len() <= MAX_COINS + EMPTY_RESERVE,
                    "Wallet input budget"
                );
            }
        }
        Ok(())
    }

    pub(crate) fn seal(&self, args: &Value) -> Result<Value> {
        self.validate()?;
        let slots = self
            .slots
            .iter()
            .map(|(&index, &slot)| crate::mobile_wallet::Slot {
                slot_index: index,
                value: slot.amount(),
                creation_id: slot.creation_id(),
                owner: if slot.is_empty() {
                    String::new()
                } else {
                    self.address.to_bech32()
                },
                empty: slot.is_empty(),
            })
            .collect();
        let record = Record {
            version: 1,
            address: self.address.to_bech32(),
            header: hex::encode(self.header.to_bytes()),
            slots,
        };
        let tag =
            crate::wallet_checkpoint::seal_record(args, DOMAIN, &serde_json::to_vec(&record)?)?;
        Ok(json!({"record":record,"tag":tag}))
    }

    pub(crate) fn open(args: &Value, address: Address, sealed: &Value) -> Result<Self> {
        let record: Record = serde_json::from_value(sealed["record"].clone())?;
        ensure!(
            record.version == 1
                && record.address == address.to_bech32()
                && record.slots.len() <= MAX_COINS + EMPTY_RESERVE,
            "Wallet record identity"
        );
        crate::wallet_checkpoint::open_record(
            args,
            DOMAIN,
            &serde_json::to_vec(&record)?,
            sealed["tag"].as_str().context("Wallet record tag")?,
        )?;
        let header = noid_chain::storage::serial::decode_header(&hex::decode(&record.header)?)
            .context("Wallet record header")?;
        let mut slots = BTreeMap::new();
        let mut previous = None;
        for slot in record.slots {
            ensure!(
                previous.is_none_or(|i| i < slot.slot_index),
                "Wallet record slot order"
            );
            previous = Some(slot.slot_index);
            let value = if slot.empty {
                ensure!(
                    slot.value == 0 && slot.creation_id == 0 && slot.owner.is_empty(),
                    "Wallet empty slot record"
                );
                SlotValue::EMPTY
            } else {
                ensure!(slot.owner == record.address, "Wallet record owner");
                SlotValue::with_owner_fields(slot.value, slot.creation_id, address.as_fields())
            };
            slots.insert(slot.slot_index, value);
        }
        let result = Self {
            header,
            address,
            slots,
        };
        result.validate()?;
        Ok(result)
    }
}
