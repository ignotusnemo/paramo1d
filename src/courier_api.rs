//! Local application bridge. Secret-bearing requests stay inside the native host.

use anyhow::{ensure, Context, Result};
use base64::{engine::general_purpose::URL_SAFE_NO_PAD, Engine};
use noid_core::Block128;
use noid_poseidon2b::{
    native::compression::Poseidon2bSponge,
    primitives::{derive_address, SpendSecret},
};
use paramo1d_courier::{decode_array, Contact, Destination, Envelope, Identity, Message};
use serde_json::{json, Value};
use std::{
    ffi::{c_char, CString},
    path::{Path, PathBuf},
};
use zeroize::{Zeroize, Zeroizing};

pub const MAX_REQUEST: usize = 70 * 1024 * 1024;
pub fn spend_secret(seed: &[u8; 32], index: u32) -> SpendSecret {
    let mut fields = Zeroizing::new([
        Block128(u128::from_le_bytes(seed[..16].try_into().unwrap())),
        Block128(u128::from_le_bytes(seed[16..].try_into().unwrap())),
    ]);
    let mut sponge = Poseidon2bSponge::with_iv([Block128(0); 2]);
    sponge.absorb(fields[0]);
    sponge.absorb(fields[1]);
    fields.zeroize();
    sponge.absorb(Block128(index as u128));
    sponge.absorb(Block128(0x6E6F69642D64657269));
    let mut result = Zeroizing::new(sponge.finalize());
    let secret = SpendSecret::from_bytes(*result);
    result.zeroize();
    secret
}
fn text<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value[key]
        .as_str()
        .with_context(|| format!("Missing {key}"))
}
fn path(value: &Value, key: &str) -> Result<PathBuf> {
    Ok(PathBuf::from(text(value, key)?))
}
fn seed(value: &Value) -> Result<Zeroizing<[u8; 32]>> {
    Ok(Zeroizing::new(decode_array(text(value, "seed_hex")?)?))
}
fn now(value: &Value) -> Result<u64> {
    value["now_ms"].as_u64().context("Missing clock")
}

pub fn dispatch(request: &Value) -> Result<Value> {
    match text(request, "op")? {
        "node_trim_memory" => {
            crate::artifacts::matrix_cache_budget(0);
            Ok(json!({"trimmed":true}))
        }
        "node_status" => Ok(json!({"phase":crate::mobile_control::phase()})),
        "node_active" => {
            let active = request["active"]
                .as_bool()
                .context("Missing activity state")?;
            crate::mobile_control::set_active(active);
            Ok(json!({"active":active}))
        }
        "profile" => {
            noid_core::cpu::ensure_production_hardware()?;
            let seed = seed(request)?;
            let identity = Identity::from_seed(&seed);
            let address = derive_address(&spend_secret(&seed, 0)).to_bech32();
            let contact = identity.contact(text(request, "name")?.to_string(), address)?;
            Ok(json!({"contact":contact,"invite":identity.invite(&contact)?}))
        }
        "contact_import" => {
            Ok(json!({"contact":paramo1d_courier::import_contact(text(request,"uri")?)?}))
        }
        "qr_parse" => crate::qr::parse(text(request, "kind")?, text(request, "text")?),
        "verify_envelope" => {
            let envelope: Envelope = serde_json::from_value(request["envelope"].clone())?;
            envelope.verify(now(request)?)?;
            if let Destination::Group { room } = &envelope.data.destination {
                ensure!(room == paramo1d_courier::LOBBY, "Unknown community channel");
            }
            Ok(
                json!({"id":envelope.id,"sender":envelope.data.sender,"destination":envelope.data.destination}),
            )
        }
        "verify_link" => {
            paramo1d_courier::verify_read(
                text(request, "id")?,
                text(request, "path")?,
                request["time_ms"].as_u64().context("Missing link time")?,
                text(request, "signature")?,
                now(request)?,
            )?;
            Ok(json!({"verified":true}))
        }
        "link_encrypt" => {
            let key = seed(request)?;
            let identity = Identity::from_seed(&key);
            let peer: Contact = serde_json::from_value(request["contact"].clone())?;
            Ok(
                json!({"packet":URL_SAFE_NO_PAD.encode(identity.seal_link(&peer,text(request,"context")?,request["frame"].clone())?)}),
            )
        }
        "link_decrypt" => {
            let key = seed(request)?;
            let identity = Identity::from_seed(&key);
            let peer: Contact = serde_json::from_value(request["contact"].clone())?;
            Ok(
                json!({"frame":identity.open_link(&peer,text(request,"context")?,&URL_SAFE_NO_PAD.decode(text(request,"packet")?)?)?}),
            )
        }
        "seal" => {
            let seed = seed(request)?;
            let identity = Identity::from_seed(&seed);
            let sender: Contact = serde_json::from_value(request["sender"].clone())?;
            let destination: Destination = serde_json::from_value(request["destination"].clone())?;
            let message: Message = serde_json::from_value(request["message"].clone())?;
            ensure!(
                !matches!(destination, Destination::Group { .. })
                    || matches!(
                        message,
                        Message::Text { .. }
                            | Message::Transaction { .. }
                            | Message::RelayUpdate { .. }
                    ),
                "Invoices and receipts belong in direct chats"
            );
            Ok(json!({"envelope":identity.seal(sender,destination,message,now(request)?)?}))
        }
        "open" => {
            let seed = seed(request)?;
            let identity = Identity::from_seed(&seed);
            let envelope: Envelope = serde_json::from_value(request["envelope"].clone())?;
            Ok(
                json!({"message":identity.open(&envelope,now(request)?)?,"sender":envelope.data.sender,"id":envelope.id}),
            )
        }
        "read_auth" => {
            let seed = seed(request)?;
            let identity = Identity::from_seed(&seed);
            let clock = now(request)?;
            Ok(
                json!({"signature":identity.read_authorization(text(request,"path")?,clock),"time_ms":clock.to_string()}),
            )
        }
        "amount" => Ok(
            json!({"micronoid":paramo1d_courier::amount_micronoid(text(request,"amount")?)?.to_string()}),
        ),
        "backup_encrypt" => Ok(
            json!({"backup":paramo1d_courier::encrypt_backup(text(request,"data")?.as_bytes(),text(request,"password")?)?}),
        ),
        "backup_decrypt" => {
            let plain = paramo1d_courier::decrypt_backup(
                text(request, "backup")?,
                text(request, "password")?,
            )?;
            Ok(json!({"data":serde_json::from_slice::<Value>(&plain)?}))
        }
        "invoice_address" => {
            let seed = seed(request)?;
            let index = request["index"].as_u64().context("Missing address index")?;
            ensure!(
                index > 0 && index <= 100000,
                "Address index outside wallet range"
            );
            Ok(json!({"address":derive_address(&spend_secret(&seed,index as u32)).to_bech32()}))
        }
        "sync_once" => crate::mobile::run(
            path(request, "artifacts")?,
            path(request, "data_dir")?,
            true,
        ),
        "route_set" => {
            let port = request["port"].as_u64().map(u16::try_from).transpose()?;
            crate::network_route::set(port, request["token"].as_str().unwrap_or(""))?;
            Ok(json!({"protected":port.is_some()}))
        }
        "wallet_sync" => crate::mobile_wallet::synchronize(request),
        "payment_preview" => crate::mobile_wallet::prepare(request),
        "payment_authorize" => crate::mobile_wallet::authorize(request),
        "transaction_status" => transaction_status(request),
        "receipt_check" => check_receipt(request),
        "broadcast_preview" => inspect_intent(text(request, "intent_hex")?),
        "broadcast_send" => {
            let preview = inspect_intent(text(request, "intent_hex")?)?;
            ensure!(
                preview["txid"].as_str() == Some(text(request, "txid")?),
                "Payment differs from the inspected transaction"
            );
            let mut rpc = crate::rpc::Rpc::new(text(request, "rpc")?)?;
            let result = match rpc.call("submitTxIntent", json!([text(request, "intent_hex")?])) {
                Ok(result) => result,
                Err(error) if error.to_string().contains("BadEpochAnchor") => {
                    let txid = text(request, "txid")?;
                    // A previously included payment can outlive its admission epoch.
                    // A lookup remains a hint until its receipt is checked locally.
                    let included = rpc.call("getTx", json!([txid]))?;
                    if !included.is_null() {
                        return Ok(
                            json!({"submitted":true,"txid":txid,"confirmed":false,"already_known":true}),
                        );
                    }
                    return Err(error);
                }
                Err(error) => return Err(error),
            };
            ensure!(
                result.as_str() == preview["txid"].as_str(),
                "Node returned a different transaction ID"
            );
            Ok(json!({"submitted":true,"txid":result,"confirmed":false}))
        }
        _ => anyhow::bail!("Unknown application operation"),
    }
}

pub fn inspect_intent(encoded: &str) -> Result<Value> {
    noid_core::cpu::ensure_production_hardware()?;
    use noid_gkr::wallet_authorization::{
        verify_paged_spend_authorization, WalletAuthorizationBundle,
    };
    ensure!(
        encoded.len() <= 2 * noid_tx::MAX_PAGED_SPEND_INTENT_BYTES,
        "Payment exceeds wire limit"
    );
    let intent = noid_tx::PagedSpendIntent::from_bytes(&hex::decode(encoded)?)
        .map_err(|e| anyhow::anyhow!("Invalid payment: {e}"))?;
    ensure!(
        intent.pages.len() <= 63,
        "Payment exceeds the current mobile page budget"
    );
    ensure!(
        intent.pages.iter().all(|p| p.body.validity_bitmap
            & (noid_tx::PAGED_SPEND_V2_CONTRACT_MASK
                | noid_tx::native_assets::wire::NATIVE_HEADER_BIT
                | noid_tx::native_assets::wire::NATIVE_PAGE_BIT)
            == 0),
        "This application supports ordinary NOID payments"
    );
    let authorization = WalletAuthorizationBundle::from_bytes(&intent.authorization_bytes)
        .map_err(|e| anyhow::anyhow!("Invalid authorization: {e}"))?;
    verify_paged_spend_authorization(&intent.pages, &authorization)
        .map_err(|e| anyhow::anyhow!("Payment authorization rejected: {e}"))?;
    let fee = intent
        .pages
        .iter()
        .try_fold(0u64, |total, p| total.checked_add(p.body.fee))
        .context("Payment fee overflow")?;
    let outputs=intent.pages.iter().flat_map(|p|p.body.live_outputs().map(|(_,o)|json!({"address":o.owner.to_bech32(),"amount_micronoid":o.amount.to_string()}))).collect::<Vec<_>>();
    Ok(
        json!({"authorized":true,"txid":hex::encode(intent.logical_txid().0),"fee":format!("{}.{:06}",fee/1_000_000,fee%1_000_000),"outputs":outputs,"epoch_anchor":hex::encode(intent.pages[0].body.epoch_anchor)}),
    )
}

fn transaction_status(request: &Value) -> Result<Value> {
    let txid = text(request, "txid")?;
    decode_array::<32>(txid)?;
    let mut rpc = crate::rpc::Rpc::new(text(request, "rpc")?)?;
    let location = rpc.call("getTx", json!([txid]))?;
    if location.is_null() {
        let pending = rpc.call("getMempoolEntry", json!([txid]))?;
        return Ok(
            json!({"txid":txid,"stage":if pending.is_null(){"unknown"}else{"in_mempool"},"receipt_hex":null}),
        );
    }
    ensure!(
        location["tx_hash"].as_str() == Some(txid),
        "Transaction lookup identity mismatch"
    );
    let height = location["height"]
        .as_u64()
        .context("Missing transaction height")?;
    let raw = rpc.call("getBlock", json!([height]))?;
    let Some(raw) = raw.as_str() else {
        return Ok(json!({"txid":txid,"stage":"body_pruned","receipt_hex":null}));
    };
    ensure!(
        raw.len() <= 4 * 1024 * 1024,
        "Block exceeds receipt collection limit"
    );
    let payload = noid_chain::block::payload::BlockBodyPayload::decode(&hex::decode(raw)?)
        .map_err(|e| anyhow::anyhow!("Block payload rejected: {e}"))?;
    let block = payload.block();
    ensure!(
        block.header.height == height
            && location["block_hash"].as_str()
                == Some(hex::encode(noid_chain::block_header::block_id(&block.header)).as_str()),
        "Receipt block identity mismatch"
    );
    let stream = noid_chain::block::native_assets::validate_scheduled_block_page_stream(
        &block.transactions,
        height,
    )
    .map_err(|e| anyhow::anyhow!("Block transaction layout rejected: {e}"))?;
    let hashes = stream
        .logical_txids(&block.transactions)
        .iter()
        .map(|v| v.0)
        .collect::<Vec<_>>();
    ensure!(
        noid_chain::tx_tree::root_from_hashes(&hashes) == block.header.tx_root,
        "Block transaction commitment mismatch"
    );
    let (index, group) = stream
        .groups()
        .enumerate()
        .find(|(_, g)| hex::encode(g.logical_txid().0) == txid)
        .context("Transaction missing from block")?;
    let position = stream.user_start_index() + index;
    ensure!(
        location["tx_position"].as_u64() == Some(position as u64),
        "Transaction position mismatch"
    );
    let receipt = noid_chain::consensus::receipt::generate_receipt(
        &block.header,
        &block.transactions[group.body_start..group.body_start + group.page_count],
        position,
        &hashes,
    );
    ensure!(
        noid_chain::consensus::receipt::verify_merkle_inclusion(&receipt),
        "Collected receipt failed inclusion verification"
    );
    Ok(
        json!({"txid":txid,"stage":"included","receipt_hex":hex::encode(receipt.to_bytes()),"height":height,"canonical_verified_locally":false}),
    )
}

fn check_receipt(request: &Value) -> Result<Value> {
    use noid_chain::consensus::receipt::{
        verify_against_header, verify_merkle_inclusion, ParanoidReceipt,
    };
    let encoded = text(request, "receipt_hex")?;
    ensure!(encoded.len() <= 262144, "Receipt exceeds payment limit");
    let receipt =
        ParanoidReceipt::from_bytes(&hex::decode(encoded)?).context("Invalid payment receipt")?;
    ensure!(
        verify_merkle_inclusion(&receipt),
        "Receipt inclusion failed"
    );
    if let Some(expected) = request["expected_txid"].as_str() {
        ensure!(
            hex::encode(receipt.summary.logical_txid) == expected,
            "Receipt belongs to another payment"
        );
    } else {
        let recipient = noid_poseidon2b::primitives::Address::parse(text(request, "address")?)
            .map_err(|e| anyhow::anyhow!("Invalid recipient: {e}"))?;
        let amount = paramo1d_courier::amount_micronoid(text(request, "amount")?)?;
        ensure!(
            receipt
                .summary
                .outputs
                .iter()
                .any(|(_, value, owner)| *owner == recipient && *value == amount),
            "Receipt does not pay this invoice"
        );
    }
    let mut bundle = path(request, "bundle")?;
    let mut state = crate::verifier_session::verify(&path(request, "artifacts")?, &bundle)?;
    if receipt.claimed_height > state.height() && request["data_dir"].as_str().is_some() {
        crate::mobile::run(
            path(request, "artifacts")?,
            path(request, "data_dir")?,
            true,
        )?;
        bundle = accepted_bundle(&path(request, "data_dir")?)?;
        state = crate::verifier_session::verify(&path(request, "artifacts")?, &bundle)?;
    }
    ensure!(
        receipt.claimed_height <= state.height(),
        "Synchronize to verify this payment"
    );
    let header = crate::verifier_session::header(
        &path(request, "artifacts")?,
        &bundle,
        receipt.claimed_height,
    )?;
    ensure!(
        verify_against_header(&receipt, &header),
        "Receipt is outside the verified chain"
    );
    let confirmations = state.height() - receipt.claimed_height + 1;
    Ok(
        json!({"verified":true,"txid":hex::encode(receipt.summary.logical_txid),"height":receipt.claimed_height,"confirmations":confirmations,"finalized":state.height().saturating_sub(noid_chain::consensus::params::CONSENSUS_FINALITY_DEPTH)>=receipt.claimed_height,"amount":request["amount"]}),
    )
}

pub fn execute(bytes: &[u8]) -> Value {
    let result = (|| {
        ensure!(
            bytes.len() <= MAX_REQUEST,
            "Application request exceeds limit"
        );
        let request: Value = serde_json::from_slice(bytes)?;
        ensure!(
            matches!(
                request["op"].as_str(),
                Some("backup_encrypt" | "backup_decrypt")
            ) || bytes.len() <= 2 * 1024 * 1024,
            "Application request exceeds message limit"
        );
        if matches!(
            request["op"].as_str(),
            Some(
                "wallet_sync"
                    | "sync_once"
                    | "payment_preview"
                    | "payment_authorize"
                    | "receipt_check"
            )
        ) {
            crate::mobile_control::run(|| dispatch(&request))
        } else {
            dispatch(&request)
        }
    })();
    match result {
        Ok(value) => json!({"ok":true,"result":value}),
        Err(error) => json!({"ok":false,"error":error.to_string()}),
    }
}

/// The caller owns the returned JSON and frees it through paramo1d_free_json.
/// # Safety
/// `data` must point to `length` readable bytes.
#[no_mangle]
pub unsafe extern "C" fn paramo1d_courier_json(data: *const u8, length: usize) -> *mut c_char {
    let value = if data.is_null() || length > MAX_REQUEST {
        json!({"ok":false,"error":"Invalid application request"})
    } else {
        std::panic::catch_unwind(|| execute(unsafe { std::slice::from_raw_parts(data, length) }))
            .unwrap_or_else(|_| json!({"ok":false,"error":"Application operation failed"}))
    };
    CString::new(value.to_string())
        .expect("JSON escapes NUL")
        .into_raw()
}

#[cfg(target_os = "android")]
#[no_mangle]
pub extern "system" fn Java_org_parano1d_courier_NativeCore_call(
    mut env: jni::JNIEnv,
    _class: jni::objects::JClass,
    request: jni::objects::JString,
) -> jni::sys::jstring {
    if let Err(error) = crate::ensure_verification_hardware() {
        let output = json!({"ok":false,"error":error.to_string()}).to_string();
        return env
            .new_string(output)
            .map_or(std::ptr::null_mut(), |s| s.into_raw());
    }
    let output = match env.get_string(&request) {
        Ok(value) => {
            let input = Zeroizing::new(value.to_string_lossy().into_owned());
            std::panic::catch_unwind(|| execute(input.as_bytes()))
                .unwrap_or_else(|_| json!({"ok":false,"error":"Native operation failed"}))
                .to_string()
        }
        Err(_) => "{\"ok\":false,\"error\":\"Invalid native request\"}".into(),
    };
    env.new_string(output)
        .map_or(std::ptr::null_mut(), |s| s.into_raw())
}

pub fn accepted_bundle(directory: &Path) -> Result<PathBuf> {
    let bytes = crate::artifacts::read_bounded(&directory.join("accepted.json"), 1024 * 1024)?;
    let saved: Value = serde_json::from_slice(&bytes)?;
    let name = text(&saved, "bundle")?;
    ensure!(
        name.starts_with("candidate-")
            && name.len() < 128
            && !name.contains('/')
            && !name.contains('\\'),
        "Invalid accepted bundle location"
    );
    Ok(directory.join(name))
}
