//! Authenticated local records of wallet views already checked by this client.
use anyhow::{ensure, Context, Result};
use hmac::{Hmac, Mac};
use noid_chain::BlockHeader;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::cell::RefCell;
use zeroize::Zeroizing;

type Authentication = Hmac<Sha256>;
const DOMAIN: &[u8] = b"Paramo1d/checked-wallet-view/1";
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Snapshot {
    release: String,
    address: String,
    tip: String,
    proof: String,
    anchor: String,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sealed {
    snapshot: Snapshot,
    tag: String,
}

fn release() -> Result<String> {
    Ok(hex::encode(Sha256::digest(serde_json::to_vec(
        &crate::artifacts::profile(),
    )?)))
}
fn master(args: &Value) -> Result<Zeroizing<[u8; 32]>> {
    Ok(Zeroizing::new(paramo1d_courier::decode_array(
        args["seed_hex"]
            .as_str()
            .context("Missing wallet identity")?,
    )?))
}

fn record_authenticator(args: &Value, domain: &[u8], bytes: &[u8]) -> Result<Authentication> {
    let seed = master(args)?;
    record_authenticator_with_key(&seed, domain, bytes)
}

fn record_authenticator_with_key(
    seed: &[u8; 32],
    domain: &[u8],
    bytes: &[u8],
) -> Result<Authentication> {
    let mut derive = Authentication::new_from_slice(seed)?;
    derive.update(b"Paramo1d/local-verified-record/key/1");
    derive.update(&(domain.len() as u64).to_le_bytes());
    derive.update(domain);
    let mut key = Zeroizing::new([0u8; 32]);
    key.copy_from_slice(&derive.finalize().into_bytes());
    let mut mac = Authentication::new_from_slice(&*key)?;
    mac.update(release()?.as_bytes());
    mac.update(&(bytes.len() as u64).to_le_bytes());
    mac.update(bytes);
    Ok(mac)
}

thread_local! { static LOCAL_KEY: RefCell<Option<Zeroizing<[u8;32]>>> = const { RefCell::new(None) }; }

pub(crate) fn with_identity<T>(args: &Value, work: impl FnOnce() -> T) -> T {
    struct Restore(Option<Zeroizing<[u8; 32]>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            LOCAL_KEY.with(|key| {
                key.replace(self.0.take());
            });
        }
    }
    let _restore = Restore(LOCAL_KEY.with(|key| key.replace(master(args).ok())));
    work()
}

pub(crate) fn local_tag(domain: &[u8], bytes: &[u8]) -> Result<Option<String>> {
    LOCAL_KEY.with(|key| {
        key.borrow()
            .as_ref()
            .map(|key| {
                record_authenticator_with_key(key, domain, bytes)
                    .map(|mac| hex::encode(mac.finalize().into_bytes()))
            })
            .transpose()
    })
}

pub(crate) fn check_local_tag(domain: &[u8], bytes: &[u8], tag: &str) -> Result<()> {
    LOCAL_KEY.with(|key| {
        let key = key.borrow();
        let key = key
            .as_ref()
            .context("Wallet identity is required for a local checkpoint")?;
        record_authenticator_with_key(key, domain, bytes)?.verify_slice(&hex::decode(tag)?)?;
        Ok(())
    })
}

pub(crate) fn seal_record(args: &Value, domain: &[u8], bytes: &[u8]) -> Result<String> {
    Ok(hex::encode(
        record_authenticator(args, domain, bytes)?
            .finalize()
            .into_bytes(),
    ))
}

pub(crate) fn open_record(args: &Value, domain: &[u8], bytes: &[u8], tag: &str) -> Result<()> {
    record_authenticator(args, domain, bytes)?.verify_slice(&hex::decode(tag)?)?;
    Ok(())
}
fn address(seed: &[u8; 32]) -> String {
    noid_poseidon2b::primitives::derive_address(&crate::courier_api::spend_secret(seed, 0))
        .to_bech32()
}
fn authenticator(seed: &[u8; 32], snapshot: &Snapshot) -> Result<Authentication> {
    let mut derive = Authentication::new_from_slice(seed)?;
    derive.update(b"Paramo1d/checked-wallet-view/key/1");
    let mut key = Zeroizing::new([0u8; 32]);
    key.copy_from_slice(&derive.finalize().into_bytes());
    let mut mac = Authentication::new_from_slice(&*key)?;
    mac.update(DOMAIN);
    mac.update(&serde_json::to_vec(snapshot)?);
    Ok(mac)
}
fn header(encoded: &str) -> Result<BlockHeader> {
    ensure!(
        encoded.len() == noid_chain::wire::BLOCK_HEADER_WIRE_SIZE * 2,
        "Wallet checkpoint header length"
    );
    let bytes = hex::decode(encoded)?;
    let mut input = bytes.as_slice();
    let header = BlockHeader::decode(&mut input)
        .map_err(|e| anyhow::anyhow!("Wallet checkpoint header: {e:?}"))?;
    ensure!(input.is_empty(), "Wallet checkpoint header framing");
    Ok(header)
}
pub(crate) fn seal(
    args: &Value,
    tip: &BlockHeader,
    proof: &BlockHeader,
    anchor: &BlockHeader,
) -> Result<Value> {
    ensure!(proof.height <= tip.height, "Wallet checkpoint proof height");
    ensure!(
        anchor.height == noid_chain::consensus::tx_epoch_anchor_height_for_child(tip.height + 1),
        "Wallet checkpoint epoch"
    );
    let seed = master(args)?;
    let snapshot = Snapshot {
        release: release()?,
        address: address(&seed),
        tip: hex::encode(tip.to_bytes()),
        proof: hex::encode(proof.to_bytes()),
        anchor: hex::encode(anchor.to_bytes()),
    };
    let tag = hex::encode(authenticator(&seed, &snapshot)?.finalize().into_bytes());
    Ok(serde_json::to_value(Sealed { snapshot, tag })?)
}
pub(crate) fn open(args: &Value, value: &Value) -> Result<(BlockHeader, BlockHeader, BlockHeader)> {
    let sealed: Sealed = serde_json::from_value(value.clone())?;
    ensure!(
        sealed.snapshot.release == release()?,
        "Wallet checkpoint release"
    );
    let seed = master(args)?;
    ensure!(
        sealed.snapshot.address == address(&seed),
        "Wallet checkpoint identity"
    );
    authenticator(&seed, &sealed.snapshot)?.verify_slice(&hex::decode(&sealed.tag)?)?;
    let tip = header(&sealed.snapshot.tip)?;
    let proof = header(&sealed.snapshot.proof)?;
    let anchor = header(&sealed.snapshot.anchor)?;
    ensure!(
        proof.height <= tip.height
            && anchor.height
                == noid_chain::consensus::tx_epoch_anchor_height_for_child(tip.height + 1),
        "Wallet checkpoint boundary"
    );
    Ok((tip, proof, anchor))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn checkpoint_binds_identity_release_and_every_header() {
        let args = serde_json::json!({"seed_hex":hex::encode([7u8;32])});
        let header = noid_chain::consensus::genesis::genesis_header();
        let saved = seal(&args, &header, &header, &header).unwrap();
        assert_eq!(open(&args, &saved).unwrap(), (header, header, header));
        assert!(open(
            &serde_json::json!({"seed_hex":hex::encode([8u8;32])}),
            &saved
        )
        .is_err());
        for field in ["tip", "proof", "anchor", "release", "address"] {
            let mut changed = saved.clone();
            let text = changed["snapshot"][field].as_str().unwrap().to_owned();
            changed["snapshot"][field] = Value::String(format!(
                "{}{}",
                if &text[..1] == "0" { "1" } else { "0" },
                &text[1..]
            ));
            assert!(open(&args, &changed).is_err(), "changed {field}");
        }
        let mut changed = saved.clone();
        changed["tag"] = Value::String("00".repeat(32));
        assert!(open(&args, &changed).is_err());
    }
}
