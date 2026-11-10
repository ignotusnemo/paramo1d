//! Versioned public-room messages and authenticated encrypted direct envelopes.

use anyhow::{bail, ensure, Context, Result};
use base64::{engine::general_purpose::URL_SAFE_NO_PAD, Engine};
use crypto_box::{aead::Aead, PublicKey, SalsaBox, SecretKey};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use hkdf::Hkdf;
use rand::{rngs::OsRng, RngCore};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use zeroize::Zeroizing;

pub const VERSION: u8 = 1;
pub const MAX_TEXT: usize = 4096;
pub const MAX_ENVELOPE: usize = 1024 * 1024;
pub const MAX_LIFETIME_MS: u64 = 7 * 24 * 60 * 60 * 1000;
pub const CLOCK_SKEW_MS: u64 = 5 * 60 * 1000;
pub const LOBBY: &str = "parano1d";
const DOMAIN: &[u8] = b"Paramo1d/Courier/envelope/1\0";

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Contact {
    pub id: String,
    pub box_key: String,
    pub name: String,
    pub address: String,
}

impl Contact {
    pub fn validate(&self) -> Result<()> {
        let key = decode_array::<32>(&self.id)?;
        ensure!(
            !VerifyingKey::from_bytes(&key)?.is_weak(),
            "Invalid contact identity"
        );
        ensure!(
            decode_array::<32>(&self.box_key)? != [0; 32],
            "Invalid encryption key"
        );
        ensure!(
            !self.name.trim().is_empty() && self.name.len() <= 64,
            "Name must be 1 to 64 bytes"
        );
        ensure!(self.address.len() <= 128, "Address is too long");
        Ok(())
    }
}

pub struct Identity {
    signing: SigningKey,
    encryption: SecretKey,
}

impl Identity {
    pub fn seal_link(
        &self,
        peer: &Contact,
        context: &str,
        frame: serde_json::Value,
    ) -> Result<Vec<u8>> {
        peer.validate()?;
        ensure!(
            context.starts_with("/nearby/v1/") && context.len() <= 512,
            "Invalid nearby session context"
        );
        let plain = serde_json::to_vec(&LinkFrame {
            context: context.into(),
            frame,
        })?;
        ensure!(
            plain.len() <= MAX_ENVELOPE + 2048,
            "Nearby frame exceeds limit"
        );
        let cipher = SalsaBox::new(
            &PublicKey::from(decode_array::<32>(&peer.box_key)?),
            &self.encryption,
        );
        let mut nonce = [0u8; 24];
        OsRng.fill_bytes(&mut nonce);
        let encrypted = cipher
            .encrypt((&nonce).into(), plain.as_slice())
            .map_err(|_| anyhow::anyhow!("Nearby encryption failed"))?;
        Ok([nonce.as_slice(), encrypted.as_slice()].concat())
    }
    pub fn open_link(
        &self,
        peer: &Contact,
        context: &str,
        packet: &[u8],
    ) -> Result<serde_json::Value> {
        peer.validate()?;
        ensure!(
            packet.len() >= 40 && packet.len() <= MAX_ENVELOPE + 2096,
            "Invalid nearby frame length"
        );
        let cipher = SalsaBox::new(
            &PublicKey::from(decode_array::<32>(&peer.box_key)?),
            &self.encryption,
        );
        let nonce: [u8; 24] = packet[..24].try_into().unwrap();
        let plain = cipher
            .decrypt((&nonce).into(), &packet[24..])
            .map_err(|_| anyhow::anyhow!("Nearby frame authentication failed"))?;
        let decoded: LinkFrame = serde_json::from_slice(&plain)?;
        ensure!(
            decoded.context == context && context.starts_with("/nearby/v1/"),
            "Nearby frame belongs to another session"
        );
        Ok(decoded.frame)
    }
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        let mut auth = Zeroizing::new([0u8; 32]);
        let mut encryption = Zeroizing::new([0u8; 32]);
        let kdf = Hkdf::<Sha256>::new(Some(b"Paramo1d/Courier/1"), seed);
        kdf.expand(b"message authentication", &mut *auth)
            .expect("fixed KDF length");
        kdf.expand(b"direct-message encryption", &mut *encryption)
            .expect("fixed KDF length");
        Self {
            signing: SigningKey::from_bytes(&auth),
            encryption: SecretKey::from(*encryption),
        }
    }

    pub fn contact(&self, name: String, address: String) -> Result<Contact> {
        let contact = Contact {
            id: hex::encode(self.signing.verifying_key().to_bytes()),
            box_key: hex::encode(self.encryption.public_key().as_bytes()),
            name,
            address,
        };
        contact.validate()?;
        Ok(contact)
    }

    pub fn invite(&self, contact: &Contact) -> Result<String> {
        self.owns(contact)?;
        let card = ContactCard {
            contact: contact.clone(),
            signature: hex::encode(self.signing.sign(&card_bytes(contact)?).to_bytes()),
        };
        Ok(format!(
            "paramo1d://contact/{}",
            URL_SAFE_NO_PAD.encode(serde_json::to_vec(&card)?)
        ))
    }

    fn owns(&self, contact: &Contact) -> Result<()> {
        contact.validate()?;
        ensure!(
            contact.id == hex::encode(self.signing.verifying_key().to_bytes())
                && contact.box_key == hex::encode(self.encryption.public_key().as_bytes()),
            "Identity mismatch"
        );
        Ok(())
    }

    pub fn seal(
        &self,
        sender: Contact,
        destination: Destination,
        message: Message,
        now_ms: u64,
    ) -> Result<Envelope> {
        self.owns(&sender)?;
        message.validate()?;
        destination.validate()?;
        let mut nonce = [0u8; 24];
        OsRng.fill_bytes(&mut nonce);
        let mut data = EnvelopeData {
            version: VERSION,
            sender,
            destination,
            created_ms: now_ms,
            expires_ms: now_ms
                .checked_add(MAX_LIFETIME_MS)
                .context("Clock overflow")?,
            nonce: hex::encode(nonce),
            body: String::new(),
        };
        let inner = serde_json::to_vec(&BoundMessage {
            context: context_hash(&data)?,
            message,
        })?;
        data.body = match &data.destination {
            Destination::Group { .. } => URL_SAFE_NO_PAD.encode(&inner),
            Destination::Direct { contact } => {
                let public = PublicKey::from(decode_array::<32>(&contact.box_key)?);
                let cipher = SalsaBox::new(&public, &self.encryption);
                URL_SAFE_NO_PAD.encode(
                    cipher
                        .encrypt((&nonce).into(), inner.as_slice())
                        .map_err(|_| anyhow::anyhow!("Message encryption failed"))?,
                )
            }
        };
        let bytes = signed_bytes(&data)?;
        let result = Envelope {
            id: hex::encode(Sha256::digest(&bytes)),
            signature: hex::encode(self.signing.sign(&bytes).to_bytes()),
            data,
        };
        ensure!(
            serde_json::to_vec(&result)?.len() <= MAX_ENVELOPE,
            "Message exceeds delivery limit"
        );
        Ok(result)
    }

    pub fn open(&self, envelope: &Envelope, now_ms: u64) -> Result<Message> {
        envelope.verify(now_ms)?;
        let body = URL_SAFE_NO_PAD.decode(&envelope.data.body)?;
        let plain = match &envelope.data.destination {
            Destination::Group { .. } => body,
            Destination::Direct { contact } => {
                let own = hex::encode(self.signing.verifying_key().to_bytes());
                let public = if own == contact.id {
                    PublicKey::from(decode_array::<32>(&envelope.data.sender.box_key)?)
                } else if own == envelope.data.sender.id {
                    PublicKey::from(decode_array::<32>(&contact.box_key)?)
                } else {
                    bail!("Message belongs to another contact");
                };
                let cipher = SalsaBox::new(&public, &self.encryption);
                let nonce = decode_array::<24>(&envelope.data.nonce)?;
                cipher
                    .decrypt((&nonce).into(), body.as_slice())
                    .map_err(|_| anyhow::anyhow!("Message authentication failed"))?
            }
        };
        let bound: BoundMessage = serde_json::from_slice(&plain)?;
        ensure!(
            bound.context == context_hash(&envelope.data)?,
            "Message context mismatch"
        );
        bound.message.validate()?;
        Ok(bound.message)
    }

    pub fn read_authorization(&self, path: &str, now_ms: u64) -> String {
        hex::encode(self.signing.sign(&read_bytes(path, now_ms)).to_bytes())
    }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct LinkFrame {
    context: String,
    frame: serde_json::Value,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "snake_case", deny_unknown_fields)]
pub enum Destination {
    Group { room: String },
    Direct { contact: Contact },
}
impl Destination {
    pub fn validate(&self) -> Result<()> {
        match self {
            Self::Group { room } => validate_room(room),
            Self::Direct { contact } => contact.validate(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "snake_case", deny_unknown_fields)]
pub enum Message {
    Text {
        text: String,
    },
    Invoice {
        invoice_id: String,
        address: String,
        amount: String,
        memo: String,
    },
    Receipt {
        invoice_id: String,
        receipt_hex: String,
    },
    Transaction {
        intent_hex: String,
    },
    RelayUpdate {
        txid: String,
        stage: String,
        receipt_hex: Option<String>,
    },
}
impl Message {
    pub fn validate(&self) -> Result<()> {
        match self {
            Self::Text { text } => ensure!(
                !text.trim().is_empty() && text.len() <= MAX_TEXT,
                "Message must be 1 to 4096 bytes"
            ),
            Self::Invoice {
                invoice_id,
                address,
                amount,
                memo,
            } => {
                decode_array::<16>(invoice_id)?;
                ensure!(
                    address.starts_with("o1") && address.len() <= 128,
                    "Invalid invoice address"
                );
                let units = amount_micronoid(amount)?;
                ensure!(units > 0 && memo.len() <= 256, "Invalid invoice");
            }
            Self::Receipt {
                invoice_id,
                receipt_hex,
            } => {
                decode_array::<16>(invoice_id)?;
                ensure!(
                    receipt_hex.len() <= 262144
                        && receipt_hex.len() % 2 == 0
                        && receipt_hex.bytes().all(|v| v.is_ascii_hexdigit()),
                    "Invalid receipt encoding"
                );
            }
            Self::Transaction { intent_hex } => {
                ensure!(
                    !intent_hex.is_empty()
                        && intent_hex.len() <= 606990
                        && intent_hex.len() % 2 == 0
                        && intent_hex.bytes().all(|v| v.is_ascii_hexdigit()),
                    "Invalid authorized payment encoding"
                );
            }
            Self::RelayUpdate {
                txid,
                stage,
                receipt_hex,
            } => {
                decode_array::<32>(txid)?;
                ensure!(
                    matches!(
                        stage.as_str(),
                        "submitted" | "in_mempool" | "included" | "rejected"
                    ),
                    "Unknown network observation"
                );
                if let Some(receipt) = receipt_hex {
                    ensure!(
                        receipt.len() <= 262144
                            && receipt.len() % 2 == 0
                            && receipt.bytes().all(|v| v.is_ascii_hexdigit()),
                        "Invalid receipt evidence"
                    );
                }
                ensure!(
                    stage != "included" || receipt_hex.is_some(),
                    "Block inclusion requires receipt evidence"
                );
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EnvelopeData {
    pub version: u8,
    pub sender: Contact,
    pub destination: Destination,
    pub created_ms: u64,
    pub expires_ms: u64,
    pub nonce: String,
    pub body: String,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Envelope {
    pub id: String,
    pub data: EnvelopeData,
    pub signature: String,
}
impl Envelope {
    pub fn public_message(&self) -> Result<Option<Message>> {
        if !matches!(self.data.destination, Destination::Group { .. }) {
            return Ok(None);
        }
        let decoded = URL_SAFE_NO_PAD.decode(&self.data.body)?;
        let bound: BoundMessage = serde_json::from_slice(&decoded)?;
        ensure!(
            matches!(
                bound.message,
                Message::Text { .. } | Message::Transaction { .. } | Message::RelayUpdate { .. }
            ),
            "Invoices and receipts belong in direct chats"
        );
        bound.message.validate()?;
        ensure!(
            bound.context == context_hash(&self.data)?,
            "Public message context mismatch"
        );
        Ok(Some(bound.message))
    }
    pub fn verify(&self, now_ms: u64) -> Result<()> {
        ensure!(self.data.version == VERSION, "Unsupported envelope version");
        self.data.sender.validate()?;
        self.data.destination.validate()?;
        decode_array::<24>(&self.data.nonce)?;
        ensure!(
            self.data.body.len() <= MAX_ENVELOPE,
            "Message exceeds delivery limit"
        );
        ensure!(
            self.data.created_ms <= now_ms.saturating_add(CLOCK_SKEW_MS)
                && self.data.expires_ms > now_ms
                && self.data.expires_ms > self.data.created_ms
                && self.data.expires_ms - self.data.created_ms <= MAX_LIFETIME_MS,
            "Message expired or clock differs"
        );
        self.public_message()?;
        let bytes = signed_bytes(&self.data)?;
        ensure!(
            self.id == hex::encode(Sha256::digest(&bytes)),
            "Message ID mismatch"
        );
        verify(&self.data.sender.id, &bytes, &self.signature)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct BoundMessage {
    context: String,
    message: Message,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ContactCard {
    contact: Contact,
    signature: String,
}

pub fn import_contact(uri: &str) -> Result<Contact> {
    ensure!(uri.len() <= 4096, "Contact card is too large");
    let encoded = uri
        .strip_prefix("paramo1d://contact/")
        .context("Use a Paramo1d contact link")?;
    let card: ContactCard = serde_json::from_slice(&URL_SAFE_NO_PAD.decode(encoded)?)?;
    card.contact.validate()?;
    verify(
        &card.contact.id,
        &card_bytes(&card.contact)?,
        &card.signature,
    )?;
    Ok(card.contact)
}

pub fn verify_read(id: &str, path: &str, time_ms: u64, signature: &str, now_ms: u64) -> Result<()> {
    ensure!(
        now_ms.abs_diff(time_ms) <= CLOCK_SKEW_MS,
        "Inbox authorization expired"
    );
    verify(id, &read_bytes(path, time_ms), signature)
}
pub fn validate_room(room: &str) -> Result<()> {
    ensure!(
        !room.is_empty()
            && room.len() <= 48
            && room
                .bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-'),
        "Use lowercase letters, numbers and hyphens for a group"
    );
    Ok(())
}
pub fn amount_micronoid(text: &str) -> Result<u64> {
    ensure!(
        !text.is_empty() && text.len() <= 24 && text.trim() == text,
        "Enter a NOID amount"
    );
    let mut parts = text.split('.');
    let whole = parts.next().unwrap();
    let fraction = parts.next().unwrap_or("");
    ensure!(
        parts.next().is_none()
            && !whole.is_empty()
            && whole.bytes().all(|v| v.is_ascii_digit())
            && fraction.len() <= 6
            && fraction.bytes().all(|v| v.is_ascii_digit()),
        "Use up to 6 decimal places"
    );
    let whole = whole
        .parse::<u64>()?
        .checked_mul(1_000_000)
        .context("Amount is too large")?;
    let fraction = if fraction.is_empty() {
        0
    } else {
        fraction.parse::<u64>()? * 10u64.pow(6 - fraction.len() as u32)
    };
    whole.checked_add(fraction).context("Amount is too large")
}
pub fn decode_array<const N: usize>(value: &str) -> Result<[u8; N]> {
    ensure!(
        value.len() == N * 2
            && value
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "Invalid canonical key encoding"
    );
    hex::decode(value)?
        .try_into()
        .map_err(|_| anyhow::anyhow!("Invalid key length"))
}
fn signed_bytes(data: &EnvelopeData) -> Result<Vec<u8>> {
    let mut b = DOMAIN.to_vec();
    b.extend(serde_json::to_vec(data)?);
    Ok(b)
}
fn card_bytes(contact: &Contact) -> Result<Vec<u8>> {
    let mut b = b"Paramo1d/Courier/contact/1\0".to_vec();
    b.extend(serde_json::to_vec(contact)?);
    Ok(b)
}
fn context_hash(data: &EnvelopeData) -> Result<String> {
    let context = serde_json::to_vec(&(
        data.version,
        &data.sender,
        &data.destination,
        data.created_ms,
        data.expires_ms,
        &data.nonce,
    ))?;
    Ok(hex::encode(Sha256::digest(context)))
}
fn read_bytes(path: &str, now_ms: u64) -> Vec<u8> {
    format!("Paramo1d/Courier/inbox/1\0{path}\0{now_ms}").into_bytes()
}
fn verify(id: &str, bytes: &[u8], signature: &str) -> Result<()> {
    let key = VerifyingKey::from_bytes(&decode_array::<32>(id)?)?;
    ensure!(!key.is_weak(), "Invalid identity");
    key.verify_strict(
        bytes,
        &Signature::from_bytes(&decode_array::<64>(signature)?),
    )?;
    Ok(())
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Backup {
    format: String,
    salt: String,
    nonce: String,
    ciphertext: String,
}
fn backup_key(password: &str, salt: &[u8; 16]) -> Result<Zeroizing<[u8; 32]>> {
    use argon2::{Algorithm, Argon2, Params, Version};
    ensure!(
        password.len() >= 12 && password.len() <= 1024,
        "Use a backup password of at least 12 characters"
    );
    let mut key = Zeroizing::new([0u8; 32]);
    Argon2::new(
        Algorithm::Argon2id,
        Version::V0x13,
        Params::new(32768, 3, 1, Some(32)).expect("fixed backup parameters"),
    )
    .hash_password_into(password.as_bytes(), salt, &mut *key)
    .map_err(|_| anyhow::anyhow!("Backup key derivation failed"))?;
    Ok(key)
}
pub fn encrypt_backup(plain: &[u8], password: &str) -> Result<String> {
    use chacha20poly1305::{
        aead::{Aead, KeyInit, Payload},
        XChaCha20Poly1305, XNonce,
    };
    ensure!(plain.len() <= 32 * 1024 * 1024, "Backup exceeds size limit");
    let mut salt = [0u8; 16];
    let mut nonce = [0u8; 24];
    OsRng.fill_bytes(&mut salt);
    OsRng.fill_bytes(&mut nonce);
    let key = backup_key(password, &salt)?;
    let cipher = XChaCha20Poly1305::new_from_slice(&*key).expect("key length");
    let encrypted = cipher
        .encrypt(
            XNonce::from_slice(&nonce),
            Payload {
                msg: plain,
                aad: b"Paramo1d/backup/1",
            },
        )
        .map_err(|_| anyhow::anyhow!("Backup encryption failed"))?;
    Ok(serde_json::to_string(&Backup {
        format: "paramo1d-backup-1".into(),
        salt: hex::encode(salt),
        nonce: hex::encode(nonce),
        ciphertext: hex::encode(encrypted),
    })?)
}
pub fn decrypt_backup(encoded: &str, password: &str) -> Result<Zeroizing<Vec<u8>>> {
    use chacha20poly1305::{
        aead::{Aead, KeyInit, Payload},
        XChaCha20Poly1305, XNonce,
    };
    ensure!(
        encoded.len() <= 65 * 1024 * 1024,
        "Backup exceeds size limit"
    );
    let backup: Backup = serde_json::from_str(encoded)?;
    ensure!(
        backup.format == "paramo1d-backup-1",
        "Unsupported backup format"
    );
    let salt = decode_array::<16>(&backup.salt)?;
    let nonce = decode_array::<24>(&backup.nonce)?;
    let key = backup_key(password, &salt)?;
    let cipher = XChaCha20Poly1305::new_from_slice(&*key).expect("key length");
    let plain = cipher
        .decrypt(
            XNonce::from_slice(&nonce),
            Payload {
                msg: &hex::decode(backup.ciphertext)?,
                aad: b"Paramo1d/backup/1",
            },
        )
        .map_err(|_| anyhow::anyhow!("Incorrect password or damaged backup"))?;
    Ok(Zeroizing::new(plain))
}

#[cfg(test)]
mod tests {
    use super::*;
    const NOW: u64 = 1_800_000_000_000;
    fn user(seed: u8) -> (Identity, Contact) {
        let key = Identity::from_seed(&[seed; 32]);
        let c = key
            .contact(format!("User {seed}"), format!("o1test{seed}"))
            .unwrap();
        (key, c)
    }
    #[test]
    fn direct_delivery_recipient_sender_and_wrong_key() {
        let (alice, a) = user(1);
        let (bob, b) = user(2);
        let (eve, _) = user(3);
        let text = Message::Text {
            text: "A message only we can read".into(),
        };
        let envelope = alice
            .seal(a, Destination::Direct { contact: b }, text.clone(), NOW)
            .unwrap();
        assert_eq!(bob.open(&envelope, NOW).unwrap(), text);
        assert_eq!(alice.open(&envelope, NOW).unwrap(), text);
        assert!(eve.open(&envelope, NOW).is_err());
        assert!(!serde_json::to_string(&envelope)
            .unwrap()
            .contains("only we can read"));
    }
    #[test]
    fn nearby_frames_bind_the_session_and_preserve_opaque_forwarded_messages() {
        let (alice, a) = user(1);
        let (bob, b) = user(2);
        let (carol, c) = user(3);
        let envelope = alice
            .seal(
                a,
                Destination::Direct { contact: c },
                Message::Text {
                    text: "For the final recipient".into(),
                },
                NOW,
            )
            .unwrap();
        let context = "/nearby/v1/one-fresh-session";
        let packet = alice
            .seal_link(
                &b,
                context,
                serde_json::json!({"type":"envelope","envelope":envelope}),
            )
            .unwrap();
        let decoded = bob
            .open_link(
                &alice.contact("Alice".into(), "o1test1".into()).unwrap(),
                context,
                &packet,
            )
            .unwrap();
        let forwarded: Envelope = serde_json::from_value(decoded["envelope"].clone()).unwrap();
        assert!(bob.open(&forwarded, NOW).is_err());
        assert_eq!(
            carol.open(&forwarded, NOW).unwrap(),
            Message::Text {
                text: "For the final recipient".into()
            }
        );
        assert!(bob
            .open_link(
                &alice.contact("Alice".into(), "o1test1".into()).unwrap(),
                "/nearby/v1/a-different-session",
                &packet
            )
            .is_err());
        let mut altered = packet;
        *altered.last_mut().unwrap() ^= 1;
        assert!(bob
            .open_link(
                &alice.contact("Alice".into(), "o1test1".into()).unwrap(),
                context,
                &altered
            )
            .is_err());
    }
    #[test]
    fn modified_routing_body_sender_and_expiry_are_rejected() {
        let (alice, a) = user(1);
        let (bob, b) = user(2);
        let e = alice
            .seal(
                a,
                Destination::Direct { contact: b },
                Message::Text {
                    text: "hello".into(),
                },
                NOW,
            )
            .unwrap();
        for changed in 0..4 {
            let mut e = e.clone();
            match changed {
                0 => e.data.sender.name = "Different person".into(),
                1 => e.data.body.push('a'),
                2 => {
                    e.data.destination = Destination::Group {
                        room: "parano1d".into(),
                    }
                }
                _ => e.data.expires_ms += 1,
            };
            assert!(bob.open(&e, NOW).is_err());
        }
        assert!(e.verify(NOW + MAX_LIFETIME_MS).is_err());
    }
    #[test]
    fn signed_contacts_and_inbox_requests_bind_exact_context() {
        let (alice, a) = user(1);
        assert_eq!(import_contact(&alice.invite(&a).unwrap()).unwrap(), a);
        let sig = alice.read_authorization("/v1/inbox/x?after=4", NOW);
        assert!(verify_read(&a.id, "/v1/inbox/x?after=4", NOW, &sig, NOW).is_ok());
        assert!(verify_read(&a.id, "/v1/inbox/x?after=5", NOW, &sig, NOW).is_err());
    }
    #[test]
    fn exact_payment_amounts() {
        assert_eq!(amount_micronoid("12.000001").unwrap(), 12_000_001);
        for invalid in [
            "-1",
            "1e6",
            "1.0000001",
            " 1",
            "1.2.3",
            "18446744073709551615",
        ] {
            assert!(amount_micronoid(invalid).is_err());
        }
    }
    #[test]
    fn network_reports_cannot_claim_verified_finality() {
        let (key, contact) = user(1);
        for stage in ["confirmed", "finalized", "verified"] {
            assert!(key
                .seal(
                    contact.clone(),
                    Destination::Group { room: LOBBY.into() },
                    Message::RelayUpdate {
                        txid: "aa".repeat(32),
                        stage: stage.into(),
                        receipt_hex: None
                    },
                    NOW
                )
                .is_err());
        }
        assert!(Message::RelayUpdate {
            txid: "aa".repeat(32),
            stage: "included".into(),
            receipt_hex: None
        }
        .validate()
        .is_err());
        let report = Message::RelayUpdate {
            txid: "aa".repeat(32),
            stage: "in_mempool".into(),
            receipt_hex: None,
        };
        let envelope = key
            .seal(
                contact,
                Destination::Group { room: LOBBY.into() },
                report.clone(),
                NOW,
            )
            .unwrap();
        assert_eq!(envelope.public_message().unwrap(), Some(report));
        assert!(envelope.verify(NOW).is_ok());
    }
    #[test]
    fn portable_backup_authenticates_password_and_ciphertext() {
        let password = "a long independent backup password";
        let encoded = encrypt_backup(br#"{"identity":"fixture","messages":[]}"#, password).unwrap();
        assert_eq!(
            &**decrypt_backup(&encoded, password).unwrap(),
            br#"{"identity":"fixture","messages":[]}"#
        );
        assert!(decrypt_backup(&encoded, "a completely wrong password").is_err());
        let mut altered: Backup = serde_json::from_str(&encoded).unwrap();
        let mut bytes = hex::decode(&altered.ciphertext).unwrap();
        bytes[0] ^= 1;
        altered.ciphertext = hex::encode(bytes);
        assert!(decrypt_backup(&serde_json::to_string(&altered).unwrap(), password).is_err());
    }
}
