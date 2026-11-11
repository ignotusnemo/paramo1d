use anyhow::{bail, ensure, Result};
use noid_poseidon2b::primitives::Address;
use serde_json::{json, Value};

pub(crate) fn parse(kind: &str, encoded: &str) -> Result<Value> {
    let text = encoded.trim();
    ensure!(
        !text.is_empty() && text.len() <= 4096,
        "This QR code is empty or too large."
    );
    match kind {
        "address" => {
            let address = Address::parse(text)
                .map_err(|_| anyhow::anyhow!("Scan a NOID receiving address QR code."))?;
            Ok(json!({"kind":kind,"text":address.to_bech32()}))
        }
        "contact" => {
            ensure!(
                text.starts_with("paramo1d://contact/"),
                "Scan a Paramo1d contact QR code."
            );
            let contact = paramo1d_courier::import_contact(text).map_err(|_| {
                anyhow::anyhow!("This contact QR code could not be verified. Ask for a new one.")
            })?;
            Ok(json!({"kind":kind,"text":text,"contact":contact}))
        }
        _ => bail!("Choose an address or contact to scan."),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use noid_poseidon2b::primitives::{derive_address, SpendSecret};

    #[test]
    fn receiving_qr_preserves_the_address_and_checks_its_checksum() {
        let address = derive_address(&SpendSecret::from_bytes([3; 32])).to_bech32();
        assert_eq!(
            parse("address", &format!("\n{address} ")).unwrap()["text"],
            address
        );
        let mut changed = address.into_bytes();
        let end = changed.len() - 1;
        changed[end] = if changed[end] == b'q' { b'p' } else { b'q' };
        assert!(parse("address", std::str::from_utf8(&changed).unwrap()).is_err());
        assert!(parse("address", "https://example.com/o1address").is_err());
    }

    #[test]
    fn contact_qr_verifies_the_signature_and_keeps_scan_types_separate() {
        let identity = paramo1d_courier::Identity::from_seed(&[7; 32]);
        let address = derive_address(&SpendSecret::from_bytes([8; 32])).to_bech32();
        let contact = identity
            .contact("QR contact".into(), address.clone())
            .unwrap();
        let invite = identity.invite(&contact).unwrap();
        let decoded = parse("contact", &invite).unwrap();
        assert_eq!(decoded["contact"]["name"], "QR contact");
        assert_eq!(decoded["text"], invite);
        assert!(parse("address", &invite).is_err());
        assert!(parse("contact", &address).is_err());
        let mut changed = invite.into_bytes();
        changed[40] = if changed[40] == b'A' { b'B' } else { b'A' };
        assert!(parse("contact", std::str::from_utf8(&changed).unwrap()).is_err());
        assert!(parse("contact", &"A".repeat(4097)).is_err());
    }
}
