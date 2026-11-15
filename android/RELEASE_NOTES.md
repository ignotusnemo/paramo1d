**Speak freely. Own your money. Carry a full node.**

Paramo1d 1.0 puts a full node for the Parano1d post-quantum blockchain, a native NOID wallet and an encrypted messenger on your Android phone. Authorize signatureless, post-quantum payments offline. Relay them over Bluetooth mesh. Verify the blockchain and payment receipts with your own node.

Send, receive and request NOID inside a conversation. Switch to Paranoid mode for a wallet that works directly through mainnet P2P.

Synchronize from scratch and verify the chain from genesis through recursive State proofs. Get your independently verified balance in 20 seconds. Balance updates in 1–2 seconds. All on a budget Android phone.

### Two wallet modes

**Normal mode** combines local blockchain verification with fast wallet data from a configurable RPC service. The phone verifies slot proofs against its own accepted State root. Community, private conversations and the wallet are available together.

**Paranoid mode** gets wallet data, broadcasts payments and retrieves inclusion receipts directly through mainnet P2P. It uses **zero wallet RPC requests**. Private conversations and the wallet stay available while Community pauses. Switching back restores Community and its saved history.

The mechanical switch changes the interface from green to orange and gives a short vibration. Connections and App VPN have their own controls in the header.

### Real measurements on an everyday phone

Measured on a **Redmi 15C with 4 GB RAM**:

| Operation | Observed time |
| --- | ---: |
| Ordinary-mode balance check with unchanged coins | **1.36 s** |
| Subsequent P2P wallet watches with unchanged coins | **0.82–1.50 s** |
| Full P2P wallet recovery after a 90-block gap, through App VPN | **37.55 s** |
| Full repeat verification of a Small recursive State proof | **2.50 s** |
| First Small recursive State proof verification | **11.69 s** |
| Native recursive State proof verification | **7.15 s** |

P2P recovery over mobile data through App VPN restored the wallet and verified the new State with **zero wallet RPC requests**. Complete local verification of a public mainnet bundle, including the header prefix and fork origins, took **23.54 seconds**. Peak verifier memory was approximately **733 MiB**.

Adaptive updates watch the wallet's coins and transaction epoch while the app is open and unlocked. The node pauses when the app is minimized or locked. Background message delivery stays active by default.

### Internet, App VPN and Bluetooth mesh

- Use ordinary mobile data or Wi-Fi.
- Enable the built-in **App VPN** for Paramo1d alone. It uses AmneziaWG with authenticated HTTPS fallback. Other apps keep their own connection.
- Exchange messages, authorized payment packets and receipts over Bluetooth without internet.
- Nearby mesh participants can carry and forward encrypted packets for another contact.
- Bluetooth and internet deliver in parallel, with message IDs preventing duplicates.
- Stalled wallet requests trigger an App VPN suggestion in either mode. Switching the connection resumes the balance check through the selected route.

### Authorize offline. Let someone connected relay it.

Prepare a payment from the wallet's saved, verified State. Review the recipient, amount and network fee, then authorize it on the phone. Send the packet to a nearby contact over Bluetooth or share it with the community in Normal mode.

A connected participant forwards the authorization. The spending secret stays with the sender. Payment cards show delivery progress. The phone verifies returned inclusion receipts against its own accepted chain. Payments settle on the Parano1d network.

The wallet checks transaction-epoch freshness and reserves inputs used by pending payments. Expired authorizations offer **Review fresh payment** to the sender.

### A messenger for everyday use

- Public community chat and end-to-end encrypted private messages.
- Replies with a jump to the original message, emoji reactions, copy and text selection.
- Conversation search, saved drafts, unread counters and background notifications.
- Verified contact cards with Copy link, Add contact and Message actions.
- Contact QR codes and an in-app scanner for adding contacts and filling payment addresses.
- Pixel warrior avatars generated locally from messaging identities.
- Floating conversation controls, composer and navigation. Light, dark and system themes.
- Separate Community and private-chat cleanup, storage usage and a chooser when storage fills up.
- **Delete chat** removes the conversation and contact from this phone. A new incoming message can start a new conversation.

### Local control and recovery

Fingerprint or the phone's screen lock protects entry. Android Keystore protects the encrypted local archive. Portable backups use Argon2id and XChaCha20-Poly1305. Screenshot capture is available as an explicit setting.

NOID payments use Parano1d's signatureless, post-quantum Owner authorization. Private-message encryption uses X25519 and XSalsa20-Poly1305. Community messages and on-chain payments are public.

### Install

Download `paramo1d-v1.0.0-arm64.apk` from this release. The APK includes the mainnet verification parameters. It requires **Android 8.0 or later** and **ARM64 hardware with AES and PMULL**.

Install over an earlier official release to retain the wallet, chats and settings. Release downloads include `SHA256SUMS` and `SIGNING-CERTIFICATE.txt`. The official release signing certificate is unchanged.

[Source code](https://github.com/ignotusnemo/paramo1d) · [Android documentation](https://github.com/ignotusnemo/paramo1d/blob/v1.0.0/android/README.md)
