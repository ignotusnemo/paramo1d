# Paramo1d

**Speak freely. Own your money. Carry a full node.**

Paramo1d 1.0 puts a full node for the Parano1d post-quantum blockchain, a native NOID wallet and an encrypted messenger on your Android phone. Authorize signatureless, post-quantum payments offline. Relay them over Bluetooth mesh. Verify the blockchain and payment receipts with your own node.

Send, receive and request NOID inside a conversation. Switch to Paranoid mode for a wallet that works directly through mainnet P2P.

Synchronize from scratch and verify the chain from genesis through recursive State proofs. Get your independently verified balance in 20 seconds. Balance updates in 1–2 seconds. All on a budget Android phone.

[Download Android](https://github.com/ignotusnemo/paramo1d/releases/latest) · [Release notes](android/RELEASE_NOTES.md) · [Android documentation](android/README.md)

## Two wallet modes

Your phone verifies the blockchain in both modes.

| | Normal mode | Paranoid mode |
| --- | --- | --- |
| Blockchain and State proof verification | On the phone | On the phone |
| Coin discovery and slot-proof delivery | Configurable RPC service | Mainnet P2P |
| Payment broadcast and receipt retrieval | Configurable RPC service | Mainnet P2P |
| Wallet RPC | Available | Disabled |
| Community chat | Available | Paused |
| Encrypted private messages | Available | Available |
| Interface | Green | Orange |

The mechanical Paranoid mode switch gives a short vibration and changes the interface from green to orange. Private chats and the wallet stay available. Switching back restores Community and its saved history.

## Internet, App VPN and Bluetooth

- **Ordinary internet.** Use mobile data or Wi-Fi for messaging, synchronization and payment delivery.
- **Built-in App VPN.** An app-only AmneziaWG protected channel with authenticated HTTPS fallback. Other applications keep their own connection.
- **Bluetooth mesh without internet.** Exchange messages, authorized payment packets and receipts with nearby participants. Connected devices can carry and forward encrypted packets for another contact.

Bluetooth and internet deliver in parallel, with message IDs preventing duplicates. Connections, App VPN and Paranoid mode have separate controls in the header. Stalled wallet requests trigger an App VPN suggestion in either mode. Switching the connection resumes the balance check through the selected route.

## Payments inside conversations

Send NOID, share a receiving address or request an amount with a memo. Scan a receiving QR code directly from the Send form. Review the recipient, amount and network fee before authorizing the payment.

Prepare an offline payment from the wallet's saved, verified State and pass the authorization over Bluetooth. A connected recipient or community participant forwards the packet to the network. The spending secret stays with the sender. Payment cards track delivery. The phone verifies returned inclusion receipts against its own accepted chain.

Payments settle on the Parano1d network using its signatureless, post-quantum Owner authorization. The wallet checks transaction-epoch freshness. Expired packets offer **Review fresh payment** to the sender.

## Conversations and contacts

- One public community and end-to-end encrypted private conversations.
- Replies with a jump to the original message, emoji reactions, copy and text selection.
- Search, saved drafts, unread counters and background message delivery.
- Verified contact cards with Copy link, Add contact and Message actions.
- Contact QR codes and an in-app scanner for adding contacts.
- Pixel warrior avatars generated locally from messaging identities.
- Floating conversation controls, composer and navigation. Light, dark and system themes.
- Separate cleanup for Community and selected private chats. Storage usage and a chooser when storage fills up.
- **Delete chat** removes its message history and contact from this phone. A new incoming message can start a new conversation.

Private-message encryption uses X25519 and XSalsa20-Poly1305. Ed25519 authenticates message envelopes and contact cards. Community messages and on-chain NOID payments are public.

## Performance on an everyday phone

Measured on a **Redmi 15C with 4 GB RAM**, Android 15:

| Operation | Observed time |
| --- | ---: |
| Ordinary-mode balance check with unchanged coins | **1.36 s** |
| Subsequent P2P wallet watches with unchanged coins | **0.82–1.50 s** |
| Full P2P wallet recovery after a 90-block gap | **37.55 s** |
| Full repeat verification of a Small recursive State proof | **2.50 s** |
| First Small recursive State proof verification | **11.69 s** |
| Native recursive State proof verification | **7.15 s** |

P2P recovery over mobile data through App VPN restored the wallet and verified the new State with **zero wallet RPC requests**. Complete local verification of a public mainnet bundle, including the header prefix and fork origins, took **23.54 seconds**. Peak verifier memory was approximately **733 MiB**.

## The node and wallet

The node retrieves headers and recursive proofs over Parano1d P2P. It verifies the header chain from genesis, proof of work, fork certificates and the recursive State proof on the device. Accepted State roots authenticate wallet inputs and payment receipts.

The default wallet checks RPC slot proofs against its independently verified State root. Paranoid mode verifies a complete sparse State snapshot for initial discovery, then retains its ordinary NOID coins and an empty-slot reserve. Short updates consume the complete ordered block bodies and check their transaction commitments. A recursive State proof authenticates the accepted extension before the updated wallet view is saved.

Verified header prefixes and wallet checkpoints carry local authentication tags bound to the wallet identity and released verification profile. Release-pinned canonical matrix commitments speed parameter loading. Checked immutable parameters stay in a bounded memory cache.

Adaptive checks watch for changes to the wallet's coins. Changed inputs and transaction epochs trigger State verification. While the app is open and unlocked, funded wallets renew payment readiness in the background. The node pauses when the application is minimized or the screen is locked. Background message delivery is on by default and continues independently.

## Local access and recovery

Fingerprint or the phone's screen lock protects entry. Android Keystore protects the encrypted local archive. Portable backups use Argon2id and XChaCha20-Poly1305. Save an encrypted backup and keep its password separately. Screenshots and screen recordings are available through an explicit setting.

## Install

Download the ARM64 APK from [Releases](https://github.com/ignotusnemo/paramo1d/releases/latest). Android 8.0 or later and ARM64 hardware with AES and PMULL are required. The APK includes the mainnet verification parameters.

Official release APKs use the same signing certificate, so updates preserve the wallet, chats and settings. Downloads include `SHA256SUMS` and `SIGNING-CERTIFICATE.txt`.

## Build Android

The build uses Rust 1.96, the Android NDK, Java 21, Gradle 8.14.3 and Go 1.27.3. Exact build inputs and their hashes are pinned in [android/build-inputs.json](android/build-inputs.json).

```sh
python3 scripts/fetch-android-artifacts.py --output ./artifacts
python3 scripts/build-courier.py \
  --ndk /path/to/android-ndk \
  --sdk /path/to/android-sdk \
  --java-home /path/to/jdk \
  --gradle /path/to/gradle/bin/gradle \
  --artifacts ./artifacts \
  --go /path/to/go/bin/go
```

The development APK is written to `android/app/build/outputs/apk/debug/app-debug.apk`. Release builds use `--variant release` and the signing environment described in the Android documentation.

The [Android workflow](.github/workflows/android.yml) runs the checks and builds an APK. A version tag builds a signed release and publishes it after the checks pass.

## Command-line client

```sh
cargo build --locked --release
paramo1d run --artifacts ./artifacts --data-dir ./mainnet
```

The client discovers mainnet peers through DNS seeds. `--once` performs one synchronization pass. `mainnet/accepted.json` records the accepted height, block hash and State root.

For offline verification, export a public proof bundle from a node database opened in read-only mode:

```sh
paramo1d export --node-data /path/to/node --output ./bundle
paramo1d verify --artifacts ./artifacts --bundle ./bundle
```

`Verifier` retains authenticated runtime material across checks. The [C interface](include/paramo1d.h) provides one-shot verification and reusable sessions. Streaming matrices and bounded caches support mobile memory budgets. Verification uses the available CPU cores automatically.

## Checks and source

```sh
cargo test --locked --release --workspace
python3 scripts/check-upstream.py
cd tunnel && go test ./...
```

Run the browser checks with `npm ci && npm test` from `android/tests`. The [Android storage fixture](android/storage-check/README.md) exercises encrypted storage and portable recovery under its own test identity.

The [source inventory](vendor/upstream.json) and [mobile adapters](vendor/client-overrides.json) bind the vendored verification code. [profiles/mainnet.json](profiles/mainnet.json) pins the production parameters. The source checker validates both inventories.

Licensed under [Apache-2.0](LICENSE). Third-party license texts are included with the relevant components and Android assets.
