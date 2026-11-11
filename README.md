# Paramo1d

**A full Parano1d node, native NOID wallet and encrypted messenger for Android.**

Send, receive and request NOID directly inside a chat. Your phone holds the spending secret, authorizes payments and verifies the blockchain. Connect through ordinary internet, turn on the built-in protected connection, or exchange messages and authorized payments with nearby participants over Bluetooth.

Reply to messages, react with emoji, copy text and share contact cards. Each conversation keeps its own encrypted draft. Pixel warrior avatars are generated on the device from each messaging identity.

## Inside the app

- **A blockchain node on your phone.** Connect directly to mainnet peers and independently verify the chain, recursive State proofs and payment receipts.
- **NOID payments in your conversations.** Send NOID, share a receiving address, request an amount with a memo and check the returned payment receipt.
- **One public community and encrypted private chats.** Share contact links or QR codes and receive messages in the background.
- **Ordinary internet.** Chat, synchronize the node and deliver payments through your normal mobile or Wi-Fi connection.
- **Built-in App VPN.** Use an app-only AmneziaWG protected channel with authenticated HTTPS fallback. Other applications keep their own connection.
- **Bluetooth without internet.** Exchange encrypted messages, already-authorized payment packets and receipts with nearby participants.
- **Community-assisted payment delivery.** Authorize a payment from your saved verified wallet view. A connected participant can forward it to the network. The spending secret stays on your phone.
- **Local access and recovery.** Fingerprint or screen-lock entry, encrypted portable backups and light, dark or system appearance.

Payments settle on the Parano1d network. Bluetooth carries the authorization and receipt between participants. Your own node checks the receipt against its accepted chain.

## Install

Download the ARM64 APK from [Releases](https://github.com/ignotusnemo/paramo1d/releases/latest). Android 8.0 or later and ARM64 hardware with AES and PMULL are required. The APK includes the mainnet verification parameters.

Release downloads include APK hashes and the public signing-certificate fingerprint. Updates use the same release signing key.

## The node and wallet

The node retrieves headers and recursive proofs over Parano1d P2P. It checks the header chain from genesis, proof of work, fork certificates and the recursive State proof on the device. Its accepted chain and State roots authenticate wallet inputs and payment receipts.

The wallet uses a configurable RPC endpoint for coin discovery, slot-proof delivery and transaction submission. It checks returned slot proofs against its independently verified State root. Internet chats use configurable delivery relays. These services provide data and delivery. Payment authorization and blockchain verification run on the phone.

Direct messages use X25519 and XSalsa20-Poly1305. NOID payments use Parano1d's post-quantum Owner authorization protocol. The community chat and blockchain payments are public.

While the app is open and unlocked, small queries watch for changes to the wallet's coins. Changed coins trigger State and membership verification. The node stops when the app is minimized or locked. Background message delivery continues independently.

On a Redmi 15C with 4 GB RAM, new Small and Native proofs took 5.042 and 5.635 seconds with authenticated parameters retained in memory. The first complete bundle check took 49.877 seconds after opening the parameter runtime. The [device report](android/reports/redmi-15c-2026-11-10.md) records the conditions, cold-start costs, mainnet payment and actual Bluetooth checks.

[Android usage and build instructions](android/README.md) · [Command-line verifier measurements](docs/verifier-benchmarks.md)

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

The [Android workflow](.github/workflows/android.yml) runs the tests and builds an APK. A version tag builds a signed release and publishes it after the checks pass.

## Command-line client

```sh
cargo build --locked --release
paramo1d run --artifacts ./artifacts --data-dir ./mainnet
```

The client discovers mainnet peers through DNS seeds. `--once` performs one synchronization pass. `mainnet/accepted.json` records the accepted height, block hash, State root and measurements.

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
