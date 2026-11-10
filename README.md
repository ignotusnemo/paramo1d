# Paramo1d

An Android messenger with a Parano1d node, encrypted direct conversations and native NOID payments. The phone verifies blockchain State and payment receipts. Nearby participants can exchange messages and carry approved payments over Bluetooth.

## Install

Download the ARM64 APK from [Releases](https://github.com/ignotusnemo/paramo1d/releases/latest). Android 8.0 or later and ARM64 hardware with AES and PMULL are required. The APK includes the mainnet verification parameters.

Release downloads include APK hashes and the public signing-certificate fingerprint. Updates use the same release signing key.

## Chat and payments

- One public community chat and encrypted direct conversations.
- Native NOID payment requests, local authorization and checked inclusion receipts.
- Bluetooth delivery for messages, authorized payments and receipts.
- Configurable internet relays and an app-only protected AmneziaWG connection with HTTPS fallback.
- Background messages, fingerprint or screen-lock entry and encrypted portable backups.

A participant can forward an already-approved payment using its existing authorization. The phone verifies received evidence against its own accepted chain.

Direct messages use X25519 and XSalsa20-Poly1305. NOID authorization uses the production Owner proof protocol. The community chat and blockchain payments are public.

## Verification on the phone

The node checks the header chain from genesis, proof of work, fork certificates and the recursive State proof. Wallet inputs and payment receipts are authenticated against accepted headers and State roots.

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
