# Paramo1d

A native Rust client for verifying Parano1d on mobile devices. It connects directly to mainnet peers, checks the header chain from genesis and verifies the current recursive State proof and fork certificates.

Verification uses all available CPU cores automatically. Compressed matrices stay on disk and are processed in bounded buffers. The terminal shows download progress, verified heights, synchronization time and peak memory use.

## Benchmarks

**Full mainnet synchronization from scratch: 48.43 seconds on an entry-level Redmi 15C smartphone.**

Measured on a **Redmi 15C with 4 GB RAM**, Android 15, ARM64 and **8 CPU cores**, using its own **4G connection through a VPN**. The client ran natively in Termux with a release build and mainnet Small proofs.

The measurement started with an empty chain-data directory. Verification parameters and prepared matrix caches were installed beforehand.

| Measurement | Result |
| --- | ---: |
| Mainnet sync from scratch | **48.43 s** |
| Accepted mainnet block | 249884 |
| Headers checked from genesis | 249,885 |
| Header-chain verification | 7.44 s |
| Current State proof verification | **10.78 s** |
| Peak process memory | **192.2 MiB** |

Full synchronization time includes runtime loading, peer discovery, downloads and verification from genesis to the accepted mainnet block.

Once synchronized, downloading and verifying a new block took **11.94–13.20 s**. The running client reused its checked header prefix and authenticated certificates, with fresh verification of each new State proof. Peak process memory reached **193.2 MiB** during these updates.

## Build

Requires Rust 1.96 and Clang with libclang. The Rust version is set in `rust-toolchain.toml`.

```sh
cargo build --locked --release
cargo test --locked
python3 scripts/check-upstream.py
```

For Android ARM64, install the Rust target and build with the Android NDK:

```sh
rustup target add aarch64-linux-android
python3 scripts/build-android.py --ndk /path/to/android-ndk --cli
```

The Android outputs are `target/aarch64-linux-android/release/paramo1d` and `libparamo1d.so`. Minimum Android API: 26. The verification backend requires NEON and PMULL on ARM64, or SSE4.1 and PCLMULQDQ on x86-64.

## Verification parameters

Prepare the parameters from the release inputs matching [`profiles/mainnet.json`](profiles/mainnet.json). The input directory contains `history-step-pack-v1`, `history-step-pack-v2` and `history-step-pack-v21`.

```sh
target/release/paramo1d prepare \
  --source /path/to/release-inputs \
  --artifacts ./artifacts
```

Preparation checks the release metadata and matrix identities, then writes compressed matrices and authenticated row-span caches. The client checks these caches against compiled SHA-256 pins and computes fresh matrix claims for each proof. Install the resulting `artifacts` directory alongside the client.

## Run

```sh
PARAMO1D_TERMINAL=1 ./paramo1d run \
  --artifacts ./artifacts \
  --data-dir ./mainnet
```

The client discovers peers through the mainnet DNS seeds and downloads chain data directly over P2P. It checks header linkage, difficulty, timestamps, State expansion and proof of work, then authenticates the fork certificates and recursive State proof.

After synchronization, it follows new blocks. Updates preserve accepted chainwork and the accepted finality boundary. `mainnet/accepted.json` records the verified height, block hash, State root, timings and peak memory.

Add `--once` for a single synchronization pass. Use `--threads N` before the subcommand to select a smaller CPU budget. Run `./paramo1d --help` for all commands.

## Offline verification

Export a public proof bundle from an ordinary node's database in read-only mode:

```sh
paramo1d export --node-data /path/to/node --output ./bundle
paramo1d verify --artifacts ./artifacts --bundle ./bundle
```

`export --height H` selects an available earlier block. The bundle contains headers, the recursive proof and public fork certificates.

The `fetch` command collects a bundle through an ordinary node's RPC:

```sh
paramo1d fetch \
  --rpc http://127.0.0.1:9601 \
  --origins /path/to/node/fork-origins \
  --output ./bundle
```

`verify --repeat 2` measures repeated verification in one process. Streaming is the default matrix mode. `--matrix-mode resident` selects the packed-row implementation.

## Library

Rust callers use `Verifier` to retain authenticated runtime data across updates. Successful verification returns a `VerifiedState` with the accepted height, block hash and State root.

The [C interface](include/paramo1d.h) provides one-shot verification and reusable sessions. Call verification on a worker thread. Session configuration contains `artifacts`, with an optional `threads` field:

```json
{"artifacts":"/private/app/artifacts"}
```

Create a session with `paramo1d_session_new_json`, then pass `{"bundle":"/private/app/bundle"}` to `paramo1d_session_verify_json`. Calls are serialized. Release returned JSON with `paramo1d_free_json` and close the session with `paramo1d_session_free` after pending calls finish.

Matrix caches bind canonical rows to the released matrix identity through compiled SHA-256 pins. Their use relies on SHA-256 second-preimage resistance and process-private cache memory. Each proof receives fresh extension-field evaluation.

## Source and license

The verifier uses Parano1d source pinned at `848209d5db75137483cb41a94b310ad11463473f`. [`vendor/upstream.json`](vendor/upstream.json) records the source hashes. [`vendor/client-overrides.json`](vendor/client-overrides.json) records the mobile adapters. `scripts/check-upstream.py` checks both inventories and the vendored MDBX binding.

The `isolated-testnet` build feature selects the local test profile in [`profiles/isolated.json`](profiles/isolated.json).

Licensed under [Apache-2.0](LICENSE).
