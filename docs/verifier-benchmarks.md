# Command-line verifier measurements


**Full mainnet synchronization from scratch: 48.43 seconds on an entry-level Redmi 15C smartphone.**

Measured on a **Redmi 15C with 4 GB RAM**, Android 15, ARM64, using its own **4G connection through a VPN**. The client ran natively in Termux with a release build and mainnet Small proofs.

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
