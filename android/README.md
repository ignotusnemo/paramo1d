# Paramo1d for Android

Paramo1d combines a full Parano1d node, native NOID wallet and encrypted messenger on Android. Send, receive and request NOID directly inside a chat. Use ordinary internet, enable the built-in app-only protected connection or exchange messages, authorized payments and receipts with nearby participants over Bluetooth.

The wallet prepares and authorizes payments on the device. A connected participant can broadcast an already-authorized payment and return its inclusion receipt. The phone's own node verifies the chain and checks the receipt.

The application uses the existing mainnet transaction format, Owner authorization and recursive State verifier. The consensus source and release pins remain in `vendor/` and `profiles/mainnet.json`.

## Conversations

Tap the three dots beside a message or hold its bubble to reply, copy text, select text or add a reaction. Tapping a quoted reply takes you to the original message saved on the phone. The smile button opens the emoji picker. Search in the conversation header finds messages and author names.

Each conversation keeps its own draft in the encrypted local archive. Reading earlier messages preserves the scroll position when new messages arrive. The down arrow returns to the latest messages. History loads in bounded windows.

**Add contact** includes a Scan button for contact QR codes. Scanning checks the signed contact and shows its name before **Add contact** saves it. **Send NOID** also has a Scan button beside the recipient field. It reads a receiving QR code, checks the address checksum and fills the recipient. The amount and fee are reviewed separately.

Pasting a Paramo1d contact link creates a contact card. The phone checks its signature before showing the identity and Add contact or Message actions. Copy link preserves the original contact link. Pixel warrior avatars are generated locally from each messaging identity and appear consistently in the conversation list, messages and contact cards.

Replies and reactions use readable, signed text inside the existing message envelope. The same envelopes travel through internet delivery and Bluetooth. Both conversation participants can update their application independently.

## Payment delivery

1. Open a direct conversation to request or send NOID.
2. Review the recipient, amount and network fee. Authorize the exact reviewed payment on the device.
3. The wallet submits the packet to its configured chain endpoint. If delivery is unavailable, select **Ask the community to help**.
4. A participant selects **Help send this payment** and reviews the packet. The participant forwards the existing authorization and needs no spending secret.
5. The same card collects authenticated helper observations. **Check payment** checks a returned receipt against the device's verified chain.

The card distinguishes ready-to-relay packets, node submission, reported mempool presence, received inclusion evidence and locally verified inclusion. Finality uses the finality depth of the verified chain. Helper counts identify contributors. Each helper's observation remains an attributed report until the client checks its inclusion evidence.

Offline preparation uses the saved, verified State bundle and slot proofs. The saved view must contain spendable inputs and empty output slots. Inputs and output slots used in pending authorizations are reserved locally. Spent inputs or an expired epoch anchor require a new review and authorization.

The client saves its verified wallet view with a local authentication tag. The tag binds the verified tip, the slot-proof header, the transaction epoch header, the account and the pinned verification profile. Its key is derived from the protected wallet identity with a separate domain. A saved view is created after State and slot-proof verification. Reopening checks its tag and slot membership proofs before reuse. A missing or invalid tag requires full verification. Online payment review also checks the observed chain height and refreshes the verified view when the transaction epoch changes.

Authorization rechecks the reviewed payment against the authenticated wallet checkpoint. An online authorization checks the observed height again. When the network rejects an expired authorization, its card shows **Payment expired**. The sender can select **Review fresh payment** to update the wallet and review a replacement. A helper is asked to contact the sender. An inclusion receipt can still establish that an earlier payment already reached the chain.

Full proof verification authenticates its parameters and preserves accepted chainwork and finality. The worker retains immutable matrix data in a bounded cache to avoid repeated decoding and authentication. The canonical matrix byte budget is 640 MiB while the app is open and 192 MiB after it is minimized. Android memory-pressure callbacks release the cache. A saved proof result can be reused in the running process only with the same bundle path and a fresh SHA-512 fingerprint of its consumed files. On a fresh synchronization after restart, the client checks the saved header prefix and verifies a newer recursive proof directly.

The initial wallet derives its ordinary NOID receiving address at index zero. Invoices carry an off-chain request identifier, address, amount and memo. A verified receipt establishes the transaction's outputs and inclusion. Account for each transaction ID once when reconciling invoices.

## Connections and battery use

The default service is `https://chat.parano1d.org`. Open **Connections** to see internet delivery, **App VPN** and Bluetooth separately. Each optional connection has an On or Off switch and a description of its current state. The header shows Online, Bluetooth only, Offline or Connecting. Its indicator is green, blue, red or amber respectively. Light, dark and system appearance are available in Settings.

Community and direct messages use configurable HTTPS delivery relays. The relay retains messages for up to seven days. The client keeps an encrypted local archive and retries its outbox after reconnecting. Authenticated requests wait up to ten seconds for new community or inbox messages and return immediately on delivery. Outgoing messages use a separate worker. Idle reads preserve the existing encrypted archive without rewriting it.

**Background messages** is on by default. It keeps a visible Android notification and maintains message delivery while the app is minimized or the screen is off. It can be disabled in Settings. App VPN also uses this foreground service. Direct conversations have unread counters. Message notifications open the relevant conversation and hide their contents while App lock is enabled.

Read acknowledgements follow the visible conversation. Wallet and Settings screens preserve unread messages. Opening a conversation clears its notification. A requested wallet check keeps the screen awake while the app window remains visible. Automatic node updates follow the phone's ordinary screen timeout.

The protected connection uses an application-owned AmneziaWG stack and an authenticated HTTPS WebSocket fallback. Only Paramo1d sockets use it. HTTPS certificates and hostnames are verified. The production gateway permits the chat service and mainnet seed connections. If the phone already has a working VPN, leave App VPN off. Otherwise, App VPN provides a connection option within Paramo1d.

Successful reads and writes renew the protected stream's idle timeout. Active chat and node connections can continue across the timeout interval.

Bluetooth links authenticate both contact cards and fresh session challenges, then encrypt frames. A device can retain an envelope addressed to another contact and carry it without decrypting its contents. Nearby exchange keeps at most two active links and a bounded inventory. A received payment packet is locally checked with the native Owner verifier before it appears as authorized. Its inclusion receipt is checked separately against the phone's verified chain.

The wallet uses adaptive updates while the application is open and unlocked. Small queries watch its coin set. A change in amount, slot or incarnation triggers independent verification of the latest State and the relevant slot proofs. Unchanged hints retain the last verified balance and its original check time. Funded wallets also watch the transaction epoch and renew their verified checkpoint in the background when it changes. **Update balance** uses the same change detection and shares an active check. Payment review waits for an active automatic check to finish and then uses its result. A new wallet starts its initial check when the Wallet screen is opened.

Minimizing the application or locking the screen cancels the node check and closes its P2P connections. Background messages continue independently. Reopening resumes the watch from the saved wallet view. An already-approved payment can finish saving its authorization if the app is closed. A helper polls a bounded set of submitted transaction IDs while the application is open. These small status requests run separately from State synchronization. Helper watches expire after an hour or stop when they collect an inclusion receipt.

The wallet's chain data endpoint supplies slot discovery, membership proofs and transaction submission. Slot contents are checked against an independently verified State root. A compatible endpoint implements `paranoid_getSlotsByOwner`, `paranoid_getSlotHints`, `paranoid_getSlotProof`, `paranoid_submitTxIntent`, `paranoid_getTx`, `paranoid_getMempoolEntry` and `paranoid_getBlock`.

## Identity and storage

**App lock** uses the phone's existing fingerprint or screen lock at entry. It is enabled by default when the device has a screen lock. The app locks after 30 seconds away or immediately through **Lock now** in Settings. An unlocked session covers chats, payment review and backup export. Sending a payment uses the ordinary recipient, amount and fee review. The backup password encrypts the portable file and is used to restore it on another device.

**Allow screenshots** in Settings permits screenshots and screen recordings on this phone. It is off by default. Camera access is requested when opening the QR scanner. Scanning runs locally with ZXing and closes the camera when leaving the scanner. The scanner's license notices are bundled in `SCANNER-NOTICES.txt`.

An identity begins with 32 random bytes generated on the device. Domain-separated derivation supplies the existing NOID spending secret and separate messaging keys. Direct envelopes use X25519 and XSalsa20-Poly1305. Ed25519 authenticates message envelopes, contact cards and mailbox reads. Contact links can be shared as QR codes. Delivery services observe routing metadata. The community chat and on-chain NOID payments are public.

The Android Keystore protects the local AES-GCM archive key. Portable backups use Argon2id and XChaCha20-Poly1305 with fresh salt and nonce. Export an encrypted backup and keep its password separately. Restore through Android's document picker on an empty installation.

Open **Settings → Chat storage** to see message counts and local storage use. Community can be cleared separately. Select any private conversations or use Select all. A conversation's three-dot menu also opens **Clear history** with that chat already selected. Clearing affects history on this phone and keeps contacts, drafts, queued messages, the wallet and saved payment records.

Each private chat has a three-dot menu in the Messages list. **Delete chat** removes its message history, draft and contact from this phone. New messages from that person start a new chat. Already queued deliveries continue, and the wallet and saved payment records are preserved. The same action is available in the open chat's three-dot menu.

Community and private chats use a floating message field. History scrolls behind the controls, with enough space to keep the latest message visible. Mobile navigation floats above the bottom edge and hides while the keyboard is open. Replies, multiline drafts and the emoji picker adjust the space automatically.

Local message storage has explicit entry and byte limits. A full archive pauses incoming delivery without advancing past an unhandled message. The app opens the chat chooser when space runs out and leaves a visible Choose chats reminder after dismissal. Background delivery posts a storage notification. Recently cleared message IDs remain in a bounded replay cache for their delivery lifetime, so ordinary relay retries and Bluetooth exchange preserve the cleanup. The cache retains at most 20,000 IDs for at most seven days. Completed payments are excluded from the pending-input reservation budget.

The bundled WebView loads its interface, fonts and scripts from APK assets. Network requests and wallet operations execute in the native host. The JavaScript view receives public profile information, conversation content and payment reviews. Secret-bearing requests are constructed in the native host.

## Build

Requirements: Rust 1.96, the `aarch64-linux-android` target, Android NDK, Go 1.27.3, JDK 21, Gradle 8.14.3, SDK platform 36 and build tools 36.0.0. The phone needs Android 8 or later, an updated Android System WebView, ARM64, NEON, AES and PMULL. The native library checks the hardware capabilities before verification. The build enables these instructions for inlining field arithmetic.

Prepare the release parameters as described in the root README, then run:

```sh
python3 scripts/build-courier.py \
  --ndk /path/to/android-ndk \
  --sdk /path/to/android-sdk \
  --java-home /path/to/jdk-21 \
  --gradle /path/to/gradle-8.14.3/bin/gradle \
  --artifacts /path/to/prepared-mainnet-artifacts \
  --go /path/to/go/bin/go
```

The script checks the upstream source inventory and parameter pins. It packages compressed verification parameters and the native ARM64 library. The APK is written to `android/app/build/outputs/apk/debug/app-debug.apk`. The first synchronization installs the parameters into private application storage. The verifier authenticates release metadata, matrix caches and proof claims. SHA-256 uses the library's ARM hardware backend when the processor supports it and its software fallback otherwise.

### Signed releases

Use `--variant release` with `PARAMO1D_ANDROID_KEYSTORE_PATH`, `PARAMO1D_ANDROID_STORE_PASSWORD` and `PARAMO1D_ANDROID_KEY_ALIAS` supplied through the build environment. The signed APK is written to `android/app/build/outputs/apk/release/app-release.apk`.

Release keys stay in the owner's private signing storage and encrypted GitHub repository secrets. The Android workflow retrieves the pinned public parameter archive, runs the checks and publishes signed APKs for version tags. Release downloads include SHA-256 hashes and the public certificate fingerprint.

Android updates require a matching signing certificate. Development APKs use the Android debug key. Preserve an encrypted portable backup when moving a development installation to the release certificate.

## Local device testing

Start a relay on the development machine:

```sh
cargo run -p paramo1d-relay -- --database ./relay-data/messages.db
adb install -r android/app/build/outputs/apk/debug/app-debug.apk
adb reverse tcp:9711 tcp:9711
```

For a local relay, set `http://127.0.0.1:9711` in **Settings → Advanced connection settings**. The installed default uses the public HTTPS service. A local node RPC can be reached through a separate `adb reverse` mapping. The development APK uses the Android debug signing key.

The [Redmi device report](reports/redmi-15c-2026-11-10.md) records the public deployment, actual Bluetooth exchange, native payment checks and observed mainnet transaction. Portable backups use Android's document picker. Keep the encrypted backup and its password separately.

## Checks

```sh
cargo test --locked --lib
cargo test --locked -p paramo1d-courier -p paramo1d-relay
python3 scripts/check-upstream.py
/path/to/gradle -p android :app:testDebugUnitTest
cd android/tests
npm install
npm test
```

Browser tests use a deterministic native-view fixture. They cover mobile layout, status presentation, payment review and safe rendering of message text. Rust tests exercise real envelope encryption, authentication, relay persistence, mailbox access, encrypted backups, authenticated slot proofs and native payment authorization.

The [Android storage check](storage-check/README.md) exercises the production Keystore archive and native backup implementation in a separate fixture package on a device. Its second stage checks persistence after restarting that package.

Run `go test ./...` from `tunnel/` for the application tunnel. Its pinned dependencies and license texts are listed in [THIRD-PARTY-NOTICES.txt](../tunnel/THIRD-PARTY-NOTICES.txt).

For an internet relay, terminate HTTPS at a reverse proxy, retain request size limits and apply per-IP rate and connection limits. Keep its database on persistent storage. The relay binary binds to loopback by default. Chain RPC access should expose only the read and submission methods required above.
