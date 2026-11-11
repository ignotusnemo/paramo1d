Paramo1d 0.1.2 makes wallet refresh adaptive, renews payment epochs automatically and includes the conversation, QR scanning and connection improvements from 0.1.1.

### Wallet updates and payment readiness

- **Fast balance checks.** Update balance checks for changed coins and keeps the verified balance when they are unchanged. An unchanged-balance check on the Redmi completed in 1.08 seconds.
- **Automatic epoch renewal.** While the app is open and unlocked, funded wallets watch the transaction epoch. An epoch change refreshes the verified State in the background, including when the balance stays the same.
- **Shared checks.** Manual refresh uses an automatic check already in progress. Payment review waits for its result and reuses the updated State.
- **Available balance during renewal.** The balance stays visible and the refresh control remains available while the app prepares payments for the current epoch in the background.
- **Reliable completion.** Errors and a full worker queue release the updating status. The app preserves the verified balance and can retry.

New coins, changed inputs and a new transaction epoch still require independent State verification on the phone. The wallet uses its authenticated checkpoint and checked slot proofs to prepare payments. Online review and authorization check epoch freshness.

### Conversations and contacts

- Compact message bubbles, colored author names and locally generated pixel warrior avatars.
- Replies with a jump to the original message. Copy text, select text and emoji reactions from the message menu.
- Emoji picker, separate saved drafts and search within a conversation.
- Contact links appear as verified contact cards with Copy link, Add contact and Message actions.
- Stable scrolling while reading earlier messages. A down arrow returns to new messages.

### Payments, connections and interface

- Scan receiving QR codes in Send NOID and signed contact QR codes in Add contact. Scanning fills the form for review.
- Clear expired-payment messages and a fresh review action for the sender. Authorization checks the current wallet checkpoint and observed transaction epoch.
- Protected connections renew their idle timeout while data is flowing.
- Consistent rounded controls in light and dark themes. Startup and the unlock screen use a short coin animation with a cached image.
- Allow screenshots through an optional setting that starts off.

### Installation

Install this APK over an earlier official release to retain the wallet, chats and settings. The signing certificate is unchanged.

The APK includes mainnet verification parameters. It requires Android 8.0 or later and ARM64 hardware with AES and PMULL support. Release downloads include `SHA256SUMS` and `SIGNING-CERTIFICATE.txt`.

[Android documentation](https://github.com/ignotusnemo/paramo1d/blob/main/android/README.md) · [Redmi device checks](https://github.com/ignotusnemo/paramo1d/blob/main/android/reports/redmi-15c-2026-11-10.md)
