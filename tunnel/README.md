# Application transport

The Android client carries its selected chat and wallet connections through AmneziaWG or authenticated HTTPS WebSockets. HTTPS starts after a 250 ms head start for AmneziaWG. HTTPS requests select a route after TLS verification. The winning connection carries the application request.

Read requests can recover over HTTPS after a transport failure. Message publication and transaction submission use a single application request. Existing streams stay open when another connection selects HTTPS.

## Relay capacity

The Linux relay accepts these options:

| Option | Default |
| --- | ---: |
| `--max-peers` | 4096 registered devices |
| `--max-streams` | 4096 concurrent streams |
| `--streams-per-peer` | 16 concurrent streams per device |

AmneziaWG and HTTPS share the same stream budgets. The chat service permits 2048 concurrent synchronization waits. Its retained-message budget is 200,000 messages and 1 GiB of encoded envelopes. Messages expire after seven days.

Size the reverse proxy and service file-descriptor limits for all streams and their upstream connections. A tunnel stream requires two relay sockets. Proxy requests arriving from the relay's loopback connection share the server's IP address. Apply the global request budget to them and reserve per-IP budgets for external clients.

## Enrollment compatibility

Updated clients request `address_bits: 16` and receive an address from `10.80.0.0/16`. Existing enrollments retain their addresses. Clients that omit this field receive an address from the legacy `10.80.0.0/24` pool. That pool supports 248 device addresses.

Deploy the updated relay before distributing the updated Android client. Existing Android clients continue using the legacy pool. The relay's loopback `/healthz` reports registered devices, active streams and configured limits.
