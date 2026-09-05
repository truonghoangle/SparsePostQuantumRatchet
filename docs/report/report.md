# Report: SPQR Functional Overview — The Top-Level (Bridging) Interface

**Venue:** Tuesday Hackathon
**Duration:** 15 minutes
**Companion slides:** [`report.pptx`](./report.pptx)

> This will be at the Tuesday Hackathon, and it will be a broad overview of the functionality, with perhaps special mention of functions relevant for bridging, i.e., top-level interface.

---

## Timing Plan (15 minutes)

| Slot | Section | Time |
|---|---|---|
| 1 | Context: SPQR and this verification project | 2 min |
| 2 | The bridging surface: `src/lib.rs` at a glance | 2 min |
| 3 | Session lifecycle: `initial_state` → `send` / `recv` | 5 min |
| 4 | Supporting API: versioning, secrets, errors | 3 min |
| 5 | Verification status of the interface, Q&A | 3 min |

---

## 1. Context (2 min)

- **SPQR** (Sparse Post-Quantum Ratchet) is Signal's Rust crate that adds
  ML-KEM 768 based post-quantum forward secrecy to the messaging ratchet, with
  KEM material *sparsely* spread over many messages.
- This repository verifies that crate in **Lean 4**: Rust → Charon → Aeneas
  (`SrcTranslated/`) → hand-written specs in `Spqr/Specs/`, mirroring the Rust
  module tree.
- Internals (`chain`, `authenticator`, `encoding`, `incremental_mlkem768`,
  `kdf`, `serialize`, `v1`) are large, but a **bridge** (e.g. a higher-level
  messaging library, FFI layer, or another language binding) sees only the
  small public API in `src/lib.rs`. That interface is the focus of this talk.

## 2. The bridging surface at a glance (2 min)

Everything crossing the boundary is a byte vector or a plain enum; the bridge
never needs the protobuf schema or any internal type.

```rust
// Opaque byte types
pub type Epoch             = u64;
pub type Secret            = Vec<u8>;
pub type MessageKey        = Option<Vec<u8>>;
pub type SerializedState   = Vec<u8>;
pub type SerializedMessage = Vec<u8>;

// Re-exported for callers
pub use chain::ChainParams;
pub use proto::pq_ratchet::{Direction, Version};   // Direction::{A2B,B2A}, Version::{V0,V1}
```

| Function | Signature | Purpose |
|---|---|---|
| `empty_state` | `() -> SerializedState` | Disabled (V0) state: empty bytes. |
| `initial_state` | `(Params) -> Result<SerializedState, Error>` | Create one side of a session. |
| `send` | `(&SerializedState, &mut impl Rng+CryptoRng) -> Result<Send, Error>` | Produce next outgoing PQ header + key. |
| `recv` | `(&SerializedState, &SerializedMessage) -> Result<Recv, Error>` | Consume peer header, negotiate version, derive key. |
| `current_version` | `(&SerializedState) -> Result<CurrentVersion, Error>` | Inspect negotiation status. |

Pattern for a bridge: **state in → (state, msg, key) out**; the caller
persists the returned state and never mutates it.

## 3. Session lifecycle (5 min)

### 3.1 `initial_state(params: Params) -> Result<SerializedState, Error>`

```rust
pub struct Params<'a> {
    pub direction: Direction,      // A2B or B2A – the two sides must differ
    pub version: Version,          // V0 = disabled, V1 = current (Version::MAX)
    pub min_version: Version,      // lowest version we accept when negotiating down
    pub auth_key: &'a [u8],        // shared key for MAC authentication
    pub chain_params: ChainParams, // out-of-order / jump limits for the key chain
}
```

- `Version::V0` → returns `empty_state()`; the ratchet is off.
- Otherwise builds a protobuf `PqRatchetState` with:
  `inner = V1 state (init_a / init_b by direction)`,
  `version_negotiation = Some{auth_key, direction, min_version, chain_params}`,
  `chain = None` (created lazily on first send/recv).
- Bridge takeaway: call once per session, store the bytes.

### 3.2 `send(state, rng) -> Result<Send, Error>`

```rust
pub struct Send {
    pub state: SerializedState,   // new state – replace the old one
    pub msg:   SerializedMessage, // PQ header to attach to the outgoing message
    pub key:   MessageKey,        // Some(k): mix into the sending chain; None: nothing yet
}
```

- V0 state → `Send { state: [], msg: [], key: None }` (no-op).
- V1 state → runs the v1 state machine (`States::send`), then:
  - lazily creates the `Chain` from the version-negotiation params if needed;
  - if the state machine produced an epoch secret, `chain.add_epoch(secret)`;
  - `chain.send_key(epoch - 1)` gives `(index, msg_key)`;
  - serialises the header with `msg.serialize(index)`; invariant `msg[0] == Version::V1`.
- **Never changes `version_negotiation`** — sending can't finish negotiation.
- Errors: `StateDecode`, `ChainNotAvailable`, plus chain errors
  (`KeyJump`, `SendKeyEpochDecreased`, …).

### 3.3 `recv(state, msg) -> Result<Recv, Error>`

```rust
pub struct Recv {
    pub state: SerializedState,   // new state
    pub key:   MessageKey,        // Some(k): key for decrypting this message
}
```

Two phases:

1. **Version negotiation** (compare `msg[0]` with our state version):
   - message version unknown (too high) → return the *unchanged* state, `key: None`;
   - equal or greater → proceed with current state;
   - lower → if `version_negotiation` is `None` → `Error::VersionMismatch`;
     if below `min_version` → `Error::MinimumVersion`;
     otherwise **re-initialise** at the peer's version, keep/create the chain,
     and set `version_negotiation = None` (no further downgrades).
2. **Processing**:
   - V0 → `Recv { state: [], key: None }`;
   - V1 → `Message::deserialize(msg)` → `States::recv` → optional
     `chain.add_epoch` → `chain.recv_key(epoch - 1, index)` (skipped for the
     very first message, epoch 0 / index 0).
   - Receiving always **clears `version_negotiation`**.
- Errors: `MsgDecode`, `MacVerifyFailed`, `EpochOutOfRange`, `KeyTrimmed`,
  `KeyAlreadyRequested`, `ErroneousDataReceived`, `Serialization`, `EncodingDecoding`.

### 3.4 Putting it together (bridge pseudo-flow)

```text
A: st = initial_state{A2B, V1, V1, k, cp}      B: st = initial_state{B2A, V1, V1, k, cp}
A: {st, msg, key} = send(st, rng)  ─ msg ─▶   B: {st, key} = recv(st, msg)
   key → mix into A's sending chain              key → mix into B's receiving chain
B: {st, msg, key} = send(st, rng)  ─ msg ─▶   A: {st, key} = recv(st, msg)
```

## 4. Supporting API (3 min)

### Version inspection

```rust
pub enum CurrentVersion {
    StillNegotiating { version: Version, min_version: Version },
    NegotiationComplete(Version),
}
pub fn current_version(state: &SerializedState) -> Result<CurrentVersion, Error>;

impl Version { pub const DISABLED: Version = V0; pub const MAX: Version = V1; }
impl TryFrom<u8> for Version;   // 0 → V0, 1 → V1, else Err
impl From<Version> for u8;
impl Direction { pub fn switch(&self) -> Self }  // A2B ↔ B2A
```

### Secret routing

```rust
pub enum SecretOutput { None, Send(Secret), Recv(Secret) }
impl SecretOutput {
    pub fn send_secret(&self) -> Option<&Secret>;  // only for Send(_)
    pub fn recv_secret(&self) -> Option<&Secret>;  // only for Recv(_)
    pub fn secret(&self)      -> Option<&Secret>;  // either
    pub fn has_secret(&self)  -> bool;             // != None
}
```

Tells the bridge *which* symmetric chain a freshly agreed secret belongs to.

### Errors a bridge must handle

`StateDecode`, `NotImplemented`, `MsgDecode`, `MacVerifyFailed`,
`EpochOutOfRange(Epoch)`, `EncodingDecoding(EncodingError)`,
`Serialization(serialize::Error)`, `VersionMismatch`, `MinimumVersion`,
`KeyJump(u32,u32)`, `KeyTrimmed(u32)`, `KeyAlreadyRequested(u32)`,
`ErroneousDataReceived`, `SendKeyEpochDecreased(u64,u64)`,
`InvalidParams(&str)`, `ChainNotAvailable`.
`From` impls lift `EncodingError`, `serialize::Error`, and
`authenticator::Error` (→ `MacVerifyFailed`) into `Error`.

## 5. Verification status of the interface (3 min)

| Interface item | Lean spec (`Spqr/Specs/Lib/…`) | Status |
|---|---|---|
| `empty_state` | `EmptyState.lean` | done |
| `decode_state` (helper used by all entry points) | `DecodeState.lean`, `DecodeState/CallOnce.lean` | done |
| `current_version` | `CurrentVersion.lean`, `CurrentVersion/CallOnce.lean` | done |
| `SecretOutput::{secret, send_secret, recv_secret, has_secret}` (+`Eq`, `Fmt`) | `SecretOutput/*.lean` | done |
| `Version::{DISABLED, MAX}`, `TryFrom<u8>`, `From<Version> for u8` | `Version/*.lean` | done |
| `Error: From<…>` | `Error/From.lean` | done |
| `initial_state` | — | next |
| `send` | — | next (depends on `Chain::{add_epoch, send_key}`, `v1::States::send`, `Message::serialize`) |
| `recv` | — | next (depends on `Chain::recv_key`, `v1::States::recv`, `Message::deserialize`) |

- Building blocks already specified: `Spqr/Specs/Chain/` (`KeyHistory`,
  `ChainParams`, epoch handling), `Spqr/Specs/Serialize/` (varint/chunk
  codecs), `Spqr/Specs/V1/` (state ↔ protobuf round-trips),
  `Spqr/Specs/Authenticator/`, `Spqr/Specs/Kdf/`.
- Goal: compose these into end-to-end statements about `send`/`recv`, e.g.
  "state returned by `send`/`recv` always decodes", "`send` preserves
  `version_negotiation`", "`recv` clears it", "unknown message version leaves
  state unchanged".
- Questions.

