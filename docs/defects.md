# Code Defects Identified from Specification Theorems

This report lists properties of the **Rust code** in `src/` (and of its integration into
libsignal) that the Lean spec theorems under `Spqr/Specs/` had to assume as preconditions, or
behaviour that their postconditions expose. All spec theorems referenced are proved; the defects
are in the Rust source, its annotations, or the trusted Lean models — not in the proofs.

## How to read this report

**Numbering.** Each finding has a stable identifier `D1`–`D40`, shared with
`Spqr/Specs/Bugs/*.lean`, the counterexample files in `docs/`, and the companion reports
(`CorruptedBlobs.md`, `network.md`, `bugSecurityRemote.md`). Findings are arranged **by theme**
rather than by identifier so that interconnected issues read together. Not every identifier is a
defect: D9, D12 and D15 are *audit notes* (rated INFO or NO DEFECT) kept under the same numbering
because the companion files cite them.

**Grouping.** Related identifiers appear in one of three forms:

- *combined heading* (`D22 / D31 / D35 / D36`) — one fix closes all of them;
- *nested sub-finding* (`D4 / D18` under D19; `D37` under D14) — a consequence or documentation
  facet of the parent, kept separate because it has its own evidence;
- *sibling with cross-reference* (`D32` after D28; `D38` after D24) — shares a root cause but has
  a distinct trigger or fix.

**Severity.** Each heading carries `(SEVERITY; qualifier)`:

| Level | Meaning |
|---|---|
| HIGH | Panic, key divergence, or unsound trusted-base model reachable in a realistic deployment |
| MEDIUM | Denial of service, downgrade, silent wrong result, or a false verification annotation |
| LOW | Latent, needs an unrealistic precondition, or documentation-only |
| INFO / NO DEFECT | Audit result recorded for completeness |

Qualifiers name the reach: `message` (an on-path message suffices), `blob` (needs influence over
the persisted state), `local-config` (needs a bad `ChainParams`), `32-bit`, `spec` (affects
soundness of annotations or models, not runtime). D10 is rated on both the `spec` and runtime axes
because they differ.

**Attacker model and terms.** *On-path* / *network-only* attacker: can read, drop, inject and
modify messages but holds no session secret. *Authenticated-but-malicious peer*: the legitimate
remote party behaving adversarially. *Blob*: the persisted `pq_ratchet_state` protobuf. DR =
Double Ratchet; PCS = post-compromise security; FO = Fujisaki–Okamoto transform; IKM = HKDF input
keying material. The full attacker-model discussion is in [`docs/network.md`](./network.md) and
[`docs/bugSecurityRemote.md`](./bugSecurityRemote.md).

**Host mitigation (referenced throughout).** libsignal (`session_cipher.rs` L607–694) clones the session, calls
`pq_ratchet_recv` (`session_cipher.rs` L633), derives the Double-Ratchet message keys with the
SPQR key as HKDF salt (`ratchet/keys.rs` L25, L96), and only then runs `verify_mac` (L657–668);
on failure the clone is dropped. A network-only attacker's forgery is therefore not persisted in
libsignal. This mitigation (a) lives outside SPQR and is not documented as a requirement of the
SPQR API, (b) does not protect any other embedder of the crate, and (c) does not protect against
an authenticated-but-malicious peer, who can then blame the resulting stall on the victim.
Findings below are stated for SPQR itself; libsignal reach is noted in each.

**Methodology.** All 231 spec files under `Spqr/Specs/` were surveyed; their
preconditions/postconditions were cross-referenced against the 39 Rust sources in `src/`, the
`sorted-vec 0.8.6` and `libcrux-ml-kem 0.0.7` dependencies pinned in `Cargo.lock`, and the
libsignal integration at commit `a47ba487` (`rust/protocol/src/{ratchet.rs, session_cipher.rs,
state/session.rs, ratchet/keys.rs, consts.rs}`). `lake build Spqr SrcTranslated` (2553 jobs)
completes with only the two expected `sorry` warnings (see D15), confirming the referenced
theorems compile as read. Every finding with a **Reproduced:** line has an executable
counterexample under `docs/`; the [Evidence and coverage](#evidence-and-coverage) table is the
authoritative mapping from identifier to file. Rust harnesses were run on a scratch copy of the
crate, since `src/` is a pinned upstream tree.

**Line numbers** refer to `src/` at the commit this repository pins (spqr v1.5.0) and to
libsignal `a47ba487`; they are given for orientation and may drift.

---

## Index

| Part | Theme | Items (in reading order) |
|---|---|---|
| I | Unauthenticated control plane: forged messages that stall, deadlock or downgrade | 24, 38, 19 (4, 18), 25, 39, 40 |
| II | Arithmetic and parameter bounds the specs could not discharge | 2, 28, 32, 8, 10, 3, 5 |
| III | Deserialisation without validation (corrupted / injected state blobs) | 1, 21, 22 (31, 35, 36), 26, 34, 13, 14 (37), 16, 17, 27, 30 |
| IV | Cryptographic hygiene and constant-time primitives | 11, 12, 29 (33) |
| V | Soundness of the Lean trusted base and limits of the verified surface | 20, 15, 6 (7), 9, 23 |

Closing sections: **Priorities** · **Evidence and coverage** · **Limitations**.

**Identifier → Part.**
D1 III · D2 II · D3 II · D4 I · D5 II · D6 V · D7 V · D8 II · D9 V · D10 II ·
D11 IV · D12 IV · D13 III · D14 III · D15 V · D16 III · D17 III · D18 I · D19 I · D20 V ·
D21 III · D22 III · D23 V · D24 I · D25 I · D26 III · D27 III · D28 II · D29 IV · D30 III ·
D31 III · D32 II · D33 IV · D34 III · D35 III · D36 III · D37 III · D38 I · D39 I · D40 I

**Reading order** for someone new to the report: Part I first (the findings reachable by a
message alone in normal operation), then Part III (the largest attack surface once a state blob
can be influenced), then Part II (which explains most of the `hax_lib::assume!` sites), then IV
and V.

**Finding template.** Long-form findings use the sections **Specs that expose it → Rust defect →
Consequence → Reproduced → Fix**. Short-form findings compress these into one or two paragraphs
but keep the **Reproduced:** and **Fix:** labels where they apply.

---

## Part I — Unauthenticated control plane

**Common root cause.** SPQR authenticates *content* (the `hdr ‖ mac` and `ct2 ‖ mac` blobs,
checked by `verify_hdr`/`verify_ct` once a chunked message is fully reassembled) but not
*control flow*. `Message::deserialize` establishes only the wire layout and `0 < epoch`
(`Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean`); nothing in
`States::recv` consults the per-epoch `Authenticator` before acting on `epoch`, `index`, the
message type tag, or a chunk's `index`. Several state-machine edges therefore fire on data an
on-path attacker can produce for free. In libsignal the host mitigation described above stops
persistence for a network-only attacker but not for a malicious peer.

**Verified non-defects on this surface.** `ek_matches_header` (libcrux 0.0.7
`validate_pk_parts`) re-hashes `pk2 ‖ seed` against the MAC-authenticated `hdr` and checks the
modulus domain of `t`, so a forged `ek` cannot pass. Forged `ct1` chunks are bound to the peer's
`hdr` via `decaps` implicit rejection + `verify_ct`, so they cost the epoch (D19) but never the
secret.

### D24. Unauthenticated `Ct2Sampled → KeysUnsampled` epoch advance: one 4-byte forged message deadlocks the ratchet (MEDIUM; message, protocol-level DoS)

**Specs that expose it.**

- `Message.deserialize_spec`: for `payloadTag .None` the message is exactly
  `[1, varint(epoch), varint(index), 0]` — no MAC, no chunk, nothing peer-derived.
- `Spqr/Specs/V1/Unchunked/SendCt/Serialize/Ct2Sent/{From,Into}Pb.lean`: `Ct2Sent` carries only
  `epoch` and `auth`; no spec (and no Rust) consults `auth` on the `recv_next_epoch` edge. Every
  other state-changing transition either runs `verify_hdr`/`verify_ct` or is preceded by one.
- `Spqr/Specs/Chain/Chain/AddEpoch.lean` requires `epoch_secret.epoch = current_epoch + 1` and
  `EpochIdx.lean` rejects `epoch > current_epoch` — the chain layer *assumes* lock-step epochs.

**Rust defect** (`src/v1/chunked/states.rs` L513–526 → `chunked/send_ct.rs` L295 →
`unchunked/send_ct.rs` L200–208).

```rust
Self::Ct2Sampled(state) => match msg.epoch.cmp(&state.epoch()) {
    Ordering::Greater => {
        if msg.epoch == state.epoch() + 1 {
            Self::KeysUnsampled(state.recv_next_epoch(msg.epoch))   // no verify_*
        } else { return Err(Error::EpochOutOfRange(msg.epoch)); }
    }
    …
```

`recv_next_epoch` only does `assert_eq!(epoch + 1, next_epoch)` and rebuilds
`KeysUnsampled { epoch: epoch + 1, auth }`. The payload type is not inspected.

**Consequence.** With A in epoch 1 (still collecting `Ct2` chunks) and B in `Ct2Sampled(1)`, an
on-path attacker delivers `[1, 2, 1, 0]` to B:

| event | B | A |
|---|---|---|
| forged message arrives at B | `recv` → `Ok`, `key: Some(_)` (!), state `KeysUnsampled(2)`, chain `recv_key(1, 1)` consumed | — |
| B sends its next message | emits `Hdr` chunk at **epoch 2** | `recv` → `Err(EpochOutOfRange(2))` on every message, forever |
| A sends its next message | `Ordering::Less` → ignored | emits `Ct1Ack` at epoch 1 |

B never sends the remaining `Ct2` chunks for epoch 1; A never sends epoch 2. **Both directions
are permanently deadlocked**, and `recv` additionally hands the caller a DR chain key for a
message that was never authenticated.

**Reproduced:** `d24_unauthenticated_epoch_advance_deadlocks_ratchet` in
[`docs/protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt),
through the public `send`/`recv` API (debug and release). Formal model:
`Spqr/Specs/Bugs/ProtocolDoS.lean`.

**Fix:** gate the transition on authenticated evidence — only accept `epoch + 1` from a `Hdr`
chunk *after* that header's MAC verifies (defer `recv_next_epoch` until `recv_hdr_chunk … Done`),
or have the `epoch + 1` message carry `mac_hdr`-style authentication. At minimum, do not return a
chain key for a payload of type `None` that changed the epoch.

### D38. Unauthenticated `Ct1Ack` stalls epoch completion on both sides (MEDIUM; message, protocol-level DoS — sibling of D24)

D24 is the one control edge that *advances* the epoch; D38 is its counterpart on the edges that
*suppress future sends*. Both are triggered by data the `Authenticator` never sees.

**Specs that expose it.**

- `Message.deserialize_spec`: `MessageType::Ct1Ack` (tag 4) decodes to
  `MessagePayload::Ct1Ack(true)`; the wire form is `[1, varint(epoch), varint(index), 4]`.
- `Spqr/Specs/V1/Unchunked/SendCt/Serialize/Ct1SentEkReceived/*` and `Ct2Sent/*`: the
  transition `Ct1SentEkReceived → Ct2Sent` (`send_ct2`) is a pure function of local state; the
  only MAC on this path (`mac_ct`) is *produced*, not verified.

**Rust defect** (`src/v1/chunked/states.rs` L463–477 → `chunked/send_ct.rs` L232–240).

```rust
Self::EkReceivedCt1Sampled(state) => match msg.epoch.cmp(&state.epoch()) {
    Ordering::Equal => {
        if matches!(msg.payload, MessagePayload::Ct1Ack(true) | MessagePayload::EkCt1Ack(_)) {
            Self::Ct2Sampled(state.recv_ct1_ack(msg.epoch))   // drops `sending_ct1` forever
        } …
```

`Ct1Ack` is the peer's claim "I have fully decoded your `ct1`". B trusts it blindly, discards
`sending_ct1`, and moves to `Ct2Sampled`, which only emits `Ct2` chunks. A, still in
`HeaderSent`, only accepts `Ct1` chunks (L305–331) and ignores `Ct2`; B in `Ct2Sampled` ignores
A's `Ek` chunks. Neither side ever emits `epoch + 1`.

**Consequence.** After B has received the full `ek` but A has not finished `ct1`, the 5-byte
forgery `[1, 1, 0xE8, 0x07, 4]` makes B switch to `Ct2`; 200 further round-trips never leave
epoch 1 (the control run without the forgery advances). `recv` again returns `key: Some(_)`.

*Why distinct from D24.* D24 needs B in `Ct2Sampled` and produces a *permanent error*
(`EpochOutOfRange` forever). D38 needs B in `EkReceivedCt1Sampled` — a large window, the whole
time B is streaming its 960-byte `ct1` at ≤ 32 B/message — and produces a *silent stall*: every
call returns `Ok` with sensible-looking state, so no host-side error handling can notice. The
`Ct1Ack` flag is also implicit in `EkCt1Ack` (tag 3): a forged `EkCt1Ack` chunk with garbage
data has the same effect from `Ct1Sampled` (L419–420, `ack = true`) *and* poisons the `ek`
decoder (D19).

**Reproduced:** `d38_forged_ct1ack_stalls_epoch` in
[`docs/forged_control_message_counterexamples.rs.txt`](./forged_control_message_counterexamples.rs.txt).

**Fix:** authenticate acknowledgements — honour the `Ct1Ack` bit only when it arrives on an
`EkCt1Ack` chunk whose contribution to the `ek` decoder is later validated by
`ek_matches_header`; or carry a short `mac_hdr`-style tag over `(epoch, type)` under the current
`mac_key`. At minimum, do not drop `sending_ct1` until the peer proves possession of `ct1`.

### D19. Unauthenticated chunk poisoning is *persistent*: one forged low-index chunk stalls the epoch (MEDIUM; message, protocol-level DoS)

**Specs that expose it.**

- `Spqr/Specs/Encoding/Polynomial/PolyDecoder/AddChunk.lean` / `Decoder/AddChunk.lean`: the
  insertion guard is `poly_idx < necessary_points(i) ∨ pts[poly].len() < necessary_points(i)`.
  For any `chunk.index < necessary_points` the first disjunct is unconditionally true, so the
  point is always inserted, and the `IsSortedPushResult` `.eq` branch is **replacement**
  (`SrcTranslated/FunsExternal.lean:2146`; `sorted_vec 0.8.6 SortedSet::push`).
- `PolyDecoder/IntoPb.lean` / `FromPb.lean`: every stored point (including a replaced one)
  round-trips through the persisted protobuf unchanged.
- `Message.deserialize_spec`: `Chunk.index`/`Chunk.data` are attacker-controlled.

**Rust defect** (`src/encoding/polynomial.rs` L888–899; `src/v1/chunked/*.rs`).

1. An on-path attacker sends `{epoch, Hdr/Ek/Ct1/Ct2, index: k, data: garbage}` with `k` below
   `necessary_points` (e.g. `k = 0`) for the epoch currently being received.
2. `add_chunk` replaces the honest `x = k` point (or pre-seeds it). `decoded_message()` is still
   `None` → `recv` returns `Ok` and the poisoned decoder is **persisted**.
3. When the honest chunks complete the message, interpolation uses the garbage point →
   `verify_hdr`/`verify_ct` fails → `recv` returns `Err(MacVerifyFailed)`. The caller keeps the
   *old, poisoned* state. Every later honest chunk yields the same `Err`, because only another
   chunk with index exactly `k` can overwrite the point, and the honest sender re-emits index `k`
   only after wrapping through 65 536 chunks (D5).

**Reproduced:** `poisoned_low_index_point_persists_and_wins` in
[`docs/decoder_poison_persistence_counterexample.rs.txt`](./decoder_poison_persistence_counterexample.rs.txt).
An independent review of the argument — including where "permanent" is stronger than the
evidence — is in [`docs/spqr_chunk_replacement_poisoning_review.md`](./spqr_chunk_replacement_poisoning_review.md).
Formal model: `Spqr/Specs/Bugs/ProtocolDoS.lean`.

**Fix** (any one suffices): (a) `find_or_push` — first write wins, matching the source comment
(see D4); (b) on MAC failure, reset the decoder for that epoch so honest retransmits can recover;
(c) keep both candidate `y` values per `x` and try alternatives on MAC failure. Option (a) is the
smallest change; it would make the Lean model in `AddChunk.lean` (replacement) *wrong*, so the
model must be updated with it.

#### D4 / D18. The `add_chunk` source comment contradicts the verified last-write-wins semantics (LOW; documentation)

The Rust comment at `polynomial.rs` L896–898 claims *"This will discard new points whose X value
matches a previous old point"*. `sorted-vec 0.8.6` `SortedSet::push` on `Equal` does `pop()` then
`push(element)`, so the **new** `y` wins; the Lean model (`AddChunk.lean`;
`FunsExternal.lean:2146` `.eq => ok (i, some a, x :: rest)`) is right and the comment is wrong
(D4). Because `Pt::eq`/`Ord` ignore `y` (`Pt/Eq.lean`: *"returns true iff self.x.value =
other.x.value (y ignored)"*), a re-sent index with a different payload overwrites earlier points
(D18). Harmless for an honest peer; D19 is what it costs against a malicious one.

**Reproduced:** `decoder_duplicate_index_last_wins` in
[`docs/decoder_logic_probe.rs.txt`](./decoder_logic_probe.rs.txt): two index-0 chunks from
different messages → output follows the **second**.

**Fix:** correct the comment, or adopt `find_or_push` (which also fixes D19).

### D25. Empty (0-byte) unauthenticated message finalises a V0 downgrade while `min_version == V0` (LOW–MEDIUM; message, downgrade / DoS)

**Specs that expose it.**

- `Spqr/Specs/Lib/DecodeState/CallOnce.lean`: an empty state decodes to
  `{ inner := none, version_negotiation := none, chain := none }` — "V0, negotiation closed".
- `Spqr/Specs/Proto/PqRatchet/Version/TryFrom.lean` and `msg_version` (`lib.rs` L464–470):
  `msg.is_empty() ⇒ Some(V0)`. There is no authentication anywhere in the negotiation path.

**Rust defect** (`src/lib.rs` L377–412, L417–421).

When `msg_version(msg) = V0 < state_version = V1` and `version_negotiation = Some(vn)` with
`vn.min_version ≤ V0`, `recv` rebuilds the state with `init_inner(V0, …) = None` and
`version_negotiation: None`, then returns `Recv { state: vec![], key: None }`. The **empty byte
string** is thus a valid downgrade message that (a) requires no MAC or peer secret,
(b) permanently disables the PQ ratchet for that session, and (c) makes every later honest V1
message a silent no-op (`Ordering::Greater` on an `inner: None` state returns `Ok`).

**Consequence.** The downgrade is *by design* while negotiation is open, but the trigger being
the empty message means an intermediary that merely strips the `pq_ratchet` protobuf field from
the first message completes it. libsignal `a47ba487` initialises with `min_version: Version::V0`
(`ratchet.rs` L109, L200, with a comment that it will be raised once all clients speak PQR), so
the window is open in production; only the host's commit-after-MAC prevents persistence for a
network-only attacker.

**Reproduced:** `d25_unauthenticated_v0_downgrade_with_empty_message` in
[`docs/protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

**Fix:** default to `min_version ≥ V1`; or accept a downgrade only from a message carrying
authenticated V0 content (not the empty string); and surface it to the host via a distinct
`Error`/`SecretOutput` so it can decide whether to accept it.

### D39. `index == 0` on an epoch-1 message is an unauthenticated per-message "skip the PQ key" sentinel (LOW–MEDIUM; message, downgrade-adjacent)

D25 is a *session-wide* opt-out of PQ key mixing; D39 is the *per-message* counterpart.

**Specs that expose it.**

- `Message.deserialize_spec`: `index` is any `u32` from the varint; `0` is accepted.
- `Spqr/Specs/Chain/ChainEpochDirection/Key.lean` (`key_spec_*`) and `KeyHistory/Get.lean`:
  every path through `key(at)` for `at = 0 < ctr` ends in `Err(KeyTrimmed)` or
  `Err(KeyAlreadyRequested)` — index 0 is *never* a valid chain key. Yet `lib.rs` never asks.

**Rust defect** (`src/lib.rs` L432–436).

```rust
let msg_key = if msg_key_epoch == 0 && index == 0 {
    vec![]                                     // → Recv { key: None }
} else {
    chain.recv_key(msg_key_epoch, index)?
};
```

The sentinel exists for the legitimate `(chain: None, min_version == V0)` sender in `send`
(L294). But the *receiver* honours it unconditionally: even when its own `min_version == V1` and
it already holds a chain, any epoch-1 message with `index = 0` yields `key: None`.

**Consequence.** Under libsignal's outer MAC this is caught (the DR message keys differ when the
PQ salt is missing). Architecturally, any embedder that mixes `spqr::MessageKey` into a KDF as an
`Option` — as libsignal does, `Hkdf::new(optional_salt, …)` (`ratchet/keys.rs` L96) — inherits a
per-message downgrade oracle whose only defence is the host MAC. A spec of `recv` (currently
absent; `send` is `verification_status(lax)`) would have to state "`key = None` iff the sender
declared V0 or `index = 0`", making the gap explicit.

**Reproduced:** `d39_index_zero_yields_no_pq_key_despite_min_version_v1` in
[`docs/forged_control_message_counterexamples.rs.txt`](./forged_control_message_counterexamples.rs.txt)
flips the index byte of an honest first message and observes `key: None` with the receiver's
chain untouched (the untampered original is still accepted afterwards).

**Fix:** when `version_negotiation.min_version ≥ V1` (or a chain exists), treat `index == 0` on
epoch 1 as `Err(Error::MsgDecode)`; and assert in `send` that `index = 0` is never emitted once a
chain exists.

### D40. Pre-authentication computational amplification: up to `max_jump` HKDFs per unauthenticated message (LOW–MEDIUM; message, CPU DoS)

**Specs that expose it.**

- `Key.lean` (`key_spec_greater_jump` / `key_spec_greater`): for `ctr < at ≤ ctr + max_jump`,
  `key` performs `at − ctr` calls to `next_key_internal`, each an HKDF-SHA256
  (`NextKeyInternal.lean`), plus up to `min(max_ooo, at − ctr)` `KeyHistory::add`s.
- `Spqr/Specs/Chain/ChainParams/MaxJumpOrDefault.lean`: default `max_jump = 25 000`; a local
  parameter, never compared to anything the peer has authenticated.

**Rust defect** (`lib.rs` L435). `recv` calls `chain.recv_key(epoch, index)` with the
attacker-chosen `index` **before any MAC in the system has been checked**: SPQR's own
`verify_hdr`/`verify_ct` run only on chunk-completion edges, and libsignal calls
`pq_ratchet_recv` before `verify_mac`.

**Consequence.** An on-path attacker who rewrites the `index` varint of every message to
`ctr + 25 000` forces 25 000 HKDFs per message; the outer MAC then fails, the clone is dropped,
`ctr` is *not* advanced, and the same cost can be re-imposed on the next message indefinitely.
libsignal repeats this for every archived session (`previous_session_states()`, up to
`ARCHIVED_STATES_MAX_LENGTH = 40`) that reaches the call. With libsignal's self-session
configuration (`max_jump = u32::MAX`, D32) the bound is effectively unlimited: one message can
demand ~4·10⁹ HKDFs.

*Comparison with the Double Ratchet.* DR has the same `MAX_FORWARD_JUMPS = 25 000` skip budget,
but derives one HMAC per step and aborts at `MAX_MESSAGE_KEYS = 2 000` stored keys; SPQR derives
25 000 and stores 2 000 — roughly 2× the pre-MAC CPU cost, unbounded in self-sessions.
`docs/CorruptedBlobs.md` C4 mentions the figure in passing; it is a defect here because the
*ordering* (SPQR key derivation before host MAC) is a property of the SPQR ↔ libsignal contract.

**Fix:** (a) cap `max_jump` for self-sessions (D32); (b) a two-phase API — `recv` returns the
key plus a deferred commit so the host can verify its MAC before SPQR performs the ratchet walk —
or accept the message MAC as an input; (c) at minimum bound work per call by `max_ooo_keys`
rather than `max_jump` (derive lazily; store seed + skip count).

---

## Part II — Arithmetic and parameter bounds the specs could not discharge

**Common root cause.** `src/chain.rs` guards its `u32`/`usize` arithmetic with
`hax_lib::assume!` and `#[hax_lib::requires]`, which are erased at runtime and, in the Aeneas
translation, become *hypotheses* of every spec theorem (`h_ooo_no_overflow`, `h_ctr_bound`,
`h_maxooo_bound : maxOoo < 390451572`, …). Nothing in the crate — no constructor, no
deserialiser, no `initial_state` check — establishes them, so the theorems describe the code
only on the sub-domain where the hypotheses hold. `docs/invariantsSPQR.md` §3 discusses which of
these hypotheses can be turned into invariants. Two arithmetic findings whose trigger is a
*deserialised* value rather than a parameter (D26, D34) are filed under Part III.

### D2. `u32` overflow in `KeyHistory::get` trimmed-check (MEDIUM; message + local-config)

`Spqr/Specs/Chain/KeyHistory/Get.lean` and `Key32.lean` require
`h_ooo_no_overflow : at1 + maxOoo ≤ U32.max`.

```rust
if at + (params.max_ooo_keys_or_default()) < current_ctr {   // chain.rs L192
```

`at` is the attacker-supplied message `index`. When `ctr` approaches `u32::MAX`, `at + max_ooo`
overflows: debug builds panic, release builds wrap so the branch is taken and a *valid* key is
reported as `KeyTrimmed`. `key()` guards the analogous `self.ctr + max_ooo` (L265, L279) only via
`hax_lib::assume!` — hence `h_ctr_bound : i + 1 ≤ U32.max − 390451572` in `Key.lean`. With
default parameters the overflow needs `ctr` near `u32::MAX`; with libsignal's self-session
parameters it is reachable today (D32).

**Fix:** `checked_add` / `saturating_add` at L192, L265, L279.

### D28. `ChainParams` are never range-checked (`Error::InvalidParams` is dead) (MEDIUM; local-config)

**Specs that expose it.** `MaxOooKeysOrDefault.lean` returns `self.max_ooo_keys` for any positive
value; `TrimSize.lean` needs `max_ooo_keys < 390451572`; `Key.lean`/`Get.lean`/`Key32.lean` need
`h_maxooo_bound`, `h_at_bound : at ≤ U32.max − 390451572` and `h_ooo_no_overflow`. None is
established anywhere; the Rust carries them only as `assume!` (`chain.rs` L86, L262–264, L275–277).

**Rust defect** (`src/chain.rs`; `src/lib.rs` L128, L212–240). `ChainParams` is public;
`initial_state` copies it unchanged into the blob; `Chain::new`/`from_pb` accept any
`ChainParamsPB`. `Error::InvalidParams(&'static str)` exists but is **never constructed**.

**Consequence.** With `max_ooo_keys = u32::MAX` (a natural way to spell "never trim"):

| Build | `recv_key(0, 3)` on a fresh chain | then `recv_key(0, 1)` |
|---|---|---|
| debug | **panic** `attempt to add with overflow` at `chain.rs:279` | — |
| release | `Ok`, but the wrapped test `ctr + max_ooo >= at` is *false*, so skipped keys 1, 2 are **never stored** | `Err(KeyTrimmed(1))` — `get`'s check wraps to `0 < 3` |

The parameter's meaning inverts in release: "keep every out-of-order key" becomes "store none".
Local configuration only (params never come from the wire), but silent in release.

**Reproduced:** `d28_unvalidated_chain_params_overflow_in_key` in
[`docs/protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

**Fix:** validate in `initial_state` and `Chain::from_pb`, finally using the dead variant:

```rust
if params.max_ooo_keys >= 390_451_572 { return Err(Error::InvalidParams("max_ooo_keys too large")); }
if params.max_jump as u64 + params.max_ooo_keys as u64 > u32::MAX as u64 {
    return Err(Error::InvalidParams("max_jump + max_ooo_keys overflows u32"));
}
```

### D32. libsignal self-session `max_jump = u32::MAX` triggers the D2/D28 overflow in production (MEDIUM; message, via libsignal config — sibling of D28)

libsignal `ratchet.rs` L41–52 (`spqr_chain_params`) sets `max_jump = u32::MAX` when the local
and remote identity keys coincide (Note-to-Self), otherwise `MAX_FORWARD_JUMPS = 25 000`. With
this value `key()`'s `at − ctr > max_jump` check is vacuous, so `at` may be anything up to
`u32::MAX`, and `at > self.ctr + max_ooo` (L265) / `at + max_ooo` (L192) overflow exactly as in
D2 — panic in debug, wrapping in release. `key_spec_greater_jump`'s
`h_ctr_bound ≤ U32.max − 390451572` correctly predicts that the upper range is unsafe. The same
setting removes any bound on the pre-MAC HKDF walk (D40). Self-sessions are real and
long-lived.

**Fix:** cap at `u32::MAX.saturating_sub(MAX_MESSAGE_KEYS as u32 + 1)` in libsignal, and/or
reject the combination in SPQR via D28's validation.

### D8. `usize` overflow in `ChainParams::trim_size` on 32-bit (LOW; local-config, 32-bit)

`TrimSize.lean` needs `h_ooo : max_ooo_keys < 390451572` because the `assume!` at `chain.rs` L86
is erased; `Gc.lean`/`Key32.lean` tighten it to `< 108458770` so `trim_size * 36` fits in 32
bits. `max_ooo * 11` overflows for large `max_ooo_keys`.

**Fix:** subsumed by D28's validation.

### D10. The claimed bound `data.len() <= KEY_SIZE * trim_size()` on `KeyHistory` is false (MEDIUM; spec — LOW at runtime)

**Specs that expose it.** `chain.rs` asserts — as `hax_lib::requires` on
`KeyHistory::add`/`remove` (L138, L174), as `assume!` inside `ChainEpochDirection::key`
(L281–282), and as the struct comment on `KeyHistory::data` (L94) — that the history never
exceeds the GC threshold. The Lean specs do **not** adopt this claim: `Add.lean` assumes only
`len + 36 ≤ Usize.max`, `Remove.lean` only `idx + 36 ≤ len`, and `Key.lean` carries the weaker
`h_prev_ctr : prev.data.length ≤ 36 * ctr` and `h_kh_cap`. This finding *explains* why those
weaker hypotheses were the strongest dischargeable ones.

**Rust defect.** The bound is **false**: the history can grow to almost twice the threshold
before `gc` runs. The bounds the code actually maintains are

* **at rest** (between calls to `key`): `data.len() < KEY_SIZE * trim_size()` (strict); and
* **inside `key`, immediately before `gc`**:
  `data.len() ≤ KEY_SIZE * ((trim_size() − 1) + (max_ooo − 1))`.

With the defaults (`max_ooo_keys = 2000`, `trim_size() = 2201`) the claimed maximum is 2201
records (79 236 B); the true pre-GC maximum is 4199 records (151 164 B). The cause: `key(at)`
clears `prev` only when `at > ctr + max_ooo`. In the boundary case `at = ctr + max_ooo` nothing
is cleared and the advancing loop stores all `max_ooo − 1` intermediate keys **on top of** what
is already there; `gc` runs only *after* the loop (L289).

**Consequence.** With `max_ooo_keys = 10`, `max_jump = 100`, `trim_size() = 12`, threshold
432 B:

| call | `prev` cleared? | records added | before `gc` | after `gc` |
|---|---|---|---|---|
| `key(11)` | yes (`11 > 0 + 10`) | 1…10 | 10 (360 B) | 10 |
| `key(14)` | no | 12, 13 | 12 (432 B) | 10 |
| `key(24)` | **no** (`24 = 14 + 10`) | 15…23 | **19 (684 B)** | 10 |

During `key(24)` six `add` calls execute with `data.len() > 432 B`, violating the `requires` on
`add` from the crate's own caller. Over 2000 random walks the maximum observed pre-GC size was
exactly `(trim_size − 1) + (max_ooo − 1) = 20` records; the at-rest bound never failed.

*Impact.* Specification: any proof relying on the `requires` of `add`/`remove` or the `assume!`
in `key` as a real invariant is unsound. Behavioural: `prev` uses up to ~2× the promised memory
(bounded; not a DoS vector). The 32-bit guard `trim_size() < 119304647` is also stated against
the wrong quantity.

*Related off-by-one.* After `key(24)` the record tagged 13 survives `gc` (horizon `23 − 10 =
13`; `gc` drops only tags *strictly below*, L152), yet `prev.get(13, 24, ..)` returns
`Err(KeyTrimmed(13))` because `get` tests `at + max_ooo < current_ctr` with the *post-increment*
counter (L192). `gc` and `get` disagree at the window boundary by one: a key still stored is
reported as trimmed. `Get.lean` and `Key.lean` faithfully describe this asymmetry.

**Reproduced:** model in
[`docs/key_history_bound_counterexample.py`](./key_history_bound_counterexample.py); tests
against the real crate in
[`docs/key_history_bound_counterexample.rs.txt`](./key_history_bound_counterexample.rs.txt)
(full file [`docs/chain.rs`](./chain.rs)).

**Fix:** (1) correct the comment and the `requires`/`assume!` to the true bound, or drop the
length clause (only `len + 36 ≤ usize::MAX` / `idx + 36 ≤ len` are needed); (2) call `gc` inside
the loop, or size `Vec::with_capacity` for the larger bound; (3) make `get` and `gc` agree:
`at + max_ooo < current_ctr − 1` in `get`, or `>=` in `gc`.

### D3. `u64 → usize` truncation in `Chain::epoch_idx` on 32-bit targets (MEDIUM; 32-bit)

`EpochIdx.lean` needs `h_diff_fits : current_epoch − epoch ≤ Usize.max`, proved by
`cases System.Platform.numBits_eq`.

```rust
let back = (self.current_epoch - epoch) as usize;   // chain.rs L376
if back >= links { return Err(EpochOutOfRange) }
Ok(links - 1 - back)
```

On 32-bit a difference ≥ 2³² truncates, so the bounds check can pass and the function returns
an index for the **wrong epoch**. Impractical (needs 2³² epochs) but the spec correctly refuses
to prove correctness without the hypothesis.

**Fix:** `usize::try_from(..).map_err(..)`.

### D5. `PolyEncoder` index truncation `u32 → u16` (LOW; blob or long-running session)

`PolyEncoder/NextChunk.lean` needs `h_idx_fits : self.idx ≤ U16.max` to prove
`chunk.index = self.idx`; `PolyEncoder/FromPb.lean` yields `encoder.idx = pb.idx` for any `u32`.

```rust
let out = self.chunk_at(self.idx as u16);      // polynomial.rs L735
self.idx = self.idx.wrapping_add(1);
```

After 65 535 chunks (or from a persisted `pb.idx > 65535`) the emitted `chunk.index` silently
wraps. This wrap is also what makes D19's poisoning effectively permanent (the honest sender
only re-emits a given index after 65 536 chunks).

**Fix:** store `idx: u16`, or reject out-of-range values in `from_pb`.

---

## Part III — Deserialisation without validation

**Common root cause.** Every `from_pb` in the crate accepts a prost-valid protobuf as
semantically valid. Constructors (`Chain::new`, `Authenticator::new`, `PolyEncoder::encode_bytes`,
`PolyDecoder::new`, the state `new()`s) establish invariants — key lengths, `epoch ≥ 1`,
alignment, admissible point counts, admissible state variants — that consumers then rely on via
erased `hax_lib` annotations or plain `assert!`. The Lean specs make this visible: the
`FromPb.lean` theorems have *no* hypotheses and prove `Ok` for any input, while the consumers'
theorems *require* the invariant. `Spqr/Specs/Lib/DecodeState.lean:54` is a `sorry` (D15), so
nothing about which blobs are accepted is formally established.

**Threat model.** Requires the ability to influence the persisted `pq_ratchet_state` — a
corrupted database, a backup-restore bug, or a host that accepts state from an untrusted source.
libsignal persists the blob opaquely (`state/session.rs` L147) and maps `Error::StateDecode` to
`InvalidState` (`session_cipher.rs` L636) but validates nothing itself; the same non-validation
applies to archived sessions (`previous_session_states()`). Panics here are therefore process
crashes on session load, not remote attacks. A formal model of the D1/D21/D22 family is in
`Spqr/Specs/Bugs/CorruptedBlobs.lean`; narrative in [`docs/CorruptedBlobs.md`](./CorruptedBlobs.md).

**What is already validated.** The unchunked V1 `from_pb`s (`send_ek/serialize.rs`,
`send_ct/serialize.rs`) **do** check the cryptographic field lengths (`dk = 2400`, `ek = 1152`,
`ct1 = 960`, `es = 2080`, `hdr = 64`). They do not check the *contents* of those fields (D30),
the `epoch` field (D26, D34), or which inner state variant is present (D27); and `chain.rs`,
`authenticator/serialize.rs` and `encoding/polynomial.rs` check nothing (D1, D21, D22, D13, D14,
D16, D17).

### D1. `ChainEpochDirection::from_pb` never validates → panics reachable from a corrupted state blob (HIGH; blob)

**Specs that expose it.**

- `Spqr/Specs/Chain/ChainEpochDirection/FromPb.lean`: postcondition is
  `ced.ctr = pb.ctr ∧ ced.next = pb.next ∧ ced.prev = { data := pb.prev }`; docstring: *"Always
  succeeds (no validation)"*.
- `NextKeyInternal.lean` requires `h_next_len : next.length = 32`.
- `KeyHistory/Get.lean` requires `h_data_aligned : self.data.length % 36 = 0` (*"models the Rust
  `assert_eq!` panic"*).
- `KeyHistory/Gc.lean` requires `h_key_ge : trim_threshold ≤ data.length → max_ooo ≤ current_key`
  (models `assert!(current_key >= max_ooo)`); `Key.lean` needs `h_prev_ctr : prev.data.length ≤
  36 * ctr` to discharge it.

**Rust defect** (`src/chain.rs` L306–312).

```rust
fn from_pb(pb) -> Result<Self, Error> {
    Ok(Self { ctr: pb.ctr, next: pb.next, prev: KeyHistory { data: pb.prev } })
}
```

**Consequence.**

| Field | Consumer | Failure |
|---|---|---|
| `next.len() ≠ 32` (non-empty) | `next_key_internal`: `next.copy_from_slice(&genr8r[..32])` (L243) | panic (length mismatch) |
| `prev.len() % 36 ≠ 0` | `KeyHistory::get`: `assert_eq!(self.data.len() % KEY_SIZE, 0)` (L191) | panic |
| `prev` large, `ctr` small | `KeyHistory::gc`: `assert!(current_key >= max_ooo)` (L149) | panic |

**Reproduced:** `q3_probe_bad_next_reaches_next_key_internal_via_recv_key`,
`q3_probe_misaligned_prev_reaches_get_via_recv_key`,
`q3_probe_large_prev_small_ctr_reaches_gc_via_recv_key` in
[`docs/corrupted_blob_counterexample.rs.txt`](./corrupted_blob_counterexample.rs.txt) (one per
table row). Formal model: `Spqr/Specs/Bugs/CorruptedBlobs.lean`.

**Fix:** validate in `from_pb` (return `Error::StateDecode`); the `h_*` hypotheses then become
provable invariants.

### D21. `Chain::from_pb` does not validate `next_root` length, `links` non-emptiness, or epoch ordering (MEDIUM; blob)

The same gap one level up, in `Chain::from_pb` (`chain.rs` L434–452). Three invariants
established by `Chain::new` are not re-checked:

| Invariant | Consumers that assume it | Failure mode |
|---|---|---|
| `next_root.len() == 32` | `add_epoch` → `hkdf_to_slice(&self.next_root, …)` (L358) | No panic (HKDF accepts any salt length) but the KDF output differs from a correctly built chain — **silent key divergence between peers** after the next `add_epoch` |
| `links.len() ≥ 1` | `epoch_idx` computes `links.len() − 1 − back` (L381); `send_key` indexes `links[i]` | underflow panic in debug; OOB panic in release |
| `send_epoch ≤ current_epoch` | `send_key` rejects `epoch < send_epoch`; `epoch_idx` rejects `epoch > current_epoch` | if violated, *every* `send_key` fails — chain permanently stuck |

**Reproduced:** `q4_probe_graceful_err_epoch_inversion` (third row) in
[`docs/corrupted_blob_counterexample.rs.txt`](./corrupted_blob_counterexample.rs.txt). Formal
model: `Spqr/Specs/Bugs/CorruptedBlobs.lean`.

**Fix:** in `Chain::from_pb`, `if pb.next_root.len() != 32 || links.is_empty() ||
pb.send_epoch > pb.current_epoch { return Err(Error::StateDecode) }`.

### D22 / D31 / D35 / D36. `Authenticator::from_pb` does not validate key lengths, and the surrounding error plumbing is unfinished (LOW; blob)

**D22 — the gap** (`src/authenticator/serialize.rs` L16–21). `Authenticator::new` always produces
32-byte `root_key`/`mac_key` (`hkdf_to_vec(…, 64)` split); `from_pb` clones any length. HMAC and
HKDF are length-agnostic, so there is no panic, but a blob with `mac_key: []` makes every
authenticator produce the same tags — ciphertext MACs become forgeable — and a short `root_key`
weakens the authenticator chain.

**D31 — a consequence.** `update` builds `ikm = [root_key, k].concat()` (L45). With
unvalidated lengths, shortening `root_key` by N and lengthening `k` by N gives identical IKM
and hence identical HKDF output. D22's length check subsumes this.

**D35 — evidence the check was planned.** `authenticator::Error` defines
`AuthenticatorRootKeyPresent/Missing` and `AuthenticatorMacKeyPresent/Missing` (`authenticator.rs`
L16–23); none is ever constructed.

**D36 — what would go wrong when it is added.** `impl From<authenticator::Error> for Error`
(`lib.rs` L145–148) blanket-maps every variant to `MacVerifyFailed`, which libsignal treats as a
*bad message* (`InvalidMessage`) rather than *bad state* (`InvalidState`). Key-validation
failures would trigger message-retry instead of session-reset.

**Fix:** `from_pb` returns `Result`, rejects `len != 32` using the D35 variants; the `From` impl
maps those variants to `StateDecode`; update the two call sites in
`src/v1/unchunked/{send_ek,send_ct}/serialize.rs`.

### D26. `epoch == 0` accepted by every `*::from_pb`, then `msg.epoch − 1` underflows in `lib::send` (LOW; blob)

**Specs that expose it.** All eleven `Spqr/Specs/V1/Unchunked/*/Serialize/*/FromPb.lean`
theorems prove `Ok` with `epoch := pb.epoch` **for any `u64`**, while `Message.deserialize_spec`
proves `0 < msg.epoch` on the *wire* path — the protocol relies on `epoch ≥ 1` (`lib.rs` L300,
L427 compute `msg.epoch − 1`).

**Rust defect.** A persisted blob whose inner `uc.epoch` is `0` (the prost default) is accepted;
`States::send` emits `Message { epoch: 0 }` and `lib::send` evaluates `0u64 − 1`:

| Build | Behaviour |
|---|---|
| debug | **panic** `attempt to subtract with overflow` at `lib.rs:302` |
| release | wraps to `u64::MAX` → `Err(EpochOutOfRange(…))` on every `send`; session stuck |

`recv` is shielded by `deserialize`'s `epoch == 0` check.

**Reproduced:** `d26_epoch_zero_state_underflows_in_send` in
[`docs/protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

**Fix:** reject `pb.epoch == 0` in the unchunked `from_pb`s and use `checked_sub` in `lib.rs`.

### D34. Chunked `Ct2Sampled::recv` does not guard `epoch < u64::MAX` before `recv_next_epoch` (LOW–MEDIUM; blob)

The mirror image of D26 at the top of the range. `unchunked/send_ct.rs` L200 carries
`#[hax_lib::requires(self.epoch < u64::MAX)]` (erased), and `recv_ct2` L161 has the same as
`assume!`. In `states.rs` L515, `state.epoch() + 1` wraps to `0` when `epoch == u64::MAX` (from
a corrupted blob); `recv_next_epoch`'s `assert_eq!(epoch + 1, next_epoch)` panics in debug,
wraps in release.

**Fix:** validate `epoch < u64::MAX` in `Ct2Sent::from_pb`, or guard at L515.

### D13. `PolyEncoder::from_pb` does not validate per-polynomial point counts → `debug_assert` panic / silently wrong chunks (MEDIUM; blob)

**Specs that expose it.** `PolyEncoder/{PointAt,ChunkAt,NextChunk}.lean` all require
`h_admissible : ∀ j < 16, len ∈ {0, 1, 3, 5, 30, 34, 36}`; `Poly/FromCompletePoints.lean`
requires the same and has *no* spec for the `_ =>` fallback arm; `PolyEncoder/FromPb.lean` has no
such hypothesis and proves `Ok` for any 16 even-length slots.

**Rust defect** (`polynomial.rs`). `from_pb` (L573–603) checks only `pts.len() % 2 == 0`. The
admissible-length fact reaches `point_at` solely via an erased `assume!` (L646–654). On the first
cache miss `from_complete_points`'s fallback is `debug_assert!(false, "missing precomputed poly
of size {}")` (L310).

**Consequence.**

| Build | Persisted encoder whose slots hold 2 points each |
|---|---|
| debug | **panic** on the 3rd `next_chunk()` |
| release | fallback Lagrange path emits chunks (all-zero for the probe) for a state the protocol never defines |

**Reproduced:** `encoder_from_pb_inadmissible_len` in
[`docs/polynomial_from_pb_counterexample.rs.txt`](./polynomial_from_pb_counterexample.rs.txt).

**Fix:** reject slots with `pts.len()/2 ∉ {0,1,3,5,30,34,36}` (and oversize `polys[i]`) with
`SerializationInvalid`, making `h_admissible` an invariant.

### D14. `PolyDecoder::from_pb` does not bound stored point-set sizes (LOW–MEDIUM; blob)

**Specs that expose it.** `Poly/LagrangeInterpolate.lean` and friends are stated for arbitrary
`pts.length`, but the Rust carries
`#[hax_lib::requires(pts.len() <= MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1)]` (L105, L143, L230)
and `into_pb`/`decoded_message` rely on erased `assume!`s. `PolyDecoder/FromPb.lean` proves `Ok`
for any `pts_needed : u32` and any number of points per slot.

**Consequence.** A blob with `pts_needed = 1600` and 100 points per slot makes
`decoded_message()` return `Some(3200 bytes)` — ~3× the stated maximum, with O(N²)
interpolation cost controlled by the blob. No memory-safety issue.

**Reproduced:** `decoder_from_pb_interpolate_oversized` in
[`docs/decoder_logic_probe.rs.txt`](./decoder_logic_probe.rs.txt).

**Fix:** require `pts_needed ≤ 576` and each slot
`len/4 ≤ 2·MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1 = 71`.

#### D37. `PolyDecoder::into_pb` truncates `pts_needed: usize` to `u32` (LOW; API)

`polynomial.rs` L795: `pts_needed: self.pts_needed as u32`. Unreachable in V1 (`≤ 1040`) but the
`Decoder` trait is `pub` and accepts any `len_bytes: usize`.

**Fix:** `u32::try_from(..)` or cap in the constructor — naturally paired with D14's bound.

### D16. `Poly::serialize`/`deserialize` are not inverses on the zero polynomial → `PolyEncoder` round-trip fails (MEDIUM; API)

**Specs that expose it.** `Poly/Zero.lean`: `coefficients.length = 0`. `Poly/Serialize.lean`:
`result.length = 2 * degree` — the zero polynomial serialises to `[]`. `Poly/Deserialize.lean`
requires `h_nonempty : serialized.length ≠ 0`. `PolyEncoder/FromPb.lean` (`FromPbWellFormed`)
requires every `polys[j]` non-empty. Together: **`from_pb ∘ into_pb` is not the identity whenever
any stored polynomial is zero.**

**Rust defect** (`polynomial.rs` L329, L343). A slot is empty whenever the encoded message has
fewer than 32 bytes (round-robin of 2-byte words over 16 slots). The V1 protocol only encodes
96/1152/960/160-byte messages so it never hits this, but the encoder is a `pub` generic component
and its own test `encode_and_decode_small` (L972) uses such a message.

**Reproduced:** `encoder_polys_roundtrip_with_empty_poly` in
[`docs/poly_roundtrip_counterexample.rs.txt`](./poly_roundtrip_counterexample.rs.txt):
`from_pb(into_pb(e)) = Err(SerializationInvalid)`.

**Fix:** accept `[]` as the zero polynomial in `deserialize` (matches `zero_spec`), or emit
`[0, 0]` in `serialize`.

### D17. `PolyDecoder::is_complete` is write-never → dead field, redundant O(N²) work, blob-controlled stall (LOW; blob)

**Specs that expose it.** `Decoder/New.lean`: `is_complete = false`; `AddChunk.lean`,
`IntoPb.lean`, `FromPb.lean`: preserved by every operation. No spec ever establishes `true`
because no Rust does.

**Rust defect.** Five sites (`polynomial.rs` L760, L789, L797, L851, L912); the only *read* is
`if self.is_complete { return None; }` at the top of `decoded_message`.

**Consequence.** (1) A completed decoder re-runs full Lagrange interpolation on every late chunk;
(2) the persisted protobuf field carries no information yet `from_pb` honours it — a blob with
`is_complete = true` makes `decoded_message()` return `None` forever, silently stalling the
epoch.

**Reproduced:** `decoder_is_complete_never_set` in
[`docs/decoder_logic_probe.rs.txt`](./decoder_logic_probe.rs.txt).

**Fix:** set it to `true` (and drop `pts`) on success, or delete the field; if kept, reject
`true` with non-empty `pts`.

### D27. `lib::send` panics on `assert!(key.is_none())` when the state emits an `EpochSecret` but no chain is available (LOW–MEDIUM; blob)

`send` is `verification_status(lax)` (`lib.rs` L264), so `hax_lib::assume!(key.is_none())` at
L292 is unverified; the `assert!` at L293 remains in release. The `None` arm is reached when
`chain == None` and `vn.min_version == V0`. Honest flow only pairs `chain: None` with the two
initial states, but `from_pb` accepts **any** inner state (e.g. `HeaderReceived`, whose `send`
always yields `Some(EpochSecret)`).

**Reproduced:** `d27_send_asserts_when_epoch_secret_but_no_chain` in
[`docs/protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

**Fix:** return `Err(Error::ChainNotAvailable)`, or always materialise the chain from
`version_negotiation` when a key is produced (as `recv`'s `chain_from` does).

### D30. `encaps2` endianness heuristic can silently produce a wrong shared secret from a corrupted `es` (MEDIUM; blob)

`incremental_mlkem768.rs` L92–138 is `#[hax_lib::opaque]` (Lean sees only the length
postcondition). The libcrux #1275 workaround inspects `error2` in `es[1536..2048]`: (1) all-zero
`error2` → no decision (p ≈ 2⁻⁵⁹⁷, negligible); (2) a corrupted `es` from `from_pb` can present a
"good LE" `error2` while `r_as_ntt` is big-endian → wrong `ct2` → wrong shared secret →
`MacVerifyFailed` on the peer, no retry; (3) the `_` wildcard proceeds silently, with the
`log::warn!` behind `#[cfg(not(hax))]`. Honest execution is safe; the exposure is `es` persisted
across the `Ct1Sent → send_ct2` gap.

**Fix:** store an explicit endianness marker with the serialised `EncapsulationState`.

---

## Part IV — Cryptographic hygiene and constant-time primitives

**Scope.** This part audits the primitives the specs either treat as opaque (`libcrux` ML-KEM
internals, `black_box`) or specify only functionally (`compare`, `inz`, HKDF outputs). Functional
theorems cannot express constant-time behaviour or secret erasure, so these findings come from
code reading, exhaustive testing and assembly inspection rather than from a spec hypothesis.
Three items result: one latent length-handling bug (D11), one clean audit (D12), and one
cross-cutting hygiene gap (D29/D33).

### D11. `compare` silently truncates when slice lengths differ (MEDIUM; latent)

`src/util.rs` L25–33 iterates `0..lhs.len()` only; the equal-length precondition is a
`#[cfg_attr(hax, hax_lib::requires(...))]`, erased at runtime.

| Condition | Behaviour |
|---|---|
| `rhs.len() > lhs.len()` | trailing bytes of `rhs` never examined → returns `0` (equal) — **silent truncation** |
| `rhs.len() < lhs.len()` | `rhs[i]` panics → DoS plus a timing signal |

**Current callers are safe by construction**: `verify_ct`/`verify_hdr` pass a 32-byte
`expected_mac` (the chunked path's `decoded_message()` yields exactly `pts_needed*2` bytes, so
`split_off` always leaves 32) and the 32-byte output of `mac_*`. The original libcrux code works on
fixed-size arrays; the port to slices lost the type-level guarantee and replaced it with an
annotation that has no runtime effect.

**Fix:** `if lhs.len() != rhs.len() { return 1; }` (or `assert_eq!`).

### D12. Audit of the constant-time comparison / FO-transform path (NO DEFECT FOUND)

Motivated by ML-KEM implementations that shipped incomplete FO re-encryption checks or no-op
constant-time selects. The FO transform is *not* in `src/`: `decaps` delegates to
`libcrux_ml_kem::ind_cca::incremental::decapsulate_compressed_key` →
`compare_ciphertexts_select_shared_secret_in_constant_time` (`libcrux-ml-kem-0.0.7/src/constant_time_ops.rs`).

| Property (libcrux 0.0.7, pinned) | Result |
|---|---|
| `compare` iterates the **full** `CIPHERTEXT_SIZE` array | ✔ |
| `inz(v) = ((!v as u16).wrapping_add(1) >> 8) & 1` | ✔ exhaustively `= (v≠0)` over all 256 bytes |
| `select_ct`: `mask = is_non_zero(sel).wrapping_sub(1)`; `out = (lhs & mask) \| (rhs & !mask)` | ✔ `sel=0 → lhs`, all `sel∈1..=255 → rhs` |
| Both candidate secrets computed before the select | ✔ no data-dependent early return |
| `#[inline(never)]` + `black_box` barriers | ✔ |

SPQR's own port: `inz` proved in `Spqr/Specs/Util/Inz.lean` and exhaustively tested; `compare`
proved in `Compare.lean` (`0 ↔ ∀ j, lhs[j] = rhs[j]`); `verify_ct_spec`/`verify_hdr_spec` give
`Ok () ↔ expected_mac = mac_*(…)`. Release AArch64 assembly: NEON `eor/orr` accumulation, no
early exit; the only branch is the final public accept/reject. Protocol level (`recv_ct2`):
`decaps` (implicit rejection, never fails) → HKDF → `auth.update` → `verify_ct(…)?`; on MAC
failure `?` discards the updated state and no secret-derived data escapes.

**Hardening notes.** (1) D11 stands. (2) SPQR's `compare` lacks `#[inline(never)]` — branchless
today thanks to LLVM, not a barrier. (3) The Lean model of `black_box` is the identity, so the
theorems establish functional correctness only. (4) On any `libcrux-ml-kem` bump re-run the two
exhaustive checks (`inz` over all bytes; `select_ct` over all selectors).

### D29 / D33. No zeroisation of cryptographic secrets (MEDIUM; hygiene, needs local memory access)

**Specs that expose it.** `NextKeyInternal.lean` and `HkdfToVec.lean` constrain derived values
and lengths but say nothing about clearing old ones.

**Rust defect.** No type implements `Zeroize`/`ZeroizeOnDrop` and the crate is not in
`Cargo.toml`. Heap-resident material never cleared (D29): `genr8r[0..96]` (chain seeds,
`chain.rs` L330/L356), `kdf_out[0..64]` (auth keys, `authenticator.rs` L51), ML-KEM shared
secret `ss` (`send_ct.rs` L129), DK 2400 B (`send_ek.rs` L51, persisted a whole epoch), ES
2080 B (`send_ct.rs` L66); `clear_next()` is `Vec::clear()` (len = 0, no overwrite). Stack
(D33): the 64-byte keygen seed and 32-byte encapsulation entropy in `incremental_mlkem768.rs`
L35–36, L52–53; `libcrux-secrets` is available but unused. libsignal's `pq_ratchet_state` field
likewise lacks zeroize. Exploitation requires local memory access (core dump, swap, cold boot).

*Related design note.* `next_root` (`chain.rs` L119) and the authenticator `root_key` are
persisted in the clear in every blob and are identical on both peers; together with the *next*
epoch's `EpochSecret` they yield all of that epoch's keys. This is the design, but it means
state-blob confidentiality is a prerequisite for PCS of the upcoming epoch, not only the current
one.

**Fix:** add `zeroize`; derive `ZeroizeOnDrop` for key-holding types; replace `Vec::clear()`
with `.zeroize()`; `randomness.zeroize()` after use.

---

## Part V — Soundness of the Lean trusted base and limits of the verified surface

**Scope.** Parts I–IV report defects the theorems *revealed*. This part reports defects in, and
limits of, the apparatus itself: the hand-written external models that every theorem trusts
(D20), the remaining `sorry`s and axioms (D15), wire-contract facts the theorems record without
the Rust asserting them (D6/D7), design observations the biconditional specs made visible (D9),
and test-only code outside the protocol (D23). Nothing here changes a proved theorem's
statement; D20 would change what a *future* theorem could soundly claim.

### D20. `VecDeque::into_iter` model yields the wrong elements whenever `head ≠ 0` (HIGH; spec — soundness of any future `Chain::into_pb` theorem)

**Location**: `SrcTranslated/FunsExternal.lean` L3733–3759
(`alloc.collections.vec_deque.into_iter.IntoIter.…Iterator.next`).

The project deliberately uses a **growing-list model** for `VecDeque` (`push_back` appends;
`pop_front` increments `head` and decrements `length`; `index` reads `buf[head + idx]`;
L1241–1381). The `into_iter.next` model instead

```lean
if deq.length == 0 then ok (none, intoIter)
else
  let newhead ← (Usize.wrapping_add deq.head 1) % len   -- ring-buffer arithmetic
  ok (deq.buf.get? deq.head, { inner := { buf, head := newhead, length := len } })
```

— never decrements `length` (never terminates) and wraps `head` modulo `length` (the *ring-buffer*
invariant of real `std`, inconsistent with the project's own `pop_front`/`push_back`/`index`).

**Consequence.** `Chain.into_pb` uses this instance, but every `.map(...).collect()` is routed
through the `sorryAx` bridge (D15) and no spec theorem yet states a postcondition for
`Chain::into_pb`/`from_pb`, so nothing proved today is falsified. Upstream PR #570
(`Spqr/Specs/Chain/Chain/ChainEpoch/CallMut.lean`) verifies the `into_pb` *closure* — a
prerequisite, but composing it with this iterator still gives wrong results when `head ≠ 0`,
which `SendKey.lean`/`RecvKey.lean` both cause.

**Reproduced:**
[`docs/vecdeque_into_iter_model_counterexample.lean.txt`](./vecdeque_into_iter_model_counterexample.lean.txt):
after one `pop_front` on `[10,20,30]` (Rust iterates `20, 30, None`) four calls yield
`[some 20, some 10, some 20, some 10]` with `length` still `2`.

**Fix:** growing-list semantics mirroring `pop_front_spec_nonempty`:

```lean
if deq.length.val = 0 then ok (none, intoIter)
else match deq.buf.val[deq.head.val]? with
  | none => fail .panic
  | some elem => do
    let head' ← deq.head + 1#usize
    let len'  ← deq.length - 1#usize
    ok (some elem, ⟨{ deq with head := head', length := len' }⟩)
```

### D15. Remaining `sorry`s and axioms bounding what the specs can claim (INFO)

- `Spqr/Specs/Lib/DecodeState.lean:54` — round-trip left as `sorry` because the prost-generated
  `Message` impl is replaced by `sorry` in translation (issue #102). Nothing about *which* blobs
  `decode_state` accepts is formally established; all of Part III sits behind this boundary.
- `Spqr/Specs/Aeneas/MapCollectBridge.lean` — single assumed bridge for `.map().collect()`
  (aeneas#1043); `ConstPolysToPolys.lean` and `point_at_spec` depend on it.
- `SrcTranslated/Funs.lean` still has four `sorry`-using declarations, all in generated protobuf code.
- Axiom audit (`#print axioms`): `send_key_spec` and `key_spec_*` depend only on
  `hkdf_to_slice_spec` and the `get_unchecked{,_mut}` externals; `mul2_u16_spec` is axiom-free
  because `aeneas-config.yml` excludes the accelerated (`PCLMULQDQ`/`PMULL`) path — so the SIMD
  GF(2¹⁶) multiplication is *not* covered by any proof, only the portable `unaccelerated::mul`.
- Rust marked `#[hax_lib::opaque]` or `verification_status(lax)` (`encaps2`'s endianness
  heuristic, `KeyHistory::gc`/`get` internals, `Chain::into_pb`/`from_pb`, `lib::send`) has no
  theorem; findings on it (D10 internals, D27, D30) rest on code reading plus executable evidence.

### D6 / D7. Wire-decoding contract inconsistencies (LOW; spec)

- **D6** — `DecodeChunk.lean`: on the two error paths of `decode_chunk` the cursor has already
  advanced by `n + 32`, so the postcondition proves only `at ≤ *future(at)`, unlike
  `decode_varint`, which restores it. `Message::deserialize` discards the cursor on error, so no
  exploit. The `assume!(*at < usize::MAX − 32)` is erased, so the spec needs
  `from.len() + 32 ≤ usize::MAX`.
- **D7** — `DecodeVarint.lean` (`varintBlockAt`) admits non-canonical encodings (`1` as
  `0x81 0x00`) and silently truncates the 10th byte's high bits. Serialisation is not injective;
  benign here, relevant to any future round-trip theorem.

### D9. Design smells surfaced by biconditional specs (INFO)

- `MaxJumpOrDefault.lean` / `MaxOooKeysOrDefault.lean` / `ChainParams/IntoPb.lean`: "zero means
  unset" makes `max_jump = 0` / `max_ooo_keys = 0` unrepresentable and `into_pb ∘ from_pb` not
  the identity.
- `Pt/Eq.lean` `pt_eq_iff`: `PartialEq` is strictly coarser than structural equality (the root of
  D4/D18/D19).

### D23. Test-only `RoundRobinEncoder`/`RoundRobinDecoder` defects (LOW; test code)

`src/encoding/round_robin.rs` is `#[cfg(test)]`. `chunk_at` does `idx % num_chunks()` — division
by zero on empty input — and slices `data[lb..lb+32]` past the end for non-multiple-of-32 input;
`RoundRobinDecoder::add_chunk` has the same zero-length modulo; `is_complete` is never set
(mirrors D17). No protocol path is affected.

---

## Priorities

Ranked by **reachability** first (message-only before blob-only before local-config), then by
**fix leverage** (how many findings one change closes). This is why D1 — the only HIGH runtime
finding — ranks below the MEDIUM Part I items: it needs a corrupted blob, whereas D24/D38 need
one forged message.

| Rank | Item | Why |
|---|---|---|
| 1 | D24, D38 | Only findings where a single unauthenticated message stalls *both* parties; D38 is silent. Fix is one design change (authenticate control edges). |
| 2 | D19 (+D4/D18) | Persistent one-sided epoch stall from one forged chunk; one-line fix (`find_or_push`) plus a model update. |
| 3 | D1, D21, D22, D13, D14, D26, D27, D34 | One validation pass over every `from_pb` closes the whole Part III family and lets ~a dozen spec hypotheses become invariants. |
| 4 | D28 (+D2, D8, D32) | One range check in `initial_state` closes the arithmetic family and the production self-session overflow. |
| 5 | D20 | Latent unsoundness in the trusted base; must be fixed before any `Chain::into_pb` spec. |
| 6 | D25, D39, D40 | Downgrade/amplification surfaces that the host MAC currently absorbs; API-level fixes. |
| 7 | D10, D16, D17, D11, D29 | Correctness of annotations, round-trip, dead field, hardening. |

## Evidence and coverage

**How each part was found.**

| Part | Technique |
|---|---|
| I | Enumerate every `States::recv` edge and every `lib::recv` branch; classify each by the evidence that gates it — a MAC-verified chunk completion, an ML-KEM consistency check (`ek_matches_header`), or nothing — and compare against the order in which libsignal (`session_cipher.rs`) authenticates relative to its SPQR call. Edges gated by nothing: D24, D38, D39; work performed before any MAC: D40; content mutable before its MAC: D19. |
| II | Collect every `hax_lib::assume!`/`requires` in `src/` (30 sites) and the hypotheses they become in the Lean theorems (`h_ooo_no_overflow`, `h_ctr_bound`, `h_maxooo_bound`, `h_diff_fits`, …); check whether any constructor or deserialiser establishes them. None does. D10 came from an attempt to *prove* one such annotation as an invariant, which produced the counterexample instead. |
| III | For every `from_pb`, compare the invariants its `FromPb.lean` theorem establishes (none) against the hypotheses the consumers' theorems require; probe each gap with a prost-valid blob. |
| IV | Targeted review of `util.rs` and the libcrux FO-transform path against known ML-KEM implementation-bug classes; assembly inspection of the release build; grep for zeroisation. |
| V | `#print axioms` on representative theorems; consistency check of the hand-written `VecDeque` models in `FunsExternal.lean` against each other. |

**Executable evidence.** All files are under `docs/`. Rust harnesses use only the crate's public
API or the `test-utils` feature and were run on a scratch copy of the crate (on case-insensitive
filesystems `tests/` aliases the Lean `Tests/` directory). This table is the authoritative
identifier → evidence mapping; individual findings cite only the test name.

| File | Items | Profile |
|---|---|---|
| `protocol_driver_counterexamples.rs.txt` | D24, D25, D26, D27, D28 | debug + release |
| `forged_control_message_counterexamples.rs.txt` | D38, D39 | debug + release |
| `decoder_poison_persistence_counterexample.rs.txt` | D19 | release |
| `decoder_logic_probe.rs.txt` | D17, D18, D14 | release |
| `corrupted_blob_counterexample.rs.txt` | D1, D21 | debug + release |
| `polynomial_from_pb_counterexample.rs.txt` | D13 | debug + release |
| `poly_roundtrip_counterexample.rs.txt` | D16 | release |
| `key_history_bound_counterexample.{py,rs.txt}`, `chain.rs` | D10 | model + real crate |
| `vecdeque_into_iter_model_counterexample.lean.txt` | D20 | `lake env lean` |
| `Spqr/Specs/Bugs/ProtocolDoS.lean`, `Bugs/CorruptedBlobs.lean` | D19/D24; D1/D21/D22 | Lean |

Findings without a **Reproduced:** line (D2, D3, D5, D6/D7, D8, D9, D11, D12, D15, D22 family,
D23, D29/D33, D30, D32, D34, D37, D40) rest on the cited theorem hypotheses and code reading;
D12 additionally on exhaustive tests of `inz`/`select_ct` and assembly inspection.

## Limitations

- Every finding is grounded either in a hypothesis a proved spec theorem requires or in a
  postcondition it establishes, except where the Rust is `#[hax_lib::opaque]` or
  `verification_status(lax)` (listed in D15), in which case it rests on code reading plus the
  executable evidence above. The SIMD GF(2¹⁶) multiplication is excluded from translation and is
  unverified.
- The libsignal host mitigation described in *How to read this report* is the single measure
  that absorbs the whole of Part I for a network-only attacker. Any embedder that commits SPQR
  state before verifying its own authentication is fully exposed to D19/D24/D25/D38/D39; an
  authenticated-but-malicious peer is not stopped by it in any embedder.
- The libsignal `min_version: Version::V0` initialisation (D25) is the one Part I window that is
  open in production without a malicious peer; it closes when libsignal raises the floor to `V1`.
- Line numbers may drift; see *How to read this report*.

