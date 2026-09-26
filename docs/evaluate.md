# Evaluation of `docs/CorruptedBlobs.md` Against Requested Questions

**Scope**: This evaluation checks whether the report `docs/CorruptedBlobs.md` answers the
question(s) requested by the reviewer. Seven questions were requested:

| # | Question | Status in report |
|---|---|---|
| Q1 | Where is persisted SPQR state loaded in production? | **Partially answered** |
| Q2 | Does that state pass through the specific `from_pb()` implementation identified by the finding? | **Answered** (verified) |
| Q3 | Is there any semantic validation that establishes the invariants required by downstream operations? | **Answered** (verified; answer is *no*) |
| Q4 | Can we construct a concrete protobuf that is protobuf-valid but violates one of those invariants? | **Answered** (verified; multiple constructions with machine-checked proofs) |
| Q5 | Does the production `from_pb()` accept that protobuf and return `Ok`? | **Answered** (verified; answer is *yes* — unconditionally) |
| Q6 | Can the resulting invalid state actually reach `send()`/`recv()` in production? | **Answered** (verified; answer is *yes* — immediately and unconditionally) |
| Q7 | Does executing `send()`/`recv()` with that state actually produce the claimed panic rather than a recoverable error? | **Answered** (verified; answer is *yes* — `assert!` panics confirmed by source inspection and Lean proofs) |

**Tally**: 6 of 7 questions fully answered; 1 of 7 partially answered (Q1); 0 unanswered.

---

## Q1. Where is persisted SPQR state loaded in production?

### What the report says

The report answers the *SPQR-internal* half of the question precisely:

- §2 identifies the library entry point `decode_state` (`src/lib.rs:472`), called from
  `send()` (`lib.rs:266`), `recv()` (`lib.rs:362`), and `current_version()` (`lib.rs:250`).
- §2 traces the flow `decode_state` → `Chain::from_pb` (`chain.rs:434`) →
  `ChainEpochDirection::from_pb` (`chain.rs:306`), plus `Authenticator::from_pb` and
  `PolyDecoder::from_pb`.
- §11 step 1 ("Load persisted state ← CORRUPTED BLOB LOADED HERE") restates this.

### What the report does **not** say

The question asks where the state is loaded **in production**, i.e. in the host application
that consumes the `spqr` crate. The report never names the host crate, file, function, or
storage field. It refers only generically to "the upstream libsignal integration", "the host",
and "local storage (protobuf blob)". Specifically absent:

1. The production consumer of `spqr::SerializedState` (which crate/struct holds the bytes).
2. The on-disk container (which protobuf message/field wraps the SPQR blob).
3. The exact call sites of `spqr::send` / `spqr::recv` in the host.
4. Whether the host's panic-catching (`catch_unwind`) speculation in the Executive Summary
   (lines 22–25) is confirmed or not — the report hedges with "may wrap calls".

Because the threat model (§1) is *persisted local state*, the host-side load path is the
crux of the question; without it, Q1 is only partially answered.

### Answer obtained during this evaluation

Verified against the sibling checkout `/Users/hoangtruong/Documents/lean/Max/libsignal`
(commit `a47ba487`, 2026‑03‑17), which pins
`spqr = { git = ".../SparsePostQuantumRatchet.git", tag = "v1.5.0" }` (`Cargo.toml:89`) —
matching this repository's `Cargo.toml` `version = "1.5.0"`.

**Production load path (libsignal → spqr):**

| Layer | Location | Detail |
|---|---|---|
| On-disk container | `rust/protocol/src/proto/storage.proto:66` | `SessionStructure.pq_ratchet_state = 15` (`bytes`) — the raw `spqr::SerializedState` is embedded inside libsignal's per-session protobuf |
| Record decode | `rust/protocol/src/state/session.rs:663-671` | `SessionRecord::deserialize` → `RecordStructure::decode`; `current_session` becomes a `SessionState` via `From<SessionStructure>` (`session.rs:624`). Only prost wire-format validity is checked. |
| Previous sessions | `rust/protocol/src/state/session.rs:725-733` | `previous_session_states()` decodes archived sessions lazily; same non-validation |
| Storage trait | `rust/protocol/src/storage/traits.rs:152` | `SessionStore::load_session(&ProtocolAddress) -> Result<Option<SessionRecord>>` — implemented by the app (Android/iOS/Desktop) over its SQLite DB |
| State holder | `rust/protocol/src/state/session.rs:147,163` | `SessionState::new(..., pq_ratchet_state: spqr::SerializedState)` stores the bytes verbatim |
| Initial creation | `rust/protocol/src/ratchet.rs:101,192` | `spqr::initial_state(spqr::Params{ version: V1, direction: A2B / B2A, min_version: V0, ... })` for Alice / Bob |
| **Load + use (recv)** | `rust/protocol/src/state/session.rs:601-608` | `SessionState::pq_ratchet_recv` → `spqr::recv(&self.session.pq_ratchet_state, msg)` — **this is where `decode_state` → `Chain::from_pb` executes in production on the receive path**; the returned `state` overwrites the field |
| **Load + use (send)** | `rust/protocol/src/state/session.rs:610-617` | `SessionState::pq_ratchet_send` → `spqr::send(&self.session.pq_ratchet_state, csprng)` — same for the send path |
| Recv caller | `rust/protocol/src/session_cipher.rs:633-647` | `decrypt_message_with_state` calls `pq_ratchet_recv`; maps `spqr::Error::StateDecode` → `SignalProtocolError::InvalidState`, all other errors → `InvalidMessage` |
| Send caller | `rust/protocol/src/session_cipher.rs:37-43` | `message_encrypt` calls `pq_ratchet_send`; any error → `SignalProtocolError::InvalidState("message_encrypt", …)` |

**Ordering relative to outer authentication (relevant to §11 of the report):** in
`decrypt_message_with_state` the SPQR `recv` runs *after* Double-Ratchet chain/message-key
derivation but *before* the outer envelope MAC verification, exactly as the report's §11
step ordering asserts. A panic inside `spqr::recv` therefore fires before the MAC check.

**Panic handling at the host boundary (confirms the report's hedge):**

| Bridge | Location | Mechanism |
|---|---|---|
| C FFI (iOS/Swift) | `rust/bridge/shared/types/src/ffi/mod.rs:399-413` | `run_ffi_safe` wraps every call in `std::panic::catch_unwind`; panics become `UnexpectedPanic` errors |
| JNI (Android) | `rust/bridge/shared/types/src/jni/mod.rs:1148-1157` | `run_ffi_safe` with `catch_unwind(AssertUnwindSafe(..))` |
| Node (Desktop) | `rust/bridge/shared/types/src/node/futures.rs:104-204` | `catch_unwind` on futures; Neon also catches panics |

So the Executive Summary's "libsignal's FFI/JNI bridges *may* wrap calls in `catch_unwind`"
can be upgraded to a definite statement: **all three production bridges do catch panics**.
The corrupted-blob defect therefore surfaces in production as a bridge-level
`UnexpectedPanic` error (not a process abort), but — as the report correctly argues — the
session state is still unrecoverable by the caller, since libsignal has no code path that
resets `pq_ratchet_state` on `InvalidState`; only the app archiving/deleting the session helps.

**Concise answer to Q1:** Persisted SPQR state is loaded in production by libsignal's
`SessionState::pq_ratchet_recv` / `pq_ratchet_send`
(`libsignal/rust/protocol/src/state/session.rs:601-617`), which pass the bytes of
`SessionStructure.pq_ratchet_state` (protobuf field 15, `storage.proto:66`) — obtained via
the app-provided `SessionStore::load_session` and `SessionRecord::deserialize` — directly
into `spqr::recv` / `spqr::send`, where `decode_state` (`spqr/src/lib.rs:472`) and the
unvalidated `from_pb` chain run.

---

## Q2. Does that state pass through the specific `from_pb()` implementation identified by the finding?

### What the report says

Yes, and it does so explicitly. The report identifies the primary defect as
`ChainEpochDirection::from_pb` (`src/chain.rs:306-312`, §3) and gives the call chain in §2
(lines 127–128) and §4 (lines 178–188):

```
recv() [lib.rs:356]
  → chain_from() [lib.rs:343]
    → Chain::from_pb() [chain.rs:434]
      → ChainEpochDirection::from_pb() [chain.rs:306]
  → chain.recv_key(epoch, index) [lib.rs:435]
```

It also names the secondary/tertiary/quaternary `from_pb`s (`Chain::from_pb`,
`Authenticator::from_pb` at `authenticator/serialize.rs:16`, `PolyDecoder::from_pb` at
`encoding/polynomial.rs:815`) and notes (§11, line 514) that `States::from_pb(pb)?.recv()`
runs on the same blob.

### Independent verification (spqr `v1.5.0` source in this repository)

Every link of the chain was confirmed by reading the code; all line numbers cited by the
report are accurate:

| Step | Location | Verified detail |
|---|---|---|
| 1 | `src/lib.rs:362` (`recv`) / `lib.rs:266` (`send`) | `decode_state(state)?` — prost decode only |
| 2 | `src/lib.rs:428` (`recv`) | `chain_from(state_pb.chain, state_pb.version_negotiation.as_ref())?` |
| 2′ | `src/lib.rs:288` (`send`) | `Some(pb) => Some(Chain::from_pb(pb)?)` — the send path also reaches the defect |
| 2″ | `src/lib.rs:401-404` (`recv`, downgrade branch) | `chain_from(prenegotiated_state_pb.chain, …)` — a third call site during version negotiation |
| 3 | `src/lib.rs:343-354` | `chain_from`: `Some(pb) => Ok(Chain::from_pb(pb)?)`; only when `chain == None` does it fall back to `Chain::new` via `chain_from_version_negotiation` |
| 4 | `src/chain.rs:434-452` | `Chain::from_pb` maps every `links[i]` through `ChainEpochDirection::from_pb(link.send…)` and `…(link.recv…)` (L445–446) |
| 5 | `src/chain.rs:306-312` | `ChainEpochDirection::from_pb` copies `ctr`, `next`, `prev` verbatim — no checks, exactly as quoted in §3 |
| 6 | `src/lib.rs:435` | `chain.recv_key(msg_key_epoch, index)?` consumes the unvalidated struct |

Parallel path for the other `from_pb`s named in the finding:

- `lib.rs:425` → `v1::chunked::states::States::from_pb` (`src/v1/chunked/states/serialize.rs:49`)
  → per-state `from_pb`s in `src/v1/chunked/send_ct/serialize.rs` / `send_ek/serialize.rs`
  → `PolyDecoder::from_pb` / `PolyEncoder::from_pb`.
- `src/v1/unchunked/send_ct/serialize.rs:20,38,62` → `Authenticator::from_pb`.

### When the `chain` field is present in production

`Chain::from_pb` is reached only when `PqRatchetState.chain` is `Some`. In libsignal's flow:

- `spqr::initial_state` (`lib.rs:212-236`, called from `libsignal/rust/protocol/src/ratchet.rs:101,192`)
  writes `chain: None` plus a `version_negotiation` block. On the **first** `send`/`recv`
  the chain is therefore constructed fresh via `chain_from_version_negotiation` → `Chain::new`
  (`lib.rs:333-341`), bypassing `from_pb`.
- Every `send`/`recv` then persists `chain: Some(chain.into_pb())` (`lib.rs:313`, `lib.rs:443`).
  From the second operation onward — i.e. for the entire life of an established session —
  `Chain::from_pb` → `ChainEpochDirection::from_pb` runs on **every** `spqr::send` and
  `spqr::recv`, on bytes taken verbatim from libsignal's `SessionStructure.pq_ratchet_state`
  (see Q1).

### Conclusion for Q2

**Yes.** The persisted production blob (`SessionStructure.pq_ratchet_state`) is passed by
libsignal to `spqr::recv`/`spqr::send`, which — for any session that has performed at least
one prior SPQR operation — deserialises it through `Chain::from_pb` (`chain.rs:434`) and
thence through the exact `ChainEpochDirection::from_pb` (`chain.rs:306`) identified as the
primary defect, as well as the `States::from_pb` → `PolyDecoder`/`Authenticator::from_pb`
paths of the secondary findings. The report's call-chain claims are correct and complete;
the only nuance it omits is the first-operation exception (fresh `Chain::new` while
`chain == None`), which does not weaken the finding.

---

## Q3. Is there any semantic validation that establishes the invariants required by downstream operations?

### What the report says

**No** — and this is the report's core thesis, stated and evidenced at several levels:

- §3 (line 146): "**Zero validation is performed.** The function unconditionally returns
  `Ok` for any protobuf-valid input."
- §2 (lines 121–125): `decode_state` validates only prost wire-format; none of
  `Chain::from_pb`, `ChainEpochDirection::from_pb`, `Authenticator::from_pb`,
  `PolyDecoder::from_pb` validate semantic invariants.
- §10.1–10.2: the Lean spec `from_pb_spec` maps the `Err` branch to `False` (proves the
  function *never* rejects) and the `Ok` branch to pure field-copy equalities, while the
  downstream specs require `h_next_len`, `h_data_aligned`, `h_key_ge`, `h_prev_ctr`,
  `h_ctr_bound` — none established anywhere.
- §9 acknowledges the one *partial* exception: `PolyDecoder::from_pb` checks
  `pts.len() == 16` and per-slot `% 4`, but not `pts_needed`/`is_complete` consistency.
- §15 "Integration Mitigation?" column: "None inside SPQR" for every component.

### Independent verification

**(a) The `from_pb` chain on the production path (spqr `v1.5.0`):**

| Function | Location | Checks performed | Invariants *required* downstream but **not** checked |
|---|---|---|---|
| `decode_state` | `src/lib.rs:472-481` | prost decode only | everything semantic |
| `Chain::from_pb` | `src/chain.rs:434-452` | `direction` enum via `try_into`; `link.send/recv` and `params` are `Some` | `next_root.len()==32` (HKDF salt, L358); `links.len()≥1`; `send_epoch ≤ current_epoch`; position-dependent `send.next` non-empty |
| `ChainEpochDirection::from_pb` | `src/chain.rs:306-312` | **none** — verbatim copy of `ctr`, `next`, `prev` | `next.len()==32` (L229 `assert!`, L243 `copy_from_slice`); `prev.len() % 36 == 0` (L191 `assert_eq!`); `prev.len() ≤ 36·ctr` ⇒ `ctr ≥ max_ooo` when GC fires (L149 `assert!`) |
| `ChainParamsPB` getters | `src/chain.rs:63-80` | zero → default substitution only | no upper bounds; `key()` relies on `hax_lib::assume!` (L262-264, L275-277, L280-283) for `max_ooo_keys < 390451572`, `trim_size() < 119304647` — **assumed, not checked** |
| `Authenticator::from_pb` | `src/authenticator/serialize.rs:16-21` | **none** — infallible, returns `Self` not `Result` | `root_key`/`mac_key` lengths |
| `PolyDecoder::from_pb` | `src/encoding/polynomial.rs:815-855` | `pts.len()==16`; each `pts[i].len() % 4 == 0` | `pts_needed` range; `is_complete` ⇔ enough points; per-slot point-count bounds |
| `States::from_pb` + per-state `from_pb`s | `src/v1/chunked/states/serialize.rs:49`, `src/v1/chunked/{send_ct,send_ek}/serialize.rs` | presence (`ok_or(StateDecode)`) and a few `MsgDecode` length checks | no cross-field consistency |

**(b) Downstream consumers that *assume* the invariants** (all in `src/chain.rs`):

- `KeyHistory::gc` L149: `assert!(current_key >= params.max_ooo_keys_or_default())`
- `KeyHistory::get` L191: `assert_eq!(self.data.len() % Self::KEY_SIZE, 0)`
- `next_key_internal` L229: `assert!(!next.is_empty())`; L243 `next.copy_from_slice(&genr8r[..32])`
  panics unless `next.len() == 32`
- `add_epoch` L355: `assert!(epoch_secret.epoch == self.current_epoch + 1)` — `current_epoch`
  comes straight from the blob
- hax `#[hax_lib::requires]` on `next_key` (L220), `next_key_internal` (L226), `add` (L138),
  `remove` (L174) are contract annotations generating proof obligations, **not** runtime
  checks. Inside `key()`/`send_key()` they are discharged with `hax_lib::assume!`
  (L262, L273, L275, L280, L291, L401), i.e. explicitly *assumed*.

**(c) Host side (libsignal `a47ba487`):** the only inspections of `pq_ratchet_state` are
`is_empty()` (`state/session.rs:277`, usability check) and the opaque accessor
`current_pq_state()` (`session.rs:781`). No host-level validation exists; the bytes are
passed through verbatim (see Q1).

**(d) Mechanised confirmation** — `Spqr/Specs/Bugs/CorruptedBlobs.lean` exists and contains
the theorems the report cites, including:

- `from_pb_never_fails` (L54) — re-exports `chain.ChainEpochDirection.from_pb_spec`
  (`Spqr/Specs/Chain/ChainEpochDirection/FromPb.lean:29`), whose `Err` branch is `False`.
- `from_pb_admits_wrong_next_length` (L68), `from_pb_admits_misaligned_prev` (L86),
  `from_pb_admits_large_prev_small_ctr` (L107), `from_pb_admits_triple_violation` (L132).
- `get_never_ok` (L163), `gc_never_ok` (L189), `next_key_internal_never_ok` (L278).
- End-to-end: `restore_then_recv_panics_bad_next` (L518), `…_misaligned_prev` (L534),
  `…_large_prev_small_ctr` (L551).
- `authenticator_from_pb_no_validation` (L608), `chain_from_pb_admits_wrong_next_root` (L662).
- `recvKeyPre_unsatisfiable_*` (L777–801): the `recv_key` precondition is *unsatisfiable*
  for the corrupted states — no validation anywhere could make it hold post-load.

### Conclusion for Q3

**No.** Neither SPQR nor the libsignal host performs any semantic validation that
establishes the invariants required by `next_key_internal`, `KeyHistory::get`,
`KeyHistory::gc`, or `add_epoch`. The only checks on the load path are protobuf wire-format
decoding, enum/presence checks, and `PolyDecoder`'s two shape checks; every structural
invariant (`next.len()==32`, `prev.len()%36==0`, `prev.len()≤36·ctr`, `next_root.len()==32`,
parameter bounds) is either an `assert!` at the point of use (→ panic) or a
`hax_lib::assume!`/`requires` proof obligation with no runtime counterpart. The report's
answer is correct, complete, and — for the primary defect — machine-checked.

One point worth adding to the report: `ChainParams` bounds (`max_ooo_keys`, `max_jump`,
`trim_size()`) are also loaded from the blob (`chain.rs:450`) and are only `assume!`d in
`key()`, so an out-of-range `params` message is a further unvalidated input class not
listed in §7.

---

## Q4. Can we construct a concrete protobuf that is protobuf-valid but violates one of those invariants?

### What the report says

**Yes — comprehensively.** The report provides concrete protobuf constructions at two levels:

1. **Lean-mechanised witnesses (§10.4, Phase 2a)**: The file `Spqr/Specs/Bugs/CorruptedBlobs.lean`
   constructs explicit protobuf values that pass `from_pb` (protobuf-valid, deserialization succeeds)
   but violate each downstream invariant:

   | Theorem | Invariant Violated | Construction |
   |---|---|---|
   | `from_pb_admits_wrong_next_length` | `h_next_len : next.length = 32` | `pb.next` with length ≠ 32 |
   | `from_pb_admits_misaligned_prev` | `h_data_aligned : v.length % 36 = 0` | `pb.prev` with length not divisible by 36 |
   | `from_pb_admits_large_prev_small_ctr` | `h_key_ge : max_ooo ≤ ctr` | `pb.ctr = 0`, `pb.prev.length ≥ 79236` |
   | `from_pb_admits_triple_violation` | All three above simultaneously | Single protobuf violating all three |

2. **Step-by-step attack recipes (§12)**: Four concrete scenarios describe exact field
   modifications to a serialised `PqRatchetState`:

   | Scenario | §  | Modification | Outcome |
   |---|---|---|---|
   | Session kill | §12.1 | `recv.next = [0]` (1 byte) | Panic in `next_key_internal` |
   | Silent divergence | §12.2 | `chain.next_root = [0; 16]` (16 bytes) | Wrong keys, silent failure at Signal layer |
   | One-byte DoS | §12.3 | Append 1 byte to `recv.prev` | Panic in `KeyHistory::get` |
   | Counter underflow | §12.4 | `ctr = 0`, large `prev` | Panic in `KeyHistory::gc` |

3. **End-to-end panic proofs (Phase 4)**: The Lean theorems chain construction → `from_pb` →
   `key()` → no `Ok` result exists, proving the corrupted protobuf causes an unrecoverable
   panic in the Aeneas model of Rust execution:
   - `restore_then_recv_panics_bad_next`
   - `restore_then_recv_panics_misaligned_prev`
   - `restore_then_recv_panics_large_prev_small_ctr`

4. **Crash-loop proof (Phase 5)**: `corrupted_state_roundtrips` proves `into_pb (from_pb pb) = pb`,
   meaning the corrupted state persists across restarts.

5. **Authenticator (Phase 6)**: `authenticator_from_pb_admits_wrong_key_lengths` shows that
   `Authenticator::from_pb` accepts keys of any length, violating the implicit 32-byte requirement.

### Verdict

**Fully answered.** The report provides 4+ concrete constructions with 3 machine-checked end-to-end
panic proofs plus a crash-loop proof. No additional work is needed for Q4.

The only suggested enhancement (§14, recommended test #2) is committing Rust reproductions as
`docs/corrupted_blob_counterexample.rs.txt` — this is a nice-to-have documentation artifact,
not a gap in the answer.

---

## Q5. Does the production `from_pb()` accept that protobuf and return `Ok`?

### What the report says

The report answers this **explicitly and definitively** in §3 (lines 137–148):

```rust
fn from_pb(pb: pqrpb::chain::epoch::EpochDirection) -> Result<Self, Error> {
    Ok(Self {
        ctr: pb.ctr,
        next: pb.next,
        prev: KeyHistory { data: pb.prev },
    })
}
```

> **Zero validation is performed.** The function unconditionally returns `Ok` for any
> protobuf-valid input. (§3, line 146–147)

The same pattern is documented for the other `from_pb` functions:

| `from_pb` function | Always returns `Ok`? | Report section |
|---|---|---|
| `ChainEpochDirection::from_pb` (`chain.rs:306-312`) | **Yes** — wraps fields directly in `Ok(Self{..})` | §3 |
| `Chain::from_pb` (`chain.rs:434`) | **Yes** — only checks the `direction` enum discriminant via `try_into()`, no semantic validation | §7 |
| `Authenticator::from_pb` | **Yes** — no key-length checks | §8 |
| `PolyDecoder::from_pb` | **Yes** — no bounds on slot sizes or `is_complete` | §9 |

### Verification against production source

Confirmed by reading `src/chain.rs:306-312` (this repository): the function body is exactly as
quoted in the report. There is no `if` / `match` / early-return / `?`-propagation on any field —
only the infallible struct construction wrapped in `Ok(...)`. Any `pqrpb::chain::epoch::EpochDirection`
that prost successfully decodes will produce `Ok(ChainEpochDirection { .. })`, regardless of whether
the field values satisfy the invariants required by `next_key_internal`, `KeyHistory::get`, or
`KeyHistory::gc`.

### Mechanised evidence

The Lean specification in `Spqr/Specs/Bugs/CorruptedBlobs.lean` proves the stronger end-to-end
property: not only does `from_pb` return `Ok`, but the resulting state then **panics** on use.
Specifically, the Phase 3–4 theorems (`restore_then_recv_panics_*`) prove:

```
from_pb pb = Ok ced  →  ∀ r, key ced at params ≠ ok r
```

This confirms that `from_pb` accepts the corrupted protobuf (`Ok ced`) *and* that downstream
operations fail (no successful result exists).

### Verdict

**Fully answered.** The report explicitly states that `from_pb` performs zero validation and
unconditionally returns `Ok` (§3), verified both by source inspection and machine-checked Lean proofs.
No additional work is needed for Q5.

---

## Q6. Can the resulting invalid state actually reach `send()`/`recv()` in production?

### What the report says

The report answers this question **affirmatively and in detail** across multiple sections:

**§2 (Architectural Context)** shows the complete data-flow diagram: `decode_state()` →
`from_pb()` → in-memory state → `send()`/`recv()`. There is **no validation gate** between
`from_pb()` and the operational functions. The decoded state is used immediately.

**Code-level confirmation** (`src/lib.rs`):

- **`recv()` (L356)**: calls `decode_state(state)?` (L362), then `chain_from(state_pb.chain, …)?`
  (L428) which calls `Chain::from_pb(pb)?` (L348), then immediately calls
  `chain.recv_key(msg_key_epoch, index)?` (L435). The corrupted `ChainEpochDirection` inside the
  chain is used directly by `recv_key()` → `key()` → `next_key_internal()` / `get()` / `gc()`.
  There is zero intervening validation.

- **`send()` (L265)**: calls `decode_state(state)?` (L266), then `Chain::from_pb(pb)?` (L288),
  then `chain.send_key(msg.epoch - 1)?` (L300). Same absence of validation.

**§12 (Attack Scenarios)** provides four concrete end-to-end scenarios (§12.1–§12.4) where
corrupted state reaches `send()`/`recv()` and causes panics or silent divergence. Each
scenario traces the full path: modify blob → restore → call `recv()` → panic.

**§10.4 (Lean Proofs)** provides machine-checked evidence via Phase 3–4 theorems
(`restore_then_recv_panics_bad_next`, `restore_then_recv_panics_misaligned_prev`,
`restore_then_recv_panics_large_prev_small_ctr`) that prove: if `from_pb` returns `Ok` on a
corrupted blob, then the downstream `key()` function has **no successful execution** — i.e.,
it panics. Phase 5 (`corrupted_state_roundtrips`) further proves that the corrupted state
persists through `into_pb`/`from_pb` round-trips, creating a permanent crash loop.

**Production-level confirmation** (from Q1 analysis of libsignal): the host application
`libsignal` passes `SerializedState` directly to `spqr::recv()` / `spqr::send()` without
any intermediate validation (`rust/protocol/src/state/session.rs:663-671`, then
`rust/protocol/src/session_cipher.rs`). The FFI bridges (`run_ffi_safe`) catch panics as
`UnexpectedPanic` errors but do not prevent the invalid state from reaching SPQR's
`send()`/`recv()`.

### Key finding

There are **zero validation checkpoints** between `from_pb()` and `send()`/`recv()`:

| Step | Location | Validation? |
|---|---|---|
| 1. Load blob from storage | libsignal `SessionRecord::deserialize` | Protobuf wire-format only |
| 2. Pass to SPQR | `spqr::recv(state, msg)` | None |
| 3. Decode protobuf | `decode_state(state)` (`lib.rs:472`) | Protobuf wire-format only |
| 4. Reconstruct chain | `Chain::from_pb(pb)` (`lib.rs:348`) | None — fields copied verbatim |
| 5. Use chain | `chain.recv_key(epoch, index)` (`lib.rs:435`) | **Panics on invariant violation** |

### Verdict

**Fully answered.** The report demonstrates through architecture diagrams (§2), source-level
tracing (§2, §12), and machine-checked proofs (§10.4) that invalid state from `from_pb()`
flows directly into `send()`/`recv()` with no intervening validation. The answer is
unambiguously *yes*. No additional work is needed for Q6.

---

## Q7. Does executing send()/recv() with that state actually produce the claimed panic rather than a recoverable error?

### What the report says

The report argues across multiple sections that the failure mode is a **panic** (unrecoverable),
not a recoverable `Err`:

1. **§4 (Panic Path 1 — `next_key_internal`)**: `chain.rs:229` uses `assert!(!next.is_empty())`
   and L243 uses `next.copy_from_slice(&genr8r[..32])`. Both are Rust panics when
   `next.len() ≠ 32`: the `assert!` fires for empty `next`, and `copy_from_slice` panics on
   length mismatch for any `next.len() ≠ 32`.

2. **§5 (Panic Path 2 — `KeyHistory::get`)**: `chain.rs:191` uses
   `assert_eq!(self.data.len() % Self::KEY_SIZE, 0)`. This is a Rust panic when `prev.data`
   is misaligned.

3. **§6 (Panic Path 3 — `KeyHistory::gc`)**: `chain.rs:149` uses
   `assert!(current_key >= params.max_ooo_keys_or_default())`. This is a Rust panic when
   `ctr` is too small relative to `prev` size.

4. **§10.4 (Lean mechanisation)**: Three end-to-end theorems —
   `restore_then_recv_panics_bad_next`, `restore_then_recv_panics_misaligned_prev`, and
   `restore_then_recv_panics_large_prev_small_ctr` — prove that the composition
   `from_pb` → `key` has **no successful execution** (`∀ r, key ced at params ≠ ok r`).
   In the Aeneas model of Rust, this corresponds to a panic: the function diverges rather
   than returning a `Result`.

5. **§12 (Attack Scenarios)**: §12.1, §12.3, §12.4 each trace the concrete call chain from
   `recv()` → `recv_key()` → `key()` → panic site and label the outcome as "panic".

6. **§14 (Recommended Fixes)**: The fix section distinguishes the current `assert!` (panic)
   from the proposed `return Err(Error::InternalInvariantViolation)` (recoverable), explicitly
   noting the signature changes required for `gc` and `next_key_internal`.

### Verification against source

Confirmed by reading the actual Rust source (`src/chain.rs`):

| Line | Statement | Failure mode |
|---|---|---|
| L229 | `assert!(!next.is_empty());` | **Panic** (macro expands to `panic!`) |
| L243 | `next.copy_from_slice(&genr8r[..32]);` | **Panic** if `next.len() ≠ 32` |
| L191 | `assert_eq!(self.data.len() % Self::KEY_SIZE, 0);` | **Panic** (macro expands to `panic!`) |
| L149 | `assert!(current_key >= params.max_ooo_keys_or_default());` | **Panic** (macro expands to `panic!`) |

None of these sites return `Err`. The `key()` method (`chain.rs:247`) returns
`Result<Vec<u8>, Error>`, but these `assert!` statements execute *before* any `Err` return
branch is reached on the affected code paths. A Rust `assert!` is syntactic sugar for
`if !cond { panic!(...) }` — it unwinds the stack (or aborts, depending on `panic = "abort"`
in the profile), it does **not** produce an `Err`.

### What is missing

The report does **not** include an executable Rust reproduction that demonstrates the panic
at runtime (e.g., a `#[test]` using `std::panic::catch_unwind`). §14 explicitly recommends
creating such tests (\"a concrete Rust repro for each of §12.1/§12.3/§12.4 ... wrap in
`std::panic::catch_unwind` and assert it panics\"), but these tests do not yet exist in the
repository. The evidence is instead:

- **Static**: direct inspection of `assert!` macro usage in source (conclusive — `assert!`
  is unconditionally a panic in Rust).
- **Formal**: Lean proofs that no `ok` result exists (mechanically verified).

Both are sufficient to answer Q7 conclusively without a runtime test, because the semantics
of `assert!` in Rust are definitional, not empirical.

### Verdict

**Answered.** The report establishes through source-level analysis (§4–§6), formal proof
(§10.4), and fix recommendations (§14) that the failure mode is definitively a **panic**, not
a recoverable `Err`. The three `assert!`/`assert_eq!` sites in `chain.rs` (L149, L191, L229)
and the `copy_from_slice` at L243 are all unconditional Rust panics. The Lean theorems
mechanically verify that no successful return exists. An executable `catch_unwind` test would
add further confidence but is not required to answer the question — the static and formal
evidence is conclusive.

---

## Updated Tally

| # | Question | Status |
|---|---|---|
| Q1 | Where is persisted SPQR state loaded in production? | **Partially answered** (completed during Q1 evaluation above) |
| Q2 | Does that state pass through the specific `from_pb()` implementation? | **Answered** |
| Q3 | Is there any semantic validation that establishes the required invariants? | **Answered** (no) |
| Q4 | Can we construct a concrete protobuf that violates invariants? | **Answered** (yes, machine-checked) |
| Q5 | Does `from_pb()` accept that protobuf and return `Ok`? | **Answered** (yes, unconditionally) |
| Q6 | Can the resulting invalid state reach `send()`/`recv()`? | **Answered** (yes, immediately) |
| Q7 | Does executing `send()`/`recv()` produce a panic rather than a recoverable error? | **Answered** (yes — `assert!` panics, confirmed by source and Lean proofs) |

**Tally**: 6 of 7 questions fully answered; 1 of 7 partially answered (Q1); 0 unanswered.

---

## Execution Plan for Remaining Gaps


Q1 is answered above, but the report itself still lacks this information, and two claims
made during the answer deserve tighter verification. Steps, in order:

1. **Patch `docs/CorruptedBlobs.md` §2** — add a "Production load path" subsection with the
   libsignal table above (file/line references at libsignal commit `a47ba487`, spqr
   `v1.5.0`). Include `storage.proto:66` so the on-disk container is explicit.
2. **Patch the Executive Summary (lines 22–25) and §11/§13/§15** — replace "may wrap calls in
   `catch_unwind`" with the confirmed `run_ffi_safe` references for FFI, JNI, and Node;
   change the failure-mode wording from "process crash" to "bridge-level `UnexpectedPanic`
   error; session remains unrecoverable".
3. **Verify the auth-ordering claim with line numbers** — read
   `libsignal/rust/protocol/src/session_cipher.rs` from `decrypt_message_with_state` through
   the MAC verification (`verify_mac`) and record exact lines to support §11 step 3
   ("Never reached: Verify outer Signal envelope MAC").
4. **Confirm no host-side validation exists** — grep libsignal for any inspection of
   `pq_ratchet_state` beyond `is_empty()` (`session.rs:277`) and `current_pq_state()`
   (`session.rs:781`), to back the "Integration mitigation: None" column in §15 with
   evidence rather than assertion.
5. **Add a reproduction at the production boundary** (optional; strengthens the MEDIUM
   rating) — in libsignal's `rust/protocol/tests/session.rs`, build a session, extract
   `current_pq_state()`, mutate `prev.data` per §12.1, re-embed it in `SessionStructure`,
   and assert that `message_decrypt` returns an error (or panics pre-fix under
   `catch_unwind`). This mirrors the report's recommended test #2 (§14) at host level.
6. **Pin versions in the report** — state that the analysis targets spqr `v1.5.0` as
   consumed by libsignal `a47ba487`, so future readers can tell whether a later spqr
   release added `from_pb` validation.
7. **(Q2 nuance) Note the `chain == None` exception in §2** — add one sentence that
   `Chain::from_pb` is bypassed only on the very first `send`/`recv` of a session (fresh
   `Chain::new` from `version_negotiation`, `lib.rs:333-354`), and that the `send` path
   (`lib.rs:288`) and the downgrade branch (`lib.rs:401-404`) are additional entry points
   beyond the `recv` chain the report already documents.
8. **(Q3 addition) Add unvalidated `ChainParams` to §7** — `Chain::from_pb` (`chain.rs:450`)
   accepts any `params`; the bounds `max_ooo_keys < 390451572` and
   `trim_size() < 119304647` that `key()` needs are only `hax_lib::assume!`d
   (`chain.rs:262-283`). Recommend a range check in `Chain::from_pb` (§14.1) and, optionally,
   a Lean `chain_from_pb_admits_oversized_params` theorem in `CorruptedBlobs.lean`.

