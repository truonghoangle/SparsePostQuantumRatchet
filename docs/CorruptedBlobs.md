# Independent Study: Unvalidated Deserialized State Blobs in SPQR

## Executive Summary

This report analyses a class of defects in the SPQR (Sparse Post-Quantum Ratchet) codebase
where protobuf-deserialized state blobs are accepted without semantic validation. Unlike the
chunk-poisoning attack (Finding 2 in `report.md`), which targets network messages and is
mitigated by the upstream libsignal integration's authentication-before-commit pattern, the
corrupted-blob class targets **persisted local state** — a threat surface that the network-level
authentication does not cover.

**Core finding**: Every `from_pb` function in SPQR's persistence layer blindly trusts the
protobuf fields it receives. The Lean formal specifications expose this gap mechanically:
they require structural invariants (`h_next_len`, `h_data_aligned`, `h_key_ge`, etc.) as
preconditions that nothing in the deserialization path establishes. A protobuf-valid but
semantically inconsistent state blob — arising from storage corruption, backup-restore bugs,
or malicious modification of the local database — converts subsequent `send()`/`recv()` calls
into unrecoverable panics rather than graceful `Err(StateDecode)` returns.

**Severity**: MEDIUM — panics are denial-of-service against the session when corrupted state
is loaded. The primary threat is non-adversarial: storage corruption, truncated writes,
backup/restore bugs, and schema skew. A `panic` at the FFI boundary becomes a bridge-level
`UnexpectedPanic` error, whereas an `Err(StateDecode)` lets the integrator log, reset, and
recover. All three production bridges (C FFI, JNI, Node) catch panics via `run_ffi_safe` /
`catch_unwind` (see §2.1), so the process does not abort — but the session remains
unrecoverable, since libsignal has no code path that resets `pq_ratchet_state` on error.
No mitigation exists *inside SPQR itself*.

**Analysed versions**: spqr `v1.5.0` as consumed by libsignal commit `a47ba487` (2026‑03‑17).
Future spqr releases may add `from_pb` validation; readers should verify against the
version they are evaluating.

**Mechanised evidence**: the primary defect (§§3–6) and its reachability from `recv()`
(§12.1, §12.3, §12.4) are machine-checked in
`Spqr/Specs/Bugs/CorruptedBlobs.lean`, which proves the *negative* form of the desired safety
property: for each scenario, `from_pb pb = Ok ced → ∀ r, key ced at params ≠ ok r` (no
successful execution exists — the Aeneas model of a Rust panic). See §10.4. The secondary
defects also have Lean witnesses: `Chain::from_pb` copies `next_root` verbatim (§7, Phase 7),
`PolyDecoder::from_pb` copies `is_complete` verbatim (§9, Phase 8), and the `recv_key` spec
precondition is unsatisfiable on corrupted `recv` directions (§10.4, Phase 9). The remaining
§7 `Chain`-level cases (`send_epoch` ordering, position-dependent `send.next`, `params`
ranges) and the §9 slot-size bound are **prose-only**.

---

## Table of Contents

1. [Threat Model](#1-threat-model)
2. [Architectural Context](#2-architectural-context-the-persistence-boundary)
   - 2.1. [Production Load Path (libsignal → spqr)](#21-production-load-path-libsignal--spqr)
3. [Primary Defect: `ChainEpochDirection::from_pb`](#3-primary-defect-chainepochdirectionfrom_pb)
4. [Panic Path 1: `next_key_internal`](#4-panic-path-1-next_key_internal--length-mismatch)
5. [Panic Path 2: `KeyHistory::get`](#5-panic-path-2-keyhistoryget--alignment-assertion)
6. [Panic Path 3: `KeyHistory::gc`](#6-panic-path-3-keyhistorygc--counter-underflow)
7. [Secondary Defect: `Chain::from_pb`](#7-secondary-defect-chainfrom_pb)
8. [Tertiary Defect: `Authenticator::from_pb`](#8-tertiary-defect-authenticatorfrom_pb)
9. [Quaternary Defect: `PolyDecoder::from_pb`](#9-quaternary-defect-polydecoderfrom_pb)
10. [Lean Specification Evidence](#10-lean-specification-evidence)
11. [Why Network Authentication Does Not Help](#11-comparison-with-finding-2-chunk-poisoning)
12. [Attack Scenarios](#12-attack-scenarios)
13. [Impact Assessment](#13-impact-assessment)
14. [Recommended Fixes](#14-recommended-fixes)
15. [Summary](#15-summary)


---

## 1. Threat Model

The corrupted-blob threat model differs fundamentally from the network-message threat model:

| Property | Network Message (Finding 2) | Corrupted Blob (This Study) |
|---|---|---|
| **Entry point** | `Message::deserialize` (wire) | `decode_state` → `from_pb` (storage) |
| **Authentication** | Signal envelope MAC covers payload | None — blob is trusted once loaded |
| **Attacker capability** | Forge/replay network messages | Modify local storage (disk, backup, cloud sync) |
| **Integration mitigation** | Auth-before-commit blocks poisoning | **None inside SPQR** — `from_pb` runs at load time, pre-auth; host catches panics as `UnexpectedPanic` (§2.1) but session is unrecoverable |
| **Failure mode** | Permanent epoch stall | Panic (unrecoverable inside SPQR; crash loop on reload) |

Concrete scenarios where a corrupted blob reaches `from_pb`:

1. **Storage corruption**: bit-flip on disk, filesystem error, incomplete write during crash
2. **Backup/restore**: restoring from an older or partially corrupted backup
3. **Cloud sync conflict**: merging state from multiple devices
4. **Malicious local modification**: attacker with local storage access (rooted device,
   compromised cloud backup) modifies the protobuf state blob
5. **Protobuf version skew**: a future schema change produces blobs that are prost-decodable
   but semantically invalid under current field expectations

---

## 2. Architectural Context: The Persistence Boundary

SPQR's state lifecycle:

```
                   ┌────────────────────────┐
                   │   Local Storage        │
                   │  (protobuf blob)       │
                   └────────┬───────────────┘
                            │ decode_state() / from_pb()
                            │ *** NO VALIDATION ***
                            ▼
                   ┌────────────────────────┐
                   │   In-Memory State      │
                   │  (Chain, Authenticator, │
                   │   PolyDecoder, States)  │
                   └────────┬───────────────┘
                            │ send() / recv()
                            │ *** PANICS HERE ***
                            ▼
                   ┌────────────────────────┐
                   │   Downstream Consumers │
                   │  (next_key_internal,   │
                   │   get, gc, etc.)       │
                   └────────────────────────┘
```

The entry point is `lib.rs:472`:

```rust
fn decode_state(s: &SerializedState) -> Result<pqrpb::PqRatchetState, Error> {
    if s.is_empty() {
        Ok(proto::pq_ratchet::PqRatchetState { inner: None, version_negotiation: None, chain: None })
    } else {
        proto::pq_ratchet::PqRatchetState::decode(s.as_slice()).map_err(|_| Error::StateDecode)
    }
}
```

This only validates **protobuf wire-format correctness** (prost decoding). The decoded state
then flows into `Chain::from_pb` (`chain.rs:434`) → `ChainEpochDirection::from_pb`
(`chain.rs:306`), `Authenticator::from_pb` (`authenticator/serialize.rs:16`), and
`PolyDecoder::from_pb` (`encoding/polynomial.rs:815`) — none of which validate semantic
invariants.

The `recv()` function at `lib.rs:356` calls `chain_from()` at `lib.rs:343-348`, which calls
`Chain::from_pb()` — then immediately uses the result for `recv_key()` at `lib.rs:435`.

**Note on entry points**: `Chain::from_pb` is reached by three distinct call sites:
- **recv path**: `chain_from(state_pb.chain, …)` (`lib.rs:428`)
- **send path**: `Chain::from_pb(pb)` (`lib.rs:288`)
- **version-downgrade branch (recv)**: `chain_from(prenegotiated_state_pb.chain, …)` (`lib.rs:401-404`)

`Chain::from_pb` is bypassed only on the very first `send`/`recv` of a session, where
`chain == None` and a fresh `Chain::new` is created from `version_negotiation`
(`chain_from_version_negotiation`, `lib.rs:333-341`).

### 2.1. Production Load Path (libsignal → spqr)

The following table traces the complete production path from on-disk storage to the SPQR
`from_pb` chain. Verified against the sibling checkout `libsignal` at commit `a47ba487`
(2026‑03‑17), which pins `spqr = { tag = "v1.5.0" }`.

| Layer | Location (libsignal) | Detail |
|---|---|---|
| On-disk container | `rust/protocol/src/proto/storage.proto:66` | `SessionStructure.pq_ratchet_state = 15` (`bytes`) — the raw `spqr::SerializedState` blob |
| Record decode | `rust/protocol/src/state/session.rs:663-671` | `SessionRecord::deserialize` → `RecordStructure::decode`; only prost wire-format checked |
| Previous sessions | `rust/protocol/src/state/session.rs:725-733` | `previous_session_states()` decodes archived sessions lazily; same non-validation |
| Storage trait | `rust/protocol/src/storage/traits.rs:152` | `SessionStore::load_session(&ProtocolAddress) → Result<Option<SessionRecord>>` — app-provided (SQLite) |
| State holder | `rust/protocol/src/state/session.rs:147,163` | `SessionState::new(…, pq_ratchet_state: spqr::SerializedState)` stores the bytes verbatim |
| **Load + use (recv)** | `rust/protocol/src/state/session.rs:601-608` | `SessionState::pq_ratchet_recv` → `spqr::recv(&self.session.pq_ratchet_state, msg)` — **`decode_state` → `Chain::from_pb` executes here** |
| **Load + use (send)** | `rust/protocol/src/state/session.rs:610-617` | `SessionState::pq_ratchet_send` → `spqr::send(&self.session.pq_ratchet_state, csprng)` — same |
| Recv caller | `rust/protocol/src/session_cipher.rs:633-647` | `decrypt_message_with_state` calls `pq_ratchet_recv`; maps `spqr::Error::StateDecode` → `SignalProtocolError::InvalidState`, others → `InvalidMessage` |
| Send caller | `rust/protocol/src/session_cipher.rs:37-43` | `message_encrypt` calls `pq_ratchet_send`; errors → `SignalProtocolError::InvalidState` |

**Ordering relative to outer authentication** (§11): In `decrypt_message_with_state`
(`session_cipher.rs:599-694`), the SPQR `recv` runs at line 633 — *after* Double-Ratchet
chain/message-key derivation (L624-632) but *before* the outer envelope MAC verification
(`ciphertext.verify_mac`, L657-661). A panic inside `spqr::recv` therefore fires before the
MAC check executes.

**Panic handling at the host boundary** (confirmed, not speculative):

| Bridge | Location (libsignal) | Mechanism |
|---|---|---|
| C FFI (iOS/Swift) | `rust/bridge/shared/types/src/ffi/mod.rs:399-413` | `run_ffi_safe` wraps every call in `std::panic::catch_unwind`; panics → `SignalFfiError::UnexpectedPanic` |
| JNI (Android) | `rust/bridge/shared/types/src/jni/mod.rs:1148-1157` | `run_ffi_safe` with `catch_unwind(AssertUnwindSafe(..))` |
| Node (Desktop) | `rust/bridge/shared/types/src/node/futures.rs:104-204` | `catch_unwind` on futures; Neon also catches panics |

All three bridges catch panics. The corrupted-blob defect surfaces in production as a
bridge-level `UnexpectedPanic` error (not a process abort), but the session remains
unrecoverable: libsignal has no code path that resets `pq_ratchet_state` on
`InvalidState`/`UnexpectedPanic`; only app-level session archival or deletion helps.

**Host-side validation**: The only libsignal inspections of `pq_ratchet_state` are
`is_empty()` (usability check, `session.rs:277`) and the opaque accessor `pq_ratchet_state()`
(`session.rs:619`). No semantic validation of the blob content exists at the host level.

---

## 3. Primary Defect: `ChainEpochDirection::from_pb`

**Source**: `src/chain.rs:306-312`

```rust
fn from_pb(pb: pqrpb::chain::epoch::EpochDirection) -> Result<Self, Error> {
    Ok(Self {
        ctr: pb.ctr,
        next: pb.next,
        prev: KeyHistory { data: pb.prev },
    })
}
```

**Zero validation is performed.** The function unconditionally returns `Ok` for any
protobuf-valid input. Yet three distinct downstream consumers require invariants that
`from_pb` never establishes:

| Field Condition | Required By | Spec Requiring It | Failure Mode |
|---|---|---|---|
| `next.is_empty() \|\| next.len() == 32` | `next_key_internal` (L228-244) | `NextKeyInternal.lean`: `h_next_len : next.length = 32` | **panic** (empty `next` is valid for cleared send directions but panics if reached) |
| `prev.data.len() % 36 == 0` | `KeyHistory::get` (L191) | `Get.lean`: `h_data_aligned : self.data.length % 36 = 0` | **panic** |
| `prev.data.len() ≤ 36 * ctr` | `KeyHistory::gc` (L149) | `Gc.lean`: `h_key_ge` + `Key.lean`: `h_prev_ctr` | **panic** |

---

## 4. Panic Path 1: `next_key_internal` — Length Mismatch

**Trigger**: `next.len() ≠ 32`

**Source**: `chain.rs:228-244`

```rust
fn next_key_internal(next: &mut [u8], ctr: &mut u32) -> (u32, [u8; 32]) {
    assert!(!next.is_empty());
    *ctr += 1;
    let mut genr8r = [0u8; 64];
    kdf::hkdf_to_slice(&[0u8; 32], &*next, /* ... */, &mut genr8r);
    next.copy_from_slice(&genr8r[..32]);  // ← PANICS if next.len() ≠ 32
    (*ctr, genr8r[32..].try_into().expect("correct size"))
}
```

`copy_from_slice` requires `self.len() == src.len()`. When `next.len() ≠ 32`, this is a
guaranteed panic.

**Call chain from `recv()`**:

```
recv() [lib.rs:356]
  → chain_from() [lib.rs:343]
    → Chain::from_pb() [chain.rs:434]
      → ChainEpochDirection::from_pb() [chain.rs:306]  // accepts any next.len()
  → chain.recv_key(epoch, index) [lib.rs:435]
    → links[idx].recv.key(index, params) [chain.rs:411]
      → next_key_internal() [chain.rs:293]  // PANIC
```

**Edge cases**:
- `next = vec![]`: hits `assert!(!next.is_empty())` at L229 — also a panic, not a graceful `Err`.
  **Note**: an empty `next` is *expected* and valid for send directions that have been cleared
  via `clear_next()` in `send_key()` (`chain.rs:396-399`). `clear_next()` is only ever
  called on `links[i].send` for `i < epoch_idx(send_epoch)`; a `recv.next` is **never**
  legitimately empty, and a `send.next` at or after the send epoch is never legitimately
  empty. The panic is triggered if a corrupted blob places an empty `next` on any such
  *active* direction. This asymmetry matters for the fix (§14.1/§14.2).
- `next = vec![0; 33]` or `vec![0; 31]`: `copy_from_slice` panics (length mismatch)

**Spec evidence**: `NextKeyInternal.lean` line 41:
```lean
theorem next_key_internal_spec (next : Slice U8) (ctr : U32)
    (h_next_len : next.length = 32)
    (h_ctr : ctr < U32.max) :
```

The `h_next_len` hypothesis is required but never established by `from_pb`.

**Mechanised** (`Spqr/Specs/Bugs/CorruptedBlobs.lean`): `next_key_internal_ok_lengths` shows
any `ok` result of `next_key_internal` forces `next.length = 32`; hence
`next_key_internal_never_ok : next.length ≠ 32 → ∀ r, next_key_internal next ctr ≠ ok r`.
This covers both the L229 `assert!` (empty) and the L243 `copy_from_slice` (wrong length)
cases. Reachability from `key` on the forward path (`ctr < at ≤ ctr + max_jump`) is
`key_never_ok_of_bad_next`; the helper `key_loop_preserves_next_length` shows the advancing
loop cannot repair a wrong-length `next`.


---

## 5. Panic Path 2: `KeyHistory::get` — Alignment Assertion

**Trigger**: `prev.data.len() % 36 ≠ 0`

**Source**: `chain.rs:191`

```rust
fn get(&mut self, at: u32, current_ctr: u32, params: &pqrpb::ChainParams,
) -> Result<Vec<u8>, Error> {
    assert_eq!(self.data.len() % Self::KEY_SIZE, 0);  // KEY_SIZE = 36, PANICS
    // ...
}
```

**Call chain**: `recv()` → `chain.recv_key()` → `key()` → `self.prev.get()` — panic at
`assert_eq!`.

**Corrupted blob example**: `pb.prev = vec![0; 37]` (not divisible by 36).

Even without the assertion, misaligned data would cause `self.data[i..i + 4]` slicing in the
loop at L197-202 to read across record boundaries, producing incorrect key material.

**Spec evidence**: `Get.lean` line 40: `(h_data_aligned : v.length % 36 = 0)`

**Mechanised** (`Spqr/Specs/Bugs/CorruptedBlobs.lean`):
`get_never_ok : data.length % 36 ≠ 0 → ∀ r, KeyHistory.get self at ctr params ≠ ok r`, and
reachability from `key` on the out-of-order path (`at < ctr`) is
`key_never_ok_of_misaligned_prev`.

---

## 6. Panic Path 3: `KeyHistory::gc` — Counter Underflow

**Trigger**: `prev.data` large, `ctr` small (specifically: `ctr < max_ooo_keys_or_default()`
when `data.len() >= trim_size() * KEY_SIZE`)

**Source**: `chain.rs:145-150`

```rust
fn gc(&mut self, current_key: u32, params: &pqrpb::ChainParams) {
    if self.data.len() >= params.trim_size() * Self::KEY_SIZE {
        assert!(current_key >= params.max_ooo_keys_or_default());  // PANICS
        let trim_horizon = &(current_key - params.max_ooo_keys_or_default()).to_be_bytes()[..];
        // ...
    }
}
```

The assertion guards against unsigned underflow in the subtraction. In normal operation,
`ctr ≥ max_ooo_keys_or_default()` by the time history is large enough for GC. A corrupted
blob can violate this: set `ctr = 0` with a large aligned `prev.data`.

**Call chain**: `recv()` → `recv_key()` → `key()` → `gc()` — panic at `assert!`.

**Trigger window**: `key(at, …)` only reaches `gc` on the forward path, and only if
`ctr < at ≤ ctr + max_ooo_keys`. If `at > ctr + max_ooo_keys`, `key` calls `prev.clear()`
first (`chain.rs:268`), the history becomes empty, and GC does **not** fire. The simplest
trigger is therefore the very next key, `at = ctr + 1`.

**Corrupted blob example** (default params: `max_ooo_keys = 2000`, `trim_size() = 2201`):
- `ctr = 0`, `prev.data = vec![0; 36 * 2201]` (79,236 bytes), request `at = 1`
- GC triggers → `assert!(0 >= 2000)` → **panic**

**Mechanised** (`Spqr/Specs/Bugs/CorruptedBlobs.lean`): `gc_never_ok` — with
`(maxOoo·11/10 + 1)·36 ≤ data.length` and `current_key < maxOoo`, `gc` has no `ok` result.
Reachability is `key_never_ok_of_large_prev_small_ctr` (hypothesis `at = ctr + 1`, which
proves the no-`clear` branch and the immediate loop exit). The end-to-end theorem
`restore_then_recv_panics_large_prev_small_ctr` uses exactly the example above
(`ctr = 0`, `prev.length ≥ 79236`, default `max_ooo_keys`, `at = 1`).

Note that `gc_never_ok`'s two hypotheses are precisely the negation of the
`prev.len() ≤ 36 · ctr` invariant proposed in §14.1: if that invariant holds and GC triggers,
then `36·(max_ooo·11/10 + 1) ≤ 36·ctr`, so `ctr > max_ooo` and the assertion is satisfied.

**Spec evidence**: `Gc.lean` lines 798-800:
```lean
(h_key_ge : let max_ooo := if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000
            let trim_threshold := (max_ooo * 11 / 10 + 1) * 36
            trim_threshold ≤ self.data.length → max_ooo ≤ current_key.val)
```


---

## 7. Secondary Defect: `Chain::from_pb`

**Source**: `src/chain.rs:434-452`

```rust
pub(crate) fn from_pb(pb: pqrpb::Chain) -> Result<Self, Error> {
    Ok(Self {
        dir: pb.direction.try_into().map_err(|_| Error::StateDecode)?,
        current_epoch: pb.current_epoch,
        send_epoch: pb.send_epoch,
        next_root: pb.next_root,       // ← no length check
        links: pb.links.into_iter().map(|link| { /* ... */ })
            .collect::<Result<VecDeque<_>, _>>()?,
        params: pb.params.ok_or(Error::StateDecode)?,
    })
}
```

Three additional unvalidated fields, plus the `params` object:

| Field | Required Invariant | Consumer | Failure |
|---|---|---|---|
| `next_root.len() ≠ 32` | `next_root.len() == 32` | `add_epoch` → `kdf::hkdf_to_slice` (L357-361) | No panic, but HKDF with wrong-length salt → peers silently derive different chain keys for the next epoch |
| `links.is_empty()` | `links.len() ≥ 1` | `epoch_idx` (L376-381): `back >= links` check | Graceful `Err(EpochOutOfRange)` — `back >= 0` is always true when `links == 0`, so the guard returns `Err` before the subtraction |
| `send_epoch > current_epoch` | `send_epoch ≤ current_epoch` | `send_key` (L385-406) | `send_key` returns `Err(EpochOutOfRange)` until `add_epoch` advances `current_epoch` to `≥ send_epoch`; a stall, not a permanent brick |
| `send.next` empty for `links[i]` with `i ≥ epoch_idx(send_epoch)` | only pre-send-epoch `send` directions may have empty `next` | `send_key` → `next_key` (L229) | Panic — this is the case §14.1 alone cannot catch (see §14.2) |
| `params.max_ooo_keys` ≥ 390451572 | `max_ooo_keys < 390451572` | `key()` (L262-264) via `hax_lib::assume!` | The `assume!` is not a runtime check — it tells hax the bound holds. An oversized value overflows the `ctr + max_ooo_keys` addition in `key()` (L265), causing incorrect GC / key-skip behaviour |
| `params.trim_size()` ≥ 119304647 | `trim_size() < 119304647` | `key()` (L280-283) via `hax_lib::assume!` | Same pattern — `assume!`d, not checked. Oversized `trim_size` disables GC, allowing unbounded `prev.data` growth |

The `next_root` case is particularly insidious: it does not panic — it silently produces
incorrect derived keys. Note that SPQR itself would still return `Ok` from `send()`/`recv()`:
`next_root` feeds the epoch-secret KDF, and the resulting chain keys are handed to the
*outer* Double Ratchet as `Send.key`/`Recv.key`. The divergence therefore surfaces as a
decryption failure at the Signal layer, **not** as SPQR's `InvalidCtMac` (the `Authenticator`
keys are derived from the epoch secret independently of `next_root`). This makes it harder
to attribute to SPQR state corruption.

**Mechanised** (`Spqr/Specs/Bugs/CorruptedBlobs.lean`, Phase 7):
`chain_from_pb_admits_wrong_next_root : pb.next_root.length ≠ 32 → Chain.from_pb pb = ok (Ok c)
→ c.next_root.length ≠ 32` — `Chain::from_pb` passes `next_root` through on every success
path. The proof case-splits the Aeneas translation of the `?` early returns (the
`core::convert::Infallible` arms are vacuous).

**Not mechanised**: the remaining rows of the table above — `send_epoch > current_epoch`, the
position-dependent `send.next` emptiness, and the `params` range assumptions — have no Lean
witness and rest on code reading only.

---

## 8. Tertiary Defect: `Authenticator::from_pb`

**Source**: `src/authenticator/serialize.rs:16-21`

```rust
pub fn from_pb(pb: &proto::pq_ratchet::Authenticator) -> Self {
    Self {
        root_key: pb.root_key.clone(),   // ← no length check
        mac_key: pb.mac_key.clone(),     // ← no length check
    }
}
```

`Authenticator::new` always produces 32-byte keys via HKDF (L51-53). `from_pb` accepts
arbitrary-length keys:

- **`mac_key = vec![]`**: HMAC-SHA256 handles any key length (no panic), but the
  authenticator produces tags derived from a non-standard-length key. Note: an attacker who
  can set `mac_key = []` in the local database can equally set it to any known 32-byte value,
  so the length check only helps against *non-adversarial corruption*, not a malicious local
  attacker.
- **`root_key = vec![]`**: weakens forward secrecy of the authenticator chain.

**Severity**: LOW. No panic; the length check is a robustness/defense-in-depth measure
against corruption, not a security boundary against a local attacker.

**Note**: Return type is `Self` (infallible). Fix requires changing to `Result<Self, Error>`
and updating all 9 call sites in `src/v1/unchunked/send_ct/serialize.rs` and
`src/v1/unchunked/send_ek/serialize.rs`.

**Mechanised** (`Spqr/Specs/Bugs/CorruptedBlobs.lean`, Phase 6):
`authenticator_from_pb_no_validation` (fields copied verbatim, no `Err` branch),
`authenticator_from_pb_admits_empty_mac_key`, `authenticator_from_pb_admits_empty_root_key`,
and `authenticator_from_pb_admits_wrong_key_lengths` (both keys of any length ≠ 32 accepted).

---

## 9. Quaternary Defect: `PolyDecoder::from_pb`

**Source**: `src/encoding/polynomial.rs:815-853`

`PolyDecoder::from_pb` validates `pb.pts.len() == 16` and each slot's length mod 4, but
does **not** validate:

- Individual slot sizes against `2 * MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1 = 71`
- The `is_complete` flag (a blob with `is_complete = true` makes `decoded_message()` return
  `None` forever, silently stalling the epoch — see Finding 5 in `report.md`)

**Note on `pts_needed`**: while `from_pb` itself does not check `pts_needed` against the V1
maximum (576), every V1 call site validates `pts_needed` exactly against the expected value
(e.g., `ENCAPSULATION_KEY_SIZE / 2`, `CIPHERTEXT1_SIZE / 2`, `(CIPHERTEXT2_SIZE + MACSIZE) / 2`
in `src/v1/chunked/send_ct/serialize.rs` and `src/v1/chunked/send_ek/serialize.rs`). A
defense-in-depth check inside `from_pb` would still be reasonable but is not strictly necessary.

**Severity**: LOW-MEDIUM. Silent stall possible via `is_complete`; no immediate panic.

**Mechanised** (`Spqr/Specs/Bugs/CorruptedBlobs.lean`, Phase 8):
`poly_decoder_from_pb_admits_premature_is_complete` — for any protobuf with 16 `%4`-aligned
slots and `is_complete = true`, `from_pb` returns `Ok` with `is_complete = true`; and
`poly_decoder_from_pb_admits_stalled_decoder` — with all 16 slots *empty*, `from_pb` still
returns `Ok` with `is_complete = true` and every point set `= []`, i.e. the permanently
stalled decoder of Finding 5.

**Not mechanised**: the per-slot size bound (`> 2 * MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1`).
`Spqr/Specs/Bugs/ProtocolDoS.lean` separately proves that *poisoned* decoder state
round-trips through `PolyDecoder::into_pb`/`from_pb` (Finding 2). The related
`PolyEncoder::from_pb` (`polynomial.rs:573`) likewise validates only `pts.len() == 16` and
per-slot `% 2`, not slot size; it is out of scope for this study but shares the pattern.


---

## 10. Lean Specification Evidence

The formal specifications mechanically expose the validation gap:

### 10.1. `FromPb.lean` — Always Succeeds, No Validation

```lean
-- Spqr/Specs/Chain/ChainEpochDirection/FromPb.lean
theorem from_pb_spec (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result) =>
      match result with
      | .Ok ced => ced.ctr = pb.ctr ∧ ced.next = pb.next ∧ ced.prev = { data := pb.prev }
      | .Err _ => False ⦄
```

The `Err` branch maps to `False` — the spec **proves** `from_pb` never errors. The `Ok`
branch establishes only field-copying equalities, no structural invariants.

### 10.2. Downstream Specs Require What `from_pb` Does Not Establish

| Spec File | Required Hypothesis | What It Guards |
|---|---|---|
| `NextKeyInternal.lean` | `h_next_len : next.length = 32` | `copy_from_slice` safety |
| `Get.lean` | `h_data_aligned : v.length % 36 = 0` | Record alignment |
| `Gc.lean` | `h_key_ge : … max_ooo ≤ current_key.val` | Subtraction underflow |
| `Key.lean` | `h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val` | GC precondition |
| `Key.lean` | `h_ctr_bound : self.ctr.val ≤ U32.max - 390451572` | Counter range (see also `Key32.lean` which uses `U32.max - 108458770`) |

**Note**: `h_ooo_no_overflow : at1 + maxOoo ≤ U32.max` (from `Get.lean` and `Key32.lean`) is
omitted from the table above because `at` comes from the *message* (`index` parameter), not
from the persisted blob. `from_pb` cannot establish this hypothesis; it belongs to the
message-validation path (see Finding 4 in `report.md`).

**The gap**: `from_pb_spec` outputs go directly into these consumers, but establishes
none of their preconditions. The spec theorems are provable only because the hypotheses
are carried as assumptions — they are never discharged from `from_pb`.

### 10.3. Provability Implications

An end-to-end theorem like:

```lean
theorem recv_after_restore_safe (blob : PqRatchetState) :
    ∀ msg, recv (from_pb blob) msg ≠ panic
```

is **unprovable** in the current spec framework — the desired property cannot be proved
because the code does not have it. §10.4 goes further and proves its **negation** for the
concrete scenarios.

### 10.4. Mechanised Bug Proofs — `Spqr/Specs/Bugs/CorruptedBlobs.lean`

The preceding subsections show only that the consumer specs *carry* unestablished
hypotheses. `Spqr/Specs/Bugs/CorruptedBlobs.lean` (builds cleanly with `lake build
Spqr.Specs.Bugs.CorruptedBlobs`; no `sorry` in the file) proves the stronger negative
result: on corrupted input the consumers have **no `ok` execution at all**, which in the
Aeneas model is exactly a Rust `panic!`/`assert!`. The development is in nine phases:

| Phase | Theorem(s) | Statement | Report § |
|---|---|---|---|
| 1 | `from_pb_never_fails` | `Err ⇒ False`; `ctr`/`next`/`prev` copied verbatim | §3 |
| 2a | `from_pb_admits_wrong_next_length`, `_misaligned_prev`, `_large_prev_small_ctr`, `_triple_violation` | Each consumer precondition can be violated by a `from_pb` output | §3 |
| 2b | `next_key_internal_never_ok` | `next.length ≠ 32 → ∀ r, next_key_internal … ≠ ok r` (L229 + L243) | §4 |
| 2b | `get_never_ok` | `data.length % 36 ≠ 0 → ∀ r, get … ≠ ok r` (L191) | §5 |
| 2b | `gc_never_ok` | `trim threshold ≤ data.length ∧ ctr < maxOoo → ∀ r, gc … ≠ ok r` (L149) | §6 |
| 3 | `key_never_ok_of_bad_next` / `_of_misaligned_prev` / `_of_large_prev_small_ctr` | Each panic is reached from `ChainEpochDirection::key` on its natural path (forward / OOO / `at = ctr+1`) | §4–6 |
| 4 | `restore_then_recv_panics_bad_next` / `_misaligned_prev` / `_large_prev_small_ctr` | `from_pb pb = Ok ced → ∀ r, key ced at params ≠ ok r` — the negation of `recv_after_restore_safe` | §12.1, §12.3, §12.4 |
| 5 | `corrupted_state_roundtrips` | `into_pb (from_pb pb) = pb` — corruption is written back unchanged (crash loop) | §13 |
| 6 | `authenticator_from_pb_admits_*` | `Authenticator::from_pb` is infallible and accepts any key length | §8 |
| 7 | `chain_from_pb_admits_wrong_next_root` | `Chain::from_pb` copies `next_root` verbatim: `pb.next_root.length ≠ 32 → c.next_root.length ≠ 32` | §7, §12.2 |
| 8 | `poly_decoder_from_pb_admits_premature_is_complete`, `_stalled_decoder` | `PolyDecoder::from_pb` copies `is_complete` verbatim, even with all point sets empty | §9 |
| 9 | `recvKeyPre_unsatisfiable_bad_next` / `_misaligned_prev` / `_large_prev_small_ctr` | The `recv_key_spec` precondition `recvKeyPre` is **unsatisfiable** on a corrupted `recv` direction | §10.2 |

**Scope of Phase 9**: it proves only that the *spec's* precondition cannot be met, i.e. that
`recv_key_spec` does not apply to corrupted state.

**Phase 10** (`recv_key_never_ok_of_key_never_ok`, `recv_key_never_ok_bad_next`,
`recv_key_never_ok_misaligned_prev`, `recv_key_never_ok_large_prev_small_ctr`): proves the
stronger `∀ r, recv_key … ≠ ok r` by composing `epoch_idx` success with the Phase 3
`key_never_ok_*` results — the full reachability lift through `Chain::recv_key`.

**What is *not* mechanised**:

- The non-`next_root` rows of §7 (`send_epoch` ordering, position-dependent `send.next`,
  `params` ranges) and the slot-size bound of §9.
- **Sufficiency of the fixes in §14** — the Lean file proves panics exist, not that the
  proposed checks remove them. In particular, `next_key_internal_never_ok` fires for
  `next.length = 0` as well, which is why §14.1's uniform `{0, 32}` acceptance is
  insufficient on its own (see §14.2).

---

## 11. Comparison with Finding 2 (Chunk Poisoning)

| Dimension | Finding 2 (Chunk Poisoning) | This Study (Corrupted Blobs) |
|---|---|---|
| **Attack vector** | Network message | Local storage |
| **Entry point** | `Message::deserialize` → `add_chunk` | `decode_state` → `from_pb` |
| **What gets corrupted** | Decoder point sets | Chain / authenticator / decoder state |
| **Failure mode** | Permanent epoch stall (`Err` loop) | Panic (unrecoverable inside SPQR) |
| **Integration mitigation** | Signal MAC auth-before-commit | **None inside SPQR**; host catches panics as `UnexpectedPanic` at FFI boundary (§2.1) but session is unrecoverable |
| **Is it a library bug?** | Yes | Yes |
| **Is it exploitable in V1?** | No (mitigated) | **Yes** (no mitigation inside SPQR) |
| **Severity in practice** | LOW (in deployed V1) | **MEDIUM** (in deployed V1) |
| **Mechanised proof** | `Spqr/Specs/Bugs/ProtocolDoS.lean` | `Spqr/Specs/Bugs/CorruptedBlobs.lean` (§10.4) |

**Why network authentication does not help**: The integration's auth-before-commit pattern
operates at the *message processing* level:

```
1. Load persisted state ← CORRUPTED BLOB LOADED HERE
   ↳ Chain::from_pb() accepts invalid invariants
2. Process SPQR message against corrupted state
   ↳ recv_key() → key() → next_key_internal() / get() / gc()
   ↳ PANIC — bridge-level `UnexpectedPanic` error (not a process abort; see §2.1);
       session remains unrecoverable. The panic fires before the outer Signal envelope
       MAC check (`ciphertext.verify_mac`, `session_cipher.rs:657-661`)
      (SPQR-internal authenticator checks may have already run via States::from_pb(pb)?.recv(),
       but the outer envelope MAC that the integration relies on has not)
3. (Never reached) Verify outer Signal envelope MAC (`ciphertext.verify_mac`, `session_cipher.rs:657`)
```

The MAC check never executes because SPQR panics at step 2. The commit that matters
already happened (when the corrupted blob was written to storage).


---

## 12. Attack Scenarios

> **Note**: The scenarios below are illustrative and assume an attacker with write access to the
> decrypted local session database. In most messenger threat models (including Signal's), local
> storage is trusted — an attacker with this capability can already delete the session, exfiltrate
> ratchet keys, or replace the entire blob. The `from_pb` validation fixes are primarily valuable
> for **non-adversarial robustness** (bit-rot, truncated writes, backup/restore bugs), not for
> defending against a local attacker.

### 12.1. Targeted Session Kill via Backup Modification

**Attacker model**: Access to the encrypted backup store (cloud backup with compromised
credentials, or physical access to device storage).

1. Locate the SPQR state blob in the backup/database.
2. Decode as protobuf (schema is public in the SPQR repo).
3. Replace `chain.links[0].recv.next` with `[0]` (1 byte instead of 32).
4. Re-encode and write back.
5. Victim restores the backup.
6. First incoming message with `index` in `(ctr, ctr + max_jump]` triggers
   `recv()` → `recv_key()` → `next_key_internal()` → **panic**.

**Result**: Session permanently bricked. Every restart loads the corrupted state and panics.

**Mechanised**: `restore_then_recv_panics_bad_next` (hypotheses `pb.next.length ≠ 32`,
`ced.ctr < at ≤ ced.ctr + maxJump`) plus `corrupted_state_roundtrips` for the crash loop.

### 12.2. Silent Key Divergence via `next_root` Truncation

1. Modify `chain.next_root` to `[0; 16]` (16 bytes instead of 32).
2. Victim restores and continues the session.
3. `add_epoch()` uses 16-byte `next_root` as HKDF salt → different chain keys than peer.
4. SPQR's `send()`/`recv()` continue to return `Ok` with wrong key material; the outer
   Double Ratchet fails to decrypt. Because the failure is at the Signal layer rather than a
   `StateDecode` (or even `InvalidCtMac`) from SPQR, the cause is obscured.

**Result**: Session silently diverges from the next epoch onward. Neither party can
communicate.

**Mechanised** (partially): `chain_from_pb_admits_wrong_next_root` (Phase 7) shows the
16-byte `next_root` survives `Chain::from_pb` unchanged. The downstream divergence in
`add_epoch` is not mechanised.

### 12.3. One-Byte DoS via Alignment Violation

1. Append a single byte to any `chain.links[i].recv.prev` field (e.g., 36 → 37 bytes).
2. Next out-of-order `recv()` (`index < ctr`) → `KeyHistory::get()` →
   `assert_eq!(37 % 36, 0)` → **panic**.

**Result**: Minimal modification (1 byte) permanently crashes the session.

**Mechanised**: `restore_then_recv_panics_misaligned_prev` (hypotheses
`pb.prev.length % 36 ≠ 0`, `at < ced.ctr`).

### 12.4. GC Panic via Counter/History Mismatch

1. Set `chain.links[i].recv.ctr = 0`.
2. Set `chain.links[i].recv.prev = vec![0; 36 * 2201]` (79,236 bytes; large enough to
   trigger GC under default `max_ooo_keys = 2000`).
3. Next `recv()` with `index = 1` (generally `ctr < index ≤ ctr + max_ooo_keys`, so that
   `prev.clear()` is not taken first) → `key()` → `gc()` → `assert!(0 >= 2000)` → **panic**.

**Mechanised**: `restore_then_recv_panics_large_prev_small_ctr` (hypotheses `pb.ctr = 0`,
`pb.prev.length ≥ 79236`, `params.max_ooo_keys = 0` i.e. default, `at = 1`).

---

## 13. Impact Assessment

### Severity: MEDIUM

- **Availability**: Panics surface as bridge-level `UnexpectedPanic` errors (§2.1). With persisted corruption, the session is
  permanently bricked — every restart loads the same corrupted state and panics again.
- **No graceful degradation**: Failures are `panic!`/`assert!` crashes, not `Err` returns.
  The caller has no opportunity to handle the error, log diagnostics, or attempt recovery.
- **No mitigation inside SPQR**: The host integration catches panics at the FFI boundary
  via `run_ffi_safe`/`catch_unwind` (§2.1), but SPQR itself provides no graceful error path.
- **Primary threat is non-adversarial**: Storage corruption, truncated writes, backup/restore
  bugs, and schema skew are the realistic scenarios. A malicious local attacker who can modify
  the decrypted session database has far more powerful attacks available than triggering a panic.

### Blast Radius

A single `PqRatchetState` blob has multiple distinct fields whose corruption leads
to panics, silent divergence, or permanent stalls:

- Each `ChainEpochDirection`: 3 panic paths (sections 4-6) — `next`, `prev` data, `ctr`
- Each `ChainEpoch`: up to 6 paths (send + recv directions)
- `Chain` level: `next_root` (silent divergence surfacing at the Signal layer),
  `send_epoch > current_epoch` (send failure until `current_epoch` catches up), empty
  `send.next` at/after the send epoch (panic in `next_key`). Note: `links.is_empty()` returns
  a graceful `Err(EpochOutOfRange)`, not a panic.
- `Authenticator`: 2 semantic failure modes — `root_key`, `mac_key` (section 8)
- `PolyDecoder`: slot sizes + `is_complete` stall (section 9)


---

## 14. Recommended Fixes

### 14.1. `ChainEpochDirection::from_pb` (Primary)

`ChainEpochDirection::from_pb` does not know whether it is building a `send` or `recv`
direction, nor its link index, so it can only enforce the *weak* `next` invariant here. The
strong, position-dependent `next` check lives in `Chain::from_pb` (§14.2).

```rust
fn from_pb(pb: pqrpb::chain::epoch::EpochDirection) -> Result<Self, Error> {
    // Weak check: next is either empty (a send direction cleared via clear_next()) or
    // exactly 32 bytes. Chain::from_pb tightens this per direction/position.
    if !(pb.next.is_empty() || pb.next.len() == 32) { return Err(Error::StateDecode); }
    // h_data_aligned (Get.lean / Gc.lean)
    if pb.prev.len() % 36 != 0 { return Err(Error::StateDecode); }
    // h_prev_ctr (Key.lean): prev.len() <= 36 * ctr. Sufficient for gc's assert: if GC
    // triggers then 36*(max_ooo*11/10+1) <= prev.len() <= 36*ctr, so ctr > max_ooo.
    if pb.prev.len() / 36 > pb.ctr as usize { return Err(Error::StateDecode); }
    Ok(Self { ctr: pb.ctr, next: pb.next, prev: KeyHistory { data: pb.prev } })
}
```

Establishes: `h_data_aligned` ✓, `h_prev_ctr` ✓ (and therefore `h_key_ge` ✓), and the weak
form `next.length = 0 ∨ next.length = 32`.

**This alone is insufficient for `h_next_len`.** `next_key_internal_never_ok` (§10.4) fires
for `next.length = 0` too, so a blob with an empty `next` on a `recv` direction, or on a
`send` direction at/after the send epoch, still panics at `chain.rs:229` after this fix.

### 14.1a. `ChainParams` range check (addition to `Chain::from_pb`)

`Chain::from_pb` accepts `params` (`chain.rs:450`) without any range check. The downstream
`key()` function relies on `hax_lib::assume!` (`chain.rs:262-264`, `280-283`) that
`max_ooo_keys_or_default() < 390451572` and `trim_size() < 119304647`. These are proof
obligations, **not** runtime checks. A blob with `max_ooo_keys = u32::MAX` causes wrapping
arithmetic in `ctr + max_ooo_keys` (L265), and an oversized `trim_size` disables GC.

Recommended: add to `Chain::from_pb`:

```rust
let params = pb.params.ok_or(Error::StateDecode)?;
if params.max_ooo_keys_or_default() >= 390451572 { return Err(Error::StateDecode); }
if params.trim_size() >= 119304647 { return Err(Error::StateDecode); }
```

### 14.2. `Chain::from_pb` (Secondary — completes the `next` check)

```rust
pub(crate) fn from_pb(pb: pqrpb::Chain) -> Result<Self, Error> {
    if pb.next_root.len() != 32 { return Err(Error::StateDecode); }
    if pb.send_epoch > pb.current_epoch { return Err(Error::StateDecode); }
    // ... existing direction/links/params parsing into `links: VecDeque<ChainEpoch>` ...
    // Note: links.is_empty() is handled gracefully by epoch_idx() which returns
    // Err(EpochOutOfRange) when back >= links.len(), so no explicit check is needed here.

    // Strong `next` check, position-aware:
    //   - recv.next is never legitimately empty.
    //   - send.next may be empty only for links[i] with i < send_idx (cleared by
    //     clear_next() in send_key()); at or after the send epoch it must be 32 bytes.
    // Mirrors epoch_idx(send_epoch): links.back() holds current_epoch.
    let back = (pb.current_epoch - pb.send_epoch) as usize;  // safe: checked above
    if back >= links.len() { return Err(Error::StateDecode); } // send epoch already dropped
    let send_idx = links.len() - 1 - back;
    for (i, link) in links.iter().enumerate() {
        if link.recv.next.len() != 32 { return Err(Error::StateDecode); }
        if i >= send_idx && link.send.next.len() != 32 { return Err(Error::StateDecode); }
    }
    // ...
}
```

(The `send_idx` computation mirrors `epoch_idx` at `chain.rs:372-382`. Since `links` is
always populated by construction and `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH` bounds how far the
send epoch can trail `links.back()`, the `back >= links.len()` guard also rejects blobs whose
`send_epoch` refers to an already-dropped link.) With this, `h_next_len : next.length = 32`
holds **unconditionally** for every direction that `send_key`/`recv_key` can actually reach.

### 14.3. `Authenticator::from_pb` (Tertiary)

Change return type to `Result<Self, Error>`:

```rust
pub fn from_pb(pb: &proto::pq_ratchet::Authenticator) -> Result<Self, Error> {
    if pb.root_key.len() != 32 || pb.mac_key.len() != 32 {
        return Err(Error::StateDecode);
    }
    Ok(Self { root_key: pb.root_key.clone(), mac_key: pb.mac_key.clone() })
}
```

Update 9 call sites in `src/v1/unchunked/send_ct/serialize.rs` and
`src/v1/unchunked/send_ek/serialize.rs`.

### 14.4. `PolyDecoder::from_pb` (Quaternary)

```rust
for slot in &pb.pts {
    if slot.len() / 4 > 2 * MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1 {
        return Err(PolynomialError::SerializationInvalid);
    }
}
```

Note: a `pts_needed` bounds check is not strictly necessary here because every V1 call site
already validates `pts_needed` exactly against the expected protocol constant. A
defense-in-depth check could be added but is optional.

### 14.5. Lean Specification Updates

After implementing fixes:

1. **Update `FromPb.lean`**: the `Err` branch should no longer map to `False` but to
   concrete error conditions matching the new validation checks (the `Ok` branch gains
   `ced.prev.data.length % 36 = 0`, `ced.prev.data.length ≤ 36 * ced.ctr.val`, and
   `ced.next.length = 0 ∨ ced.next.length = 32`).
2. **`h_data_aligned`, `h_prev_ctr`** (and hence `h_key_ge`) become **provable invariants**
   from `ChainEpochDirection::from_pb` alone.
3. **`h_next_len : next.length = 32`** becomes provable **unconditionally** for `recv`
   directions and for `send` directions at index `≥ send_idx`, but only from a
   `Chain::from_pb` spec (§14.2) — not from `ChainEpochDirection::from_pb`, which can only
   provide the disjunction. `NextKeyInternal.lean` needs the `= 32` form, so the end-to-end
   argument must go through `Chain::from_pb`.
4. **`Spqr/Specs/Bugs/CorruptedBlobs.lean` becomes a regression oracle**: after the fix,
   `from_pb_never_fails` and the `restore_then_recv_panics_*` theorems must *fail to
   type-check* (their `h_load : from_pb pb = ok (Ok ced)` hypothesis becomes unsatisfiable
   for the corrupted `pb`). Retarget them as positive theorems
   (`from_pb pb = ok (Err StateDecode)` for each witness) rather than deleting them.
   Likewise `chain_from_pb_admits_wrong_next_root` (Phase 7) becomes vacuous once §14.2's
   `next_root.len() != 32` check lands, and `authenticator_from_pb_*` (Phase 6) once §14.3's
   return type changes; retarget both the same way. The Phase 8 `PolyDecoder` witnesses
   are unaffected by §14.4 as written (that fix does not touch `is_complete`).
5. An end-to-end `recv_after_restore_safe` theorem (the positive counterpart of Phase 4)
   becomes provable.

### 14.6. Defense-in-Depth: Replace `assert!` with `Err`

Even after `from_pb` validation, convert the downstream `assert!`/`assert_eq!` at L149,
L191, L229 to return `Err(Error::InternalInvariantViolation)` (new error variant) rather
than panicking. This guards against any future code path constructing a
`ChainEpochDirection` without going through `from_pb`.

Split by effort:

- **Cheap now**: `KeyHistory::get` (L191) already returns `Result<Vec<u8>, Error>`, so its
  `assert_eq!` can become `return Err(...)` with no signature change.
- **Requires signature changes**: `KeyHistory::gc` returns `()` and `next_key_internal`
  returns `(u32, [u8; 32])`. Converting their asserts to `Err` changes `key()`'s and
  `next_key()`'s call chains, the hax preconditions, and the `Gc.lean` /
  `NextKeyInternal.lean` specs. Plan carefully.

**Note**: adding `Error::InternalInvariantViolation` is a public API change to `spqr::Error`.

**Recommended additional tests**:

1. A proptest that round-trips `Chain::into_pb` → `from_pb` on states that have gone
   through `send_key` across multiple epochs, to guard against the regression where valid
   empty-`next` directions (pre-send-epoch `send`) are rejected by §14.2.
2. A concrete Rust repro for each of §12.1/§12.3/§12.4 (mirroring the Lean
   `restore_then_recv_panics_*` theorems): build a `Chain`, `into_pb()`, mutate the field,
   `from_pb()`, and assert that `recv_key` **returns `Err(StateDecode)`** after the fix
   (before the fix, wrap in `std::panic::catch_unwind` and assert it panics). Consider
   committing the pre-fix version as `docs/corrupted_blob_counterexample.rs.txt` alongside
   the other counterexample files in `docs/`.

---

## 15. Summary

| Component | Defect | Failure Mode | Severity | Integration Mitigation? | Mechanised? |
|---|---|---|---|---|---|
| `ChainEpochDirection::from_pb` | No validation of `next.len()`, `prev` alignment/size | Panic (3 paths) | **MEDIUM** | None inside SPQR; host catches panics as `UnexpectedPanic` (§2.1) | **Yes** — `CorruptedBlobs.lean` Phases 1–5 |
| `Chain::from_pb` | No validation of `next_root.len()`, epoch ordering, position-dependent `send.next` | Silent divergence (Signal layer) / send stall / panic | **MEDIUM** | None inside SPQR | **Partial** — Phase 7 (`next_root` only) |
| `Authenticator::from_pb` | No validation of key lengths | Non-standard-length keys weaken MAC properties | LOW | None inside SPQR | **Yes** — Phase 6 |
| `PolyDecoder::from_pb` | No bounds on slot sizes, `is_complete` | Silent stall | LOW-MEDIUM | None inside SPQR | **Partial** — Phase 8 (`is_complete` only) |

**Key conclusion**: This is a **real robustness defect in the deployed V1 protocol**. Unlike
Finding 2 (chunk poisoning), which is mitigated by the upstream integration's
authentication-before-commit pattern, the corrupted-blob class operates at the state-loading
level where no authentication boundary exists. Any corruption of the persisted state blob —
from disk errors, backup issues, or schema skew — can crash or silently brick an SPQR session
with no graceful recovery path *inside SPQR itself*. The host integration catches panics at
the FFI boundary via `run_ffi_safe`/`catch_unwind` (§2.1), but this is defense-in-depth, not a substitute for proper error returns.

The fix is straightforward: validate semantic invariants in every `from_pb` function,
converting assumed preconditions into checked postconditions — with the one subtlety that
the `next.len() == 32` check must be made in `Chain::from_pb`, where direction and epoch
position are known (§14.1–14.2). This simultaneously fixes the Rust code and makes the Lean
specification's structural hypotheses provable invariants; the negative theorems in
`Spqr/Specs/Bugs/CorruptedBlobs.lean` then serve as a regression oracle (§14.5).
