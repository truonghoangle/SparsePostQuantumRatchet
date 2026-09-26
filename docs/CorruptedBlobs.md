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

**Revision note (2026‑09‑26)**: this report was independently reviewed in
`docs/evaluateSPQR.md`. That review confirmed every panic site and failure-mode
classification below against `src/chain.rs` and `Spqr/Specs/**`, executed 14 compiled-Rust
probes in both debug and release profiles, and identified fourteen residual gaps (G1–G14).
This revision folds the resulting corrections into the report: a previously unanalysed `ctr`
range invariant (§3, §14.1), a fourth panic site in `KeyHistory::gc` at `chain.rs:157`
(§5a), the debug/release dependence of the arithmetic-overflow cases (§7), a corrected
consequence for the `PolyDecoder` slot-size bound (§9), a runtime-evidence section (§10.5),
a three-way split of the "crash loop" persistence claim (§13), and an invariant → fix
traceability table (§14.7).

**Mechanised evidence**: the primary defect (§§3–6) and its reachability from `recv()`
(§12.1, §12.3, §12.4) are machine-checked in
`Spqr/Specs/Bugs/CorruptedBlobs.lean`, which proves the *negative* form of the desired safety
property: for each scenario, `from_pb pb = Ok ced → ∀ r, key ced at params ≠ ok r` (no
successful execution exists — the Aeneas model of a Rust panic). See §10.4. The secondary
defects also have Lean witnesses: `Chain::from_pb` copies `next_root` verbatim (§7, Phase 7),
`PolyDecoder::from_pb` copies `is_complete` verbatim (§9, Phase 8), and the `recv_key` spec
precondition is unsatisfiable on corrupted `recv` directions (§10.4, Phase 9). The remaining
§7 `Chain`-level cases (`send_epoch` ordering, position-dependent `send.next`, `params`
ranges), the `ctr` range (§3) and the §9 slot-size bound have **no Lean witness**, but every
panic-class case — including the position-dependent `send.next` route through `send_key` —
has now been **confirmed at runtime** with compiled probes (§10.5, source preserved in
`docs/corrupted_blob_counterexample.rs.txt`).

---

## Table of Contents

1. [Threat Model](#1-threat-model)
2. [Architectural Context](#2-architectural-context-the-persistence-boundary)
   - 2.1. [Production Load Path (libsignal → spqr)](#21-production-load-path-libsignal--spqr)
3. [Primary Defect: `ChainEpochDirection::from_pb`](#3-primary-defect-chainepochdirectionfrom_pb)
4. [Panic Path 1: `next_key_internal`](#4-panic-path-1-next_key_internal--length-mismatch)
5. [Panic Path 2: `KeyHistory::get`](#5-panic-path-2-keyhistoryget--alignment-assertion)
   - 5a. [Panic Path 2b: `KeyHistory::gc` slice index](#5a-panic-path-2b-keyhistorygc--slice-index-on-misaligned-history)
6. [Panic Path 3: `KeyHistory::gc`](#6-panic-path-3-keyhistorygc--counter-underflow)
7. [Secondary Defect: `Chain::from_pb`](#7-secondary-defect-chainfrom_pb)
8. [Tertiary Defect: `Authenticator::from_pb`](#8-tertiary-defect-authenticatorfrom_pb)
9. [Quaternary Defect: `PolyDecoder::from_pb`](#9-quaternary-defect-polydecoderfrom_pb)
10. [Lean Specification Evidence](#10-lean-specification-evidence)
    - 10.5. [Runtime Evidence — Compiled-Rust Probes](#105-runtime-evidence--compiled-rust-probes)
11. [Why Network Authentication Does Not Help](#11-comparison-with-finding-2-chunk-poisoning)
12. [Attack Scenarios](#12-attack-scenarios)
13. [Impact Assessment](#13-impact-assessment)
    - [Persistence: Three Senses](#persistence-three-senses-in-which-the-corruption-survives)
14. [Recommended Fixes](#14-recommended-fixes)
    - 14.7. [Invariant → Fix Traceability](#147-invariant--fix-traceability)
15. [Summary](#15-summary)
16. [Remote Attack Analysis](#16-analysis-can-a-remote-network-attack-cause-an-attacker-controlled-spqr-invalid-value-to-be-persisted-in-the-protobuf-state-subsequently-consumed-by-from_pb-without-requiring-local-or-storage-layer-access)
    - 16.7. [Counterexample: `ctr` Steering](#167-counterexample-malicious-authenticated-peer-drives-ctr-past-h_ctr_bound)
    - 16.8. [Recommended Fix for `ctr` Steering](#168-recommended-additional-fix-for-ctr-steering)


---

## 1. Threat Model

The corrupted-blob threat model differs fundamentally from the network-message threat model:

| Property | Network Message (Finding 2) | Corrupted Blob (This Study) |
|---|---|---|
| **Entry point** | `Message::deserialize` (wire) | `decode_state` → `from_pb` (storage) |
| **Authentication** | Signal envelope MAC covers payload | None — blob is trusted once loaded |
| **Attacker capability** | Forge/replay network messages | Modify local storage (disk, backup, cloud sync) |
| **Integration mitigation** | Auth-before-commit blocks poisoning | **None inside SPQR** — `from_pb` runs at load time, pre-auth; host catches panics as `UnexpectedPanic` (§2.1) but session is unrecoverable |
| **Failure mode** | Permanent epoch stall | Panic on the §§4–6 paths (unrecoverable inside SPQR; crash loop on reload — §13); graceful `Err` for epoch ordering; `Ok`-with-wrong-semantics for `next_root`/`Authenticator`/`PolyDecoder`; profile-dependent for arithmetic overflow (§10.5 taxonomy) |

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
protobuf-valid input. Yet the downstream consumers require four invariants that
`from_pb` never establishes:

| Field Condition | Required By | Spec Requiring It | Failure Mode |
|---|---|---|---|
| `next.is_empty() \|\| next.len() == 32` | `next_key_internal` (L228-244) | `NextKeyInternal.lean`: `h_next_len : next.length = 32` | **panic** — `next = []` → `assert!` at L229; `0 < next.len() ≠ 32` → `copy_from_slice` at L243 (empty `next` is valid for cleared send directions but panics if reached) |
| `prev.data.len() % 36 == 0` | `KeyHistory::get` (L191); `KeyHistory::gc` (L157) | `Get.lean`: `h_data_aligned : self.data.length % 36 = 0`; `Gc.lean:85`: `h_data_aligned` | **panic** — `assert_eq!` at L191 on the out-of-order path; slice index at L157 on the forward path once `prev` reaches the GC threshold (§5a) |
| `prev.data.len() ≤ 36 * ctr` | `KeyHistory::gc` (L149) | `Gc.lean`: `h_key_ge` + `Key.lean`: `h_prev_ctr` | **panic** |
| `ctr ≤ u32::MAX − 390451572` | `key()` (L262-265, L275-279): `self.ctr + params.max_ooo_keys_or_default()` | `Key.lean`: `h_ctr_bound : self.ctr.val ≤ U32.max - 390451572` (`Key32.lean` uses `U32.max - 108458770`) | **debug/test builds: panic** (`attempt to add with overflow` at L265); **release builds: silent wrap** → `Ok` with a wrong `prev.clear()` / `add` decision. `Cargo.toml` sets no `overflow-checks` override, so libsignal release builds wrap. |

The `ctr` row is guarded only by `hax_lib::assume!` (L262-264), which is a proof obligation
handed to hax, **not** a runtime check. `ctr` is copied verbatim from the blob, so a corrupted
value near `u32::MAX` reaches the addition directly. Confirmed at runtime (§10.5, probe Q4‑3):
`ctr = u32::MAX − 1`, `recv_key(0, u32::MAX)` panics at L265 in debug and returns
`Ok(32‑byte key)` in release.

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

**Confirmed at runtime** (§10.5): `recv.next = vec![0; 31]` → `Chain::from_pb` `Ok` →
`recv_key(0, 1)` panics at `chain.rs:243:14` (`copy_from_slice: source slice length (32)
does not match destination slice length (31)`); `recv.next = vec![]` → panics at
`chain.rs:229:9` (`assertion failed: !next.is_empty()`); both in debug **and** release. The
same L243 panic is reached through the **public** `spqr::recv()` entry point after two real
`send`/`recv` round-trips (probe Q3‑5). The `send` route (`send.next = vec![]` at the send
epoch → `send_key(0)` → L229) is also confirmed (probe Q3‑4), closing the gap that §7 left
prose-only.

**Panic-site attribution**: regression tests must distinguish the two sites per mutation —
`next = []` → L229 `assert!`; `next.len() ∉ {0, 32}` → L243 `copy_from_slice`. §12.1 uses a
1‑byte `next` and therefore panics at L243, not L229.


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

**Confirmed at runtime** (§10.5, probe Q3‑2): `recv.ctr = 5`, `recv.prev = vec![0; 37]`,
`recv_key(0, 1)` → panic at `chain.rs:191:9` (`assertion left == right failed`).

**Latent corruption — this path is *not* hit by in-order traffic.** `key()` only calls
`prev.get()` when `at < ctr`. Every in-order message (`at = ctr + 1`) takes the forward path,
which never inspects `prev` alignment, **succeeds**, appends a 36-byte record to the
misaligned `prev`, and re-persists it (probe Q5‑2: `prev.len()` grows 37 → 73, still
`% 36 ≠ 0`; probe Q5‑3: the same through the public `spqr::recv()`, which returns `Ok` with
the correct key and hands the caller a still-misaligned `state` to persist). The panic fires
only on the first out-of-order message, or — once `prev` reaches the GC threshold — via the
`gc` slice index described next. See §13 for the persistence consequence.

### 5a. Panic Path 2b: `KeyHistory::gc` — Slice Index on Misaligned History

**Trigger**: `prev.data.len() % 36 ≠ 0` **and** `prev.data.len() ≥ trim_size() * 36`,
on the *forward* path (`at > ctr`).

**Source**: `chain.rs:155-157`

```rust
let mut i: usize = 0;
while i < self.data.len() {
    if matches!(trim_horizon.cmp(&self.data[i..i + 4]), std::cmp::Ordering::Greater) {  // ← PANICS
        self.remove(i, params);
    } else {
        i += Self::KEY_SIZE;
    }
}
```

`gc` has **no** alignment assertion of its own — `Gc.lean:85` carries `h_data_aligned` as a
hypothesis. On misaligned data the loop steps by 36 from `i = 0`, so the final iteration
lands on a tail of `len % 36` bytes; if that tail is shorter than 4 the slice
`self.data[i..i + 4]` panics with `range end index … out of range`. (For a tail of 4–35 bytes
the slice succeeds but reads across the record boundary, and `remove(i, …)` then drains a
misaligned 36-byte window — silent corruption of the history rather than a panic.)

**Call chain**: `recv()` → `recv_key()` → `key()` (forward path, `ctr < at ≤ ctr + max_ooo`) →
`gc()` → slice index panic.

**Corrupted blob example** (default params): `ctr = 5000`, `prev.data = vec![0; 36 * 2201 + 1]`,
request `at = 5001`. The `assert!` at L149 passes (`5000 ≥ 2000`), then the loop panics at
L157.

**Confirmed at runtime** (§10.5, probe Q4‑2): `chain.rs:157:48` —
`range end index 4 out of range for slice of length 1`, in both debug and release.

**Why this matters for the fix**: §14.6's cheap conversion of `get`'s `assert_eq!` to `Err`
does **not** cover this path. `gc` needs its own `data.len() % 36 == 0` guard (or a `Result`
return), and L157 must be added to the list of sites to harden. Establishing
`h_data_aligned` in `from_pb` (§14.1) closes both L191 and L157 at once.

**Not mechanised**: no Lean witness for the L157 panic; `Gc.lean` assumes alignment.

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

**Confirmed at runtime** (§10.5, probe Q3‑3): exactly the example above panics at
`chain.rs:149:13` (`assertion failed: current_key >= params.max_ooo_keys_or_default()`).

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
| `send_epoch > current_epoch` | `send_epoch ≤ current_epoch` | `send_key` (L385-406) | `send_key` returns `Err(EpochOutOfRange)` until `add_epoch` advances `current_epoch` to `≥ send_epoch`; a stall, not a permanent brick. **Confirmed at runtime** (§10.5, probe Q4‑5): `send_epoch = 7`, `current_epoch = 0` → `send_key(7)` = `Err(EpochOutOfRange(7))`, `send_key(0)` = `Err(SendKeyEpochDecreased(7, 0))` — recoverable |
| `send.next` empty for `links[i]` with `i ≥ epoch_idx(send_epoch)` | only pre-send-epoch `send` directions may have empty `next` | `send_key` → `next_key` (L229) | Panic — this is the case §14.1 alone cannot catch (see §14.2). **Confirmed at runtime** (§10.5, probe Q3‑4): `links[0].send.next = vec![]` → `send_key(0)` panics at `chain.rs:229:9` |
| `params.max_ooo_keys` ≥ 390451572 | `max_ooo_keys < 390451572` | `key()` (L262-264) via `hax_lib::assume!` | The `assume!` is not a runtime check — it tells hax the bound holds. The `ctr + max_ooo_keys` addition at L265/L279 overflows **only when `ctr + max_ooo > u32::MAX`**: with `ctr = 0` and `max_ooo_keys = u32::MAX` there is no overflow and `recv_key(0, 1)` returns `Ok` in both profiles (probe Q4‑4). When it does overflow: **debug/test builds panic** (`attempt to add with overflow`); **release builds wrap** (no `overflow-checks` in `Cargo.toml`) and take the wrong `prev.clear()` / `add` arm. `trim_size()` is computed in `usize` (L86-88) and does not overflow on 64-bit; the practical consequence of a huge `max_ooo_keys` is that the GC threshold (`trim_size·36` ≈ 170 GB) is never reached — see the next row |
| `params.trim_size()` ≥ 119304647 | `trim_size() < 119304647` | `key()` (L280-283) via `hax_lib::assume!` | Same pattern — `assume!`d, not checked. Oversized `trim_size` disables GC, allowing unbounded `prev.data` growth; `trim_size() * 36` may overflow `usize` on 32-bit targets |

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
witness. The first two are now confirmed by compiled probes (§10.5); the `params` rows rest on
code reading plus the negative probe Q4‑4. Note also that `h_maxooo_bound` (`Key.lean:63,197`)
and `h_ooo` (`Gc.lean:797,833`) are the Lean-side names of the `max_ooo_keys` bound; they are
hypotheses of `recvKeyPre` (`Spqr/Specs/Chain/Chain/Defs.lean:99`) exactly like the §10.2 rows.

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

- Individual slot sizes against `2 * MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1 = 71`. **Consequence
  corrected**: this is *not* a stall. `decoded_message()` slices only
  `&pts[..necessary_points(i)]` (`polynomial.rs:922`), so excess points are ignored; the only
  effects are memory and `into_pb` output size (the `hax_lib::assume!` at `polynomial.rs:801`
  bounds the serialised size on the assumption that `add_chunk` gating at `:895-896` was the
  only writer). The invariant is violable, but its severity is memory-only.
- The `is_complete` flag (a blob with `is_complete = true` makes `decoded_message()` return
  `None` forever, silently stalling the epoch — see Finding 5 in `report.md`)

**Note on `pts_needed`**: while `from_pb` itself does not check `pts_needed` against the V1
maximum (576), every V1 call site validates `pts_needed` exactly against the expected value
(e.g., `ENCAPSULATION_KEY_SIZE / 2`, `CIPHERTEXT1_SIZE / 2`, `(CIPHERTEXT2_SIZE + MACSIZE) / 2`
in `src/v1/chunked/send_ct/serialize.rs` and `src/v1/chunked/send_ek/serialize.rs`). A
defense-in-depth check inside `from_pb` would still be reasonable but is not strictly necessary.

**Severity**: LOW-MEDIUM. Silent stall possible via `is_complete`; oversized slots cost
memory only; no immediate panic.

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
| `Key.lean` | `h_ctr_bound : self.ctr.val ≤ U32.max - 390451572` | Counter range (see also `Key32.lean` which uses `U32.max - 108458770`); analysed in §3 (fourth row) |
| `Key.lean:63,197`, `Gc.lean:797,833` | `h_maxooo_bound` / `h_ooo : max_ooo < 390451572` | `params.max_ooo_keys` range (§7, §14.1a) — blob-derived via `Chain.params` |
| `Gc.lean:85` | `h_data_aligned : self.data.length % 36 = 0` | Alignment for the `gc` loop's `data[i..i+4]` slice (§5a) |

All of the above are conjuncts of `recvKeyPre` (`Spqr/Specs/Chain/Chain/Defs.lean:95-106`),
the precondition of `recv_key_spec`; that list is therefore exactly the set of blob-derived
invariants that a validating `from_pb` would have to establish (§14.7).

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
Aeneas model is exactly a Rust `panic!`/`assert!`. The development is in ten phases (Phase 10
is described after the table):

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
- The `gc` slice-index panic at L157 (§5a), the `ctr` range (§3), and any `Chain`-level or
  `Authenticator`/`PolyDecoder`-level round-trip theorem (§13; `Chain::into_pb` is
  `#[hax_lib::opaque]` at `chain.rs:414`).

### 10.5. Runtime Evidence — Compiled-Rust Probes

The Lean model stops at the `Chain` API and does not exercise the compiled binary. To close
that gap, fourteen probe tests were written against the existing `#[cfg(test)] mod test` in
`src/chain.rs`, executed on stable‑aarch64 in **both** profiles, and then removed from the
tree; the source is preserved as `docs/corrupted_blob_counterexample.rs.txt` (repo convention
for `docs/*_counterexample.rs.txt`). Every probe builds a valid `Chain`, calls `into_pb()`,
mutates one field, calls `Chain::from_pb()` (which returned `Ok` in **every** case), and then
drives the consumer.

```
cargo test --lib           q3_probe -- --nocapture --test-threads=1   # 5 passed
cargo test --lib           q4_probe -- --nocapture --test-threads=1   # 5 passed
cargo test --release --lib q4_probe -- --nocapture --test-threads=1   # 5 passed
cargo test --lib           q5_probe -- --nocapture --test-threads=1   # 4 passed
cargo test --release --lib q5_probe --             --test-threads=1   # 4 passed
```

**Reachability and panic sites** (§§4–7):

| # | Probe | Blob mutation | Call | Debug | Release |
|---|---|---|---|---|---|
| Q3‑1 | `q3_probe_bad_next_reaches_next_key_internal_via_recv_key` | `recv.next = [0; 31]` | `recv_key(0, 1)` | **panic** `chain.rs:243:14` `copy_from_slice` length mismatch | same |
| Q3‑2 | `q3_probe_misaligned_prev_reaches_get_via_recv_key` | `recv.ctr = 5`, `recv.prev = [0; 37]` | `recv_key(0, 1)` | **panic** `chain.rs:191:9` `assertion left == right failed` | same |
| Q3‑3 | `q3_probe_large_prev_small_ctr_reaches_gc_via_recv_key` | `recv.ctr = 0`, `recv.prev = [0; 36·2201]` | `recv_key(0, 1)` | **panic** `chain.rs:149:13` `current_key >= max_ooo` | same |
| Q3‑4 | `q3_probe_empty_send_next_reaches_next_key_via_send_key` | `links[0].send.next = []` | `send_key(0)` | **panic** `chain.rs:229:9` `!next.is_empty()` | same |
| Q3‑5 | `q3_probe_top_level_recv_reaches_panic` | two real `send`/`recv` round-trips via the public API, then `PqRatchetState::decode`, set every `links[i].recv.next = [0]`, re-encode; peer sends once more | **`spqr::recv(&corrupted, &msg)`** (`lib.rs:356`) | **panic** `chain.rs:243:14` | same |
| Q4‑1 | `q4_probe_empty_recv_next_hits_assert_229` | `recv.next = []` | `recv_key(0, 1)` | **panic** `chain.rs:229:9` | same |
| Q4‑2 | `q4_probe_misaligned_large_prev_forward_path_hits_gc_slice_index` | `recv.ctr = 5000`, `recv.prev = [0; 36·2201 + 1]` | `recv_key(0, 5001)` (forward → `gc`) | **panic** `chain.rs:157:48` `range end index 4 out of range for slice of length 1` | same |
| Q4‑3 | `q4_probe_ctr_overflow_profile_dependent` | `recv.ctr = u32::MAX − 1` | `recv_key(0, u32::MAX)` | **panic** `chain.rs:265:17` `attempt to add with overflow` | **`Ok(32‑byte key)`** — silent wrap |
| Q4‑4 | `q4_probe_max_ooo_overflow_profile_dependent` | `params.max_ooo_keys = u32::MAX` (`ctr = 0`) | `recv_key(0, 1)` | `Ok` — no overflow (`0 + u32::MAX` fits; `trim_size()` is `usize`) | `Ok` |
| Q4‑5 | `q4_probe_graceful_err_epoch_inversion` | `send_epoch = 7` (> `current_epoch = 0`) | `send_key(7)`; `send_key(0)` | `Err(EpochOutOfRange(7))`; `Err(SendKeyEpochDecreased(7, 0))` — **recoverable** | same |

Q3‑5 closes the `lib.rs` → `Chain` gap: the corruption reaches `next_key_internal` through
the **public** `spqr::recv` entry point, after `decode_state`, `States::from_pb` and
`chain_from`, with no intervening check.

**Persistence and round-trip** (§13):

| # | Probe | What it does | Result (debug and release) |
|---|---|---|---|
| Q5‑1 | `q5_probe_chain_level_roundtrip_is_identity_on_corrupted_blobs` | For each of 10 mutations (`recv.next` = 31 B / `[]`; `recv.prev` = 37 B; `ctr = 0` + 79 236 B `prev`; `ctr = u32::MAX`; `next_root` = 16 B; `send_epoch = 7`; `send.next = []`; `max_ooo_keys = u32::MAX`; `max_jump = u32::MAX`): `Chain::from_pb(pb)` → `into_pb()`, and prost `encode_to_vec`/`decode` | All 10 blobs round-trip **byte-for-byte** through both the struct layer and the wire layer |
| Q5‑2 | `q5_probe_misaligned_prev_survives_ok_recv_and_is_repersisted` | `recv.ctr = 5`, `recv.prev = 37 B`; `recv_key(0, 7)` (in-order, forward) | Returns **`Ok`** (32-byte key); `into_pb()` shows `ctr = 7`, `prev.len() = 73` (still `% 36 ≠ 0`); reloading succeeds; the next out-of-order `recv_key(0, 1)` panics at L191 |
| Q5‑3 | `q5_probe_top_level_recv_ok_repersists_misaligned_prev` | Public API: two round-trips, corrupt `recv.prev = [0; 1]` on the persisted blob, peer sends one in-order message | **`spqr::recv(&corrupted, &msg)` returns `Ok`**, the derived key equals the peer's send key (corruption is invisible to the protocol), and the **returned `state`** decodes to a chain whose `recv.prev` is still misaligned — the host would persist this as the new good state |
| Q5‑4 | `q5_probe_authenticator_and_poly_decoder_roundtrip_corruption` | `Authenticator { root_key: 5 B, mac_key: [] }`; `PolynomialDecoder { is_complete: true, pts: 16 × [] }` | Both `into_pb(from_pb(pb)) == pb` |

**Failure-mode taxonomy** (consolidating §§3–9 with the probe results):

| Class | Fields | Sites | Profile |
|---|---|---|---|
| **Panic** | `recv.next` (any `≠ 32`), `send.next = []` at/after send epoch, misaligned `prev` (OOO path), misaligned + large `prev` (forward path), small `ctr` + large `prev` | L229, L243, L191, L157, L149 | debug **and** release |
| **Panic (debug/test only) / silent wrap (release)** | `ctr` near `u32::MAX`; `ctr + max_ooo_keys > u32::MAX` | L265, L279 | profile-dependent |
| **Graceful `Err`** | `send_epoch > current_epoch`; `links.is_empty()`; `current_epoch − send_epoch ≥ links.len()` | `epoch_idx` L372-382 | both |
| **`Ok` but wrong semantics** | `next_root.len() ≠ 32` (silent key divergence); `Authenticator` key lengths; `PolyDecoder::is_complete` (stall); oversized `PolyDecoder` slots (memory); oversized `trim_size` (GC disabled) | `add_epoch` L357-361; `decoded_message` L912 | both |

**Recommended follow-up**: promote these probes to permanent tests in `src/chain.rs` under a
`corrupted_blob_*` naming scheme, run in both profiles in CI, and — once §14 lands — flip
each `catch_unwind` assertion to `assert!(matches!(Chain::from_pb(pb), Err(Error::StateDecode)))`.
Gate the Q4‑3 debug-only expectation with `#[cfg(debug_assertions)]`.

---

## 11. Comparison with Finding 2 (Chunk Poisoning)

| Dimension | Finding 2 (Chunk Poisoning) | This Study (Corrupted Blobs) |
|---|---|---|
| **Attack vector** | Network message | Local storage |
| **Entry point** | `Message::deserialize` → `add_chunk` | `decode_state` → `from_pb` |
| **What gets corrupted** | Decoder point sets | Chain / authenticator / decoder state |
| **Failure mode** | Permanent epoch stall (`Err` loop) | Panic (unrecoverable inside SPQR) on §§4–6 paths; see §10.5 taxonomy for the `Err`/`Ok`/profile-dependent classes |
| **Integration mitigation** | Signal MAC auth-before-commit | **None inside SPQR**; host catches panics as `UnexpectedPanic` at FFI boundary (§2.1) but session is unrecoverable |
| **Is it a library bug?** | Yes | Yes |
| **Is it exploitable in V1?** | No (mitigated) | **Yes** (no mitigation inside SPQR) |
| **Severity in practice** | LOW (in deployed V1) | **MEDIUM** (in deployed V1) |
| **Mechanised proof** | `Spqr/Specs/Bugs/ProtocolDoS.lean` | `Spqr/Specs/Bugs/CorruptedBlobs.lean` (§10.4) |
| **Runtime reproduction** | `docs/decoder_poison_persistence_counterexample.rs.txt` | `docs/corrupted_blob_counterexample.rs.txt` (§10.5, 14 probes, both profiles) |

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
   `recv()` → `recv_key()` → `next_key_internal()` → **panic** at `chain.rs:243`
   (`copy_from_slice` length mismatch — the L229 `assert!` passes because `next` is
   non-empty; had step 3 used `[]` instead, the panic site would be L229).

**Result**: Session permanently bricked. Every restart loads the corrupted state and panics.
Note that the *reload* half of this loop is host behaviour (the aborted call never produced
a new blob, so libsignal keeps the old one — §2.1); the SPQR-side contribution is that
`from_pb` accepts the blob unchanged on every load. See §13 for the three distinct senses
in which the corruption persists.

**Mechanised**: `restore_then_recv_panics_bad_next` (hypotheses `pb.next.length ≠ 32`,
`ced.ctr < at ≤ ced.ctr + maxJump`) plus `corrupted_state_roundtrips` for the crash loop.
**Confirmed at runtime** end-to-end through the public API: probe Q3‑5 (§10.5).

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

**Result**: Minimal modification (1 byte) permanently crashes the session — but **latently**.
Unlike §12.1 and §12.4, this corruption does *not* crash on the next `recv()`: every in-order
message takes the forward path in `key()`, which never inspects `prev` alignment, so it
**succeeds**, appends 36 bytes to the misaligned history (37 → 73 → 109 → …) and re-persists
it through the `Ok` return value (probes Q5‑2 / Q5‑3, §10.5). The panic fires on the first
out-of-order message (`get`, L191), or — once `prev` grows past `trim_size()·36` — inside the
`gc` loop on the forward path (L157, §5a). Between the corruption event and the first panic
the session looks healthy, so backups taken in that window, and host-side "roll back to last
good state" strategies, carry the corruption forward.

**Mechanised**: `restore_then_recv_panics_misaligned_prev` (hypotheses
`pb.prev.length % 36 ≠ 0`, `at < ced.ctr`). The latent `Ok`-path re-persistence is confirmed
at runtime only (§10.5); a Lean corollary that the forward-path `key` preserves
`prev.data.length % 36` is future work (§14.5).

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

- **Availability**: Panics surface as bridge-level `UnexpectedPanic` errors (§2.1). With
  persisted corruption, the session is permanently bricked — every restart loads the same
  corrupted state and panics again.
- **No graceful degradation on the §§4–6 paths**: failures on the `next_key_internal`,
  `KeyHistory::get` and `KeyHistory::gc` paths (L229, L243, L191, L157, L149) are
  `panic!`/`assert!`/slice-index aborts, not `Err` returns; `next_key_internal` and `gc`
  have no `Result` channel at all. The caller has no opportunity to handle the error, log
  diagnostics, or attempt recovery. This statement is **scoped**: the §7 epoch-ordering cases
  return a recoverable `Err(EpochOutOfRange)`, the `ctr`/`max_ooo_keys` overflows panic only in
  debug builds and wrap in release (§3, §7), and the `next_root`, `Authenticator` and
  `PolyDecoder` cases return `Ok` with wrong semantics (§10.5 taxonomy).
- **No mitigation inside SPQR**: The host integration catches panics at the FFI boundary
  via `run_ffi_safe`/`catch_unwind` (§2.1), but SPQR itself provides no graceful error path.
- **Primary threat is non-adversarial**: Storage corruption, truncated writes, backup/restore
  bugs, and schema skew are the realistic scenarios. A malicious local attacker who can modify
  the decrypted session database has far more powerful attacks available than triggering a panic.

### Persistence: Three Senses in Which the Corruption Survives

The "crash loop" claim above conflates three distinct mechanisms. Only the second and third
are properties of SPQR; all three were confirmed at runtime (§10.5, probes Q5‑1 – Q5‑4).

1. **Reload after panic (host policy).** A panicking `send()`/`recv()` never returns a new
   `state`, so the host keeps the pre-call blob and reloads it on the next call. This is
   libsignal's behaviour (`docs/evaluate.md` Q7; §2.1 — no code path resets
   `pq_ratchet_state` on error), not something SPQR does. It is what makes §12.1 and §12.4
   a *loop* rather than a single crash.
2. **Identity round-trip (SPQR).** Every `into_pb` in the persistence path is a pure
   field-by-field repackaging with no normalisation, so `into_pb ∘ from_pb` is the identity
   on every blob `from_pb` accepts — corrupted or not — at all four layers
   (`ChainEpochDirection`, `Chain`, `Authenticator`, `PolyDecoder`) and through the prost
   wire encoding. Mechanised for `ChainEpochDirection` (Phase 5, `corrupted_state_roundtrips`);
   `Chain::into_pb` is `#[hax_lib::opaque]` (`chain.rs:414`) so the `Chain` level has no Lean
   statement; confirmed empirically for all ten §3/§7 corruption classes byte-for-byte
   (probe Q5‑1) and for `Authenticator`/`PolyDecoder` (probe Q5‑4). The one non-identity case
   is a `PolyDecoder` slot with duplicate `x` values, which `SortedSet::push` de-duplicates —
   moving the state *toward* validity.
3. **Propagation through a successful call (SPQR).** A corrupted blob can be loaded, used
   with an `Ok` result, and written back **still corrupted** into the `state` the caller is
   told to persist. `spqr::send`/`recv` unconditionally re-encode `chain.into_pb()`
   (`lib.rs:301, 313, 443`), so whatever `Chain::from_pb` accepted and the operation did not
   touch is re-serialised verbatim. Demonstrated for misaligned `prev` through
   `Chain::recv_key` (probe Q5‑2: 37 → 73 bytes, `Ok`) and through the public `spqr::recv()`
   (probe Q5‑3: `Ok`, correct key, returned state still misaligned). This form defeats any
   host-side "roll back to last good state" strategy — the *last good state* is itself
   corrupted — and lets corruption survive backups taken after the corruption event, or reach
   another device via state sync, while looking healthy.

**Immediate vs latent**: `next.len() ≠ 32` (§4) and small `ctr` + large `prev` (§6) crash on
the very next in-order message. Misaligned `prev` (§5) is latent: it panics only on the first
out-of-order message or once GC triggers (§5a), and until then propagates via sense 3. The
overflow cases (§3 `ctr` row, §7 `max_ooo_keys`) are latent in release builds indefinitely —
they round-trip unchanged (probe Q5‑1) and are applied with wrapping arithmetic on every call.

### Blast Radius

A single `PqRatchetState` blob has multiple distinct fields whose corruption leads
to panics, silent divergence, or permanent stalls:

- Each `ChainEpochDirection`: 4 panic sites across 3 fields (§§4–6, §5a) — `next` (L229,
  L243), `prev` data (L191, L157), `prev`+`ctr` (L149); plus the `ctr` range (L265/L279,
  debug-only panic / release wrap)
- Each `ChainEpoch`: up to twice that (send + recv directions)
- `Chain` level: `next_root` (silent divergence surfacing at the Signal layer),
  `send_epoch > current_epoch` (send failure until `current_epoch` catches up), empty
  `send.next` at/after the send epoch (panic in `next_key`), `params` ranges (overflow /
  GC disabled). Note: `links.is_empty()` returns a graceful `Err(EpochOutOfRange)`, not a panic.
- `Authenticator`: 2 semantic failure modes — `root_key`, `mac_key` (section 8)
- `PolyDecoder`: `is_complete` stall; slot sizes cost memory only (section 9)


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
    // h_ctr_bound (Key.lean): ctr <= u32::MAX - 390451572, the constant already assume!'d
    // at chain.rs:263. Use 108458770 (Key32.lean) if 32-bit targets must be covered.
    if pb.ctr > u32::MAX - 390451572 { return Err(Error::StateDecode); }
    Ok(Self { ctr: pb.ctr, next: pb.next, prev: KeyHistory { data: pb.prev } })
}
```

Establishes: `h_data_aligned` ✓ (closing both L191 and the §5a L157 slice index),
`h_prev_ctr` ✓ (and therefore `h_key_ge` ✓), `h_ctr_bound` ✓ (and `h_ctr_lt` ✓, closing the
debug-only overflow at L265/L279 for any `max_ooo_keys` that passes §14.1a), and the weak
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
   `ced.prev.data.length % 36 = 0`, `ced.prev.data.length ≤ 36 * ced.ctr.val`,
   `ced.ctr.val ≤ U32.max - 390451572`, and `ced.next.length = 0 ∨ ced.next.length = 32`).
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
6. **Round-trip and `Ok`-path corollaries** (closing the §13 sense‑2/sense‑3 gaps):
   `authenticator_corrupted_roundtrips` and `poly_decoder_corrupted_roundtrips` are two-line
   `spec_mono` compositions of the existing `into_pb_spec`/`from_pb_spec` pairs (the
   `PolyDecoder` version needs a no-duplicate-`x` hypothesis, the documented non-identity
   case). A `Chain`-level `corrupted_chain_roundtrips` requires the manual case-split style of
   Phase 7 because `Chain::into_pb` is `#[hax_lib::opaque]`. A corollary of `Key.lean`'s
   forward-path spec stating that `prev.data.length % 36` is *preserved* by a successful
   `key` (adds are 36 bytes) would formalise the §12.3 latent-propagation observation.

### 14.6. Defense-in-Depth: Replace `assert!` with `Err`

Even after `from_pb` validation, convert the downstream `assert!`/`assert_eq!`/implicit
panics at **L149, L157, L191, L229, L243** to return `Err(Error::InternalInvariantViolation)`
(new error variant) rather than panicking. This guards against any future code path
constructing a `ChainEpochDirection` without going through `from_pb`.

Split by effort:

- **Cheap now**: `KeyHistory::get` (L191) already returns `Result<Vec<u8>, Error>`, so its
  `assert_eq!` can become `return Err(...)` with no signature change.
- **Requires signature changes**: `KeyHistory::gc` returns `()` and `next_key_internal`
  returns `(u32, [u8; 32])`. Converting their asserts to `Err` changes `key()`'s and
  `next_key()`'s call chains, the hax preconditions, and the `Gc.lean` /
  `NextKeyInternal.lean` specs. Plan carefully.
- **`gc` needs its own alignment guard**: converting only `get`'s `assert_eq!` leaves the
  L157 slice index (§5a) panicking on the same misaligned data via the forward path. Add
  `if self.data.len() % Self::KEY_SIZE != 0 { return Err(...) }` (or an early `return` that
  skips GC) before the loop at L154; `Gc.lean:85` already carries the corresponding
  `h_data_aligned` hypothesis, so the spec change is a hypothesis → checked-branch move.
- **`next_key_internal`** has two sites: the `assert!` at L229 (empty) and the
  `copy_from_slice` at L243 (wrong non-zero length). A single `if next.len() != 32` check at
  entry replaces both.

**Note**: adding `Error::InternalInvariantViolation` is a public API change to `spqr::Error`.

**Recommended additional tests**:

1. A proptest that round-trips `Chain::into_pb` → `from_pb` on states that have gone
   through `send_key` across multiple epochs, to guard against the regression where valid
   empty-`next` directions (pre-send-epoch `send`) are rejected by §14.2.
2. A concrete Rust repro for each of §12.1/§12.3/§12.4 (mirroring the Lean
   `restore_then_recv_panics_*` theorems): build a `Chain`, `into_pb()`, mutate the field,
   `from_pb()`, and assert that `recv_key` **returns `Err(StateDecode)`** after the fix
   (before the fix, wrap in `std::panic::catch_unwind` and assert it panics). **Done in
   pre-fix form**: the fourteen probes of §10.5 are committed as
   `docs/corrupted_blob_counterexample.rs.txt`; promote them into `src/chain.rs` under a
   `corrupted_blob_*` naming scheme. The expected-panic-site column must distinguish L229
   (`next = []`) from L243 (`next.len() ∉ {0, 32}`), and the I4 (`ctr`) case must be gated
   with `#[cfg(debug_assertions)]` because release builds return `Ok`.
3. A **corrupted-state** round-trip test (probe Q5‑1 of §10.5: ten mutations, `into_pb ∘
   from_pb == id` and prost `encode`/`decode == id`) alongside the valid-state proptest of
   item 1, and a **re-persisted-after-`Ok`** test (probe Q5‑3: misaligned `prev` survives a
   successful `spqr::recv()` into the returned `state`). After the §14 fixes land, both flip
   to `assert!(matches!(Chain::from_pb(pb), Err(Error::StateDecode)))`.
4. Run every test in **both** profiles (`cargo test` and `cargo test --release`) so the
   debug/release divergence of the overflow cases is exercised.

### 14.7. Invariant → Fix Traceability

Numbering follows `docs/evaluateSPQR.md` §3 (I1–I16). "Lean" is the hypothesis a validating
`from_pb` would discharge; "Runtime" cites the §10.5 probe that exhibits the violation.

| # | Invariant | Failure | Fix | Lean hypothesis | Runtime |
|---|---|---|---|---|---|
| I1 | `recv.next.len() == 32` | panic L229 / L243 | §14.1 (weak) + §14.2 (strong) | `h_next_len` | Q3‑1, Q3‑5, Q4‑1 |
| I2 | `prev.len() % 36 == 0` | panic L191 (OOO) / L157 (forward GC) | §14.1 | `h_data_aligned` (`Get.lean`, `Gc.lean`) | Q3‑2, Q4‑2, Q5‑2, Q5‑3 |
| I3 | `prev.len() ≤ 36·ctr` | panic L149 | §14.1 | `h_prev_ctr` → `h_key_ge` | Q3‑3 |
| I4 | `ctr ≤ u32::MAX − 390451572` | debug panic L265/L279; release wrap | §14.1 (`ctr` check) | `h_ctr_bound`, `h_ctr_lt` | Q4‑3 |
| I5 | `prev.len() + 36·(index−ctr) ≤ usize::MAX` | allocation failure only | — (unreachable from a realistic blob) | `h_kh_cap` | — |
| I6 | `next_root.len() == 32` | silent key divergence | §14.2 | — (construction invariant) | Q5‑1 (round-trip) |
| I7 | `send_epoch ≤ current_epoch` | graceful `Err(EpochOutOfRange)` | §14.2 | — | Q4‑5 |
| I8 | `links.len() ≥ 1`, `current_epoch − send_epoch < links.len()` | graceful `Err(EpochOutOfRange)` | §14.2 (`back >= links.len()` guard) | — | — |
| I9 | `send.next.len() == 32` for `i ≥ send_idx` | panic L229 | §14.2 | `h_next_len` via `send_key` | Q3‑4 |
| I10 | `max_ooo_keys < 390451572` | debug panic L265 (if `ctr` large) / GC disabled | §14.1a | `h_maxooo_bound`, `h_ooo` | Q4‑4 (negative) |
| I11 | `trim_size() < 119304647` | GC disabled → unbounded `prev` | §14.1a | `hax_lib::requires` on `add`/`remove` | — |
| I12 | `index + max_ooo ≤ u32::MAX` | overflow in `get` | *message* validation (not `from_pb`) | `h_ooo_no_overflow` | — |
| I13 | `root_key.len() == mac_key.len() == 32` | non-standard MAC key | §14.3 | — | Q5‑4 (round-trip) |
| I14 | `is_complete == false` until decoded | permanent stall | not fixed by §14.4 as written; needs `is_complete` re-derivation or rejection | — | Q5‑4 (round-trip) |
| I15 | `pts[i].len() ≤ 71` | memory / `into_pb` size only | §14.4 | `hax_lib::assume!` at `polynomial.rs:801` | — |
| I16 | `pts_needed ≤ 576` | not violable (checked at every V1 call site) | optional defense-in-depth | — | — |

---

## 15. Summary

| Component | Defect | Failure Mode | Severity | Integration Mitigation? | Mechanised? | Runtime-confirmed? |
|---|---|---|---|---|---|---|
| `ChainEpochDirection::from_pb` | No validation of `next.len()`, `prev` alignment/size, `ctr` range | Panic (4 sites: L229, L243, L191/L157, L149); debug-only panic / release wrap on `ctr` overflow (L265) | **MEDIUM** | None inside SPQR; host catches panics as `UnexpectedPanic` (§2.1) | **Yes** — `CorruptedBlobs.lean` Phases 1–5, 9–10 (not L157, not `ctr`) | **Yes** — Q3‑1…3, Q4‑1…3, Q5‑1…3 (both profiles) |
| `Chain::from_pb` | No validation of `next_root.len()`, epoch ordering, position-dependent `send.next`, `params` ranges | Silent divergence (Signal layer) / graceful `Err` stall / panic (L229) / GC disabled | **MEDIUM** | None inside SPQR | **Partial** — Phase 7 (`next_root` only) | **Yes** — Q3‑4, Q4‑4, Q4‑5, Q5‑1 |
| `Authenticator::from_pb` | No validation of key lengths | Non-standard-length keys weaken MAC properties | LOW | None inside SPQR | **Yes** — Phase 6 | Round-trip only — Q5‑4 |
| `PolyDecoder::from_pb` | No bounds on slot sizes, `is_complete` | Silent stall (`is_complete`); memory only (slot size) | LOW-MEDIUM | None inside SPQR | **Partial** — Phase 8 (`is_complete` only) | Round-trip only — Q5‑4 |
| All four `into_pb`/`from_pb` pairs + prost wire | No normalisation | Corruption round-trips byte-for-byte and is re-persisted by successful calls (§13) | — (amplifier) | Host keeps old blob on panic (§2.1) | **Partial** — Phase 5 (`ChainEpochDirection` only) | **Yes** — Q5‑1…4 |

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
position are known (§14.1–14.2). The clean formal target is: every blob-derived conjunct of
`recvKeyPre` (`Spqr/Specs/Chain/Chain/Defs.lean:95-106`, i.e. all but the `index`-dependent
terms) becomes a provable **postcondition** of `Chain::from_pb` (§14.7). This
simultaneously fixes the Rust code and makes the Lean specification's structural hypotheses
provable invariants; the negative theorems in `Spqr/Specs/Bugs/CorruptedBlobs.lean` and the
runtime probes in `docs/corrupted_blob_counterexample.rs.txt` then serve as a regression
oracle (§14.5, §14.6).

**Evidence status after this revision** (per `docs/evaluateSPQR.md`): the five questions the
study was asked — does `from_pb` accept semantically invalid state (Q1); which invariants can
be violated (Q2); can such state reach `key`/`get`/`gc` (Q3); does the consumer panic rather
than return `Err` (Q4); can the malformed state be persisted and restored (Q5) — are all
answered *yes* and each is now backed by three independent lines of evidence: source
reading, machine-checked Lean (for I1–I3, I6, I13, I14 and the `ChainEpochDirection`
round-trip), and compiled-Rust probes in both profiles (for every panic site, the graceful
`Err` cases, the profile-dependent overflows, and all four round-trip layers). What remains
prose-only is the Lean mechanisation of I4, I7–I11, I15, the L157 panic, and the `Chain`/


---

## 16. Analysis: Can a Remote Network Attack Cause an Attacker-Controlled, SPQR-Invalid Value to Be Persisted in the Protobuf State Subsequently Consumed by `from_pb()`, Without Requiring Local or Storage-Layer Access?

**Answer: No for the primary panic-class fields (`next`, `prev`, `next_root`, `params`);
Yes for the `ctr` range invariant (I4), but only from a malicious authenticated peer.**

A purely remote, *unauthenticated* network attacker cannot cause any SPQR-invalid value to be
persisted. Four independent defensive layers prevent this. However, a **malicious
authenticated peer** — who holds valid Signal ratchet keys and therefore passes all MAC
checks — can drive the victim's persisted `recv.ctr` past `h_ctr_bound`
(`u32::MAX − 390451572`) by repeatedly choosing large (but individually in-range) `index`
values in their messages, without requiring any local or storage-layer access. This violates
invariant I4 (§14.7). **Correction (2026‑09‑26, §16.9)**: crossing `h_ctr_bound` itself
has *no* runtime effect — the bound is proof-side slack. The runtime fault fires only when
`ctr > u32::MAX − max_ooo_keys` (default: `u32::MAX − 2000`), i.e. ≈ 390 M messages *later*
than the Lean bound; at that point the peer can trigger a debug-build panic at L265/L279/L192
or, in release, a silent `prev.clear()`, dropped history keys, or a spurious `KeyTrimmed`
(probes Q16b‑S1…S8, `src/chain.rs`). The practical impact is bounded to **self-DoS of the
attacker's own send direction** plus a modest CPU-amplification vector (§16.9.4).

**Second revision (§16.10)**: widening the question from "SPQR-*invalid*" to "attacker-
*chosen*" values uncovers three further **yes** answers for a malicious authenticated peer,
all confirmed through the public `spqr::recv()` API (probes Q16c‑C1…C4, `src/lib.rs`):
(C1/C2) **attacker-chosen chunk bytes are persisted verbatim** into the `PolyDecoder` point
sets *before* any SPQR MAC can run, and a single replayed chunk index permanently stalls the
epoch — Finding 2 is *not* mitigated against an authenticated peer; (C3) during the
negotiation window an empty V0 message **persists `inner: None`** and silently disables SPQR
for the whole session under libsignal's `min_version = V0`. These do not violate any
`from_pb`-level structural invariant (I1–I16), but they are attacker-controlled persisted
state reached remotely with no storage access.

The conclusion is supported by source-level tracing, mechanised Lean proofs, compiled-Rust
runtime probes, the steering probe Q16‑1 (`#[ignore]`d — ≈ 4·10⁹ HKDFs), the eight
seeded-state probes Q16b‑S1…S8 (`src/chain.rs`), and the four public-API probes
Q16c‑C1…C4 (`src/lib.rs`), all in both profiles.

### 16.1. Why the Network Path Cannot Inject Malformed Persisted State (Primary Fields)

The `from_pb()` functions (`Chain::from_pb`, `ChainEpochDirection::from_pb`,
`Authenticator::from_pb`, `PolyDecoder::from_pb`) consume the **persisted local state blob**
loaded from `SessionStore::load_session`. This blob is written only after a successful
`spqr::send()`/`spqr::recv()` returns `Ok`. Four barriers block a remote attacker from
injecting arbitrary values into the primary panic-class fields:

0. **Clone-then-commit-on-success** (`session_cipher.rs:455,475`):
   `decrypt_message_with_state` operates on a *clone* of the session state. The clone is
   committed to the `SessionRecord` (and thence to `SessionStore`) only if the entire
   function returns `Ok`. On any error — including MAC failure at L663 — the clone is dropped
   and the persisted state is unchanged. This is the most fundamental barrier: even if
   SPQR's `recv()` mutates its state portion before MAC verification (L606 vs L657), the
   mutation is confined to an ephemeral clone.

1. **Signal envelope MAC** (`ciphertext.verify_mac`, `session_cipher.rs:657-661`):
   authenticates messages before state commit. Forged messages are discarded (and the clone
   is dropped — see layer 0).

2. **SPQR-internal authenticator**: `States::from_pb(pb)?.recv()` performs its own MAC check.

3. **No verbatim copy of primary fields**: `recv()` derives `next` and `prev` state via KDF
   chains — it does **not** copy attacker-controlled bytes into persisted `next`, `prev`,
   `next_root`, or `params` fields. The attacker cannot choose arbitrary values for these
   fields via the network path.
   (See `evaluateV1.md` §5.1, lines 209–214.)

   **Limitation**: layer 3 does **not** cover `ctr`. While `ctr` is not copied verbatim from
   wire content, it is *incremented to match the attacker-chosen `index`* parameter on each
   `recv_key` call. A malicious authenticated peer can therefore *steer* `ctr` into an
   invalid range cumulatively. See §16.7.

### 16.2. The State Write Path

```
Network message
  → Clone session state (session_cipher.rs:455)
    → Signal envelope MAC verification (session_cipher.rs:657-661)
      → SPQR authenticator MAC check (States::from_pb(pb)?.recv())
        → spqr::recv() derives state via KDF from current valid state
          → Ok(new_state_bytes) → Commit clone to SessionRecord (L475)
            → Host persists to SessionStore
  (on any Err: clone is dropped; persisted state unchanged)
```

**Ordering note**: inside `decrypt_message_with_state`, SPQR's `recv` actually runs at L633
*before* the envelope MAC at L657. The key insight is that both operate on the **clone**
(layer 0), so even if SPQR mutates `pq_ratchet_state` at L606, a subsequent MAC failure
causes the entire clone to be discarded at L481.

At no point does attacker-controlled wire content flow verbatim into persisted primary-field
bytes (`next`, `prev`, `next_root`, `params`). However, the `ctr` field is indirectly driven
by the attacker-chosen `index` — see §16.7.

### 16.3. What a Remote Attacker *Can* Do (and Why It Doesn't Suffice for Primary Fields)

Via Finding 2 (chunk poisoning, §11), a remote attacker bypassing authentication could poison
`PolyDecoder` point sets (permanent epoch stall). However: (a) this is **mitigated** by Signal
MAC auth-before-commit in deployed V1, and (b) even if committed, it affects `PolyDecoder`
state (LOW severity stall), **not** the `Chain`-level fields whose corruption causes the
MEDIUM severity panics of §§3–7.

### 16.4. Threat Sources That *Can* Inject Malformed Fields

Per §12 and `evaluateV1.md` §5.3, extended with source 7 (§16.7):

| # | Source | Remote? | Storage Access Required? | Chosen Values? | Fields Affected |
|---|---|---|---|---|---|
| 1 | Storage corruption (bit-rot, FS errors) | No | N/A (non-adversarial) | Random | Any |
| 2 | Backup/restore bugs | No | N/A (non-adversarial) | Truncation/skew | Any |
| 3 | Cloud sync conflict | Partially | N/A (non-adversarial) | Merge artifacts | Any |
| 4 | Compromised cloud backup credentials | Remote **+ storage** | **Yes** | **Yes** | Any |
| 5 | Rooted/compromised device | Local | **Yes** | **Yes** | Any |
| 6 | Protobuf schema skew | No | N/A (non-adversarial) | Misinterpreted | Any |
| **7** | **Malicious authenticated peer** | **Yes (remote only)** | **No** | **Steered, not chosen** | **`ctr` only (I4)** |

Sources 1–6 require local or storage-layer access (or are non-adversarial). Source 7 is
purely remote but requires the attacker to be the legitimate conversation peer (or to have
compromised the peer's ratchet keys), and can only affect `ctr` — not the primary panic-class
fields (`next`, `prev`, `next_root`, `params`).

### 16.5. Evidence Summary

| Evidence Type | Finding | Reference |
|---|---|---|
| Source-level tracing (libsignal `a47ba487`) | Clone-then-commit at L455/L475; MAC precedes commit; `recv()` derives primary fields via KDF | `evaluateV1.md` §5.1, §7.2–7.4; `session_cipher.rs:455,475` |
| Runtime probe Q3‑5 | Primary-field corruption must be pre-existing in blob; does not originate from network | §10.5, `evaluateV1.md` §5.4 |
| Lean mechanised proof | Panics proven on corrupted blobs; premise requires pre-corrupted blob | §10.4 |
| Threat-source enumeration | Seven sources; only source 7 is purely remote, and it affects `ctr` only | §12, `evaluateV1.md` §5.3, §16.7 |
| **Runtime probe Q16‑1** | **Malicious peer drives `ctr` past `h_ctr_bound` via repeated in-range `index` jumps; persisted state violates I4** | **§16.7, `src/chain.rs`** |

### 16.6. Conclusion

The corrupted-blob vulnerability is **primarily a local-storage robustness defect**. For the
primary panic-class fields (`next`, `prev`, `next_root`, `params`), it is not remotely
exploitable: the Signal envelope MAC, the clone-then-commit pattern, the SPQR-internal
authenticator, and KDF-based state derivation collectively prevent any remote injection.

**Exception — `ctr` range (I4)**: A malicious authenticated peer can drive `recv.ctr` past
`h_ctr_bound` purely via the network, by sending ~156K messages with `index = ctr + max_jump`
(§16.7). This is the weakest of the invariant violations (debug-build panic at L265 /
release-build silent wrap — not the MEDIUM-severity L229/L243/L191/L149 panics), but it is a
genuine counterexample to a blanket "No" answer. The `from_pb` check proposed in §14.1
(`if pb.ctr > u32::MAX - 390451572 { return Err(…) }`) closes the *reload* path but does not
prevent `ctr` from reaching the invalid range during normal operation; a runtime check inside
`key()` replacing the `hax_lib::assume!` at L262–264 with an actual `Err` guard would close
it at the source (§16.8).

The `from_pb()` validation fixes (§14) remain valuable for:

- **Non-adversarial robustness**: storage corruption, backup bugs, schema skew.
- **Defense-in-depth**: hardening against storage-layer compromise (source 4).
- **Formal completeness**: making Lean structural hypotheses provable invariants.
- **Closing the `ctr`-steering reload path** (§14.1, source 7).

### 16.7. Counterexample: Malicious Authenticated Peer Drives `ctr` Past `h_ctr_bound`

**Attacker model**: The attacker is the legitimate conversation peer (or has compromised the
peer's Signal ratchet keys). They pass the Signal envelope MAC and the SPQR-internal
authenticator on every message — they are an *authenticated* sender.

**Mechanism**: Each `recv_key(epoch, index)` call advances `recv.ctr` to `index` via the
KDF loop in `key()` (`chain.rs:270-286`). The `max_jump` guard at L250-252 limits each call
to advancing `ctr` by at most `max_jump` (default 25,000). But the attacker controls `index`
in every message, so by repeatedly sending messages with `index = ctr + max_jump`, they
advance the victim's `recv.ctr` by 25,000 per message.

**Cost**: `h_ctr_bound = u32::MAX − 390,451,572 = 3,904,515,723`. At 25,000 per message:
`⌈3,904,515,723 / 25,000⌉ = 156,181` messages. Each message triggers a KDF loop of up to
25,000 iterations, but the computation completes successfully.

**Result**: After ~156K messages, `recv.ctr > h_ctr_bound`. The state is persisted by the
host (the `recv_key` call returns `Ok`; the host commits the clone per §16.2).

> **Correction (§16.9)**: the original text of this section claimed the *next* message then
> overflows at L265. That is wrong. L265 adds `ctr + max_ooo_keys_or_default()` (= 2000 by
> default), which fits in `u32` for every `ctr ≤ u32::MAX − 2000`. `h_ctr_bound`
> (`u32::MAX − 390451572`) is a *proof-side* slack constant chosen so the hax/Lean arithmetic
> lemmas close for any `max_ooo_keys < 390451572`; it is not the runtime overflow threshold.
> Probe Q16b‑S1 confirms `recv_key` returns `Ok` in both profiles for every `ctr` in
> `(h_ctr_bound, u32::MAX − 2000]`, including `ctr + 1` and `ctr + max_jump` requests. The
> `#[ignore]`d Q16‑1 probe has been corrected accordingly.
>
> The real threshold is `ctr > u32::MAX − max_ooo_keys`, reached after
> `⌈(u32::MAX − 2000) / 25 000⌉ ≈ 171 799` steering messages (≈ 4.3·10⁹ HKDF evaluations on
> the victim, ≈ 10 ms per message in release — S6). At that point:
>
> - **Debug builds**: panic (`attempt to add with overflow`) at `chain.rs:265` (S2), at
>   `chain.rs:279` mid-KDF-loop (S3, triggered *during* steering, no reload needed), or at
>   `chain.rs:192` in `get` for an out-of-order `index` (S4).
> - **Release builds**: silent wrap. S2: `at > ctr + max_ooo` becomes `at > tiny`, so
>   `prev.clear()` fires spuriously and every stored out-of-order key of the epoch is
>   discarded. S3: `ctr + max_ooo >= at` becomes false, so skipped keys with
>   `ctr > u32::MAX − max_ooo` are never stored (1000 of 1999 stored). S4: `index + max_ooo`
>   wraps, `get` returns `Err(KeyTrimmed)` for a key that *is* in `prev`. The key that `key()`
>   itself returns is still the correct KDF output — divergence from the peer is confined to
>   the *history*, i.e. to later out-of-order messages, not to the in-order stream.

**Why this bypasses all four defensive layers of §16.1**:

- **Layer 0 (clone-then-commit)**: the clone is committed because `recv_key` returns `Ok`.
- **Layer 1 (Signal MAC)**: the attacker is authenticated; MAC passes.
- **Layer 2 (SPQR authenticator)**: the attacker is the legitimate peer; auth passes.
- **Layer 3 (no verbatim copy)**: `ctr` is not copied verbatim — it is *incremented* to
  match `index`. But the effect is the same: the attacker controls where `ctr` ends up.

**Invariant violated**: I4 (`ctr ≤ u32::MAX − 390451572`), corresponding to `h_ctr_bound` in
`Key.lean`. The `hax_lib::assume!` at L262-264 is not a runtime check.

**Runtime evidence**: Probe `q16_probe_remote_index_drives_ctr_past_bound` in `src/chain.rs`
demonstrates the full sequence: repeated `recv_key(0, ctr + max_jump)` calls, persist via
`into_pb`, reload via `from_pb` (which accepts the out-of-range `ctr`), and observe the
overflow on the next call.

**Scope**: This affects `ctr` only. The primary panic-class fields (`next.len()`,
`prev` alignment/size, `next_root.len()`, `params` ranges) remain unreachable via the
network path — they are derived from KDFs, not from message parameters.

### 16.8. Recommended Additional Fix for `ctr` Steering

The `from_pb` validation in §14.1 (`if pb.ctr > u32::MAX - 390451572 { return Err(…) }`)
catches corrupted blobs on *reload* but does not prevent `ctr` from reaching the invalid
range during normal operation. To close the `ctr`-steering attack at the source, replace the
`hax_lib::assume!` at `chain.rs:262-264` with a runtime guard:

```rust
// Replace:
//   hax_lib::assume!(
//       params.max_ooo_keys_or_default() < 390451572 && self.ctr <= u32::MAX - 390451572
//   );
// With:
if self.ctr > u32::MAX - 390451572 {
    return Err(Error::CounterExhausted(self.ctr));
}
```

This ensures that even if `ctr` is driven to the boundary by a malicious peer during a long
session, the overflow is caught as a graceful `Err` rather than a panic (debug) or silent
wrap (release). The same check should be applied at the loop-interior `assume!` at L275-277.

**Note**: `Error::CounterExhausted` is a new error variant. The practical impact is that a
session is limited to ~3.9 billion messages per epoch per direction before requiring an epoch
advance, which is far beyond any realistic usage.

**Lean specification impact**: `h_ctr_bound` in `Key.lean` becomes a checked runtime
invariant (both at `from_pb` and at `key()`) rather than an assumed precondition. The
`hax_lib::assume!` can be replaced with `hax_lib::assert!` or removed entirely once the
runtime check is in place.



### 16.9. In-Depth Scenario Analysis: What a Remote Peer Can and Cannot Do to Persisted State

This section enumerates every persisted field a network peer can influence, the exact
runtime thresholds involved, and the consequences per build profile. Evidence is the eight
seeded-state probes `q16b_probe_*` in `src/chain.rs` (both profiles, `cargo test [--release]
--lib q16b_ -- --nocapture --test-threads=1`). Each probe seeds via `into_pb`/`from_pb` the
*exact* `ChainEpochDirection` a steering peer would produce — `key()` depends only on
`ctr`, `prev`, `next`, and `prev` is empty after any jump `> max_ooo` — so the multi-hour
steering loop (Q16‑1, now `#[ignore]`d) is not needed to observe the end state.

#### 16.9.1. Attacker classes

| Class | Passes Signal MAC? | Passes SPQR authenticator? | Can commit state? | Can influence |
|---|---|---|---|---|
| A. Unauthenticated network attacker | No | No | **No** (clone dropped, §16.1 layer 0) | Nothing persisted. Only CPU on the victim *before* the MAC check (SPQR `recv` runs at `session_cipher.rs:633`, MAC at `:657`); bounded by `KeyJump` (`max_jump` HKDFs). |
| B. Authenticated peer, honest-but-buggy | Yes | Yes | Yes | `ctr` (via `index`), epoch advance (via SCKA messages), `prev` contents (indirectly, via which keys are skipped/consumed) |
| C. Authenticated peer, malicious | Yes | Yes | Yes | Same as B, chosen adversarially; also CPU amplification |
| D. Attacker holding peer's ratchet keys (compromise) | Yes | Yes | Yes | Same as C — but such an attacker can already read all traffic; DoS is not their goal |

Only B–D matter for persistence. Everything below concerns class C.

#### 16.9.2. Field-by-field reachability from the network

| Persisted field | Derivation | Remotely steerable? | Probe |
|---|---|---|---|
| `recv.ctr` | `+= 1` per KDF step until `== index` | **Yes**, monotone, ≤ `max_jump` per message | Q16‑1, S1–S7 |
| `recv.next` | HKDF output, always 32 B | No — length invariant I1 is preserved by every `Ok` call | S8 |
| `recv.prev` | 36 B records appended in the KDF loop; removed by `get`/`gc`/`clear` | **Contents/size only**, never alignment (I2) nor `len ≤ 36·ctr` (I3); bounded by `trim_size·36 = 79 236` B | S6, S8 |
| `send.*` | Only touched by local `send_key` | No (the peer never drives our send direction) | — |
| `next_root` | HKDF output from previous `next_root` + epoch secret | No — 32 B always | — |
| `current_epoch`, `links` | Advanced by `add_epoch` when SCKA completes an epoch | Peer can *pace* epochs (needs the KEM round-trip, i.e. both parties send), cannot skip or invert them | — |
| `params` | Copied verbatim from the *local* blob, never from the wire | No | — |
| `Authenticator`, `PolyDecoder` | SCKA state machine; Finding 2 (poisoning) blocked by MAC-before-commit | No (in deployed V1) | — |

**Conclusion**: the *only* remotely steerable Lean invariant is I4 (`ctr` range); I12
(`index + max_ooo ≤ u32::MAX`) is message-side and becomes reachable *because* I4 is.

#### 16.9.3. The `ctr` axis — thresholds and consequences (default params)

| Zone | `ctr` range | Lean (`recvKeyPre`) | Runtime, debug | Runtime, release | Probe |
|---|---|---|---|---|---|
| Z0 normal | `0 … u32::MAX − 390 451 572` | satisfiable | Ok | Ok | — |
| Z1 Lean-invalid, runtime-benign | `(u32::MAX − 390 451 572, u32::MAX − 2000]` | **unsatisfiable** (I4) | **Ok** | **Ok** | S1 |
| Z2 L265/L279 overflow zone | `(u32::MAX − 2000, u32::MAX)` | unsatisfiable | **panic** L265 (in-order) / L279 (mid-loop) | Ok, but spurious `prev.clear()` (S2) / skipped keys not stored (S3) | S2, S3 |
| Z2′ OOO request with `index > u32::MAX − 2000` | any `ctr > index` | I12 violated | **panic** L192 | `Err(KeyTrimmed)` for a key that *is* stored | S4 |
| Z3 exhausted | `ctr == u32::MAX` | `h_ctr_lt` violated | permanent `Err` (no path to `*ctr += 1` since `at > ctr` impossible) | same | S5 |

Cost to reach Z2 from a fresh epoch: `⌈(u32::MAX − 2000)/25 000⌉ ≈ 171 799` authenticated
messages, each costing the victim 25 000 HKDF evaluations (≈ 10 ms release / 470 ms debug —
S6), and the attacker one real message send. Total victim CPU ≈ 30 min (release). Any epoch
advance resets `ctr` to 0 in the *new* link — but the attacker controls whether they ever
complete the KEM handshake, so they can hold the epoch fixed indefinitely.

**Reload path**: a blob with `ctr` in Z1 or Z2 passes `Chain::from_pb` unchanged (Q16‑1
Phase 2, Q5‑1) and is re-persisted by every `Ok` call (§13 sense 3). The §14.1 check
`pb.ctr > u32::MAX − 390451572 → Err(StateDecode)` would therefore **turn a Z1 state that is
runtime-benign into a hard `StateDecode` on reload** — i.e. the fix as written would *create*
a remotely triggerable session brick that does not exist today (see §16.9.6).

#### 16.9.4. Consequence assessment — who is harmed?

`recv.ctr` in link *i* is the counter of **the attacker's own send direction**. Every effect
in Z2/Z3 lands on the *victim's ability to decrypt the attacker's messages*:

- Spurious `prev.clear()` (S2) → the attacker's own delayed out-of-order messages become
  `KeyAlreadyRequested`.
- Unstored skipped keys (S3) / spurious `KeyTrimmed` (S4) → same.
- Exhaustion (S5) → the attacker can no longer send in this epoch until a new epoch.
- Debug-build panic → `UnexpectedPanic` at the bridge; but only when processing *the
  attacker's* message. The clone is dropped; the persisted state is the pre-call blob, so the
  victim's session with everyone else — and even the victim's *send* direction to the
  attacker — is unaffected. Repeat messages repeat the panic (loop), but production bridges
  ship release builds with `overflow-checks = false` (no `[profile]` override in
  `Cargo.toml`).

What the attacker **cannot** do via this axis: brick the victim's send direction, affect any
other conversation, corrupt `next`/`prev` alignment (I1–I3, S8), influence `next_root` or
epoch secrets, or cause an incorrect *in-order* key (the KDF chain is exact; only the
history bookkeeping wraps).

Net: **self-DoS plus CPU amplification**. Severity LOW. The CPU-amplification part exists at
`ctr = 0` too (S6: any in-range `index = ctr + max_jump` costs 25 000 HKDFs, `Err(KeyJump)`
for larger jumps costs nothing and leaves the state byte-identical) and is independent of
the overflow.

#### 16.9.5. Non-default `ChainParams`

`ChainParams` is chosen by the *local* integrator (libsignal uses defaults), never by the
peer, but integrators that raise the limits shrink the attack:

| `max_ooo_keys` | `max_jump` | Z2 threshold `u32::MAX − max_ooo` | Messages to reach Z2 | Probe |
|---|---|---|---|---|
| 2 000 (default) | 25 000 (default) | 4 294 965 295 | ≈ 171 799 | S1–S4 |
| 2³¹ | 2²⁰ | 2 147 483 647 | ≈ 2 048 | S7 |
| ≥ 390 451 572 | any | `u32::MAX − max_ooo` | violates I10 (§14.1a) at `ctr = 0` already, yet L265 still fits until Z2 | Q4‑4 |

For `max_jump ≥ u32::MAX − max_ooo` a *single* message reaches Z2. Such configurations are
pathological but not rejected anywhere (§14.1a is the proposed guard).

#### 16.9.6. Fix guidance revisited

1. **Do not add the §14.1 `ctr > u32::MAX − 390451572 → StateDecode` check in isolation.**
   It converts the runtime-benign zone Z1 — which a peer can reach with ≈ 156 K messages —
   into a permanent `StateDecode` on every reload, a *worse* outcome than today. If a
   reload-time check is wanted, use the runtime-meaningful bound
   `ctr.checked_add(params.max_ooo_keys_or_default()).is_none()` (Z2), and pair it with the
   in-`key()` guard below so that Z2 is never persisted in the first place.
2. **Guard at the source (§16.8), with the right bound.** Replace the `hax_lib::assume!` at
   L262–264 and L275–277 with `checked_add` on `ctr + max_ooo`, returning a new
   `Error::CounterExhausted(ctr)`; and at L192 use `at.checked_add(max_ooo)` (I12). With
   these, the persisted `ctr` can never exceed `u32::MAX − max_ooo`, so I4 becomes
   `ctr ≤ u32::MAX − max_ooo` — a *tighter* runtime invariant than the Lean slack, and the
   Lean bound `U32.max − 390451572` remains a valid (weaker) precondition whenever
   `max_ooo < 390451572` (I10).
3. **Tighten the Lean side rather than the code**: `recvKeyPre` could state the exact
   `ce.recv.ctr.val + maxOoo ≤ U32.max` instead of the slack constant; the `Key.lean` proofs
   already need only that fact. That would make Z1 disappear as a *spec* anomaly and align
   I4 with the runtime threshold.
4. **Probes to keep**: S1 (regression oracle that Z1 is benign — must flip to `Err` only if
   item 1's *correct* bound is adopted, never for the slack bound), S2–S4 (flip from
   `catch_unwind` to `Err(CounterExhausted)` after item 2), S8 (I1–I3 preservation).

#### 16.9.7. Scenario summary

| # | Scenario | Attacker class | Fields | Lean | Debug | Release | Impact |
|---|---|---|---|---|---|---|---|
| 1 | Forged message, wrong MAC | A | none persisted | — | `Err`, ≤ 25 000 HKDFs wasted | same | CPU only |
| 2 | Steer `ctr` into Z1 | C | `ctr` | I4 ✗ | Ok | Ok | none today; **bricks on reload if §14.1 slack check is added** |
| 3 | Steer `ctr` into Z2, in-order msg | C | `ctr` | I4 ✗ | panic L265 | spurious `prev.clear()` | attacker's own OOO msgs undecryptable |
| 4 | Steer `ctr` into Z2 mid-jump | C | `ctr`, `prev` | I4 ✗ | panic L279 | skipped keys unstored | same |
| 5 | OOO `index` near `u32::MAX` | C | — | I12 ✗ | panic L192 | spurious `KeyTrimmed` | same |
| 6 | Exhaust `ctr = u32::MAX` | C (release only) | `ctr` | `h_ctr_lt` ✗ | permanent `Err` | same | attacker cannot send until epoch advance |
| 7 | Repeated `max_jump` jumps at low `ctr` | C | `ctr`, `prev` (bounded) | ✓ | Ok | Ok | ≈ 10 ms CPU per message; `prev ≤ 79 236` B |
| 8 | Any attempt on `next`/`prev`-alignment/`next_root`/`params` | A–D | — | I1–I3, I6, I10, I11 ✓ | — | — | **not reachable remotely** (KDF-derived / local-only) |
| 9 | Hold epoch fixed (never finish KEM) to keep steering | C | `current_epoch` | ✓ | Ok | Ok | enables 2–6; also a plain protocol stall, already possible |


### 16.10. Additional "Yes" Scenarios — Attacker-Chosen Persisted State Beyond `ctr`

§16.1–16.9 asked whether a remote peer can persist an *SPQR-invalid* value, i.e. one that
violates a `from_pb`-level structural invariant (I1–I16). Reading the question more broadly
— can a remote peer persist an **attacker-chosen** value that `from_pb` will later consume
with harmful effect — yields three further **yes** answers. All are confirmed end-to-end
through the public `spqr::recv()` API by probes `q16c_probe_*` in `src/lib.rs`
(`cargo test [--release] --lib q16c_ -- --nocapture --test-threads=1`, 4/4 passing in both
profiles).

#### 16.10.1. Where the earlier reasoning was too narrow

§16.1 layer 3 ("no verbatim copy") is correct for the `Chain` fields but **false for the
`PolyDecoder` point sets**: `add_chunk` (`polynomial.rs:879-904`) stores the 32 chunk bytes
of every accepted message as 16 `(x, y)` points *verbatim*, and `States::recv` returns `Ok`
(so the host commits) whenever the decoder is still incomplete. The SPQR-internal MAC
(`verify_hdr`/`verify_ct`) runs only once the *whole* header/ciphertext has been
reassembled — layer 2 is therefore **after** persistence for every chunk but the last. §16.3
dismissed this as "mitigated by the Signal MAC", which holds only against attacker class A
(unauthenticated); an authenticated peer (class C) passes the Signal MAC by construction.

#### 16.10.2. C1 — Attacker-chosen bytes persisted verbatim

*Setup*: A (attacker) sends its first `Hdr` chunk; B receives (`Ok`). A then sends a second
`Hdr` message with chunk index 100 and 32 arbitrary bytes.

*Observed*: `recv` → `Ok`; B's persisted V1 state grows by 65 B (16 points × 4 B + varint
length bytes). The bytes are exactly what A chose. A *third* forged chunk completes the
3-points-per-slot header decoder with garbage → `verify_hdr` fails → `Err(MacVerifyFailed)`
(clone dropped), but the first forged chunk **remains in the committed state**, and every
later *honest* chunk from A now also fails the MAC (C1 tail assertion).

*Bound*: growth is capped by `add_chunk` gating at `2·35 + 1 = 71` points per slot
(`necessary_points` + low-index extras) — I15 is *not* violable remotely; only the *contents*
are attacker-chosen.

#### 16.10.3. C2 — Authenticated chunk poisoning → permanent epoch stall

*Setup*: after B receives A's honest chunk 0, A replays chunk index **0** with different
bytes. `SortedSet::push` de-duplicates on `x` only (last-write-wins), so the honest point is
replaced. `recv` → `Ok`, poisoned state persisted.

*Observed*: A continues honestly; on the message that completes the header, B gets
`Err(MacVerifyFailed)`; every retry fails identically. The epoch never advances — this is
Finding 2 (`report.md`) reached by a **remote authenticated** peer with **no storage
access**, contradicting the "mitigated in deployed V1" verdict of §11/§16.3 for class C.

*Who is harmed*: the SCKA epoch for *both* directions stalls (no new `EpochSecret`), so the
conversation stays on the current epoch's chain keys indefinitely — a loss of post-quantum
*forward secrecy / healing* for the victim, not just self-DoS. Unlike §16.9, the attacker
does **not** lose the ability to send; the Double Ratchet continues, SPQR just never
contributes fresh key material. This is a **MEDIUM**-severity, silent, remotely-triggered
degradation. (The decoder is `Ok`-persisted; §13 sense 3 applies.)

*Fix*: `report.md` Finding 2 option (b) — reset the decoder on `MacVerifyFailed` — or
first-write-wins in `add_chunk`; plus a Lean spec that the persisted point set for index `x`
equals the *first* accepted chunk for `x`.

#### 16.10.4. C3 — Version downgrade persists `inner: None`

*Setup*: libsignal initialises with `min_version = V0` (`ratchet.rs:109, 200`). Before B has
received any V1 message, `version_negotiation` is `Some`. A sends an **empty** message
(`msg_version = V0`).

*Observed*: `recv` takes the `Ordering::Less` arm (`lib.rs:377-409`), persists
`{ inner: None, version_negotiation: None, chain: None }` → `Ok`. Thereafter every V1 message
from A returns `Ok(key: None)` via the `Greater` arm (`lib.rs:373`) and B's own `send()`
emits empty messages with no key (`lib.rs:268`). **SPQR is permanently and silently off for
this session.** Once B has received a single V1 message the window closes
(`version_negotiation: None` at `lib.rs:442`; V0 then → `Err(VersionMismatch)`).

*Assessment*: this is the *designed* negotiation behaviour, and an attacker who holds the
peer's Double-Ratchet keys can already read the traffic. But (i) it is a remotely-persisted
attacker-chosen state (`inner: None`) with no local access, (ii) it is *silent* to the
victim, and (iii) an attacker positioned to inject the very first message of a session (e.g.
a compromised peer device before it is repaired) gains a permanent PQ opt-out. Severity LOW
as a protocol choice; worth flagging because the answer to the §16 question is "yes".

#### 16.10.5. C4 — Unauthenticated attacker: CPU only, nothing persisted

For completeness: a forged message with `index = 25 000` makes `spqr::recv()` (which runs
*before* the outer Signal MAC, `session_cipher.rs:633` vs `:657`) spend 25 000 HKDFs
(≈ 470 ms debug / ≈ 10 ms release) and return `Ok`; the host's MAC then fails and the clone
is dropped. Confirms §16.1 layer 0 for class A: **no** persisted effect.

#### 16.10.6. Scenarios examined and rejected

| Candidate | Why it is a "no" |
|---|---|
| `add_epoch` `assert!(epoch == current_epoch + 1)` (`chain.rs:355`) | `EpochSecret.epoch` comes from the SCKA state machine, which only ever emits `current + 1`; a peer cannot make it skip (message `epoch` is checked `==` state epoch at every transition, `states.rs:282-340`). |
| `links` growth / `EPOCHS_TO_KEEP` | `add_epoch` pushes one link per completed KEM; `send_key` pops. A peer that completes epochs while the victim never sends grows `links` by one per epoch — bounded by epoch pacing (a full 1088+960+128-byte KEM per epoch), ≈ 0.5 KB per link. Memory only, honest-traffic-equivalent. |
| `pts_needed` | Set from constants at decoder construction; not wire-derived. |
| `is_complete` | No code path sets it; wire-unreachable. |
| Chunk `index > 65535` / `epoch == 0` | Rejected by `deserialize` (`serialize.rs:195, 254`). |
| `Authenticator` keys | Derived by HKDF from epoch secrets; peer influences the secret only via a valid KEM exchange. |
| `ek_matches_header` failure (`ErroneousDataReceived`) | `Err` → clone dropped; but the *decoder* holding the bad EK bytes was already persisted on the earlier `Ok` chunks → same stall class as C2 (subsumed). |

#### 16.10.7. Revised answer to §16

| Class of persisted value | Remote, authenticated peer? | Remote, unauthenticated? | Probe |
|---|---|---|---|
| Violates a `from_pb` structural invariant (I1–I3, I6–I11, I13–I16) | **No** | No | S8, C1 (bound) |
| Violates I4 (`ctr` Lean bound) — runtime-benign until `u32::MAX − max_ooo` | **Yes**, ≈156K–172K msgs, self-DoS only | No | Q16‑1, S1–S7 |
| Attacker-chosen `PolyDecoder` points (valid shape, poisoned content) → epoch stall | **Yes**, 1 message, MEDIUM | No (Signal MAC) | C1, C2 |
| `inner: None` (SPQR disabled) via V0 downgrade in the negotiation window | **Yes**, 1 message, LOW | No | C3 |
| Anything | — | **No** (CPU only) | C4 |

