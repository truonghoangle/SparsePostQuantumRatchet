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

**Severity**: HIGH — panics are denial-of-service against the session, and no integration-level
mitigation is available.

---

## Table of Contents

1. [Threat Model](#1-threat-model)
2. [Architectural Context](#2-architectural-context-the-persistence-boundary)
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
| **Integration mitigation** | Auth-before-commit blocks poisoning | **None** — `from_pb` runs at load time, pre-auth |
| **Failure mode** | Permanent epoch stall | Unrecoverable panic (process crash) |

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
`Chain::from_pb()` — then immediately uses the result for `recv_key()` at `lib.rs:435`,

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
| `next.len() == 32` | `next_key_internal` (L228-244) | `NextKeyInternal.lean`: `h_next_len : next.length = 32` | **panic** |
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
- `next = vec![]`: hits `assert!(!next.is_empty())` at L229 — also a panic, not a graceful `Err`
- `next = vec![0; 33]` or `vec![0; 31]`: `copy_from_slice` panics (length mismatch)

**Spec evidence**: `NextKeyInternal.lean` line 41:
```lean
theorem next_key_internal_spec (next : Slice U8) (ctr : U32)
    (h_next_len : next.length = 32)
    (h_ctr : ctr < U32.max) :
```

The `h_next_len` hypothesis is required but never established by `from_pb`.


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

**Spec evidence**: `Get.lean` line 43: `(h_data_aligned : v.length % 36 = 0)`

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

**Corrupted blob example** (default params: `max_ooo_keys = 2000`, `trim_size() = 2201`):
- `ctr = 5`, `prev.data = vec![0; 36 * 2201]` (79,236 bytes)
- GC triggers → `assert!(5 >= 2000)` → **panic**

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

Three additional unvalidated fields:

| Field | Required Invariant | Consumer | Failure |
|---|---|---|---|
| `next_root.len() ≠ 32` | `next_root.len() == 32` | `add_epoch` → `kdf::hkdf_to_slice` (L357-361) | No panic, but HKDF with wrong-length salt → peers silently derive different chain keys |
| `links.is_empty()` | `links.len() ≥ 1` | `epoch_idx` (L376-381): `links.len() - 1 - back` | Underflow on `0 - 1` → **panic** |
| `send_epoch > current_epoch` | `send_epoch ≤ current_epoch` | `send_key` (L385-406) | Every `send_key` call fails permanently |

The `next_root` case is particularly insidious: it does not panic — it silently produces
incorrect derived keys, causing both sides of the conversation to diverge without error.

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

- **`mac_key = vec![]`**: HMAC-SHA256 handles any key length (no panic), but every
  authenticator produces the same tags — MAC forgery becomes trivial.
- **`root_key = vec![]`**: weakens forward secrecy of the authenticator chain.

**Severity**: LOW-MEDIUM. No panic, but semantic security properties are violated.

**Note**: Return type is `Self` (infallible). Fix requires changing to `Result<Self, Error>`
and updating all 9 call sites in `src/v1/unchunked/send_ct/serialize.rs` and
`src/v1/unchunked/send_ek/serialize.rs`.

---

## 9. Quaternary Defect: `PolyDecoder::from_pb`

**Source**: `src/encoding/polynomial.rs:815-853`

`PolyDecoder::from_pb` validates `pb.pts.len() == 16` and each slot's length mod 4, but
does **not** validate:

- `pts_needed` against V1 maximum (576)
- Individual slot sizes against `2 * MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1 = 71`
- The `is_complete` flag (a blob with `is_complete = true` makes `decoded_message()` return
  `None` forever, silently stalling the epoch — see Finding 5 in `report.md`)

**Severity**: LOW-MEDIUM. Resource exhaustion and silent stall possible, no immediate panic.


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
| `Get.lean` | `h_ooo_no_overflow : at1 + maxOoo ≤ U32.max` | Arithmetic overflow |
| `Gc.lean` | `h_key_ge : … max_ooo ≤ current_key.val` | Subtraction underflow |
| `Key.lean` | `h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val` | GC precondition |
| `Key.lean` | `h_ctr_bound : self.ctr.val ≤ U32.max - 390451572` | Counter range |

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
because the code does not have it.

---

## 11. Comparison with Finding 2 (Chunk Poisoning)

| Dimension | Finding 2 (Chunk Poisoning) | This Study (Corrupted Blobs) |
|---|---|---|
| **Attack vector** | Network message | Local storage |
| **Entry point** | `Message::deserialize` → `add_chunk` | `decode_state` → `from_pb` |
| **What gets corrupted** | Decoder point sets | Chain / authenticator / decoder state |
| **Failure mode** | Permanent epoch stall (`Err` loop) | Process panic (crash) |
| **Integration mitigation** | Signal MAC auth-before-commit | **None available** |
| **Is it a library bug?** | Yes | Yes |
| **Is it exploitable in V1?** | No (mitigated) | **Yes** (no mitigation) |
| **Severity in practice** | LOW (in deployed V1) | **HIGH** (in deployed V1) |

**Why network authentication does not help**: The integration's auth-before-commit pattern
operates at the *message processing* level:

```
1. Load persisted state ← CORRUPTED BLOB LOADED HERE
   ↳ Chain::from_pb() accepts invalid invariants
2. Process SPQR message against corrupted state
   ↳ recv_key() → key() → next_key_internal() / get() / gc()
   ↳ PANIC — process crashes before reaching MAC check
3. (Never reached) Verify Signal envelope MAC
```

The MAC check never executes because the process panics at step 2. The commit that matters
already happened (when the corrupted blob was written to storage).


---

## 12. Attack Scenarios

### 12.1. Targeted Session Kill via Backup Modification

**Attacker model**: Access to the encrypted backup store (cloud backup with compromised
credentials, or physical access to device storage).

1. Locate the SPQR state blob in the backup/database.
2. Decode as protobuf (schema is public in the SPQR repo).
3. Replace `chain.links[0].recv.next` with `[0]` (1 byte instead of 32).
4. Re-encode and write back.
5. Victim restores the backup.
6. First incoming message triggers `recv()` → `recv_key()` → `next_key_internal()` → **panic**.

**Result**: Session permanently bricked. Every restart loads the corrupted state and panics.

### 12.2. Silent Key Divergence via `next_root` Truncation

1. Modify `chain.next_root` to `[0; 16]` (16 bytes instead of 32).
2. Victim restores and continues the session.
3. `add_epoch()` uses 16-byte `next_root` as HKDF salt → different chain keys than peer.
4. All messages fail MAC verification — but error is `InvalidCtMac`, not `StateDecode`,
   obscuring the cause.

**Result**: Session silently diverges. Neither party can communicate.

### 12.3. One-Byte DoS via Alignment Violation

1. Append a single byte to any `chain.links[i].recv.prev` field (e.g., 36 → 37 bytes).
2. Next `recv()` → `KeyHistory::get()` → `assert_eq!(37 % 36, 0)` → **panic**.

**Result**: Minimal modification (1 byte) permanently crashes the session.

### 12.4. GC Panic via Counter/History Mismatch

1. Set `chain.links[i].recv.ctr = 0`.
2. Set `chain.links[i].recv.prev = vec![0; 36 * 2201]` (large enough to trigger GC).
3. Next `recv()` with `at > ctr` → `key()` → `gc()` → `assert!(0 >= 2000)` → **panic**.

---

## 13. Impact Assessment

### Severity: HIGH

- **Availability**: Panics crash the process. With persisted corruption, the session is
  permanently bricked — every restart loads the same corrupted state and panics again.
- **No graceful degradation**: Failures are `panic!`/`assert!` crashes, not `Err` returns.
  The caller has no opportunity to handle the error, log diagnostics, or attempt recovery.
- **No integration mitigation**: Unlike Finding 2, no layer above SPQR can prevent this.

### Blast Radius

A single `PqRatchetState` blob has at least **11+ distinct fields** whose corruption leads
to panics, silent divergence, or permanent stalls:

- Each `ChainEpochDirection`: 3 panic paths (sections 4-6)
- Each `ChainEpoch`: 6 paths (send + recv)
- `Chain` level: 3 more failure modes (section 7)
- `Authenticator`: 2 semantic failure modes (section 8)
- `PolyDecoder`: resource exhaustion + silent stall (section 9)


---

## 14. Recommended Fixes

### 14.1. `ChainEpochDirection::from_pb` (Primary)

```rust
fn from_pb(pb: pqrpb::chain::epoch::EpochDirection) -> Result<Self, Error> {
    if pb.next.len() != 32 { return Err(Error::StateDecode); }
    if pb.prev.len() % 36 != 0 { return Err(Error::StateDecode); }
    if pb.prev.len() / 36 > pb.ctr as usize { return Err(Error::StateDecode); }
    Ok(Self { ctr: pb.ctr, next: pb.next, prev: KeyHistory { data: pb.prev } })
}
```

Establishes: `h_next_len` ✓, `h_data_aligned` ✓, `h_prev_ctr` ✓

### 14.2. `Chain::from_pb` (Secondary)

```rust
pub(crate) fn from_pb(pb: pqrpb::Chain) -> Result<Self, Error> {
    if pb.next_root.len() != 32 { return Err(Error::StateDecode); }
    // ... existing direction/links/params parsing ...
    if links.is_empty() { return Err(Error::StateDecode); }
    if pb.send_epoch > pb.current_epoch { return Err(Error::StateDecode); }
    // ...
}
```

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
if pb.pts_needed as usize > 576 { return Err(PolynomialError::SerializationInvalid); }
for slot in &pb.pts {
    if slot.len() / 4 > 71 { return Err(PolynomialError::SerializationInvalid); }
}
```

### 14.5. Lean Specification Updates

After implementing fixes:

1. **Update `FromPb.lean`**: the `Err` branch should no longer map to `False` but to
   concrete error conditions matching the new validation checks.
2. **`h_next_len`, `h_data_aligned`, `h_prev_ctr`** become **provable invariants** rather
   than assumed preconditions, because `from_pb` now establishes them.
3. An end-to-end `recv_after_restore_safe` theorem becomes provable.

### 14.6. Defense-in-Depth: Replace `assert!` with `Err`

Even after `from_pb` validation, convert the downstream `assert!`/`assert_eq!` at L149,
L191, L229 to return `Err(Error::InternalInvariantViolation)` (new error variant) rather
than panicking. This guards against any future code path constructing a
`ChainEpochDirection` without going through `from_pb`.

---

## 15. Summary

| Component | Defect | Failure Mode | Severity | Integration Mitigation? |
|---|---|---|---|---|
| `ChainEpochDirection::from_pb` | No validation of `next.len()`, `prev` alignment/size | Panic (3 paths) | **HIGH** | **None** |
| `Chain::from_pb` | No validation of `next_root.len()`, `links` emptiness, epoch ordering | Panic / silent divergence | **HIGH** | **None** |
| `Authenticator::from_pb` | No validation of key lengths | Weak MACs, forgery possible | MEDIUM | **None** |
| `PolyDecoder::from_pb` | No bounds on `pts_needed`, slot sizes, `is_complete` | Resource exhaustion, silent stall | LOW-MEDIUM | **None** |

**Key conclusion**: This is a **real, unmitigated bug in the deployed V1 protocol**. Unlike
Finding 2 (chunk poisoning), which is mitigated by the upstream integration's
authentication-before-commit pattern, the corrupted-blob class operates at the state-loading
level where no authentication boundary exists. Any corruption of the persisted state blob —
from disk errors, backup issues, or malicious modification — can crash or silently brick an
SPQR session with no graceful recovery path.

The fix is straightforward: validate semantic invariants in every `from_pb` function,
converting assumed preconditions into checked postconditions. This simultaneously fixes the
Rust code and makes the Lean specification's structural hypotheses provable invariants.
