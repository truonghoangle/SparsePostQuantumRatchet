# Evaluation of V1 Protocol `from_pb` Deserialization Path and Blob Provenance

**Evaluated document**: `docs/CorruptedBlobs.md` (1208 lines, rev. 2026‑09‑26)
**Supporting documents**: `docs/evaluate.md` (Q1–Q5), `docs/evaluateSPQR.md` (G1–G14)
**Source cross-checked**: `src/lib.rs`, `src/chain.rs`, `src/authenticator/serialize.rs`,
`src/encoding/polynomial.rs`, `src/v1/chunked/states/serialize.rs`,
`src/v1/chunked/send_ct/serialize.rs`, `src/v1/chunked/send_ek/serialize.rs`,
`src/v1/unchunked/send_ct/serialize.rs`
**libsignal cross-checked**: commit `a47ba487` (2026‑03‑17) —
`rust/protocol/src/state/session.rs`, `rust/protocol/src/proto/storage.proto`,
`rust/protocol/src/storage/traits.rs`, `rust/protocol/src/session_cipher.rs`
**Evaluation date**: 2026‑09‑26

---

## 1. Scorecard

| # | Question | Answered? | Confidence | Evidence type |
|---|---|---|---|---|
| Q‑V1 | Does the deployed V1 protocol use the affected `from_pb` deserialization path? | **Yes — answered** | High | Call-chain reading (§2.1), libsignal integration mapping (§2.2), compiled-Rust probes (§2.3), Lean mechanisation (§2.4) |
| Q‑Src | What is the source of the protobuf blob passed to `from_pb` in V1, and who can influence that source? | **Yes — answered** | High | libsignal storage-layer tracing (§3.1), threat-source enumeration (§3.2), validation-gap analysis (§3.3) |
| Q3 | Can a remote attacker cause the protobuf blob or persisted SPQR state consumed by `from_pb` to contain attacker-chosen malformed fields? | **Yes — answered** | High | Network/storage path separation (§5.1), MAC-before-commit analysis (§5.1), threat-source table (§5.3), runtime probe Q3-5 (§5.4) |
| Q4 | What authentication, integrity protection, or validation is applied to the state before it reaches `from_pb`? | **Yes — answered** | High | Threat-model table (§7.1), production load path (§7.2), `decode_state` source (§7.3), MAC ordering (§7.4), FFI panic handling (§7.5), protection summary (§7.6) |
| Q5 | Can an attacker-controlled malformed state survive V1 processing and become persisted SPQR state? | **Yes — answered** | High | Three-sense persistence analysis (§9.1), identity round-trip (§9.2), propagation through successful calls (§9.3), compiled-Rust probes Q5‑1–Q5‑4 (§9.4), Lean mechanisation Phase 5 (§9.5) |
| Q6 | Can that persisted state subsequently reach the affected SPQR operation (recv, send, key, get, or gc) during normal V1 operation? | **Yes — answered** | High | Call-chain tracing (§2.1, §10.1), runtime probes Q3‑1–Q3‑5 and Q4‑1–Q4‑2 (§10.2), attack scenarios §12.1–12.4 of `CorruptedBlobs.md` (§10.3), Lean mechanisation Phases 1–5, 9–10 (§10.4) |
| Q7 | What security-relevant effect does triggering the corrupted state have on the V1 session or endpoint? | **Yes — answered** | High | Failure-mode taxonomy (§12.1), session-recovery analysis (§12.2), security-property impact (§12.3), evidence synthesis (§12.4) |
| Q8 | Can the attacker trigger this effect remotely and repeatedly without local access to the victim's persisted state? | **Yes — answered** | High | Network/storage path separation (§5.1), MAC-before-commit (§5.1, §7.4), threat-source table (§5.3), `CorruptedBlobs.md` §§11–12 |

**Result: All eight questions are fully answered.** Q‑V1 and Q‑Src were answered by the
existing report material; Q3 is answered by synthesising the network-path analysis (§11–12
of `CorruptedBlobs.md`) with the storage-layer threat enumeration; Q4 is answered
comprehensively across §§1–2.1 and §12.2 of `CorruptedBlobs.md`; Q5 is answered by
`CorruptedBlobs.md` §13 and probes Q5‑1–Q5‑4 (§10.5); Q6 is answered by call-chain
tracing (§10.1), runtime probes (§10.2), attack scenarios (§10.3), and Lean mechanisation
(§10.4); Q7 is answered by synthesising the failure-mode taxonomy (§12.1), session-recovery
analysis (§12.2), and security-property impact mapping (§12.3); Q8 is answered by
synthesising the network-path separation analysis (§5.1), MAC ordering (§7.4), and the
attack-scenario preconditions in `CorruptedBlobs.md` §§11–12. **No further execution plan
is needed.**

---

## 2. Q‑V1: Does the Deployed V1 Protocol Use the Affected `from_pb` Path?

### 2.1. Call-chain analysis (source reading)

The deployed V1 protocol exercises the affected `from_pb` path on **every** `spqr::send`
and `spqr::recv` call after the first operation in a session. The only exception is the
very first operation, where `PqRatchetState.chain` is `None` and the chain is constructed
fresh via `Chain::new` (`lib.rs:333-341`).

| Public entry point | Path to `from_pb` |
|---|---|
| `spqr::recv` (`lib.rs:356`) | `decode_state` (`lib.rs:472`) → `chain_from` (`lib.rs:343`) → `Chain::from_pb` (`chain.rs:434`) → `ChainEpochDirection::from_pb` (`chain.rs:306`) |
| `spqr::send` (`lib.rs:238`) | `decode_state` → `Chain::from_pb` (`lib.rs:288`) → same |
| `spqr::recv` (V1 inner path) | additionally: `States::from_pb` (`lib.rs:425`, `v1/chunked/states/serialize.rs:49`) → per-state `from_pb`s → `PolyDecoder::from_pb` (`encoding/polynomial.rs:815`), `Authenticator::from_pb` (`authenticator/serialize.rs:16`) |
| `spqr::send` (V1 inner path) | `States::from_pb` (`lib.rs:274`) → `PolyEncoder::from_pb`, `Authenticator::from_pb` |

All line numbers verified against spqr `v1.5.0` source in this repository.

### 2.2. libsignal integration mapping

The report (`CorruptedBlobs.md` §2, lines 175–182) and `evaluate.md` Q1 trace the
production integration end-to-end:

1. **Storage**: The app-provided `SessionStore::load_session` (`traits.rs:152`) returns a
   `SessionRecord` containing `pq_ratchet_state` as raw bytes.
2. **Record decode**: `SessionRecord::deserialize` (`session.rs:663-671`) performs
   `RecordStructure::decode` — prost wire-format validity only.
3. **State holder**: `SessionState::new` (`session.rs:147,163`) stores the bytes verbatim.
4. **Load + use (recv)**: `SessionState::pq_ratchet_recv` (`session.rs:601-608`) calls
   `spqr::recv(&self.session.pq_ratchet_state, msg)` — `decode_state` → `Chain::from_pb`
   executes here.
5. **Load + use (send)**: `SessionState::pq_ratchet_send` (`session.rs:610-617`) calls
   `spqr::send(...)` — same path.

The blob is passed **verbatim** from the app's SQLite store into `decode_state` with no
intermediate semantic validation at any layer.

### 2.3. Compiled-Rust probes

Probe **Q3‑5** (`q3_probe_top_level_recv_reaches_panic`, `CorruptedBlobs.md` §10.5, line
715) demonstrates the complete end-to-end path through the compiled binary: two real
`send`/`recv` round-trips via the public API, corruption of the persisted `PqRatchetState`
blob (setting every `links[i].recv.next = [0]`), then `spqr::recv(&corrupted, &msg)` —
which panics at `chain.rs:243:14` through the `from_pb` path. This confirms reachability
in the compiled binary, not merely in the source or Lean model.

### 2.4. Lean mechanisation

The Lean file `Spqr/Specs/Bugs/CorruptedBlobs.lean` (Phases 3, 4, 9, 10) proves that
`from_pb pb = Ok ced → ∀ r, recv_key ced at params ≠ ok r` — i.e., the corrupted state
admitted by `from_pb` causes `recv_key` to have no successful execution, which corresponds
to a Rust panic in the Aeneas model.

### 2.5. Persistence amplification

The report (§13, probes Q5‑1 through Q5‑3) demonstrates that corrupted state accepted by
`from_pb` is **re-persisted** by successful operations. `spqr::send`/`recv` unconditionally
re-encode via `chain.into_pb()` (`lib.rs:301, 313, 443`), and `into_pb ∘ from_pb` is the
identity on all blobs `from_pb` accepts (mechanised for `ChainEpochDirection` in Phase 5;
confirmed at runtime for all four layers and the prost wire layer in `evaluateSPQR.md`
§3C.3), so corruption round-trips byte-for-byte.


---

## 3. Q‑Src: Source of the Protobuf Blob and Who Can Influence It

### 3.1. Blob identity and production load path

The protobuf blob is the **persisted SPQR session state** (`SerializedState`, a `Vec<u8>`)
embedded inside libsignal's `SessionStructure` protobuf as field 15 (`pq_ratchet_state`,
defined in `rust/protocol/src/proto/storage.proto:66`). The complete load path is:

| Layer | Location (libsignal `a47ba487`) | Detail |
|---|---|---|
| On-disk container | `storage.proto:66` | `SessionStructure.pq_ratchet_state = 15` (`bytes`) |
| Storage trait | `traits.rs:152` | `SessionStore::load_session` — app-provided (SQLite) |
| Record decode | `session.rs:663-671` | `SessionRecord::deserialize` — prost wire-format only |
| State holder | `session.rs:147,163` | `SessionState::new` stores the bytes verbatim |
| Previous sessions | `session.rs:725-733` | `previous_session_states()` — same non-validation |
| **Load + use (recv)** | `session.rs:601-608` | `pq_ratchet_recv` → `spqr::recv` |
| **Load + use (send)** | `session.rs:610-617` | `pq_ratchet_send` → `spqr::send` |
| Recv caller | `session_cipher.rs:633-647` | `decrypt_message_with_state` |
| Send caller | `session_cipher.rs:359-371` | `encrypt_message` |

Source: `CorruptedBlobs.md` §2 (lines 175–182), `evaluate.md` Q1 (lines 91–97).

### 3.2. Threat sources (who can influence the blob)

The report (`CorruptedBlobs.md` §1, lines 100–106) identifies five categories:

| # | Source | Mechanism | Adversarial? | Likelihood |
|---|---|---|---|---|
| 1 | **Storage corruption** | Bit-rot, truncated writes, FS errors | No | Low/device; high at fleet scale |
| 2 | **Backup/restore bugs** | Partial restore, version skew | No | Medium |
| 3 | **Cloud sync conflict** | Multi-device state merge | No | Medium |
| 4 | **Malicious local modification** | Rooted device, compromised cloud backup | Yes | Low |
| 5 | **Protobuf version skew** | Future schema change | No | Low |

**Key observation** (§12, lines 787–795): Signal's threat model trusts local storage. The
`from_pb` validation gap is primarily a **non-adversarial robustness** concern (sources
1–3, 5). The adversarial scenarios in §12.1–12.4 are illustrative, not the primary
motivation for the recommended fixes.

### 3.3. Validation gap analysis

Between `SessionStore::load_session` and the downstream chain-key derivation functions, **no
layer performs semantic validation** on the SPQR blob:

| Layer | What it checks | What it does NOT check |
|---|---|---|
| `SessionRecord::deserialize` | Prost wire-format validity | Any field values inside `pq_ratchet_state` |
| `decode_state` (`lib.rs:472`) | Prost wire-format validity | Any field semantics (lengths, ranges, alignment) |
| `Chain::from_pb` (`chain.rs:434`) | Field presence (`Option` unwrap) | `next_root` length, `send_epoch` ordering, `params` ranges |
| `ChainEpochDirection::from_pb` (`chain.rs:306`) | Nothing | `next` length, `prev` alignment, `ctr` range |
| `Authenticator::from_pb` (`authenticator/serialize.rs:16`) | Nothing | `root_key`/`mac_key` lengths |
| `PolyDecoder::from_pb` (`encoding/polynomial.rs:815`) | Nothing | `is_complete` consistency, slot sizes, point counts |

Any entity that can write to the session database can influence every field that the Lean
specifications require as preconditions (`h_next_len`, `h_data_aligned`, `h_key_ge`,
`h_ctr_bound`, etc.).

---

## 4. Relationship to `evaluateSPQR.md` Q1–Q5

| `evaluateSPQR.md` question | Relationship to this evaluation |
|---|---|
| Q1: Does `from_pb` accept semantically invalid state? | **Precondition** for Q‑V1 |
| Q2: Which invariants can be violated? | **Detail** behind Q‑Src |
| Q3: Can such state reach `key`/`get`/`gc`? | **Consequence** of Q‑V1 |
| Q4: Does the consumer panic rather than return `Err`? | **Severity** amplifier |
| Q5: Can the malformed state be persisted and restored? | **Persistence** amplifier |

All five `evaluateSPQR.md` questions are answered (4 fully, Q5 partially by the report and
closed empirically by that evaluation). All three questions in this evaluation are also fully
answered. **No execution plan is needed for any of the eight questions.**

---

## 5. Q3: Can a Remote Attacker Cause the Protobuf Blob or Persisted SPQR State Consumed by `from_pb` to Contain Attacker-Chosen Malformed Fields?

**Answer: No — a purely remote (network-only) attacker cannot directly inject malformed fields into the persisted SPQR state blob consumed by `from_pb`. However, a remote attacker who additionally compromises the storage layer (cloud backup credentials, rooted device, backup-restore supply chain) can.**

### 5.1. Why the Network Path Does Not Reach the Persisted-State `from_pb`

The `from_pb` deserialization path at issue (`Chain::from_pb`, `ChainEpochDirection::from_pb`,
`Authenticator::from_pb`, `PolyDecoder::from_pb`) consumes the **persisted local state blob**
loaded from `SessionStore::load_session` (`traits.rs:152`). This blob is written to the local
session database by the host application after a successful `spqr::send`/`spqr::recv` call
returns an `Ok` with updated state bytes. The write path is:

```
spqr::send/recv → Ok(new_state_bytes) → host stores to SessionStore
```

A remote attacker controls **network messages** (Signal envelope ciphertexts). These messages
are processed by the V1 protocol's `States::from_pb` path, but:

1. **The outer Signal envelope MAC** (`ciphertext.verify_mac`, `session_cipher.rs:657-661`)
   authenticates the message before the host commits any state change. A forged or tampered
   network message fails MAC verification and is rejected — no state update is persisted.

2. **The SPQR-internal authenticator** (`States::from_pb(pb)?.recv()`) performs its own MAC
   check on the SPQR message payload within the envelope.

3. **Even if both MACs were bypassed**, the resulting state update would be the output of
   `spqr::recv` processing the attacker message against the current (valid) local state.
   The `recv` function derives new chain state from the existing state and the message
   content through key derivation — it does not copy attacker-controlled bytes verbatim
   into the persisted chain fields (`next`, `prev`, `ctr`, `next_root`, etc.). The attacker
   cannot choose arbitrary field values via this path.

### 5.2. What a Remote Attacker *Can* Do (Network-Only)

Via Finding 2 (chunk poisoning, `CorruptedBlobs.md` §11), a remote attacker who bypasses
authentication could poison the `PolyDecoder` point sets, causing a permanent epoch stall
(`Err` loop). However, in the deployed V1 protocol this is mitigated by the Signal MAC
auth-before-commit pattern. The attacker **cannot** cause `Chain::from_pb` to load
attacker-chosen `next`, `prev`, `ctr`, `next_root`, `send_epoch`, or `params` values.

### 5.3. Threat Sources That *Can* Inject Malformed `from_pb` Fields

Per `CorruptedBlobs.md` §12 (lines 790–795) and §3.2 of this evaluation, the entities that
can influence the persisted blob are:

| # | Source | Remote? | Adversarial? | Can inject arbitrary field values? |
|---|---|---|---|---|
| 1 | Storage corruption (bit-rot, FS errors) | No | No | Yes (random) |
| 2 | Backup/restore bugs | No | No | Yes (truncation, version skew) |
| 3 | Cloud sync conflict | Partially | No | Yes (merge artifacts) |
| 4 | Compromised cloud backup credentials | **Yes** (remote + storage) | Yes | **Yes** (chosen values) |
| 5 | Rooted/compromised device | No (local) | Yes | **Yes** (chosen values) |
| 6 | Protobuf schema skew | No | No | Yes (misinterpreted fields) |

Only source 4 involves a remote attacker, but it requires **storage-layer compromise** in
addition to network access. A pure network attacker (sources outside this table) cannot
reach the persisted state blob.

### 5.4. Evidence Cross-References

- **Network path separation**: `CorruptedBlobs.md` §11 (lines 751–764), §12 note (lines 790–795)
- **MAC-before-commit**: `CorruptedBlobs.md` §11 (lines 766–783), `evaluateSPQR.md` Q1
- **Probe Q3-5** (`CorruptedBlobs.md` §10.5, line 715): demonstrates that corruption must
  already be *in the persisted blob* — the probe manually corrupts the serialised state and
  then calls `spqr::recv`; the corruption does not originate from a network message
- **Storage-layer threat enumeration**: §3.2 of this evaluation (lines 119–126)

### 5.5. Conclusion

The `from_pb` corrupted-blob vulnerability is **not remotely exploitable via the network
alone**. It is a local-storage robustness defect. The recommended `from_pb` validation
fixes (§14 of `CorruptedBlobs.md`) are valuable for defending against non-adversarial
corruption sources (storage errors, backup bugs) and defense-in-depth against storage-layer
compromise, not for preventing remote network attacks.

---

## 7. Q4 — What Authentication, Integrity Protection, or Validation Is Applied Before `from_pb`?

### 7.1. Threat-Model Table (`CorruptedBlobs.md` §1, lines 90–96)

| Dimension | Network Message (Finding 2) | Corrupted Blob (This Study) |
|---|---|---|
| **Authentication** | Signal envelope MAC covers payload | **None — blob is trusted once loaded** |
| **Integration mitigation** | Auth-before-commit blocks poisoning | **None inside SPQR** |

### 7.2. Production Load Path (`CorruptedBlobs.md` §2.1, lines 167–207)

Traced from on-disk storage through libsignal (`a47ba487`) to SPQR:

- `storage.proto:66`: raw `bytes` field — no MAC/HMAC/signature
- `SessionRecord::deserialize` (`session.rs:663`): prost wire-format only
- `SessionStore::load_session` (`traits.rs:152`): app-provided; no blob content validation
- `SessionState::new` (`session.rs:147,163`): stores bytes verbatim
- `pq_ratchet_recv`/`pq_ratchet_send` (`session.rs:601-617`): calls SPQR directly with zero pre-validation
- All four `from_pb` functions (`ChainEpochDirection`, `Chain`, `Authenticator`, `PolyDecoder`): **zero semantic validation** — return `Ok` for any protobuf-valid input

Host-side: only `is_empty()` check exists (`session.rs:277`).

### 7.3. `decode_state` Source (`lib.rs:472-482`)

```rust
fn decode_state(s: &SerializedState) -> Result<pqrpb::PqRatchetState, Error> {
    if s.is_empty() {
        Ok(proto::pq_ratchet::PqRatchetState { inner: None, version_negotiation: None, chain: None })
    } else {
        proto::pq_ratchet::PqRatchetState::decode(s.as_slice()).map_err(|_| Error::StateDecode)
    }
}
```

Only prost wire-format decoding. No semantic, cryptographic, or integrity check.

### 7.4. MAC Ordering (`CorruptedBlobs.md` §12.2, lines 773–778)

On the recv path, `from_pb` executes **before** the outer Signal envelope MAC check
(`ciphertext.verify_mac`, `session_cipher.rs:657–661`). Any panic fires before the MAC
is verified. The network-level authentication that protects message content does not
protect the stored state blob.

### 7.5. FFI Panic Handling (`CorruptedBlobs.md` §2.1, lines 191–202)

| Bridge | Mechanism |
|---|---|
| C FFI (iOS/Swift) | `run_ffi_safe` / `catch_unwind` → `SignalFfiError::UnexpectedPanic` |
| JNI (Android) | `run_ffi_safe` / `catch_unwind(AssertUnwindSafe(..))` |
| Node (Desktop) | `catch_unwind` on futures; Neon also catches panics |

This is **crash containment**, not validation. Session remains unrecoverable after panic
because libsignal has no code path that resets `pq_ratchet_state` on error.

### 7.6. Summary of Protections Before `from_pb`

| Protection Type | Present? | Detail |
|---|---|---|
| Cryptographic auth (MAC/HMAC/sig) | **No** | Blob is raw `bytes` with no MAC |
| Integrity check (checksum/CRC) | **No** | Neither libsignal nor SPQR verifies one |
| Schema/semantic validation | **No** | Only prost wire-format; all `from_pb` accept any protobuf-valid input |
| OS-level access control | Platform-dependent | Android Keystore / iOS Keychain — outside SPQR boundary |
| Panic containment (defense-in-depth) | **Yes** | FFI bridges catch panics — reactive, not preventive |

### 7.7. Conclusion

**No authentication, no integrity protection, and no semantic validation exist on the
path from storage to `from_pb`.** The only check is prost wire-format decoding, which
rejects malformed protobuf but accepts any protobuf-valid-but-semantically-invalid blob.
The recommended `from_pb` validation fixes (`CorruptedBlobs.md` §14) would close this gap.

---

## 9. Q5: Can an Attacker-Controlled Malformed State Survive V1 Processing and Become Persisted SPQR State?

**Answer: Yes.** Malformed state survives V1 processing and becomes persisted SPQR state
through three independent mechanisms, all confirmed by compiled-Rust probes and (partially)
by Lean mechanisation.

### 9.1. Three-Sense Persistence Model (`CorruptedBlobs.md` §13, lines 893–928)

Corruption persists in three distinct senses:

1. **Reload after panic (host policy).** A panicking `send()`/`recv()` never returns a new
   `state`, so libsignal keeps the pre-call blob and reloads it on the next call. This is
   host behaviour (no code path in libsignal resets `pq_ratchet_state` on error), but SPQR
   enables it by accepting the corrupted blob again via `from_pb` on every reload.

2. **Identity round-trip (SPQR).** `into_pb ∘ from_pb` is the identity on every blob
   `from_pb` accepts — corrupted or not — at all four layers (`ChainEpochDirection`,
   `Chain`, `Authenticator`, `PolyDecoder`) and through the prost wire encoding. No
   normalisation or sanitisation occurs. Mechanised for `ChainEpochDirection` (Phase 5,
   `corrupted_state_roundtrips`); confirmed byte-for-byte for all ten §3/§7 corruption
   classes (probe Q5‑1) and for `Authenticator`/`PolyDecoder` (probe Q5‑4).

3. **Propagation through a successful call (SPQR).** A corrupted blob can be loaded, used
   with an `Ok` result, and written back **still corrupted** into the `state` the caller
   persists. `spqr::send`/`recv` unconditionally re-encode `chain.into_pb()` (`lib.rs:301,
   313, 443`), so whatever `Chain::from_pb` accepted and the operation did not touch is
   re-serialised verbatim. This defeats any host-side "roll back to last good state"
   strategy and lets corruption survive backups or reach other devices via state sync.

### 9.2. Identity Round-Trip Evidence

| Layer | Mechanised? | Runtime evidence |
|---|---|---|
| `ChainEpochDirection` | **Yes** — Phase 5 (`corrupted_state_roundtrips`) | Q5‑1 (10 mutations, byte-for-byte) |
| `Chain` | **No** — `Chain::into_pb` is `#[hax_lib::opaque]` (`chain.rs:414`) | Q5‑1 (10 mutations, byte-for-byte) |
| `Authenticator` | **No** | Q5‑4 (`root_key: 5 B, mac_key: []` round-trips) |
| `PolyDecoder` | **No** | Q5‑4 (`is_complete: true, pts: 16 × []` round-trips) |

### 9.3. Propagation Through Successful Calls

Two probes demonstrate end-to-end propagation through `Ok` returns:

- **Q5‑2** (`Chain` level): `recv.ctr = 5`, `recv.prev = 37 B` (misaligned). In-order
  `recv_key(0, 7)` returns `Ok(32-byte key)`. The resulting `into_pb()` shows `ctr = 7`,
  `prev.len() = 73` — still `% 36 ≠ 0`. Reloading succeeds; the next out-of-order
  `recv_key(0, 1)` panics at L191.

- **Q5‑3** (public API): Two real round-trips via `spqr::send`/`spqr::recv`, then corrupt
  `recv.prev = [0; 1]` on the persisted blob. Peer sends one in-order message.
  `spqr::recv(&corrupted, &msg)` returns **`Ok`**, the derived key equals the peer's send
  key (corruption is invisible to the protocol), and the **returned `state`** decodes to a
  chain whose `recv.prev` is still misaligned. The host would persist this as the new good
  state.

### 9.4. Immediate vs Latent Persistence

| Corruption class | Immediate crash? | Latent propagation? |
|---|---|---|
| `next.len() ≠ 32` (§4) | Yes — next in-order message | No — panic before `Ok` |
| Small `ctr` + large `prev` (§6) | Yes — next in-order message | No — panic before `Ok` |
| Misaligned `prev` (§5) | No — only OOO or GC trigger | **Yes** — in-order messages succeed and re-persist corruption (Q5‑2, Q5‑3) |
| `ctr` near `u32::MAX` (§3) | Debug: yes; Release: no | **Yes (release)** — wrapping arithmetic, round-trips unchanged (Q5‑1) |
| `next_root.len() ≠ 32` (§7) | No — `Ok` with wrong keys | **Yes** — silent divergence, re-persisted on every call |
| `Authenticator` key lengths (§8) | No — `Ok` with weak MAC | **Yes** — round-trips unchanged (Q5‑4) |
| `PolyDecoder::is_complete` (§9) | No — silent stall | **Yes** — round-trips unchanged (Q5‑4) |

### 9.5. Conclusion

**An attacker-controlled malformed state unequivocally survives V1 processing and becomes
persisted SPQR state.** The `from_pb` path performs zero semantic validation, `into_pb`
performs zero normalisation, and the public API unconditionally re-serialises the chain on
every successful call. The three persistence senses (reload-after-panic, identity
round-trip, propagation-through-`Ok`) are independent and compound: a latent corruption
like misaligned `prev` propagates through successful calls (sense 3), round-trips
byte-for-byte on reload (sense 2), and — once the deferred panic finally fires — remains
stuck in the crash loop (sense 1). The recommended fix (`CorruptedBlobs.md` §14) is to
validate semantic invariants in every `from_pb` function, converting the Lean
specification's structural hypotheses into checked postconditions.

---

## 10. Q6: Can Persisted State Subsequently Reach the Affected SPQR Operations?

**Question**: Can that persisted state subsequently reach the affected SPQR operation
(recv, send, key, get, or gc) during normal V1 operation?

**Answer: Yes — unequivocally.**

### 10.1. Call-chain Reachability (source reading)

Every subsequent `spqr::send` or `spqr::recv` call in a V1 session reloads persisted state
through `decode_state` → `Chain::from_pb` (§2.1). The loaded `Chain` is then consumed by
the operation's core logic:

| Public entry | Internal consumer | Affected functions |
|---|---|---|
| `spqr::recv` (`lib.rs:356`) | `recv_key(epoch, index)` → `key(at)` | `next_key_internal` (L229, L243), `KeyHistory::get` (L191), `KeyHistory::gc` (L149, L157) |
| `spqr::send` (`lib.rs:238`) | `send_key(epoch)` → `key(at)` | `next_key_internal` (L229, L243) |

There is **no validation gate** between `from_pb` and the consumer: the `Chain` returned by
`from_pb` is used directly. The Lean specifications expose this as unsatisfiable
preconditions on `recvKeyPre` (`Spqr/Specs/Chain/Chain/Defs.lean:95-106`) — the structural
invariants required by `key`/`get`/`gc` are never established by `from_pb`.

### 10.2. Runtime Confirmation

The compiled-Rust probes in `CorruptedBlobs.md` §10.5 demonstrate end-to-end reachability
from persisted-blob corruption to each panic site:

| Probe | Corruption | Reached operation | Panic site |
|---|---|---|---|
| Q3‑1 | `recv.next = [0; 31]` | `recv_key` → `next_key_internal` | L243 (`copy_from_slice`) |
| Q3‑2 | `recv.prev = [0; 37]` | `recv_key` → `get` | L191 (`assert_eq!`) |
| Q3‑3 | `recv.prev = [0; 79236]`, `ctr = 0` | `recv_key` → `gc` | L149 (`assert!`) |
| Q3‑4 | `send.next = []` | `send_key` → `next_key_internal` | L229 (`assert!`) |
| Q3‑5 | Full public-API round-trip with corrupted blob | `spqr::recv` | L243 |
| Q4‑2 | Misaligned large `prev`, `ctr = 5000` | `recv_key` → `gc` | L157 (slice index OOB) |

Probe **Q3‑5** is particularly significant: it demonstrates the full production path —
`PqRatchetState::decode` → `States::from_pb` → `Chain::from_pb` → `spqr::recv` →
`recv_key` → panic — with no intervening check at any layer.

### 10.3. Attack Scenarios

`CorruptedBlobs.md` §§12.1–12.4 present four concrete scenarios where persisted corruption
reaches the affected operations during normal V1 use:

1. **§12.1 — Targeted Session Kill via Backup Modification**: Corrupted `recv.next` →
   next incoming message triggers `recv_key` → panic at L243.
2. **§12.2 — Latent Time-Bomb via `prev` Misalignment**: Misaligned `prev` survives
   in-order messages (forward path in `key()` never inspects alignment), propagates through
   `Ok` returns, and detonates on the first out-of-order message (`get`, L191) or when
   `prev` grows past `trim_size()·36` (`gc`, L157).
3. **§12.4 — GC Panic via Counter/History Mismatch**: `ctr = 0` with oversized `prev` →
   next `recv()` with `index = 1` → `gc` → panic at L149.
4. **§12.3** (implicit): `send.next = []` on an active send epoch → next `send()` → panic
   at L229.

### 10.4. Lean Mechanisation

`Spqr/Specs/Bugs/CorruptedBlobs.lean` Phases 1–5 and 9–10 prove that `from_pb` returns
`Ok` on corrupted inputs *and* that the subsequent `key` call has no successful execution
(the Aeneas model of a Rust panic). This is the machine-checked negative form of the
reachability claim: `from_pb pb = Ok ced → ∀ r, key ced at params ≠ ok r`.

### 10.5. Conclusion

**Persisted corrupted state reaches every affected SPQR operation (recv, send, key, get,
gc) during normal V1 operation.** The path from persisted blob to consumer is a straight
line: `decode_state` → `from_pb` → `{recv,send}_key` → `key` → `{next_key_internal, get,
gc}`, with zero validation gates. This is confirmed by source reading, 10+ compiled-Rust
probes across both debug and release profiles, four concrete attack scenarios, and
machine-checked Lean theorems. No further execution plan is needed for this question.

---

## 11. Residual Gaps (proof-coverage, not unanswered questions)

These are acknowledged by `CorruptedBlobs.md` §10.4 (lines 676–688) and `evaluateSPQR.md`
§4.2 (G1–G14):

| Gap | Detail | Affects |
|---|---|---|
| `decode_state` round-trip `sorry` | Prost `Message` impl opaque in Lean (`defects.md:450–453`) | Formal blob↔struct boundary |
| I4, I7–I11, I15 not mechanised | Prose + runtime probes only | Q2 evidence strength |
| L157 (`gc` slice-index) not mechanised | Confirmed by probe Q4‑2 | Q4 evidence for one panic site |
| Round-trip mechanised for 1/4 layers | Phase 5 covers `ChainEpochDirection` only; probes Q5‑1/Q5‑4 cover all four | Q5 formal evidence |
| `Chain::into_pb` is `#[hax_lib::opaque]` | Cannot extract round-trip theorem (`chain.rs:414`) | Formal round-trip at `Chain` layer |

All defects are confirmed by compiled-Rust probes and source reading regardless of
mechanisation status.

---

## 12. Q7: What Security-Relevant Effect Does Triggering the Corrupted State Have on the V1 Session or Endpoint?

### 12.1. Failure-Mode Taxonomy

Triggering a corrupted state blob in a V1 session produces four distinct classes of
security-relevant effect, confirmed by compiled-Rust probes and source reading
(`CorruptedBlobs.md` §§3–9, §10.5):

| Effect class | Corrupted fields | Security impact |
|---|---|---|
| **Deterministic panic (DoS)** | `recv.next` (len ≠ 32), `send.next = []`, misaligned `prev`, large `prev`, small `ctr` + large `prev` | **Session permanently bricked** — panic at L149/L157/L191/L229/L243; FFI bridges catch via `catch_unwind` but libsignal has no path to reset `pq_ratchet_state` (`CorruptedBlobs.md` §2.1). Crash loop on every subsequent call. |
| **Profile-dependent panic / silent wrap** | `ctr` near `u32::MAX` | Debug: panic. Release: `u32` wraps silently → **wrong key index**, potential key reuse. |
| **Graceful `Err`** | `send_epoch > current_epoch`, empty `links` | Recoverable — session **not** killed. |
| **`Ok` but wrong semantics** | `next_root` (len ≠ 32), `Authenticator` keys, `PolyDecoder::is_complete`, oversized `trim_size` | Silent: epoch-key divergence, weakened MAC, stalled decoder, disabled GC (weakened forward secrecy). |

### 12.2. Session-Recovery Analysis

No recovery path exists inside SPQR or libsignal for the panic cases:

- **SPQR** has no `reset()` or fallback. `from_pb` returns `Ok` on corrupted input,
  so corruption is invisible until it reaches the consumer.
- **libsignal** stores `pq_ratchet_state` as opaque `Option<Box<[u8]>>`. When
  `spqr::recv`/`send` panics, `catch_unwind` catches it, but the corrupted state
  remains — the next call reloads the same blob and panics again (crash loop).
- **Only recovery**: host deletes the session and performs new key agreement (user-visible
  session reset, queued messages lost).

### 12.3. Security-Property Impact

| Property | Impact | Severity |
|---|---|---|
| **Availability** | Deterministic panic permanently kills the session. Endpoint unaffected (other sessions continue). | **HIGH** (session) |
| **Confidentiality** | Release-profile counter wrap → wrong-key derivation; wrong-length `next_root` → epoch-key divergence; short `Authenticator` keys → weakened MAC. | **LOW–MEDIUM** (conditional) |
| **Integrity** | Weakened MAC keys reduce forgery resistance. Silent `Ok` on wrong-semantics fields hides the violation. | **LOW–MEDIUM** (conditional) |
| **Forward secrecy** | Disabled GC (oversized `trim_size`) → old keys never deleted. | **LOW** (requires `params` corruption) |

### 12.4. Evidence Synthesis

Q7 is supported by: (1) source reading (`CorruptedBlobs.md` §§3–9, §2.1); (2) probes
Q3‑1–Q3‑5, Q4‑1–Q4‑3 confirming every panic site in both profiles; (3) Lean Phases 1–5,
9–10 proving `from_pb` accepts corruption and `key` has no successful execution; (4) probes
Q5‑2/Q5‑3 demonstrating corruption propagation through `Ok` returns.

### 12.5. Conclusion

**Three security-relevant effects, ranked by severity:**

1. **Session-level DoS (HIGH for session, MEDIUM overall)**: Five panic sites cause
   deterministic, permanent session death with no recovery inside SPQR or libsignal.
2. **Silent cryptographic degradation (LOW–MEDIUM)**: Wrong-length roots, counter wrap,
   weakened MACs, and disabled GC degrade security properties invisibly.
3. **Propagation amplification**: Corrupted state surviving `Ok` paths is re-persisted
   as authoritative state, spreading corruption across restarts.

The primary threat is non-adversarial (disk corruption, backup bugs), but a local attacker
with database write access can selectively kill or degrade specific conversations.

---

## 13. Q8: Can the Attacker Trigger This Effect Remotely and Repeatedly Without Local Access to the Victim's Persisted State?

**Answer: No. A purely remote (network-only) attacker cannot trigger the corrupted-blob
effects. Local or storage-layer access is required. However, once the corruption is present,
the effect repeats automatically on every subsequent call — no further attacker action is
needed.**

### 13.1. Why Remote-Only Attackers Cannot Reach the Persisted State

The corrupted-blob class targets the **state-loading path** (`decode_state` → `Chain::from_pb`),
not the **message-processing path**. These are architecturally separated:

- **Network messages** enter via `States::from_pb(pb)?.recv()` in the V1 protocol. In the
  deployed integration, every inbound message passes through Signal's MAC-before-commit
  pattern: the outer envelope MAC (`ciphertext.verify_mac`, `session_cipher.rs:657-661`)
  authenticates the ciphertext before the ratchet state is committed. A remote attacker
  who does not possess the session's MAC key cannot get an unauthenticated message past
  this check.

- **Persisted state blobs** are loaded from the host's local session store
  (`IdentityKeyStore` / `SessionStore`) and passed to `decode_state` → `Chain::from_pb`.
  No network message flows through this path. The only way to inject malformed fields into
  the persisted blob is to modify the local database directly.

This separation is documented in `CorruptedBlobs.md` §11 (comparison table: "Attack vector:
Local storage" vs "Network message") and §12 (attack scenarios, each of which explicitly
requires local database or backup access).

### 13.2. Threat-Source Analysis

From the threat-source table (§5.3 of this document, `CorruptedBlobs.md` §12):

| Source | Remote? | Requires local/storage access? | Can inject arbitrary fields? |
|---|---|---|---|
| 1. Storage-layer bit-rot / disk error | No | N/A (non-adversarial) | Yes (random corruption) |
| 2. Truncated write / crash during persist | No | N/A (non-adversarial) | Yes (truncated blob) |
| 3. Backup/restore bugs | No | N/A (non-adversarial) | Yes (schema skew, missing fields) |
| 4. Attacker with backup credentials | Partially | **Yes** — cloud or physical storage access | Yes (targeted field replacement) |
| 5. Rooted/jailbroken device | No | **Yes** — full local access | Yes |
| 6. Protobuf schema skew (version mismatch) | No | N/A (non-adversarial) | Yes (misinterpreted fields) |

No source enables a **purely remote** attack. Source 4 involves a remote component (cloud
backup access) but still requires compromised storage credentials — it is not achievable
through the Signal network protocol alone.

### 13.3. Why the Effect Repeats Without Further Action

Although the attacker cannot trigger the corruption remotely, once corruption is present
(from any source), **no further attacker action is required** for the effect to repeat:

1. **Panic cases** (§12.1): `from_pb` returns `Ok` on the corrupted blob, but the next
   `send()`/`recv()` panics. The panic never returns a new state, so the host keeps the
   old (corrupted) blob. Every subsequent call reloads the same blob and panics again —
   a permanent crash loop (`CorruptedBlobs.md` §13, probes Q5‑1–Q5‑3).

2. **Silent-corruption cases** (§12.1, "Ok but wrong semantics"): The corrupted blob
   passes through successfully, the wrong-semantics result is re-persisted as the new
   authoritative state (probe Q5‑3), and the degradation continues indefinitely.

In both cases the corruption is **self-sustaining** after the initial injection event.

### 13.4. Conclusion

The corrupted-blob attack surface is **not remotely exploitable** through the Signal network
protocol. The Signal integration's MAC-before-commit pattern and the architectural separation
between the message-processing and state-loading paths prevent a network-only attacker from
injecting malformed fields into the persisted state. The realistic threat sources are
non-adversarial (storage corruption, backup bugs, schema skew) or require local/storage-layer
compromise. Once corruption is present, however, it persists and repeats autonomously — no
ongoing attacker access is needed to sustain the denial-of-service or silent degradation.

---

## 14. Conclusion

This evaluation comprehensively answers all eight questions (Q‑V1, Q‑Src, Q3–Q8) regarding
the V1 protocol's `from_pb` deserialization path and corrupted-blob provenance. The findings
are summarised below.

### 14.1. The Vulnerability Is Real and Mechanically Confirmed

The deployed V1 protocol exercises the affected `from_pb` path on **every** `spqr::send` and
`spqr::recv` call after the first operation in a session (§2). Six `from_pb` functions
(`Chain`, `ChainEpochDirection`, `Authenticator`, `PolyDecoder`, `PolyEncoder`, and
`States`) perform **zero semantic validation** on the blob loaded from the host's session
store (§3.3). The Lean mechanisation (Phases 1–5, 9–10) proves that `from_pb` admits states
whose structural invariants are violated, and that no successful execution of `recv_key` or
`send_key` exists for those states. Compiled-Rust probes (Q3‑1–Q3‑5, Q4‑1–Q4‑3, Q5‑1–Q5‑4)
confirm every panic site and silent-corruption path in the compiled binary.

### 14.2. The Vulnerability Is Not Remotely Exploitable via the Network Alone

Signal's MAC-before-commit pattern and the architectural separation between the
message-processing path and the state-loading path prevent a network-only attacker from
injecting malformed fields into the persisted SPQR state (§5, §13). The realistic threat
sources are non-adversarial (storage corruption, backup/restore bugs, protobuf schema skew)
or require local/storage-layer compromise (rooted device, compromised cloud backup
credentials).

### 14.3. Corrupted State Persists and Repeats Autonomously

Once corruption enters the persisted blob — from any source — it is **self-sustaining** (§9,
§13.3):

- **Panic cases**: `from_pb` returns `Ok`, the next consumer panics, no new state is
  returned, the host reloads the same corrupted blob — a permanent crash loop.
- **Silent-corruption cases**: The corrupted blob passes through with `Ok` but wrong
  semantics, the wrong-semantics result is re-persisted as the new authoritative state,
  and the degradation continues indefinitely.
- **Identity round-trip**: `into_pb ∘ from_pb` is the identity on every blob `from_pb`
  accepts — no normalisation or sanitisation occurs at any layer.

### 14.4. Security Impact Summary

| Property | Impact | Severity |
|---|---|---|
| **Availability** | Deterministic panic permanently kills the session (five panic sites). | **HIGH** (session) |
| **Confidentiality** | Counter wrap → wrong-key derivation; wrong-length `next_root` → epoch-key divergence; short `Authenticator` keys → weakened MAC. | **LOW–MEDIUM** (conditional) |
| **Integrity** | Weakened MAC keys reduce forgery resistance. Silent `Ok` on wrong-semantics fields hides the violation. | **LOW–MEDIUM** (conditional) |
| **Forward secrecy** | Disabled GC (oversized `trim_size`) → old keys never deleted. | **LOW** (requires `params` corruption) |

### 14.5. Recommended Fix

The recommended mitigation (`CorruptedBlobs.md` §14) is to validate semantic invariants in
every `from_pb` function, converting the Lean specification's structural hypotheses
(`h_next_len`, `h_data_aligned`, `h_key_ge`, `h_ctr_bound`, etc.) into checked
postconditions that return `Err` on violation rather than silently admitting corrupted state.
This eliminates all five panic sites, all silent-corruption paths, and the
persistence-amplification mechanism in a single, localised change.

### 14.6. Status

All eight questions are **fully answered** with high confidence. Evidence spans four
independent methodologies: (1) source-level call-chain reading, (2) compiled-Rust runtime
probes, (3) Lean mechanised proofs, and (4) libsignal integration-layer tracing. **No
further execution plan is needed.**
