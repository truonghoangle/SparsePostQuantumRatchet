# Unvalidated Deserialized State Blobs in SPQR

**Analysed version**: spqr `v1.5.0` (`Cargo.toml`), as consumed by libsignal commit
`a47ba487` (2026‑03‑17). All `chain.rs` / `lib.rs` line numbers refer to this tree.
**Document revision**: 2026‑09‑26 (consolidated rewrite; see Appendix D for history).

---

## Executive Summary

Every `from_pb` function on SPQR's persistence path accepts any protobuf-decodable input
without checking the semantic invariants that its consumers rely on. The Lean specifications
make this gap visible: `recv_key_spec` needs `h_next_len`, `h_data_aligned`, `h_prev_ctr`,
`h_key_ge`, … as *hypotheses*, and nothing in `Chain::from_pb` /
`ChainEpochDirection::from_pb` establishes them.

The result is that a **wire-valid but semantically inconsistent persisted state blob**
turns the next `send()` / `recv()` into a `panic!` (five sites in `src/chain.rs`), rather
than a graceful `Err(StateDecode)`. Some other malformed fields do not panic but produce
silently wrong behaviour (`next_root` length → key divergence; `PolyDecoder::is_complete`
→ permanent stall).

**Three questions, three answers**:

| Question | Answer | Where |
|---|---|---|
| Does SPQR accept and then crash on a corrupted *local* blob? | **Yes.** Five panic sites, all reached from the public `spqr::recv()`/`spqr::send()`; corruption round-trips byte-for-byte and can be re-persisted by an `Ok` call. | Part I |
| Can a *remote* attacker cause an SPQR-invalid value to be persisted, without storage access? | **No** for every panic-class field (`next`, `prev`, `next_root`, `params`); they are KDF-derived. **Yes, but harmless in practice** for the `ctr` counter — an *authenticated* peer can steer it past the Lean proof bound in ≈156 K messages, and to the real `u32` overflow zone in ≈172 K messages, where the effect is self-DoS of the attacker's own send direction. | Part II, §14 |
| Can a remote *authenticated* peer persist attacker-*chosen* (rather than SPQR-invalid) state? | **Yes** — chunk bytes are stored verbatim in `PolyDecoder` before any SPQR MAC runs, and one replayed chunk permanently stalls the epoch. This re-opens `report.md` Finding 2 for the authenticated-peer attacker class. | Part II, §15 |

**Severity**: **MEDIUM** for the local-blob class (denial of service of one session, no
recovery path inside SPQR; primary threat is non-adversarial: backup/restore bugs, schema
skew, truncated writes). **LOW** for `ctr` steering. **MEDIUM** for authenticated chunk
poisoning (silent loss of PQ forward secrecy/healing, tracked as an amendment to Finding 2).

**Host behaviour** (libsignal): all three bridges (C FFI, JNI, Node) wrap calls in
`catch_unwind`, so a panic surfaces as `UnexpectedPanic`, not a process abort. But libsignal
never resets `pq_ratchet_state` on error, so the same blob is reloaded on the next call and
the session is effectively bricked until the app archives it.

**Fix in one sentence**: make every blob-derived conjunct of `recvKeyPre`
(`Spqr/Specs/Chain/Chain/Defs.lean:95-106`) a checked postcondition of `Chain::from_pb`
(§16), guard the `ctr + max_ooo` addition in `key()` with `checked_add` (§16.5), and — for
the `ctr` check specifically — use the runtime bound `ctr + max_ooo ≤ u32::MAX`, **never**
the Lean slack constant `u32::MAX − 390451572` (§16.5 explains why the latter would make
things worse).

**Evidence**: source reading (`src/chain.rs`, `src/lib.rs`), 46 machine-checked theorems in
`Spqr/Specs/Bugs/CorruptedBlobs.lean` (Appendix B), and 27 compiled-Rust probes executed in
both `debug` and `release` (Appendix C). Every panic site, every graceful-`Err` case, every
profile-dependent overflow and every round-trip claim in this document has a probe.

---

## Table of Contents

**Part I — Local Corrupted Blobs**
1. [Threat Model](#1-threat-model)
2. [The Persistence Boundary](#2-the-persistence-boundary)
3. [Primary Defect: `ChainEpochDirection::from_pb`](#3-primary-defect-chainepochdirectionfrom_pb)
4. [Panic Sites](#4-panic-sites)
5. [Secondary Defect: `Chain::from_pb`](#5-secondary-defect-chainfrom_pb)
6. [Tertiary Defect: `Authenticator::from_pb`](#6-tertiary-defect-authenticatorfrom_pb)
7. [Quaternary Defect: `PolyDecoder::from_pb`](#7-quaternary-defect-polydecoderfrom_pb)
8. [Lean Specification Evidence](#8-lean-specification-evidence)
9. [Runtime Evidence](#9-runtime-evidence)
10. [Failure-Mode Taxonomy](#10-failure-mode-taxonomy)
11. [Local Attack Scenarios](#11-local-attack-scenarios)
12. [Persistence of Corruption](#12-persistence-of-corruption)
13. [Impact Assessment](#13-impact-assessment)

**Part II — Remote Reachability**
14. [Can a Remote Peer Persist an SPQR-Invalid Value?](#14-can-a-remote-peer-persist-an-spqr-invalid-value)
15. [Attacker-Chosen Persisted State (Finding 2 Revisited)](#15-attacker-chosen-persisted-state-finding-2-revisited)

**Part III — Fixes**
16. [Recommended Fixes](#16-recommended-fixes)

**Appendices**
- [A. Invariant → Fix Traceability](#appendix-a-invariant--fix-traceability)
- [B. Lean Theorem Index](#appendix-b-lean-theorem-index)
- [C. Probe Index](#appendix-c-probe-index)
- [D. Revision History](#appendix-d-revision-history)

---

# Part I — Local Corrupted Blobs

## 1. Threat Model

| Property | Network message (Finding 2, `report.md`) | Corrupted blob (this study) |
|---|---|---|
| Entry point | `Message::deserialize` (wire) | `decode_state` → `from_pb` (storage) |
| Authentication | Signal envelope MAC over payload | None — the blob is trusted once loaded |
| Attacker capability | Forge/replay network messages | Modify local storage (disk, backup, cloud sync) |
| Mitigation | Auth-before-commit (unauthenticated attackers only, see §15) | **None inside SPQR**; host catches the panic (§2.1) but cannot recover the session |
| Failure mode | Permanent epoch stall | Panic / silent divergence / stall, per §10 |

Concrete sources of a semantically corrupted but prost-decodable blob:

1. **Backup/restore and schema skew** — restoring an older or partially written blob, or a
   future schema producing fields with different length conventions. *This is the realistic
   non-adversarial source.*
2. **Truncated / torn writes** — a length-prefixed `bytes` field cut short.
3. **Cloud sync conflict** — merge artefacts across devices.
4. **Random bit-rot** — possible but narrow: most single-bit flips either break prost decoding
   (already `Err(StateDecode)`) or flip a key byte (wrong key, `Ok`). Only flips in a length
   varint produce the `next.len() ≠ 32` / misaligned-`prev` class analysed here, and an
   encrypted-at-rest session store typically fails authentication before SPQR sees the blob.
5. **Malicious local modification** — rooted device, compromised cloud backup credentials.
   Such an attacker can already delete the session or read ratchet keys; the panics add
   little. The fixes in Part III are therefore justified by **robustness**, not by defence
   against a local attacker.

---

## 2. The Persistence Boundary

```
 Local storage (protobuf blob)
        │  decode_state() / from_pb()          ← prost wire-validity only, NO semantic checks
        ▼
 In-memory Chain / Authenticator / PolyDecoder
        │  send() / recv()
        ▼
 next_key_internal / KeyHistory::get / KeyHistory::gc   ← PANICS HERE
```

Entry point, `src/lib.rs:472`:

```rust
fn decode_state(s: &SerializedState) -> Result<pqrpb::PqRatchetState, Error> {
    if s.is_empty() {
        Ok(proto::pq_ratchet::PqRatchetState { inner: None, version_negotiation: None, chain: None })
    } else {
        proto::pq_ratchet::PqRatchetState::decode(s.as_slice()).map_err(|_| Error::StateDecode)
    }
}
```

`Chain::from_pb` (`chain.rs:434`) is reached from three call sites, and bypassed only on the
very first `send`/`recv` of a session (`chain == None`, fresh `Chain::new`):

| Path | Call | Consumer |
|---|---|---|
| recv | `chain_from(state_pb.chain, …)` `lib.rs:343-348` → `Chain::from_pb` | `chain.recv_key(epoch, index)` `lib.rs:435` |
| send | `Chain::from_pb(pb)` `lib.rs:288` | `chain.send_key(epoch)` |
| recv, version-downgrade branch | `chain_from(prenegotiated_state_pb.chain, …)` `lib.rs:401-405` | as recv |

`Chain::from_pb` then calls `ChainEpochDirection::from_pb` (`chain.rs:306`) for every
link's `send` and `recv`. `Authenticator::from_pb` (`authenticator/serialize.rs:16`) and
`PolyDecoder::from_pb` (`encoding/polynomial.rs:815`) are reached via
`States::from_pb` on the V1 inner state.

### 2.1. Host (libsignal) behaviour

| Aspect | Location (libsignal `a47ba487`) | Behaviour |
|---|---|---|
| Recv caller | `rust/protocol/src/session_cipher.rs:633-647` | `decrypt_message_with_state` → `pq_ratchet_recv`; `spqr::Error::StateDecode` → `SignalProtocolError::InvalidState`, other errors → `InvalidMessage` |
| Send caller | `session_cipher.rs:37-43` | `message_encrypt` → `pq_ratchet_send`; any error → `InvalidState` |
| Ordering | `session_cipher.rs:599-694` | SPQR `recv` runs at L633, *after* Double-Ratchet key derivation and *before* the outer envelope MAC check (`ciphertext.verify_mac`, L657-661). A panic in `spqr::recv` therefore fires before the MAC is checked. |
| State commit | `session_cipher.rs:455,475` | `decrypt_message_with_state` works on a **clone**; the clone is committed only if the whole function returns `Ok`. |
| C FFI (iOS) | `rust/bridge/shared/types/src/ffi/mod.rs:399-413` | `run_ffi_safe` → `catch_unwind` → `SignalFfiError::UnexpectedPanic` |
| JNI (Android) | `rust/bridge/shared/types/src/jni/mod.rs:1148-1157` | `run_ffi_safe` with `catch_unwind(AssertUnwindSafe(..))` |
| Node (Desktop) | `rust/bridge/shared/types/src/node/futures.rs:104-204` | `catch_unwind` on futures; Neon also catches panics |
| Host-side inspection of the blob | `session.rs:277` (`is_empty()`), `session.rs:619` (opaque accessor) | No semantic validation |
| Recovery on error | — | **None.** No code path resets `pq_ratchet_state` on `InvalidState` or `UnexpectedPanic`; only app-level session archival helps. (Source inspection, `docs/evaluate.md` Q7.) |

Consequences: panics do not abort the process, but because the failed call never returns a
new `state`, the host keeps the old blob and the same panic recurs on every subsequent
message for that session.

---

## 3. Primary Defect: `ChainEpochDirection::from_pb`

`src/chain.rs:306-312`:

```rust
fn from_pb(pb: pqrpb::chain::epoch::EpochDirection) -> Result<Self, Error> {
    Ok(Self {
        ctr: pb.ctr,
        next: pb.next,
        prev: KeyHistory { data: pb.prev },
    })
}
```

No validation at all. The consumers require the following invariants (numbering I1–I16 is
shared with Appendix A and `docs/evaluateSPQR.md` §3):

| # | Invariant | Required by | Lean hypothesis | Failure when violated |
|---|---|---|---|---|
| I1 | `next.len() == 32` on every direction that `send_key`/`recv_key` can reach (`recv` always; `send` at/after the send epoch). Pre-send-epoch `send` directions legitimately have `next = []` after `clear_next()` (`chain.rs:314-316`, called from `send_key` L396-399). | `next_key_internal` L228-244 | `NextKeyInternal.lean` `h_next_len : next.length = 32` | **panic**: `next = []` → `assert!` L229; `0 < len ≠ 32` → `copy_from_slice` L243 |
| I2 | `prev.len() % 36 == 0` | `KeyHistory::get` L191; `KeyHistory::gc` L157 | `Get.lean` / `Gc.lean:85` `h_data_aligned` | **panic**: `assert_eq!` L191 (out-of-order path); slice index L157 (forward path, once `prev` reaches the GC threshold) |
| I3 | `prev.len() ≤ 36 · ctr` (each stored index is `< ctr` and stored once) | `KeyHistory::gc` L149 | `Key.lean` `h_prev_ctr` → `Gc.lean` `h_key_ge` | **panic**: `assert!(current_key >= max_ooo)` L149 |
| I4 | `ctr + max_ooo_keys_or_default() ≤ u32::MAX` (runtime bound). The Lean specs use the weaker slack constant `ctr ≤ u32::MAX − 390451572` (`Key.lean` `h_ctr_bound`; `Key32.lean` uses `108458770`), chosen so the arithmetic lemmas close for any `max_ooo < 390451572 = ⌊u32::MAX/11⌋`. **The Lean constant is not the runtime threshold** — see §14.3. | `key()` L265, L279 | `Key.lean` `h_ctr_bound`, `h_ctr_lt` | **debug/test builds**: `attempt to add with overflow` panic at L265/L279. **release**: silent wrap (no `overflow-checks` override in `Cargo.toml`) → wrong `prev.clear()` / `add` decision |

The I4 addition is guarded only by `hax_lib::assume!` (L262-264, L275-277) — a proof
obligation handed to hax, not a runtime check.

---

## 4. Panic Sites

All five sites are in `src/chain.rs`. Each is reachable from the public API after a
corrupted blob passes `Chain::from_pb`; the call chain is always
`spqr::recv()` `lib.rs:356` → `chain_from` → `Chain::from_pb` → `chain.recv_key()` `lib.rs:435`
→ `links[idx].recv.key(index, params)` `chain.rs:411` → one of the functions below (or, for
the send route, `spqr::send()` → `send_key` → `next_key` → `next_key_internal`).

### 4.1. `next_key_internal` — L229 and L243 (I1)

```rust
fn next_key_internal(next: &mut [u8], ctr: &mut u32) -> (u32, [u8; 32]) {
    assert!(!next.is_empty());                       // L229
    *ctr += 1;
    let mut genr8r = [0u8; 64];
    kdf::hkdf_to_slice(&[0u8; 32], &*next, /* ... */, &mut genr8r);
    next.copy_from_slice(&genr8r[..32]);             // L243 — panics if next.len() ≠ 32
    (*ctr, genr8r[32..].try_into().expect("correct size"))
}
```

Reached from `key()` on the forward path (`ctr < at ≤ ctr + max_jump`), both inside the
advancing loop (L274) and for the final key (L293). The loop cannot repair a wrong-length
`next` (`key_loop_preserves_next_length`). Regression tests must attribute the site
correctly: `next = []` → L229; `next.len() ∉ {0, 32}` → L243.

**Probes**: Q3‑1 (`recv.next = [0; 31]` → L243), Q4‑1 (`recv.next = []` → L229), Q3‑4
(`links[0].send.next = []` → `send_key(0)` → L229), Q3‑5 (public `spqr::recv()` → L243).
**Lean**: `next_key_internal_never_ok`, `key_never_ok_of_bad_next`,
`recv_key_never_ok_bad_next`, `restore_then_recv_panics_bad_next`.

### 4.2. `KeyHistory::get` — L191 (I2, out-of-order path)

```rust
fn get(&mut self, at: u32, current_ctr: u32, params: &pqrpb::ChainParams) -> Result<Vec<u8>, Error> {
    assert_eq!(self.data.len() % Self::KEY_SIZE, 0);   // L191, KEY_SIZE = 36
    …
}
```

Reached when `at < ctr` (`key()` L254-256). Without the assertion, the `data[i..i+4]`
comparisons at L198 would read across record boundaries — silent misbehaviour instead of a
panic.

**Probes**: Q3‑2 (`ctr = 5`, `prev = [0; 37]`, `recv_key(0, 1)`). **Lean**: `get_never_ok`,
`key_never_ok_of_misaligned_prev`, `recv_key_never_ok_misaligned_prev`,
`restore_then_recv_panics_misaligned_prev`.

### 4.3. `KeyHistory::gc` — L157 (I2, forward path)

`gc` (`#[hax_lib::opaque]`, L144-183) has no alignment assertion of its own. When
`data.len() ≥ trim_size() · 36` it walks the history in 36-byte steps comparing
`trim_horizon.cmp(&self.data[i..i + 4])` (L157). On misaligned data the last window is
shorter than 4 bytes → slice-index panic. Reached on the *forward* path (`ctr < at ≤ ctr +
max_ooo`), i.e. by an **in-order** message, once the misaligned history has grown past the
threshold.

**Probes**: Q4‑2 (`ctr = 5000`, `prev = [0; 36·2201 + 1]`, `recv_key(0, 5001)` → `range end
index 4 out of range for slice of length 1`). **Lean**: not mechanised (`Gc.lean` assumes
alignment).

### 4.4. `KeyHistory::gc` — L149 (I3)

```rust
fn gc(&mut self, current_key: u32, params: &pqrpb::ChainParams) {
    if self.data.len() >= params.trim_size() * Self::KEY_SIZE {
        assert!(current_key >= params.max_ooo_keys_or_default());   // L149
        let trim_horizon = &(current_key - params.max_ooo_keys_or_default()).to_be_bytes()[..];
        …
```

Guards the subtraction against underflow. In honest operation `ctr ≥ max_ooo` whenever the
history is large enough to GC; a blob with small `ctr` and large aligned `prev` violates
this. GC fires only on the forward path with `ctr < at ≤ ctr + max_ooo` (a larger jump
takes `prev.clear()` at L268 first and GC does nothing), so the simplest trigger is
`at = ctr + 1`. Default params: `max_ooo = 2000`, `trim_size() = 2201`, threshold
`79 236` bytes.

**Probes**: Q3‑3 (`ctr = 0`, `prev = [0; 79236]`, `recv_key(0, 1)`). **Lean**: `gc_never_ok`,
`key_never_ok_of_large_prev_small_ctr`, `recv_key_never_ok_large_prev_small_ctr`,
`restore_then_recv_panics_large_prev_small_ctr`. Note `gc_never_ok`'s hypotheses are exactly
the negation of I3: if `prev.len() ≤ 36·ctr` and GC triggers, then
`36·(max_ooo·11/10 + 1) ≤ 36·ctr`, so `ctr > max_ooo`.

### 4.5. `key()` — L265 / L279 arithmetic overflow (I4, debug only)

`self.ctr + params.max_ooo_keys_or_default()` at L265 and L279 (and `at + max_ooo` in
`get` at L192, invariant I12). Panics in `debug`/test; wraps in `release`. Wrapping at
L265 makes `at > tiny` true → spurious `prev.clear()`; at L279 makes `ctr + max_ooo >= at`
false → skipped keys not stored; at L192 → spurious `Err(KeyTrimmed)`. The in-order key
returned by `key()` is still the correct KDF output — divergence is confined to the
out-of-order history.

**Probes**: Q4‑3 (`ctr = u32::MAX − 1`, `recv_key(0, u32::MAX)`: debug panic L265, release
`Ok`), Q4‑4 (`max_ooo = u32::MAX`, `ctr = 0`: `Ok` in both — `0 + u32::MAX` fits),
S2/S3/S4 (§14.3). **Lean**: `recvKeyPre_unsatisfiable_ctr_zone_z1/z3` (Phase 11).

---

## 5. Secondary Defect: `Chain::from_pb`

`src/chain.rs:434-452` copies `current_epoch`, `send_epoch`, `next_root` and `params`
verbatim; only `direction` is validated (`try_into`) and `params: None` is rejected.

| # | Invariant | Consumer | Failure | Probe |
|---|---|---|---|---|
| I6 | `next_root.len() == 32` | `add_epoch` → `hkdf_to_slice(&self.next_root, …)` L357-361, where `next_root` is the HKDF **salt** | No panic (HKDF accepts any salt length; empty ≡ default zero salt). Peers derive different chain keys from the next epoch on; SPQR still returns `Ok`; the failure surfaces as a Double-Ratchet decryption error at the Signal layer, not as an SPQR error, because `Authenticator` keys do not depend on `next_root`. | Q5‑1 (round-trip) |
| I7 | `send_epoch ≤ current_epoch` | `send_key` L385-388 → `epoch_idx` L372-382 | Graceful `Err(EpochOutOfRange)` until `add_epoch` catches up; `send_key(0)` → `Err(SendKeyEpochDecreased)`. Recoverable stall. | Q4‑5 |
| I8 | `links.len() ≥ 1`, `current_epoch − send_epoch < links.len()` | `epoch_idx` | Graceful `Err(EpochOutOfRange)` (`back >= links` is true for `links == 0`). | — |
| I9 | `send.next.len() == 32` for `links[i]`, `i ≥ epoch_idx(send_epoch)` | `send_key` → `next_key` → L229 | **panic** — the position-dependent half of I1 that `ChainEpochDirection::from_pb` cannot check alone (§16.2). | Q3‑4 |
| I10 | `max_ooo_keys_or_default() < 390451572` | `key()` L262-264 `assume!`; `trim_size()` L86 `assume!` | Not a runtime check. Overflow at L265 only when `ctr + max_ooo > u32::MAX` (Q4‑4 shows `ctr = 0`, `max_ooo = u32::MAX` is `Ok`). Practical effect: GC threshold `trim_size·36` ≈ 170 GB never reached → unbounded `prev`. | Q4‑4 |
| I11 | `trim_size() < 119304647` (equivalently `max_ooo ≤ 108458769`, since `trim_size = max_ooo·11/10 + 1`; `119304647 · 36 ≤ u32::MAX`) | `key()` L280-283 `assume!` | Same pattern; I11 is strictly tighter than I10 and implies it. `trim_size · 36` may overflow `usize` on 32-bit targets. | — |

---

## 6. Tertiary Defect: `Authenticator::from_pb`

`src/authenticator/serialize.rs:16` returns `Self` (infallible) and copies `root_key` /
`mac_key` of any length; `Authenticator::new` always produces 32-byte keys (L51-53).

| # | Invariant | Failure |
|---|---|---|
| I13 | `root_key.len() == mac_key.len() == 32` | No panic. HMAC-SHA256 accepts any key length; a non-standard-length key produces non-standard tags. A local attacker who can set `mac_key = []` can equally set a known 32-byte key, so the length check is a robustness measure, not a security boundary. |

**Severity**: LOW. Fix requires a `Result` return type and updating the 9 call sites in
`src/v1/unchunked/send_ct/serialize.rs` and `src/v1/unchunked/send_ek/serialize.rs`.
**Lean**: `authenticator_from_pb_no_validation`, `authenticator_from_pb_admits_empty_mac_key`,
`authenticator_from_pb_admits_empty_root_key`, `authenticator_from_pb_admits_wrong_key_lengths`.
**Probe**: Q5‑4 (round-trip).

---

## 7. Quaternary Defect: `PolyDecoder::from_pb`

`src/encoding/polynomial.rs:815-853` checks `pts.len() == 16` and each slot's `% 4`, but not:

| # | Invariant | Failure |
|---|---|---|
| I14 | `is_complete == false` until the message is actually decoded | A blob with `is_complete = true` makes `decoded_message()` return `None` forever — permanent silent epoch stall (Finding 5, `report.md`). No code path in SPQR sets `is_complete` from the wire, so this is local-only. |
| I15 | `pts[i].len() / 4 ≤ 2 · MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1 = 71` | **Memory only.** `decoded_message()` slices `&pts[..necessary_points(i)]` (`polynomial.rs:922`) so excess points are ignored; the `hax_lib::assume!` at `polynomial.rs:801` bounding `into_pb` size assumed `add_chunk` gating (`:895-896`) was the only writer. Not a stall. |
| I16 | `pts_needed ≤ 576` | Not violable in practice: every V1 call site (`src/v1/chunked/send_ct/serialize.rs`, `src/v1/chunked/send_ek/serialize.rs`) compares `pts_needed` exactly against its expected constant. |

`PolyEncoder::from_pb` (`polynomial.rs:573`) shares the pattern (validates `pts.len() ==
16` and `% 2` only) but is out of scope.

**Severity**: LOW‑MEDIUM (stall via `is_complete`).
**Lean**: `poly_decoder_from_pb_admits_premature_is_complete`,
`poly_decoder_from_pb_admits_stalled_decoder`. **Probe**: Q5‑4 (round-trip).

---

## 8. Lean Specification Evidence

### 8.1. `FromPb.lean` proves `from_pb` never fails

```lean
-- Spqr/Specs/Chain/ChainEpochDirection/FromPb.lean
theorem from_pb_spec (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result) =>
      match result with
      | .Ok ced => ced.ctr = pb.ctr ∧ ced.next = pb.next ∧ ced.prev = { data := pb.prev }
      | .Err _ => False ⦄
```

The `Err` branch is `False`: the spec *proves* there is no rejection path. The `Ok` branch
gives only field equalities.

### 8.2. Downstream specs need what `from_pb` does not establish

| Spec | Hypothesis | Guards | Invariant |
|---|---|---|---|
| `NextKeyInternal.lean:41` | `h_next_len : next.length = 32` | `copy_from_slice` | I1 |
| `Get.lean`, `Gc.lean:85` | `h_data_aligned : data.length % 36 = 0` | record alignment (L191, L157) | I2 |
| `Key.lean` | `h_prev_ctr : prev.data.length ≤ 36 * ctr.val` | GC precondition | I3 |
| `Gc.lean:798-800` | `h_key_ge : trim_threshold ≤ data.length → max_ooo ≤ current_key` | subtraction at L150 | I3 |
| `Key.lean:62` | `h_ctr_bound : ctr.val ≤ U32.max − 390451572` (slack) | additions at L265/L279 | I4 |
| `Key.lean:63,197`, `Gc.lean:797,833` | `h_maxooo_bound : maxOoo < 390451572` | `params` range | I10 |
| `Get.lean`, `Key32.lean` | `h_ooo_no_overflow : at + maxOoo ≤ U32.max` | `get` L192 — **message-side** (`index`), not blob-side | I12 |

All blob-derived rows are conjuncts of `recvKeyPre` (`Spqr/Specs/Chain/Chain/Defs.lean:95-106`),
the precondition of `recv_key_spec`. That list is exactly what a validating `Chain::from_pb`
must establish (Appendix A). An end-to-end theorem
`∀ blob msg, recv (from_pb blob) msg ≠ panic` is unprovable today; §8.3 proves its negation.

### 8.3. Mechanised bug proofs — `Spqr/Specs/Bugs/CorruptedBlobs.lean`

46 theorems, organised in eleven phases (full index in Appendix B). Each "never ok"
theorem has the form `from_pb pb = Ok ced → ∀ r, f ced … ≠ ok r` — the Aeneas model of a
Rust panic is the absence of any successful execution.

| Phase | Content | Invariants |
|---|---|---|
| 1 | `from_pb_never_fails`; `from_pb_admits_{wrong_next_length, misaligned_prev, large_prev_small_ctr, triple_violation}` | I1–I3 accepted |
| 2 | `get_never_ok`, `gc_never_ok`, `next_key_internal_ok_lengths`, `next_key_internal_never_ok` | consumers panic |
| 3 | `key_loop_body_preserves_next_length`, `key_loop_preserves_next_length`, `key_never_ok_of_{misaligned_prev, bad_next, large_prev_small_ctr}` | reachability through `key` |
| 4 | `restore_then_recv_panics_{bad_next, misaligned_prev, large_prev_small_ctr}` | end-to-end `from_pb` → `key` |
| 5 | `corrupted_state_roundtrips` — `into_pb ∘ from_pb = id` on `ChainEpochDirection` | §12 sense 2 |
| 6 | `authenticator_from_pb_*` (4 theorems) | I13 |
| 7 | `chain_from_pb_admits_wrong_next_root` (manual case-split over the Aeneas `?` arms; `Chain::into_pb` is `#[hax_lib::opaque]`, `chain.rs:414`) | I6 |
| 8 | `poly_decoder_from_pb_admits_{premature_is_complete, stalled_decoder}` | I14 |
| 9 | `recvKeyPre_unsatisfiable_{bad_next, misaligned_prev, large_prev_small_ctr}` | spec precondition unsatisfiable |
| 10 | `recv_key_never_ok_of_key_never_ok`, `recv_key_never_ok_{bad_next, misaligned_prev, large_prev_small_ctr}` | full lift through `Chain::recv_key` |
| 11 | `from_pb_copies_{ctr, next, prev}_verbatim`, `from_pb_bad_next_length_survives`, `recvKeyPre_unsatisfiable_ctr_zone_{z1, z3}`, `ctr_z1_survives_from_pb`, `recvKeyPre_slack_implies_runtime_bound`, `ctr_steering_breaks_recvKeyPre`, `recvKeyPre_zone_z0_ctr_bound` | I4 / §14 |

**Not mechanised**: the L157 slice-index panic (§4.3); I7–I11, I15; any `Chain`-,
`Authenticator`- or `PolyDecoder`-level round-trip theorem; and **sufficiency of the fixes**
in §16 (the file proves panics exist, not that the proposed checks remove them).

---

## 9. Runtime Evidence

Twenty-seven compiled-Rust probes, run on stable‑aarch64 in **both** `debug` and `release`.
Each Q3/Q4/Q5 probe builds a valid `Chain`, calls `into_pb()`, mutates one field, calls
`Chain::from_pb()` — which returned `Ok` in **every** case — and drives the consumer.

| Group | Location | Count | Command |
|---|---|---|---|
| Q3, Q4, Q5 | `docs/corrupted_blob_counterexample.rs.txt` (removed from tree per repo convention for `docs/*_counterexample.rs.txt`) | 14 | `cargo test [--release] --lib q{3,4,5}_probe -- --test-threads=1` |
| Q16‑1 | `src/chain.rs:469` (`#[ignore]`, ≈4·10⁹ HKDFs) | 1 | `cargo test --release --lib q16_probe -- --ignored` |
| Q16b S1–S8 | `src/chain.rs:540-686` | 8 | `cargo test [--release] --lib q16b_ -- --test-threads=1` |
| Q16c C1–C4 | `src/lib.rs:1180` `mod q16c_probes` | 4 | `cargo test [--release] --lib q16c_ -- --test-threads=1` |

Per-probe results are in Appendix C. Headline results:

- **Every panic site** (L229, L243, L191, L157, L149) is reached from `Chain::recv_key` /
  `send_key`, and L243 additionally from the public `spqr::recv()` after two real
  round-trips (Q3‑5). Identical in both profiles.
- **Arithmetic overflow** (L265/L279/L192) panics in debug and wraps in release (Q4‑3, S2–S4).
- **Graceful `Err`** for epoch inversion (Q4‑5).
- **Round-trip is the identity** at all four layers and through the prost wire for all ten
  §3/§5 corruption classes (Q5‑1, Q5‑4).
- **An `Ok` call re-persists corruption**: misaligned `prev` survives an in-order
  `spqr::recv()` that returns the *correct* key and a still-misaligned state (Q5‑2, Q5‑3).

---

## 10. Failure-Mode Taxonomy

| Class | Fields | Sites | Profile |
|---|---|---|---|
| **Panic** | `recv.next` (any `≠ 32`); `send.next = []` at/after send epoch; misaligned `prev` (OOO path); misaligned + large `prev` (forward path); small `ctr` + large `prev` | L229, L243, L191, L157, L149 | debug **and** release |
| **Panic (debug) / silent wrap (release)** | `ctr + max_ooo > u32::MAX`; `index + max_ooo > u32::MAX` | L265, L279, L192 | profile-dependent |
| **Graceful `Err`** | `send_epoch > current_epoch`; `links.is_empty()`; `current_epoch − send_epoch ≥ links.len()` | `epoch_idx` L372-382 | both |
| **`Ok`, wrong semantics** | `next_root.len() ≠ 32` (key divergence); `Authenticator` key lengths; `PolyDecoder::is_complete` (stall); oversized `PolyDecoder` slots (memory); oversized `trim_size` (GC disabled) | `add_epoch` L357-361; `decoded_message` | both |

---

## 11. Local Attack Scenarios

> Illustrative only. They assume write access to the decrypted session database, which in
> Signal's threat model is trusted storage. Their purpose is to pin down exact panic sites
> for regression tests, not to argue that the local attacker matters.

| # | Mutation | Trigger | Site | Character |
|---|---|---|---|---|
| 11.1 | `links[i].recv.next = [0]` (1 byte) | next in-order message | L243 (`[]` would be L229) | **immediate**; recurs on every reload (§12 sense 1) |
| 11.2 | `next_root = [0; 16]` | next epoch advance | none — `add_epoch` HKDF | **silent**; both parties `Ok` at SPQR level, Double Ratchet decryption fails from the next epoch |
| 11.3 | append 1 byte to `links[i].recv.prev` | first **out-of-order** message (L191), or in-order message once `prev ≥ 79 236` B (L157) | L191 / L157 | **latent**; in-order messages succeed, append 36 B each, and re-persist the misaligned history looking healthy (Q5‑2/Q5‑3) — defeats "roll back to last good state" |
| 11.4 | `recv.ctr = 0`, `recv.prev = [0; 79236]` | next message with `index = 1` | L149 | **immediate** |

Lean witnesses: `restore_then_recv_panics_bad_next` (11.1), `chain_from_pb_admits_wrong_next_root`
(11.2, `from_pb` half only), `restore_then_recv_panics_misaligned_prev` (11.3, L191 half),
`restore_then_recv_panics_large_prev_small_ctr` (11.4).

---

## 12. Persistence of Corruption

"The session crash-loops" bundles three distinct mechanisms. Only the second and third are
SPQR properties.

1. **Reload after panic (host policy).** A panicking call returns no new `state`, so
   libsignal keeps the pre-call blob (§2.1) and reloads it on the next message.
2. **Identity round-trip (SPQR).** Every `into_pb` on the persistence path is a pure
   field-by-field repackaging; `into_pb ∘ from_pb = id` on every blob `from_pb` accepts, at
   all four layers and through prost. Mechanised for `ChainEpochDirection`
   (`corrupted_state_roundtrips`); confirmed byte-for-byte for the `Chain` layer and ten
   corruption classes (Q5‑1) and for `Authenticator`/`PolyDecoder` (Q5‑4). The single
   non-identity case is a `PolyDecoder` slot with duplicate `x`, which `SortedSet::push`
   de-duplicates — towards validity.
3. **Propagation through a successful call (SPQR).** `spqr::send`/`recv` re-encode
   `chain.into_pb()` unconditionally (`lib.rs:301, 313, 443`), so whatever `from_pb`
   accepted and the operation did not touch is re-serialised verbatim in the state the
   caller is told to persist (Q5‑2: 37 → 73 B, `Ok`; Q5‑3: public API, correct key, still
   misaligned). This lets corruption survive into backups taken *after* the corruption event
   and reach other devices via state sync.

**Immediate vs latent**: I1 and I3 violations crash on the next in-order message. I2 is
latent (§11.3). I6 is silent until the next epoch.

---

## 13. Impact Assessment

**Severity: MEDIUM** (local-blob class).

- **Availability**: with persisted corruption on the L229/L243/L191/L157/L149 paths the
  session is unusable until the app deletes or archives it. The host process survives
  (§2.1); the session does not.
- **No graceful degradation on those paths**: `next_key_internal` and `gc` have no `Result`
  channel; `get`'s assertion precedes its `Result`. The caller cannot log, reset or recover.
  This statement is **scoped**: I7/I8 return a recoverable `Err`; I4/I12 panic only in debug;
  I6/I13/I14/I15 return `Ok` with wrong semantics (§10).
- **Realistic source is non-adversarial**: backup/restore, schema skew, torn writes (§1).
  Random bit-rot rarely produces this class. A malicious local attacker has strictly stronger
  attacks available.
- **Blast radius**: one session per corrupted blob. No cross-session or cross-device effect
  except through sync of the corrupted blob itself (§12 sense 3).

---

# Part II — Remote Reachability

## 14. Can a Remote Peer Persist an SPQR-Invalid Value?

*Question*: can a network attacker, without local or storage-layer access, cause a value
that violates one of I1–I16 to be persisted and later consumed by `from_pb`?

**Answer**: **No** for every panic-class field. **Yes for `ctr` (I4)**, from an
*authenticated* peer only, and the consequence is bounded to self-DoS of the attacker's own
send direction plus modest CPU amplification. Severity **LOW**.

### 14.1. Attacker classes

| Class | Passes Signal MAC? | Passes SPQR authenticator? | Can commit state? |
|---|---|---|---|
| A — unauthenticated network attacker | No | No | **No** (clone dropped, §2.1) |
| B — network attacker with a valid envelope but wrong SPQR keys | Yes | No | Only chunks that precede the SPQR MAC (§15) |
| C — malicious authenticated peer (holds the conversation's ratchet keys) | Yes | Yes | **Yes**, every `Ok` call |
| D — local / storage attacker | n/a | n/a | Yes (Part I) |

### 14.2. Why panic-class fields are unreachable remotely

Four layers, evaluated against class C (the strongest remote class):

| Layer | Mechanism | Holds against C? |
|---|---|---|
| 0 | Clone-then-commit (`session_cipher.rs:455,475`) — state is committed only if the whole decrypt returns `Ok` | passes trivially (C's messages return `Ok`) |
| 1 | Signal envelope MAC (`session_cipher.rs:657-661`) | passes trivially |
| 2 | SPQR-internal authenticator (`States::recv`) | passes trivially |
| 3 | **No verbatim copy**: `next`, `next_root`, `Authenticator` keys are HKDF outputs; `prev` records are appended by the KDF loop in 36-byte units; `params` is copied from the *local* blob only; `current_epoch`/`links` advance only via `add_epoch`, whose `assert!(epoch == current + 1)` (L355) is fed by the SCKA state machine, not the wire | **Holds** for `Chain` fields. The peer can pace them, never choose them. (Does *not* hold for `PolyDecoder` points — §15.) |

| Persisted field | Remotely influenceable? | Invariant at risk | Probe |
|---|---|---|---|
| `recv.ctr` | **Yes** — advanced to `index` by `key()`; the peer chooses `index` within `(ctr, ctr + max_jump]` | I4 | Q16‑1, S1–S7 |
| `recv.prev` | Contents/size only; alignment (I2) and `len ≤ 36·ctr` (I3) preserved; bounded by `trim_size·36 = 79 236` B | none | S6, S8 |
| `recv.next`, `next_root`, `Authenticator` keys | No — KDF outputs, always 32 B | I1, I6, I13 | — |
| `send.*` | No — only the local `send_key` touches it | I9 | — |
| `current_epoch`, `links` | Peer can pace epochs (needs a full KEM round-trip), cannot skip or invert; ≈0.5 KB per link, memory only | I7, I8 | — |
| `params` | No — local | I10, I11 | — |
| `PolyDecoder` points | **Yes** — see §15 | none of I1–I16; *content* is attacker-chosen | C1, C2 |

### 14.3. The `ctr` axis — zones, thresholds and consequences

Each `recv_key(epoch, index)` advances `recv.ctr` to `index` via the KDF loop (L270-286),
capped by `max_jump` (default 25 000) per message (L250-252). A class‑C peer sending
`index = ctr + max_jump` every message advances `ctr` by 25 000 per message. Each message
costs the victim 25 000 HKDFs (≈10 ms release / ≈470 ms debug — S6). Any epoch advance
resets `ctr` in the *new* link, but the peer controls whether it ever completes the KEM
handshake and can hold the epoch fixed indefinitely.

Default params (`max_ooo = 2000`):

| Zone | `ctr` range | Lean `recvKeyPre` | Debug | Release | Messages to reach | Probe |
|---|---|---|---|---|---|---|
| Z0 normal | `0 … u32::MAX − 390 451 572` | satisfiable (`recvKeyPre_zone_z0_ctr_bound`) | Ok | Ok | — | — |
| Z1 Lean-invalid, **runtime-benign** | `(u32::MAX − 390 451 572, u32::MAX − 2000]` | unsatisfiable (`recvKeyPre_unsatisfiable_ctr_zone_z1`) | **Ok** | **Ok** | ≈156 181 | S1 |
| Z2 overflow zone | `(u32::MAX − 2000, u32::MAX)` | unsatisfiable | **panic** L265 (in-order) / L279 (mid-loop) | spurious `prev.clear()` (S2) / skipped keys not stored (S3) | ≈171 799 (≈4.3·10⁹ HKDFs, ≈30 min victim CPU in release) | S2, S3 |
| Z2′ OOO `index > u32::MAX − 2000` | any `ctr > index` | I12 violated | **panic** L192 | `Err(KeyTrimmed)` for a stored key | — | S4 |
| Z3 exhausted | `ctr = u32::MAX` | unsatisfiable (`recvKeyPre_unsatisfiable_ctr_zone_z3`) | permanent `Err(KeyAlreadyRequested)` | same | — | S5 |

Key facts:

- **The Lean bound is not the runtime threshold.** `h_ctr_bound = u32::MAX − 390451572` is
  proof slack so the lemmas close for any `max_ooo < 390451572`. Z1 is provably outside the
  spec and provably harmless at runtime (S1: every `ctr` in Z1 returns `Ok` in both
  profiles for `ctr + 1` and `ctr + max_jump` requests).
  `recvKeyPre_slack_implies_runtime_bound` shows the runtime bound `ctr + maxOoo ≤ U32.max`
  implies the Lean slack whenever `maxOoo < 390451572`; the converse is false.
- **A Z1/Z2 blob survives `from_pb` unchanged** (`ctr_z1_survives_from_pb`, Q5‑1) and is
  re-persisted by every `Ok` call (§12 sense 3).
- **Non-default params shrink the distance** (S7): with `max_ooo = 2³¹`, `max_jump = 2²⁰`,
  Z2 is ≈2 048 messages away. With `max_jump ≥ u32::MAX − max_ooo` a single message
  reaches Z2. `params` is chosen by the local integrator (libsignal uses defaults).
- **I1–I3 are preserved by steering** (S8): `next.len() = 32`, `prev % 36 = 0`,
  `prev ≤ 36·ctr` hold throughout.
- **Unauthenticated attackers (class A) get CPU only**: a forged `index = 25 000` costs
  the victim 25 000 HKDFs before the outer MAC fails and the clone is dropped (C4). Nothing
  persists. `Err(KeyJump)` for larger jumps is pure — state is byte-identical (S6).

### 14.4. Who is harmed by `ctr` steering?

`recv.ctr` in link *i* is the counter of **the attacker's own send direction**. Every Z2/Z3
effect lands on the victim's ability to decrypt *the attacker's* messages: spurious
`prev.clear()` / unstored skipped keys / spurious `KeyTrimmed` make the attacker's own
delayed out-of-order messages undecryptable; exhaustion stops the attacker sending until a
new epoch; a debug-build panic fires only while processing the attacker's message, the
clone is dropped, and the victim's send direction and all other sessions are untouched.
Production bridges are release builds (no `[profile]` override in `Cargo.toml`), so the
panic does not occur in deployment.

What the attacker **cannot** do: brick the victim's send direction, affect any other
conversation, corrupt `next`/`prev` structure, influence `next_root` or epoch secrets, or
cause an incorrect in-order key.

**Net**: self-DoS plus a CPU-amplification vector that exists at `ctr = 0` too. **LOW.**
Fix guidance in §16.5 — with a warning: the naïve reload check
`ctr > u32::MAX − 390451572 → StateDecode` would convert the harmless Z1 into a
**remotely triggerable permanent `StateDecode` on every reload**, i.e. create a session
brick that does not exist today.

### 14.5. Evidence summary for §14

| Evidence | Finding | Reference |
|---|---|---|
| libsignal source (`a47ba487`) | clone-then-commit L455/L475; MAC precedes commit | `docs/evaluateV1.md` §5.1, §7.2–7.4 |
| Probe Q3‑5 | primary-field corruption must pre-exist in the blob | Appendix C |
| Lean Phase 11 | `from_pb` copies `ctr`/`next`/`prev` verbatim; Z1/Z3 unsatisfiable; Z1 survives reload; runtime bound ⇒ Lean bound; Z0 non-empty | Appendix B |
| Probe Q16‑1 | full steering loop to Z1 (ignored by default, ≈4·10⁹ HKDFs) | `src/chain.rs:469` |
| Probes S1–S8 | seeded-state end states for every zone, both profiles | `src/chain.rs:540-686` |
| Probe C4 | unauthenticated attacker: CPU only, nothing persisted | `src/lib.rs:1358` |

---

## 15. Attacker-Chosen Persisted State (Finding 2 Revisited)

Widening the §14 question from "SPQR-*invalid*" to "attacker-*chosen*" values gives three
more **yes** answers for class C, all confirmed through the public `spqr::recv()` API
(`src/lib.rs` `mod q16c_probes`, 4/4 in both profiles). None violates I1–I16; they are
included because the answer to the §14 question, read broadly, is "yes".

### 15.1. Where §14.2 layer 3 is too narrow

Layer 3 ("no verbatim copy") is true for `Chain` fields but **false for `PolyDecoder`
point sets**: `add_chunk` (`polynomial.rs:879-904`) stores the 32 chunk bytes of every
accepted message as 16 `(x, y)` points verbatim, and `States::recv` returns `Ok` (host
commits) whenever the decoder is still incomplete. The SPQR MAC (`verify_hdr` /
`verify_ct`) runs only once the whole header/ciphertext is reassembled — layer 2 is
**after** persistence for every chunk but the last. `report.md` rated Finding 2 "mitigated
in deployed V1"; that verdict holds for class A only.

### 15.2. C1 — attacker-chosen bytes persisted verbatim

A sends its first `Hdr` chunk; B receives (`Ok`). A sends a second `Hdr` with chunk index
100 and 32 arbitrary bytes → `Ok`; B's persisted V1 state grows by 65 B containing exactly
A's bytes. A third forged chunk completes the header decoder with garbage → `verify_hdr`
fails → `Err(MacVerifyFailed)` (clone dropped) — but the first forged chunk **remains in
committed state**, and every later *honest* chunk now also fails the MAC. Growth is capped
by `add_chunk` gating at 71 points per slot (I15 is *not* violable remotely).

### 15.3. C2 — authenticated chunk poisoning → permanent epoch stall

After B receives A's honest chunk 0, A replays chunk index **0** with different bytes.
`SortedSet::push` de-duplicates on `x` only (last-write-wins), replacing the honest point;
`recv` → `Ok`, poisoned state persisted. Every subsequent header completion fails the MAC;
the epoch never advances.

**Who is harmed**: the SCKA epoch stalls for *both* directions — no new `EpochSecret`, so
the conversation stays on the current epoch's chain keys indefinitely: **loss of
post-quantum forward secrecy / healing for the victim**, not just self-DoS. The attacker
keeps sending via the Double Ratchet. Silent, one message, remotely triggered.
**MEDIUM.** (Persisted via an `Ok` call — §12 sense 3.)

**Fix**: `report.md` Finding 2 option (b) — reset the decoder on `MacVerifyFailed` — or
first-write-wins in `add_chunk`, plus a Lean spec that the persisted point for index `x`
equals the *first* accepted chunk for `x`.

### 15.4. C3 — version downgrade persists `inner: None`

libsignal initialises with `min_version = V0` (`ratchet.rs:109, 200`). Before B has received
any V1 message, `version_negotiation` is `Some`. A sends an **empty** message (`V0`);
`recv` takes the `Ordering::Less` arm (`lib.rs:377-409`) and persists
`{ inner: None, version_negotiation: None, chain: None }`. Thereafter every V1 message
returns `Ok(key: None)` (`lib.rs:373`) and B's `send()` emits empty messages (`lib.rs:268`).
**SPQR is permanently and silently off for the session.** The window closes after B's first
V1 receive (`lib.rs:442`).

This is *designed* negotiation behaviour and the attacker already holds the peer's ratchet
keys, but it is remotely-persisted attacker-chosen state, silent to the victim, and a
permanent PQ opt-out for an attacker positioned at session start. **LOW**, flagged for
completeness.

### 15.5. Candidates examined and rejected

| Candidate | Why "no" |
|---|---|
| `add_epoch` `assert!(epoch == current_epoch + 1)` (L355) | `EpochSecret.epoch` comes from the SCKA state machine, which only emits `current + 1` (`states.rs:282-340`) |
| `links` growth | one link per completed KEM; ≈0.5 KB; bounded by epoch pacing; memory only |
| `pts_needed` | set from constants at construction; not wire-derived |
| `is_complete` | no code path sets it from the wire |
| chunk `index > 65535` / `epoch == 0` | rejected by `deserialize` (`serialize.rs:195, 254`) |
| `Authenticator` keys | HKDF from epoch secrets; peer influences the secret only via a valid KEM |
| `ek_matches_header` failure (`ErroneousDataReceived`) | `Err` → clone dropped; but the decoder holding bad EK bytes was already persisted on earlier `Ok` chunks → same class as C2 |

### 15.6. Consolidated answer to Part II

| Class of persisted value | Remote authenticated (C)? | Remote unauthenticated (A)? | Probe |
|---|---|---|---|
| Violates a `from_pb` structural invariant (I1–I3, I6–I11, I13–I16) | **No** | No | S8, C1 (bound) |
| Violates I4 (Lean `ctr` slack) — runtime-benign until Z2 | **Yes**, ≈156 K–172 K msgs, self-DoS only, LOW | No | Q16‑1, S1–S7 |
| Attacker-chosen `PolyDecoder` points → epoch stall | **Yes**, 1 message, **MEDIUM** | No (Signal MAC) | C1, C2 |
| `inner: None` (SPQR disabled) via V0 downgrade in the negotiation window | **Yes**, 1 message, LOW | No | C3 |
| Anything | — | **No** (CPU only) | C4 |

---

# Part III — Fixes

## 16. Recommended Fixes

Design principle: every blob-derived conjunct of `recvKeyPre` becomes a checked
postcondition of `Chain::from_pb`, returning `Err(Error::StateDecode)` on violation. Two
constraints shape the details:

- **`next` is position-dependent** (I1/I9): `ChainEpochDirection::from_pb` does not know
  whether it is building `send` or `recv`, nor its link index, so it can only enforce the
  weak form `len ∈ {0, 32}`; the strong form lives in `Chain::from_pb` (§16.2).
- **`ctr` must use the runtime bound, not the Lean slack** (I4): a remote peer can
  legitimately drive `ctr` into Z1 (§14.3). Rejecting Z1 at reload would *create* a
  remotely triggerable brick. Use `ctr.checked_add(max_ooo).is_some()` and pair it with a
  guard inside `key()` so Z2 is never persisted in the first place (§16.5).

### 16.1. `ChainEpochDirection::from_pb` — I1 (weak), I2, I3

```rust
fn from_pb(pb: pqrpb::chain::epoch::EpochDirection) -> Result<Self, Error> {
    // I1, weak form: empty (send direction cleared via clear_next()) or exactly 32 bytes.
    // Chain::from_pb tightens this per direction/position (§16.2).
    if !(pb.next.is_empty() || pb.next.len() == 32) { return Err(Error::StateDecode); }
    // I2 — h_data_aligned (Get.lean / Gc.lean): closes L191 and L157.
    if pb.prev.len() % KeyHistory::KEY_SIZE != 0 { return Err(Error::StateDecode); }
    // I3 — h_prev_ctr (Key.lean): closes L149. If GC triggers then
    // 36·(max_ooo·11/10 + 1) ≤ prev.len() ≤ 36·ctr, hence ctr > max_ooo.
    if pb.prev.len() / KeyHistory::KEY_SIZE > pb.ctr as usize { return Err(Error::StateDecode); }
    Ok(Self { ctr: pb.ctr, next: pb.next, prev: KeyHistory { data: pb.prev } })
}
```

`ctr` is deliberately **not** checked here: the bound depends on `params.max_ooo_keys`,
which this function does not see. It is checked in `Chain::from_pb` (§16.2).

### 16.2. `Chain::from_pb` — I1 (strong), I4, I6, I7, I8, I9

```rust
pub(crate) fn from_pb(pb: pqrpb::Chain) -> Result<Self, Error> {
    if pb.next_root.len() != 32 { return Err(Error::StateDecode); }           // I6
    if pb.send_epoch > pb.current_epoch { return Err(Error::StateDecode); }   // I7
    let params = Self::validate_params(pb.params.ok_or(Error::StateDecode)?)?; // §16.3
    let links: VecDeque<ChainEpoch> = /* existing per-link parsing via §16.1 */;

    // I8: send epoch must still be within `links` (mirrors epoch_idx, chain.rs:372-382).
    let back = (pb.current_epoch - pb.send_epoch) as usize;       // safe: I7 checked
    if back >= links.len() { return Err(Error::StateDecode); }
    let send_idx = links.len() - 1 - back;

    for (i, link) in links.iter().enumerate() {
        // I1 strong + I9: recv.next is never legitimately empty; send.next may be empty
        // only for i < send_idx (cleared by clear_next() in send_key()).
        if link.recv.next.len() != 32 { return Err(Error::StateDecode); }
        if i >= send_idx && link.send.next.len() != 32 { return Err(Error::StateDecode); }
        // I4, runtime bound (NOT the Lean slack constant — see §16.5).
        for d in [&link.send, &link.recv] {
            if d.ctr.checked_add(params.max_ooo_keys_or_default()).is_none() {
                return Err(Error::StateDecode);
            }
        }
    }
    Ok(Self { dir: …, current_epoch: pb.current_epoch, send_epoch: pb.send_epoch,
              next_root: pb.next_root, links, params })
}
```

With this, `h_next_len : next.length = 32` holds unconditionally for every direction that
`send_key`/`recv_key` can actually reach. `links.is_empty()` is rejected by the
`back >= links.len()` guard (for `links = 0` it reads `back >= 0`).

### 16.3. `ChainParams` range check — I10, I11

```rust
fn validate_params(p: pqrpb::ChainParams) -> Result<pqrpb::ChainParams, Error> {
    // I11 implies I10: trim_size() = max_ooo·11/10 + 1 < 119304647  ⇔  max_ooo ≤ 108458769,
    // the Key32.lean constant; also keeps trim_size·36 ≤ u32::MAX on 32-bit targets.
    if p.max_ooo_keys_or_default() > 108_458_769 { return Err(Error::StateDecode); }
    Ok(p)
}
```

`params` is local-only (§14.2), so this is pure robustness. It also makes the I4 check in
§16.2 meaningful: without a bound on `max_ooo`, `checked_add` could reject every blob under
a pathological configuration.

### 16.4. `Authenticator::from_pb` (I13) and `PolyDecoder::from_pb` (I14, I15)

```rust
// authenticator/serialize.rs — return type changes; update the 9 call sites in
// src/v1/unchunked/{send_ct,send_ek}/serialize.rs
pub fn from_pb(pb: &proto::pq_ratchet::Authenticator) -> Result<Self, Error> {
    if pb.root_key.len() != 32 || pb.mac_key.len() != 32 { return Err(Error::StateDecode); }
    Ok(Self { root_key: pb.root_key.clone(), mac_key: pb.mac_key.clone() })
}

// encoding/polynomial.rs — PolyDecoder::from_pb, inside the existing per-slot loop
if slot.len() / 4 > 2 * MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1 {
    return Err(PolynomialError::SerializationInvalid);
}
```

I14 (`is_complete`) is **not** closed by a length check. Options: reject
`is_complete = true` when any slot has fewer than `necessary_points(i)` points, or drop the
persisted flag and re-derive it from the point sets on load. The Phase 8 Lean witnesses are
the regression oracle either way.

### 16.5. `ctr` overflow — guard at the source, with the right bound

Replace the `hax_lib::assume!` at `chain.rs:262-264` and `275-277` with a runtime check:

```rust
let Some(horizon) = self.ctr.checked_add(params.max_ooo_keys_or_default()) else {
    return Err(Error::CounterExhausted(self.ctr));   // new variant — public API change
};
if at > horizon { self.prev.clear(); }
```

and at L192 in `get`, `at.checked_add(max_ooo)` (I12, message-side).

**Why this bound and not the Lean constant**:

| Check | Effect on Z1 (`u32::MAX − 390451572 < ctr ≤ u32::MAX − max_ooo`) | Effect on Z2 |
|---|---|---|
| `ctr > u32::MAX − 390451572 → Err` (Lean slack) | **Rejects a runtime-benign state** that a remote peer can reach in ≈156 K messages (§14.3) → every reload fails with `StateDecode` → a remotely triggerable session brick that does not exist today. **Do not ship.** | rejects |
| `ctr.checked_add(max_ooo).is_none() → Err` (runtime bound) | accepts (correct — Z1 is harmless) | rejects |

With the `key()` guard in place, `ctr` can never be persisted in Z2, so the §16.2 reload
check becomes a pure corruption detector. I4 then reads `ctr + max_ooo ≤ u32::MAX`; the
Lean `h_ctr_bound` remains a valid (weaker) precondition whenever I10 holds
(`recvKeyPre_slack_implies_runtime_bound`). Longer term, `recvKeyPre` should state the
exact bound and Z1 disappears as a spec anomaly. The session limit becomes
`u32::MAX − max_ooo` messages per epoch per direction — far beyond realistic use.

### 16.6. Defence in depth — replace `assert!` with `Err`

Even after §16.1–16.3, convert the five sites so that a `ChainEpochDirection` built by any
future path cannot panic:

| Site | Effort | Note |
|---|---|---|
| `get` L191 | cheap | already returns `Result`; `assert_eq!` → `return Err(InternalInvariantViolation)` |
| `gc` L149, L157 | signature change (`gc` returns `()`) | L157 needs its **own** alignment guard before the loop at L154 — converting only L191 leaves the forward path panicking; `Gc.lean:85` already carries `h_data_aligned`, so the spec change is hypothesis → checked branch |
| `next_key_internal` L229, L243 | signature change (`(u32, [u8; 32])`) | a single `if next.len() != 32` at entry replaces both; ripples into `key()`, `next_key()`, hax preconditions and `NextKeyInternal.lean` |

`Error::InternalInvariantViolation` is a public API change to `spqr::Error`.

### 16.7. Lean specification updates

1. `FromPb.lean`: `Err` branch stops being `False`; `Ok` branch gains
   `prev.data.length % 36 = 0`, `prev.data.length ≤ 36 * ctr.val`,
   `next.length = 0 ∨ next.length = 32`. A `Chain::from_pb` spec supplies
   `next.length = 32` per reachable direction, `next_root.length = 32`,
   `send_epoch ≤ current_epoch`, and `ctr.val + maxOoo ≤ U32.max`.
2. `h_data_aligned`, `h_prev_ctr` (hence `h_key_ge`), `h_next_len`, `h_ctr_bound` become
   provable invariants; `recv_after_restore_safe` (positive counterpart of Phase 4) becomes
   provable.
3. `Spqr/Specs/Bugs/CorruptedBlobs.lean` becomes a **regression oracle**: after the fix,
   `from_pb_never_fails`, `restore_then_recv_panics_*`, `chain_from_pb_admits_wrong_next_root`
   and `authenticator_from_pb_*` must fail to type-check (their `h_load` hypothesis becomes
   unsatisfiable). Retarget them as `from_pb pb = ok (Err StateDecode)` for each witness
   rather than deleting them. Phase 8 (`PolyDecoder`) is unaffected by §16.4 as written.
   Phase 11 `ctr_z1_survives_from_pb` must **continue to hold** (Z1 is accepted by design).
4. Round-trip corollaries for `Authenticator`/`PolyDecoder` (`spec_mono` compositions) and a
   `Chain`-level `corrupted_chain_roundtrips` (manual, because `Chain::into_pb` is opaque)
   close the §12 sense‑2/3 gaps; a `Key.lean` corollary that a successful forward-path
   `key` preserves `prev.data.length % 36` formalises the §11.3 latent propagation.

### 16.8. Tests to add

1. Promote the 14 Q3/Q4/Q5 probes to permanent tests in `src/chain.rs` under
   `corrupted_blob_*`, run in both profiles in CI; once §16.1–16.3 land, flip each
   `catch_unwind` assertion to `assert!(matches!(Chain::from_pb(pb), Err(Error::StateDecode)))`.
   Gate the Q4‑3 debug-only expectation with `#[cfg(debug_assertions)]`.
2. Keep S1 as the oracle that **Z1 is accepted** (it must flip to `Err` only if someone
   wrongly adopts the slack bound); flip S2–S4 to `Err(CounterExhausted)` after §16.5; keep
   S8 for I1–I3 preservation.
3. A proptest round-tripping `Chain::into_pb → from_pb` on states driven through
   `send_key` across several epochs, guarding against §16.2 rejecting legitimately empty
   pre-send-epoch `send.next`.
4. For §15: C2 flips to "epoch advances after honest retry" once the Finding 2 fix lands.

---

# Appendices

## Appendix A. Invariant → Fix Traceability

Numbering follows `docs/evaluateSPQR.md` §3. "Lean" is the hypothesis a validating
`from_pb` discharges; "Probe" cites Appendix C.

| # | Invariant | Failure today | Fix | Lean hypothesis | Probe |
|---|---|---|---|---|---|
| I1 | `recv.next.len() == 32` | panic L229 / L243 | §16.1 (weak) + §16.2 (strong) | `h_next_len` | Q3‑1, Q3‑5, Q4‑1 |
| I2 | `prev.len() % 36 == 0` | panic L191 (OOO) / L157 (forward GC) | §16.1 | `h_data_aligned` | Q3‑2, Q4‑2, Q5‑2, Q5‑3 |
| I3 | `prev.len() ≤ 36·ctr` | panic L149 | §16.1 | `h_prev_ctr` → `h_key_ge` | Q3‑3 |
| I4 | `ctr + max_ooo ≤ u32::MAX` (runtime); Lean uses slack `ctr ≤ u32::MAX − 390451572` | debug panic L265/L279; release wrap | §16.2 reload check (**runtime bound**) + §16.5 source guard | `h_ctr_bound`, `h_ctr_lt` | Q4‑3, S1–S5 |
| I5 | `prev.len() + 36·(index−ctr) ≤ usize::MAX` | allocation failure only | — (unrealistic) | `h_kh_cap` | — |
| I6 | `next_root.len() == 32` | silent key divergence | §16.2 | — | Q5‑1 |
| I7 | `send_epoch ≤ current_epoch` | graceful `Err` | §16.2 | — | Q4‑5 |
| I8 | `links ≥ 1`, `current_epoch − send_epoch < links` | graceful `Err` | §16.2 | — | — |
| I9 | `send.next.len() == 32` for `i ≥ send_idx` | panic L229 | §16.2 | `h_next_len` via `send_key` | Q3‑4 |
| I10 | `max_ooo < 390451572` | GC disabled; overflow only with large `ctr` | §16.3 (implied by I11) | `h_maxooo_bound`, `h_ooo` | Q4‑4 |
| I11 | `trim_size() < 119304647` ⇔ `max_ooo ≤ 108458769` | GC disabled → unbounded `prev` | §16.3 | `requires` on `add`/`remove` | — |
| I12 | `index + max_ooo ≤ u32::MAX` | debug panic L192 / release `KeyTrimmed` | §16.5 (`get`, message-side) | `h_ooo_no_overflow` | S4 |
| I13 | `root_key.len() == mac_key.len() == 32` | non-standard MAC key | §16.4 | — | Q5‑4 |
| I14 | `is_complete == false` until decoded | permanent stall | §16.4 (needs re-derivation or rejection) | — | Q5‑4 |
| I15 | `pts[i].len()/4 ≤ 71` | memory only | §16.4 | `assume!` `polynomial.rs:801` | — |
| I16 | `pts_needed ≤ 576` | not violable | optional | — | — |

## Appendix B. Lean Theorem Index

`Spqr/Specs/Bugs/CorruptedBlobs.lean`, 46 theorems (one private helper `bind_eq_ok_iff`).

| Phase | Theorems | Referenced in |
|---|---|---|
| 1 | `from_pb_never_fails`, `from_pb_admits_wrong_next_length`, `from_pb_admits_misaligned_prev`, `from_pb_admits_large_prev_small_ctr`, `from_pb_admits_triple_violation` | §3, §8.3 |
| 2 | `get_never_ok`, `gc_never_ok`, `next_key_internal_ok_lengths`, `next_key_internal_never_ok` | §4.1, §4.2, §4.4 |
| 3 | `key_loop_body_preserves_next_length`, `key_loop_preserves_next_length`, `key_never_ok_of_misaligned_prev`, `key_never_ok_of_bad_next`, `key_never_ok_of_large_prev_small_ctr` | §4 |
| 4 | `restore_then_recv_panics_bad_next`, `restore_then_recv_panics_misaligned_prev`, `restore_then_recv_panics_large_prev_small_ctr` | §11 |
| 5 | `corrupted_state_roundtrips` | §12 |
| 6 | `authenticator_from_pb_no_validation`, `authenticator_from_pb_admits_empty_mac_key`, `authenticator_from_pb_admits_empty_root_key`, `authenticator_from_pb_admits_wrong_key_lengths` | §6 |
| 7 | `chain_from_pb_admits_wrong_next_root` | §5, §11.2 |
| 8 | `poly_decoder_from_pb_admits_premature_is_complete`, `poly_decoder_from_pb_admits_stalled_decoder` | §7 |
| 9 | `recvKeyPre_unsatisfiable_bad_next`, `recvKeyPre_unsatisfiable_misaligned_prev`, `recvKeyPre_unsatisfiable_large_prev_small_ctr` | §8.3 |
| 10 | `recv_key_never_ok_of_key_never_ok`, `recv_key_never_ok_bad_next`, `recv_key_never_ok_misaligned_prev`, `recv_key_never_ok_large_prev_small_ctr` | §4 |
| 11 | `from_pb_copies_ctr_verbatim`, `from_pb_copies_next_verbatim`, `from_pb_copies_prev_verbatim`, `from_pb_bad_next_length_survives`, `recvKeyPre_unsatisfiable_ctr_zone_z1`, `recvKeyPre_unsatisfiable_ctr_zone_z3`, `ctr_z1_survives_from_pb`, `recvKeyPre_slack_implies_runtime_bound`, `ctr_steering_breaks_recvKeyPre`, `recvKeyPre_zone_z0_ctr_bound` | §14 |

## Appendix C. Probe Index

All probes pass in both `debug` and `release` unless a column says otherwise. "Panic"
means the probe caught the panic with `catch_unwind` and asserted its message/location.

**Q3/Q4/Q5** — `docs/corrupted_blob_counterexample.rs.txt` (14):

| # | Function | Mutation | Call | Debug | Release |
|---|---|---|---|---|---|
| Q3‑1 | `q3_probe_bad_next_reaches_next_key_internal_via_recv_key` | `recv.next = [0; 31]` | `recv_key(0, 1)` | panic `chain.rs:243` | same |
| Q3‑2 | `q3_probe_misaligned_prev_reaches_get_via_recv_key` | `recv.ctr = 5`, `recv.prev = [0; 37]` | `recv_key(0, 1)` | panic `chain.rs:191` | same |
| Q3‑3 | `q3_probe_large_prev_small_ctr_reaches_gc_via_recv_key` | `recv.ctr = 0`, `recv.prev = [0; 36·2201]` | `recv_key(0, 1)` | panic `chain.rs:149` | same |
| Q3‑4 | `q3_probe_empty_send_next_reaches_next_key_via_send_key` | `links[0].send.next = []` | `send_key(0)` | panic `chain.rs:229` | same |
| Q3‑5 | `q3_probe_top_level_recv_reaches_panic` | public API: two round-trips, decode blob, set every `links[i].recv.next = [0]`, re-encode; peer sends once more | `spqr::recv(&corrupted, &msg)` | panic `chain.rs:243` | same |
| Q4‑1 | `q4_probe_empty_recv_next_hits_assert_229` | `recv.next = []` | `recv_key(0, 1)` | panic `chain.rs:229` | same |
| Q4‑2 | `q4_probe_misaligned_large_prev_forward_path_hits_gc_slice_index` | `recv.ctr = 5000`, `recv.prev = [0; 36·2201 + 1]` | `recv_key(0, 5001)` | panic `chain.rs:157` (`range end index 4 out of range for slice of length 1`) | same |
| Q4‑3 | `q4_probe_ctr_overflow_profile_dependent` | `recv.ctr = u32::MAX − 1` | `recv_key(0, u32::MAX)` | panic `chain.rs:265` (`attempt to add with overflow`) | **`Ok`** (wrap) |
| Q4‑4 | `q4_probe_max_ooo_overflow_profile_dependent` | `params.max_ooo_keys = u32::MAX`, `ctr = 0` | `recv_key(0, 1)` | `Ok` | `Ok` |
| Q4‑5 | `q4_probe_graceful_err_epoch_inversion` | `send_epoch = 7`, `current_epoch = 0` | `send_key(7)`; `send_key(0)` | `Err(EpochOutOfRange(7))`; `Err(SendKeyEpochDecreased(7, 0))` | same |
| Q5‑1 | `q5_probe_chain_level_roundtrip_is_identity_on_corrupted_blobs` | 10 mutations (`recv.next` 31 B / `[]`; `recv.prev` 37 B; `ctr = 0` + 79 236 B; `ctr = u32::MAX`; `next_root` 16 B; `send_epoch = 7`; `send.next = []`; `max_ooo = u32::MAX`; `max_jump = u32::MAX`) | `from_pb → into_pb`, prost encode/decode | byte-identical | same |
| Q5‑2 | `q5_probe_misaligned_prev_survives_ok_recv_and_is_repersisted` | `recv.ctr = 5`, `recv.prev = 37 B` | `recv_key(0, 7)` then reload, `recv_key(0, 1)` | `Ok`; `prev = 73 B`; reload `Ok`; then panic L191 | same |
| Q5‑3 | `q5_probe_top_level_recv_ok_repersists_misaligned_prev` | public API, `recv.prev = [0; 1]` on persisted blob, peer sends in-order | `spqr::recv` | `Ok`, key equals peer's, returned state still misaligned | same |
| Q5‑4 | `q5_probe_authenticator_and_poly_decoder_roundtrip_corruption` | `Authenticator { root_key: 5 B, mac_key: [] }`; `PolynomialDecoder { is_complete: true, pts: 16 × [] }` | `into_pb(from_pb(pb))` | `== pb` | same |

**Q16 / S1–S8** — `src/chain.rs` (9):

| # | Function | Seeded state / action | Debug | Release |
|---|---|---|---|---|
| Q16‑1 | `q16_probe_remote_index_drives_ctr_past_bound` (`#[ignore]`) | loop `recv_key(0, ctr + max_jump)` until `ctr > u32::MAX − 390451572`; persist; reload | reload `Ok`; next in-order key `Ok` | same |
| S1 | `q16b_probe_lean_bound_is_not_runtime_threshold` | `ctr ∈ Z1` (incl. exactly `u32::MAX − 2000`); `recv_key(ctr+1)`, `recv_key(ctr+1+25 000)` | `Ok` | `Ok` |
| S2 | `q16b_probe_l265_threshold_and_spurious_clear` | `ctr = u32::MAX − 1999` with one stored key; `recv_key(ctr+1)` | panic L265 | `Ok`, `prev` cleared (36 → 0 B) |
| S3 | `q16b_probe_l279_midloop_overflow_drops_keys` | `ctr = u32::MAX − 3000`, `recv_key(u32::MAX − 1000)` | panic L279 | `Ok`, 1000 of 1999 skipped keys stored |
| S4 | `q16b_probe_l192_get_overflow_misreports_trimmed` | `ctr = u32::MAX − 1000`, key `u32::MAX − 1500` stored; OOO request | panic L192 | `Err(KeyTrimmed)` for a stored key |
| S5 | `q16b_probe_counter_exhaustion_hard_stop` | `ctr = u32::MAX` | `Err(KeyAlreadyRequested)`; OOO `Err(KeyTrimmed)`; permanent | same |
| S6 | `q16b_probe_key_jump_cpu_cost_and_err_is_pure` | `index = 25 000` (cost); `index = 50 001` → `Err(KeyJump)`; 60 near-`max_ooo` jumps | ≈470 ms; state byte-identical on `Err`; `prev ≤ 79 236` B | ≈10 ms; same |
| S7 | `q16b_probe_nondefault_params_lower_threshold` | `max_ooo = 2³¹`, `max_jump = 2²⁰`; `ctr = 2³¹` | panic L265 | wrap |
| S8 | `q16b_probe_steering_preserves_i1_i2_i3` | 2 000-step random walk, `max_ooo = 10`, `max_jump = 50` | I1, I2, I3 hold; `prev ≤ 36·12` | same |

**C1–C4** — `src/lib.rs` `mod q16c_probes` (4):

| # | Function | Scenario | Result (both profiles) |
|---|---|---|---|
| C1 | `q16c_probe_peer_chunk_bytes_persist_verbatim` | authenticated peer sends forged `Hdr` chunk 100 | `Ok`; +65 B persisted with attacker's bytes; later honest chunks fail MAC |
| C2 | `q16c_probe_authenticated_poison_then_stall` | replay chunk 0 with different bytes, then honest completion | `Ok`, then `Err(MacVerifyFailed)` on every completion; epoch never advances |
| C3 | `q16c_probe_peer_forces_v0_downgrade` | empty V0 message during negotiation window | `Ok`; `inner: None` persisted; SPQR off for the session |
| C4 | `q16c_probe_unauth_cpu_only_no_persist` | forged `index = 25 000` from unauthenticated sender | `Ok` from `spqr::recv`; host MAC fails; clone dropped; nothing persisted |

## Appendix D. Revision History

| Date | Change |
|---|---|
| 2026‑03 | Initial study: four `from_pb` defects, three panic paths, Lean Phases 1–10. |
| 2026‑09‑26 (a) | Review in `docs/evaluateSPQR.md` (gaps G1–G14). Added: `ctr` range invariant, fourth panic site L157, debug/release split for overflow, corrected `PolyDecoder` slot-size consequence, 14 runtime probes, three-sense persistence split, traceability table. |
| 2026‑09‑26 (b) | Remote-reachability analysis: `ctr` steering by an authenticated peer; correction that the Lean bound is proof slack, not the runtime threshold; probes Q16‑1, S1–S8; Lean Phase 11. |
| 2026‑09‑26 (c) | Attacker-chosen state: C1–C4; Finding 2 re-opened for authenticated peers. |
| 2026‑09‑26 (d) | **This consolidated rewrite.** Resolved contradictions between the layers above: (1) the `ctr` reload check now uses the runtime bound throughout — earlier §14.1/§14.7/§16.8 recommended the Lean slack constant, which §16.9.6 in the same document correctly said not to ship; (2) the `ctr` invariant row and the "Finding 2 mitigated" verdict now match Part II; (3) Phase 11 theorems indexed (earlier text listed `ctr` as unmechanised); (4) truncated sentence at the end of the old §15 removed; (5) the "crash loop" claim is scoped once (§12) rather than asserted then retracted; (6) I10/I11 dependency stated; (7) bit-rot realism caveat added (§1); (8) TOC covers every section. No new technical findings. |

