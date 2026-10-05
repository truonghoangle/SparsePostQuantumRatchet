# SPQR Defect Report: All Issues Identified from Specification Theorems

> **Version:** 2.0 — 2026-10-04 · **Previous version:** 1.0 (8 findings, source-level analysis only)
>
> **Scope:** Every defect surfaced by the 231 Lean specification files under `Spqr/Specs/`,
> cross-referenced against the 39 Rust source files in `src/`, the `sorted-vec 0.8.6` and
> `libcrux-ml-kem 0.0.7` dependencies, and the libsignal integration at commit `a47ba487`.
> In addition, three external Double Ratchet defects from Cheval–Jacomme–Richards 2026 are
> included because they affect the host protocol SPQR composes with.
>
> **Audience:** Engineers, auditors, and non-specialists who need to understand what went wrong,
> why it matters, and how to verify each claim independently.

---

## Table of Contents

- [1. What Is SPQR and Why Does This Matter?](#1-what-is-spqr-and-why-does-this-matter)
- [2. How Defects Were Found](#2-how-defects-were-found)
- [3. Reading Guide](#3-reading-guide)
- [4. Master Defect Table](#4-master-defect-table)
- [5. Part I — Unauthenticated Control Plane](#5-part-i--unauthenticated-control-plane)
- [6. Part II — Arithmetic and Parameter Bound Failures](#6-part-ii--arithmetic-and-parameter-bound-failures)
- [7. Part III — Deserialisation Without Validation](#7-part-iii--deserialisation-without-validation)
- [8. Part IV — Cryptographic Hygiene](#8-part-iv--cryptographic-hygiene)
- [9. Part V — Lean Trusted-Base Soundness](#9-part-v--lean-trusted-base-soundness)
- [10. External: Double Ratchet Defects](#10-external-double-ratchet-defects-ext-1--ext-3)
- [11. How to Verify Each Defect](#11-how-to-verify-each-defect)
- [12. Root Cause Analysis](#12-root-cause-analysis)
- [13. Recommended Fixes](#13-recommended-fixes-priority-order)
- [14. Template for Reporting New Defects](#14-template-for-reporting-new-defects)
- [15. Revision History](#15-revision-history)

---

## 1. What Is SPQR and Why Does This Matter?

### For non-experts

**SPQR** (Sparse Post-Quantum Ratchet) is a cryptographic component used by Signal to protect
messages against future quantum computers. It sits inside Signal's "Triple Ratchet" — an
upgrade of the Double Ratchet that adds a quantum-resistant key-exchange layer using ML-KEM
(a lattice-based algorithm). SPQR splits large KEM ciphertexts into small chunks that travel
alongside normal Signal messages, so users never notice the extra overhead.

**Why defects here matter:** SPQR manages cryptographic keys and protocol state. If an attacker
can corrupt the state (even without breaking encryption), they can:

- **Brick a session** — the app panics (crashes) every time it loads the corrupted state.
- **Stall key rotation** — quantum-resistant keys stop updating, so forward secrecy degrades.
- **Cause silent key divergence** — two peers derive different keys and can no longer communicate.

### Technical context

Signal uses [hax](https://github.com/AeneasVerif/hax) to translate SPQR's Rust into F*,
proving parts of the implementation correct. This project independently re-verifies SPQR by
translating it into [Lean 4](https://lean-lang.org/) via
[Aeneas](https://github.com/AeneasVerif/aeneas) and writing specification theorems. The gap
between what specs *require as preconditions* and what Rust *actually checks* is where every
defect lives.

### Key terms

| Term | Meaning |
|---|---|
| **`from_pb`** | "From protobuf" — deserialises persisted state from bytes back into structs |
| **`into_pb`** | "Into protobuf" — serialises state into bytes for storage |
| **Blob** | The persisted `pq_ratchet_state` protobuf — SPQR's saved state |
| **Chunk** | A ≤32-byte fragment of a larger protocol message |
| **Epoch** | One round of the post-quantum key exchange |
| **`sorry`** | Lean keyword meaning "claimed true but not yet proved" — a proof gap |
| **`assume!`** | Rust macro from `hax_lib` — checked in F* but **erased at runtime** |
| **MAC** | Message Authentication Code — proves message authenticity |
| **DR** | Double Ratchet — Signal's main key-ratcheting protocol |

---

## 2. How Defects Were Found

### Methodology

1. **Spec-gap analysis.** Every Lean spec theorem states preconditions (hypotheses like
   `h_next_len : next.length = 32`). When the Rust code that produces the input never checks
   the condition, we have a defect: the Rust can violate the invariant the spec needs.

2. **Postcondition analysis.** Spec postconditions sometimes reveal that a function *always*
   succeeds (e.g. `from_pb` returns `Ok` for any input) or *always* fails (e.g. `key` returns
   no `ok` on corrupted state). These are the basis for "never-validated" and "always-panics"
   findings.

3. **Executable counterexamples.** Each finding with a **Reproduced** label has a Rust test
   harness under `docs/*.rs.txt` that demonstrates the bug on the actual crate, run in both
   `debug` (panics visible) and `release` (wrapping/silent-failure visible) profiles.

4. **Machine-checked theorems.** `Spqr/Specs/Bugs/ProtocolDoS.lean` and
   `Spqr/Specs/Bugs/CorruptedBlobs.lean` contain 50+ proved theorems that formally establish
   the attack chains. `lake build Spqr SrcTranslated` (2553 jobs) confirms they compile.

5. **Internet research.** The Cheval–Jacomme–Richards 2026 paper ("Automated formal analysis
   of Signal's Double Ratchet") was consulted for external defects (EXT-1–EXT-3). Signal's own
   blog posts on SPQR and hax verification were used to understand claimed security properties.

### What "defect" means here

A **defect** is a property of the Rust code (or its Lean model) that a proved specification
theorem had to work around — either by requiring a precondition the code doesn't establish, or
by proving a postcondition that reveals unintended behaviour. The theorems themselves are
correct; the bugs are in the Rust source, its annotations, or the trusted Lean models.

| **PCS** | Post-Compromise Security — ability to "heal" after key compromise |

---

## 3. Reading Guide

### Severity levels

| Level | Meaning | Example |
|---|---|---|
| **HIGH** | Panic, key divergence, or unsound model reachable in realistic deployment | D1, D16, D17 |
| **MEDIUM** | DoS, downgrade, silent wrong result, or false verification annotation | D2, D11, D21 |
| **LOW** | Latent issue, needs unrealistic precondition, or documentation-only | D8, D20, D23 |
| **INFO** | Audit observation, no defect | *(removed)* |

### Qualifiers

- **message** — triggered by a single network message (on-path attacker)
- **blob** — requires influence over the persisted state (local storage access)
- **local-config** — requires a bad `ChainParams` value
- **32-bit** — only affects 32-bit platforms
- **spec** — affects soundness of Lean annotations/models, not runtime

### Attacker models

| Attacker | Capability | Example defects |
|---|---|---|
| **Network-only (forging)** | Read, drop, inject, modify messages; no session keys | D21, D22, D35, D36 |
| **Authenticated peer** | Legitimate remote party behaving adversarially | D16, D37 |
| **Local storage** | Can modify the persisted protobuf blob | D1, D18, D19, D23 |

### Host mitigation (libsignal)

libsignal (`session_cipher.rs` L607–694) clones the session, runs `pq_ratchet_recv`, derives
DR message keys, and only commits the clone if `verify_mac` passes. A **network-only**
attacker's forgery is therefore not persisted. This mitigation:

- (a) lives **outside** SPQR and is undocumented as an SPQR API requirement
- (b) does **not** protect other embedders of the `spqr` crate
- (c) does **not** protect against an authenticated-but-malicious peer

### Grouping conventions

- **Combined heading** (e.g. `D19 / D28 / D32 / D33`) — one fix closes all
- **Nested sub-finding** (e.g. `D4 / D15` under D16) — consequence of the parent defect
- **Sibling** (e.g. `D29` after D25) — shared root cause, distinct trigger


---

## 4. Master Defect Table

### Internal Defects (D1–D37)

| ID | Severity | Part | Short Description | Remote? | Reproduced? |
|---|---|---|---|---|---|
| **D1** | HIGH | III | `from_pb` admits `next.len() ≠ 32` → panic in `next_key_internal` | ❌ blob | ✅ `corrupted_blob_counterexample.rs.txt` |
| **D2** | MEDIUM | II | `u32` overflow in `KeyHistory::get` trimmed-check | ⚠️ msg+config | Spec |
| **D3** | MEDIUM | II | `u64→usize` truncation in `epoch_idx` (32-bit) | ❌ 32-bit | Spec |
| **D4** | MEDIUM | I | `SortedSet::push` comment says "noop" but replaces | ❌ | Spec |
| **D5** | MEDIUM | II | `PolyEncoder` index `u32→u16` truncation after 65535 | ❌ | Spec |
| **D6** | LOW | V | Wire-contract biconditional spec observations | ❌ | Spec |
| **D7** | LOW | V | Wire-contract (companion to D6) | ❌ | Spec |
| **D8** | LOW | II | `usize` overflow in `trim_size` on 32-bit | ❌ 32-bit | Spec |
| **D9** | MEDIUM | II | Claimed `data.len() ≤ KEY_SIZE * trim_size()` bound is false | ❌ | ✅ `key_history_bound_counterexample.*` |
| **D10** | LOW | IV | `chunk_at` panics on empty input (`#[cfg(test)]` only) | ❌ | Spec |
| **D11** | MEDIUM | III | `PolyEncoder::from_pb` no point-count validation | ❌ blob | ✅ `polynomial_from_pb_counterexample.rs.txt` |
| **D12** | LOW–MED | III | `PolyDecoder::from_pb` no point-set size bound | ❌ blob | ✅ `decoder_logic_probe.rs.txt` |
| **D13** | MEDIUM | III | `serialize`/`deserialize` not inverses on zero poly | ❌ | ✅ `poly_roundtrip_counterexample.rs.txt` |
| **D14** | LOW | III | `is_complete` never set → dead field, blob stall | ❌ blob | ✅ `decoder_logic_probe.rs.txt` |
| **D15** | MEDIUM | I | `add_chunk` guard always true for low indices | ⚠️ msg | Spec |
| **D16** | MEDIUM | I | Chunk poisoning persistent → epoch stall | ⚠️ msg | ✅ `decoder_poison_persistence_counterexample.rs.txt` |
| **D17** | HIGH | V | `VecDeque::into_iter` model wrong when `head ≠ 0` | ❌ spec | ✅ `vecdeque_into_iter_model_counterexample.lean.txt` |
| **D18** | MEDIUM | III | `Chain::from_pb` no `next_root`/`links`/epoch validation | ❌ blob | ✅ `corrupted_blob_counterexample.rs.txt` |
| **D19** | LOW | III | `Authenticator::from_pb` no key-length validation | ❌ blob | Spec |
| **D20** | LOW | V | Test-only code outside protocol | ❌ | Spec |
| **D21** | HIGH | I | Unauthenticated epoch advance → deadlock | ✅ msg | ✅ `protocol_driver_counterexamples.rs.txt` |
| **D22** | MEDIUM | I | Empty message finalises V0 downgrade | ✅ msg | ✅ `protocol_driver_counterexamples.rs.txt` |
| **D23** | LOW | III | `epoch == 0` blob → `msg.epoch − 1` underflow | ❌ blob | ✅ `protocol_driver_counterexamples.rs.txt` |
| **D24** | LOW–MED | III | `lib::send` panics on unexpected `EpochSecret` | ❌ blob | Spec |
| **D25** | MEDIUM | II | `ChainParams` never validated; `InvalidParams` dead | ❌ config | ✅ `protocol_driver_counterexamples.rs.txt` |
| **D26** | LOW | IV | No `Zeroize` on heap key-holding types | ❌ local | Spec |
| **D27** | LOW | III | `trim_size` overflow disables GC → FS loss | ❌ blob | Spec |
| **D28** | LOW | III | `Authenticator` IKM collision (sub of D19) | ❌ blob | Spec |
| **D29** | MEDIUM | II | Self-session `max_jump = u32::MAX` triggers D2/D25 | ⚠️ msg+config | Spec |
| **D30** | LOW | IV | No `Zeroize` on stack secrets | ❌ local | Spec |
| **D31** | LOW–MED | III | No `epoch < u64::MAX` guard in chunked recv | ❌ blob | Spec |
| **D32** | LOW | III | `authenticator::Error` variants never constructed | ❌ | Spec |
| **D33** | LOW | III | `From<authenticator::Error>` maps to wrong error class | ❌ | Spec |
| **D34** | LOW | III | `into_pb` truncates `pts_needed: usize` to `u32` | ❌ | Spec |
| **D35** | MEDIUM | I | Unauthenticated `Ct1Ack` → epoch stall | ✅ msg | ✅ `forged_control_message_counterexamples.rs.txt` |
| **D36** | MEDIUM | I | Unauthenticated `EkCt1Ack` stalls + poisons | ✅ msg | ✅ `forged_control_message_counterexamples.rs.txt` |
| **D37** | LOW–MED | I | Self-session removes HKDF-walk bound (CPU DoS) | ⚠️ msg+config | Spec |

### External Defects (EXT-1 – EXT-3)

| ID | Severity | Description | Fixed? |
|---|---|---|---|
| **EXT-1** | MEDIUM | DR spec: Null Decryption Key — `KDF_CK(None)` produces public key | ✅ Nov 2025 |
| **EXT-2** | HIGH | libsignal: Weak state forced storage → FS break after key rotation | ✅ Mar 2025 |
| **EXT-3** | HIGH | libsignal: X25519 replay via torsion points → duplicate session | ✅ Sep 2025 |


---

## 5. Part I — Unauthenticated Control Plane

### What this means in plain English

SPQR authenticates the *content* of messages (using MACs checked after full reassembly) but
does **not** authenticate the *control signals* — epoch numbers, message types, acknowledgement
flags, and chunk indices. An attacker who can inject messages into the network can trigger
state-machine transitions that corrupt or deadlock the protocol, even without knowing any keys.

### D21. Unauthenticated epoch advance deadlocks the PQ ratchet (HIGH; message)

**The problem.** A single 4-byte message `[1, 2, 1, 0]` with `epoch == self.epoch + 1` makes
SPQR advance to the next epoch without any authentication. The `Authenticator` — keyed
per-epoch to bind transitions to the shared secret — is never consulted.

**What happens.** Bob advances to `KeysUnsampled(epoch 2)` and consumes `recv_key(1, 1)`.
Alice remains in epoch 1. Neither side can complete → **permanent deadlock in both
directions**. `recv` also hands the caller a DR chain key for an unauthenticated message.

**Lean evidence.** `Spqr/Specs/Bugs/ProtocolDoS.lean` line 156 — theorem
`recv_hdr_chunk_persists_unauthenticated_state` proves `recv_hdr_chunk` returns
`Ok(StillReceiving)` with the unauthenticated decoder; no MAC check runs.

**Rust location.** `src/v1/chunked/states.rs` L513–526 → `send_ct.rs` L295.

**Reproduced:** `d24_unauthenticated_epoch_advance_deadlocks_ratchet` in
[`protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

**Fix.** Gate the transition on authenticated evidence — only accept `epoch + 1` after the
header's MAC verifies, or carry a short MAC tag over `(epoch, type)`.

### D35. Unauthenticated `Ct1Ack` stalls epoch completion (MEDIUM; message)

**The problem.** `Ct1Ack` is the peer's claim "I decoded your `ct1`". The protocol trusts it
blindly: Bob discards `sending_ct1` and moves to `Ct2Sampled`, which only emits `Ct2` chunks.
Alice, still in `HeaderSent`, only accepts `Ct1` chunks. Neither side makes progress.

**What happens.** A 5-byte forgery `[1, 1, 0xE8, 0x07, 4]` stalls both sides; 200 further
round-trips never leave epoch 1.

**Rust location.** `src/v1/chunked/states.rs` L463–477 → `send_ct.rs` L232–240.

**Reproduced:** `d38_forged_ct1ack_stalls_epoch` in
[`forged_control_message_counterexamples.rs.txt`](./forged_control_message_counterexamples.rs.txt).

### D36. Unauthenticated `EkCt1Ack` stalls + poisons `ek` decoder (MEDIUM; message)

Combines D35's stall with D16's poisoning — a forged `EkCt1Ack` chunk carries both a `Ct1Ack`
flag and garbage data injected into the `ek` decoder.

**Reproduced:** test in [`forged_control_message_counterexamples.rs.txt`](./forged_control_message_counterexamples.rs.txt).

### D22. Empty message finalises V0 downgrade (MEDIUM; message)

An **empty byte string** (0 bytes) triggers a version downgrade from V1 to V0 when
`min_version ≤ V0`. PQ ratchet permanently disabled.

**Reproduced:** `d25_unauthenticated_v0_downgrade_with_empty_message` in
[`protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

### D16. Chunk poisoning is persistent (MEDIUM; message)

**The problem in plain English.** SPQR splits large messages into chunks. When Bob receives a
chunk, he stores the data points. If an attacker sends a fake chunk with the same index as a
real one, the fake data *replaces* the real data (last-write-wins). The poisoned data is saved
to disk. When all chunks arrive, the MAC check fails — but the poisoned state was already
saved. Every future attempt also fails, permanently.

**How it works technically:**

1. `add_chunk` guard `poly_idx < necessary_points(i)` is always true for low-index chunks
2. `SortedSet::push` (`sorted-vec 0.8.6`) replaces on `.eq` (compares only `x`, not `y`)
3. `decoded_message()` returns `None` → `recv` returns `Ok` → poisoned decoder **persisted**

**Lean evidence.** `ProtocolDoS.lean`:
- `add_chunk_index_zero_pushes` (line 58) — attacker's values enter the decoder
- `sorted_push_replaces_singleton` (line 85) — replacement proven
- `poison_survives_persistence` (line 119) — survives `into_pb`/`from_pb`
- `recv_hdr_chunk_persists_unauthenticated_state` (line 156) — no MAC on this path

**Reproduced:** `poisoned_low_index_point_persists_and_wins` in
[`decoder_poison_persistence_counterexample.rs.txt`](./decoder_poison_persistence_counterexample.rs.txt).

**Fix.** (a) First-write-wins: `find_or_insert` instead of `push`; or (b) reset decoder on
MAC failure; or (c) keep both candidate `y` values and try alternatives.

#### D4. Source comment contradicts code

`polynomial.rs:898–900` says "discard new points whose X value matches" — the *opposite* of
what the code does. `sorted-vec 0.8.6` `SortedSet::push` replaces the existing element.

#### D15. Guard always true for low indices

The guard `poly_idx < necessary_points(i)` is unconditionally true for all chunks with
`index < pts_needed / 16`, so low-index chunks are always accepted regardless of duplicates.

### D37. Self-session removes HKDF-walk bound (LOW–MEDIUM; message + config)

libsignal self-sessions set `max_jump = u32::MAX`, making `at − ctr > max_jump` vacuous. An
attacker can force arbitrarily long HKDF chain derivation (~14ms for index 25000; unbounded
for larger), causing pre-MAC CPU DoS.


---

## 6. Part II — Arithmetic and Parameter Bound Failures

### What this means in plain English

SPQR uses `hax_lib::assume!` macros to tell the formal verifier "trust me, this holds." But
`assume!` is **erased at runtime** — the check disappears from the compiled binary. When the
assumption is false (e.g. a counter overflows), the code silently does the wrong thing in
release builds, or panics in debug builds.

### D2. `u32` overflow in `KeyHistory::get` (MEDIUM; message + config)

**Lean spec:** `h_ooo_no_overflow : at1 + maxOoo ≤ U32.max` (`Get.lean`).

**Rust:** `chain.rs` L192: `at + params.max_ooo_keys_or_default()` overflows near `u32::MAX`.
Debug: panic. Release: valid key reported as `KeyTrimmed`.

**Fix.** `checked_add` or `saturating_add`.

### D25. `ChainParams` never range-checked (MEDIUM; config)

**Lean spec:** `TrimSize.lean` needs `max_ooo_keys < 390451572`.

**Rust:** `Error::InvalidParams(&'static str)` exists but is **never constructed**. With
`max_ooo_keys = u32::MAX`, "keep every key" becomes "store none" in release.

**Reproduced:** `d28_unvalidated_chain_params_overflow_in_key` in
[`protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

**Fix.** Validate in `initial_state` and `Chain::from_pb`:
```rust
if params.max_ooo_keys >= 390_451_572 {
    return Err(Error::InvalidParams("max_ooo_keys too large"));
}
```

### D29. Self-session `max_jump = u32::MAX` triggers D2/D25 (MEDIUM; message + config)

libsignal `ratchet.rs` L41–52 sets `max_jump = u32::MAX` for Note-to-Self sessions, making
`at − ctr > max_jump` vacuous and `at + max_ooo` overflow reachable. The Lean hypothesis
`h_ctr_bound ≤ U32.max − 390451572` correctly predicts this.

### D9. Claimed history bound is false (MEDIUM; spec)

Code comments and `hax_lib::requires` claim key history never exceeds the GC threshold. The
Lean specs could not adopt this — they used weaker hypotheses. Investigation: history can grow
to **2× the threshold** before `gc` runs (4199 records vs. claimed 2201 with defaults).

**Reproduced:** [`key_history_bound_counterexample.py`](./key_history_bound_counterexample.py)
and [`key_history_bound_counterexample.rs.txt`](./key_history_bound_counterexample.rs.txt).

### D3. `u64→usize` truncation on 32-bit (LOW; 32-bit)

`chain.rs` L376: `(current_epoch - epoch) as usize` truncates ≥ 2³² → wrong epoch key.

### D5. `PolyEncoder` index `u32→u16` truncation (LOW)

`polynomial.rs` L735: `self.idx as u16` wraps after 65535 chunks.

### D8. `trim_size` overflow on 32-bit (LOW; 32-bit, config)

`max_ooo * 11` overflows for large `max_ooo_keys` on 32-bit. Subsumed by D25's fix.


---

## 7. Part III — Deserialisation Without Validation

### What this means in plain English

Every time SPQR restarts, it loads state from a protobuf "blob" on disk. The `from_pb`
functions accept **any bytes that are valid protobuf** without checking whether values make
cryptographic sense. If the blob is corrupted (by a bug, bad backup, or attack), SPQR crashes
on the next operation. The Lean specs make this visible: they need hypotheses like "the key is
32 bytes long" — but nothing in `from_pb` checks that.

### D1. `ChainEpochDirection::from_pb` — three panic paths (HIGH; blob)

**Proven in:** `Spqr/Specs/Bugs/CorruptedBlobs.lean` (1283 lines, 46 theorems, 11 phases).

`from_pb` copies `ctr`, `next`, `prev` verbatim with **zero validation**. Three consumers panic:

| Corrupted field | Consumer | Failure | Lean theorem |
|---|---|---|---|
| `next.len() ≠ 32` | `next_key_internal` (L241) | panic (`copy_from_slice`) | `next_key_internal_never_ok` |
| `prev.len() % 36 ≠ 0` | `KeyHistory::get` (L191) | panic (`assert_eq!`) | `get_never_ok` |
| `prev` too large for `ctr` | `KeyHistory::gc` (L149) | panic (`assert!`) | `gc_never_ok` |

**End-to-end proof chain:**
1. `from_pb_never_fails` — `from_pb` always returns `Ok` (no validation)
2. `key_never_ok_of_bad_next` / `key_never_ok_of_misaligned_prev` / `key_never_ok_of_large_prev_small_ctr` — `key` always panics on corrupted state
3. `recv_key_never_ok_bad_next` etc. — public API `recv_key` never returns `Ok`

**Reproduced:** Three probes in [`corrupted_blob_counterexample.rs.txt`](./corrupted_blob_counterexample.rs.txt).

**Fix.** Validate in `from_pb` (return `Error::StateDecode`):
```rust
if pb.next.len() != 32 { return Err(Error::StateDecode); }
if pb.prev.len() % 36 != 0 { return Err(Error::StateDecode); }
if pb.prev.len() / 36 > pb.ctr as usize { return Err(Error::StateDecode); }
```

### D18. `Chain::from_pb` — no `next_root`/`links`/epoch validation (MEDIUM; blob)

| Invariant | Failure mode |
|---|---|
| `next_root.len() == 32` | Silent key divergence (HKDF accepts any salt but output differs) |
| `links.len() ≥ 1` | Underflow panic (debug) / OOB panic (release) |
| `send_epoch ≤ current_epoch` | Every `send_key` fails → chain stuck |

**Reproduced:** `q4_probe_graceful_err_epoch_inversion` in
[`corrupted_blob_counterexample.rs.txt`](./corrupted_blob_counterexample.rs.txt).

### D19 / D28 / D32 / D33. `Authenticator::from_pb` — no key-length validation (LOW; blob)

`from_pb` clones any length. `mac_key: []` makes all tags identical → MACs forgeable.
D32: error variants exist but are never constructed (validation was planned, never done).
D33: `From` impl maps validation errors to `MacVerifyFailed` (wrong error class).

### D23. `epoch == 0` blob → underflow in `lib::send` (LOW; blob)

`lib.rs` L300 computes `msg.epoch − 1`. With `epoch = 0`: debug panics; release wraps to
`u64::MAX` → `Err(EpochOutOfRange)` forever.

**Reproduced:** `d26_epoch_zero_state_underflows_in_send` in
[`protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

### D11. `PolyEncoder::from_pb` — no point-count validation (MEDIUM; blob)

Lean specs require `h_admissible : ∀ j < 16, len ∈ {0, 1, 3, 5, 30, 34, 36}`. `FromPb.lean`
has no such hypothesis. Inadmissible slot sizes hit `debug_assert!(false, ...)` → panic in
debug, silently wrong chunks in release.

**Reproduced:** `encoder_from_pb_inadmissible_len` in
[`polynomial_from_pb_counterexample.rs.txt`](./polynomial_from_pb_counterexample.rs.txt).

### D12 / D34. `PolyDecoder::from_pb` — no size bound (LOW–MEDIUM; blob)

Blob with `pts_needed = 1600` → `decoded_message()` returns 3200 bytes (3× max) with O(N²)
cost. D34: `into_pb` truncates `pts_needed: usize` to `u32`.

### D13. Zero polynomial round-trip fails (MEDIUM; API)

Zero polynomial serialises to `[]`; `deserialize` requires non-empty input.
`from_pb(into_pb(encoder))` = `Err(SerializationInvalid)`. V1 never hits this; public API does.

**Reproduced:** `encoder_polys_roundtrip_with_empty_poly` in
[`poly_roundtrip_counterexample.rs.txt`](./poly_roundtrip_counterexample.rs.txt).

### D14. `is_complete` never set — dead field (LOW; blob)

Never set to `true` by any code. A blob with `is_complete = true` makes `decoded_message()`
return `None` forever — permanent silent stall. Also: completed decoder re-runs O(N²)
interpolation on every late chunk.

**Reproduced:** `decoder_is_complete_never_set` in
[`decoder_logic_probe.rs.txt`](./decoder_logic_probe.rs.txt).

### D24. `lib::send` panics on `assert!(key.is_none())` (LOW–MEDIUM; blob)

`assume!(key.is_none())` (L292) is unverified; `assert!` (L293) remains in release.

### D27. `trim_size` overflow disables GC (LOW; blob)

Large `max_ooo_keys` → `trim_size()` overflows → GC never runs → old keys never deleted →
forward secrecy degrades.

### D31. No `epoch < u64::MAX` guard in chunked recv (LOW–MEDIUM; blob)

`epoch + 1` wraps to `0` when `epoch == u64::MAX`; `assert_eq!` panics in debug.


---

## 8. Part IV — Cryptographic Hygiene

### D26 / D30. No `Zeroize` on key-holding types (LOW; local memory access)

No type implements `Zeroize`/`ZeroizeOnDrop`. Heap secrets (chain seeds, auth keys, ML-KEM
shared secrets, DK 2400 B, ES 2080 B) are never cleared. `clear_next()` is `Vec::clear()` —
sets length to zero without overwriting memory. Stack secrets (keygen seed, encapsulation
entropy) similarly uncleared. Exploitation requires local memory access (core dump, swap).

**Fix.** Add `zeroize` crate; derive `ZeroizeOnDrop`; replace `Vec::clear()` with `.zeroize()`.

### D10. `chunk_at` panics on empty input (LOW)

`#[cfg(test)]`-only code; not reachable in production.

---

## 9. Part V — Lean Trusted-Base Soundness

### What this means in plain English

The Lean specifications are *themselves* software that can have bugs. This section documents
issues in the specification infrastructure that could cause future proofs to be silently wrong.

### D17. `VecDeque::into_iter` model is wrong when `head ≠ 0` (HIGH; spec)

The hand-written Lean model uses ring-buffer arithmetic inconsistent with the project's own
`pop_front`/`push_back`/`index` model (growing list with `head` offset). It also never
decrements `length`, so it never terminates.

**Impact today.** Nothing proved is falsified because `Chain.into_pb` routes through a
`sorryAx` bridge. But any future round-trip theorem would be unsound.

**Reproduced:** [`vecdeque_into_iter_model_counterexample.lean.txt`](./vecdeque_into_iter_model_counterexample.lean.txt) with `lake env lean`.

### D6 / D7. Wire-contract biconditional observations (LOW)

Specs record that certain message fields have exact length constraints checked on
deserialisation but not serialisation. Not defects — explicit observations.

### D20. Test-only code outside protocol path (LOW)

Test utilities under `#[cfg(test)]` not in the production protocol.


---

## 10. External: Double Ratchet Defects (EXT-1 – EXT-3)

These were found by Cheval, Jacomme, and Richards (2026) in the Double Ratchet layer that
SPQR sits on top of. Documented here because they affect the overall Triple Ratchet security.

### EXT-1. Null Decryption Key (MEDIUM; spec-only, fixed Nov 2025)

DR's `RatchetDecrypt` doesn't ratchet when `dh == state.DHr`. Since initial `DHr = None`,
an attacker crafts `dh = None` → `KDF_CK(None)` → publicly computable key. No real-world
impact (PQXDH produces a different initial state). Fixed in DR spec revision 4.

### EXT-2. Weak State Forced Storage (HIGH; implementation, fixed Mar 2025)

Attacker replays legitimate PQXDH init. Responder stores state containing `SPKsk_R`. After
key rotation/deletion, device compromise leaks `SPKsk_R` → Forward Secrecy break.

### EXT-3. X25519 Replay via Torsion Points (HIGH; implementation, fixed Sep 2025)

Without one-time pre-key, attacker mangles ephemeral key with X25519 torsion points →
duplicate session with same `SK`. Combined with EXT-2, breaks Forward Secrecy.

### SPQR impact

The paper models SPQR as *completely insecure* and shows DR's FS and PCS still hold,
confirming DR provides a security floor independent of SPQR. Compositional DR+SPQR results
remain an open problem.

---

## 11. How to Verify Each Defect

### Step 1: Build the Lean proofs

```bash
cd /path/to/SparsePostQuantumRatchet
lake build Spqr SrcTranslated
# Should complete with 2553 jobs and only 2 expected sorry warnings
```

### Step 2: Read the theorem statements

Each theorem encodes the defect as a formal claim. Example from `ProtocolDoS.lean:156`:

```lean
theorem recv_hdr_chunk_persists_unauthenticated_state
    (self : NoHeaderReceived) (epoch : U64) (chunk : Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (decoder' : PolyDecoder)
    (h_add : add_chunk self.receiving_hdr chunk = ok decoder')
    (h_none : decoded_message decoder' = ok none) :
    recv_hdr_chunk self epoch chunk =
      ok (Ok (StillReceiving { self with receiving_hdr := decoder' }))
```

**Reading this:** "If `add_chunk` succeeds and the message isn't complete yet, then
`recv_hdr_chunk` returns `Ok` with the unauthenticated decoder in the state. No MAC ran."

### Step 3: Run Rust counterexamples

Each `docs/*.rs.txt` file contains Rust tests. To run:

1. Copy into `tests/` in a scratch copy of the spqr crate
2. Rename `.rs.txt` → `.rs`
3. `cargo test --test <filename> -- --nocapture` (both debug and release)

### Evidence-to-defect mapping

| Evidence file | Defects | Profile |
|---|---|---|
| `protocol_driver_counterexamples.rs.txt` | D21, D22, D23, D25, D29, D37 | debug + release |
| `forged_control_message_counterexamples.rs.txt` | D35, D36 | debug + release |
| `decoder_poison_persistence_counterexample.rs.txt` | D16 | release |
| `decoder_logic_probe.rs.txt` | D12, D14, D15 | release |
| `corrupted_blob_counterexample.rs.txt` | D1, D18 | debug + release |
| `polynomial_from_pb_counterexample.rs.txt` | D11 | debug + release |
| `poly_roundtrip_counterexample.rs.txt` | D13 | release |
| `key_history_bound_counterexample.{py,rs.txt}` | D9 | model + crate |
| `vecdeque_into_iter_model_counterexample.lean.txt` | D17 | `lake env lean` |
| `remote_attacker_harness.rs.txt` | Overall fuzz (40K inputs, 0 panics) | release |
| `dolev_yao_harness.rs.txt` | D21, D35 network model | release |
| `Spqr/Specs/Bugs/ProtocolDoS.lean` | D16, D21 | Lean |
| `Spqr/Specs/Bugs/CorruptedBlobs.lean` | D1, D18, D19 | Lean |


---

## 12. Root Cause Analysis

### The three systemic patterns

**Pattern 1: Authenticate-after-persist.** The state machine persists intermediate state on
every `Ok` return, but MAC authentication only runs after full message assembly. The gap
between "state persisted" and "state authenticated" is the window for poisoning.

> Affects: D16, D21, D35, D36, D22

**Pattern 2: `from_pb` copies without validating.** Every `from_pb` function accepts any
protobuf-valid input and copies fields verbatim. The invariants downstream consumers rely on
(key lengths, alignment, counter bounds) are never re-established after deserialisation.

> Affects: D1, D11, D12, D13, D14, D18, D19, D23, D24, D27, D31

**Pattern 3: `assume!` erased at runtime.** `hax_lib::assume!` tells the formal verifier a
condition holds, but expands to nothing at runtime. When false, Rust silently misbehaves.

> Affects: D2, D3, D5, D8, D9, D25, D29, D37

### Formal property classification

| Formal Property | Defects | CWE |
|---|---|---|
| Refinement type violation (length invariant) | D1, D11, D12, D18, D19 | CWE-20, CWE-502 |
| Integer overflow / wraparound | D2, D3, D5, D8, D25, D29 | CWE-190 |
| Authentication ordering | D16, D21, D35, D36 | CWE-345 |
| State-machine liveness | D14, D22 | CWE-672, CWE-841 |
| Spec–impl mismatch | D4, D9 | CWE-684 |
| Missing key erasure | D26, D30 | CWE-404 |
| Model soundness | D17 | — |

### Cryptographic impact

| Crypto Property | Defects | Impact |
|---|---|---|
| Availability (session liveness) | D1, D21, D35 | Panic = session destruction |
| IND-CPA / Key uniqueness | D2, D5, D29 | Counter wrap → nonce/key reuse |
| KDF security | D18 (next_root) | Wrong-length root breaks domain separation |
| MAC unforgeability (EUF-CMA) | D19 | Empty key → public hash; anyone forges tags |
| Post-compromise security | D14 | Stalled epoch prevents KEM re-keying |
| Forward secrecy | D26, D27 | Old keys retained; past plaintext exposed |


---

## 13. Recommended Fixes (Priority Order)

### Priority 1 — Critical (fix immediately)

| Fix | Closes | Effort |
|---|---|---|
| Validate all fields in `ChainEpochDirection::from_pb` | D1 | Small |
| Gate epoch transitions on authenticated evidence | D21, D35, D36, D22 | Medium |
| Validate in `Chain::from_pb` (`next_root`, `links`, epoch) | D18 | Small |

### Priority 2 — Important (next release)

| Fix | Closes | Effort |
|---|---|---|
| First-write-wins or reset-on-MAC-failure in `add_chunk` | D16, D4, D15 | Small–medium |
| `checked_add`/`saturating_add` for counter arithmetic | D2, D25, D29, D8 | Small |
| Validate `ChainParams` in `initial_state` and `from_pb` | D25, D29 | Small |
| Validate `Authenticator::from_pb` key lengths | D19, D28, D32, D33 | Small |
| Validate `PolyEncoder`/`PolyDecoder` `from_pb` | D11, D12, D34 | Small |
| Reject `epoch == 0`; `checked_sub` in `lib.rs` | D23, D31 | Small |

### Priority 3 — Hardening (schedule when convenient)

| Fix | Closes | Effort |
|---|---|---|
| Add `zeroize` crate; derive `ZeroizeOnDrop` | D26, D30 | Medium |
| Fix zero-polynomial serialisation round-trip | D13 | Small |
| Set `is_complete = true` on success (or delete field) | D14 | Small |
| Fix `VecDeque::into_iter` Lean model | D17 | Small |
| Correct source comment in `add_chunk` | D4 | Trivial |
| Guard `lib::send` against unexpected `EpochSecret` | D24 | Small |
| Cap self-session `max_jump` in libsignal | D29, D37 | Small (libsignal) |

---

## 14. Template for Reporting New Defects

Use this template to maintain consistency and traceability when adding new findings:

```markdown
### D<N>. <One-line summary> (<SEVERITY>; <qualifier>)

**Specs that expose it.**
List the Lean spec file(s) and specific hypothesis/postcondition that reveals the gap.

**Rust defect.**
Source file, line number(s), and the specific code violating the invariant.

**Consequence.**
What happens when triggered? Distinguish debug (panic) vs release (silent wrap / wrong result).

**Reproduced:** `<function_name>` in [`docs/<file>.rs.txt`](./file.rs.txt).

**Fix.**
Concrete code or design change that closes the defect.

**Related.** Cross-references to parent/sibling/consequence defects.
```

### Checklist for new findings

- [ ] Assigned stable identifier `D<N>` (next: D38, D39, …)
- [ ] Added to [Master Defect Table](#4-master-defect-table)
- [ ] Severity and qualifier assigned
- [ ] Lean spec file(s) cited
- [ ] Rust source file and line(s) cited
- [ ] Consequence described for debug and release
- [ ] Verification instructions (Lean theorem and/or Rust counterexample)
- [ ] Fix described
- [ ] Cross-references added
- [ ] Added to [Evidence-to-defect mapping](#evidence-to-defect-mapping) if counterexample exists
- [ ] Revision history updated

---

## 15. Revision History

| Version | Date | Changes |
|---|---|---|
| 2.0 | 2026-10-04 | Complete rewrite: expanded from 8 to 43 findings (D1–D37 + EXT-1–EXT-3); added non-expert explanations; verification instructions; new-defect template; root cause analysis; CWE and crypto-property classification; priority-ordered fixes |
| 1.0 | 2026-09-26 | Initial source-level analysis (8 findings) |

