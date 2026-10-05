# SPQR Defect Report

> **Date:** 2026-10-05 · **Scope:** 63 defects (D1–D63) plus 3 external findings (EXT-1–EXT-3)
> identified across 240 Lean specification files under `Spqr/Specs/`, 39 Rust source files in
> `src/`, the `sorted-vec 0.8.6` and `libcrux-ml-kem 0.0.7` dependencies, and the libsignal
> integration at commit `a47ba487`.
>
> **Audience:** Engineers, auditors, and non-specialists who need to understand what is wrong,
> why it matters, and how to verify each claim independently.
>
> **Companion documents:**
> [`listDefects.md`](./listDefects.md) — per-defect detail for all 63 findings;
> [`classificationBug.md`](./classificationBug.md) — SPQR-vs-V1 bug classification;
> [`network.md`](./network.md) — network-attacker mitigation analysis;
> [`invariantsSPQR.md`](./invariantsSPQR.md) — global invariant composition proof;
> [`CorruptedBlobs.md`](./CorruptedBlobs.md) — corrupted-blob deep-dive.

---

## Table of Contents

- [1. What Is SPQR and Why Does This Matter?](#1-what-is-spqr-and-why-does-this-matter)
- [2. How Defects Were Found](#2-how-defects-were-found)
- [3. Reading Guide](#3-reading-guide)
- [4. Fix Status Summary](#4-fix-status-summary)
- [5. Master Defect Table](#5-master-defect-table)
- [6. Part I — Unauthenticated Control Plane](#6-part-i--unauthenticated-control-plane)
- [7. Part II — Arithmetic and Parameter Bound Failures](#7-part-ii--arithmetic-and-parameter-bound-failures)
- [8. Part III — Deserialisation Without Validation](#8-part-iii--deserialisation-without-validation)
- [9. Part IV — Cryptographic Hygiene](#9-part-iv--cryptographic-hygiene)
- [10. Part V — Lean Trusted-Base Soundness](#10-part-v--lean-trusted-base-soundness)
- [11. Part VI — New Findings (D38–D63)](#11-part-vi--new-findings-d38d63)
- [12. External: Double Ratchet Defects](#12-external-double-ratchet-defects-ext-1--ext-3)
- [13. Attacker Model and Network Exploitability](#13-attacker-model-and-network-exploitability)
- [14. Global Invariant Composition](#14-global-invariant-composition)
- [15. Root Cause Analysis](#15-root-cause-analysis)
- [16. Recommended Fixes](#16-recommended-fixes-priority-order)
- [17. How to Verify Each Defect](#17-how-to-verify-each-defect)
- [18. Template for Reporting New Defects](#18-template-for-reporting-new-defects)


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
| **Blob** | The persisted `pq_ratchet_state` bytes stored by the app between calls |
| **Chain** | The `Chain` struct containing per-epoch send/recv key material |
| **`ChainEpochDirection`** | Per-direction (send or recv) key state within one epoch |
| **`PolyEncoder` / `PolyDecoder`** | Polynomial secret-sharing codec that splits/reassembles KEM ciphertexts |
| **`Authenticator`** | HMAC-based authenticator keyed per epoch |
| **Epoch** | One complete KEM key-exchange cycle |
| **DR** | Double Ratchet — the classical ratchet SPQR composes with |

---

## 2. How Defects Were Found

Defects D1–D37 were found by writing Lean specification theorems for each Rust function
and observing where the specs require preconditions the Rust code does not check.

Defects D38–D49 were found via extended methods:

| Method | Description |
|---|---|
| M1 — Model checking | Exhaustive state-space exploration of `from_pb` inputs |
| M2 — Miri | Undefined-behaviour detection for memory safety |
| M3 — Fuzz surface | Targeted fuzzing of `from_pb` and `add_chunk` |
| M4 — Property testing | QuickCheck-style random testing of invariants |
| M12 — Differential testing | Cross-checking Lean model vs compiled binary |

Defects D50–D63 were found via advanced verification methods:

| Method | Description |
|---|---|
| M13 — Refinement checking | Proving code refines its specification |
| M14 — Compositional invariant verification | Checking invariant preservation across calls |
| M16 — Information-flow typing | Tracking taint of secrets to enforce erasure |
| M18 — Trusted-base/axiom soundness audit | Auditing `sorry`, `sorryAx`, and external axioms |

---

## 3. Reading Guide

**Severity scale:**

| Level | Meaning |
|---|---|
| **HIGH** | Panic / session destruction reachable from a single input |
| **MEDIUM** | Silent corruption, protocol stall, or cryptographic degradation |
| **LOW** | Latent issue, spec observation, or requires unlikely preconditions |

**Qualifier tags:** `blob` (corrupted persisted state), `message` (wire message),
`config` (unusual parameters), `spec` (model/spec issue), `32-bit` (32-bit targets only),
`local memory` (requires local access), `crypto` (cryptographic hygiene), `protocol` (logic).

---

## 4. Fix Status Summary

All defects were identified against SPQR **v1.5.0** as consumed by libsignal commit `a47ba487`.

| Status | Count | Defect IDs |
|---|---|---|
| 🔴 **Unfixed** | 27 | D23–D31, D37, D38, D40–D47, D51, D54–D56, D60–D63 |
| 🟢 **Proved** | 15 | D1, D2, D3, D5, D8, D9, D10, D11, D12, D13, D14, D15, D18, D19, D57 |
| 🟡 **Mitigated by host** | 4 | D21, D22, D35, D36 |
| ✅ **Fixed** | 13 | D4, D16, D17, D20, D32, D33, D34, D39, D48, D49, D50, D52, D53 |
| 🟢 **No fix needed** | 2 | D6, D7 |
| 🔵 **Spec-only** | 2 | D58, D59 |

> **Note on D21/D22/D35/D36.** libsignal's clone-then-commit-after-MAC pattern discards
> the mutated state on MAC failure. The SPQR library itself remains vulnerable; only the
> Signal integration absorbs the attack. Other embedders of the `spqr` crate are fully exposed.


---

## 5. Master Defect Table

### D1–D37 (Original Findings)

| ID | Sev | Part | Summary | Qualifier |
|---|---|---|---|---|
| **D1** | HIGH | III | `ChainEpochDirection::from_pb` — three panic paths | blob |
| **D2** | MED | II | `u32` overflow in `KeyHistory::get` | msg+config |
| **D3** | MED | II | `u64→usize` truncation in `epoch_idx` (32-bit) | 32-bit |
| **D4** | MED | III | `SortedSet::push` comment contradicts replacement | spec |
| **D5** | MED | II | `PolyEncoder` index `u32→u16` truncation | blob |
| **D6** | LOW | V | `decode_chunk` cursor advanced on error | spec |
| **D7** | LOW | V | `decode_varint` contract inconsistency | spec |
| **D8** | LOW | II | `trim_size` overflow on 32-bit | config, 32-bit |
| **D9** | MED | II | Claimed history bound is false | spec |
| **D10** | LOW | II | `RoundRobinEncoder::chunk_at` panics on empty | spec |
| **D11** | MED | III | `PolyEncoder::from_pb` no point-count validation | blob |
| **D12** | LOW–MED | III | `PolyDecoder::from_pb` no size bound | blob |
| **D13** | MED | III | Zero polynomial round-trip fails | API |
| **D14** | LOW | III | `PolyDecoder::is_complete` never set — dead field | blob |
| **D15** | MED | I | `add_chunk` guard always true for low-index chunks | msg |
| **D16** | MED | I | Chunk poisoning → permanent epoch stall | msg |
| **D17** | HIGH | V | `VecDeque::into_iter` model wrong (`head ≠ 0`) | spec |
| **D18** | MED | III | `Chain::from_pb` — no `next_root`/`links`/epoch check | blob |
| **D19** | LOW | IV | `Authenticator::from_pb` no key-length check | blob |
| **D20** | LOW | V | Test-only code outside protocol path | spec |
| **D21** | HIGH | I | Unauthenticated epoch advance → PQ deadlock | msg |
| **D22** | MED | I | Empty message finalises V0 downgrade | msg |
| **D23** | LOW | III | `epoch == 0` blob → underflow in `lib::send` | blob |
| **D24** | LOW–MED | III | `lib::send` panics on `assert!(key.is_none())` | blob |
| **D25** | MED | II | `ChainParams` never range-checked | config |
| **D26** | LOW | IV | No `Zeroize` on heap key-holding types | local memory |
| **D27** | LOW | II | `trim_size` overflow disables GC | blob |
| **D28** | LOW | IV | `Authenticator` IKM collision | blob |
| **D29** | MED | II | Self-session `max_jump = u32::MAX` triggers D2/D25 | msg+config |
| **D30** | LOW | IV | No `Zeroize` on stack secrets | local memory |
| **D31** | LOW–MED | III | No `epoch < u64::MAX` guard in chunked recv | blob |
| **D32** | LOW | IV | `authenticator::Error` variants never constructed | spec |
| **D33** | LOW | IV | `From<authenticator::Error>` maps wrong error class | spec |
| **D34** | LOW | III | `PolyDecoder::into_pb` truncates `pts_needed` to `u32` | blob |
| **D35** | MED | I | Unauthenticated `Ct1Ack` → epoch stall | msg |
| **D36** | MED | I | Unauthenticated `EkCt1Ack` stalls + poisons | msg |
| **D37** | LOW–MED | I | Self-session removes HKDF-walk bound (CPU DoS) | msg+config |

### D38–D63 (Extended Findings)

| ID | Sev | Summary | Method | Status |
|---|---|---|---|---|
| **D38** | MED | `decode_varint` shift overflow → silent truncation | M1 | 🔴 |
| **D39** | LOW | `Authenticator::update` IKM includes unchecked-length `root_key` | M1 | ✅ |
| **D41** | MED | `compare` panics on mismatched lengths | M1 | 🔴 |
| **D42** | LOW–MED | `PolyEncoder::from_pb` accepts arbitrary `idx` | M1 | 🔴 |
| **D43** | HIGH | `ChainEpochDirection::from_pb` — `copy_from_slice` crash (D1 variant) | M1 | 🔴 |
| **D44** | LOW–MED | `epoch == 0` in chunked `from_pb` (D23 variant) | M1 | 🔴 |
| **D45** | MED | `KeyHistory::gc` panics when `ctr < max_ooo_keys` after blob restore | M1 | 🔴 |
| **D46** | LOW | `PolyDecoder::from_pb` accepts `pts_needed == 0` → div-by-zero | M3 | 🔴 |
| **D47** | LOW | `flip_endianness` leaks secret copy in memory | M2 | 🔴 |
| **D48** | LOW | `hkdf_to_slice` panics on `okm` > 8160 bytes | M12 | ✅ |
| **D49** | LOW | `is_complete` flag not validated on `from_pb` | M1 | ✅ |
| **D50** | MED | `PolyEncoder::next_chunk` `idx` wraps `u16` — duplicate chunks | M13 | ✅ |
| **D51** | MED | `compare` constant-time comparison panics on mismatched lengths | M13 | 🔴 |
| **D52** | LOW | `Authenticator::update` IKM lacks length prefix | M14 | ✅ |
| **D53** | MED | `epoch_idx` `as usize` truncation on 32-bit | M13 | ✅ |
| **D54** | LOW | `add_chunk` `GF16::new(poly_idx as u16)` truncation | M13 | 🔴 |
| **D55** | MED | `from_complete_points` fallback wrong polynomial in release | M14 | 🔴 |
| **D56** | LOW | `trim_size` `max_ooo * 11` overflows `usize` | M14 | 🔴 |
| **D57** | MED | `key` `ctr + max_ooo` overflow bypasses `KeyTrimmed` | M14 | 🟢 |
| **D58** | LOW | `Option::next_chunk` `unwrap()` panics on `None` | M18 | 🔵 |
| **D59** | LOW | Eviction loop depends on unsound `VecDeque` model | M18 | 🔵 |
| **D60** | LOW | `encaps1` 32-byte KEM entropy not zeroized | M16 | 🔴 |
| **D61** | LOW | `decaps` no ML-KEM algebraic validity on blob inputs | M18 | 🔴 |
| **D62** | MED | `SortedSet::push` last-write-wins — point replacement | M13 | 🔴 |
| **D63** | LOW | `decode_varint` 10-byte varint desynchronises parse | M13 | 🔴 |

### External Defects (EXT-1 – EXT-3)

| ID | Sev | Description | Fixed? |
|---|---|---|---|
| **EXT-1** | MED | DR spec: Null Decryption Key — `KDF_CK(None)` produces public key | ✅ Nov 2025 |
| **EXT-2** | HIGH | libsignal: Weak state forced storage → FS break | ✅ Mar 2025 |
| **EXT-3** | HIGH | libsignal: X25519 replay via torsion points → duplicate session | ✅ Sep 2025 |


---

## 6. Part I — Unauthenticated Control Plane

SPQR authenticates the *content* of messages (MACs checked after full reassembly) but does
**not** authenticate *control signals* — epoch numbers, message types, acknowledgement flags,
and chunk indices. An attacker who can inject messages can trigger state-machine transitions
that corrupt or deadlock the protocol, even without knowing any keys.

**D21 (HIGH).** A 4-byte message `[1, 2, 1, 0]` advances SPQR to the next epoch without
authentication. The `Authenticator` is never consulted. Result: permanent PQ ratchet deadlock.
Lean: `recv_hdr_chunk_persists_unauthenticated_state` (`ProtocolDoS.lean:156`).

**D35 (MEDIUM).** A forged `Ct1Ack` (5 bytes) stalls both sides — 200 further round-trips
never leave epoch 1.

**D36 (MEDIUM).** A forged `EkCt1Ack` combines D35's stall with D16's chunk poisoning.

**D22 (MEDIUM).** The empty byte string (0 bytes) triggers V0 downgrade. PQ ratchet
permanently disabled.

**D16 (MEDIUM).** Attacker injects a chunk with matching `x` but wrong `y`. `SortedSet::push`
replaces the honest point (D4/D62). Poisoned decoder persisted on `Ok` return. One ~40-byte
message permanently blocks the epoch.

**D15 (MEDIUM).** `add_chunk` guard is always true for low-index chunks, enabling D16.

**D37 (LOW–MED).** With `max_jump = u32::MAX` (Note-to-Self), large `at` causes up to 2³²
HKDF steps before MAC verification.

---

## 7. Part II — Arithmetic and Parameter Bound Failures

`hax_lib::assume!` tells the verifier a condition holds but is **erased at runtime**. When
false, Rust silently misbehaves in release or panics in debug.

**D2 (MEDIUM).** `chain.rs` L192: `at + max_ooo` overflows near `u32::MAX`. Release: valid
key reported as `KeyTrimmed`.

**D25 (MEDIUM).** `Error::InvalidParams` exists but is **never constructed**. With
`max_ooo_keys = u32::MAX`, release stores no keys.

**D29 (MEDIUM).** libsignal Note-to-Self sets `max_jump = u32::MAX`, making D2/D25 reachable.

**D57 (MEDIUM).** `ctr + max_ooo` overflow bypasses `KeyTrimmed` check. Proved in Lean.

**D9 (MEDIUM).** History can grow to 2× the claimed GC threshold (4199 vs 2201 records).

**D3 (LOW).** `epoch_idx` `as usize` truncates on 32-bit. **D5 (LOW).** `PolyEncoder` index
wraps after 65535 chunks. **D8 (LOW).** `trim_size` overflow on 32-bit. **D10 (LOW).**
`chunk_at` div-by-zero on empty encoder. **D27 (LOW).** Oversized `trim_size` disables GC.

---

## 8. Part III — Deserialisation Without Validation

Every `from_pb` function accepts **any protobuf-valid bytes** without checking semantic
validity. Corrupted blobs (from bugs, bad backups, or attacks) cause panics or silent
divergence on the next operation.

**D1 (HIGH).** `ChainEpochDirection::from_pb` — zero validation. Three panic paths:
`next.len() ≠ 32` → panic in `next_key_internal`; `prev.len() % 36 ≠ 0` → panic in `get`;
`prev` too large for `ctr` → panic in `gc`. Proven end-to-end in `CorruptedBlobs.lean`
(48 theorems, 11 phases).

**D43 (HIGH).** `copy_from_slice` crash variant of D1.

**D18 (MEDIUM).** `Chain::from_pb` — `next_root.len() ≠ 32` → silent key divergence;
`links.len() == 0` → underflow panic; `send_epoch > current_epoch` → chain stuck.

**D45 (MEDIUM).** `gc` panics when `ctr < max_ooo_keys` after blob restore.

**D11 (MEDIUM).** `PolyEncoder::from_pb` — inadmissible slot sizes → panic (debug) or wrong
chunks (release).

**D19 (LOW).** `Authenticator::from_pb` — any-length keys accepted. Empty `mac_key` makes
all MACs forgeable. **D23 (LOW).** `epoch == 0` → underflow to `u64::MAX`.
**D44 (LOW–MED).** Same in chunked `from_pb`. **D12 (LOW–MED).** `PolyDecoder::from_pb` —
no size bound. **D46 (LOW).** `pts_needed == 0` → div-by-zero. **D13 (MEDIUM).** Zero
polynomial round-trip fails. **D14 (LOW).** `is_complete` never set — dead field.
**D24 (LOW–MED).** `lib::send` panics on unexpected `EpochSecret`. **D42 (LOW–MED).**
`PolyEncoder::from_pb` accepts arbitrary `idx`.


---

## 9. Part IV — Cryptographic Hygiene

**D26 (LOW).** No `Zeroize` on heap key-holding types (`ChainEpochDirection`, `Chain`,
`Authenticator`). Secret keys persist in freed memory.

**D30 (LOW).** Stack locals holding KEM shared secrets not zeroized.

**D47 (LOW).** `flip_endianness` clones 2080 bytes of secret encapsulation state.

**D60 (LOW).** `encaps1` 32-byte KEM entropy not zeroized on stack.

**D52 (LOW).** `Authenticator::update` IKM = `root_key ‖ shared_secret` without length
prefix — domain separation failure.

**D39 (LOW).** `Authenticator::update` IKM includes unchecked-length `root_key` (via D19).

**D61 (LOW).** `decaps` performs no ML-KEM algebraic validity check on blob inputs.

**D28 (LOW).** `Authenticator` IKM collision when `root_key ‖ ss₁ = root_key' ‖ ss₂`.

**D32/D33 (LOW).** Error variants never constructed; `From` impl maps to wrong error class.

---

## 10. Part V — Lean Trusted-Base Soundness

**D17 (HIGH).** `VecDeque::into_iter` Lean model uses wrong ring-buffer arithmetic and never
terminates. Currently behind `sorryAx` — nothing falsified today, but future round-trip
theorems would be unsound.

**D58 (LOW).** `Option::next_chunk` model panics on `None`. **D59 (LOW).** Eviction loop
proof depends on D17's unsound model.

**D6/D7 (LOW).** Wire-contract observations — not defects.

**D20 (LOW).** Test-only code outside protocol path.

---

## 11. Part VI — New Findings (D38–D63)

These defects extend the original Lean-spec-gap analysis with model checking (D38–D49) and
advanced verification methods (D50–D63). Full details in [`listDefects.md`](./listDefects.md).

**Highlights:**

- **D43 (HIGH)** — `copy_from_slice` crash, a distinct D1 variant found by model checking.
- **D55 (MEDIUM)** — `from_complete_points` fallback computes wrong polynomial in release.
- **D62 (MEDIUM)** — `SortedSet::push` last-write-wins contradicts comment, enabling D16.
- **D51 (MEDIUM)** — `compare` panics on mismatched lengths in constant-time comparison.
- **D38 (MEDIUM)** — `decode_varint` shift overflow produces silent truncation.
- **D50 (MEDIUM)** — `PolyEncoder::next_chunk` `idx` wraps `u16`, producing duplicate chunks.

---

## 12. External: Double Ratchet Defects (EXT-1 – EXT-3)

From Cheval–Jacomme–Richards 2026, affecting the DR layer SPQR composes with. All fixed.

**EXT-1 (MEDIUM).** `KDF_CK(None)` → publicly computable key. No real-world impact. Fixed
Nov 2025.

**EXT-2 (HIGH).** Replayed PQXDH init stores weak state → FS break. Fixed Mar 2025.

**EXT-3 (HIGH).** X25519 torsion-point replay → duplicate session. Fixed Sep 2025.

The paper models SPQR as *completely insecure* and shows DR's FS and PCS still hold,
confirming DR provides a security floor independent of SPQR.


---

## 13. Attacker Model and Network Exploitability

### The key distinction

**SPQR has the bug, but the V1 integration's outer authentication prevents remote
exploitation of blob-sourced defects.** Signal's MAC-before-commit pattern discards mutated
state when the MAC fails. The protection lives in libsignal, not SPQR.

| Property | Network-only | Auth peer | Local storage |
|---|---|---|---|
| Can trigger message-path bugs (D21/D22/D35/D36) in SPQR | Yes | Yes | N/A |
| Mutation persisted (libsignal) | **No** | **Yes** | **Yes** |
| Mutation persisted (raw SPQR) | **Yes** | **Yes** | **Yes** |
| Can trigger blob-path bugs (D1/D18/D23 etc.) | No | No | **Yes** |

### Why SPQR must fix internally

1. **Layering violation.** SPQR's `Authenticator` exists to bind transitions to the shared
   secret. D21/D22/D35/D36 bypass it.
2. **Contract mismatch.** `recv` returns `{ state, key }` implying validity and authenticity.
3. **No embedder guidance.** The crate docs don't require MAC-before-commit.

See [`network.md`](./network.md) and [`classificationBug.md`](./classificationBug.md) for
full analysis.

---

## 14. Global Invariant Composition

A machine-checked composition proof (`invariants_composition_check.lean.txt`, 0 `sorry`)
establishes:

- `Chain::new` establishes the global invariant `ChainInv`.
- `recv_key`, `send_key`, and `add_epoch` preserve `ChainInv`.
- **The invariant is preserved inside one call but not re-established on entry** — `from_pb`
  performs no validation, breaking the inductive argument at the persistence boundary.
- **Arithmetic hypotheses are not invariants:** `ctr ≤ u32::MAX − 390451572` is a fuel bound
  that a peer can push the state out of.

See [`invariantsSPQR.md`](./invariantsSPQR.md) for details.

---

## 15. Root Cause Analysis

### Three systemic patterns

**Pattern 1: Authenticate-after-persist.** State persisted on every `Ok` return; MAC runs
only after full assembly. Affects: D16, D21, D22, D35, D36, D62.

**Pattern 2: `from_pb` copies without validating.** Every `from_pb` copies fields verbatim.
Affects: D1, D11, D12, D13, D14, D18, D19, D23, D24, D27, D31, D42–D46, D49, D61.

**Pattern 3: `assume!` erased at runtime.** Affects: D2, D3, D5, D8, D9, D25, D29, D37,
D56, D57.

### Formal property classification

| Property | Defects | CWE |
|---|---|---|
| Refinement type violation | D1, D11, D12, D18, D19, D43, D45, D46 | CWE-20, CWE-502 |
| Integer overflow | D2, D3, D5, D8, D25, D29, D38, D50, D53, D54, D56, D57 | CWE-190 |
| Authentication ordering | D16, D21, D35, D36, D62 | CWE-345 |
| State-machine liveness | D14, D22, D49 | CWE-672, CWE-841 |
| Spec–impl mismatch | D4, D9, D55, D62 | CWE-684 |
| Missing key erasure | D26, D30, D47, D60 | CWE-404 |
| Domain separation | D52 | CWE-327 |
| Constant-time violation | D41, D51 | CWE-208 |
| Model soundness | D17, D58, D59 | — |

### Cryptographic impact

| Crypto Property | Defects |
|---|---|
| Availability (session liveness) | D1, D21, D35, D43, D45 |
| IND-CPA / Key uniqueness | D2, D5, D29, D50, D57 |
| KDF security / domain separation | D18, D52 |
| MAC unforgeability (EUF-CMA) | D19 |
| Post-compromise security | D14, D16 |
| Forward secrecy | D26, D27, D30, D47, D60 |
| Ciphertext integrity | D55, D62 |


---

## 16. Recommended Fixes (Priority Order)

### Priority 1 — Critical (fix immediately)

| Fix | Closes | Effort |
|---|---|---|
| Validate all fields in `ChainEpochDirection::from_pb` | D1, D43 | Small |
| Gate epoch transitions on authenticated evidence | D21, D35, D36, D22 | Medium |
| Validate in `Chain::from_pb` (`next_root`, `links`, epoch) | D18 | Small |

### Priority 2 — Important (next release)

| Fix | Closes | Effort |
|---|---|---|
| First-write-wins or reset-on-MAC-failure in `add_chunk` | D16, D4, D15, D62 | Small–medium |
| `checked_add`/`saturating_add` for counter arithmetic | D2, D25, D29, D8, D57 | Small |
| Validate `ChainParams` in `initial_state` and `from_pb` | D25, D29, D56 | Small |
| Validate `Authenticator::from_pb` key lengths | D19, D28, D32, D33, D39 | Small |
| Validate `PolyEncoder`/`PolyDecoder` `from_pb` | D11, D12, D34, D42, D46, D49 | Small |
| Reject `epoch == 0`; `checked_sub` in `lib.rs` | D23, D31, D44 | Small |
| Fix `compare` length handling | D41, D51 | Small |
| Fix `from_complete_points` fallback polynomial | D55 | Small |

### Priority 3 — Hardening (schedule when convenient)

| Fix | Closes | Effort |
|---|---|---|
| Add `zeroize` crate; derive `ZeroizeOnDrop` | D26, D30, D47, D60 | Medium |
| Fix zero-polynomial serialisation round-trip | D13 | Small |
| Set `is_complete = true` on success (or delete field) | D14 | Small |
| Guard `lib::send` against unexpected `EpochSecret` | D24 | Small |
| Cap self-session `max_jump` in libsignal | D29, D37 | Small (libsignal) |
| Fix `decode_varint` shift overflow | D38, D63 | Small |
| In-place endianness fix (no clone) | D47 | Small |
| Validate ML-KEM blob inputs | D61 | Small |
| Guard `add_chunk` `GF16::new` truncation | D54 | Small |
| Fix `KeyHistory::gc` assertion | D45 | Small |

---

## 17. How to Verify Each Defect

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

### Step 3: Run Rust counterexamples

Each `docs/*.rs.txt` file contains Rust tests. Copy into `tests/`, rename `.rs.txt` → `.rs`,
and run `cargo test --test <filename> -- --nocapture` (both debug and release).

### Evidence-to-defect mapping

| Evidence file | Defects |
|---|---|
| `protocol_driver_counterexamples.rs.txt` | D21, D22, D23, D25, D29, D37 |
| `forged_control_message_counterexamples.rs.txt` | D35, D36 |
| `decoder_poison_persistence_counterexample.rs.txt` | D16 |
| `decoder_logic_probe.rs.txt` | D12, D14, D15 |
| `corrupted_blob_counterexample.rs.txt` | D1, D18 |
| `polynomial_from_pb_counterexample.rs.txt` | D11 |
| `poly_roundtrip_counterexample.rs.txt` | D13 |
| `key_history_bound_counterexample.{py,rs.txt}` | D9 |
| `vecdeque_into_iter_model_counterexample.lean.txt` | D17 |
| `remote_attacker_harness.rs.txt` | Overall fuzz (40K inputs, 0 panics) |
| `dolev_yao_harness.rs.txt` | D21, D35 network model |
| `invariants_composition_check.lean.txt` | Global invariant composition |
| `Spqr/Specs/Bugs/ProtocolDoS.lean` | D16, D21 |
| `Spqr/Specs/Bugs/CorruptedBlobs.lean` | D1, D18, D19 |
| `Spqr/Specs/Bugs/RoundRobinEmpty.lean` | D10 |

---

## 18. Template for Reporting New Defects

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

- [ ] Assigned stable identifier `D<N>` (next: D64, D65, …)
- [ ] Added to [Master Defect Table](#5-master-defect-table)
- [ ] Severity and qualifier assigned
- [ ] Lean spec file(s) cited
- [ ] Rust source file and line(s) cited
- [ ] Consequence described for debug and release
- [ ] Verification instructions (Lean theorem and/or Rust counterexample)
- [ ] Fix described
- [ ] Cross-references added
- [ ] Added to [Evidence-to-defect mapping](#evidence-to-defect-mapping) if counterexample exists

