# Bug Classification: SPQR vs V1 Protocol

This document classifies bugs found in the SPQR codebase according to three dimensions —
**SPQR-level bug**, **V1 security-relevant robustness problem**, and **remote network
exploitability** — and explains the distinction between bugs intrinsic to SPQR versus
those whose invariants are maintained by the V1 protocol integration.

---

## 1. Classification Dimensions

| Dimension | Meaning |
|---|---|
| **SPQR bug** | A defect in the SPQR library: code accepts input violating its own internal invariants (documented by Lean specs). |
| **V1 security-relevant robustness problem** | The bug has security-relevant effect (DoS, crypto degradation) when exercised through the deployed V1 protocol. |
| **Remote network exploitability** | Whether a purely remote attacker (network-only, no local storage access) can trigger the bug. |

## 2. The Key Distinction

**SPQR has the bug, but the V1 integration's outer authentication prevents remote
exploitation.** SPQR's `from_pb` functions accept protobuf-valid but semantically invalid
states without validation. Signal's MAC-before-commit pattern and the architectural
separation between message-processing and state-loading paths prevent network-only attackers
from injecting malformed fields. The invariant is maintained by the protocol layer, not SPQR.

---

## 3. Bug Type Classification (by Level)

### Level 1 — Unvalidated Deserialization Panic (Session-Bricking DoS)

| ID | Bug | Remote | Severity |
|---|---|---|---|
| L1-1 | `from_pb` admits `next.len() ≠ 32` → panic in `next_key_internal` (L241) | ❌ No | **HIGH** |
| L1-2 | `from_pb` admits `prev.len() % 36 ≠ 0` → panic in `KeyHistory::get` (L191) | ❌ No | **HIGH** |
| L1-3 | `from_pb` admits large `prev` + small `ctr` → panic in `gc` (L149) | ❌ No | **HIGH** |
| L1-4 | `send.next = []` → panic in `next_key_internal` (L229/L243) | ❌ No | **HIGH** |
| L1-5 | `ctr` near `u32::MAX` → debug panic / release silent wrap | ❌ No | **MEDIUM** |

SPQR bug: ✅ | V1 security: ✅ | Remote: ❌
Primary threat: non-adversarial storage corruption (backup bugs, truncated writes, schema skew).


### Level 2 — Silent Semantic Corruption

| ID | Bug | Remote | Severity |
|---|---|---|---|
| L2-1 | `next_root.len() ≠ 32` → silent epoch-key divergence | ❌ No | **LOW–MEDIUM** |
| L2-2 | `Authenticator::from_pb` admits empty keys → weakened HMAC | ❌ No | **LOW** |
| L2-3 | `ctr` wrap in release → wrong key index, potential key reuse | ❌ No | **LOW–MEDIUM** |

SPQR bug: ✅ | V1 security: ✅ | Remote: ❌
`from_pb` returns `Ok` with wrong-semantics fields; corruption is invisible and re-persisted.

### Level 3 — Deserialization-Induced Stall

| ID | Bug | Remote | Severity |
|---|---|---|---|
| L3-1 | `PolyDecoder::from_pb` admits `is_complete = true` → permanent epoch stall | ❌ No | **MEDIUM** |
| L3-2 | Oversized `trim_size` disables GC → forward secrecy loss | ❌ No | **LOW** |
| L3-3 | `send_epoch > current_epoch` → graceful `Err(EpochOutOfRange)` | ❌ No | **LOW** |

SPQR bug: ✅ | V1 security: ✅ | Remote: ❌
Protocol stalls or loses forward secrecy; less severe than Level 1 (no panic).

### Level 4 — Authenticated-Peer Protocol Attack

| ID | Bug | Remote | Severity |
|---|---|---|---|
| L4-1 | `ctr` steering by auth peer (~156K msgs → proof bound, ~172K → overflow) | ⚠️ Auth peer | **LOW** |
| L4-2 | Chunk poisoning: auth peer stores chosen bytes in `PolyDecoder` before SPQR MAC | ⚠️ Auth peer | **MEDIUM** |

SPQR bug: ✅ | V1 security: ✅ | Remote: ⚠️ (authenticated peer only)
Unlike Levels 1–3, these are reachable over the network by an authenticated peer. The
invariant is only partially maintained by V1.

### Level 5 — Non-Security Code Defect

| ID | Bug | Remote | Severity |
|---|---|---|---|
| L5-1 | `SortedSet::push` comment says "noop if present" but replaces | ❌ No | **LOW** |
| L5-2 | `RoundRobinEncoder::chunk_at` panics on empty input (`#[cfg(test)]` only) | ❌ No | **LOW** |
| L5-3 | `PolyDecoder` oversized `pts[i]` — extra points ignored, excess memory only | ❌ No | **LOW** |

SPQR bug: ✅ | V1 security: ❌ | Remote: ❌

---

## 4. Summary Matrix

| Level | Name | SPQR Bug | V1 Security | Remote | Count |
|---|---|---|---|---|---|
| **1** | Unvalidated Deserialization Panic | ✅ | ✅ | ❌ | 5 |
| **2** | Silent Semantic Corruption | ✅ | ✅ | ❌ | 3 |
| **3** | Deserialization-Induced Stall | ✅ | ✅ | ❌ | 3 |
| **4** | Authenticated-Peer Protocol Attack | ✅ | ✅ | ⚠️ Auth peer | 2 |
| **5** | Non-Security Code Defect | ✅ | ❌ | ❌ | 3 |

## 5. Answer: "Bug in SPQR or Invariant Maintained?"

**Both.** The bugs exist in SPQR — its `from_pb` functions perform zero semantic validation.
But the V1 protocol integration maintains the invariant against remote attackers through:

1. **MAC-before-commit**: Signal's envelope MAC authenticates before state commit.
2. **Architectural separation**: Network messages and persisted state use separate paths.
3. **KDF-derived fields**: Panic-class fields (`next`, `prev`, `next_root`) are KDF outputs.

- **Levels 1–3**: SPQR bug ✅, remote exploitability ❌. Invariant maintained by protocol.
- **Level 4**: SPQR bug ✅, remote exploitability ⚠️. Invariant *not* fully maintained.
- **Level 5**: SPQR bug ✅, no security relevance.

## 6. Formal Verification Classification

Classifying each bug by the **formal property** it violates, using standard verification
taxonomy (type safety, state-machine invariants, information-flow properties).

| ID | Formal Property Violated | Category |
|---|---|---|
| L1-1 … L1-4 | **Type-level precondition** — runtime length invariant not enforced by the type system | Refinement type violation |
| L1-5, L2-3 | **Bounded arithmetic** — absence of overflow/wrap proof obligation on `u32` counter | Integer model soundness |
| L2-1 | **Functional correctness** — KDF domain separation requires fixed-length root | Specification conformance |
| L2-2 | **Non-degeneracy precondition** — HMAC with empty key collapses to `H(0-pad ‖ m)` | Cryptographic precondition |
| L3-1 | **State-machine reachability** — `is_complete = true` creates a terminal absorbing state | Liveness / progress violation |
| L3-2 | **Monotonicity invariant** — GC trim must shrink key-history window; oversized = no-op | Safety property (temporal) |
| L3-3 | **Well-ordering** — `send_epoch > current_epoch` violates causal ordering | Causality / happened-before |
| L4-1 | **Bounded-resource assumption** — counter forced past proof bound (~156K) | Parameterised safety bound |
| L4-2 | **Integrity before authentication** — data ingested before MAC verification | Authentication ordering |
| L5-1 | **Spec–impl mismatch** — code semantics (replace) contradicts docs (noop) | Refinement gap |
| L5-2 | **Partial function totality** — `chunk_at` undefined on empty input | Domain totality |
| L5-3 | **Input canonicalization** — extra polynomial points silently ignored | Strictness / canonical form |

### Verification-Strategy Mapping

| Strategy | Applicable Bugs | Notes |
|---|---|---|
| **Dependent / refinement types** (e.g. Lean `Subtype`) | L1-1 … L1-4, L2-1, L2-2 | Encode length and non-emptiness in the type |
| **Bounded model checking** | L1-5, L2-3, L4-1 | Exhaustive counter-range exploration |
| **State-machine model checking** (TLA⁺ / Alloy) | L3-1, L3-3 | Prove liveness + causal ordering |
| **Information-flow typing** | L3-2 | Track taint of retained keys to enforce erasure |
| **Bisimulation / refinement proof** | L5-1 | Prove code refines its spec comment |

---

## 7. Cryptographic Security-Property Classification

Each bug mapped to the standard cryptographic property it degrades (Bellare–Rogaway
IND-CPA/CCA, Cohn-Gordon et al. Signal model, Alwen–Coretti–Dodis PQ ratchet).

| ID | Crypto Property Affected | Impact |
|---|---|---|
| L1-1 … L1-4 | **Availability (session liveness)** | Panic = session destruction; selective DoS |
| L1-5, L2-3 | **IND-CPA / Key uniqueness** | Counter wrap → nonce/key reuse; breaks IND-CPA |
| L2-1 | **KDF security (PRF assumption)** | Non-32-byte root breaks HKDF-SHA256 domain separation |
| L2-2 | **PRF/MAC unforgeability (EUF-CMA)** | Empty key → public hash; anyone can forge tags |
| L3-1 | **Post-compromise security (PCS)** | Stalled epoch prevents KEM re-keying; no healing |
| L3-2 | **Forward secrecy (FS)** | GC disabled → old keys retained; past plaintext exposed |
| L4-1 | **Ratchet security bound** | Peer forces counter past proof bound (~156K) |
| L4-2 | **Ciphertext integrity (INT-CTXT)** | Chosen bytes before MAC = adaptive chosen-ciphertext oracle |

### STRIDE Cross-Reference

| STRIDE | Bug IDs |
|---|---|
| **S**poofing | L2-2 (empty-key HMAC forgery) |
| **T**ampering | L4-2 (chunk injection) |
| **R**epudiation | — (not applicable) |
| **I**nformation Disclosure | L3-2 (forward secrecy loss) |
| **D**enial of Service | L1-1 … L1-5, L3-1 |
| **E**levation of Privilege | L4-1 (beyond proof-bound trust) |

---

## 8. CWE Classification

| ID | CWE | CWE Name |
|---|---|---|
| L1-1 … L1-4 | CWE-20, CWE-502 | Improper Input Validation / Deserialization of Untrusted Data |
| L1-5, L2-3 | CWE-190 | Integer Overflow or Wraparound |
| L2-1 | CWE-130 | Improper Handling of Length Parameter Inconsistency |
| L2-2 | CWE-321 | Use of Hard-Coded / Empty Cryptographic Key |
| L3-1 | CWE-672 | Operation on Resource after Expiration or Release |
| L3-2 | CWE-404 | Improper Resource Shutdown or Release (key not erased) |
| L3-3 | CWE-841 | Improper Enforcement of Behavioral Workflow |
| L4-1 | CWE-400 | Uncontrolled Resource Consumption |
| L4-2 | CWE-345 | Insufficient Verification of Data Authenticity |
| L5-1 | CWE-684 | Incorrect Provision of Specified Functionality |
| L5-2 | CWE-252 | Unchecked Return Value (partial function on empty) |
| L5-3 | CWE-20 | Improper Input Validation (non-canonical input) |

---

## 9. Post-Quantum Ratchet–Specific Classification

| PQ-Ratchet Property | Bug IDs | Explanation |
|---|---|---|
| **KEM encapsulation integrity** | L2-1 | Wrong-length root corrupts the KEM-derived shared secret |
| **Sparse ratchet liveness** | L3-1, L4-1 | Stalled decoder or exhausted counter prevents next KEM round |
| **Polynomial secret-sharing soundness** | L4-2, L5-3 | Injected/extra points violate (k,n)-threshold reconstruction |
| **Epoch monotonicity** | L3-3 | Epoch numbers must be strictly increasing for CKA security |
| **GC-enforced key erasure** | L3-2, L1-3 | Security proof assumes old keys erased after `trim_size` messages |

---

## References

- `docs/CorruptedBlobs.md` — Primary unvalidated deserialization analysis
- `docs/evaluateSPQR.md` — SPQR-level invariant violations (Q1–Q5)
- `docs/evaluateV1.md` — V1 protocol path and remote exploitability (Q-V1–Q8)
- `docs/defects.md` — Code defects from Lean specification theorems
- `docs/report.md` — Initial findings (chunk replacement, poisoning)
