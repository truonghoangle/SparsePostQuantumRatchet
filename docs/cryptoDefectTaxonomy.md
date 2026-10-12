# Cryptographic Defect Taxonomy Applied to SPQR (D1–D63)

This document maps every known SPQR defect (D1–D63, plus three external findings) onto
the standard seven-category classification of cryptographic defects. It is written to
be **readable on its own** — all background needed to understand the findings is included
below. One defect may appear in more than one category when it has multiple facets
(e.g., D1 is both an implementation panic and an input-validation failure).

**Contents:**
[0. Background](#0-background-read-this-first-if-you-are-new-to-the-project) ·
[1. Design](#category-1--design-level-defects-protocol--algorithmic-flaws) ·
[2. Implementation](#category-2--implementation-defects) ·
[3. Randomness](#category-3--randomness--entropy-defects) ·
[4. Key management](#category-4--key-management-defects) ·
[5. Usage/misuse](#category-5--usage--misuse-defects-api-contract-and-kdf-hygiene-errors) ·
[6. Configuration](#category-6--configuration--deployment-defects) ·
[7. Operational/trust boundary](#category-7--operational--trust-boundary-defects) ·
[Worked example](#worked-example-anatomy-of-one-defect-chain) ·
[Summary matrix](#summary-matrix)

---

## 0. Background (read this first if you are new to the project)

### 0.1 What is SPQR?

**SPQR (Sparse Post-Quantum Ratchet)** is a Rust library used by Signal to make its
messaging protocol resistant to future quantum computers. It sits inside Signal's
"Triple Ratchet" — the classical Double Ratchet (DR) plus a quantum-resistant
key-agreement layer built on **ML-KEM-768** (a NIST-standardised lattice-based KEM).
Because ML-KEM public keys and ciphertexts are large (~1–2 KB), SPQR splits them into
small **chunks** using a polynomial secret-sharing erasure code and sends one chunk
alongside each ordinary message. One complete KEM exchange is called an **epoch**;
each completed epoch mixes fresh quantum-resistant secret material into the message keys.

### 0.2 How were the defects found?

This project independently verifies SPQR by translating its Rust into
[Lean 4](https://lean-lang.org/) via [Aeneas](https://github.com/AeneasVerif/aeneas) and
writing **specification theorems** for each function. A defect is found wherever a Lean
spec must *assume* a precondition (e.g., "this byte array has length 32") that the Rust
code never actually checks, or where a proved postcondition exposes surprising behaviour.
63 defects (D1–D63) plus 3 external findings (EXT-1–EXT-3, in the host Double Ratchet) were
catalogued; many have machine-checked Lean counterexample theorems.

### 0.3 Key terms

| Term | Meaning |
|---|---|
| **Blob** | The persisted `pq_ratchet_state` protobuf bytes the app stores between calls |
| **`from_pb` / `into_pb`** | Deserialise state from / serialise state into protobuf |
| **Chain / `ChainEpochDirection`** | Per-epoch symmetric key-derivation state (send or recv direction) |
| **`PolyEncoder` / `PolyDecoder`** | Polynomial secret-sharing codec that splits/reassembles KEM data |
| **`Authenticator`** | HMAC-based message authenticator keyed per epoch |
| **Epoch** | One complete KEM key-exchange cycle; must increase monotonically |
| **FS / PCS** | Forward secrecy (past messages safe after compromise) / post-compromise security (session "heals" after compromise) |
| **HKDF / IKM** | RFC-5869 key-derivation function / its input keying material |
| **EUF-CMA / IND-CPA** | Standard unforgeability (MAC) and indistinguishability (encryption) security notions |
| **GC** | Garbage collection of old out-of-order receive keys (required for FS) |

### 0.4 Attacker model and reach qualifiers

Every defect carries a *reach qualifier* saying who can trigger it:

| Qualifier | Attacker needed |
|---|---|
| `message` | **On-path network attacker** — can read/drop/inject/modify ciphertexts, holds no secret |
| `blob` | Influence over the **persisted state** (backup bug, truncated write, storage corruption, schema skew — usually *non-adversarial*) |
| `config` | A bad `ChainParams` value supplied by the embedding application |
| `32-bit` | Only manifests on 32-bit targets |
| `spec` | Affects soundness of annotations or the Lean trusted base, not runtime |
| auth peer | The **legitimate remote party behaving maliciously** |

**The critical mitigation context:** libsignal (Signal's host library) clones the session,
runs SPQR's receive path, and only commits the state *after* its own MAC verifies. This
"clone-then-commit-after-MAC" pattern externally neutralises the `message`-reachable
defects (D21, D22, D35, D36) for network-only attackers — but the mitigation is
(a) undocumented as an SPQR API requirement, (b) absent for any other embedder of the
crate, and (c) useless against an authenticated-but-malicious peer.

### 0.5 Severity scale

| Level | Meaning |
|---|---|
| **HIGH** | Panic / permanent session destruction reachable from a single input |
| **MEDIUM** | Silent corruption, protocol stall, or cryptographic degradation |
| **LOW** | Latent, needs unrealistic preconditions, or documentation-only |

---

## Category 1 — Design-Level Defects (Protocol / Algorithmic Flaws)

**General definition.** The scheme itself is attackable even when implemented perfectly:
weak primitives, missing authentication of protocol messages, downgrade paths, replay
windows, or absent security properties. Historic examples: POODLE/FREAK (downgrade),
unauthenticated renegotiation in TLS.

**In SPQR.** No weak primitives exist (ML-KEM-768, HKDF-SHA256, HMAC are all sound).
Every design defect is instead in the **unauthenticated control plane**: protocol-state
transitions (epoch advance, acknowledgements, version negotiation, chunk acceptance) that
take effect *before* any MAC binds them to the peer. An attacker who can't read a single
message can still steer the state machine.

| ID | Defect | Explanation |
|---|---|---|
| **D21** | Unauthenticated epoch advance deadlocks PQ ratchet (HIGH) | The protocol accepts an epoch-advance control message *before* MAC verification binds it to the session. An on-path attacker can advance the receiver's epoch; the ratchet deadlocks. This is a **protocol-flaw** classic: control plane not covered by authentication. |
| **D22** | Empty message finalises V0 downgrade (MEDIUM) | A network attacker can confirm a downgrade from the PQ-protected V1 to V0 with an unauthenticated empty message — a textbook **downgrade attack** (same family as POODLE/FREAK). The post-quantum guarantee is silently removed. |
| **D35 / D36** | Unauthenticated `Ct1Ack` / `EkCt1Ack` stall the epoch and poison the `ek` decoder (MEDIUM) | Acknowledgement messages drive the KEM state machine but are not authenticated. Forged acks stall KEM re-keying → **post-compromise security (healing) is lost**. |
| **D15 / D16 / D62** | `add_chunk` guard always true for low-index chunks; chunk poisoning persists → permanent epoch stall; `SortedSet::push` last-write-wins allows point replacement (MEDIUM) | The sparse polynomial secret-sharing design lets an authenticated-but-malicious peer (or pre-MAC attacker) insert chosen points into the `PolyDecoder` that are persisted *before* the SPQR MAC runs. The (k,n)-threshold reconstruction soundness assumption is violated by design of the chunk-acceptance path. |
| **D37** | Self-session removes HKDF-walk bound → pre-MAC CPU DoS (LOW–MEDIUM) | The design allows an attacker to force a long HKDF key-derivation walk before any authentication check — **resource-exhaustion by protocol design**. |
| **D29** | Self-session `max_jump = u32::MAX` (MEDIUM) | A design decision (unbounded jump for self-sessions) feeds the arithmetic defects D2/D25. |
| **EXT-1–EXT-3** | External Double Ratchet defects (Cheval–Jacomme–Richards 2026) | Flaws in the host protocol SPQR composes with — pure design-level findings outside this crate. |

**Why this category matters most here:** D21/D22/D35/D36 are the only *network-reachable*
(message-qualifier) defects. libsignal's clone-then-commit-after-MAC pattern mitigates them
externally, but the mitigation is undocumented, lives outside SPQR, and does not protect
other embedders or against an authenticated-but-malicious peer.

---

## Category 2 — Implementation Defects

**General definition.** The scheme is sound, the code is wrong: side-channel leaks,
non-constant-time comparisons, buffer bugs (Heartbleed), padding oracles, or plain logic
errors in the crypto path.

**In SPQR.** No memory-unsafety (Rust + Miri audit) and no timing side channels were
found. Instead the implementation defects fall into three sub-patterns: (a) **panic paths**
— Rust panics on malformed state, and since the state is reloaded on every app start, one
panic becomes a *crash loop = permanent session destruction* (availability is a security
property of a secure channel); (b) **integer overflow/truncation** — silent wraps that
violate uniqueness assumptions the crypto depends on; (c) **wrong-result bugs** — code
paths that silently produce incorrect cryptographic output.

### 2a. Panic / crash-loop paths (availability failures)

| ID | Defect | Explanation |
|---|---|---|
| **D1 / D43** | `ChainEpochDirection::from_pb` — three panic paths; `next.len() != 32` panics in `copy_from_slice` (chain.rs L243) (HIGH) | A corrupted blob bricks the session: every load → panic → crash loop. Proved in Lean by 48+ theorems in `CorruptedBlobs.lean`. |
| **D45** (+ D1 row 2) | `KeyHistory::get` panics on `prev.len() % 36 ≠ 0` (D1 family); `gc` asserts `ctr ≥ max_ooo_keys` (chain.rs L149) (MEDIUM–HIGH) | First `recv_key` after restoring a corrupted blob panics. *(Note: the ID "D40" appears only in fix-status counts elsewhere; it has no entry of its own — the defect numbering jumps D39 → D41. Documentation gap in the project's defect catalogue.)* |
| **D24** | `lib::send` panics on `assert!(key.is_none())` (LOW–MEDIUM) | Internal invariant enforced by `assert!` instead of an error return. |
| **D10 / D58** | `RoundRobinEncoder::chunk_at` panics on empty; `Option::next_chunk` `unwrap()` on `None` (LOW) | Partial functions called without totality guards. |
| **D41 / D51** | `compare` (constant-time comparison) **panics on mismatched lengths** (MEDIUM) | Doubly ironic: the constant-time primitive itself is a DoS vector. The length check should return `false`/error, not panic. |
| **D48** | `kdf::hkdf_to_slice` panics when `okm > 255 × hash_len` (LOW) | HKDF RFC-5869 output-length limit enforced by panic rather than `Result`. |

### 2b. Integer overflow / truncation (CWE-190/CWE-197)

| ID | Defect | Explanation |
|---|---|---|
| **D2 / D57** | `u32` overflow in `KeyHistory::get`; `ctr + max_ooo` overflow bypasses `KeyTrimmed` check (MEDIUM) | Counter wrap → wrong key index → potential **key reuse**, which breaks IND-CPA (nonce/key uniqueness). |
| **D3 / D53** | `u64→usize` truncation in `epoch_idx` on 32-bit (MEDIUM) | On 32-bit targets, two distinct epochs can map to the same index → **silent key mismatch / divergence**. |
| **D5 / D50 / D54** | `PolyEncoder` `u32→u16` index truncation; `next_chunk` idx wraps `u16` → duplicate chunk indices; `GF16::new(poly_idx as u16)` truncates x-coordinates (MEDIUM) | Duplicate x-coordinates violate Lagrange-interpolation preconditions → wrong reconstructed ciphertexts. |
| **D8 / D27 / D56** | `trim_size` `usize` overflow on 32-bit; oversized `trim_size` silently disables GC (LOW) | GC disabled → old keys never erased → **forward secrecy loss** (see Category 4). |
| **D23 / D44** | `epoch == 0` blob → `0u64 − 1` underflow in `lib::send` (debug panic, release wrap to `u64::MAX`) (LOW–MEDIUM) | Session permanently stuck returning `EpochOutOfRange` in release builds. |
| **D31** | No `epoch < u64::MAX` guard → `epoch + 1` wraps to 0 (LOW–MEDIUM) | Mirror of D23 at the top of the range. |
| **D34** | `PolyDecoder::into_pb` truncates `pts_needed: usize → u32` (LOW) | Serialisation lossy on pathological values. |
| **D38 / D63** | `decode_varint` shift overflow → silent truncation; 10-byte varint desynchronises parse position (MEDIUM/LOW) | Wire-format parser accepts non-canonical encodings and silently corrupts the stream — message-reachable. |

### 2c. Wrong-result / semantic implementation bugs

| ID | Defect | Explanation |
|---|---|---|
| **D13** | `Poly::serialize`/`deserialize` not inverses on the zero polynomial (MEDIUM) | Round-trip property fails — proved by `serialize_deserialize_zero_roundtrip_fails`. |
| **D55** | `from_complete_points` fallback computes the wrong polynomial in release builds (MEDIUM) | `debug_assert!(false)` arm falls through to an undefined Lagrange path in release → silently wrong chunks. |
| **D14 / D49** | `PolyDecoder::is_complete` is write-never (dead field), and not validated on `from_pb` (LOW) | A blob with `is_complete = true` permanently stalls the epoch (bridges to Category 1 PCS loss). |

---

## Category 3 — Randomness / Entropy Defects

**General definition.** Weak or predictable RNGs, seed reuse, low entropy, backdoored
generators (Dual_EC_DRBG), and nonce/IV reuse (GCM nonce reuse, the PlayStation 3 ECDSA
nonce-reuse key leak).

**In SPQR: largely clean.** SPQR delegates randomness to the caller and the audited
`libcrux-ml-kem` implementation; the Lean audit found no RNG defects. However, two
arithmetic defects reproduce the *effect* of nonce reuse — the protocol assumes certain
values are unique and the implementation can silently repeat them:

| ID | Defect | Explanation |
|---|---|---|
| **D50** (facet) | Duplicate chunk indices from `u16` wrap | Not an RNG bug, but produces the *effect* of nonce reuse: non-unique indices where the protocol assumes uniqueness. |
| **D2/D57** (facet) | Counter wrap → key-index reuse | Same "uniqueness assumption violated by arithmetic" pattern — the PQ analogue of ECDSA nonce reuse, via counters rather than random nonces. |

---

## Category 4 — Key Management Defects

**General definition.** Hardcoded keys, insecure key storage, missing rotation/erasure,
poor key generation (shared RSA primes — ROCA), and keys accepted without validation
(CWE-321).

**In SPQR.** The dominant hygiene weakness is that **secrets are never erased**: no type
in the crate implements `Zeroize`, so chain keys, message keys and KEM secrets survive in
freed memory. This directly undermines the *point* of a ratchet — forward secrecy assumes
old keys are destroyed. All findings here need a *local* attacker (memory disclosure, core
dump, swap, cold boot), hence LOW severity, except D9/D19 which are proof-level.

| ID | Defect | Explanation |
|---|---|---|
| **D26** | No `Zeroize` on heap key-holding types (LOW) | Chain keys, message keys and KEM secrets remain in freed heap memory; recoverable by local memory disclosure (core dump, swap, cold boot). |
| **D30** | No `Zeroize` on stack secrets (LOW) | Same for stack-resident intermediate secrets. |
| **D47** | `flip_endianness_of_encapsulation_state` leaks a secret copy (LOW) | An extra unzeroized copy of KEM secret state is created during endianness conversion. |
| **D60** | `encaps1` — 32-byte KEM entropy not zeroized on stack (LOW) | The encapsulation randomness (equivalent to the shared-secret seed) lingers on the stack. |
| **D8 / D27 / D56** | GC disabled by `trim_size` overflow (LOW) | **Key-erasure failure**: the security proof assumes old receive keys are deleted after `trim_size` messages; overflow retains them indefinitely → forward secrecy breaks for past messages if the device is later compromised. |
| **D9** | Claimed key-history bound is false (MEDIUM spec) | The documented bound on retained keys is disproved (`claimed_history_bound_false`, counterexample in `key_history_bound_counterexample.py`) — more old keys live than the design claims. |
| **D19** | `Authenticator::from_pb` admits **empty MAC keys** (LOW; blob) | Proved forgeable in Lean (`from_pb_empty_mac_key_forgeable`, `from_pb_mac_key_attacker_controlled`): an empty HMAC key makes tags publicly computable → **EUF-CMA broken**. CWE-321 territory. |

---

## Category 5 — Usage / Misuse Defects (API-contract and KDF-hygiene errors)

**General definition.** Sound primitives used incorrectly: ECB mode, fast hashes for
passwords, encryption without a MAC, disabled certificate validation, ambiguous inputs
fed to a KDF.

**In SPQR.** The misuse pattern here is **KDF input-encoding ambiguity**: HKDF is a sound
PRF, but if two semantically different inputs can serialise to the same IKM byte string,
two different protocol states derive the *same* key — the proof's domain-separation
assumption silently fails. Plus several API contracts that set traps for integrators.

| ID | Defect | Explanation |
|---|---|---|
| **D52** | `Authenticator::update` IKM concatenation lacks length prefixes → **domain-separation failure** (LOW) | Two distinct `(a, b)` input pairs can concatenate to identical IKM byte strings → identical derived keys. Classic KDF-misuse pattern (ambiguous encoding into a hash/KDF). |
| **D28** | `Authenticator` IKM collision (LOW) | Concrete instance of the same ambiguity: distinct states collide to the same authenticator key. |
| **D39** | `Authenticator::update` IKM includes `root_key` of unchecked length (LOW) | A non-32-byte root (reachable via D18) feeds HKDF with out-of-contract input, breaking the PRF-assumption domain the proof relies on. |
| **D7** | `decode_varint` contract inconsistency (LOW; spec) | Caller-facing contract and behaviour disagree — API-misuse trap for integrators. |
| **D6** | `decode_chunk` cursor advanced on error paths (LOW; spec) | Error paths leave the parser in a state callers won't expect — misuse-prone API. |
| **D33** | `From<authenticator::Error>` maps to the wrong error class (LOW) | Callers matching on error class take the wrong recovery path. |

---

## Category 6 — Configuration & Deployment Defects

**General definition.** For servers: weak cipher suites, legacy protocol versions, expired
certificates. For a *library* like SPQR, the equivalents are **runtime parameters**
(`ChainParams`: `max_jump`, `max_ooo_keys`, `trim_size`) and **target-platform
assumptions** (pointer width). The common failure: the library documents valid ranges but
never enforces them, so the embedder's configuration silently activates arithmetic defects.

| ID | Defect | Explanation |
|---|---|---|
| **D25** | `ChainParams` never range-checked — `InvalidParams` is dead code (MEDIUM) | The validation machinery exists but is never invoked: any embedder passing bad params (e.g., `max_jump = u32::MAX`, huge `max_ooo_keys`) silently gets the arithmetic defects D2/D8/D56/D57. |
| **D29** | Self-session configuration sets `max_jump = u32::MAX` (MEDIUM) | A shipped configuration that activates D2/D25. |
| **D3 / D8 / D53** | 32-bit-target truncation/overflow (LOW–MEDIUM) | Deployment-environment defects: correct on 64-bit, broken on 32-bit targets (older Android devices are in scope for Signal). |
| **D48** | HKDF output-length limit vs config (LOW) | Config-derived okm length can exceed RFC-5869's 255×hash_len → panic. |

---

## Category 7 — Operational / Trust-Boundary Defects

**General definition.** Traditionally: key leakage via insiders, poor operational
practices, unpatched known vulnerabilities. For a verified library, the operational layer
is (a) the **persisted-blob trust boundary** — the undocumented assumption that storage
returns exactly the bytes written — and (b) the **soundness of the verification trusted
base** itself (hand-written Lean models of Rust stdlib types, axioms, annotations): if a
trusted model is wrong, every proof built on it can silently vouch for false claims.

### 7a. Blob trust boundary — unvalidated deserialization (CWE-502)

The single largest systemic pattern: **11+ `from_pb` paths accept protobuf-valid but
semantically invalid state**. The operational assumption "storage is trusted" is undocumented
and violated in practice by backup bugs, truncated writes, and schema skew.

| ID | Defect |
|---|---|
| **D11 / D42** | `PolyEncoder::from_pb`: no per-poly point-count validation; arbitrary `idx` |
| **D12 / D46** | `PolyDecoder::from_pb`: unbounded point-set sizes; `pts_needed == 0` → zero `necessary_points` for all polys |
| **D18** | `Chain::from_pb`: no `next_root` length / `links` / epoch-inversion validation (proved: `chain_from_pb_admits_wrong_next_root`, `..._epoch_inversion`, `..._empty_links`) |
| **D19** | `Authenticator::from_pb`: no key-length validation (→ Category 4) |
| **D23 / D31 / D44** | epoch range never validated on restore |
| **D61** | `decaps`: no ML-KEM algebraic-validity check on blob-restored ciphertexts — the FO-transform guarantee assumes well-formed inputs |

### 7b. Trusted-base soundness (meta-level: defects in the *verification*, not the code)

| ID | Defect | Explanation |
|---|---|---|
| **D17 / D59** | `VecDeque::into_iter` Lean model wrong when `head ≠ 0`; eviction-loop proof depends on it (HIGH spec) | An unsound trusted-base model can "prove" false theorems about the Rust code — the verification analogue of a backdoored primitive. (D17 fixed.) |
| **D4** | `SortedSet::push` comment contradicts replacement semantics (MEDIUM; spec) | A false annotation propagated into specs; behavioural twin is D62. (Fixed.) |
| **D9** | False documented bound (see Category 4) | Documentation claims the proof does not support. |
| **D20 / D32** | Test-only code in tree; dead error variants (LOW) | Audit hygiene findings. |

---

## Worked example: anatomy of one defect chain

To see how categories compose, follow the **D19 → D39 chain** end-to-end:

1. **Trust boundary (Cat. 7a).** `Authenticator::from_pb` (`src/authenticator.rs`)
   deserialises `root_key` and `mac_key` from the persisted blob with **no length check**.
   A corrupted backup can restore a `root_key` of any length — including empty (D19).
2. **Key management (Cat. 4).** An empty HMAC key means every MAC tag is computable by
   anyone — unforgeability (EUF-CMA) collapses. Proved in Lean:
   `from_pb_empty_mac_key_forgeable`.
3. **Usage/misuse (Cat. 5).** `Authenticator::update` builds its HKDF input as
   `[root_key, k].concat()` (L45) with no length prefix. With a wrong-length `root_key`,
   the two peers feed *different* IKM to HKDF (D39) — and the ambiguous concatenation also
   allows distinct states to collide to the same key (D28/D52).
4. **Consequence.** After one `update`, the peers hold different `mac_key`s; every future
   MAC fails; the session is **permanently broken** and cannot heal. Formalised in Lean:
   `update_diverges_on_bad_root_key` (`Spqr/Specs/Authenticator/Authenticator/Update.lean`).
5. **The fix** is a Category-7 fix: validate `root_key.len() == 32` in `from_pb` — which
   simultaneously discharges the Cat. 4 forgery and the Cat. 5 divergence.

This pattern — *one missing `from_pb` check cascading through three taxonomy categories* —
recurs across roughly a third of all findings and is why the recommended remediation is a
single uniform validation layer at deserialisation.

---

## Summary Matrix

| Category | Defect IDs | Count | Worst severity |
|---|---|---|---|
| 1. Design / protocol | D15, D16, D21, D22, D29, D35, D36, D37, D62, EXT-1–3 | 12 | **HIGH** (D21) |
| 2. Implementation | D1–D3, D5, D10, D13, D14, D23, D24, D31, D34, D38, D41, D43–D45, D48–D51, D53–D55, D57, D58, D63 | 26 | **HIGH** (D1/D43) |
| 3. Randomness | — (facets of D2, D50, D57 only) | 0 direct | — |
| 4. Key management | D8, D9, D19, D26, D27, D30, D47, D56, D60 | 9 | MEDIUM (D9) |
| 5. Usage / misuse | D6, D7, D28, D33, D39, D52 | 6 | LOW |
| 6. Configuration | D3, D8, D25, D29, D48, D53 | 6 | MEDIUM (D25) |
| 7. Operational / trust boundary | D11, D12, D18, D19, D23, D31, D42, D44, D46, D61 (blob) + D4, D9, D17, D20, D32, D59 (trusted base) | 16 | HIGH-spec (D17) |

### Headline observations

1. **No broken primitives.** Unlike typical crypto audits, Category 1 contains no weak
   algorithms — ML-KEM-768, HKDF-SHA256 and HMAC are all sound choices. The design defects
   are all in the *unauthenticated control plane* (D21/D22/D35/D36).
2. **The dominant root cause is a trust-boundary error** (Category 7a): `from_pb` treats the
   persisted blob as trusted, while the Lean specs demonstrably require invariants the code
   never checks. One fix pattern — validate in every `from_pb`, return `SerializationInvalid`
   — closes ~20 defects.
3. **Panics are cryptographic defects here**: a panic on state load is a crash loop =
   permanent session destruction, i.e. an availability break of the secure channel.
4. **Key hygiene is uniformly weak** (no `Zeroize` anywhere: D26/D30/D47/D60) but low
   severity because exploitation needs local memory disclosure.
5. **The verification itself has a defect class** (Category 7b): unsound trusted-base models
   (D17/D59) could mask any of the above — a category unique to formally verified projects.

## Further reading (optional)

Readers wanting per-defect reproduction evidence, Lean theorem sources, CWE/STRIDE
mappings, or the full attacker-model discussion can consult the other reports in this
`docs/` directory; this document stands alone and none of them are required to follow
the classification above.

