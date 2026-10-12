# Finding Defects in a Post-Quantum Ratchet: A Formal Verification Case Study of Signal's SPQR Library

**Draft — October 2026**

---

## Abstract

We present a formal-verification–driven defect analysis of SPQR (Sparse
Post-Quantum Ratchet), the Rust library that provides post-quantum forward
secrecy and post-compromise security for the Signal messaging protocol. Using
the Aeneas translator, we extracted the Rust sources into Lean 4 and wrote 251
specification files stating pre- and postconditions for the library's
functions. The discipline of machine-checked proof — in which every assumption
must be made explicit — surfaced **63 distinct defects**, each substantiated by
a Lean theorem or an executable Rust counterexample. The dominant defect class
is unvalidated deserialization of persisted session state: 27 defects remain
unfixed, including panics that permanently brick sessions, silent acceptance of
cryptographically degenerate states (e.g., empty MAC keys), protocol stalls
that defeat post-compromise security, and integer overflow/underflow. We show
that while Signal's host application (libsignal) externally mitigates the
message-level attacks, the mitigations are undocumented API obligations that do
not protect other embedders, storage-corruption scenarios, or against an
authenticated-but-malicious peer. Our results demonstrate that specification
extraction is an effective defect-discovery method complementary to testing and
fuzzing.

**Keywords:** formal verification, Lean 4, Aeneas, post-quantum cryptography,
Signal protocol, deserialization, ratchet protocols

---

## 1. Introduction

Modern secure messengers derive their security from *ratchet* protocols that
continually refresh key material, providing forward secrecy (FS) and
post-compromise security (PCS). To resist future quantum adversaries, Signal
introduced SPQR, a sparse post-quantum ratchet built on ML-KEM-768 that
amortizes large KEM ciphertexts across many messages via polynomial
secret-sharing ("chunking").

Cryptographic protocol implementations are notoriously hard to test: the
dangerous states are deep in the state space, and silent key-material
corruption produces no observable failure. We ask: *can writing machine-checked
specifications for an existing implementation serve as a systematic
defect-discovery method?*

**Contributions.**

1. A Lean 4 formalization of SPQR via Aeneas: 251 spec files covering all 39
   Rust source files of the crate.
2. A register of 63 defects, each with severity, root cause, attacker
   model, reproduction evidence, and proposed fix; 15 are confirmed by
   machine-checked Lean theorems, the rest by executable Rust counterexamples.
   Throughout this paper, defects are labelled **D1–D63** in order of
   discovery; each label is defined where first used, and Appendix A gives a
   one-line description of every defect cited in the text.
3. A classification of the defects along cryptographic-property (FS, PCS,
   EUF-CMA, INT-CTXT), CWE, and STRIDE axes, and an analysis of why host-level
   mitigations in libsignal do not close them.
4. A catalogue of 18 detection methods (M1–M18) mapping each verification
   technique to the defect classes it uncovers.

## 2. Background

### 2.1 SPQR

SPQR maintains per-session state: epoch counters, a symmetric key chain
(`chain.rs`), an HMAC authenticator, and polynomial encoder/decoder state for
chunked ML-KEM ciphertext transport (`polynomial.rs`, `encoding/`). The state
is persisted between app launches as a protobuf blob and reloaded through a
family of `from_pb` deserialization functions.

### 2.2 Verification toolchain

We used **Aeneas** to translate the Rust crate (upstream commit `f2589fef`,
v1.5.0, with minimal extraction-enabling patches recorded in
`src-modifications.diff`) into pure Lean 4 functions, then wrote specification
theorems in `Spqr/Specs/` mirroring the Rust module tree. The upstream code
also carries `hax_lib` annotations (`requires`/`assume!`), which are *erased at
runtime* — a fact that itself becomes a defect source (§4.4).

## 3. Methodology

The core observation: a Lean proof of a function's postcondition cannot be
completed unless every needed precondition is stated as a hypothesis. Whenever
a hypothesis is required by the proof but **not enforced by any Rust check**,
we have a candidate defect; we then confirm it by constructing a concrete
counterexample (a Lean theorem of reachability or a Rust reproduction).

Eighteen methods were applied. M1–M12 include model checking, Miri, fuzz-surface
analysis, property testing, panic-path audit, crypto-protocol analysis, and
differential testing. M13–M18 are specification-centric: refinement checking
(gaps between erased `hax` contracts and code), compositional invariant
verification (postconditions must establish the next call's preconditions),
termination/fuel analysis, information-flow typing for secret hygiene, symbolic
state-machine model checking, and a trusted-base/axiom soundness audit of every
`assume!` and `opaque` declaration.

## 4. Findings

The 63 defects fall into four recurring classes. We introduce each defect with
a plain-language description the first time its label appears; Appendix A
summarizes all cited defects in one table.

### 4.1 Unvalidated deserialization → session-bricking panics (HIGH)

SPQR reloads its persisted session state through `from_pb` ("from protobuf")
functions, which accept any protobuf-valid input without checking that the
fields are semantically meaningful. Representative defects:

- **D1 — corrupted chain state crashes on first use.** The epoch key-chain
  deserializer (`ChainEpochDirection::from_pb`, `chain.rs`) copies the `ctr`
  counter and the `next`/`prev` key buffers verbatim. Three later code paths
  then panic on malformed values: a `next` key whose length is not exactly
  32 bytes crashes `copy_from_slice`; a key-history buffer whose length is not
  a multiple of the 36-byte record size fails an `assert_eq!`; and a history
  too large for the counter fails an assertion in garbage collection. Because
  the corrupted blob is written back unchanged and reloaded at every app
  launch, the result is a **permanent crash loop — the session is destroyed**.
  This defect is formalized by 50 Lean theorems in `CorruptedBlobs.lean`.
  **D43** (non-empty but wrong-length `next` key) and **D45** (restored blob
  with a small counter but non-empty key history, panicking on the first
  received message) are refinements of the same missing validation.
- **D23 — epoch zero underflow.** The protobuf default value for an unset
  integer field is `0`, yet the protocol requires `epoch ≥ 1`. All eleven
  state variants accept `epoch = 0`; the next `send` computes `epoch − 1` on
  an unsigned 64-bit integer — a panic in debug builds, and a wrap to
  `u64::MAX` in release builds that leaves the session permanently unable to
  send. **D44** shows the same hole is reachable through all the "chunked"
  state variants as well.

### 4.2 Silent cryptographic weakening (MEDIUM)

These defects do not crash; they quietly produce a cryptographically weaker
state that is invisible to the user and re-persisted.

- **D19 — empty MAC key accepted.** The authenticator deserializer accepts a
  zero-length HMAC key. HMAC with an empty (effectively public) key provides
  no unforgeability: anyone can compute valid authentication tags. Proved in
  Lean (`from_pb_empty_mac_key_forgeable`).
- **D2 and D5 — lossy counter arithmetic.** Message counters are cast between
  integer widths without checks (`u64→u32`, `usize→u16`). Near the maximum
  value, additions wrap silently in release builds, so a *different* key index
  can be derived than intended — risking key reuse, which undermines
  confidentiality (IND-CPA).
- **D11, D12, D46 — degenerate polynomial coder states.** The polynomial
  encoder/decoder (used to split large post-quantum ciphertexts into chunks)
  can be deserialized with point counts the protocol never defines (D11),
  with unbounded per-slot point sets causing quadratic blow-up (D12), or with
  `pts_needed = 0`, under which *zero* points are deemed sufficient and an
  empty decoder "successfully" decodes an empty message (D46).

### 4.3 Protocol stalls defeating post-compromise security (MEDIUM)

A decoder blob restored with its "complete" flag pre-set permanently halts the
current epoch: the ML-KEM re-keying step that gives the protocol its
post-compromise security never finishes, the user sees nothing wrong, and the
stalled state is saved back to disk. Separately, an oversized `trim_size`
parameter disables garbage collection of old message keys, so keys that the
security argument assumes are erased remain in storage — eroding forward
secrecy.

### 4.4 Erased contracts as a systemic root cause

Many of SPQR's invariants exist only as `hax_lib::requires`/`assume!`
annotations — verification hints that **compile to nothing** in the shipped
binary. Our trusted-base audit (method M18) found several sites where the
entire safety argument rests on such an erased annotation, with no runtime
check and no caller-side validation. Examples: the admissible polynomial point
counts of D11; **D21**, where an unauthenticated header chunk mutates decoder
state before any MAC check (the annotation assumes authenticated input); and
**D31**, where an `epoch < u64::MAX` requirement is assumed but never checked,
so a corrupted blob makes the epoch counter wrap to zero. The code is
"verified" against contracts that nothing enforces.

### 4.5 Attacker-model analysis

| Attacker | Reach |
|---|---|
| Network-only | Blocked in **libsignal** by MAC-before-commit (clone session, verify, then persist) — but this mitigation is external, undocumented as an SPQR API requirement, and absent for other embedders. |
| Storage corruption (non-adversarial) | Triggers all blob-class defects (§4.1–4.3); the most realistic threat. |
| Authenticated-but-malicious peer | Can poison decoder state with chosen chunk bytes before any MAC check (**D16/D21**: a crafted chunk with index 0 *replaces* the honest point because insertion is last-write-wins, and the poisoned decoder survives persistence), and can steer counters past the ~156K-message bound assumed by the security proof. |

## 5. Discussion

**Why testing missed these.** The defects live on the *state-reload* path, not
the message path exercised by interoperability tests. Property tests rarely
generate semantically hostile protobufs; fuzzers rarely reach the deep chain
state. Specification extraction inverts the search: instead of hunting inputs,
we enumerate unproved obligations.

**Mitigation layering is fragile.** The security of SPQR as deployed depends on
an invariant (authenticated state commits) maintained by libsignal and nowhere
stated in SPQR's API. This violates the principle that a library should either
enforce or document its preconditions.

**Fixes are cheap.** Nearly all 27 unfixed defects close by (a) field
validation in the `from_pb` family returning `SerializationInvalid`, and (b)
checked arithmetic at a handful of sites.

## 6. Related Work

Cheval, Jacomme & Richards (2026, ePrint 2026/727) analyze the composed Double
Ratchet and report external defects (EXT-1–EXT-3) in the host protocol. Our
work is complementary: we verify the SPQR component itself at the code level.
Aeneas and hax represent the two main Rust-verification pipelines; our findings
on erased `hax` contracts (§4.4) highlight the risk of annotation/enforcement
divergence.

## 7. Conclusion

Writing Lean specifications for SPQR surfaced 63 concrete defects — 27 still
unfixed — dominated by unvalidated deserialization of persisted cryptographic
state. Machine-checked proof turned implicit assumptions into an auditable
defect register. We recommend upstreaming the `from_pb` validation fixes,
documenting the authenticated-state API contract, and maintaining the Lean
specs as a permanent regression barrier.

## References

1. Signal, *SparsePostQuantumRatchet*, commit `f2589fef`. https://github.com/signalapp/SparsePostQuantumRatchet
2. Aeneas: https://github.com/AeneasVerif/aeneas
3. Cheval, Jacomme, Richards. ePrint 2026/727 (`docs/2026-727.pdf`).
4. Project defect register: `docs/listDefects.md` (D1–D63, v2.1, 2026-10-11).
5. Classification: `docs/classificationBug.md`; narrative: `docs/defects.md`.

## Appendix A. Catalog of defects cited in this paper

Defect labels D1–D63 are internal identifiers from the project's defect
register (`docs/listDefects.md`), assigned in order of discovery. The table
below gives a one-line description of every defect cited in the text; the full
register documents all 63.

| ID | One-line description | Severity | Status |
|---|---|---|---|
| D1 | Chain-state deserializer accepts corrupt counters/keys → three distinct panic paths; crash loop on every relaunch | HIGH | Proved in Lean; Rust unfixed |
| D2 | Unchecked `u32` addition in key-history lookup wraps near max → valid key reported as trimmed | MEDIUM | Proved in Lean; Rust unfixed |
| D5 | Lossy `usize→u16` cast of chunk index → silent wrap after 65,536 chunks | MEDIUM | Proved in Lean; Rust unfixed |
| D11 | Polynomial encoder deserializer accepts point counts the protocol never defines → debug panic / wrong chunks | MEDIUM | Unfixed |
| D12 | Polynomial decoder accepts unbounded point sets → oversized output, O(N²) work | LOW–MED | Unfixed |
| D16 | Decoder point insertion is last-write-wins → a peer's crafted chunk replaces the honest point (poisoning) | MEDIUM | Lean fix characterised; Rust unfixed |
| D19 | Authenticator deserializer accepts an empty HMAC key → tags forgeable by anyone | LOW–MED | Proved in Lean; Rust unfixed |
| D21 | Header chunk mutates decoder state before any MAC check (contract erased at runtime) | MEDIUM | Mitigated in libsignal only |
| D23 | `epoch = 0` (protobuf default) accepted → `0 − 1` underflow; session permanently unable to send | MEDIUM | Unfixed |
| D31 | `epoch < u64::MAX` assumed, never checked → epoch wrap to 0 from corrupted blob | LOW–MED | Unfixed |
| D43 | Non-empty but wrong-length `next` key bypasses assert → panic in `copy_from_slice` | HIGH | Unfixed (refines D1) |
| D44 | Epoch-zero hole of D23 also reachable via all chunked state variants | LOW–MED | Unfixed |
| D45 | Restored blob with small counter + non-empty history → assertion panic on first received message | MEDIUM | Unfixed |
| D46 | Decoder accepts `pts_needed = 0` → zero points "sufficient"; empty message decodes successfully | LOW | Unfixed |

### Overall status of all 63 defects

| Status | Count | Defect IDs |
|---|---|---|
| 🔴 Unfixed in SPQR | 27 | D23–D31, D37–D47, D51, D54–D56, D60–D63 |
| 🟢 Confirmed by machine-checked Lean proof (Rust unfixed) | 15 | D1, D2, D3, D5, D8–D15, D18, D19, D57 |
| 🟡 Unfixed, mitigated by libsignal host only | 4 | D21, D22, D35, D36 |
| ✅ Fixed during the project (docs/models/comments) | 13 | incl. D4, D16, D17, D20, D32 |
| 🟢 No fix needed (latent spec observations) | 2 | D6, D7 |
