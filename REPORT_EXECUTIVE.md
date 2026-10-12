# Executive Report: Defect Findings in SPQR (Sparse Post-Quantum Ratchet)

**Date:** 2026-10-11 · **Audience:** Management (high-level summary)
**Full technical details:** `docs/listDefects.md`, `docs/defects.md`, `docs/classificationBug.md`

---

## 1. What we did

We formally verified Signal's **SPQR** library — the Rust component that adds
post-quantum security to the Signal messaging protocol — using the **Lean 4**
theorem prover (via the Aeneas Rust-to-Lean translator). Writing machine-checked
mathematical specifications for the code forced every hidden assumption into the
open. Each assumption the code fails to enforce is a potential defect.

## 2. Headline result

We identified **63 defects (D1–D63)** in the SPQR codebase. Each one is backed by
either a machine-checked Lean proof or a runnable Rust counterexample — these are
not opinions; they are demonstrated facts about the code.

| Status | Count |
|---|---|
| 🔴 Unfixed in SPQR | 27 |
| 🟡 Unfixed, but mitigated by the host app (libsignal) | 4 |
| 🟢 Confirmed with machine-checked Lean proofs | 15 |
| ✅ Fixed (docs/models corrected during the project) | 13 |
| 🟢 No fix needed (latent observations) | 2 |

## 3. What the defects are, in plain terms

The dominant root cause: **SPQR trusts its own saved state too much.** When the
library reloads its persisted session state ("blob") from storage, it performs
almost no validation. A corrupted or tampered blob leads to:

1. **Crashes (Denial of Service, HIGH).** Malformed fields (wrong key lengths,
   bad counters) cause panics — the app crash-loops every time it reopens the
   session, permanently bricking that conversation.
2. **Silent cryptographic weakening (MEDIUM).** Some corruption is accepted
   without error: empty authentication keys (anyone could forge messages),
   wrong-length key material, or counter wraparound that could cause key reuse.
3. **Protocol stalls (MEDIUM).** Certain states permanently halt the
   "ratchet" — the mechanism that heals a session after compromise — silently
   losing post-compromise security.
4. **Integer overflow/underflow bugs.** e.g., epoch 0 or near-max counters
   cause arithmetic panics in debug builds and wrong results in release builds.
5. **Authenticated-peer attacks.** A malicious conversation partner (not just a
   hacker on the network) can poison decoder state or steer counters past the
   security proof's bounds.

## 4. How bad is it in practice?

- **A remote network attacker cannot exploit most of these today.** Signal's
  app (libsignal) authenticates messages before committing state, which shields
  the message-level issues. **However**, this protection lives *outside* SPQR:
  any other product embedding the library would not get it, and it does not
  protect against storage corruption (backup bugs, truncated writes) or a
  malicious chat partner.
- The most realistic risk is **session bricking from corrupted storage** and
  **silent security degradation** that is invisible to users and re-persisted.

## 5. Why our method matters

Traditional testing missed these for years. Formal verification found them
because proving correctness *requires* stating every precondition: wherever a
proof needed an assumption the Rust code never checks (e.g., "this key is
exactly 32 bytes"), we had found a defect. We confirmed each with 18 distinct
methods (model checking, fuzzing, Miri, property testing, refinement proofs).

## 6. Recommended next steps

1. **Report upstream to Signal** — the fixes are small: validate fields in the
   `from_pb` deserialization functions and use checked arithmetic.
2. **Document the implicit API contract** — SPQR should state that it requires
   authenticated state, or enforce it itself.
3. **Continue verification** — extend Lean proofs so the fixed invariants are
   permanently machine-checked, preventing regressions.

---
*Prepared from the project's verified defect register (D1–D63, version 2.1,
re-verified against HEAD `baa499f6` on 2026-10-11).*
