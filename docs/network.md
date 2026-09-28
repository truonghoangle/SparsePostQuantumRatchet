# Network-Only Attacker Mitigation for Items 24 & 25: Scope, Limits, and Residual Risk

## 1. Executive Summary

Items 24 and 25 from [`defects.md`](./defects.md) are genuine SPQR bugs — unauthenticated
messages that deadlock the PQ ratchet (Item 24) or finalise a V0 downgrade (Item 25). For a
**network-only attacker** (no session keys, no storage access), libsignal's
*clone-then-commit-after-MAC* pattern prevents these mutations from persisting: the corrupted
SPQR state lives on a clone that is discarded when the outer Double Ratchet MAC fails. This
study examines exactly how that mitigation works, why it is insufficient as a complete defence,
and what residual risk remains.

**Key findings:**

| Dimension | Status |
|---|---|
| Network-only attacker (forging) | **Mitigated** — by libsignal, not SPQR |
| Other embedders of the `spqr` crate | **Not mitigated** — the defence is external |
| Authenticated-but-malicious peer | **Not mitigated** — MAC passes, clone is committed |
| SPQR as a standalone library | **Vulnerable** — no internal auth gate on either path |

---

## 2. Background: Items 24 and 25

### 2.1. Item 24 — Unauthenticated epoch advance deadlocks the PQ ratchet

A single 4-byte message `[1, 2, 1, 0]` with `epoch == self.epoch + 1` triggers
`recv_next_epoch` without any authentication check. The `Authenticator` — keyed per epoch
precisely to bind transitions to the shared secret — is never consulted on this edge.

**Effect (reproduced):** B advances to `KeysUnsampled(epoch+1)` and consumes
`recv_key(epoch, 1)`. A remains in the old epoch. Neither side can complete the transition →
**permanent PQ ratchet deadlock in both directions**, plus `recv` hands the caller a
Double-Ratchet chain key for a message that was never authenticated.

*Source:* `defects.md` §24; `d24_unauthenticated_epoch_advance_deadlocks_ratchet` in
[`protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

### 2.2. Item 25 — Empty message finalises a V0 downgrade

When `msg_version(msg) = V0 < state_version = V1` and `version_negotiation.min_version ≤ V0`,
`recv` rebuilds the state with `init_inner(V0) = None` and `version_negotiation: None`. The
**empty byte string** (0 bytes) is a valid downgrade trigger: no MAC, no peer secret required.

**Effect (reproduced):** PQ ratchet permanently disabled (`NegotiationComplete(V0)`); every
subsequent honest V1 message silently returns `Ok` with `state: vec![]`.

*Source:* `defects.md` §25; `d25_unauthenticated_v0_downgrade_with_empty_message` in
[`protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

---

## 3. The Clone-then-Commit-after-MAC Pattern

### 3.1. Mechanism (libsignal `a47ba487`)

`decrypt_message_with_state` in `session_cipher.rs` (lines 599–694) executes:

```
1. Clone the session state                        (L455, L475)
2. Run spqr::recv on the CLONE                    (L633)
3. Run the Double Ratchet decrypt on the CLONE     (L640–655)
4. Verify the envelope MAC                         (L657–661)
5. IF mac passes: commit the clone to the store    (L670–680)
   ELSE:          drop the clone                   (error return)
```

**State is committed only if the entire decrypt returns `Ok`**, which requires the MAC to
verify. Since Items 24 and 25 involve messages with no valid session key material, the MAC
always fails and the mutated clone is discarded.

### 3.2. Evidence

| Source | Finding | Reference |
|---|---|---|
| libsignal source (`a47ba487`) | Clone at L455/L475; MAC precedes commit | [`bugSecurityRemote.md`](./bugSecurityRemote.md) §3 |
| Harness (200 states × 200 forged msgs) | 0 panics, 0 persisted mutations | [`remote_attacker_harness.rs.txt`](./remote_attacker_harness.rs.txt) |
| `CorruptedBlobs.md` §14 | Class A (unauthenticated network) → clone dropped | [`CorruptedBlobs.md`](./CorruptedBlobs.md) §14 |

### 3.3. What it protects against

For a **forging, network-only attacker** — one who cannot produce a valid envelope MAC — both
Items 24 and 25 are dead ends: `spqr::recv` mutates the clone, but `verify_mac` fails and the
clone is dropped. Classification per [`bugSecurityRemote.md`](./bugSecurityRemote.md) §8:
`SPQR bug ✅ / V1 security ❌ / Remote ✅` — reachable but harmless under the deployed
integration.

---

## 4. Why This Mitigation Is Insufficient

The clone-then-commit-after-MAC defence has three structural limitations.

### 4.1. It lives outside SPQR

The `spqr` crate exposes `pub fn recv(state: &[u8], msg: &[u8]) -> Result<Recv>`. This function
**returns the mutated state unconditionally**. Whether that state is committed is entirely up to
the host. libsignal discards it on MAC failure, but the SPQR API contract makes no such promise.

```
    ┌──────────────────────────────────────────────┐
    │           libsignal (safe)                   │
    │  clone → spqr::recv → DR → MAC → commit?    │
    └──────────────────────────────────────────────┘
                         ↑  defence layer
    ┌──────────────────────────────────────────────┐
    │           spqr crate (vulnerable)            │
    │  recv() returns mutated state unconditionally│
    └──────────────────────────────────────────────┘
```

### 4.2. It does not protect other embedders

Any application embedding `spqr` without replicating clone-then-commit-after-MAC is fully
exposed. The crate's API docs do not warn that `recv` may return state corrupted by
unauthenticated input. A test harness, a future embedder that commits before MAC check, or a
protocol using SPQR without an outer MAC are all vulnerable.

### 4.3. It does not stop an authenticated-but-malicious peer

The most important gap. A malicious peer holds the conversation's ratchet keys and **passes the
envelope MAC**, so the mutated clone **is committed**.

| Attacker class | Passes Signal MAC? | Clone committed? |
|---|---|---|
| A — unauthenticated network | No | **No** |
| B — valid envelope, wrong SPQR keys | Yes | Partial |
| C — malicious authenticated peer | Yes | **Yes** |
| D — local / storage | n/a | Yes |

*(From [`CorruptedBlobs.md`](./CorruptedBlobs.md) §14)*

For **Class C**, both items are fully exploitable. The malicious peer can deadlock the PQ
ratchet (Item 24) or permanently downgrade to V0 (Item 25) and blame the stall on the victim.

---

## 5. Attacker Model Comparison

| Property | Network-only (forging) | Dolev-Yao | Authenticated peer |
|---|---|---|---|
| Can forge envelope MAC | No | No | Yes |
| Can trigger Item 24/25 in SPQR | Yes | Yes | Yes |
| Mutation persisted (libsignal) | **No** | **No** | **Yes** |
| Mutation persisted (raw SPQR) | **Yes** | **Yes** | **Yes** |
| Permanent PQ deadlock (24) | No (libsignal) | No (libsignal) | **Yes** |
| Permanent V0 downgrade (25) | No (libsignal) | No (libsignal) | **Yes** |

---

## 6. Why SPQR Must Fix This Internally

1. **Layering violation.** SPQR's `Authenticator` exists precisely to bind state transitions to
   the shared secret. Items 24/25 bypass it — not because it's broken, but because the
   epoch-advance and version-downgrade paths never consult it.

2. **Contract mismatch.** `recv` returns `Recv { state, key }` implying validity and
   authenticity. Item 24 violates both: deadlocked state and unauthenticated chain key.

3. **Specification gap.** Lean proves `recv_hdr_chunk_persists_unauthenticated_state`
   (`Spqr/Specs/Bugs/ProtocolDoS.lean:156`) — the spec identifies the bug; the code doesn't
   fix it.

4. **No embedder guidance.** The crate docs don't require MAC-before-commit. A secure-by-default
   API should not depend on undocumented external invariants.

---

## 7. Recommended Fixes

**Item 24:** Gate epoch advance on authentication — only accept `epoch + 1` from a `Hdr` chunk
after its MAC verifies, or require `mac_hdr`-style authentication on the transition message. At
minimum, never return `key: Some(_)` for a `None`-payload epoch change.

**Item 25:** Require `min_version ≥ V1` by default, or only accept downgrades from messages
carrying authenticated V0 content (not the empty string). Surface the downgrade to the host via
a distinct error/output so it can decide whether to accept.

**API-level:** Document the persistence contract. Consider a richer return type distinguishing
"authenticated transition" from "tentative/pending".

---

## 8. Summary

libsignal's clone-then-commit-after-MAC is an effective **external** mitigation for Items 24/25
against a **network-only** attacker. It is not a substitute for fixing the bugs in SPQR because:

* It lives outside `spqr` and is invisible to other embedders.
* It does not protect against an authenticated-but-malicious peer.
* SPQR's own per-epoch `Authenticator` exists for exactly this purpose and is simply not
  consulted on the affected paths.

The correct fix is internal: authenticate the epoch-advance and version-downgrade paths, and do
not return unauthenticated keys or state to the caller.

---

## References

* [`defects.md`](./defects.md) §24, §25 — Bug descriptions and reproductions
* [`bugSecurityRemote.md`](./bugSecurityRemote.md) §1–8 — Full network-attacker analysis
* [`CorruptedBlobs.md`](./CorruptedBlobs.md) §14 — Attacker classification table
* [`remote_attacker_harness.rs.txt`](./remote_attacker_harness.rs.txt) — Forging-attacker harness
* [`dolev_yao_harness.rs.txt`](./dolev_yao_harness.rs.txt) — Dolev-Yao harness
* [`protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt) — `d24_*`, `d25_*` reproductions
* [`evaluateV1.md`](./evaluateV1.md) §5, §13 — Network-path analysis
* libsignal `a47ba487`: `session_cipher.rs:424–694` — clone-then-commit implementation
