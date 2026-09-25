# Report II: Can Unauthenticated or Malformed Inputs Permanently Corrupt Persisted Protocol State?

**Scope:** All paths in SPQR where external inputs (wire messages or deserialized state
blobs) flow into state that is subsequently serialized and persisted via protobuf.

**Answer: Yes.** Multiple independent mechanisms allow unauthenticated or malformed
inputs to permanently corrupt persisted protocol state.

---

## Architectural Root Cause

SPQR's `recv()` (`lib.rs:356–454`) follows a **process-then-persist** pattern:
deserialize state → process message → serialize new state → return. The state machine
advances and the new state is returned for persistence **before** full message
authentication completes. MAC verification only runs after full chunk assembly, but
each intermediate chunk advances decoder state persisted on `Ok` returns.

---

## BUG 1 — Poisoned Decoder Chunk Permanently Stalls Epoch (CRITICAL)

**Files:** `send_ek.rs`, `send_ct.rs`, `states.rs`, `encoding/polynomial.rs`

The `PolyDecoder` accumulates chunks in a `SortedSet<Pt>` where equality compares only
`x` (`polynomial.rs:60–63`), so a new point with matching `x` but different `y` is
silently discarded. Chunks are **not individually authenticated**; MAC runs only after
full decode. A chunk with `index < necessary_points` is unconditionally accepted
(`polynomial.rs:895`).

When `States::recv()` processes a chunk, `add_chunk` poisons the decoder. If
`decoded_message()` returns `None`, the poisoned state is returned as `Ok` and
persisted. When honest chunks complete, interpolation produces garbage → MAC fails →
`Err` → caller keeps pre-call poisoned state. Index re-emitted only after 65,536 wraps.

**Affected transitions:** `send_ek.rs:129–148`, `send_ek.rs:194–222`,
`send_ct.rs:82–107`, `send_ct.rs:131–197`, `send_ct.rs:255–276`.

**Cost:** One ~40-byte unauthenticated message permanently blocks the epoch.

---

## BUG 2 — Chain `from_pb` Has No Validation — Panics from Corrupted Blobs (HIGH)

**File:** `chain.rs:306–312`

`ChainEpochDirection::from_pb` performs zero validation on deserialized fields.
Downstream consumers require `next.len() == 32` (panic in `next_key_internal` L241),
`prev.data.len() % 36 == 0` (panic in `KeyHistory::get` L186), and `max_ooo ≤ ctr`
(panic in `gc` L149). A corrupted state blob causes panics on next `send()`/`recv()`,
permanently bricking the session.

---

## BUG 3 — Authenticator `from_pb` Accepts Arbitrary-Length Keys (MEDIUM)

**File:** `authenticator/serialize.rs:16–21`

No validation that `root_key.len() == 32` or `mac_key.len() == 32`. Truncated/empty
keys produce weak HMAC output. Persists through subsequent serialize cycles.

---

## BUG 4 — `epoch == 0` in All `from_pb` Variants → Underflow (MEDIUM)

**Files:** `v1/unchunked/send_ct/serialize.rs`, `v1/unchunked/send_ek/serialize.rs`

All unchunked `from_pb` accept `epoch == 0`. At `lib.rs:427`:
`msg_key_epoch = scka_msg.epoch - 1` underflows to `u64::MAX`, causing out-of-range
chain indexing. The corrupted `epoch == 0` state persists.

---

## BUG 5 — Unverified ct1 Persisted Before MAC Check (MEDIUM)

**File:** `v1/chunked/states.rs:399–413`, `v1/chunked/send_ek.rs:129–148`

When `HeaderSent::recv_ct1_chunk` completes decoding, state transitions to
`Ct1Received` storing unauthenticated `ct1`. This is persisted. The ct1 is only
verified much later when ct2+MAC arrive. Malformed ct1 causes `decaps` to produce
wrong shared secret, permanently desynchronizing the session.

---

## BUG 6 — `PolyDecoder::from_pb` Accepts Inconsistent Point Sets (MEDIUM)

**File:** `encoding/polynomial.rs:835–868`

No validation that point count is consistent with `pts_needed`, no duplicate-x check,
no message-size consistency check. A corrupted blob creates a decoder that produces
garbage immediately or has permanent silent decoding failures.

---

## BUG 7 — `u32` Overflow in `KeyHistory::get` (MEDIUM)

**File:** `chain.rs:192`

`at + max_ooo` wraps around near `u32::MAX`, causing valid keys to be erroneously
reported as `KeyTrimmed`. Persistent: corrupted `ctr` value stays in serialized state.

---

## BUG 8 — `PolyEncoder` idx `u32→u16` Truncation (LOW)

**File:** `encoding/polynomial.rs:735`

`from_pb` stores `idx` as `u32` but `chunk_at` truncates to `u16`. Persisted state
with `idx > 65535` wraps, potentially colliding with poisoned points from Bug 1.

---

## BUG 9 — `hax_lib::assume!` Guards Erased at Runtime (LOW)

`send_ek.rs:161` (`epoch < u64::MAX`), `chain.rs:86` (`max_ooo < 390451572`),
`states/serialize.rs:236,243` (`into.len() > 0`). No runtime enforcement. Violated
assumptions persist through serialization.

---

## Summary Table

| # | Severity | Bug | Input Source | Persists? |
|---|----------|-----|-------------|-----------|
| 1 | **CRITICAL** | Poisoned decoder → permanent stall | Unauth wire msg | ✅ |
| 2 | **HIGH** | Chain `from_pb` → panics | Corrupted blob | ✅ |
| 3 | MEDIUM | Auth `from_pb` no key-length check | Corrupted blob | ✅ |
| 4 | MEDIUM | `epoch == 0` → u64 underflow | Corrupted blob | ✅ |
| 5 | MEDIUM | Unverified ct1 persisted before MAC | Unauth wire msg | ✅ |
| 6 | MEDIUM | `PolyDecoder::from_pb` inconsistent | Corrupted blob | ✅ |
| 7 | MEDIUM | `u32` overflow in `KeyHistory::get` | Corrupted blob | ✅ |
| 8 | LOW | Encoder idx truncation | Corrupted blob | ✅ |
| 9 | LOW | `assume!` erased at runtime | Long session/blob | ✅ |

---

## Recommendations

1. **Authenticate before persisting.** Buffer chunks without modifying decoder state
   until full message MAC verification, or add per-chunk authentication.
2. **Validate all `from_pb` paths.** Check `next.len() == 32`, `prev.len() % 36 == 0`,
   `root_key/mac_key.len() == 32`, `epoch > 0`, point-count consistency.
3. **Use checked arithmetic.** `at.checked_add(max_ooo)`, `epoch.checked_sub(1)`.
4. **Enforce `assume!` at runtime** via `assert!` or `debug_assert!`.
