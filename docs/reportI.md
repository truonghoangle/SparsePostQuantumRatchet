# Report I: Bugs Derivable from Lean Specs × Rust State Machine Persistence Logic

Cross-referential analysis of the Lean formal specifications (`Spqr/Specs/`), the
auto-translated Lean models (`SrcTranslated/`), and the Rust source (`src/`). Every finding
is grounded in specific spec preconditions/postconditions that the Rust code fails to
establish or maintain, with particular focus on how poisoned / invalid state survives
serialisation.

---

## CRITICAL / HIGH

### 1. Poisoned Decoder State Survives Persistence — Permanent Epoch Stall (HIGH, Protocol DoS)

**Spec chain:**

| Spec file | What it pins down |
|---|---|
| `AddChunk.lean` | Guard `poly_idx < necessary_points(i)` unconditionally true for low-index chunks |
| `FunsExternal.lean:2146` | `SortedSet::push` on `.eq` does **replacement** (last-write-wins) |
| `Pt/Eq.lean` | `Pt` equality compares only `x`, ignoring `y` |
| `IntoPb.lean` / `FromPb.lean` | Poisoned points round-trip through protobuf unchanged |
| `Message/Deserialize.lean` | No authentication on chunk messages |

**Mechanism.** Attacker sends `{epoch, msg_type, index: k, data: garbage}` with
`k < necessary_points`. Replacement overwrites the honest point. `decoded_message()`
is `None` → `recv` returns `Ok` → **poisoned decoder persisted**. When honest chunks
complete, Lagrange interpolation corrupted → MAC fails → `recv` returns `Err` → caller
keeps pre-call poisoned state. Permanent: index `k` re-emitted only after 65 536 wraps.

**Affected paths** (all persist poisoned decoder before MAC check):
`send_ek.rs:194–222`, `send_ct.rs:82–107`, `send_ek.rs:129–148`,
`send_ct.rs:131–197`, `send_ct.rs:255–276`.

**Net effect.** One unauthenticated ~40-byte message permanently blocks the epoch.

---

### 2. Deserialized Chain State Never Validated — Panics from Corrupted Blobs (HIGH)

**Specs:** `ChainEpochDirection/FromPb.lean` (no validation), `NextKeyInternal.lean`
(requires `next.length = 32`), `KeyHistory/Get.lean` (requires `data.length % 36 = 0`),
`KeyHistory/Gc.lean` (requires `max_ooo ≤ current_key`).

**Rust.** `chain.rs` L306–312: `from_pb` does zero validation.

| Field | Consumer | Failure |
|---|---|---|
| `next.len() ≠ 32` | `next_key_internal` L241 | **panic** |
| `prev.len() % 36 ≠ 0` | `KeyHistory::get` L191 | **panic** |
| `prev` large, `ctr` small | `KeyHistory::gc` L149 | **panic** |

---

## MEDIUM

### 3. `u32` Overflow in `KeyHistory::get` Trimmed-Check

**Specs.** `Get.lean`, `Key32.lean`: `h_ooo_no_overflow : at1 + maxOoo ≤ U32.max`.
`chain.rs` L192: `at + max_ooo` overflows near `u32::MAX`. Debug: panic. Release:
valid key reported as `KeyTrimmed`.

### 4. `u64 → usize` Truncation in `Chain::epoch_idx` (32-bit)

**Spec.** `EpochIdx.lean`: `h_diff_fits : current_epoch - epoch ≤ Usize.max`.
`chain.rs` L376: `(self.current_epoch - epoch) as usize` truncates ≥ 2³² → wrong
epoch's key returned.

### 5. `compare` Truncates on Length Mismatch — Latent Auth Bypass

**Spec.** `Compare.lean`: correct only under `lhs.len() == rhs.len()` (erased at
runtime). `util.rs` L25–33: `rhs` longer → trailing bytes ignored → returns equal.
`rhs` shorter → panic. Current callers safe; latent.

### 6. `KeyHistory` Off-by-One — `gc`/`get` Disagree at Boundary

**Specs.** `Get.lean`: `KeyTrimmed` at `ats + maxOoo < self.ctr`. `Gc.lean`: drops
strictly below horizon. Key surviving `gc` still reported as `KeyTrimmed`.

### 7. Authenticator `from_pb` No Validation

**Spec.** `authenticator.serialize.Authenticator.from_pb_spec`: pure field copy.
`authenticator/serialize.rs` L16–21 accepts any bytes for `root_key`/`mac_key`.
Attacker controlling state blob can inject arbitrary key material.

---

## LOW

### 8. `PolyEncoder` Index Truncation `u32 → u16`

**Spec.** `NextChunk.lean`: `h_idx_fits : self.idx ≤ U16.max`. `FromPb.lean` accepts
any `u32`. `polynomial.rs` L735: `self.idx as u16` wraps after 65 535 chunks. Feeds
into Bug #1 by controlling when honest re-send of index `k` occurs.

### 9. `decode_chunk` Mutates Cursor Before Bounds Check

**Spec.** `DecodeChunk.lean`: on error paths cursor already advanced. Inconsistent with
`decode_varint`. No exploit (cursor discarded on error).

### 10. `decode_varint` Non-canonical Encodings / Truncation

**Spec.** `DecodeVarint.lean`: explicitly models non-canonical acceptance. 10-byte
encoding with non-zero high byte silently truncates to 64 bits.

### 11. `epoch == 0` Accepted in All `from_pb` Variants

State transitions require `epoch > 0`. `lib.rs:427` computes
`msg_key_epoch = scka_msg.epoch - 1` — underflows to `u64::MAX` with `epoch = 0`.

### 12. `hax_lib::assume!` Guards Erased at Runtime

| Location | Guard |
|---|---|
| `send_ek.rs:161` | `epoch < u64::MAX` |
| `chain.rs:86` | `max_ooo < 390451572` |
| `states/serialize.rs:236,243` | `into.len() > 0` |

No runtime enforcement. Long-lived session or crafted state can violate.

### 13. `VecDeque` `into_iter` Model Never Terminates — Latent Unsoundness

`FunsExternal.lean`: `IntoIter::next` never decrements `length`, wraps `head` modulo
`length`. `Chain::into_pb` uses this via `.map(...).collect()`. Behind `sorryAx` today;
will bite when chain-serialisation specs are written.

### 14. `Ct1Sent::from_pb` Accepts Mis-encoded `es` (Encapsulation State)

`send_ct/serialize.rs` L59: validates only `es.len() == 2080`. `encaps2` applies
heuristic endianness fix for libcrux#1275 but misclassifies when all `error2` values
are 0 or −1 (identical in both endiannesses).

---

## Architectural Root Cause

> **The state machine persists intermediate decoder/chain state on `Ok` paths, but
> MAC authentication only runs after full message assembly.** The gap between
> "state persisted" and "state authenticated" is the window in which poisoned data
> becomes permanent.

The Lean specs expose this mechanically: they model the replacement semantics
(`IsSortedPushResult` `.eq` in `AddChunk.lean`), the unconditional low-index guard,
the faithful `IntoPb`/`FromPb` round-trip, and the absence of validation in
`Chain`/`Authenticator`/`epoch` `from_pb` — making persistence of poison a *provable
consequence* of the specified behaviour.

---

## Summary Table

| # | Sev | Bug | Spec Evidence | Persists? |
|---|---|---|---|---|
| 1 | **HIGH** | Chunk poison → permanent stall | `AddChunk`, `Pt/Eq`, `IntoPb/FromPb` | ✅ |
| 2 | **HIGH** | Chain `from_pb` → panics | `FromPb`, `Get`, `Gc` | ✅ |
| 3 | MED | `u32` overflow in `get` | `Get`, `Key32` | ✅ |
| 4 | MED | `u64→usize` truncation 32-bit | `EpochIdx` | ✅ |
| 5 | MED | `compare` length mismatch | `Compare` | latent |
| 6 | MED | `gc`/`get` off-by-one | `Get`, `Gc` | ✅ |
| 7 | MED | Auth `from_pb` no validation | `from_pb_spec` | ✅ |
| 8 | LOW | Encoder `u32→u16` truncation | `NextChunk`, `FromPb` | ✅ |
| 9 | LOW | `decode_chunk` cursor | `DecodeChunk` | no |
| 10 | LOW | `decode_varint` non-canonical | `DecodeVarint` | no |
| 11 | LOW | `epoch == 0` in `from_pb` | transition invariants | ✅ |
| 12 | LOW | `assume!` erased at runtime | multiple preconditions | ✅ |
| 13 | LOW | `VecDeque` iter model unsound | `FunsExternal` | latent |
| 14 | LOW | `es` endianness heuristic | `FlipEndianness` | ✅ |
