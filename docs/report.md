# Research Report: Independent Source-Level Bug Analysis of SPQR Decoder and Chain Persistence Logic

This report documents an independent, source-level research study of the SPQR (Sparse
Post-Quantum Ratchet) codebase. The investigation was motivated by the question: *can
unauthenticated or malformed inputs permanently corrupt persisted protocol state?*

The study examined the Rust source (`src/`), the `sorted-vec 0.8.6` upstream dependency
(`~/.cargo/registry/src/.../sorted-vec-0.8.6/src/lib.rs`), the Lean formal specifications
(`Spqr/Specs/`), and the auto-translated Lean models (`SrcTranslated/`). Every finding
below is grounded in specific source lines, spec preconditions, and (where applicable)
executable counterexamples in `docs/`.

---

## Methodology

1. **Dependency audit.** Read the `sorted-vec 0.8.6` source to determine the exact semantics
   of `SortedSet::push` and `SortedSet::replace` on duplicate keys.
2. **Data-flow tracing.** Traced every path from chunk ingestion (`add_chunk`) through
   decoder state persistence (`into_pb`/`from_pb`) to message assembly (`decoded_message`)
   and MAC verification.
3. **Spec cross-reference.** Compared Lean spec preconditions/postconditions against the Rust
   code to identify gaps: invariants the specs must *assume* that the code never *establishes*.
4. **State machine analysis.** Examined the chunked protocol state machines
   (`send_ek.rs`, `send_ct.rs`) to determine whether poisoned state is committed before or
   after authentication.

---

## Background: How Chunks Are Stored

SPQR splits large protocol messages (headers, encapsulation keys, ciphertexts) into 32-byte
chunks, each carrying 16 two-byte GF(2^16) evaluation points distributed round-robin across 16
polynomial slots. On the receiving side, `PolyDecoder::add_chunk`
(`src/encoding/polynomial.rs`, lines 879-904) iterates the 16 pairs in each chunk and inserts
them into per-polynomial sorted sets (`SortedSet<Pt>` from `sorted-vec 0.8.6`):

```rust
fn add_chunk(&mut self, chunk: &Chunk) {
    for i in 0usize..16 {
        let total_idx = (chunk.index as usize) * 16 + i;
        let poly = total_idx % 16;
        let poly_idx = total_idx / 16;
        let x = GF16::new(poly_idx as u16);
        let y1 = chunk.data[i * 2] as u16;
        let y2 = chunk.data[i * 2 + 1] as u16;
        let y = GF16::new((y1 << 8) + y2);
        if poly_idx < self.necessary_points(i)
            || self.pts[poly].len() < self.necessary_points(i)
        {
            // This will discard new points whose X value matches a previous
            // old point, since we've implemented equality for the Pt object
            // to only care about the X value.
            self.pts[poly].push(Pt { x, y });
        }
    }
}
```

Two aspects are critical:

1. **The guard condition.** The first disjunct `poly_idx < necessary_points(i)` is
   unconditionally true for any chunk whose index is below the decode threshold, so low-index
   chunks are *always* accepted regardless of whether a point with that x already exists.

2. **`SortedSet::push` replacement semantics.** `Pt` implements `Eq`/`Ord` on `x.value` alone,
   ignoring `y` (`Spqr/Specs/Encoding/Polynomial/Pt/Eq.lean`). When `SortedSet::push` finds an
   equal element, `sorted-vec 0.8.6` does `pop()` then `push(element)` -- the **new** element
   replaces the old. The Lean model at `SrcTranslated/FunsExternal.lean:2146` confirms:
   `.eq => ok (i, some a, x :: rest)`.

   **Upstream source verification.** The `SortedSet::push` method in `sorted-vec 0.8.6`
   (`src/lib.rs`, lines 392-417) and `SortedSet::replace` (`src/lib.rs`, lines 365-381) both
   implement last-write-wins replacement. For `push`, the `Equal` fast-path does:

   ```rust
   // sorted-vec 0.8.6, SortedSet::push (lib.rs:400-405)
   } else if cmp == std::cmp::Ordering::Equal {
       let original = self.set.vec.pop();   // remove existing element
       self.set.vec.push(element);           // insert new element
       return (self.vec.len() - 1, original);
   }
   ```

   For non-tail positions, `push` delegates to `replace` (lib.rs:365-381), which uses
   `std::mem::swap` to replace the existing element in-place:

   ```rust
   // sorted-vec 0.8.6, SortedSet::replace (lib.rs:367-374)
   Ok(existing_index) => {
       std::mem::swap(&mut element, self.set.vec.get_unchecked_mut(existing_index));
       (existing_index, Some(element))
   }
   ```

   Both paths unambiguously implement **last-write-wins** semantics.

---

## Finding 1 -- Source Comment Contradicts Actual `SortedSet::push` Semantics

**Severity**: LOW (documentation defect with security implications)

**Source location.** `src/encoding/polynomial.rs`, lines 898-900.

**The comment states:**
> "This will discard new points whose X value matches a previous old point, since we have
> implemented equality for the Pt object to only care about the X value."

**The actual semantics are the opposite.** As verified above, `sorted-vec 0.8.6`'s
`SortedSet::push` on `Equal` **replaces** the existing element -- "last write wins", not
"first write wins". The Lean specification in `AddChunk.lean` correctly models replacement
via `IsSortedPushResult`, whose second disjunct is
`new_ = old.take j ++ [p] ++ old.drop (j + 1)` (replacement at position `j`).

For the honest protocol this is harmless: the same chunk index always carries identical data,
so replacement is a no-op. However, the incorrect comment creates a false sense of security --
a reader would believe that once a point is stored, it cannot be overwritten. Findings 2 and
3 show this matters.

**Counterexample.** See [`docs/decoder_logic_probe.rs.txt`](./decoder_logic_probe.rs.txt):
feeding two chunks with `index = 0` from two different messages into the same decoder
produces output matching the **second** message, directly contradicting the comment.

---

## Finding 2 -- Unauthenticated Chunk Poisoning Permanently Corrupts Decoder State

**Severity**: MEDIUM at decoder layer; LOW in the inspected upstream integration (see mitigation)

### Research Approach

We traced the full data-flow from chunk injection to state persistence:

1. `Message::deserialize` (modelled in `Message/Deserialize.lean`) -- **no authentication**
   on `Chunk.index` or `Chunk.data`.
2. `add_chunk` -- guard `poly_idx < necessary_points(i)` is unconditionally true for low-index
   chunks, so the point is always passed to `SortedSet::push`.
3. `SortedSet::push` -- replaces the existing honest point (Finding 1).
4. `decoded_message()` -- returns `None` if not all polynomials are complete.
5. State machine returns `Ok` -> caller persists the poisoned decoder via `into_pb`.
6. `from_pb` -- faithfully round-trips the poisoned points (verified: `IntoPb.lean`/`FromPb.lean`).
7. When honest chunks complete the message, Lagrange interpolation produces garbage ->
   MAC check fails -> `recv` returns `Err` -> caller keeps **pre-call** (still poisoned) state.

### Attack Chain

**Step 1 -- Injection.** Attacker sends
`{epoch: E, type: Hdr/Ek/Ct1/Ct2, index: 0, data: <garbage>}`.

**Step 2 -- Replacement.** `add_chunk` unconditionally accepts the point (guard true for
index 0). `SortedSet::push` replaces any existing honest point at `x = 0`.

**Step 3 -- Persistence.** `decoded_message()` returns `None` (incomplete). The state machine
returns `Ok` and the caller persists the decoder. The poisoned point is now in the stored state.

**Step 4 -- Permanent corruption.** Subsequent honest chunks complete the message, but
Lagrange interpolation over the corrupted point set yields wrong output -> MAC verification
fails -> `Err` is returned -> caller retains pre-call state (still poisoned). The only chunk
that could repair it has the same `index` as the poisoned one, but the honest sender emits
each index only once (it wraps after 2^16 chunks via `self.idx.wrapping_add(1)` at
`polynomial.rs:736`). The epoch is permanently stalled.

**Affected state machine paths** (all persist decoder before MAC check):
- `send_ek.rs:129-148` (`HeaderSent::recv_ct1_chunk`)
- `send_ek.rs:194-222` (`EkSentCt1Received::recv_ct2_chunk`)
- `send_ct.rs:82-107` (`NoHeaderReceived::recv_hdr_chunk`)
- `send_ct.rs:131-197` (`Ct1Sampled::recv_ek_chunk`)
- `send_ct.rs:255-276` (`Ct1Acknowledged::recv_ek_chunk`)

### Counterexample

See [`docs/decoder_poison_persistence_counterexample.rs.txt`](./decoder_poison_persistence_counterexample.rs.txt).
The test sends an honest `index 0` chunk, then a poisoned one (which replaces it), persists
through `into_pb`/`from_pb`, completes the decode, and confirms the output never matches the
original -- even after ten more honest chunks.

### Integration-Level Mitigation

> An independent review (`docs/spqr_chunk_replacement_poisoning_review.md`) found that the
> upstream libsignal integration at `rust/protocol/src/triple_ratchet.rs` authenticates the
> enclosing Signal message (which covers the SPQR payload) **before** committing the candidate
> SPQR state. A forged chunk alters authenticated bytes -> MAC check fails -> candidate state
> is never committed -> persisted state remains intact. The persistent poisoning attack is
> therefore **not established** against the inspected upstream integration. It would require
> an integration that commits SPQR output without this authentication step.



---

## Finding 3 -- Deserialized Chain State Never Validated -> Panics from Corrupted Blobs

**Severity**: HIGH

### Research Approach

We cross-referenced every `from_pb` precondition in the Lean specs against the Rust
`ChainEpochDirection::from_pb` at `chain.rs:306-312`:

```rust
fn from_pb(pb: pqrpb::chain::epoch::EpochDirection) -> Result<Self, Error> {
    Ok(Self {
        ctr: pb.ctr,
        next: pb.next,
        prev: KeyHistory { data: pb.prev },
    })
}
```

**Zero validation** is performed. Yet the following downstream consumers require invariants
that `from_pb` never establishes:

| Field | Spec requiring invariant | Consumer | Failure mode |
|---|---|---|---|
| `next.len() != 32` (non-empty) | `NextKeyInternal.lean`: `h_next_len : next.length = 32` | `next_key_internal` L243: `next.copy_from_slice(&genr8r[..32])` | **panic** (length mismatch) |
| `prev.len() % 36 != 0` | `KeyHistory/Get.lean`: `h_data_aligned : self.data.length % 36 = 0` | `KeyHistory::get` L191: `assert_eq!(self.data.len() % KEY_SIZE, 0)` | **panic** |
| `prev` large, `ctr` small | `KeyHistory/Gc.lean`: `h_key_ge : max_ooo <= current_key` | `KeyHistory::gc` L149: `assert!(current_key >= max_ooo)` | **panic** |

A protobuf-valid but semantically inconsistent state blob (e.g. from storage corruption or a
malicious peer in a backup-restore scenario) turns `recv`/`send` into an unrecoverable panic
instead of `Err(StateDecode)`.

---

## Finding 4 -- `u32` Overflow in `KeyHistory::get` Trimmed-Check

**Severity**: MEDIUM

**Source.** `chain.rs:192`:
```rust
if at + (params.max_ooo_keys_or_default()) < current_ctr {
```

**Spec evidence.** `Get.lean` and `Key32.lean` require `h_ooo_no_overflow : at1 + maxOoo <= U32.max`.

`at` is the attacker-supplied message `index` (a `u32`). When `ctr` approaches `u32::MAX`,
`at + max_ooo` overflows: debug builds **panic**, release builds wrap to a small value so the
branch is taken and a *valid, recoverable* key is reported as `KeyTrimmed` -- a silent
protocol failure.

---

## Finding 5 -- `is_complete` Flag Never Set -> Redundant Decoding and Stall-by-Blob

**Severity**: LOW

**Source.** `polynomial.rs:912`: `if self.is_complete { return None; }`. But no code path
ever sets `is_complete = true`. The field is initialized `false` (L789) and faithfully
round-tripped through `into_pb`/`from_pb`.

**Consequences:**
1. After a successful decode, every subsequent late chunk for that epoch triggers a full
   redundant Lagrange interpolation.
2. A state blob with `is_complete = true` (injected via storage corruption) makes
   `decoded_message()` return `None` forever, silently stalling the epoch with no error.

---

## Finding 6 -- `PolyEncoder` Index Truncation `u32 -> u16`

**Severity**: LOW

**Source.** `polynomial.rs:735`:
```rust
fn next_chunk(&mut self) -> Chunk {
    let out = self.chunk_at(self.idx as u16);
    self.idx = self.idx.wrapping_add(1);
    out
}
```

`self.idx` is `u32` but `chunk_at` takes `u16`. After 65535 chunks, the index wraps to 0,
re-emitting points that were already consumed. This feeds into Finding 2: the only way to
"repair" a poisoned `x = 0` point is to re-send `index = 0`, which happens only after
this 2^16 wrap -- far too late for practical recovery.

**Spec evidence.** `NextChunk.lean`: `h_idx_fits : self.idx <= U16.max`. `FromPb.lean`
accepts any `u32`.

---

## Finding 7 -- `hax_lib::assume!` Guards Erased at Runtime

**Severity**: LOW

Multiple critical preconditions are guarded only by `hax_lib::assume!`, which Aeneas uses
during extraction but which **compiles to nothing** at runtime:

| Location | Guard | Consequence if violated |
|---|---|---|
| `send_ek.rs:161` | `epoch < u64::MAX` | Epoch counter overflow |
| `chain.rs:86` | `max_ooo < 390451572` | `trim_size()` overflow |
| `chain.rs:263` | `self.ctr <= u32::MAX - 390451572` | `key()` arithmetic overflow |
| `states/serialize.rs:236,243` | `into.len() > 0` | Empty-slice panic |

A long-lived session or crafted state can violate any of these.

---

## Finding 8 -- `VecDeque` `into_iter` Lean Model Never Terminates

**Severity**: LOW (latent unsoundness in trusted base)

**Source.** `FunsExternal.lean`: the `IntoIter::next` model never decrements `length` and
wraps `head` modulo `length` -- producing an infinite, cycling iterator that revisits
already-popped elements.

**Impact.** `Chain::into_pb` (`Funs.lean` L5875 ff.) uses this via `.map(...).collect()`.
Currently behind `sorryAx` (via `MapCollectBridge.lean`), so no proved theorem is falsified
today. However, any future chain-serialisation spec unfolding this iterator would inherit
the unsoundness.

**Counterexample.** See [`docs/vecdeque_into_iter_model_counterexample.lean.txt`](./vecdeque_into_iter_model_counterexample.lean.txt).

---

## Architectural Root Cause

> **The state machine persists intermediate decoder/chain state on `Ok` paths, but MAC
> authentication only runs after full message assembly.** The gap between "state persisted"
> and "state authenticated" is the window in which poisoned data becomes permanent.

The Lean specs expose this mechanically: they model the replacement semantics
(`IsSortedPushResult` `.eq` in `AddChunk.lean`), the unconditional low-index guard, the
faithful `IntoPb`/`FromPb` round-trip, and the absence of validation in
`Chain`/`Authenticator` `from_pb` -- making persistence of poison a *provable consequence*
of the specified behaviour.

---

## Summary Table

| # | Sev | Finding | Key Source Evidence | Persists? |
|---|---|---|---|---|
| 1 | LOW | Comment contradicts actual push semantics | `polynomial.rs:898-900` vs `sorted-vec:392-417` | n/a |
| 2 | **MED** | Chunk poison -> permanent decoder stall | `add_chunk` guard + `SortedSet::push` + `into_pb`/`from_pb` | Yes |
| 3 | **HIGH** | Chain `from_pb` -> panics from corrupted blobs | `chain.rs:306-312` vs `NextKeyInternal`/`Get`/`Gc` specs | Yes |
| 4 | MED | `u32` overflow in `KeyHistory::get` | `chain.rs:192` vs `Get.lean` `h_ooo_no_overflow` | Yes |
| 5 | LOW | `is_complete` never set -> redundant decode / stall-by-blob | `polynomial.rs:789,912` | Yes |
| 6 | LOW | Encoder `u32->u16` truncation after 65535 chunks | `polynomial.rs:735` vs `NextChunk.lean` | Yes |
| 7 | LOW | `hax_lib::assume!` guards erased at runtime | multiple locations | Yes |
| 8 | LOW | `VecDeque` iter model unsound | `FunsExternal.lean` | latent |

---

## Recommended Fixes

### For Finding 2 (chunk poisoning):

Given the review finding that the upstream integration already authenticates before committing
SPQR state, these recommendations are **defense-in-depth** measures:

- **Option (a): First Write Wins.** Replace `self.pts[poly].push(Pt { x, y })` with
  `find_or_insert` that only inserts when no point with the same x exists. Use
  `SortedSet::find_or_insert` (available in `sorted-vec 0.8.6`, lib.rs:385) instead of `push`.
  **Note:** this is partial -- an attacker whose chunk arrives *before* the honest one still
  wins. Update Lean model in `AddChunk.lean` accordingly.

- **Option (b): Reset Decoder on MAC Failure (recommended).** On `Err(InvalidHdrMac/InvalidCtMac)`,
  clear the decoder's point sets so honest retransmissions can recover.

- **Correct the source comment** (lines 898-900) regardless of fix chosen.

### For Finding 3 (chain `from_pb`):

Validate in `ChainEpochDirection::from_pb`: check `next.len() == 32`,
`prev.len() % 36 == 0`, and `prev.len() / 36 <= ctr`. Return `Error::StateDecode` on failure.

### For Finding 4 (`u32` overflow):

Use `at.checked_add(params.max_ooo_keys_or_default())` or `saturating_add`.

### Cross-cutting:

- **Update Lean specifications** to match whichever semantics fixes implement.
- **Strengthen `IsSortedPushResult`** -- the current postcondition does not pin down exact
  duplicate-key semantics. A useful strengthening: when the guard admits a point, the resulting
  value at its x-coordinate is the incoming y-value, while values at other coordinates are
  unchanged (under sortedness and uniqueness invariants).
- **Add an integration-level state-persistence test** -- alter SPQR bytes inside an otherwise
  genuine message without recomputing its MAC, submit through the normal receive path, verify
  rejection and unchanged persisted state, then verify a subsequent honest sequence completes
  normally. This directly validates the authentication-before-commit boundary.
