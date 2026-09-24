# Report: Chunk Replacement Semantics and Unauthenticated Chunk Poisoning

This report consolidates and provides detailed analysis of three related defects concerning the `PolyDecoder::add_chunk` path in
SPQR's polynomial erasure-coding layer. Together they describe a chain from a documentation
inconsistency, through a behavioural confirmation, to a concrete
protocol-level denial-of-service attack.

---

## Background: How Chunks Are Stored

SPQR splits large protocol messages (headers, encapsulation keys, ciphertexts) into 32-byte
chunks, each carrying 16 two-byte GF(2¹⁶) evaluation points distributed round-robin across 16
polynomial slots. On the receiving side, `PolyDecoder::add_chunk`
(`src/encoding/polynomial.rs`, lines 879–904) iterates the 16 pairs in each chunk and inserts
them into per-polynomial sorted sets (`SortedSet<Pt>` from `sorted-vec 0.8.6`):

```rust
fn add_chunk(&mut self, chunk: &Chunk) {
    for i in 0usize..16 {
        let total_idx = (chunk.index as usize) * 16 + i;
        let poly = total_idx % 16;
        let poly_idx = total_idx / 16;
        let x = GF16::new(poly_idx as u16);
        let y = GF16::new(((chunk.data[i*2] as u16) << 8) + chunk.data[i*2+1] as u16);
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
   equal element, `sorted-vec 0.8.6` does `pop()` then `push(element)` — the **new** element
   replaces the old. The Lean model at `SrcTranslated/FunsExternal.lean:2146` confirms:
   `.eq => ok (i, some a, x :: rest)`.

---

## Item 1 — Source Comment Contradicts Actual Push Semantics

**Severity**: LOW (documentation / potentially behavioural)

The Rust comment at lines 898–900 states: *"This will discard new points whose X value matches a
previous old point."* This describes "first write wins" semantics.

**The actual semantics are the opposite.** `sorted-vec 0.8.6`'s `SortedSet::push` on `Equal`
replaces the existing element — "last write wins". The Lean specification in
`AddChunk.lean` correctly models this via `IsSortedPushResult`, whose second disjunct is
`new_ = old.take j ++ [p] ++ old.drop (j + 1)` (replacement at position `j`).

For the honest protocol this is harmless: the same chunk index always carries identical data, so
replacement is a no-op. However, the incorrect comment creates a false sense of security — a
reader would believe that once a point is stored, it cannot be overwritten. Items 2 and 3 show
this assumption matters.

---

## Item 2 — Behavioural Confirmation: Duplicate Index → Last Write Wins

**Severity**: LOW

The test `decoder_duplicate_index_last_wins` (in
[`docs/decoder_logic_probe.rs.txt`](./decoder_logic_probe.rs.txt)) feeds two chunks with
`index = 0` from two different 10-byte messages into the same `PolyDecoder`. The decoder output
matches the **second** message (`"ABCDEFGHIJ"`), confirming last-write-wins and directly
contradicting the source comment.

**Lean specifications that pin this down:**

| Spec file | What it establishes |
|---|---|
| `AddChunk.lean` | `IsSortedPushResult` `.eq` branch is replacement |
| `Pt/Eq.lean` | `Pt` equality compares only `x.value`, ignoring `y` |
| `IntoPb.lean` / `FromPb.lean` | Replaced points survive serialisation unchanged |

The practical consequence: a replayed chunk with a bit-flip **does** corrupt polynomial
reconstruction until the MAC check rejects the result, rather than being harmlessly ignored.

   unconditionally true for any chunk whose index is below the decode threshold, so low-index
   chunks are *always* accepted regardless of whether a point with that x already exists.

2. **`SortedSet::push` replacement semantics.** `Pt` implements `Eq`/`Ord` on `x.value` alone,
   ignoring `y` (`Spqr/Specs/Encoding/Polynomial/Pt/Eq.lean`). When `SortedSet::push` finds an
   equal element, `sorted-vec 0.8.6` does `pop()` then `push(element)` — the **new** element
   replaces the old. The Lean model at `SrcTranslated/FunsExternal.lean:2146` confirms:
   `.eq => ok (i, some a, x :: rest)`.

---

## Item 3 — Unauthenticated Chunk Poisoning Permanently Stalls an Epoch

**Severity**: MEDIUM (protocol-level denial of service)

This is the most impactful finding and builds directly on items 1 and 2.

### Attack Overview

An on-path attacker can permanently block a PQ ratchet epoch for the receiver by sending a
single forged chunk message (~40 bytes). No knowledge of keys or secrets is required — only
the ability to inject a message into the transport.

### Detailed Attack Steps

**Step 1 — Injection.** The attacker sends a chunk message
`{epoch: E, type: Hdr/Ek/Ct1/Ct2, index: k, data: <garbage>}` where `E` is the current
epoch and `k` is any index below `necessary_points` (e.g. `k = 0`). `Message::deserialize`
(`Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean`) performs **no
authentication** — `Chunk.index` and `Chunk.data` are entirely attacker-controlled.

**Step 2 — Replacement.** `add_chunk` processes the forged chunk. Because
`k < necessary_points` (first disjunct of the guard at line 895), the point is unconditionally
inserted. `SortedSet::push` replaces any existing honest point with the same x-coordinate
(last-write-wins per items 4/18), or pre-seeds the slot if the honest chunk hasn't arrived yet.

**Step 3 — Persistence without detection.** `decoded_message()` returns `None` (not all
points collected yet). The state machine returns `Ok(StillReceiving(...))` with the poisoned
decoder embedded. The caller persists this state. **The poisoned point is now permanently part
of the decoder state.** The relevant code path in `recv_ct2_chunk`
(`src/v1/chunked/send_ek.rs` lines 194–222):

```rust
receiving_ct2.add_chunk(chunk);
if let Some(mut ct2) = receiving_ct2.decoded_message() {
    let mac: authenticator::Mac = ct2.split_off(CIPHERTEXT2_SIZE);
    let (uc, sec) = uc.recv_ct2(ct2, mac)?;   // MAC check here
    // ... success path ...
} else {
    Ok(EkSentCt1ReceivedRecvChunk::StillReceiving(
        EkSentCt1Received { uc, receiving_ct2 },  // poisoned decoder persisted
    ))
}
```

The MAC check only runs when `decoded_message()` returns `Some`. Until then, the poisoned
state accumulates honest chunks without any authentication gate. The same pattern applies to
`recv_hdr_chunk` in `src/v1/chunked/send_ct.rs` (lines 82–107).

**Step 4 — Permanent failure.** When the remaining honest chunks complete the message,
Lagrange interpolation uses the garbage point at `x = k`. The result is corrupted, so
`verify_hdr`/`verify_ct` fails and `recv` returns `Err`. The `?` operator propagates the
error, and the caller retains the *pre-call* (poisoned) state.

Every subsequent honest chunk yields the same `Err` because:

- The only way to overwrite the `x = k` point is another chunk with index exactly `k`.
- `PolyEncoder::next_chunk` (`polynomial.rs` L734–737) casts `idx` (a `u32`) to `u16`,
  so index `k` is not re-emitted until the encoder wraps through all 65,536 indices.
- Honest chunks with indices ≥ `necessary_points` are dropped (the slot is full).

### Net Effect

**One forged, unauthenticated ~40-byte message permanently blocks the PQ ratchet epoch for
the receiver.** No new epoch secret can ever be derived for that direction, and the peer
receives no indication of *why* — only repeated MAC verification errors.

If the code matched the comment's stated intent ("discard new points"), the attack would be a
no-op once the honest chunk for index `k` arrives first.

### Specifications That Expose the Vulnerability

| Specification file | What it establishes |
|---|---|
| `PolyDecoder/AddChunk.lean` | Guard is unconditionally true for low indices; `.eq` = replacement |
| `FunsExternal.lean:2146` | `SortedSet::push` `.eq` branch replaces |
| `Pt/Eq.lean` | `Pt` equality ignores `y` |
| `IntoPb.lean` / `FromPb.lean` | Poisoned points survive serialisation |
| `Message/Deserialize.lean` | No authentication on chunk messages |

### Reproduction

See [`docs/decoder_poison_persistence_counterexample.rs.txt`](./decoder_poison_persistence_counterexample.rs.txt).
The test sends an honest `index 0` chunk first, then a poisoned one (which replaces it),
persists through `into_pb`/`from_pb`, completes the decode, and confirms the output never
matches the original — even after ten more honest chunks.

---

## Recommended Fixes

Any **one** of the following suffices for item 3. Option (a) also resolves items 1 and 2.

### Option (a): First Write Wins (smallest change)

Replace `self.pts[poly].push(Pt { x, y })` with a find-or-push that only inserts when no
point with the same x exists. Matches the source comment's stated intent. **Requires updating
the Lean model** in `AddChunk.lean` (the `.eq` replacement branch becomes a no-op).

### Option (b): Reset Decoder on MAC Failure

On `Err(InvalidHdrMac/InvalidCtMac)`, clear the decoder's point sets so honest retransmissions
can recover. Requires changes in `send_ek.rs`/`send_ct.rs`. An attacker can force repeated
resets, but each is recoverable (unlike the current permanent stall).

### Option (c): Keep Both Candidate Values

Store both original and replacement y-values per x. On MAC failure, retry with the alternative.
Maximum resilience but significant implementation and specification complexity.

### Additional Recommendations

- **Correct the source comment** (lines 896–900) regardless of fix chosen.
- **Update Lean specifications** to match whichever semantics the fix implements.
