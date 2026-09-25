# Review of the SPQR Chunk Replacement / Poisoning Report

**There is a real documentation/behaviour discrepancy here, but I would not accept the report’s main conclusion as written.** The current upstream libsignal integration prevents the claimed unauthenticated poisoning from being committed: it verifies an outer message MAC before accepting the candidate SPQR state. Also, **first-write-wins is not a sufficient general fix** for poisoning.

I checked the BAIF verification repository at `f49c43d2d5f6` and upstream libsignal at `e8cc2dddd578`. This was a source review; I did not execute the two linked reproduction files.

## 1. The decisive omission: outer authentication and state commitment

The report’s critical inference is:

> The chunk decoder returns `Ok(StillReceiving(...))`, so the caller persists the poisoned state.

**That does not follow from the chunk-layer code—and it is not what the inspected libsignal integration does.**

SPQR’s public `recv` takes an immutable reference to the serialized state and returns a candidate replacement state. It does not itself overwrite the caller’s saved state. An inner `Ok` therefore means that a candidate state is available, not that the enclosing messaging operation has accepted it.

In upstream `rust/protocol/src/triple_ratchet.rs`, the receive sequence is:

1. Call `spqr::recv`, obtaining `new_pqr_state` and a possible PQ key.
2. Derive the message keys.
3. Verify the enclosing Signal message’s MAC.
4. Decrypt the ciphertext.
5. Only after those operations succeed, assign `self.pqr_state = new_pqr_state`.

Furthermore, this outer MAC **covers the SPQR payload**. In `SignalMessage::new`, the `pq_ratchet` field is included in the serialized message before the MAC is computed; verification checks that serialized content. Changing a chunk’s data, index, or other serialized SPQR fields therefore changes authenticated bytes.

Consequently, under the report’s keyless on-path attacker model, the proposed sequence instead becomes:

```text
Forged chunk is processed tentatively.
SPQR may return a poisoned candidate state.
The enclosing message fails authentication.
The candidate SPQR state is not committed.
```

This breaks the proposed attack at **Step 3**, before persistent poisoning is established. It is not necessary for authentication to execute before every tentative decoder operation; what matters here is that authentication succeeds **before the resulting state is committed**.

The report could still investigate a different integration that commits SPQR output without authenticating the enclosing message. But it must identify such a caller. `Message::deserialize` lacking authentication is not sufficient evidence.

**Scope:** this conclusion concerns the inspected source revisions and attack path. It is not a claim that every historical release or every downstream SPQR integration has been audited.

## 2. What the report does establish locally

The underlying decoder observation is sound.

For loop index \(i<16\), the routing simplifies to

\[
\texttt{poly}=i,\qquad
\texttt{poly\_idx}=\texttt{chunk.index}.
\]

The guard therefore admits a point whenever its index is below that polynomial’s threshold, even if the set already contains that x-coordinate. The source comment says an existing point will be retained, while the call goes through the replacement-capable `SortedSet::push`.

The repository’s concrete external model explicitly implements replacement on equality. It also records the dependency’s equal-to-last fast path, which removes the old element and pushes the incoming one. Thus the comment does not describe the modelled operation.

I would distinguish the findings as follows:

| Report item | Assessment |
|---|---|
| **1. Incorrect source comment** | A genuine documentation defect. |
| **2. Duplicate-index last-write-wins** | Supporting behavioural evidence for item 1, rather than a separate security vulnerability. The described probe is consistent with the inspected source/model, but I have not run it. |
| **3. Persistent unauthenticated epoch poisoning** | A conditional concern for a caller that commits unauthenticated decoder state; the proposed attack is blocked by the inspected libsignal integration’s outer authentication and commit ordering. |

That distinction also matters at the specification level. The ML-KEM Braid decoder interface describes reconstruction from codewords produced by **one encoder**. It does not promise that the erasure decoder itself will correct arbitrary maliciously altered codewords. A corrupted-input demonstration is therefore not, by itself, a violation of the decoder’s stated correctness contract.

## 3. Several details of the poisoning argument need correction

### Low-index poison need not involve interpolation

The report repeatedly attributes corruption to Lagrange interpolation. However, `decoded_message()` first looks for each required output x-coordinate among stored points. When found, it copies that point’s y-value directly; it interpolates only when the required coordinate is missing.

A more accurate explanation is:

> A corrupted stored value at a required systematic coordinate is used directly in reconstruction; receiving correct values at other coordinates does not overwrite it.

This makes the local mechanism clearer without overstating protocol exploitability.

### “The slot is full, so later chunks are dropped” conflicts with rollback

The report combines two different execution models: a raw decoder whose mutations remain in place, and a transactional receive operation that discards its candidate state on error.

Consider an illustrative three-point threshold:

```text
Saved state:                  {0_bad, 1_good}
Add chunk 2 tentatively:      {0_bad, 1_good, 2_good}
Internal verification fails.
Saved state remains:          {0_bad, 1_good}
```

A subsequent high-index chunk can still pass the `len() < necessary_points(...)` guard, because the saved decoder is **not full**. It may again produce a corrupt candidate and fail verification, but the reason is not that all later chunks are dropped.

The conditional repeated-failure argument can survive this correction. Its explanation needs to distinguish those execution models.

### “Permanent” is stronger than the evidence

Ten additional honest chunks demonstrate persistence over that test sequence, not permanent failure.

The encoder casts its counter to `u16` when selecting a chunk, so its chunk-index sequence repeats. Also, under last-write-wins, a subsequently admitted correct chunk at the poisoned coordinate can replace the bad value.

That does **not** establish that a real session will automatically recover after 65,536 transmissions: other protocol state and acceptance conditions would need analysis. But it does mean that the index argument alone cannot establish “no new epoch secret can ever be derived.”

A defensible conditional claim would be:

> Once committed, the corrupted coordinate can cause repeated reconstruction failures until it is corrected or the affected protocol state is replaced.

## 4. The proposed fixes are not interchangeable or individually sufficient

### Option (a): first-write-wins

**This prevents overwriting an honest value; it does not prevent an attacker from supplying the first value.**

The counterexample is immediate:

```text
First accepted value at x = k: forged
Later value at x = k:          honest
First-write-wins result:       forged value remains
```

Indeed, for that arrival order, first-write-wins removes a recovery mechanism that last-write-wins provides. Neither policy identifies which value is authentic.

Thus option (a) addresses the particular **honest-first, forged-second** overwrite scenario, not the general poisoning problem described by the report. Whether to change duplicate handling should be a separate API/design decision, not presented as a complete security fix.

### Option (b): reset on internal MAC failure

This could form part of a recovery design, but “clear the decoder and return `Err`” is insufficient with the existing public API. The function works from an immutable serialized input and returns updated state only on success. A reset performed solely in a discarded candidate state will not change the caller’s saved state.

There is also a scope problem: the ciphertext authenticator checks `ct1 || ct2`. If corruption has already been incorporated into stored `ct1`, clearing only the `ct2` decoder does not repair that earlier state.

Any recovery change must also preserve the outer authentication boundary. An unauthenticated packet should not acquire the ability to reset committed state merely because a new error handler was introduced.

### Option (c): retain both candidates

This helps only when the retained alternatives include the correct value.

It does not establish general recovery when the honest value has never been received at that coordinate, when more alternatives are supplied than the policy retains, or when multiple coordinates are ambiguous. With two independent alternatives at each of \(r\) coordinates, a naive reconstruction search has \(2^r\) combinations.

A bounded candidate policy can be useful, but its memory limits, retry limits, eviction rules, and recovery guarantees need to be specified. “Keep both” is not automatically a complete fix.

## 5. The report overstates what `AddChunk.lean` proves

This is particularly important from the formal-verification perspective.

The concrete external model does contain an equality case that replaces the existing element. But **`IsSortedPushResult` itself has no `.eq` branch**. Its definition merely says that the new list results from either inserting or replacing the incoming point at some position. It does not tie that position to an equal x-coordinate or state which alternative must occur when a duplicate exists.

For example, as a mathematical observation about that definition, the relation permits:

```text
old = [(k, a)]
p   =  (k, b)
new = [(k, a), (k, b)]
```

The insertion alternative witnesses the relation, despite the repeated x-coordinate. That is **not** a claim that the actual `SortedSet` produces this result; it demonstrates that this particular postcondition is too weak to rule it out on its own.

Accordingly:

> The concrete model establishes the replacement operation. The abstract `IsSortedPushResult` postcondition alone does not pin down exact duplicate-key semantics.

A useful strengthening would characterize the operation by lookup: when the guard admits a point, the resulting value at its x-coordinate is the incoming y-value, while values at other coordinates are unchanged, under the relevant sortedness and uniqueness invariants.

There is another important modelling boundary here: **changing the application to first-write-wins must not change the external `SortedSet::push` model to pretend that the dependency ignores duplicates.** The dependency would still replace. The Rust application would instead need to avoid calling it for an existing key; the application translation and proofs would then change accordingly.

## 6. How I would revise and act on the report

I would replace the headline security claim with something like:

> **Duplicate-index replacement contradicts documentation; decoder poisoning requires unauthenticated state commitment.**
>
> `PolyDecoder::add_chunk` admits low-index duplicate points and replaces the stored value, contrary to its source comment. If a caller commits state derived from unauthenticated chunks, corrupted coordinates can persist and cause repeated reconstruction failures. However, the inspected upstream libsignal integration authenticates the enclosing message, including its SPQR payload, before committing the candidate SPQR state. The proposed keyless persistent-poisoning attack is therefore not established against that integration.

That wording preserves the valid finding without treating a missing trust-boundary argument as a demonstrated exploit.

The most valuable next test is an **integration-level state-persistence test**, not another raw decoder test: alter the SPQR bytes inside an otherwise genuine message without recomputing its MAC, submit it through the normal receive path, verify rejection and unchanged persisted state, then verify that a subsequent honest sequence completes normally. That directly tests the disputed step.

**Recommendation:** correct the source comment and add precise duplicate-handling coverage, but revise item 3 and its severity before presenting this as a confirmed protocol vulnerability. The key finding from this review is that **the inspected integration already has the authentication-and-commit boundary that the attack assumes is absent**.
