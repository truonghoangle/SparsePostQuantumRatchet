# Talk Script — Formal Verification of SPQR in Lean 4

**Duration:** 15 minutes (≈ 1 min 40 s per slide × 9 slides)
**Companion deck:** [`report.pptx`](./report.pptx)

---

## Slide 1 — What is SPQR and what are we doing to it?

*≈ 1 min 40 s*

Good morning, everyone. I'm here to talk about our formal verification of SPQR — Signal's Sparse Post-Quantum Ratchet.

So what is SPQR? It's a Rust library that adds post-quantum forward secrecy to Signal's messaging ratchet, using ML-KEM 768. The word "sparse" refers to how it handles the large key material: instead of sending everything in one shot, the key is chopped into 32-byte chunks and spread across many messages. An erasure code over the finite field GF(2¹⁶) ensures that any sufficient subset of those chunks can reconstruct the whole key. This is clever engineering — but clever engineering is exactly where subtle bugs hide.

That's where we come in. Testing finds *some* bugs. A machine-checked proof rules out entire *classes* of bugs — for all inputs, not just the ones you happened to test. Our toolchain goes like this: we take the Rust source, run it through Charon to get a low-level intermediate representation, then through Aeneas to produce a pure functional Lean 4 model. That model lives in `SrcTranslated/`. We then write hand-written specifications and proofs in `Spqr/Specs/`, mirroring the Rust module tree. We also have a mathematical library in `Spqr/Math/` that formalizes GF(2¹⁶) as a real Mathlib field, with Lagrange interpolation and all the algebra that implies.

The trusted base is small: the Lean kernel itself, the Aeneas translation, and a handful of axioms for external FFI crates like libcrux, prost, and bytes.

---

## Slide 2 — Results so far (numbers)

*≈ 1 min 40 s*

Let me give you the headline numbers. The SPQR crate has 312 verifiable Rust functions — that's after excluding test code, trait impls, and opaque externals. Of those, 147 now have a Lean specification theorem — that's 47 percent. And of those 147, 146 are fully proved with no `sorry` anywhere in their own proof. The single exception is `decode_state`, which is blocked on protobuf-generated code that our translator currently replaces with `sorry` — I'll come back to that.

On the Lean side, we have 188 spec files containing 419 spec theorems, plus 110 mathematical lemmas in the `Spqr/Math/` library — about 555 hand-written theorems and lemmas in total. We have exactly one project-level axiom: the semantics of HKDF. The external-crate axioms — about 40 of them for libcrux, prost, and bytes — are clearly separated in the translated code.

The key point for non-experts: "verified" here means a theorem about the *exact* translated code, checked by the Lean kernel. This is not a re-implementation or a model. And the entire erasure-coding core — the mathematically hardest part — is at 100 percent coverage. What remains is mostly the protocol state machines and the top-level entry points.

---

## Slide 3 — Growth of verified Rust functions over time

*≈ 1 min 30 s*

This chart shows our progress week by week since mid-April. The blue bars are functions verified each week; the dark line is the cumulative total.

You can see that the first few weeks were slow — 8 functions by week 16, then a plateau through weeks 17 to 19 while we set up the Aeneas extraction pipeline. That investment paid off: once the infrastructure was in place, progress accelerated. Week 23 marks when `gf.rs` — the finite field arithmetic — was fully complete. Week 28 was the big Lagrange interpolation proof, which I'll show you in Slide 5. Weeks 31 and 32 were our highest-throughput period — 13 and 30 functions respectively — as the encoder, decoder, serialization, and the first `lib.rs` API helpers all came together. And just last week, week 36, we finished `KeyHistory::gc`, the garbage collector proof, which at 962 lines of Lean is our largest single proof.

The pattern is clear: we invest in infrastructure — the math library, the field formalization, the tactic framework — and then that investment compounds as we move to higher-level functions.

---

## Slide 4 — File-by-file report

*≈ 1 min 50 s*

Let me break the status down by file. You're looking at four cards, one per major area.

Top left: `encoding/gf.rs`, our finite field arithmetic. Thirteen out of thirteen functions — 100 percent done. Every Rust operation is proved equal to the corresponding Mathlib field operation, including the 256-entry lookup table and the fast multiplication tricks.

Top right: `encoding/polynomial.rs`. Thirty-two out of thirty-two top-level functions, also 100 percent. This is the erasure code — Lagrange interpolation, the encoder, the decoder, and the byte format. Our math library has 110 lemmas backing this up.

Bottom left: `chain.rs`, at 11 out of 25, or 44 percent. The chain manages symmetric message keys and keeps a history of skipped keys for out-of-order delivery. We've finished all of `ChainParams` and all of `KeyHistory`. What's next is `ChainEpochDirection` — the per-epoch key derivation — and the top-level `Chain` itself.

Bottom right: the serialization files — `serialize.rs`, the v1 serialization modules, and the authenticator serializer. Thirty-two out of thirty-nine done. All the varint and chunk codecs are verified, all eighteen unchunked protobuf round-trips are done. The remaining seven are chunked-state protobuf conversions that involve vector-of-struct loops.


---

## Slide 5 — A complex function: `Poly::lagrange_interpolate`

*≈ 2 min*

Now let me show you what a real verification looks like. This is `lagrange_interpolate` from `polynomial.rs`. It's the heart of the erasure code.

On the left, the math. Given n points with distinct x-coordinates in GF(2¹⁶), there's exactly one polynomial of degree less than n passing through all of them — the Lagrange interpolant. The formula is the classical one: L(x) equals the sum of yᵢ times the basis polynomial ℓᵢ(x).

But the Rust code doesn't compute it the textbook way. It uses a three-step shortcut. Step one: multiply out the template polynomial T(x) — the product of all the (x minus xⱼ) factors — once. Step two: for each point i, copy T, synthetically divide out the (x minus xᵢ) factor, and scale by yᵢ times the Fermat inverse of the denominator product. The working buffer now holds x times yᵢ times ℓᵢ(x). Step three: add coefficients 1 through n into the output — skipping coefficient zero is "divide by x" for free.

On the right is the Lean theorem. It says: the output of the Rust code, read as a Mathlib polynomial via `toGF216Poly`, equals `lagrangeInterpolantSum` — our mathematical definition of the Lagrange interpolant. This is a coefficient-exact identity, not just "agrees at the sample points." The proof mirrors the three steps of the code: one lemma for the inner loop, one for the outer loop with an invariant that the buffer really holds x times yᵢ times ℓᵢ(x), then a cancellation. The only assumption is that the point count fits in a machine integer.

---

## Slide 6 — Using `polynomial.rs` from `encoding.rs`: `Option<T>::add_chunk`

*≈ 1 min 40 s*

This slide shows how verified components compose. The function `add_chunk` for `Option<T>` in `encoding.rs` is a generic wrapper: it unwraps the `Option`, calls the inner decoder's `add_chunk`, and wraps the result back up. Three lines of Rust.

We prove the wrapper once, generically — for any type `T` that implements the `Decoder` trait. The theorem says: if you start with `Some(decoder)`, after calling `add_chunk` you still have `Some`, and the inner decoder has been updated exactly as if you had called `T::add_chunk` on it directly. That's the top row on the slide.

Then we *instantiate* that generic theorem with the concrete `PolyDecoder`. The bottom row shows the composed result: the theorem about `Option<PolyDecoder>::add_chunk` says that the polynomial decoder inside the `Option` has absorbed the new chunk correctly — its internal point list has grown by one, with the right x-coordinate and the right y-values. The proof is four lines: apply the generic lift lemma, then plug in the concrete `PolyDecoder.add_chunk_spec`.

This is the payoff of modular verification. We prove each layer once, and composition is almost free.


---

## Slide 7 (1/2) — Case study: `KeyHistory::gc` — what it does and why it is hard

*≈ 1 min 50 s*

Now for the hardest proof in the project: `KeyHistory::gc` in `chain.rs`. It's 20 lines of Rust and 962 lines of Lean. The previous verification tool — hax — had skipped this function as too hard.

What does it do? The key history is a flat byte array where every 36 bytes is one record: a 4-byte key index followed by a 32-byte key. When the array gets too long, the garbage collector scans it and deletes every record whose index is older than `current_key` minus `max_ooo_keys`.

Why is the theorem hard to state? Three reasons. First, everything is bytes. The theorem can't say "key number is at least the horizon" — it has to reason about 4-byte big-endian comparisons, and we have to prove that comparing bytes is the same as comparing numbers. Second, deletion reorders: a record is removed by swap-removing — the last record moves into the deleted slot. That moved record might itself be old, so a simple "everything before position i is fine" invariant is false. Third, what does "correct" even mean? We need three properties: every kept record is still live, every live record is kept, and nothing is duplicated. For the third property, we need an explicit one-to-one matching — a bijection — between positions in the old and new arrays.

---

## Slide 7 (2/2) — How the theorem evolved

*≈ 1 min 30 s*

This table shows how the `gc` theorem evolved over four commits in about a week.

The first draft on August 25th was *true* — it correctly described the function — but its preconditions were so strict it could never be used. It required `current_key` to be at least 2000, which only makes sense with the default `max_ooo_keys` setting. With `max_ooo_keys` set to 10 and `current_key` at 500 — a perfectly valid configuration — the theorem could not fire. Worse, the condition was required even when `gc` does nothing: if the history is short, `gc` returns immediately, but the draft theorem still demanded the bound.

A concrete case: default settings, one stored key, `current_key` equals 7. The Rust code returns immediately because the history is tiny. But the draft theorem needs 2000 ≤ 7, which is false — so the caller's proof is stuck.

---

## Slide 8 — The bridge: the top-level interface in `src/lib.rs`

*≈ 1 min 40 s*

Now let's zoom out to what the application actually sees. `lib.rs` is the bridge — the only file an application, an FFI layer, or a language binding ever talks to.

The interface is deliberately small. Five public functions: `initial_state` to create a session, `send` to produce the next outgoing message and key, `recv` to consume a peer's message and derive the matching key, `current_version` to inspect the protocol negotiation status, and `empty_state` for the disabled case. Everything crossing this boundary is a byte vector or a plain enum — the caller never sees chains, polynomials, or protobuf schemas.

On the right, the status table. Seven of the sixteen functions in `lib.rs` already have theorems: `empty_state` is proved, the four `SecretOutput` accessors are proved, and `current_version` is proved. `decode_state` has one `sorry`, blocked on the protobuf generated code. The three big entry points — `initial_state`, `send`, and `recv` — are next.

Why are they last? Because they depend on everything else: the chain, the v1 state machine, protobuf decoding, the KEM. We verified bottom-up, so each callee's theorem is ready when its caller needs it. The shared blocker is protobuf encode/decode — once we specify that generated code, it unblocks `decode_state`, `initial_state`, `send`, and `recv` all at once.

---

## Slide 9 — Closing: the bridge in context — architecture & what's next

*≈ 1 min 40 s*

Let me close with the big picture. On the left, the end-to-end architecture, five layers from top to bottom.

At the top, the application — Signal's app, an FFI binding, whatever consumes this crate. It sees only opaque byte vectors. Below that, `src/lib.rs` — our five public functions, the bridge. Below that, the internal modules: chain, v1, authenticator, encoding, kdf, serialize, incremental ML-KEM — 47 percent specified so far. Below that, `SrcTranslated/` — the Aeneas-generated Lean 4 model, mechanically extracted from the Rust source. And at the bottom, our hand-written proofs in `Spqr/Specs/` and `Spqr/Math/` — 147 of 312 functions specified, 146 fully proved, 419 spec theorems, 110 math theorems.

On the right, the roadmap. The immediate next step is specifying protobuf encode/decode, which unblocks four functions in one shot. Then `initial_state`, then `send` and `recv` — the end-to-end correctness statements. In parallel, we finish the remaining chain functions and start on the `v1/chunked` state machine, the largest unspecified module.

The key takeaway: the bridge is the last layer, not the first — and that's by design. Bottom-up verification means every callee's theorem is already proved when its caller needs it. Once the protobuf blocker is resolved, the three big entry points can be specified by composing the 146 theorems already beneath them. The goal is a statement that no amount of testing can make: "for all valid inputs, send then recv yields matching keys and a decodable successor state."

Thank you. I'm happy to take questions.

