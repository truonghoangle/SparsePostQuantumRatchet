# Presentation Plan: Formal Verification of SPQR in Lean 4

**Audience:** mixed — non-experts (product / management / cryptography-curious) and
deep-technical (Rust, Lean 4, Aeneas, formal methods).
**Format:** 9 slides (7 was split into 2 in the deck, plus a closing Slide 9). Each slide has a *one-line takeaway* for non-experts (top of slide)
and a *technical layer* (body) that experts can dig into.
**Data snapshot:** 2026-09-05, `main` @ `5e77690` (`lake exe status` after a clean
`lake build`; git history for the timeline).
**Companion slides:** [`report.pptx`](./report.pptx), generated from this plan by
`npm run report-slides` (`scripts/report-slides.ts`). Slide 7 is split over two
slides in the deck (1/2: why it is hard, 2/2: spec history and examples).

> Convention used below: **[Plain]** = what to say to non-experts,
> **[Tech]** = detail for experts, **[Visual]** = what is on the slide.

---

## Slide 1 — What is SPQR and what are we doing to it?

**Takeaway:** *We are mathematically proving that Signal's post-quantum ratchet code does
what it is supposed to do — not just testing it.*

**[Plain]**
- **SPQR = Sparse Post-Quantum Ratchet**, Signal's Rust library that adds
  post-quantum forward secrecy (ML-KEM 768) to the messaging ratchet.
- "Sparse": the large ML-KEM key material is chopped into 32-byte chunks and spread
  across many messages, using an erasure code over the finite field GF(2¹⁶) so that
  any sufficient subset of chunks reconstructs the whole.
- Testing finds *some* bugs; a **machine-checked proof** rules out entire classes of
  bugs for *all* inputs.

**[Tech]**
- Toolchain: Rust → **Charon** (LLBC) → **Aeneas** (pure functional Lean 4 model in
  `SrcTranslated/Funs.lean`, `Types.lean`) → hand-written **spec theorems** in
  `Spqr/Specs/`, mirroring the Rust module tree, plus a mathematical library in
  `Spqr/Math/` (GF(2¹⁶) as a Mathlib field, Lagrange interpolation, Horner, etc.).
- Every theorem has the shape
  `f args ⦃ result => postcondition ⦄` under explicit preconditions; proofs are
  assembled with the project's `step*` tactic from per-callee `@[step]` lemmas.
- Trusted base: Lean kernel, Aeneas translation, a small set of external axioms for
  FFI crates (libcrux, prost, bytes) — see Slide 2.
- Maintained by the Beneficial AI Foundation; Apache-2.0 for our Lean, AGPL-3 for
  upstream Rust and its translation.

**[Visual]** Pipeline diagram `Rust ➜ Charon ➜ Aeneas ➜ Lean specs ➜ ✓`, with the
Signal logo / ML-KEM icon on the left and a Lean check-mark on the right.

---

## Slide 2 — Results so far (numbers)

**Takeaway:** *Roughly half of the crate's functions are formally verified, including
all of the finite-field and polynomial-coding core.*

**[Visual]** Two-column KPI board + a small donut chart.

### Rust-side metrics (from `lake exe status` → `status.json`)

| Metric | Value |
|---|---|
| Crate-local, verifiable Rust functions (tests excluded, trait-impl & opaque excluded) | **312** |
| … of which loop bodies extracted by Aeneas as separate functions | 94 |
| … "top-level" Rust functions (non-artifact) | 218 |
| Functions with a Lean `_spec` theorem | **147 / 312 (47 %)** |
| … top-level functions specified | 102 / 218 (47 %) |
| Specs fully proved (no `sorry` in own proof) | **146 / 147** |
| Only unfinished spec | `spqr::decode_state` (blocked on prost-generated code translated as `sorry`) |
| Remaining unspecified Rust functions | 165 (mostly `v1/chunked/*`, `v1/unchunked/{send_ek,send_ct}.rs`, `Chain::*`, protobuf-generated code) |

### Completion status per `.rs` file (top-level functions, specified / total)

| File | Done | Notes |
|---|---|---|
| `encoding/gf.rs` | **13 / 13 (100 %)** | GF(2¹⁶) arithmetic incl. Barrett/table reduction |
| `encoding/polynomial.rs` | **32 / 32 (100 %)** | Lagrange interpolation, encoder/decoder |
| `authenticator.rs` (+`serialize.rs`) | **8 / 8 (100 %)** | HMAC-based header/ct MACs |
| `kdf.rs` | 1 / 1 | HKDF (modulo `hkdf_to_slice_spec` axiom) |
| `util.rs` | 3 / 3 | constant-time helpers |
| `v1/unchunked/send_ek/serialize.rs` | 8 / 8 | protobuf round-trips |
| `v1/unchunked/send_ct/serialize.rs` | 10 / 10 | protobuf round-trips |
| `v1/chunked/states/serialize.rs` | 7 / 9 | varint / chunk / message codec |
| `chain.rs` | 11 / 25 (44 %) | `ChainParams`, `KeyHistory` done; `ChainEpochDirection`, `Chain` in progress |
| `lib.rs` | 7 / 16 | public API helpers; `send`/`recv`/`initial_state` next |
| `incremental_mlkem768.rs` | 2 / 6 | thin wrappers over libcrux |
| `v1/chunked/{send_ek,send_ct}.rs`, `v1/unchunked/{send_ek,send_ct}.rs`, `v1/chunked/states.rs` | 0 | state machines — next phase |
| `generated/signal.proto.pq_ratchet.rs` | 0 / 19 | generated protobuf code (out of scope) |

### Lean-side metrics (`grep` over `Spqr/`)

| Metric | Value |
|---|---|
| Spec files (`Spqr/Specs/**/*.lean`) | 188 |
| Spec theorems (`*_spec`) | 312 (incl. loop-body / loop specs) |
| Auxiliary lemmas inside spec files | 107 |
| Mathematical library files (`Spqr/Math/`) | 32 files, 110 lemmas, 21 definitions |
| Aeneas-model / crypto helper lemmas (`Spqr/Auxiliary`, `Spqr/Crypto`) | 18 |
| **Total hand-written theorems/lemmas** | **≈ 555** |
| Project-level axioms (hand-written) | **1** — `spqr.kdf.hkdf_to_slice_spec` (HKDF semantics) |
| External-crate axioms in `SrcTranslated/FunsExternal.lean` / `TypesExternal.lean` | ≈ 40 (libcrux ML-KEM & HMAC, prost, bytes, `core::fmt`) |
| Standard Lean axioms reached by specs | `propext`, `Quot.sound`, `Classical.choice` (147 / 135 / 131 specs) |
| Specs depending on `sorryAx` (transitively, via translated generated code) | 9 |
| Specs depending on any external axiom | ≤ 15 per axiom (e.g. slice `RangeFull` get_unchecked: 15; `libcrux_hmac.hmac`: 4) |
| Lines in the largest single proof file | 962 (`Spqr/Specs/Chain/KeyHistory/Gc.lean`) |

**[Plain] talking points**
- "Verified" here means: a theorem about the *exact* translated code, checked by the
  Lean kernel; not a model, not a re-implementation.
- The entire erasure-coding core — the mathematically hardest part — is 100 % covered.
- Remaining work is mostly protocol state machines and the top-level `send`/`recv`.

---

## Slide 3 — Growth of verified Rust functions over time

**Takeaway:** *Steady, accelerating progress: from 8 verified Rust functions in
mid-April to 147 in early September.*

**[Visual]** Combo chart (x = ISO week 2026): bars = Rust functions verified that
week, line (secondary axis) = cumulative number of verified Rust functions.
Annotate milestones: `gf.rs` done (W23), Lagrange core (W27–W28), encoder +
serialization (W31–W32), `lib.rs` API + `Authenticator` + `ChainParams` (W32–W34),
`KeyHistory` (W35–W36).

**Data source (what the chart actually counts):** the 147 Rust functions that have a
spec theorem in `status.json` today; each is dated by the ISO week in which the Lean
file declaring its `_spec` theorem first entered git
(`python3 scripts/lib/verified_over_time.py status.json`). Loop-body artifacts count
as functions, consistent with the 147 total on Slide 2.

| Week (2026) | Verified | Cumulative | Milestone |
|---|---|---|---|
| W16 (Apr 13) | 8 | 8 | first proofs: `gf::{poly_reduce, poly_mul, mul}`, `Pt`/`Poly` `serialize`/`deserialize` |
| W17–W19 | 0 | 8 | extraction pipeline / Aeneas setup |
| W20 | 2 | 10 | `reduce_from_byte`, `REDUCE_BYTES` |
| W21 | 8 | 18 | `GF16::{new, const_sub, const_mul, const_div}`, `reduce_bytes`, `unaccelerated::mul2` |
| W22 | 0 | 18 | GF(2¹⁶) as a Mathlib `Field` (`Spqr/Math/Gf16`) |
| W23 | 5 | 23 | **`gf.rs` complete** (`div_impl`, `div`, `parallel_mult`, …) |
| W24 | 8 | 31 | `Poly::{zero, lagrange_interpolate_complete, mult_xdiff_assign_trailing}`, `util::*` |
| W25 | 4 | 35 | `Poly::{mult_assign, compute_at}`, `Authenticator::{into_pb, from_pb}` |
| W26 | 2 | 37 | `Poly::{clone, lagrange_interpolate_prepare}` |
| W27 | 11 | 48 | `PolyConst::*`, `Authenticator::{mac_ct, mac_hdr}`, `mlkem768::generate` |
| W28 | 19 | 67 | **`Poly::lagrange_interpolate`** (Slide 5) + its loop bodies, `add_assign`, `lagrange_sum` |
| W29 | 5 | 72 | `COMPLETE_POINTS_POLYS_*`, `PolyEncoder::encode_bytes_base` |
| W30 | 5 | 77 | `PolyDecoder::new*`, `Pt::{eq, cmp}`, `decode_varint` |
| W31 | 13 | 90 | `Poly::from_complete_points`, `PolyDecoder::{into_pb, from_pb}`, `encode/decode_chunk`, `encode_varint` |
| W32 | 30 | 120 | `PolyEncoder::{point_at, chunk_at}`, `PolyEncoder` pb loops, **`Option<T>::add_chunk`** (Slide 6), `Message::{serialize, deserialize}`, all unchunked `into_pb`/`from_pb`, `lib.rs` `SecretOutput`/`Version` |
| W33 | 5 | 125 | `empty_state`, `Version::MAX`, `Error::from` |
| W34 | 11 | 136 | `Authenticator::{new, update, verify_ct, verify_hdr}`, `ChainParams::*`, `decode_state`, `current_version`, `hkdf_to_vec` |
| W35 | 5 | 141 | `KeyHistory::{KEY_SIZE, new, add, remove}`, `DEFAULT_CHAIN_PARAMS` |
| W36 (Sep 1) | 6 | 147 | **`KeyHistory::gc`** (Slide 7, largest proof), `KeyHistory::{get, clear}` |

<details><summary>Earlier PR-based proxy (kept for reference)</summary>

Merged PRs titled "Specify and verify …" per week (144 PRs ↔ 147 functions):

| Week (2026) | Added | Cumulative | Milestone |
|---|---|---|---|
| W20 (May 11) | 1 | 1 | `gf::reduce::reduce_from_byte` — first proof |
| W21 | 11 | 12 | `reduce_bytes`, `poly_reduce`, `unaccelerated::{mul, mul2}`, `GF16::{new, ZERO, ONE, const_sub, const_mul, const_div}` |
| W22 | 2 | 14 | `mul`, `mul_assign` (GF(2¹⁶) field infrastructure built) |
| W23 (Jun 1) | 5 | 19 | **`gf.rs` complete** (`div_impl`, `div`, `div_assign`, `mul2_u16`, `parallel_mult`) |
| W24 | 12 | 31 | `Poly::{zero, lagrange_interpolate_complete, mult_xdiff_assign_trailing, add_assign}`, `polynomial.rs` constants, `util::{inz, is_non_zero, compare}` |
| W25 | 7 | 38 | `Poly::{mult_assign, serialize, deserialize, compute_at}`, `Authenticator::{MACSIZE, into_pb, from_pb}` |
| W26 | 3 | 41 | `Poly::{clone, lagrange_interpolate_prepare, lagrange_sum}` (Lagrange lemmas in `Spqr/Math/Poly/Lagrange`) |
| W27 (Jul 1) | 7 | 48 | `Poly::lagrange_interpolate_pt`, `PolyConst::{mult, mult_xdiff, lagrange_interpolate_pt}`, `Authenticator::{mac_ct, mac_hdr}` |
| W28 | 5 | 53 | **`Poly::lagrange_interpolate`** (Slide 5), `lagrange_polys_for_complete_points`, `PolyConst::to_poly`, `PolyEncoder::into_pb` |
| W29 | 11 | 64 | `COMPLETE_POINTS_POLYS_{3,5,30,34,36}`, `PolyEncoder::{encode_bytes_base, from_pb}`, `serialize::Error::*`, `flip_endianness` |
| W30 | 18 | 82 | `PolyDecoder::{new, new_with_poly_count, get_pts_needed}`, `Pt::{eq, cmp, partial_cmp}`, `const_polys_to_polys` closures, `decode_varint`, `MessageType::*` |
| W31 (Aug 1) | 10 | 92 | `Poly::from_complete_points`, `PolyDecoder::{into_pb, from_pb, necessary_points}`, `encode_varint`, `encode_chunk`, `decode_chunk` |
| W32 | 15 | 107 | `PolyEncoder::{point_at, chunk_at}`, **`PolyDecoder::add_chunk`** (Slide 6), `Message::{serialize, deserialize}`, all unchunked `into_pb`/`from_pb`, `Option<T>` Encoder/Decoder impls |
| W33 | 13 | 120 | `lib.rs`: `empty_state`, `SecretOutput::*`, `Version::{DISABLED, TryFrom, From}`, `Error::from` |
| W34 | 17 | 137 | `lib.rs`: `decode_state`, `current_version`, `Version::MAX`; `Authenticator::{verify_ct, verify_hdr, update, new}`; `ChainParams::*`, `DEFAULT_CHAIN_PARAMS` |
| W35 | 4 | 141 | `KeyHistory::{KEY_SIZE, new, add, remove}` |
| W36 (Sep 1) | 3 | 144 | **`KeyHistory::gc`** (Slide 7, largest proof), `KeyHistory::{get, clear}` |

</details>

**[Tech] note for the chart:** the gaps (W17–W19, W22) correspond to building
reusable infrastructure (Aeneas extraction setup; `Spqr/Math/Gf16/Field.lean` — GF(2¹⁶)
as a Mathlib `Field`; `Spqr/Math/Poly/Lagrange/*`), which then paid off with the W28
and W32 spikes. The PR-based proxy and the function-based count agree on the total
but differ in timing because one PR often lands several loop-body specs at once.

---

## Slide 4 — File-by-file report

**Takeaway:** *Four areas: finite field (done), polynomial coding (done), key chain (in
progress), serialization (mostly done).*

**[Visual]** Four cards, one per file, each with a status badge and 3–4 bullets.

### `src/encoding/gf.rs` — ✅ 13 / 13
- What it is: arithmetic in **GF(2¹⁶)** with the irreducible polynomial
  `x¹⁶ + x⁵ + x³ + x + 1` (`0x2100B`); table-based and Barrett-style reduction,
  `parallel_mult`, constant-time `div` via exponentiation.
- Lean: `Spqr/Math/Gf16/{Basic,Field,Irreducible}.lean` build `GF216` as a genuine
  Mathlib field (irreducibility proved by `decide`/`bv_decide`); every Rust op is
  proved equal to the corresponding field operation via `GF16.toGF216`.
- Notable specs: `reduce_bytes_spec` (256-entry table is correct for every index),
  `div_impl_spec` (`a / b = a * b^(2^16-2)`), `mul2_u16_spec`.

### `src/encoding/polynomial.rs` — ✅ 32 / 32 top-level (63 incl. loop bodies)
- What it is: the erasure code. A message is split into 16 interleaved sequences of
  GF(2¹⁶) symbols; each sequence defines a polynomial through **Lagrange
  interpolation**; chunk `k` = evaluation of all 16 polynomials at `x = k`.
- Lean: `Spqr/Math/Poly/{Lagrange,Horner,LinearFactors,Identities,…}` — 110 lemmas.
  Key definitions: `lagrangeBasisPoly`, `lagrangeScaleGF216`,
  `lagrangeInterpolantSum`, `scaledLagrangeBasis`, `completePoints`.
- Notable specs: `lagrange_interpolate_spec` (Slide 5), `from_complete_points_spec`,
  `PolyEncoder.point_at_spec` / `chunk_at_spec`, `PolyDecoder.add_chunk_spec` (Slide 6).
- Challenges solved: Rust's "×x then drop lowest coefficient" trick; `const fn`
  precomputed tables `COMPLETE_POINTS_POLYS_{1,3,5,30,34,36}`; iterator adapters
  (`enumerate().map().collect()`) needing a bridge lemma (`MapCollectBridge`).

### `src/encoding.rs` — ✅ (traits + `Option<T>` wrappers)
- Defines `Encoder`/`Decoder` traits and `Chunk { index: u16, data: [u8; 32] }`.
- Lean: `Spqr/Specs/Encoding/{Encoder,Decoder,EncodingError}` — trait-impl
  forwarding lemmas for `Option<T>`, error-conversion spec.

### `src/chain.rs` — 🟡 11 / 25 (44 %)
- What it is: symmetric key chain per epoch; `KeyHistory` stores skipped keys as
  36-byte records `[u32 BE index ‖ 32-byte key]`, garbage-collected when the history
  exceeds `trim_size = ⌊1.1·max_ooo_keys⌋ + 1` records.
- Done: `ChainParams::{default, clone, into_pb, max_jump_or_default,
  max_ooo_keys_or_default, trim_size}`, `DEFAULT_CHAIN_PARAMS`,
  `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH`, `KeyHistory::{KEY_SIZE, new, add, remove,
  gc, get, clear}`, `ChainEpochDirection::new`.
- In progress / next: `ChainEpochDirection::{next_key_internal, next_key, key,
  into_pb, from_pb, clear_next}`, `Chain::{new, add_epoch, send_key, recv_key,
  epoch_idx, ced_for_direction}`.
- Highlight: `gc_spec` — full bijection between retained records and unexpired
  input records (Slide 7).

### Serialization (`src/serialize.rs`, `src/v1/**/serialize.rs`, `src/authenticator/serialize.rs`) — 🟢 32 / 39
- What it is: (a) hand-rolled varint / chunk / message wire format for the chunked V1
  protocol, (b) protobuf `into_pb`/`from_pb` round-trips for every state struct.
- Done: `encode_varint`/`decode_varint`, `encode_chunk`/`decode_chunk`,
  `Message::{serialize, deserialize}`, `MessageType::{try_from, from_payload}`,
  all 18 unchunked `into_pb`/`from_pb`, `serialize::Error::{clone, eq, from}`.
- Remaining: 10 chunked-state `into_pb` (Vec-of-struct loops), 2 `States::{into_pb,
  from_pb}`.
- Typical spec shape: `decode (encode x) = ok x` plus exact byte-length formulas
  (`MAX_VARINT_BYTES_LEN = 10`).

---


## Slide 5 — A complex function in `polynomial.rs`: `Poly::lagrange_interpolate`

**Takeaway:** *The left side is the textbook formula; the right side is the theorem Lean
checked about the real Rust code — they say the same thing.*

**[Visual]** Split slide. Top strip: the Rust signature
`fn lagrange_interpolate(pts: &[Pt]) -> Poly` and the doc-comment
"return a Poly with f(pts[i].x) == pts[i].y for all i; O(N²) work, O(N) space".

### Left — mathematical description (natural language)

Given `n` points `(x₀,y₀), …, (xₙ₋₁,yₙ₋₁)` in GF(2¹⁶) with distinct `xᵢ`, the
Lagrange interpolant is

```
L(x) = Σᵢ yᵢ · ℓᵢ(x),    ℓᵢ(x) = Πⱼ≠ᵢ (x − xⱼ) / (xᵢ − xⱼ)
```

The Rust code computes it *without* division and *without* re-multiplying for each `i`:

1. **Prepare.** `T(x) = Πⱼ (x − xⱼ)` (the "template"), built highest-coefficient-first
   by repeated `mult_xdiff_assign_trailing` (multiply the trailing sub-polynomial by
   `(x − xⱼ)`).
2. **Complete for point `i`.** Starting from a copy of `T`, synthetic-divide by
   `(x − xᵢ)` and scale by `yᵢ · dᵢ^(2¹⁶−2)` where `dᵢ = Πⱼ≠ᵢ (xᵢ − xⱼ)` (Fermat
   inverse; char 2 so `+ = −`). The working buffer now holds `x · yᵢ · ℓᵢ(x)`.
3. **Accumulate.** Add coefficients `1..n` of the working buffer into `out`
   (dropping index 0 is "divide by `x`" for free).

Result: a polynomial of degree `< n` (exactly `n` coefficients) equal to `L(x)`.
Edge case: `n = 0` gives the zero polynomial.

### Right — Lean specification (`Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolate.lean`)

```lean
@[step]
theorem lagrange_interpolate_spec
    (pts : Slice Pt)
    (h_len : pts.length + 1 ≤ Usize.max) :
    lagrange_interpolate pts ⦃ (result : Poly) =>
      result.degree = pts.length ∧
      (pts.length = 0 → result.toGF216Poly = 0) ∧
      result.toGF216Poly = lagrangeInterpolantSum pts pts.length ⦄
```

where (`Spqr/Math/Poly/Lagrange/`):

```lean
noncomputable def lagrangeInterpolantSum (pts : List Pt) : Nat → GF216[X]
  | 0     => 0
  | n + 1 => lagrangeInterpolantSum pts n +
      (if h : n < pts.length
       then C (lagrangeScaleGF216 (pts.get ⟨n, h⟩) pts) * lagrangeBasisPoly pts n
       else 0)

noncomputable def lagrangeScaleGF216 (pi : Pt) (pts : List Pt) : GF216 :=
  pi.y.toGF216 * (lagrangeDenomProd pi.x pts 0) ^ (2 ^ 16 - 2)

noncomputable def lagrangeBasisPoly (pts : List Pt) (i : Nat) : GF216[X] :=
  if i < pts.length
  then prodLinearFactors pts 0 i * prodLinearFactors pts (i + 1) pts.length
  else 1
```

**[Tech] what to point out**
- `result.toGF216Poly` lifts the `Vec<GF16>` coefficient list to a Mathlib
  `Polynomial GF216`, so the RHS is an honest algebraic object; the identity is
  *coefficient-exact*, not just "agrees at the sample points".
- Proof structure mirrors the code: `lagrange_interpolate_loop0_loop0.loop_spec`
  (inner `+=` loop, invariant on processed prefix), `lagrange_interpolate_loop0`
  (outer loop, invariant `working · (X − C xᵢ) = X · C(scaleᵢ) · T`), then
  `lagrange_interpolate_formula` → `lagrange_interpolate_spec` via
  `mul_right_cancel₀` on the monic factor `X − C xᵢ`.
- Only precondition is a `usize` non-overflow bound; the Rust `hax_lib::requires
  (pts.len() ≤ 36)` is *not* needed for correctness, only for the caller's capacity
  reasoning.

**[Plain] one sentence:** "The theorem literally says: the bytes the Rust code produces
are the coefficients of the unique polynomial through those points."

---


## Slide 6 — Using `polynomial.rs` from `encoding.rs`: `Option<T>::add_chunk`

**Takeaway:** *`encoding.rs` only unwraps a box, calls the decoder inside, and puts it
back. Prove that once for any decoder, then plug in the `polynomial.rs` result.*

**[Visual]** 2 × 2 grid. Row 1 = plain-language description, row 2 = Lean.
Column 1 = *without* `polynomial.rs` (works for any decoder `T`); column 2 = *with*
`polynomial.rs` (`T = PolyDecoder`). Arrow "⊕ `PolyDecoder.add_chunk_spec`" between
the columns.

Rust (`src/encoding.rs`):

```rust
impl<T: Decoder> Decoder for Option<T> {
    #[hax_lib::requires(self.is_some())]
    fn add_chunk(&mut self, chunk: &Chunk) {
        let mut tmp = self.take().unwrap();
        T::add_chunk(&mut tmp, chunk);
        *self = Some(tmp);
    }
}
```

### Top-left — without `polynomial.rs` (any decoder `T`)

The box must not be empty. Take the decoder out, let it process the chunk, put it
back. So: the box is still full afterwards, and whatever is true of the inner
decoder's result is true of what is inside the box. We do not need to know what the
decoder does.

### Bottom-left — `add_chunk_spec_lift` (`Spqr/Specs/Encoding/Decoder/AddChunk.lean`)

```lean
theorem add_chunk_spec_lift
    {T : Type} (DecoderInst : encoding.Decoder T) (self : Option T)
    (chunk : encoding.Chunk)
    (h_some : self.isSome)
    (P : T → Prop)
    (h_inner : ∀ tmp, self = some tmp →
        DecoderInst.add_chunk tmp chunk ⦃ (r : T) => P r ⦄) :
    add_chunk DecoderInst self chunk ⦃ (result : Option T) =>
      ∃ tmp', result = some tmp' ∧ P tmp' ⦄ := by
  unfold add_chunk
  simp only [Aeneas.Std.core.option.Option.take]
  step with Aeneas.Std.core.option.Option.unwrap.spec as ⟨tmp, h_eq⟩
  have h_post := h_inner tmp h_eq
  step with h_post
  grind
```

`P` is *any* property of the inner decoder; the `Option` layer just re-tags it with
`some`.

### Top-right — with `polynomial.rs` (`T = PolyDecoder`)

Now the decoder is the polynomial one. Each of the 16 byte pairs in the chunk becomes a
point (x = chunk index, y = the two bytes) for polynomial number `j`. The point is
stored, in sorted order, only if it is still useful (index small, or that polynomial
does not yet have enough points); otherwise nothing changes. The counters `pts_needed`
and `is_complete` never change.

### Bottom-right — `add_chunk_spec_poly_decoder` (same file)

```lean
theorem add_chunk_spec_poly_decoder
    (pd0 : PolyDecoder) (chunk : encoding.Chunk)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 → (pd0.pts[k]!).length + 17 ≤ Usize.max) :
    add_chunk PolyDecoder.Insts.SpqrEncodingDecoder (some pd0) chunk ⦃
        (result : Option PolyDecoder) =>
      ∃ pd, result = some pd ∧
        pd.pts_needed = pd0.pts_needed ∧
        pd.is_complete = pd0.is_complete ∧
        ∃ (selfs : Nat → PolyDecoder),
          selfs 0 = pd0 ∧
          selfs 16 = pd ∧
          ∀ (j : Nat), j < 16 →
            let total_idx := chunk.index.val * 16 + j
            let poly := total_idx % 16
            let poly_idx := total_idx / 16
            let np := pd0.pts_needed.val / 16 +
              (if poly < pd0.pts_needed.val % 16 then 1 else 0)
            (selfs (j + 1)).pts_needed = pd0.pts_needed ∧
            (selfs (j + 1)).is_complete = pd0.is_complete ∧
            poly < 16 ∧
            poly_idx = chunk.index.val ∧
            ∃ (p : Pt),
              p.x.value.val = poly_idx ∧
              p.y.value.val = (chunk.data[j * 2]!) * 256 + (chunk.data[j * 2 + 1]!) ∧
              (if poly_idx < np ∨ ((selfs j).pts.val[poly]!).val.length < np
               then
                 (∀ (k : Nat), k ≠ poly → (selfs (j + 1)).pts[k]! = (selfs j).pts.val[k]!) ∧
                 PolyDecoder.Insts.SpqrEncodingDecoder.IsSortedPushResult
                   ((selfs j).pts.val[poly]!).val
                   ((selfs (j + 1)).pts.val[poly]!).val p
               else
                 selfs (j + 1) = selfs j) ⦄ := by
  apply add_chunk_spec_lift PolyDecoder.Insts.SpqrEncodingDecoder (some pd0) chunk (by simp)
  intro tmp h_eq
  simp only [Option.some.injEq] at h_eq
  rw [h_eq] at h_push_cap
  rw [h_eq]
  exact PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec tmp chunk h_overflow h_push_cap
```

**[Tech] talking points**
- The whole right-hand proof is six lines: `add_chunk_spec_lift` does the `Option`
  plumbing, `PolyDecoder…add_chunk_spec` (from `Spqr/Specs/Encoding/Polynomial/
  PolyDecoder/AddChunk.lean`) supplies `P`.
- `selfs 0 … selfs 16` is the chain of intermediate decoder states, one per byte pair;
  `IsSortedPushResult` captures the sorted-set append / replace / insert cases.
- The two hypotheses are pure `usize` non-overflow bounds forwarded verbatim to the
  inner spec; nothing protocol-specific is assumed.

**[Plain] one sentence:** "Left: the wrapper is honest — it never loses the decoder and
never changes what it did. Right: therefore every guarantee we proved about the
polynomial decoder carries straight through to the type the protocol actually uses."

---

## Slide 7 — Case study: the specification of `KeyHistory::gc` in `chain.rs`

**Takeaway:** *The "delete old keys" routine is 20 lines of Rust and 962 lines of Lean;
the spec went through four iterations before it was both true and useful.*

**[Visual]** Timeline strip (Aug 25 → Aug 29 → Aug 31 PR #491) above; below, a
two-column "v1 spec → final spec" diff with the changed lines highlighted.

### What `gc` does (Rust, `src/chain.rs` 145–168)

```rust
#[hax_lib::opaque] // ordering of slices needed
fn gc(&mut self, current_key: u32, params: &pqrpb::ChainParams) {
    if self.data.len() >= params.trim_size() * Self::KEY_SIZE {
        assert!(current_key >= params.max_ooo_keys_or_default());
        let trim_horizon = &(current_key - params.max_ooo_keys_or_default()).to_be_bytes()[..];
        let mut i = 0;
        while i < self.data.len() {
            if trim_horizon.cmp(&self.data[i..i + 4]) == Ordering::Greater {
                self.remove(i, params);   // swap-remove: last record moves to position i
            } else { i += Self::KEY_SIZE; }
        }
    }
}
```

`data` is a flat `Vec<u8>` of 36-byte records `[u32 BE index ‖ 32-byte key]`.
Note that **hax marked this function `opaque`** ("ordering of slices needed") — i.e. it
was considered out of reach for the F\* pipeline. We verified it in Lean.

### Why the specification is complex

1. **Byte-level representation.** Records are not a `Vec<Record>`; the spec has to talk
   about 36-alignment (`m % 36 = 0`), 4-byte prefixes (`data.slice m (m+4)`) and
   lexicographic byte comparison (`Slice.lexCmpAux OrdU8 … ≠ ok .gt`) instead of `≥`
   on integers. Big-endian encoding makes lexicographic order agree with numeric order —
   a fact that has to be *used*, not assumed.
2. **Swap-remove reorders the data.** After `remove(i)`, position `i` holds the former
   last record, which may itself be expired, so `i` is *not* advanced. A naive
   invariant "everything before `i` is live and untouched" is false; the correct one is
   "everything before `i` is live, and the multiset of records is preserved up to
   deletion".
3. **What does "correct GC" mean?** Three increasingly strong properties:
   - *liveness*: every record left is unexpired (`index ≥ horizon`);
   - *completeness*: every unexpired input record is still present;
   - *no duplication*: nothing is copied twice (swap-remove could in principle
     duplicate). Stating this needs an explicit **injective provenance map**
     `f : result offsets → source offsets` and its inverse `g` — together a bijection
     between result records and unexpired source records.
4. **Two loops and two platforms.** Aeneas extracts the `while` as `gc_loop`; the spec
   has a body lemma (`body_spec`), a loop lemma (`gc_loop_spec`, by
   `loop.spec_decr_nat` with a 12-conjunct invariant), and two top-level theorems
   (`gc_spec` for 32-bit-safe bounds, `gc_spec_64` for 64-bit).

### Where the verification difficulty lies

- Proving the **bijection** through a `setSlice!`/`take` swap-remove: the maps `f`, `g`
  must be rebuilt at every iteration (`f_inv`, `g_inv` in the proof) and injectivity
  re-established; three private slice lemmas (`slice_eq_of_getElem!`,
  `getElem!_of_slice_eq`, `slice_eq_of_prefix`) were needed just to move between
  "slices equal" and "elements equal".
- **Totality of the comparison**: `Slice.lexCmpAux` returns a `Result`; lemma
  `lexCmpAux_OrdU8_ok` (induction on both lists) shows it never fails, otherwise the
  body spec could not case-split on the `Ordering`.
- **Arithmetic side conditions** from `trim_size = max_ooo * 11 / 10 + 1` and
  `trim_size * 36`: overflow bounds differ per platform
  (`max_ooo_keys < 108 458 770` for 32-bit vs `< 390 451 572` for 64-bit — the latter is
  the number hax-`assume`d in `trim_size`).


### How the preconditions were flawed at first (development history of `Gc.lean`)

| Date | Commit | Preconditions on `current_key` | Postcondition | Size |
|---|---|---|---|---|
| Aug 25 | `7886560` (first draft) | `h_key_ooo : max_ooo_keys ≤ current_key` **and** `h_key_def : 2000 ≤ current_key` | liveness + weak provenance (`∀ m ∃ n`) | ~480 lines, 14 thms |
| Aug 29 | `201b82d` | same | + completeness (`∀ live n ∃ m`) | +108 / −31 |
| Aug 29 | `036857f` | same | + `gc_spec_64` variant | — |
| Aug 31 | `aa4962d` PR #491 (final) | `h_key_ge : trim_threshold ≤ data.length → max_ooo ≤ current_key` | + injective `f` **and** `g` (bijection) | 962 lines |

**The flaw.** The first draft required *unconditionally* that
`current_key ≥ max_ooo_keys` **and** `current_key ≥ 2000`.
- The `2000` clause was an artefact of how the proof handled the default branch
  (`max_ooo_keys = 0 ⇒ 2000`): it was required for *both* branches even when the caller
  passed an explicit non-zero `max_ooo_keys`. With `max_ooo_keys = 10`, a caller with
  `current_key = 500` is perfectly valid Rust, yet the theorem was inapplicable.
- The unconditional form also over-constrained the **common no-op path**: when the
  history is below the trim threshold, `gc` returns immediately and never evaluates
  `assert!(current_key >= max_ooo)`; demanding the bound anyway made the lemma
  unusable inside `ChainEpochDirection::key`, which calls `gc` on *every* key derivation
  including `ctr = 0`.
- **Example that broke v1:** `max_ooo_keys = 2000` (default), `data.len() = 36`
  (one stored key), `current_key = 7`. Rust: `36 < 2201·36`, returns unchanged — fine.
  v1 spec: precondition `2000 ≤ 7` is false → theorem unusable, `step*` in the caller
  stalls.
- **Fix:** make the bound *conditional on the branch that needs it*
  (`h_key_ge : trim_threshold ≤ self.data.length → max_ooo ≤ current_key`), fold the
  default into `max_ooo` via the `if 0 < max_ooo_keys then … else 2000` definition
  (`spqr.chain.maxOoo`), and prove the `assert!` from it in the proof
  (`rw [if_pos hlt] at h_key_ge; grind`). This mirrors the Rust `assert!` exactly:
  it is a *precondition of the trimming branch*, not of the function.

**Example that motivated the bijection (v2 → final).** With records
`[A:idx 5, B:idx 1, C:idx 9]`, horizon `3`, the loop at `i = 36` removes `B` by copying
`C` into slot 1 and truncating → `[A, C]`. Liveness + completeness alone would also be
satisfied by the (wrong) output `[A, C, C]` or by `[A, A]` if `C`'s bytes were mis-copied
over `A`. Only the injective provenance map `f` (and its inverse `g`) excludes these,
which is what a downstream `get` proof needs to argue "the key is found exactly once".

**[Plain] one sentence:** "The first version of the theorem was *true* but described
the function so strictly that it could never be applied; the final version says exactly
what the code guarantees — no more, no less — and that is what makes it reusable."

---

## Slide 8 — The bridge: the top-level interface in `src/lib.rs`

**[Plain] takeaway:** `lib.rs` is the only part an application talks to. Its small helpers
are proved; the three big entry points — `initial_state`, `send`, `recv` — are next, and
everything they call is already done.

**[Plain] what the bridge does (left column)**
- An application never sees chains, polynomials or key histories — only bytes: a
  serialized state, a serialized message, and (sometimes) a secret.
- Three entry points do all the work: `initial_state` creates a state, `send` produces a
  message and a key, `recv` reads a message and returns the new state and key.
- Around them sit small helpers: `decode_state` (read the state bytes), `current_version`
  (which protocol version is in use), `SecretOutput::*` (unpack the returned secret).
- This is where every proved piece must fit together; a wrong bridge would make the rest
  of the proofs useless to the application.

**[Tech] public API shown as code**
```rust
pub fn initial_state(params: Params) -> Result<SerializedState, Error>
pub fn send<R: Rng + CryptoRng>(state: &SerializedState, rng: &mut R) -> Result<Send, Error>
pub fn recv(state: &SerializedState, msg: &SerializedMessage) -> Result<Recv, Error>
pub fn current_version(state: &SerializedState) -> Result<CurrentVersion, Error>
pub fn empty_state() -> SerializedState
```

**[Tech] status table (right column)** — `lib.rs`: 16 functions, 7 with theorems
(`status.json`, tests excluded)

| Function | Status | What the theorem says |
|---|---|---|
| `empty_state` | ✅ proved | returns the empty byte string |
| `SecretOutput::{send_secret, recv_secret, secret, has_secret}` | ✅ proved (4) | exactly which variant yields a secret |
| `current_version` | ✅ proved | empty → `V0`, negotiation done; else the decoded state's version, or `StateDecode` |
| `decode_state` | 🟡 1 `sorry` | empty → default state; else decode/encode round-trip — blocked on prost generated code (issue #102) |
| `initial_state`, `init_inner` | ⬜ next | state bytes contain the right version, direction, chain params |
| `send`, `recv` | ⬜ next | top-level correctness statements |
| `chain_from*`, `msg_version`, `state_version`, `Direction::switch` | ⬜ next | helpers used by `send` / `recv` |

Spec files: `Spqr/Specs/Lib/{EmptyState,CurrentVersion,DecodeState}.lean`,
`Spqr/Specs/Lib/SecretOutput/*.lean`.

**[Tech] why the big three are last**
- They depend on everything else (chain 11/25, v1 state machine, protobuf decoding, KEM);
  verification was bottom-up so each layer's theorem is ready when its caller needs it.
- The blocker is shared: protobuf encode/decode is generated code that the translator
  replaces with `sorry`. Specifying it once unblocks `decode_state`, `initial_state`,
  `send` and `recv` together.

---

## Slide 9 — Closing: the bridge in context — architecture & what's next

**Takeaway:** *The bridge is the capstone: every layer below is being proved so
these five functions can carry machine-checked guarantees to the application.*

**[Visual]** Two-panel slide.

**Left panel — layered architecture diagram** (five stacked rounded boxes with
down-arrows between them):

```
┌──────────────────────────────────────────────────┐
│  Application  (Signal app / FFI / language binding) │  light blue
│  Sees only opaque byte vectors — never touches internals │
└───────────────────────┬──────────────────────────┘
                        ▼
┌──────────────────────────────────────────────────┐
│  src/lib.rs  —  5 public functions               │  accent blue, white text
│  initial_state · send · recv · current_version · empty_state │
└───────────────────────┬──────────────────────────┘
                        ▼
┌──────────────────────────────────────────────────┐
│  Internal modules  (47 % specified)              │  light green
│  chain · v1 · authenticator · encoding · kdf · serialize · incremental_mlkem768 │
└───────────────────────┬──────────────────────────┘
                        ▼
┌──────────────────────────────────────────────────┐
│  SrcTranslated/  (Aeneas-generated Lean 4 model) │  light yellow
│  Funs.lean · Types.lean — mechanically extracted via Charon → Aeneas │
└───────────────────────┬──────────────────────────┘
                        ▼
┌──────────────────────────────────────────────────┐
│  Spqr/Specs/ + Spqr/Math/  (hand-written proofs) │  navy, white text
│  147/312 specified · 146 fully proved · 419 spec + 110 math theorems │
└──────────────────────────────────────────────────┘
```

**Right panel — "What's next" table**

| Milestone | Impact |
|---|---|
| Specify protobuf encode/decode (unblocks prost `sorry` — issue #102) | Unblocks `decode_state`, `initial_state`, `send`, `recv` in one shot |
| Specify `initial_state` | Proves session is created with correct version, direction, chain params |
| Specify `send` + `recv` | End-to-end: send/recv round-trip produces matching keys for all inputs |
| Remaining chain functions (11/25 → 25/25) | Complete key-management layer; needed transitively by send/recv proofs |
| `v1/chunked/*` specs | Largest remaining module — erasure-code state machine |

**Right panel — "Key takeaway" bullets (green heading)**

- The bridge is the last layer, not the first — by design. Bottom-up
  verification means each callee's theorem is ready when its caller needs it.
- Once the protobuf blocker is resolved, the three big entry points can be
  specified by composing the 146 theorems already proved below them.
- Goal: "for all valid inputs, send then recv yields matching keys and a
  decodable successor state" — a statement no amount of testing can make.

---

## Appendix — reproducing the numbers

```bash
lake build Spqr                       # ~40 min cold
lake exe status /tmp/status.json      # 312 functions, 147 specified
python3 scripts/lib/status_summary.py /tmp/status.json

# Lean-side counts
find Spqr/Specs -name '*.lean' | wc -l                                   # 188
grep -rhoE '^(private |protected )?(theorem|lemma) ' Spqr/Specs | wc -l  # 419
grep -rhoE '^(private |protected )?(theorem|lemma) ' Spqr/Math  | wc -l  # 110
grep -rn '^axiom' Spqr SrcTranslated                                     # 1 project + external

# Weekly growth (Slide 3)
git log --date=format:%G-W%V --pretty='%ad %s' | grep -iE 'specify|verify' \
  | awk '{print $1}' | sort | uniq -c

# gc spec history (Slide 7)
git log --date=short --pretty='%h %ad %s' -- Spqr/Specs/Chain/KeyHistory/Gc.lean
git show 7886560:Spqr/Specs/Chain/KeyHistory/Gc.lean | grep -n 'theorem gc_spec' -A8
```

**Assumptions / caveats**
- "Serialize" files in Slide 4 are interpreted as `src/serialize.rs`,
  `src/v1/**/serialize.rs` and `src/authenticator/serialize.rs` (the request's
  `seriars.rs` was read as `serialize.rs`).
- "Verified" = `verified_modulo_specs` in `status.json`: the spec theorem's own proof is
  `sorry`-free. Transitive dependence on external axioms (libcrux, prost) is reported
  separately in Slide 2.
- Weekly growth counts PRs, not functions; a few PRs verify two functions, so the
  cumulative total (144) is slightly below the 147 specified functions.
- The `gc` example values (`max_ooo_keys = 10`, `current_key = 7`, records A/B/C) are
  illustrative; they are not test vectors from the repository.

