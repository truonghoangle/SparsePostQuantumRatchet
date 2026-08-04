/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk

/-!
# Spec theorems for `spqr::encoding::{Encoder for Option<T>}::next_chunk`

Whenever `T : Encoder`, the `Encoder` trait also applies to `Option<T>`. In Rust the `next_chunk`
method on `Option<T>` takes `&mut self` (which must be `Some`), extracts the inner encoder via
`Option::take` + `unwrap`, delegates to `T::next_chunk` to produce the next serialized chunk, and
stores the updated inner state back into `*self` as `Some(tmp)`.

After hax extraction this borrow-rewriting body becomes a simple pipeline:

  1. `core.option.Option.take self` — pure decomposition `(o, _) := (self, none)`, returning
     the "extracted" inner option together with a `none` placeholder.
  2. `core.option.Option.unwrap o` — partial projection out of `Option T`, succeeding iff
     `o.isSome` (i.e. `self.isSome`).
  3. `EncoderInst.next_chunk tmp` — delegation to the underlying `Encoder T` instance on the
     unwrapped state, producing a pair `(chunk, tmp1)`.
  4. `ok (chunk, some tmp1)` — re-injection of the updated inner state back into the `Some`
     branch, paired with the chunk.

The composition is a *pure structural lift*: the outer `next_chunk` carries no extra mathematical
content beyond that of `EncoderInst.next_chunk`; the `Option` layer merely repackages inputs and
outputs. This mirrors, on the encoding side, the `Option<T>` lifting already established for the
decoder's `add_chunk`, and for the encoder's own `encode_bytes`.

This file proves two theorems built on that observation:

  • `next_chunk_spec_lift` — transports an arbitrary postcondition of the inner encoder's
    `next_chunk` through the `Option<T>` wrapper, under the `self.isSome` precondition.
  • `next_chunk_spec_poly_encoder` — the `T = PolyEncoder` instance, obtained from the lift plus
    the chunk-serialization / polynomial-evaluation postcondition of
    `PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec`.

**Source**: spqr/src/encoding.rs (lines 63:4-71:5)
-/

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial

namespace spqr.core.option.Option.Insts.SpqrEncodingEncoder

/-- **Predicate-lifting spec for `Option<T>::next_chunk`**:

Given an `Encoder T` instance `EncoderInst`, an option `self` with `self.isSome`, and a
predicate `P` on the inner result `(chunk, T)`, the hypothesis `h_inner` states that whenever
`self = some tmp` the inner call `EncoderInst.next_chunk tmp` satisfies `P`. The theorem
concludes that `next_chunk EncoderInst self` satisfies the postcondition obtained by pushing `P`
through the `Some` constructor:

  `result ↦ ∃ tmp', result = (chunk, some tmp') ∧ P (chunk, tmp')`.

The proof composes the four functional steps of the extraction:

  1. `core.option.Option.take` — pure decomposition `(o, _) := (self, none)`.
  2. `core.option.Option.unwrap.spec` — succeeds because `self.isSome`, producing `tmp` with
     `self = some tmp`.
  3. `EncoderInst.next_chunk tmp` — the opaque inner call, discharged by `h_inner`.
  4. `ok (chunk, some tmp1)` — repackaging the chunk and updated state into the `Some` branch.

Since the `Option` layer only re-injects along `Some`, whatever `P` holds for the inner encoder
holds — retagged with `Some` — for the wrapped one. This is the reusable building block behind
`next_chunk_spec_poly_encoder`.

**Source**: spqr/src/encoding.rs (lines 63:4-71:5)
-/
@[step]
theorem next_chunk_spec_lift
    {T : Type} (EncoderInst : encoding.Encoder T) (self : Option T)
    (h_some : self.isSome)
    (P : encoding.Chunk → T → Prop)
    (h_inner : ∀ tmp, self = some tmp →
        EncoderInst.next_chunk tmp ⦃ ((chunk, tmp') : encoding.Chunk × T) =>
          P chunk tmp' ⦄) :
    next_chunk EncoderInst self ⦃ ((chunk, result) : encoding.Chunk × (Option T)) =>
      ∃ tmp', result = some tmp' ∧ P chunk tmp' ⦄ := by
  unfold next_chunk
  simp only [Aeneas.Std.core.option.Option.take]
  step with Aeneas.Std.core.option.Option.unwrap.spec
  rename_i tmp h_eq
  have h_post := h_inner tmp h_eq
  step with h_post
  grind

/-- **`next_chunk` spec for `Option<PolyEncoder>`**:

`next_chunk PolyEncoder.Insts.SpqrEncodingEncoder (some pe0)` inherits, through the `Option<T>`
wrapper, the chunk-serialization behaviour of the underlying `PolyEncoder`: the call succeeds in
the `(chunk, some pe)` shape — the option stays `Some` — and the inner state `pe` together with
the returned `chunk` satisfy exactly the postcondition of
`PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec`:

  • `chunk.index.val = pe0.idx.val` — the chunk's U16 index equals the (pre-increment) encoder
    index.
  • `chunk.data.val.length = 32` — the data array contains exactly 32 bytes.
  • `pe.idx.val = (pe0.idx.val + 1) % U32.size` — the encoder's index is wrapping-incremented.
  • If the encoder was initially in the `Polys` state:
      - The encoder state field is unchanged: `pe.s = pe0.s`.
      - For every `j ∈ [0, 16)`, the big-endian encoding of the `j`-th polynomial evaluation
        satisfies:
        `Nat.toGF216 (256 * chunk.data.val[2 * j]! + chunk.data.val[2 * j + 1]!) =
          (polys[j]!).toGF216Poly.eval (pe0.idx.val.toGF216)`
  • If the encoder was initially in the `Points` state:
      - For any resulting `Polys polys'` state, each polynomial equals the Lagrange interpolation
        of the corresponding points.

The hypotheses `h_idx_fits` (index fits in U16), `h_admissible` (point-set lengths are admissible
for Lagrange interpolation), and `h_coeff_bound` (coefficient arrays have room for one extra
element) are forwarded verbatim to the inner spec.

Proved by feeding `PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec` (the inner `PolyEncoder`
postcondition) into `next_chunk_spec_lift`, whose `Some`-lifted conclusion matches the target shape.

**Source**: spqr/src/encoding.rs (lines 63:4-71:5)
-/
@[step]
theorem next_chunk_spec_poly_encoder
    (pe0 : PolyEncoder)
    (h_idx_fits : pe0.idx.val ≤ U16.max)
    (h_admissible : ∀ pts, pe0.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ (polys : Array encoding.polynomial.Poly 16#usize),
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    next_chunk PolyEncoder.Insts.SpqrEncodingEncoder (some pe0) ⦃
        ((chunk, result) : encoding.Chunk × (Option PolyEncoder)) =>
      ∃ pe, result = some pe ∧
        chunk.index.val = pe0.idx.val ∧
        chunk.data.val.length = 32 ∧
        pe.idx.val = (pe0.idx.val + 1) % U32.size ∧
        match pe0.s with
        | .Polys polys =>
            pe.s = pe0.s ∧
            ∀ (j : Nat), j < 16 →
              Nat.toGF216 (256 * chunk.data.val[2 * j]! + chunk.data.val[2 * j + 1]!) =
                (polys[j]!).toGF216Poly.eval (pe0.idx.val.toGF216)
        | .Points pts =>
            ∀ polys', pe.s = .Polys polys' →
              ∀ (j : Nat), j < 16 →
                polys'[j]!.toGF216Poly =
                  ∑ k ∈ Finset.range (pts[j]!).value.length,
                    C (((pts[j]!).value[k]!).toGF216) *
                      scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k ⦄ := by
  unfold next_chunk
  simp only [Aeneas.Std.core.option.Option.take]
  step with Aeneas.Std.core.option.Option.unwrap.spec
  rename_i tmp h_eq
  have h_tmp_eq : tmp = pe0 := by injection h_eq with h; exact h.symm
  simp only [h_tmp_eq]
  have h_inner := PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec pe0
    h_idx_fits h_admissible h_coeff_bound
  step with h_inner
  grind

end spqr.core.option.Option.Insts.SpqrEncodingEncoder
