/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::encoding::{Encoder for Option<T>}::next_chunk`

The `Encoder` trait is canonically lifted to `Option<T>` whenever `T : Encoder`.  In Rust the
method `next_chunk` on `Option<T>` operates on a `&mut Option<T>` and is only legitimate when the
option is `Some`; under that precondition it transparently delegates to `T::next_chunk` on the
inner value, leaves the option in the `Some` state, and returns the inner chunk verbatim.

To enable formal verification with hax — which disallows mutable references that escape a function
body via APIs such as `Option::take` — the extracted Lean version reifies the borrow as a pair of
ordinary functional steps:

  1. `core.option.Option.take self` — pure decomposition `self ↦ (self, none)`, returning the
     "extracted" inner option together with a `none` placeholder.
  2. `core.option.Option.unwrap o` — partial projection out of `Option T`, succeeding iff
     `o.isSome` (i.e. `self.isSome`).
  3. `EncoderInst.next_chunk tmp` — delegation to the underlying `Encoder T` instance on the
     unwrapped state.
  4. `ok (chunk, some tmp1)` — re-injection of the updated inner state back into the `Some`
     branch.

The composition is a *pure structural lift*: the spec of the outer `next_chunk` carries no extra
mathematical content beyond that of `EncoderInst.next_chunk`; the `Option` layer merely repackages
inputs and outputs.

**Source**: spqr/src/encoding.rs (lines 63:4-71:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.core.option.Option.Insts.SpqrEncodingEncoder

/-- **Spec theorem for `core.option.Option.Insts.SpqrEncodingEncoder.next_chunk` (generic lifting)**:

The `Option<T>`-level `next_chunk` is a transparent lift of `EncoderInst.next_chunk` along the
`Some` constructor.  Concretely: given that `self = some tmp` and that the underlying
`EncoderInst.next_chunk tmp` is specified by some postcondition `Q : encoding.Chunk × T → Prop`,
the `Option`-level call satisfies the lifted postcondition
  `Q' (chunk, self')  ≜  ∃ tmp', self' = some tmp' ∧ Q (chunk, tmp')`.

The proof composes:
  1. `core.option.Option.take` — pure decomposition `(self, _) := (self, none)`.
  2. `core.option.Option.unwrap.spec` — succeeds because `self.isSome`, producing `tmp` with
     `self = some tmp`.
  3. `EncoderInst.next_chunk tmp` — opaque inner call returning `(chunk, tmp1)`.
  4. `ok (chunk, some tmp1)` — repackaging.

No extra hypothesis on `EncoderInst` is required beyond the precondition `self.isSome` imposed by
the Rust `#[hax_lib::requires(self.is_some())]` annotation.

**Source**: spqr/src/encoding.rs (lines 63:4-71:5)
-/
theorem next_chunk_spec_generic
    {T : Type} (EncoderInst : encoding.Encoder T) (self : Option T)
    (h_some : self.isSome)
    (Q : encoding.Chunk × T → Prop)
    (h_inner : ∀ tmp, self = some tmp →
        EncoderInst.next_chunk tmp ⦃ (p : encoding.Chunk × T) => Q p ⦄) :
    next_chunk EncoderInst self ⦃ ((chunk, self') : encoding.Chunk × Option T) =>
      ∃ tmp', self' = some tmp' ∧ Q (chunk, tmp') ⦄ := by
  unfold next_chunk
  simp only [Aeneas.Std.core.option.Option.take]
  step with Aeneas.Std.core.option.Option.unwrap.spec
  rename_i tmp h_eq
  have h_post := h_inner tmp h_eq
  step with h_post
  grind

/--
Specialised to the trivial postcondition `Q ≡ True`, the generic lifting theorem certifies that
`next_chunk` on a `some`-shaped `Option<T>` is total (no panic / no error): it always reduces to
`ok (chunk, some tmp1)` for some `chunk : encoding.Chunk` and `tmp1 : T`, provided the inner
`EncoderInst.next_chunk` is itself total on the unwrapped value.

This is the `Option`-level analogue of the structural fact that the `Encoder` trait is preserved
under the `Some` injection `T ↪ Option T`, lifting the inner encoder's totality verbatim.
-/
@[step]
theorem next_chunk_spec
    {T : Type} (EncoderInst : encoding.Encoder T) (self : Option T)
    (h_some : self.isSome)
    (h_inner_total : ∀ tmp, self = some tmp →
        EncoderInst.next_chunk tmp ⦃ (_ : encoding.Chunk × T) => True ⦄) :
    next_chunk EncoderInst self ⦃ ((_, self') : encoding.Chunk × Option T) =>
      self'.isSome ⦄ := by
  have h := next_chunk_spec_generic EncoderInst self h_some
    (fun _ => True) h_inner_total
  apply WP.spec_mono h
  intro (_, self') ⟨tmp', h_eq, _⟩
  simp [h_eq]

end spqr.core.option.Option.Insts.SpqrEncodingEncoder
