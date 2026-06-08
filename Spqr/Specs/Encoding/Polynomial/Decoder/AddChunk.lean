/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::{Decoder for Option<T>}::add_chunk`

The `Decoder` trait is canonically lifted to `Option<T>` whenever `T : Decoder`.  In Rust the
method `add_chunk` on `Option<T>` operates on a `&mut Option<T>` and is only legitimate when the
option is `Some`; under that precondition it transparently delegates to `T::add_chunk` on the
inner value, absorbs the supplied `Chunk` into it, and leaves the option in the `Some` state.

To enable formal verification with hax — which disallows mutable references that escape a function
body via APIs such as `Option::take` — the extracted Lean version reifies the borrow as a chain
of ordinary functional steps:

  1. `core.option.Option.take self` — pure decomposition `self ↦ (self, none)`, returning the
     "extracted" inner option together with a `none` placeholder.
  2. `core.option.Option.unwrap o` — partial projection out of `Option T`, succeeding iff
     `o.isSome` (i.e. `self.isSome`).
  3. `DecoderInst.add_chunk tmp chunk` — delegation to the underlying `Decoder T` instance on
     the unwrapped state, absorbing `chunk` into it.
  4. `ok (some tmp1)` — re-injection of the updated inner state back into the `Some` branch.

The composition is a *pure structural lift*: the spec of the outer `add_chunk` carries no extra
mathematical content beyond that of `DecoderInst.add_chunk`; the `Option` layer merely repackages
the input and threads the output verbatim through the `Some` constructor.

**Source**: spqr/src/encoding.rs (lines 84:4-91:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.core.option.Option.Insts.SpqrEncodingDecoder

/-- **Spec theorem for `core.option.Option.Insts.SpqrEncodingDecoder.add_chunk` (generic
lifting)**:

The `Option<T>`-level `add_chunk` is a transparent lift of `DecoderInst.add_chunk` along the
`Some` constructor.  Concretely: given that `self = some tmp` and that the underlying
`DecoderInst.add_chunk tmp chunk` is specified by some postcondition `Q : T → Prop`, the
`Option`-level call satisfies the lifted postcondition
  `Q' self'  ≜  ∃ tmp', self' = some tmp' ∧ Q tmp'`.

The proof composes:
  1. `core.option.Option.take` — pure decomposition `(self, _) := (self, none)`.
  2. `core.option.Option.unwrap.spec` — succeeds because `self.isSome`, producing `tmp` with
     `self = some tmp`.
  3. `DecoderInst.add_chunk tmp chunk` — opaque inner call returning the updated state `tmp1`.
  4. `ok (some tmp1)` — repackaging into the `Some` branch.

No extra hypothesis on `DecoderInst` is required beyond the precondition `self.isSome` imposed
by the Rust `#[hax_lib::requires(self.is_some())]` annotation.

**Source**: spqr/src/encoding.rs (lines 84:4-91:5)
-/
theorem add_chunk_spec_generic
    {T : Type} (DecoderInst : encoding.Decoder T) (self : Option T)
    (chunk : encoding.Chunk)
    (h_some : self.isSome)
    (Q : T → Prop)
    (h_inner : ∀ tmp, self = some tmp →
        DecoderInst.add_chunk tmp chunk ⦃ (tmp1 : T) => Q tmp1 ⦄) :
    add_chunk DecoderInst self chunk ⦃ (self' : Option T) =>
      ∃ tmp', self' = some tmp' ∧ Q tmp' ⦄ := by
  unfold add_chunk
  simp only [Aeneas.Std.core.option.Option.take]
  step with Aeneas.Std.core.option.Option.unwrap.spec
  have h_post := h_inner
  step with h_post
  grind

/--
Specialised to the trivial postcondition `Q ≡ True`, the generic lifting theorem certifies that
`add_chunk` on a `some`-shaped `Option<T>` is total (no panic / no error): it always reduces to
`ok (some tmp1)` for some `tmp1 : T`, provided the inner `DecoderInst.add_chunk` is itself total
on the unwrapped value.

This is the `Option`-level analogue of the structural fact that the `Decoder` trait is preserved
under the `Some` injection `T ↪ Option T`, lifting the inner decoder's totality verbatim.  In
particular, the output is always in the `Some` branch — the `Option` layer never destroys the
`is_some` invariant established at entry.
-/
@[step]
theorem add_chunk_spec
    {T : Type} (DecoderInst : encoding.Decoder T) (self : Option T)
    (chunk : encoding.Chunk)
    (h_some : self.isSome)
    (h_inner_total : ∀ tmp, self = some tmp →
        DecoderInst.add_chunk tmp chunk ⦃ (_ : T) => True ⦄) :
    add_chunk DecoderInst self chunk ⦃ (self' : Option T) => self'.isSome ⦄ := by
  have h := add_chunk_spec_generic DecoderInst self chunk h_some
    (fun _ => True) h_inner_total
  apply WP.spec_mono h
  intro self' ⟨tmp', h_eq, _⟩
  simp [h_eq]

end spqr.core.option.Option.Insts.SpqrEncodingDecoder
