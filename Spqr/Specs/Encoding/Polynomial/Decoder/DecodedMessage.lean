/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::{Decoder for Option<T>}::decoded_message`

The `Decoder` trait is canonically lifted to `Option<T>` whenever `T : Decoder`.  In Rust the
method `decoded_message` on `Option<T>` operates on a `&Option<T>` and is only legitimate when the
option is `Some`; under that precondition it transparently delegates to `T::decoded_message` on
the inner value, returning the resulting `Option<Vec<u8>>` verbatim.

To enable formal verification with hax — which disallows shared references that escape a function
body via APIs such as `Option::as_ref` — the extracted Lean version reifies the borrow as a pair
of ordinary functional steps:

  1. `core.option.Option.as_ref self` — pure shared projection `self ↦ self`, returning the
     "borrowed" inner option (semantically the identity in the absence of mutability).
  2. `core.option.Option.unwrap o` — partial projection out of `Option T`, succeeding iff
     `o.isSome` (i.e. `self.isSome`).
  3. `DecoderInst.decoded_message value` — delegation to the underlying `Decoder T` instance on
     the unwrapped state, returning an `Option (Vec U8)`.

The composition is a *pure structural lift*: the spec of the outer `decoded_message` carries no
extra mathematical content beyond that of `DecoderInst.decoded_message`; the `Option` layer
merely repackages the input and threads the output verbatim.

**Source**: spqr/src/encoding.rs (lines 94:4-100:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.core.option.Option.Insts.SpqrEncodingDecoder

/-- **Spec theorem for `core.option.Option.Insts.SpqrEncodingDecoder.decoded_message` (generic
lifting)**:

The `Option<T>`-level `decoded_message` is a transparent lift of `DecoderInst.decoded_message`
along the `Some` constructor.  Concretely: given that `self = some value` and that the underlying
`DecoderInst.decoded_message value` is specified by some postcondition
`Q : Option (alloc.vec.Vec Std.U8) → Prop`, the `Option`-level call satisfies the *very same*
postcondition `Q`.

The proof composes:
  1. `core.option.Option.as_ref` — pure shared projection, modelled by the semantic equation
     `core.option.Option.as_ref self = ok self` carried by the hypothesis `h_as_ref`.
  2. `core.option.Option.unwrap.spec` — succeeds because `self.isSome`, producing `value` with
     `self = some value`.
  3. `DecoderInst.decoded_message value` — opaque inner call returning an `Option (Vec U8)`.

No extra hypothesis on `DecoderInst` is required beyond the precondition `self.isSome` imposed by
the Rust `#[hax_lib::requires(self.is_some())]` annotation, together with the structural
"as_ref-is-identity" equation `h_as_ref`.

**Source**: spqr/src/encoding.rs (lines 94:4-100:5)
-/
theorem decoded_message_spec_generic
    {T : Type} (DecoderInst : encoding.Decoder T) (self : Option T)
    (h_some : self.isSome)
    (h_as_ref : core.option.Option.as_ref self = ok self)
    (Q : Option (alloc.vec.Vec Std.U8) → Prop)
    (h_inner : ∀ value, self = some value →
        DecoderInst.decoded_message value ⦃ (r : Option (alloc.vec.Vec Std.U8)) => Q r ⦄) :
    decoded_message DecoderInst self ⦃ (result : Option (alloc.vec.Vec Std.U8)) => Q result ⦄ := by
  unfold decoded_message
  rw [h_as_ref]
  simp only [bind_tc_ok]
  step with Aeneas.Std.core.option.Option.unwrap.spec
  step
  grind

/--
Specialised to the trivial postcondition `Q ≡ True`, the generic lifting theorem certifies that
`decoded_message` on a `some`-shaped `Option<T>` is total (no panic / no error): it always
reduces to `ok result` for some `result : Option (Vec U8)`, provided the inner
`DecoderInst.decoded_message` is itself total on the unwrapped value.

This is the `Option`-level analogue of the structural fact that the `Decoder` trait is preserved
under the `Some` injection `T ↪ Option T`, lifting the inner decoder's totality verbatim.
-/
@[step]
theorem decoded_message_spec
    {T : Type} (DecoderInst : encoding.Decoder T) (self : Option T)
    (h_some : self.isSome)
    (h_as_ref : core.option.Option.as_ref self = ok self)
    (h_inner_total : ∀ value, self = some value →
        DecoderInst.decoded_message value ⦃ (_ : Option (alloc.vec.Vec Std.U8)) => True ⦄) :
    decoded_message DecoderInst self ⦃ (_ : Option (alloc.vec.Vec Std.U8)) => True ⦄ := by
  exact decoded_message_spec_generic DecoderInst self h_some h_as_ref
    (fun _ => True) h_inner_total

end spqr.core.option.Option.Insts.SpqrEncodingDecoder
