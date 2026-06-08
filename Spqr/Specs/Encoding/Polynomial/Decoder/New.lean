/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::{Decoder for Option<T>}::new`

The `Decoder` trait is canonically lifted to `Option<T>` whenever `T : Decoder`.  In Rust the
associated constructor `new` on `Option<T>` is defined by the one-line desugaring
`Ok(Some(T::new(len_bytes)?))`: it delegates the construction to the inner decoder and, on
success, wraps the resulting state in the `Some` constructor; on failure the `?` operator
propagates the `EncodingError` unchanged.

After hax extraction this `?`-elaborated body becomes the following pure functional pipeline:

  1. `DecoderInst.new len_bytes` — delegation to the inner `Decoder T` instance, producing a
     `core::result::Result T EncodingError`.
  2. `core.result.Result.Insts.CoreOpsTry_traitTry.branch r` — splits the inner `Result` into a
     `ControlFlow`: `Continue val` on `Ok val`, `Break residual` on `Err _`.
  3. Pattern match on the `ControlFlow`:
       • `Continue val ↦ ok (Ok (some val))` — re-injection into the `Some` branch of `Option T`.
       • `Break residual ↦ from_residual …` — identity transport of the residual error along
         the canonical `FromSame EncodingError` instance.

The composition is a *pure structural lift* along the functor `Some : T ↪ Option T`: the
specification of the outer `new` carries no mathematical content beyond that of the inner
`DecoderInst.new`; the `Option` layer merely repackages the success branch with the `Some`
constructor and threads the error branch through verbatim.

**Source**: spqr/src/encoding.rs (lines 76:4-81:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.core.option.Option.Insts.SpqrEncodingDecoder

/-- **Spec theorem for `core.option.Option.Insts.SpqrEncodingDecoder.new` (generic
lifting)**:

The `Option<T>`-level `new` is a transparent lift of `DecoderInst.new` along the `Some`
constructor, propagating errors unchanged.  Concretely, given an inner postcondition
`Q : T → Prop` describing the success value produced by `DecoderInst.new len_bytes`, the
`Option`-level call satisfies the lifted postcondition

  `Q' (result : Result (Option T) EncodingError)  ≜
      (∃ val, result = Ok (some val) ∧ Q val) ∨ (∃ e, result = Err e)`.

The proof composes:
  1. `DecoderInst.new len_bytes` — opaque inner call returning either `Ok val` or `Err e`.
  2. `core.result.Result.Insts.CoreOpsTry_traitTry.branch` — pure decomposition of the inner
     `Result` into a `ControlFlow`, succeeding total.
  3. Case analysis on the `ControlFlow`:
       • `Continue val` — repackage as `Ok (some val)`.
       • `Break residual` — propagate the residual error verbatim via `from_residual`.

No extra hypothesis on `DecoderInst` is required beyond the precondition `True` imposed by the
Rust `#[hax_lib::requires(true)]` annotation (in fact `new` carries no `requires` clause at all).

**Source**: spqr/src/encoding.rs (lines 76:4-81:5)
-/
theorem new_spec_generic
    {T : Type} (DecoderInst : encoding.Decoder T) (len_bytes : Std.Usize)
    (Q : T → Prop)
    (h_inner :
        DecoderInst.new len_bytes ⦃ (r : core.result.Result T encoding.EncodingError) =>
          (∀ val, r = core.result.Result.Ok val → Q val) ⦄) :
    new DecoderInst len_bytes ⦃
        (result : core.result.Result (Option T) encoding.EncodingError) =>
      (∃ val, result = core.result.Result.Ok (some val) ∧ Q val) ∨
      (∃ e, result = core.result.Result.Err e) ⦄ := by
  unfold new
  step with h_inner
  cases r with
  | Ok val =>
    simp only [bind_tc_ok, WP.spec_ok]
    exact Or.inl ⟨val, rfl, r_post val rfl⟩
  | Err e =>
    simp only [bind_tc_ok,
      _root_.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual_err_spec,
      core.convert.FromSame.from_, WP.spec_ok]
    exact Or.inr ⟨e, rfl⟩


/--
Specialised to the trivial postcondition `Q ≡ True`, the generic lifting theorem certifies that
`new` on `Option<T>` is total (no panic / no error from the lift layer itself): it always
reduces either to `ok (Ok (some val))` for some `val : T` produced by the inner decoder, or to
`ok (Err e)` for some `e : EncodingError` propagated unchanged from the inner decoder, provided
the inner `DecoderInst.new` is itself total on `len_bytes`.

This is the `Option`-level analogue of the structural fact that the `Decoder` trait is preserved
under the `Some` injection `T ↪ Option T`, lifting the inner decoder's totality verbatim along
the functor `Some` and the canonical `FromSame EncodingError` error-transport instance.
-/
@[step]
theorem new_spec
    {T : Type} (DecoderInst : encoding.Decoder T) (len_bytes : Std.Usize)
    (h_inner_total :
        DecoderInst.new len_bytes ⦃ (_ : core.result.Result T encoding.EncodingError) =>
          True ⦄) :
    new DecoderInst len_bytes ⦃
        (result : core.result.Result (Option T) encoding.EncodingError) =>
      (∃ val, result = core.result.Result.Ok (some val)) ∨
      (∃ e, result = core.result.Result.Err e) ⦄ := by
  have h := new_spec_generic DecoderInst len_bytes (fun _ => True)
    (by
      apply WP.spec_mono h_inner_total
      intro _ _ _ _
      trivial)
  apply WP.spec_mono h
  intro result h_post
  rcases h_post with ⟨val, h_eq, _⟩ | ⟨e, h_eq⟩
  · left; exact ⟨val, h_eq⟩
  · right; exact ⟨e, h_eq⟩

end spqr.core.option.Option.Insts.SpqrEncodingDecoder
