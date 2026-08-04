/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New

/-!
# Spec theorems for `spqr::encoding::{Decoder for Option<T>}::new`

Whenever `T : Decoder`, the `Decoder` trait also applies to `Option<T>`. In Rust the definition
is a single line, `Ok(Some(T::new(len_bytes)?))`: it hands the construction to the inner decoder
and, on success, wraps the result in `Some`; on failure the `?` operator passes the
`EncodingError` straight through.

After hax extraction this `?`-desugared body becomes a simple pipeline:

  1. `DecoderInst.new len_bytes` — run the inner `Decoder T` instance, yielding a
     `core::result::Result T EncodingError`.
  2. `core.result.Result.Insts.CoreOpsTry.branch r` — convert the inner `Result` into a
     `ControlFlow`: `Continue val` for `Ok val`, `Break residual` for `Err _`.
  3. Match on the `ControlFlow`:
       • `Continue val ↦ ok (Ok (some val))` — wrap the value in `Some`.
       • `Break residual ↦ from_residual …` — forward the error unchanged via the
         `FromSame EncodingError` instance.

In other words the outer `new` is just a structural wrapper around the inner one: it adds no
mathematical content, only tagging successes with `Some` and passing errors through untouched.
This mirrors, on the decoding side, the `Option<T>` lifting already established for the encoder's
`encode_bytes`.

This file proves two theorems built on that observation:

  • `new_spec_lift` — transports an arbitrary postcondition of the inner decoder through the
    `Option<T>` wrapper.
  • `new_spec_poly_decoder` — the `T = PolyDecoder` instance, obtained from the lift plus the
    parity-conditioned postcondition of
    `PolyDecoder.Insts.SpqrEncodingDecoder.new_spec`.

**Source**: spqr/src/encoding.rs (lines 76:4-81:5)
-/

open Aeneas Aeneas.Std Result spqr encoding.polynomial

namespace spqr.core.option.Option.Insts.SpqrEncodingDecoder

/-- **Predicate-lifting spec for `Option<T>::new`**:

Given a `Decoder T` instance `DecoderInst`, a length `len_bytes`, and a predicate `P` on the inner
result, the hypothesis `h_inner` states that `DecoderInst.new len_bytes` satisfies `P`. The
theorem concludes that `new DecoderInst len_bytes` satisfies the postcondition obtained by pushing
`P` through the `Option<T>` wrapper:

  • `Ok (some val)` ↦ `P (Ok val)`  — the inner success value, retagged with `Some`.
  • `Err e`         ↦ `P (Err e)`  — the inner error, forwarded unchanged.
  • otherwise (`Ok none`) ↦ `False` — unreachable.

Since the `Option` layer only relabels the branches, whatever `P` holds for the inner decoder
holds for the wrapped one. This is the reusable building block behind `new_spec_poly_decoder`.

**Source**: spqr/src/encoding.rs (lines 76:4-81:5)
-/
@[step]
theorem new_spec_lift
    {T : Type} (DecoderInst : encoding.Decoder T) (len_bytes : Std.Usize)
    (P : core.result.Result T encoding.EncodingError → Prop)
    (h_inner :
        DecoderInst.new len_bytes ⦃ (r : core.result.Result T encoding.EncodingError) =>
          P r ⦄) :
    new DecoderInst len_bytes ⦃
        (result : core.result.Result (Option T) encoding.EncodingError) =>
      match result with
      | core.result.Result.Ok (some val) => P (core.result.Result.Ok val)
      | core.result.Result.Err e => P (core.result.Result.Err e)
      | _ => False ⦄ := by
  unfold new
  step with h_inner
  cases r with
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, WP.spec_ok]
    assumption
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, WP.spec_ok]
    assumption

/-- **`new` spec for `Option<PolyDecoder>`**:

`new PolyDecoder.Insts.SpqrEncodingDecoder len_bytes` inherits, through the `Option<T>` wrapper,
the parity-conditioned behaviour of the underlying `PolyDecoder` constructor:

  • When `len_bytes.val` is even, the call succeeds in the `Ok (some pd)` branch — no other branch
    (`Err`, `Ok none`) is reachable — with the freshly-built decoder `pd` satisfying:
      - `pd.pts_needed = len_bytes.val / 2` (as a bounded `Usize`),
      - `pd.pts.val = List.replicate 16 default` (16 empty point buckets),
      - `pd.is_complete = false`.
  • When `len_bytes.val` is odd, the error is forwarded verbatim: the result is
    `Err (PolynomialError MessageLengthEven)`.

Proved by feeding `PolyDecoder.Insts.SpqrEncodingDecoder.new_spec` (the inner `PolyDecoder`
postcondition) into `new_spec_lift` and reconciling the lifted branch structure with the parity
split.

**Source**: spqr/src/encoding.rs (lines 76:4-81:5)
-/
@[step]
theorem new_spec_poly_decoder (len_bytes : Std.Usize) :
    new PolyDecoder.Insts.SpqrEncodingDecoder len_bytes ⦃
        (result : core.result.Result (Option PolyDecoder) encoding.EncodingError) =>
      if len_bytes.val % 2 = 0 then
        match result with
        | core.result.Result.Ok (some pd) =>
            pd.pts_needed = ⟨len_bytes.val / 2, by
                have : len_bytes.val / 2 ≤ len_bytes.val := Nat.div_le_self _ _
                exact Nat.lt_of_le_of_lt this len_bytes.hBounds⟩ ∧
            pd.pts.val = List.replicate 16 default ∧
            pd.is_complete = false
        | _ => False
      else
        result = core.result.Result.Err
          (encoding.EncodingError.PolynomialError
            encoding.polynomial.PolynomialError.MessageLengthEven) ⦄ := by
  have h := new_spec_lift PolyDecoder.Insts.SpqrEncodingDecoder len_bytes _
    (PolyDecoder.Insts.SpqrEncodingDecoder.new_spec len_bytes)
  apply WP.spec_mono h
  intro result hpost
  by_cases h_even : len_bytes.val % 2 = 0
  · cases result with
    | Ok o =>
      cases o with
      | none => exact hpost.elim
      | some pd => grind
    | Err e => grind
  · cases result with
    | Ok o =>
      cases o with
      | none => exact hpost.elim
      | some pd => grind
    | Err e => grind

end spqr.core.option.Option.Insts.SpqrEncodingDecoder
