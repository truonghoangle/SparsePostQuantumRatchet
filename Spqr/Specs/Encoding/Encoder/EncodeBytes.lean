/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytes

<<<<<<< HEAD
/-!
# Spec theorems for `spqr::encoding::{Encoder for Option<T>}::encode_bytes`

Whenever `T : Encoder`, the `Encoder` trait also applies to `Option<T>`. In Rust the definition
is a single line, `Ok(Some(T::encode_bytes(msg)?))`: it hands the encoding to the inner encoder
and, on success, wraps the result in `Some`; on failure the `?` operator passes the
`EncodingError` straight through.

After hax extraction this `?`-desugared body becomes a simple pipeline:

  1. `EncoderInst.encode_bytes msg` — run the inner `Encoder T` instance, yielding a
     `core::result::Result T EncodingError`.
  2. `core.result.Result.Insts.CoreOpsTry.branch r` — convert the inner `Result` into a
     `ControlFlow`: `Continue val` for `Ok val`, `Break residual` for `Err _`.
  3. Match on the `ControlFlow`:
       • `Continue val ↦ ok (Ok (some val))` — wrap the value in `Some`.
       • `Break residual ↦ from_residual …` — forward the error unchanged via the
         `FromSame EncodingError` instance.

In other words the outer `encode_bytes` is just a structural wrapper around the inner one: it
adds no mathematical content, only tagging successes with `Some` and passing errors through
untouched.

This file proves two theorems built on that observation:

  • `encode_bytes_spec_lift` — transports an arbitrary postcondition of the inner encoder
    through the `Option<T>` wrapper.
  • `encode_bytes_spec_poly_encoder` — the `T = PolyEncoder` instance, obtained from the lift
    plus the round-robin postcondition of
    `PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes_spec`.

**Source**: spqr/src/encoding.rs (lines 55:4-60:5)
-/
=======
/-! # Spec theorems for `spqr::encoding::{Encoder for Option<T>}::encode_bytes`

The `Option<T>` encoder wraps the inner `T` encoder: successes are tagged with `Some`, errors
pass through unchanged.

Two theorems:
  • `encode_bytes_spec_lift` — lifts any postcondition of the inner encoder through the wrapper.
  • `encode_bytes_spec_poly_encoder` — instantiates the lift for `T = PolyEncoder`.

**Source**: spqr/src/encoding.rs -/
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5

open Aeneas Aeneas.Std Result spqr encoding.polynomial

namespace spqr.core.option.Option.Insts.SpqrEncodingEncoder

/-- **Predicate-lifting spec for `Option<T>::encode_bytes`**:

<<<<<<< HEAD
Given an `Encoder T` instance `EncoderInst`, a message `msg`, and a predicate `P` on the inner
result, the hypothesis `h_inner` states that `EncoderInst.encode_bytes msg` satisfies `P`. The
theorem concludes that `encode_bytes EncoderInst msg` satisfies the postcondition obtained by
pushing `P` through the `Option<T>` wrapper:

  • `Ok (some val)` ↦ `P (Ok val)`  — the inner success value, retagged with `Some`.
  • `Err e`         ↦ `P (Err e)`  — the inner error, forwarded unchanged.
  • otherwise (`Ok none`) ↦ `False` — unreachable.

Since the `Option` layer only relabels the branches, whatever `P` holds for the inner encoder
holds for the wrapped one. This is the reusable building block behind
`encode_bytes_spec_poly_encoder`.

**Source**: spqr/src/encoding.rs (lines 55:4-60:5)
-/
=======
If the inner encoder satisfies `P`, then the wrapped encoder satisfies `P` relabelled through
`Option`: `Ok (some val) ↦ P (Ok val)`, `Err e ↦ P (Err e)`, `Ok none ↦ False`. -/
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
@[step]
theorem encode_bytes_spec_lift
    {T : Type} (EncoderInst : encoding.Encoder T) (msg : Slice Std.U8)
    (P : core.result.Result T encoding.EncodingError → Prop)
    (h_inner :
        EncoderInst.encode_bytes msg ⦃ (r : core.result.Result T encoding.EncodingError) =>
          P r ⦄) :
    encode_bytes EncoderInst msg ⦃
        (result : core.result.Result (Option T) encoding.EncodingError) =>
      match result with
      | core.result.Result.Ok (some val) => P (core.result.Result.Ok val)
      | core.result.Result.Err e => P (core.result.Result.Err e)
      | _ => False ⦄ := by
  unfold encode_bytes
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

/-- **`encode_bytes` spec for `Option<PolyEncoder>`**:

<<<<<<< HEAD
Under the hypotheses `h_even` (`msg.length` is even) and `h_len` (`msg.length ≤ 2^16 * 16`),
`encode_bytes PolyEncoder.Insts.SpqrEncodingEncoder msg` succeeds and its result matches the
`Ok (some ⟨idx, Points pts⟩)` branch — no other branch (`Err`, `Ok none`, or a non-`Points`
state) is reachable — with:

  • `idx = 0#u32` — the encoder index.
  • For every `j < 16`, `pts[j]!.value.length` equals `msg.length / 2 / 16`, plus one extra
    coefficient when `j < (msg.length / 2) % 16` (the round-robin remainder).
  • For every `j < 16` and every in-range coefficient index `k`, the byte pair at round-robin
    positions `2·(j + 16·k)` and `2·(j + 16·k) + 1` lies within `msg`, and coefficient `k` of
    `pts[j]` is their big-endian combination `256 * b_hi + b_lo` mapped into `GF(2^16)`.

Proved by feeding `PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes_spec` (the inner
`PolyEncoder` postcondition) into `encode_bytes_spec_lift`.

**Source**: spqr/src/encoding.rs (lines 55:4-60:5)
-/
=======
Instantiates `encode_bytes_spec_lift` with the `PolyEncoder` postcondition. Given `h_even` and
`h_len`, the result is `Ok (some ⟨0#u32, Points pts⟩)` where each `pts[j]` has the expected
round-robin length and coefficients matching big-endian byte pairs from `msg`. -/
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
@[step]
theorem encode_bytes_spec_poly_encoder
    (msg : Slice U8)
    (h_even : msg.length % 2 = 0)
    (h_len : msg.length ≤ 2 ^ 16 * 16) :
    encode_bytes PolyEncoder.Insts.SpqrEncodingEncoder msg ⦃
        (result : core.result.Result (Option PolyEncoder) encoding.EncodingError) =>
      match result with
      | core.result.Result.Ok (some ⟨idx, EncoderState.Points pts⟩) =>
        idx = 0#u32 ∧
        (∀ (j : Nat), j < 16 →
          pts[j]!.value.length =
            if j < (msg.length / 2) % 16
            then msg.length / 2 / 16 + 1
            else msg.length / 2 / 16) ∧
        (∀ (j : Nat), j < 16 →
          ∀ (k : Nat), k < pts[j]!.value.length →
            2 * (j + 16 * k) + 1 < msg.length ∧
            (listToGF216Poly pts[j]!.value).coeff k =
              (256 * msg[2 * (j + 16 * k)]! + (msg[2 * (j + 16 * k) + 1]!).val).toGF216)
      | _ => False ⦄ := by
  have h_inner := PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes_spec msg h_even h_len
  unfold encode_bytes
  step with h_inner
  cases r with
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, WP.spec_ok]
    obtain ⟨idx, s⟩ := val
    cases s <;> assumption
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, WP.spec_ok]
    assumption

end spqr.core.option.Option.Insts.SpqrEncodingEncoder
