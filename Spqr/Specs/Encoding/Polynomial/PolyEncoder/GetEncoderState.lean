/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::get_encoder_state`

A `PolyEncoder` wraps a chunk index `idx : U32` together with an `EncoderState`, which is either
  • `EncoderState.Points pts` — an array of 16 evaluation-data `Point`s, or
  • `EncoderState.Polys  ps`  — an array of 16 interpolated `Poly`s.

The function `get_encoder_state` is a pure field accessor: it takes a `PolyEncoder` and returns the
`EncoderState` stored in its `s` field, performing no computation and never failing:
  `get_encoder_state self = ok self.s`

**Source**: spqr/src/encoding/polynomial.rs (lines 537:4-539:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.PolyEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.get_encoder_state`**:

`get_encoder_state` is the trivial projection that extracts the `EncoderState` stored in the `s`
field of a `PolyEncoder`.

• The function always succeeds (no panic / no error) for any `PolyEncoder` input.
• The result is propositionally equal to `self.s`:
    `get_encoder_state self = ok self.s`

This is unconditional and pure — no arithmetic, no allocation, no fallibility — so the Hoare-triple
postcondition simply identifies the output with the `s` field of the input.

**Source**: spqr/src/encoding/polynomial.rs (lines 537:4-539:5)
-/
@[simp]
theorem get_encoder_state_eq (self : encoding.polynomial.PolyEncoder) :
    get_encoder_state self = ok self.s := by
  simp [get_encoder_state]

@[step]
theorem get_encoder_state_spec (self : encoding.polynomial.PolyEncoder) :
    get_encoder_state self ⦃ (result : encoding.polynomial.EncoderState) =>
      result = self.s ⦄ := by
  simp [get_encoder_state]

end spqr.encoding.polynomial.PolyEncoder
