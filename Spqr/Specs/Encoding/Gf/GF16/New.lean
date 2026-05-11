/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
/-! # Spec theorem for `spqr::encoding::gf::GF16::new`

In GF(2¹⁶) — the Galois field with 65 536 elements — every element
is represented internally by a 16-bit unsigned integer.  The `new`
function is the trivial wrapper that takes a `u16` value and packages
it as a `GF16`:
  `new value = ok (GF16 { value })`

The constructor is unconditional and pure — it never fails and
performs no arithmetic on its input.  Conceptually, it implements
the canonical bijection between the raw representation `u16` and
the abstract type `GF16`, and so its semantic interpretation in
`GF216 = GaloisField 2 16` is exactly the lift of the input `u16`
under the canonical map
`Nat.toGF216 = φ ∘ natToGF2Poly` (with
`φ : GF2Poly →+* GF216`).

**Source**: spqr/src/encoding/gf.rs (lines 544:4-546:5)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16

/-- **Spec theorem for `encoding.gf.GF16.new`**:

• The function always succeeds: `new value = ok (GF16 { value })`.
• The underlying `u16` value of the wrapped `GF16` is `value`, and
  equivalently as a natural number it is `value.val`.
• Lifting `value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the GF(2¹⁶) element
  represented by the raw input `value`:
    `(value.val.toGF216 : GF216) = value.val.toGF216`.
  In Hoare-triple form, calling `new value` produces a `GF16`
  `result` whose lift agrees with that of the raw input:
    `new value ⦃ result =>
        (result.value.val.toGF216 : GF216) = value.val.toGF216 ⦄`.

**`new value` reduces to `ok (GF16 { value })`**: the constructor
is the trivial monadic wrapper around the underlying `u16`. -/
@[simp]
theorem new_eq (value : Std.U16) :
    new value = ok ({ value } : GF16) := by
  simp [new]

@[simp]
theorem mk_value_toGF216 (value : Std.U16) :
    (({ value } : GF16).value.val.toGF216 : GF216)
      = value.val.toGF216 := by
  rfl

@[step]
theorem new_spec (value : U16) :
    new value ⦃ (result : GF16) =>
      (GF16toGF216 result : GF216) = value.val.toGF216 ⦄ := by
  simp [GF16toGF216, new]

end spqr.encoding.gf.GF16
