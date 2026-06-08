/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Coeff.Basic

/-!
# `GF16.toGF216` at distinguished values, and the `getElem!`/`coeff` bridge

## Main statements

* `GF16.toGF216_zero_val` — `g.value.val = 0 → g.toGF216 = 0`.
* `GF16.toGF216_one_val` — `g.value.val = 1 → g.toGF216 = 1`.
* `getElem_bang_toGF216_eq_coeff` — bridge between `cs[j]!.toGF216` and the polynomial
  coefficient.
-/

open Polynomial
open spqr.math.gf spqr.encoding.gf

namespace spqr.encoding.gf

/-! ## `GF16.toGF216` at 0 and 1 -/

/-- `GF16.toGF216` maps the zero GF16 element to `0 : GF216`. -/
lemma GF16.toGF216_zero_val (g : spqr.encoding.gf.GF16) (h : g.value.val = 0) :
    g.toGF216 = 0 := by
  unfold GF16.toGF216 Nat.toGF216
  rw [h]
  simp [natToBinaryPoly_zero, map_zero]

/-- `GF16.toGF216` preserves the one element. -/
lemma GF16.toGF216_one_val (g : spqr.encoding.gf.GF16) (h : g.value.val = 1) :
    g.toGF216 = 1 := by
  unfold GF16.toGF216 Nat.toGF216
  rw [h]
  simp [natToBinaryPoly_one, map_one]

end spqr.encoding.gf

namespace spqr.encoding.polynomial

/-! ## Bridge between `getElem!` and coefficients -/

/--
Bridge: `getElem!` with `toGF216` equals `listToGF216Poly` coefficient.

Connects the Lean list indexing `cs[j]!.toGF216` to the mathematical coefficient
`(listToGF216Poly cs).coeff j`, handling the out-of-bounds case.
-/
lemma getElem_bang_toGF216_eq_coeff
    (cs : List GF16) (j : Nat) :
    (cs[j]!).toGF216 = (listToGF216Poly cs).coeff j := by
  rw [listToGF216Poly_coeff]
  by_cases hj : j < cs.length
  · rw [dif_pos hj, List.get_eq_getElem]
    grind
  · rw [dif_neg hj]
    have : (cs[j]! : spqr.encoding.gf.GF16) = default := by
      grind
    rw [this]; exact GF16.toGF216_zero_val _ (by rfl)

end spqr.encoding.polynomial
