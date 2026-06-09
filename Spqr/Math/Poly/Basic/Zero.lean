/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Basic.Defs

/-!
# Zero-polynomial characterization

The empty coefficient list maps to the zero polynomial under `listToGF216Poly`. As a
consequence, a `Poly` with empty coefficient vector represents `0 : GF216[X]`.

## Main statements

* `listToGF216Poly_nil` — `listToGF216Poly [] = 0`.
* `Poly.toGF216Poly_eq_zero` — empty coefficient vector ⇒ zero polynomial.
* `listToGF216Poly_empty` — `simp`-normal form of `listToGF216Poly_nil`.
-/

open Polynomial
open spqr.math.gf spqr.encoding.gf

namespace spqr.encoding.polynomial

/-! ## Zero polynomial characterization -/

/--
The empty coefficient list produces the zero polynomial.

`listToGF216Poly [] = 0` because `Fin 0` is empty, so the sum over `Fin [].length` yields the
additive identity.
-/
lemma listToGF216Poly_nil :
    listToGF216Poly [] = 0 := by
  simp [listToGF216Poly]

/--
A `Poly` with an empty coefficient vector represents the zero polynomial in `GF(2¹⁶)[X]`.
-/
theorem Poly.toGF216Poly_eq_zero (p : Poly)
    (h : p.coefficients.length = 0) :
    p.toGF216Poly = 0 := by
  unfold Poly.toGF216Poly
  have hnil : p.coefficients.val = [] :=
    List.eq_nil_of_length_eq_zero h
  rw [hnil]
  exact listToGF216Poly_nil

/-- `listToGF216Poly [] = 0` (simp-normal form). -/
@[simp]
lemma listToGF216Poly_empty :
    listToGF216Poly ([] : List spqr.encoding.gf.GF16) = 0 :=
  listToGF216Poly_nil

/-! ## Replicate-zero polynomial -/

/-- A `List` of `n` copies of `GF16.ZERO` represents the zero polynomial in `GF216[X]`.
Since `GF16.ZERO.toGF216 = 0`, every term `C (cs[i].toGF216) * X ^ i` vanishes. -/
theorem listToGF216Poly_replicate_ZERO (n : Nat) :
    listToGF216Poly (List.replicate n GF16.ZERO) = 0 := by
  simp only [listToGF216Poly]
  apply Finset.sum_eq_zero
  intro i _
  simp only [List.get_eq_getElem, List.getElem_replicate, GF16.ZERO]
  simp [GF16.toGF216, Nat.toGF216, natToBinaryPoly_zero, map_zero]

end spqr.encoding.polynomial
