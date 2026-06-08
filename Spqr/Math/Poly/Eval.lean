/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Basic.Zero
import Spqr.Math.Poly.Coeff.Basic

/-!
# Polynomial evaluation bridge

## Main definitions

* `Poly.evalAt` — evaluate the mathematical interpretation of a `Poly` at a `GF16` point.

## Main statements

* `Poly.evalAt_zero_poly` — empty coefficient vector ⇒ evaluation is zero.
* `listToGF216Poly_eval` — `Polynomial.eval` of `listToGF216Poly` as a coefficient sum.
-/

open Polynomial
open spqr.encoding.gf

namespace spqr.encoding.polynomial

/-- Evaluate the mathematical interpretation of a `Poly` at a `GF16` point. -/
noncomputable def Poly.evalAt (p : Poly) (x : GF16) : GF216 :=
  (p.toGF216Poly).eval (x.toGF216)

/-- Evaluating the zero polynomial at any point gives `0 : GF216`. -/
lemma Poly.evalAt_zero_poly (p : Poly) (x : GF16)
    (h : p.coefficients.length = 0) :
    p.evalAt x = 0 := by
  unfold Poly.evalAt
  rw [Poly.toGF216Poly_eq_zero p h]
  simp

/--
Evaluation of `listToGF216Poly` equals the coefficient sum.

This is the key linking lemma for verifying `Poly.compute_at`.
-/
lemma listToGF216Poly_eval (cs : List spqr.encoding.gf.GF16) (a : GF216) :
    (listToGF216Poly cs).eval a =
      ∑ i : Fin cs.length,
        (cs.get i).toGF216 * a ^ i.val := by
  unfold listToGF216Poly
  simp [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]

end spqr.encoding.polynomial
