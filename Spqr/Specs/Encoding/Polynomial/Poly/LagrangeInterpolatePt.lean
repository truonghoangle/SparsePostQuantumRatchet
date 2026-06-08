/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.Basic.Defs
import Spqr.Math.Poly.Basic.Zero
import Spqr.Math.Poly.Coeff.Basic
import Spqr.Math.Poly.Coeff.ListOps
import Spqr.Math.Poly.CharTwo.Basic
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Math.Poly.Eval
import Spqr.Math.Poly.LinearFactors.Basic
import Spqr.Math.Poly.LinearFactors.Degree
import Spqr.Math.Poly.Lagrange.DenomProd
import Spqr.Math.Poly.Lagrange.BasisPoly
import Spqr.Math.Poly.Lagrange.InterpolantSum
import Spqr.Math.Poly.Horner.Defs
import Spqr.Math.Poly.Horner.Eval
import Spqr.Math.Poly.ExpectedTrailing.Defs
import Spqr.Math.Poly.ExpectedTrailing.Basic
import Spqr.Math.Poly.Identities.Basic
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolatePrepare
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateComplete

/-! # Spec theorem for
`spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::lagrange_interpolate_pt`

Given a slice of evaluation points `pts : &[Pt]` and an index `i < pts.len()`, the Rust function
`Poly::lagrange_interpolate_pt` (in `src/encoding/polynomial.rs`, lines 231:4-236:5) returns the
i-th scaled Lagrange basis polynomial over GF(2¹⁶): the unique polynomial of degree
`< pts.len() − 1` that, together with the contributions from all other points, sums to the Lagrange
interpolant of the point set.

Concretely the Aeneas-extracted Lean function
`encoding.polynomial.Poly.lagrange_interpolate_pt` proceeds as follows:

1. **Prepare template**: compute
     `template = ∏_{j=0}^{pts.len()−1} (X − pts[j].x)`
   via `Poly::lagrange_interpolate_prepare` (see `LagrangeInterpolatePrepare`).
   The result has `coefficients.len() = pts.len() + 1` and a leading `GF16::ONE`.

2. **Complete for point `i`**: call
     `template.lagrange_interpolate_complete(pts, i)`
   to obtain `result1` satisfying the algebraic identity
     `result1 · (X − pts[i].x) =
          X · lagrangeScale(pts[i], pts) · template`
   in `GF216[X]` (see `LagrangeInterpolateComplete`).
   The output `result1` has `coefficients.len() = pts.len() + 1`.
   Due to the synthetic long-division with simultaneous scaling performed
   by `lagrange_interpolate_complete`, the result polynomial `result1` is
   effectively the quotient `template / (X − pts[i].x)` scaled by
   `lagrangeScale(pts[i], pts)` and multiplied by `X` (the "X-artifact"
   arising from the in-place Horner-style division on the little-endian
   coefficient vector).  As a consequence, `result1.coefficients[0]` is
   zero.

3. **Remove leading zero**: `result.coefficients.remove(0)` strips the
   zero constant-term coefficient (the X-artifact), producing a polynomial
   with `coefficients.len() = pts.len()`.  This effectively divides the
   polynomial by `X`, yielding the final result.

The net effect is to produce a polynomial `result` such that:

  `result(X) · (X − pts[i].x) =
       C(lagrangeScaleGF216(pts[i], pts)) ·
         ∏_{j=0}^{n−1} (X − pts[j].x)`

in `GF216[X]`.  Since `∏_{j=0}^{n−1} (X − pts[j].x) = (X − pts[i].x) · lagrangeBasisPoly pts i`
(the product factors through the i-th linear factor), cancelling `(X − pts[i].x)` in the integral
domain `GF216[X]` yields:

  `result.toGF216Poly = C(lagrangeScaleGF216(pts[i], pts)) · lagrangeBasisPoly pts i`

where `lagrangeBasisPoly pts i = ∏_{j ≠ i} (X − pts[j].x)`.  This is exactly the i-th term in the
classical Lagrange interpolation formula.

Unfolding the definition of `lagrangeScaleGF216`, the full expression is:

  `result(X) = pᵢ.y · (∏_{j ≠ i} (pᵢ.x − pⱼ.x))^(2¹⁶ − 2) · ∏_{j ≠ i} (X − pⱼ.x)`

which in the case of pairwise distinct x-coordinates (so the denominator product is nonzero) equals:

  `result(X) = pᵢ.y / (∏_{j ≠ i} (pᵢ.x − pⱼ.x)) · ∏_{j ≠ i} (X − pⱼ.x)`

the i-th Lagrange basis polynomial scaled to pass through `(pᵢ.x, pᵢ.y)`.

**Source**: spqr/src/encoding/polynomial.rs (lines 231:4-236:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly
open spqr.encoding.polynomial

namespace spqr.encoding.polynomial.Poly

@[step]
private axiom vec_remove_zero_spec
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (h : 0 < v.val.length) :
    alloc.vec.Vec.remove Global v 0#usize
      ⦃ (result : GF16 × alloc.vec.Vec GF16) =>
        result.2.val = v.val.drop 1 ⦄

/--
**Spec theorem for `spqr.encoding.polynomial.Poly.lagrange_interpolate_pt`**:

Given a slice of points `pts` with `pts.len() + 1 ≤ Usize.max` and a valid index `i < pts.len()`,
the function returns a polynomial `result : Poly` satisfying:

• The function always succeeds (no panic) under the stated preconditions, since
  `lagrange_interpolate_prepare`, `lagrange_interpolate_complete`,
  and `Vec::remove(0)` are all total under these assumptions.

• **Length of the result**:
    `result.coefficients.val.length = pts.val.length`.
  The template polynomial from `lagrange_interpolate_prepare` has `pts.len() + 1` coefficients;
  `lagrange_interpolate_complete` preserves this length; and `remove(0)` reduces it by one.

• **Polynomial identity**:
    `result.toGF216Poly *
       (X − C(GF16.toGF216(pts[i].x))) =
         C(lagrangeScaleGF216(pts[i], pts)) ·
           prodLinearFactors pts.val 0 pts.val.length`
  in `GF216[X]`.  This identity says that `result(X)` times the linear factor `(X − pts[i].x)`
  equals the scaled product of all linear factors.

  Since `prodLinearFactors pts 0 n = (X − pts[i].x) · lagrangeBasisPoly pts i` (see
  `prodLinearFactors_eq_factor_mul_basis` in `LagrangeInterpolate.lean`), cancelling the common
  factor
  `(X − pts[i].x)` in the integral domain `GF216[X]` gives the cleaner form:
    `result.toGF216Poly =
         C(lagrangeScaleGF216(pts[i], pts)) · lagrangeBasisPoly pts i`
  where `lagrangeBasisPoly pts i = ∏_{j ≠ i} (X − pts[j].x)`.

**Source**: spqr/src/encoding/polynomial.rs (lines 231:4-236:5)
-/
@[step]
theorem lagrange_interpolate_pt_spec
    (pts : Slice Pt)
    (i : Std.Usize)
    (hi : i.val < pts.val.length)
    (h_len : pts.val.length + 1 ≤ Std.Usize.max) :
    lagrange_interpolate_pt pts i ⦃ (result : Poly) =>
      result.coefficients.val.length = pts.val.length ∧
      result.toGF216Poly *
        (X - C (GF16.toGF216
          (pts.val.get ⟨i.val, hi⟩).x)) =
        C (lagrangeScaleGF216
          (pts.val.get ⟨i.val, hi⟩) pts.val) *
          prodLinearFactors pts.val 0 pts.val.length ⦄ := by
  unfold lagrange_interpolate_pt
  step with lagrange_interpolate_prepare_spec pts h_len as
    ⟨template, h_template_len, _, _, _, h_template_eq⟩
  have h_template_pos : 0 < template.coefficients.val.length := by
    rw [h_template_len]; omega
  have h_root_template :
      template.evalAt (pts.val.get ⟨i.val, hi⟩).x = 0 := by
    unfold Poly.evalAt
    rw [h_template_eq]
    exact prodLinearFactors_eval_root pts.val 0 pts.val.length i.val
      (Nat.zero_le _) hi hi
  step with lagrange_interpolate_complete_spec template pts i
    hi h_template_pos h_root_template as
    ⟨result1, h_r1_len, h_r1_id⟩
  have h_r1_pos : 0 < result1.coefficients.val.length := by
    rw [h_r1_len, h_template_len]; omega
  step with vec_remove_zero_spec result1.coefficients h_r1_pos as
    ⟨_, _, h_v_drop⟩
  simp_all only
  have h_r1_len_eq : result1.coefficients.val.length = pts.val.length + 1 := by
    omega
  constructor
  · change (result1.coefficients.val.drop 1).length = pts.val.length
    rw [List.length_drop, h_r1_len_eq]
    omega
  · have h_prod_root : (prodLinearFactors pts.val 0 pts.val.length).eval
        (GF16.toGF216 (pts.val.get ⟨i.val, hi⟩).x) = 0 := by
      have := h_root_template
      unfold Poly.evalAt at this
      rwa [h_template_eq] at this
    have h_r1_coeff0 : result1.toGF216Poly.coeff 0 = 0 :=
      coeff_zero_of_X_mul_identity result1.toGF216Poly
        (GF16.toGF216 (pts.val.get ⟨i.val, hi⟩).x)
        (lagrangeScaleGF216 (pts.val.get ⟨i.val, hi⟩) pts.val)
        (prodLinearFactors pts.val 0 pts.val.length)
        h_r1_id h_prod_root
    have h_r1_X_factor : result1.toGF216Poly =
        X * listToGF216Poly (result1.coefficients.val.drop 1) := by
      unfold Poly.toGF216Poly
      exact listToGF216Poly_eq_X_mul_drop_one result1.coefficients.val h_r1_coeff0
    unfold Poly.toGF216Poly
    rw [h_v_drop]
    have h_X_ne_zero : (X : GF216Poly) ≠ 0 := Polynomial.X_ne_zero
    have h_cancel : X * listToGF216Poly (result1.coefficients.val.drop 1) *
        (X - C (GF16.toGF216 (pts.val.get ⟨i.val, hi⟩).x)) =
        X * C (lagrangeScaleGF216 (pts.val.get ⟨i.val, hi⟩) pts.val) *
          prodLinearFactors pts.val 0 pts.val.length := by
      rw [← h_r1_X_factor]
      exact h_r1_id
    have h_cancel' :
        X * (listToGF216Poly (result1.coefficients.val.drop 1) *
          (X - C (GF16.toGF216 (pts.val.get ⟨i.val, hi⟩).x))) =
        X * (C (lagrangeScaleGF216 (pts.val.get ⟨i.val, hi⟩) pts.val) *
          prodLinearFactors pts.val 0 pts.val.length) := by
      ring_nf
      ring_nf at h_cancel
      exact h_cancel
    exact mul_left_cancel₀ h_X_ne_zero h_cancel'

end spqr.encoding.polynomial.Poly
