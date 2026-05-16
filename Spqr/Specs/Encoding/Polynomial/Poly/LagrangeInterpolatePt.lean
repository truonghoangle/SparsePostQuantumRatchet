/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
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

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the 16-bit
encodings:
  `a + b = a − b = a ⊕ b`,
so the `−` in `(X − pts[j].x)` is the same as `+`, and all field operations are carried out via the
`GF16` Rust type wrapping `u16`.

**Source**: spqr/src/encoding/polynomial.rs (lines 231:4-236:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly
open spqr.encoding.polynomial
  (prodLinearFactors prodLinearFactors_eval_root)

namespace spqr.encoding.polynomial.Poly

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

instance : Inhabited spqr.encoding.polynomial.Pt where
  default := ⟨⟨0#u16⟩, ⟨0#u16⟩⟩

/-!
## Helper: spec for `alloc.vec.Vec.remove` at index 0

`alloc.vec.Vec.remove` is an external axiom (declared in `FunsExternal.lean`) modelling Rust's
`Vec::remove`.  For the `lagrange_interpolate_pt` proof we only need the case `index = 0`, where the
first element is extracted and the remaining elements are shifted down:

  `result.2.val = v.val.drop 1`

The axiom captures the standard semantics of Rust's `Vec::remove(0)` on a non-empty vector.
-/

/--
**Spec for `alloc.vec.Vec.remove` at index 0, specialised to `GF16` vectors.**

Given a non-empty vector `v` with `0 < v.val.length`, `Vec.remove v 0` returns the pair
`(v[0], tail)` where `tail.val = v.val.drop 1`.  The first element is extracted and the remaining
elements are shifted down by one position.

This is an external axiom matching the standard semantics of Rust's `Vec::remove(0)`.
-/
@[step]
private axiom vec_remove_zero_spec
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (h : 0 < v.val.length) :
    alloc.vec.Vec.remove Global v 0#usize
      ⦃ (result : GF16 × alloc.vec.Vec GF16) =>
        result.2.val = v.val.drop 1 ⦄

/-!
## Helper: polynomial division by `X` via `List.drop 1`

When the constant-term coefficient (position 0) of a GF16 coefficient list is zero under
`GF16.toGF216`, dropping the first element corresponds to polynomial division by `X`:

  `listToGF216Poly cs = X · listToGF216Poly (cs.drop 1)`

This is the algebraic content of the `coefficients.remove(0)` operation in the Rust implementation:
since `result1.coefficients[0] = GF16::ZERO` (verified by the `debug_assert_eq!` in
`lagrange_interpolate_complete`), removing it is equivalent to dividing the polynomial by `X`.
-/

/--
**`listToGF216Poly` of `drop 1` relates to the original polynomial by division by `X`.**

If the constant-term coefficient of a `GF16` list has `toGF216 = 0`, then
`listToGF216Poly cs = X · listToGF216Poly (cs.drop 1)`.
-/
private lemma listToGF216Poly_eq_X_mul_drop_one
    (cs : List spqr.encoding.gf.GF16)
    (h0 : (listToGF216Poly cs).coeff 0 = 0) :
    listToGF216Poly cs = X * listToGF216Poly (cs.drop 1) := by
  ext m
  cases m with
  | zero =>
    simp only [coeff_X_mul_zero, h0]
  | succ n =>
    rw [coeff_X_mul, listToGF216Poly_coeff, listToGF216Poly_coeff]
    by_cases hn : n + 1 < cs.length
    · have hdn : n < (cs.drop 1).length := by rw [List.length_drop]; omega
      rw [dif_pos hn, dif_pos hdn]
      congr 1
      simp only [List.get_eq_getElem]
      simp only [List.getElem_drop]
      grind
    · have hdn : ¬(n < (cs.drop 1).length) := by rw [List.length_drop]; omega
      rw [dif_neg hn, dif_neg hdn]

/--
**The constant term of `result1.toGF216Poly` is zero.**

From the polynomial identity
  `result1 · (X − C(a)) = X · C(s) · P`
the RHS has a factor of `X` and hence zero constant term.  Comparing constant terms:
  `result1.coeff(0) · (−a) = 0`
In GF(2¹⁶), `−a = a`, so `result1.coeff(0) · a = 0`.

• When `a ≠ 0`: since `GF216` is an integral domain, `result1.coeff(0) = 0`.
• When `a = 0`: `(X − C(0)) = X`, so `result1 · X = X · C(s) · P`, giving
  `result1 = C(s) · P`.  Since `P.eval a = 0` and `a = 0`, the factor theorem
  gives `X ∣ P`, so `P = X · Q` and `result1 = C(s) · X · Q`, hence
  `result1.coeff(0) = 0`.

The additional hypothesis `h_root : P.eval a = 0` is needed for the `a = 0` case,
where the constant-term argument alone is insufficient.  In the application context,
this holds because `P = prodLinearFactors` evaluates to zero at every point `pts[j].x`.
-/
private lemma coeff_zero_of_X_mul_identity
    (p : GF216Poly) (a s : GF216) (P : GF216Poly)
    (h_id : p * (X - C a) = X * C s * P)
    (h_root : P.eval a = 0) :
    p.coeff 0 = 0 := by
  by_cases ha : a = 0
  · -- Case a = 0: X − C 0 = X, and P.eval 0 = 0 gives X ∣ P by the factor theorem
    subst ha
    simp only [map_zero, sub_zero] at h_id
    -- h_id : p * X = X * C s * P
    -- Factor theorem: P.eval 0 = 0 ⟹ (X − C 0) ∣ P, i.e., X ∣ P
    have h_X_dvd_P : (X : GF216Poly) ∣ P := by
      have h_div : (X - C (0 : GF216)) ∣ P := dvd_iff_isRoot.mpr h_root
      rwa [map_zero, sub_zero] at h_div
    obtain ⟨Q, hQ⟩ := h_X_dvd_P
    -- Cancel X: p * X = (C s * P) * X ⟹ p = C s * P
    have hX_ne : (X : GF216Poly) ≠ 0 := X_ne_zero
    have hp_eq : p = C s * P := by
      have h1 : p * X = (C s * P) * X := by
        ring_nf; ring_nf at h_id; exact h_id
      exact mul_right_cancel₀ hX_ne h1
    -- Substitute P = X * Q: p = C s * (X * Q)
    -- p.coeff 0 = s * (0 * Q.coeff 0) = 0
    rw [hp_eq, hQ]
    simp only [Polynomial.mul_coeff_zero, coeff_C_zero, coeff_X_zero,
               zero_mul, mul_zero]
  · -- Case a ≠ 0: extract constant terms, use char 2 and integral domain
    have h0 := congr_arg (fun q => q.coeff 0) h_id
    simp only [Polynomial.mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero,
               zero_sub, zero_mul] at h0
    -- h0 : p.coeff 0 * -a = 0
    -- In char 2, -a = a
    rw [CharTwo.neg_eq] at h0
    -- h0 : p.coeff 0 * a = 0. Since a ≠ 0, p.coeff 0 = 0.
    exact (mul_eq_zero.mp h0).elim id (absurd · ha)

/-!
## Main theorem

The specification theorem for `lagrange_interpolate_pt` combines the prepare, complete, and remove
steps into a single postcondition.
-/

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
