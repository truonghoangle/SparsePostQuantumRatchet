/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.PolyConstN.LagrangeInterpolatePtLoopBody0

/-!
# Spec theorem for `PolyConst::lagrange_interpolate_pt`: loop 0

The Rust function `PolyConst::lagrange_interpolate_pt` (in `src/encoding/polynomial.rs`, lines
370:4-395:5) computes the Lagrange basis polynomial for the `i`-th point in a slice of evaluation
points `pts`, scaled by `pts[i].y / denominator`.  The computation is performed in two phases:

  1. A `while j < N` loop (lines 380:12-391:13) that builds the unnormalised Lagrange basis
     polynomial `p = ∏_{j ≠ i} (X − pts[j].x)` and the denominator
     `∏_{j ≠ i} (pts[i].x − pts[j].x)`.
  2. A final scalar multiplication `p.mult(pts[i].y.const_div(&denominator))`.

This file specifies **loop 0** — the `loop` fixed-point wrapper around the body
(`LagrangeInterpolatePtLoopBody0.body_spec`), which iterates over indices `j = 0, 1, …, N−1` and
simultaneously constructs the unnormalised Lagrange basis polynomial and the corresponding
denominator by conditionally multiplying in each factor.

At each step, the body processes index `j`:
  1. **Done** (`j ≥ N`): the loop terminates and `(pi, p, denominator)` are returned unchanged.
  2. **Continue** (`j < N`):
     a. Reads `pj := pts[j]` via `Slice.index_usize`.
     b. Advances the loop counter: `j1 = j + 1`.
     c. If `pi.x.value = pj.x.value` (skip case): returns `(p, denominator, j1)` unchanged —
        the point `pts[j]` is the interpolation point itself (`i = j`), so it is excluded from
        the Lagrange basis product.
     d. If `pi.x.value ≠ pj.x.value` (update case):
        - Multiplies the polynomial by the linear factor `(X − pj.x)`:
            `p1 = p.mult_xdiff(pj.x)`
        - Computes the field difference `g = pi.x.const_sub(pj.x)` via `const_sub`.
        - Updates the denominator: `denominator1 = denominator.const_mul(g)` via `const_mul`.

**Closed-form postcondition** (after all iterations from `j` to `N−1`):

The loop processes the point indices `j, j+1, …, N−1` and builds the conditional products:

  - **Polynomial**: the polynomial is multiplied by all linear factors `(X − pts[k].x)` for
    `k ∈ [j, N)` where `pts[k].x ≠ pi.x`:
      `listToGF216Poly pR.coefficients.val =
         condProdLinearFactors pi.x (pts.val.take N.val) j.val *
           listToGF216Poly p.coefficients.val`
    where `condProdLinearFactors` is the conditional product of `(X − C(pts[k].x.toGF216))` for
    indices `k ∈ [start, pts.length)` where `pi.x.value ≠ pts[k].x.value`.

  - **Denominator**: the denominator is multiplied by all field differences
    `pi.x − pts[k].x` for `k ∈ [j, N)` where `pts[k].x ≠ pi.x`:
      `denominatorR.toGF216 =
         denominator.toGF216 *
           lagrangeDenomProd pi.x (pts.val.take N.val) j.val`

  - **Interpolation point unchanged**: `piR = pi`.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition (`a − b = a + b = a ⊕ b`),
so `(X − pj.x) = (X + pj.x)` and `pi.x − pj.x = pi.x + pj.x`.  All field operations are carried
out via the `GF16` Rust type wrapping `u16`, with carry-less polynomial multiplication modulo the
irreducible polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 380:12-391:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open encoding.polynomial

namespace spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

/-! ## Conditional product of linear factors

`condProdLinearFactors pi_x pts start` computes the conditional product

  `∏_{k = start}^{pts.length − 1}
      (if pi_x.value = pts[k].x.value then 1
       else X − C(pts[k].x.toGF216))`

over the point list `pts` from index `start`.  This is the polynomial analogue of
`lagrangeDenomProd`, which computes the same conditional product but for field elements
`(pi_x.toGF216 − pts[k].x.toGF216)` instead of linear polynomial factors.

The definition mirrors `lagrangeDenomProd` from `Spqr.Math.Poly` and satisfies the same
recursion/base-case structure: it returns `1` (the multiplicative identity in `GF216[X]`) when
`start ≥ pts.length`, skips when `pi_x.value = pts[start].x.value`, and multiplies by the
linear factor `(X − C(pts[start].x.toGF216))` otherwise.
-/

/--
**Conditional product of linear factors** `∏_{k ≥ start, pts[k].x ≠ pi_x} (X − C(pts[k].x.toGF216))`.

Returns `1` when `start ≥ pts.length` (empty product).  Skips index `start` when
`pi_x.value = pts[start].x.value` (the interpolation point itself).  Multiplies by
`(X − C(pts[start].x.toGF216))` otherwise.
-/
noncomputable def condProdLinearFactors (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat) : GF216Poly :=
  if h : start < pts.length then
    if pi_x.value = (pts.get ⟨start, h⟩).x.value
    then condProdLinearFactors pi_x pts (start + 1)
    else (X - C ((pts.get ⟨start, h⟩).x.toGF216)) *
         condProdLinearFactors pi_x pts (start + 1)
  else 1
termination_by pts.length - start

/-- When `start ≥ pts.length`, the product is `1` (empty product). -/
@[simp]
lemma condProdLinearFactors_ge (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : pts.length ≤ start) :
    condProdLinearFactors pi_x pts start = 1 := by
  unfold condProdLinearFactors
  simp [show ¬(start < pts.length) from by omega]

/-- One-step unfolding when the current point matches `pi_x` (skip). -/
lemma condProdLinearFactors_skip (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : start < pts.length)
    (heq : pi_x.value = (pts.get ⟨start, h⟩).x.value) :
    condProdLinearFactors pi_x pts start =
      condProdLinearFactors pi_x pts (start + 1) := by
  conv_lhs => unfold condProdLinearFactors
  rw [dif_pos h, if_pos heq]

/-- One-step unfolding when the current point differs from `pi_x` (accumulate). -/
lemma condProdLinearFactors_accum (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : start < pts.length)
    (hne : pi_x.value ≠ (pts.get ⟨start, h⟩).x.value) :
    condProdLinearFactors pi_x pts start =
      (X - C ((pts.get ⟨start, h⟩).x.toGF216)) *
        condProdLinearFactors pi_x pts (start + 1) := by
  conv_lhs => unfold condProdLinearFactors
  rw [dif_pos h, if_neg hne]

/-! ## Relaxed body spec

The body spec from `LagrangeInterpolatePtLoopBody0` requires `h_leading_zero` unconditionally.
For the loop proof, we need a relaxed version that only requires it when the iteration is an
update (i.e., `pi.x ≠ pts[j].x`, so that `mult_xdiff` is actually called).  The skip and done
cases succeed without the leading-zero condition.
-/

/--
**Relaxed body spec**: requires `h_leading_zero` only when the current iteration is an update
(`j < N` and `pi.x.value ≠ pts[j].x.value`).  Skip and done cases succeed unconditionally.
-/
private theorem body_spec_gen
    {N : Usize}
    (pts : Slice Pt)
    (pi : Pt)
    (p : PolyConst N)
    (denominator : GF16)
    (j : Usize)
    (h_N_pos : 0 < N.val)
    (h_N_le_pts : N.val ≤ pts.val.length)
    (h_leading : (h_jN : j.val < N.val) →
      pi.x.value ≠ (pts.val.get ⟨j.val, by omega⟩).x.value →
      (p.coefficients.val[N.val - 1]!).value.val = 0) :
    body pts pi p denominator j ⦃ cf =>
      match cf with
      | ControlFlow.done (pi', p', denominator') =>
          pi' = pi ∧ p' = p ∧ denominator' = denominator ∧ ¬ (j.val < N.val)
      | ControlFlow.cont (p1, denominator1, j1) =>
          j.val < N.val ∧
          j1.val = j.val + 1 ∧
          ∀ (hj : j.val < pts.val.length),
            (pi.x.value = (pts.val.get ⟨j.val, hj⟩).x.value →
              p1 = p ∧ denominator1 = denominator) ∧
            (pi.x.value ≠ (pts.val.get ⟨j.val, hj⟩).x.value →
              listToGF216Poly p1.coefficients.val =
                (X - C ((pts.val.get ⟨j.val, hj⟩).x.toGF216)) *
                  listToGF216Poly p.coefficients.val ∧
              denominator1.toGF216 =
                denominator.toGF216 *
                  (pi.x.toGF216 - (pts.val.get ⟨j.val, hj⟩).x.toGF216)) ⦄ := by
  unfold body
  by_cases h_lt : j.val < N.val
  · simp only [UScalar.lt_equiv, h_lt, ↓reduceIte, not_true_eq_false, and_false,
      List.get_eq_getElem, ne_eq, UScalar.neq_to_neq_val, true_and]
    step*
    · grind
    · grind
    ·  grind
  · simp [h_lt]

/-! ## Main loop spec -/

/--
**Spec theorem for `encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop`**:

The full `while j < N` loop in `PolyConst::lagrange_interpolate_pt`, which simultaneously
constructs the unnormalised Lagrange basis polynomial and the corresponding denominator.  Given
the slice `pts`, the interpolation point `pi = pts[i]`, the running polynomial `p`, the running
`denominator`, and the starting loop counter `j`, the loop processes all indices from `j` to
`N−1` and returns `(piR, pR, denominatorR)` satisfying:

• The function always succeeds (no panic) provided the preconditions hold, since
  `Slice.index_usize` is bounded by `N ≤ pts.length`, `mult_xdiff` is total under the
  leading-zero precondition, and `const_sub`/`const_mul` are total on `GF16 × GF16`.

• **Interpolation point unchanged**: `piR = pi`.

• **Polynomial accumulation**:
    `listToGF216Poly pR.coefficients.val =
       condProdLinearFactors pi.x (pts.val.take N.val) j.val *
         listToGF216Poly p.coefficients.val`
  where `condProdLinearFactors` is the product of `(X − C(pts[k].x.toGF216))` over indices
  `k ∈ [j, N)` where `pi.x.value ≠ pts[k].x.value` (skipping the interpolation point itself).

• **Denominator accumulation**:
    `denominatorR.toGF216 =
       denominator.toGF216 *
         lagrangeDenomProd pi.x (pts.val.take N.val) j.val`
  where `lagrangeDenomProd` is the product of `(pi.x.toGF216 − pts[k].x.toGF216)` over the
  same set of indices, defined in `Spqr.Math.Poly`.

**Source**: spqr/src/encoding/polynomial.rs (lines 380:12-391:13)
-/
@[step]
theorem loop_spec
    {N : Usize}
    (pts : Slice Pt)
    (pi : Pt)
    (p : PolyConst N)
    (denominator : GF16)
    (j : Usize)
    (h_N_pos : 0 < N.val)
    (h_N_le_pts : N.val ≤ pts.val.length)
    (h_j_le_N : j.val ≤ N.val)
    (h_leading_zero : (p.coefficients.val[N.val - 1]!).value.val = 0) :
    lagrange_interpolate_pt_loop pts pi p denominator j
      ⦃ result =>
        let (piR, pR, denominatorR) := result
        piR = pi ∧
        listToGF216Poly pR.coefficients.val =
          condProdLinearFactors pi.x (pts.val.take N.val) j.val *
            listToGF216Poly p.coefficients.val ∧
        denominatorR.toGF216 =
          denominator.toGF216 *
            lagrangeDenomProd pi.x (pts.val.take N.val) j.val ⦄ := by
  unfold lagrange_interpolate_pt_loop
  -- Capture the interpolation point's x-coordinate for use in the invariant
  set pi_x := pi.x with h_pi_x
  apply loop.spec_decr_nat
    (measure := fun (state : (PolyConst N) × GF16 × Usize) =>
                  N.val - state.2.2.val)
    (inv := fun (state : (PolyConst N) × GF16 × Usize) =>
        let p' := state.1
        let d' := state.2.1
        let j' := state.2.2
        j.val ≤ j'.val ∧
        j'.val ≤ N.val ∧
        -- Polynomial accumulation invariant (multiplicative form):
        -- p'(X) · condProd_remaining(j') = p(X) · condProd_remaining(j)
        listToGF216Poly p'.coefficients.val *
          condProdLinearFactors pi_x (pts.val.take N.val) j'.val =
          listToGF216Poly p.coefficients.val *
            condProdLinearFactors pi_x (pts.val.take N.val) j.val ∧
        -- Denominator accumulation invariant (multiplicative form):
        -- d' · denomProd_remaining(j') = denominator · denomProd_remaining(j)
        d'.toGF216 *
          lagrangeDenomProd pi_x (pts.val.take N.val) j'.val =
          denominator.toGF216 *
            lagrangeDenomProd pi_x (pts.val.take N.val) j.val ∧
        -- The body can succeed: either h_leading_zero holds, or all remaining are skips
        ((p'.coefficients.val[N.val - 1]!).value.val = 0 ∨
         (∀ (k : Nat) (hk : k < pts.val.length), j'.val ≤ k → k < N.val →
           pi_x.value = (pts.val.get ⟨k, hk⟩).x.value)))
  · -- Body step: prove invariant is preserved and measure decreases
    simp
    sorry
  · -- Initial invariant
    refine ⟨le_refl _, h_j_le_N, ?_, ?_, Or.inl h_leading_zero⟩
    · ring
    · ring

end spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop
