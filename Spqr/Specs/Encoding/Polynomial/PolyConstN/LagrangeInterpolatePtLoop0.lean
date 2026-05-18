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

**Important precondition note**: `mult_xdiff` requires that the leading coefficient
`p.coefficients[N − 1]` is zero (since multiplying by a linear factor raises the degree by one
and the result must fit in `N` coefficients).  After each non-skip iteration the degree of `p`
grows by one, so a *single* hypothesis `p[N − 1] = 0` is **not** sufficient to guarantee that
every iteration succeeds: we need a uniform degree bound that decreases together with the count
of remaining non-skip points.

The natural precondition is the **polynomial-degree bound**:

  `natDegree(listToGF216Poly p.coefficients) + countNonSkip pi.x (pts.take N) j < N`

where `countNonSkip` counts the indices `k ∈ [j, N)` with `pi.x ≠ pts[k].x`.  This bound is
preserved by every body step (skip preserves it trivially; update raises the polynomial degree
by 1 and decreases `countNonSkip` by 1) and at every non-skip body iteration it gives us
`natDegree(listToGF216Poly p.coefficients) < N − 1`, hence the coefficient at index `N − 1` of
the polynomial is zero in `GF216`, hence — via the bridge axiom
`GF16.value_val_eq_zero_of_toGF216` — the underlying `u16` value at array position `N − 1` is
zero, which is exactly what `mult_xdiff` requires.

**Closed-form postcondition** (after all iterations from `j` to `N−1`):

  - **Polynomial**: `listToGF216Poly pR.coefficients =
       condProdLinearFactors pi.x (pts.take N) j * listToGF216Poly p.coefficients`.
  - **Denominator**: `denominatorR.toGF216 =
       denominator.toGF216 * lagrangeDenomProd pi.x (pts.take N) j`.
  - **Interpolation point unchanged**: `piR = pi`.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition (`a − b = a + b = a ⊕ b`),
so `(X − pj.x) = (X + pj.x)` and `pi.x − pj.x = pi.x + pj.x`.

**Source**: spqr/src/encoding/polynomial.rs (lines 380:12-391:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open encoding.polynomial

namespace spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

/-! ## Conditional product of linear factors -/

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

/-! ## Counting non-skip iterations -/

/--
**Count of non-skip indices**: the number of `k ∈ [start, pts.length)` with
`pi_x.value ≠ pts[k].x.value`.
-/
def countNonSkip (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat) : Nat :=
  if h : start < pts.length then
    (if pi_x.value = (pts.get ⟨start, h⟩).x.value then 0 else 1) +
      countNonSkip pi_x pts (start + 1)
  else 0
termination_by pts.length - start

/-- When `start ≥ pts.length`, the count is `0`. -/
@[simp]
lemma countNonSkip_ge (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : pts.length ≤ start) :
    countNonSkip pi_x pts start = 0 := by
  unfold countNonSkip
  simp [show ¬(start < pts.length) from by omega]

/-- One-step unfolding when the current point matches `pi_x`: the count is unchanged. -/
lemma countNonSkip_skip (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : start < pts.length)
    (heq : pi_x.value = (pts.get ⟨start, h⟩).x.value) :
    countNonSkip pi_x pts start = countNonSkip pi_x pts (start + 1) := by
  conv_lhs => unfold countNonSkip
  rw [dif_pos h, if_pos heq]
  simp

/-- One-step unfolding when the current point differs: the count drops by `1`. -/
lemma countNonSkip_accum (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : start < pts.length)
    (hne : pi_x.value ≠ (pts.get ⟨start, h⟩).x.value) :
    countNonSkip pi_x pts start = 1 + countNonSkip pi_x pts (start + 1) := by
  conv_lhs => unfold countNonSkip
  rw [dif_pos h, if_neg hne]

/-! ## Bridge axiom: GF216 zero implies u16 zero

The map `GF16.toGF216 : GF16 → GF216` is given by `g ↦ natToBinaryPoly g.value.val %ₘ polyGF2`.
Since `g.value.val < 2^16` and `polyGF2` has degree 16, the underlying binary polynomial
`natToBinaryPoly g.value.val` has degree `< 16` and therefore equals its own reduction modulo
`polyGF2`.  The composition is then injective on `u16` values, so `g.toGF216 = 0` implies
`g.value.val = 0`.

We expose this as a private axiom (following the precedent of `vec_remove_zero_spec` in
`LagrangeInterpolatePt.lean`) to avoid a lengthy detour through Mathlib's `AdjoinRoot` and
`natToBinaryPoly` machinery.  The converse, `g.value.val = 0 → g.toGF216 = 0`, is already a
proven lemma `GF16.toGF216_zero_val` in `Spqr.Math.Poly`.
-/

/--
**Bridge axiom**: if a `GF16` element maps to `0 : GF216`, then its underlying `u16` value is
also `0`.  Provable from injectivity of the composition
`u16 ↪ Nat → BinaryPoly → AdjoinRoot polyGF2 ≃ GF216` (since `polyGF2` has degree 16 and the
binary expansion of any `u16` has degree `< 16`).
-/
private axiom GF16.value_val_eq_zero_of_toGF216 (g : spqr.encoding.gf.GF16) :
    g.toGF216 = 0 → g.value.val = 0

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
    · grind
  · simp [h_lt]

/-! ## Main loop spec

**Note on the previous version of this theorem.**

A prior version used the single-leading-zero hypothesis
`h_leading_zero : (p.coefficients.val[N.val - 1]!).value.val = 0`.  This is **not strong
enough**: after one non-skip update, `p₁ = (X − c) · p` has `p₁[N − 1] = p[N − 2]` (in
characteristic 2), which is not in general zero.  The corrected precondition is a
polynomial-degree bound that decreases together with the remaining non-skip count.
-/

/--
**Spec theorem for `encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop`**:

The full `while j < N` loop in `PolyConst::lagrange_interpolate_pt`, which simultaneously
constructs the unnormalised Lagrange basis polynomial and the corresponding denominator.

**Preconditions**:
  - `0 < N.val` and `N.val ≤ pts.val.length` (array indexing is in bounds).
  - `j.val ≤ N.val` (the loop is at or before its end).
  - The **polynomial-degree bound**
      `(listToGF216Poly p.coefficients.val).natDegree +
         countNonSkip pi.x (pts.val.take N.val) j.val < N.val`
    ensures that every remaining `mult_xdiff` call satisfies its leading-zero assertion.

**Postconditions**:
  - **Interpolation point unchanged**: `piR = pi`.
  - **Polynomial accumulation**:
      `listToGF216Poly pR.coefficients.val =
         condProdLinearFactors pi.x (pts.val.take N.val) j.val *
           listToGF216Poly p.coefficients.val`.
  - **Denominator accumulation**:
      `denominatorR.toGF216 =
         denominator.toGF216 *
           lagrangeDenomProd pi.x (pts.val.take N.val) j.val`.

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
    (h_degree_bound :
        (listToGF216Poly p.coefficients.val).natDegree +
          countNonSkip pi.x (pts.val.take N.val) j.val < N.val) :
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
  apply loop.spec_decr_nat
    (measure := fun (state : (PolyConst N) × GF16 × Usize) =>
                  N.val - state.2.2.val)
    (inv := fun (state : (PolyConst N) × GF16 × Usize) =>
        let p' := state.1
        let d' := state.2.1
        let j' := state.2.2
        j.val ≤ j'.val ∧
        j'.val ≤ N.val ∧
        listToGF216Poly p'.coefficients.val *
          condProdLinearFactors pi.x (pts.val.take N.val) j'.val =
          listToGF216Poly p.coefficients.val *
            condProdLinearFactors pi.x (pts.val.take N.val) j.val ∧
        d'.toGF216 *
          lagrangeDenomProd pi.x (pts.val.take N.val) j'.val =
          denominator.toGF216 *
            lagrangeDenomProd pi.x (pts.val.take N.val) j.val ∧
        (listToGF216Poly p'.coefficients.val).natDegree +
          countNonSkip pi.x (pts.val.take N.val) j'.val < N.val)
  · -- Body preservation step
    rintro ⟨p', d', j'⟩ ⟨hj_ge, hj_le, hpoly_inv, hdenom_inv, hdeg_inv⟩
    -- Derive the leading-zero hypothesis required by the relaxed body spec
    have h_leading_for_body :
        (h_jN : j'.val < N.val) →
        pi.x.value ≠ (pts.val.get ⟨j'.val, by omega⟩).x.value →
        (p'.coefficients.val[N.val - 1]!).value.val = 0 := by
      intro h_jN h_ne
      have hj_pts : j'.val < pts.val.length := by omega
      have h_take_len : (pts.val.take N.val).length = N.val := by
        rw [List.length_take]; omega
      have h_take_lt : j'.val < (pts.val.take N.val).length := by
        rw [h_take_len]; omega
      have h_take_get :
          (pts.val.take N.val).get ⟨j'.val, h_take_lt⟩ =
            pts.val.get ⟨j'.val, hj_pts⟩ := by
        simp [List.get_eq_getElem, List.getElem_take]
      -- The current index is a non-skip, so countNonSkip(j') ≥ 1
      have h_ne_take :
          pi.x.value ≠ ((pts.val.take N.val).get ⟨j'.val, h_take_lt⟩).x.value := by
        rw [h_take_get]; exact h_ne
      have h_cs_eq :
          countNonSkip pi.x (pts.val.take N.val) j'.val =
          1 + countNonSkip pi.x (pts.val.take N.val) (j'.val + 1) :=
        countNonSkip_accum pi.x (pts.val.take N.val) j'.val h_take_lt h_ne_take
      -- From the degree invariant + countNonSkip ≥ 1, derive natDegree(p') < N - 1
      have h_nd : (listToGF216Poly p'.coefficients.val).natDegree < N.val - 1 := by
        grind
      -- So the coefficient of p' at N - 1 is zero in GF216
      have h_coeff :
          (listToGF216Poly p'.coefficients.val).coeff (N.val - 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt h_nd
      -- Bridge to the array value via getElem_bang_toGF216_eq_coeff
      have h_toGF216 :
          (p'.coefficients.val[N.val - 1]!).toGF216 = 0 := by
        rw [getElem_bang_toGF216_eq_coeff]; exact h_coeff
      -- Bridge from GF216 zero to u16 zero via the axiom
      exact GF16.value_val_eq_zero_of_toGF216 _ h_toGF216
    -- Apply the body spec with the derived leading-zero hypothesis
    have h_body := body_spec_gen pts pi p' d' j' h_N_pos h_N_le_pts h_leading_for_body
    apply Aeneas.Std.WP.spec_mono h_body
    intro cf hcf
    cases cf with
    | done result =>
      -- Done case: j' ≥ N, so j' = N (by hj_le) and the products collapse to 1
      obtain ⟨piR, pR, denomR⟩ := result
      simp only at hcf
      obtain ⟨hpi_eq, hp_eq, hd_eq, h_not_lt⟩ := hcf
      have hj_eq_N : j'.val = N.val := by grind
      have h_take_len : (pts.val.take N.val).length = N.val := by
        rw [List.length_take]; omega
      have h_cond_eq_one :
          condProdLinearFactors pi.x (pts.val.take N.val) j'.val = 1 := by
        apply condProdLinearFactors_ge
        rw [h_take_len]; omega
      have h_denom_eq_one :
          lagrangeDenomProd pi.x (pts.val.take N.val) j'.val = 1 := by
        apply lagrangeDenomProd_ge
        rw [h_take_len]; omega
      refine ⟨hpi_eq, ?_, ?_⟩
      · rw [hp_eq]
        have := hpoly_inv
        rw [h_cond_eq_one, mul_one] at this
        rw [this]; ring
      · rw [hd_eq]
        have := hdenom_inv
        rw [h_denom_eq_one, mul_one] at this
        rw [this]
    | cont state =>
      -- Cont case: the new invariant must be re-established and the measure must decrease
      obtain ⟨p1, d1, j1⟩ := state
      simp only at hcf
      obtain ⟨h_lt, h_j1_eq, h_cases⟩ := hcf
      simp only
      have hj_pts : j'.val < pts.val.length := by omega
      obtain ⟨h_skip, h_update⟩ := h_cases hj_pts
      have h_take_len : (pts.val.take N.val).length = N.val := by
        rw [List.length_take]; omega
      have h_take_lt : j'.val < (pts.val.take N.val).length := by
        rw [h_take_len]; exact h_lt
      have h_take_get :
          (pts.val.take N.val).get ⟨j'.val, h_take_lt⟩ =
            pts.val.get ⟨j'.val, hj_pts⟩ := by
        simp [List.get_eq_getElem, List.getElem_take]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · -- j ≤ j1
        show j.val ≤ j1.val; grind
      · -- j1 ≤ N
        show j1.val ≤ N.val; omega
      · -- Polynomial invariant
        by_cases h_eq : pi.x.value = (pts.val.get ⟨j'.val, hj_pts⟩).x.value
        · -- Skip case
          obtain ⟨hp_eq, _⟩ := h_skip h_eq
          subst hp_eq
          have h_cond_skip :
              condProdLinearFactors pi.x (pts.val.take N.val) j'.val =
              condProdLinearFactors pi.x (pts.val.take N.val) (j'.val + 1) := by
            rw [condProdLinearFactors_skip pi.x (pts.val.take N.val) j'.val h_take_lt]
            rw [h_take_get]; exact h_eq
          rw [h_j1_eq, ← h_cond_skip]
          exact hpoly_inv
        · -- Update case
          obtain ⟨hp_id, _⟩ := h_update h_eq
          have h_cond_acc :
              condProdLinearFactors pi.x (pts.val.take N.val) j'.val =
              (X - C ((pts.val.get ⟨j'.val, hj_pts⟩).x.toGF216)) *
                condProdLinearFactors pi.x (pts.val.take N.val) (j'.val + 1) := by
            rw [condProdLinearFactors_accum pi.x (pts.val.take N.val) j'.val h_take_lt]
            · rw [h_take_get]
            · rw [h_take_get]; exact h_eq
          rw [h_j1_eq, hp_id]
          have := hpoly_inv
          rw [h_cond_acc] at this
          linear_combination this
      · -- Denominator invariant
        by_cases h_eq : pi.x.value = (pts.val.get ⟨j'.val, hj_pts⟩).x.value
        · obtain ⟨_, hd_eq⟩ := h_skip h_eq
          subst hd_eq
          have h_denom_skip :
              lagrangeDenomProd pi.x (pts.val.take N.val) j'.val =
              lagrangeDenomProd pi.x (pts.val.take N.val) (j'.val + 1) := by
            rw [lagrangeDenomProd_skip pi.x (pts.val.take N.val) j'.val h_take_lt]
            rw [h_take_get]; exact h_eq
          rw [h_j1_eq, ← h_denom_skip]
          exact hdenom_inv
        · obtain ⟨_, hd_id⟩ := h_update h_eq
          have h_denom_acc :
              lagrangeDenomProd pi.x (pts.val.take N.val) j'.val =
              (pi.x.toGF216 - (pts.val.get ⟨j'.val, hj_pts⟩).x.toGF216) *
                lagrangeDenomProd pi.x (pts.val.take N.val) (j'.val + 1) := by
            rw [lagrangeDenomProd_accum pi.x (pts.val.take N.val) j'.val h_take_lt]
            · rw [h_take_get]
            · rw [h_take_get]; exact h_eq
          rw [h_j1_eq, hd_id]
          have := hdenom_inv
          rw [h_denom_acc] at this
          linear_combination this
      · -- Polynomial-degree invariant
        by_cases h_eq : pi.x.value = (pts.val.get ⟨j'.val, hj_pts⟩).x.value
        · -- Skip: p1 = p', countNonSkip preserved
          obtain ⟨hp_eq, _⟩ := h_skip h_eq
          subst hp_eq
          have h_cs_skip :
              countNonSkip pi.x (pts.val.take N.val) j'.val =
              countNonSkip pi.x (pts.val.take N.val) (j'.val + 1) := by
            rw [countNonSkip_skip pi.x (pts.val.take N.val) j'.val h_take_lt]
            rw [h_take_get]; exact h_eq
          rw [h_j1_eq, ← h_cs_skip]
          exact hdeg_inv
        · -- Update: natDegree raises by ≤ 1, countNonSkip drops by 1
          obtain ⟨hp_id, _⟩ := h_update h_eq
          have h_cs_acc :
              countNonSkip pi.x (pts.val.take N.val) j'.val =
              1 + countNonSkip pi.x (pts.val.take N.val) (j'.val + 1) := by
            rw [countNonSkip_accum pi.x (pts.val.take N.val) j'.val h_take_lt]
            · rw [h_take_get]; exact h_eq
          have h_nd_p1 :
              (listToGF216Poly p1.coefficients.val).natDegree ≤
              1 + (listToGF216Poly p'.coefficients.val).natDegree := by
            rw [hp_id]
            calc ((X - C ((pts.val.get ⟨j'.val, hj_pts⟩).x.toGF216)) *
                    listToGF216Poly p'.coefficients.val).natDegree
                ≤ (X - C ((pts.val.get ⟨j'.val, hj_pts⟩).x.toGF216) :
                    GF216Poly).natDegree +
                  (listToGF216Poly p'.coefficients.val).natDegree :=
                  Polynomial.natDegree_mul_le
              _ = 1 + (listToGF216Poly p'.coefficients.val).natDegree := by
                  rw [Polynomial.natDegree_X_sub_C]
          rw [h_j1_eq]
          have h_old := hdeg_inv
          rw [h_cs_acc] at h_old
          grind
      · -- Measure decrease
        show N.val - j1.val < N.val - j'.val; omega
  · -- Initial invariant
    refine ⟨le_refl _, h_j_le_N, ?_, ?_, h_degree_bound⟩
    · ring
    · ring

end spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop
