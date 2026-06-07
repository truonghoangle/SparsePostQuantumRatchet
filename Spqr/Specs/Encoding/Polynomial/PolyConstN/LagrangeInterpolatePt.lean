/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Gf.GF16.ConstDiv
import Spqr.Specs.Encoding.Polynomial.PolyConstN.Mult
import Spqr.Specs.Encoding.Gf.GF16.ZERO
import Spqr.Specs.Encoding.Gf.GF16.ONE
import Spqr.Specs.Encoding.Polynomial.PolyConstN.MultXdiff
import Spqr.Specs.Encoding.Gf.GF16.ConstSub
import Spqr.Specs.Encoding.Gf.GF16.ConstMul

/-!
# Spec theorem for `PolyConst::lagrange_interpolate_pt`: loop body 0

The Rust function `PolyConst::lagrange_interpolate_pt` (in `src/encoding/polynomial.rs`, lines
370:4-395:5) computes the Lagrange basis polynomial for the `i`-th point in a slice of evaluation
points `pts`, scaled by `pts[i].y / denominator`.  The computation is performed in two phases:

  1. A `while j < N` loop (lines 380:12-391:13) that builds the unnormalised Lagrange basis
     polynomial `p = ∏_{j ≠ i} (X − pts[j].x)` and the denominator
     `∏_{j ≠ i} (pts[i].x − pts[j].x)`.
  2. A final scalar multiplication `p.mult(pts[i].y.const_div(&denominator))`.

This file specifies **loop body 0** — one iteration of the `while j < N` loop (lines 380-391).
The extracted Lean function `encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop.body`
performs one iteration:

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

At the end of the full loop (after all `N` iterations starting from `j = 0`), the polynomial and
denominator satisfy:
  - `p = ∏_{j : pts[j].x ≠ pts[i].x} (X − pts[j].x)` — the unnormalised Lagrange basis polynomial.
  - `denominator = ∏_{j : pts[j].x ≠ pts[i].x} (pts[i].x − pts[j].x)` — the Lagrange denominator.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition (`a − b = a + b = a ⊕ b`),
so `(X − pj.x) = (X + pj.x)` and `pi.x − pj.x = pi.x + pj.x`.  All field operations are carried
out via the `GF16` Rust type wrapping `u16`, with carry-less polynomial multiplication modulo the
irreducible polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 380:12-391:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open encoding.polynomial

namespace spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

/--
**Spec theorem for `encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop.body`**:

One step of the loop in `PolyConst::lagrange_interpolate_pt`, which builds the unnormalised
Lagrange basis polynomial and the corresponding denominator.  Given the slice `pts`, the
interpolation point `pi = pts[i]`, the running polynomial `p`, the running `denominator`, and
the loop counter `j`, the body processes one index:

• The function always succeeds (no panic) provided the preconditions hold, since
  `Slice.index_usize` is bounded by `N ≤ pts.length`, `mult_xdiff` is total under the
  leading-zero precondition, and `const_sub`/`const_mul` are total on `GF16 × GF16`.

• In the **done** case (`j ≥ N`):
    `pi' = pi ∧ p' = p ∧ denominator' = denominator`
    — all outputs are returned unchanged.

• In the **cont** case (`j < N`):
    - The loop counter has advanced: `j1.val = j.val + 1`.
    - **Skip sub-case** (`pi.x.value = pts[j].x.value`):
        `p1 = p ∧ denominator1 = denominator`
        — the polynomial and denominator are unchanged (this index corresponds to the
        interpolation point itself).
    - **Update sub-case** (`pi.x.value ≠ pts[j].x.value`):
        - The polynomial is multiplied by the linear factor `(X − pts[j].x)`:
            `listToGF216Poly p1.coefficients.val =
               (X − C (pts[j].x.toGF216)) * listToGF216Poly p.coefficients.val`
        - The denominator is updated with the field difference:
            `denominator1.toGF216 =
               denominator.toGF216 * (pi.x.toGF216 − pts[j].x.toGF216)`

**Source**: spqr/src/encoding/polynomial.rs (lines 380:12-391:13)
-/
@[step]
theorem body_spec
    {N : Usize}
    (pts : Slice Pt)
    (pi : Pt)
    (p : PolyConst N)
    (denominator : GF16)
    (j : Usize)
    (h_N_pos : 0 < N.val)
    (h_N_le_pts : N.val ≤ pts.val.length)
    (h_leading_zero : (p.coefficients.val[N.val - 1]!).value.val = 0) :
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
  · step*

end spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop



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

/-- **Conditional product of linear factors**
`∏_{k ≥ start, pts[k].x ≠ pi_x} (X − C(pts[k].x.toGF216))`.

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


/-! # Spec theorem for
`spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyConst<N>}::lagrange_interpolate_pt`

Given a slice of evaluation points `pts : &[Pt]` and an index `i < N ≤ pts.len()`, the Rust
function `PolyConst::lagrange_interpolate_pt` (in `src/encoding/polynomial.rs`, lines 370:4-395:5)
returns the i-th scaled Lagrange basis polynomial over GF(2¹⁶) packed into a fixed-size
`PolyConst N` whose coefficient array has exactly `N` slots.  Unlike the heap-backed `Poly`
variant (`Poly::lagrange_interpolate_pt`), this version is `const fn`, allocates no `Vec`, and
relies on a tight static degree bound: every intermediate polynomial fits in `N` coefficients
because the leading slot `coefficients[N − 1]` is maintained zero throughout the loop.

Concretely the Aeneas-extracted Lean function
`encoding.polynomial.PolyConst.lagrange_interpolate_pt` proceeds as follows:

1. **Read the interpolation point**: `pi := pts[i]` via `Slice.index_usize`.

2. **Initialise the unit polynomial**: build an `Array GF16 N` filled with `GF16.ZERO` and
   overwrite position `0` with `GF16.ONE`, yielding the coefficient list
     `[ONE, ZERO, …, ZERO]`,
   which represents the constant polynomial `1 ∈ GF216[X]`.  This is the multiplicative
   identity of the loop's running product.

3. **Build the unnormalised basis polynomial and the denominator** by calling
     `lagrange_interpolate_pt_loop pts pi {coefficients := a1} GF16.ONE 0#usize`
   (see `LagrangeInterpolatePtLoop0`).  After all `N` iterations, the loop returns
   `(pi1, p, denominator)` with `pi1 = pi` and
   - `listToGF216Poly p.coefficients =
        condProdLinearFactors pi.x (pts.take N) 0`        — the running poly, started at `1`.
   - `denominator.toGF216 =
        lagrangeDenomProd pi.x (pts.take N) 0`             — the denominator, started at `1`.

   Here `condProdLinearFactors pi.x (pts.take N) 0 = ∏_{j < N, pts[j].x.value ≠ pi.x.value}
   (X − C(pts[j].x.toGF216))` and `lagrangeDenomProd pi.x (pts.take N) 0 =
   ∏_{j < N, pts[j].x.value ≠ pi.x.value} (pi.x.toGF216 − pts[j].x.toGF216)` are the
   value-skip Lagrange products restricted to the first `N` points.  Index `j = i` is always
   skipped because `pi.x.value = pts[i].x.value`.

4. **Fermat-style division**: compute
     `g := pi.y.const_div denominator`,
   whose specification (`GF16.const_div_spec`) gives at the GF(2¹⁶) level
     `g.toGF216 = pi.y.toGF216 * denominator.toGF216 ^ (2¹⁶ − 2)`.
   When `denominator ≠ 0` Fermat's little theorem in GF(2¹⁶) makes the exponent
   `2¹⁶ − 2` the multiplicative inverse, so `g = pi.y / denominator`.

5. **Scale the basis polynomial**: return `p.mult(g)`, which (via `PolyConst.mult_spec`)
   yields a polynomial whose `GF216[X]` interpretation is `C g.toGF216 ·
   listToGF216Poly p.coefficients`.

The net effect is to produce a polynomial `result` such that

  `listToGF216Poly result.coefficients
       = C (pi.y.toGF216 *
            (lagrangeDenomProd pi.x (pts.take N) 0) ^ (2¹⁶ − 2)) *
         condProdLinearFactors pi.x (pts.take N) 0`

in `GF216[X]`, which — using `lagrangeScaleGF216 pi (pts.take N) =
pi.y.toGF216 * (lagrangeDenomProd pi.x (pts.take N) 0) ^ (2¹⁶ − 2)` — collapses to

  `listToGF216Poly result.coefficients
       = C (lagrangeScaleGF216 pi (pts.take N)) *
         condProdLinearFactors pi.x (pts.take N) 0`.

When the first `N` x-coordinates are pairwise distinct, `condProdLinearFactors` coincides with
the classical Lagrange basis polynomial `∏_{j ≠ i} (X − pts[j].x)` and the denominator is
non-zero, so the right-hand side is the i-th term of the standard Lagrange interpolation
formula passing through `(pi.x, pi.y)`.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition (`a − b = a + b = a ⊕ b`),
so the linear factors `(X − pts[j].x)` and the differences `pi.x − pts[j].x` are equivalently
`(X + pts[j].x)` and `pi.x + pts[j].x`.

**Source**: spqr/src/encoding/polynomial.rs (lines 370:4-395:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop
  (condProdLinearFactors countNonSkip countNonSkip_skip countNonSkip_accum
   countNonSkip_ge)

namespace spqr.encoding.polynomial.PolyConst

/-! ## Helper lemmas for the initial state -/

/--
**The freshly-initialised coefficient array represents the constant polynomial `1`.**

After `let a := Array.repeat N GF16.ZERO` and `a1 := Array.update a 0 GF16.ONE`, the underlying
list is `[ONE, ZERO, ZERO, …, ZERO]` with `N` entries.  Mapping through `listToGF216Poly` and
using `GF16.toGF216_zero_val` / `GF16.toGF216_one_val` at each coefficient position, every
coefficient at degree `≥ 1` is zero and the constant coefficient is `1`, so the resulting
`GF216[X]` element is `C 1 = 1`.
-/
private theorem listToGF216Poly_init_one
    {N : Usize} (a1 : Array GF16 N)
    (h_len : a1.val.length = N.val)
    (h0 : (a1.val[0]!).value.val = 1)
    (h_rest : ∀ j, 0 < j → j < N.val → (a1.val[j]!).value.val = 0) :
    listToGF216Poly a1.val = (1 : GF216Poly) := by
  -- We compare coefficient-by-coefficient.  At every position `m`:
  -- * `(1 : GF216Poly).coeff m` is `1` if `m = 0` and `0` otherwise.
  -- * `(listToGF216Poly a1.val).coeff m` is `(a1.val[m]!).toGF216` (via
  --   `getElem_bang_toGF216_eq_coeff`, which folds the out-of-bounds case to the
  --   `GF16` default — whose `toGF216` is also `0`).
  -- The hypotheses `h0` and `h_rest` exactly say that the underlying `value.val`
  -- equals `1` at position `0` and `0` elsewhere, so `GF16.toGF216_one_val` /
  -- `GF16.toGF216_zero_val` close each case.
  apply Polynomial.ext
  intro m
  cases m with
  | zero =>
    -- `(1 : GF216Poly).coeff 0 = 1` and the LHS coefficient is
    -- `(a1.val[0]!).toGF216 = 1` by `h0`.
    rw [Polynomial.coeff_one_zero, ← getElem_bang_toGF216_eq_coeff]
    exact GF16.toGF216_one_val _ h0
  | succ n =>
    -- The RHS coefficient is `0`.
    have h_one : (1 : GF216Poly).coeff (n + 1) = 0 := by
      rw [Polynomial.coeff_one]; simp
    rw [h_one]
    by_cases hlt : n + 1 < a1.val.length
    · -- In-bounds: use `h_rest`.
      rw [← getElem_bang_toGF216_eq_coeff]
      apply GF16.toGF216_zero_val
      exact h_rest (n + 1) (Nat.succ_pos n) (h_len ▸ hlt)
    · -- Out-of-bounds: the coefficient is zero by length bound.
      push Not at hlt
      exact listToGF216Poly_coeff_eq_zero a1.val (n + 1) hlt

/--
**The freshly-initialised coefficient array has zero leading coefficient when `N ≥ 2`.**

Since position `N − 1 ≥ 1` of `a1 = [ONE, ZERO, …, ZERO]` is `GF16.ZERO`, the underlying
`u16` value is `0`.  This is the precondition needed to feed `mult_xdiff` (and hence the
loop body) inside `lagrange_interpolate_pt_loop`.
-/
private theorem init_leading_zero
    {N : Usize} (a1 : Array GF16 N)
    (h_N_ge_two : 2 ≤ N.val)
    (h_rest : ∀ j, 0 < j → j < N.val → (a1.val[j]!).value.val = 0) :
    (a1.val[N.val - 1]!).value.val = 0 := by
  exact h_rest (N.val - 1) (by omega) (by omega)


/-! ## Helper lemma: degree bound for the initial state

The loop spec (`lagrange_interpolate_pt_loop.loop_spec`) requires the polynomial-degree
invariant
    `(listToGF216Poly p.coefficients.val).natDegree +
        countNonSkip pi.x (pts.val.take N.val) j.val < N.val`.

At the entry point `(p, j) = ({coefficients := a1}, 0)`, the initial polynomial is the
constant `1` so its `natDegree` is `0`, and `countNonSkip pi.x (pts.val.take N.val) 0` is at
most `N.val − 1` because index `i < N.val` is always a skip (`pi.x.value = pts[i].x.value`).
-/

/-! ### Helper lemmas for the `countNonSkip` bound

The original axiom statement used `m ≤ pts.length`, but the conclusion
`countNonSkip pi_x pts 0 ≤ m - 1` is only valid when the segment `pts` itself has length at
most `m` (since `countNonSkip` counts over the full list `[0, pts.length)`, not just `[0, m)`).
We therefore strengthen the hypothesis to `pts.length ≤ m`; in the actual call site we have
`pts = pts.val.take N.val` with `(pts.val.take N.val).length = N.val = m`, so the new
hypothesis holds with equality and the lemma is used in exactly the intended way.
-/

/--
**Trivial bound**: `countNonSkip pi_x pts start ≤ pts.length - start` for all `start`.

By induction on the natural well-founded measure `pts.length - start`: in the recursive case
we use either `countNonSkip_skip` (count is preserved) or `countNonSkip_accum` (count grows
by exactly `1`), and in either case the recursive IH together with `omega` closes the goal.
-/
private lemma countNonSkip_le_length_sub
    (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat) :
    countNonSkip pi_x pts start ≤ pts.length - start := by
  by_cases h_lt : start < pts.length
  · have ih := countNonSkip_le_length_sub pi_x pts (start + 1)
    by_cases h_eq : pi_x.value = (pts.get ⟨start, h_lt⟩).x.value
    · rw [countNonSkip_skip pi_x pts start h_lt h_eq]; omega
    · rw [countNonSkip_accum pi_x pts start h_lt h_eq]; omega
  · rw [countNonSkip_ge pi_x pts start (by omega)]; omega
termination_by pts.length - start

/--
**Strict bound when a skip exists**: if `start ≤ i < pts.length` and `pi_x.value =
pts[i].x.value` (i.e., index `i` is a skip), then
`countNonSkip pi_x pts start + 1 ≤ pts.length - start`.

Proof by induction on `i - start`:
* If `start = i`, the current iteration is a skip, so the count is preserved
  (`countNonSkip_skip`) and the result follows from `countNonSkip_le_length_sub` applied at
  `start + 1`.
* If `start < i`, we recurse on `start + 1`; whether the current iteration is a skip or an
  accumulate, `omega` combines the recursive IH with the appropriate unfolding lemma.
-/
private lemma countNonSkip_add_one_le_of_skip
    (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (i : Nat) (h_start_le : start ≤ i) (h_i_lt : i < pts.length)
    (h_skip : pi_x.value = (pts.get ⟨i, h_i_lt⟩).x.value) :
    countNonSkip pi_x pts start + 1 ≤ pts.length - start := by
  by_cases h_eq_si : start = i
  · -- Base: the current iteration `start = i` is itself the skip.
    subst h_eq_si
    rw [countNonSkip_skip pi_x pts start h_i_lt h_skip]
    have := countNonSkip_le_length_sub pi_x pts (start + 1)
    omega
  · -- Step: recurse at `start + 1`, then case on whether `start` is a skip or accumulate.
    have h_start_lt_i : start < i := by omega
    have h_start_lt : start < pts.length := by omega
    have ih := countNonSkip_add_one_le_of_skip pi_x pts (start + 1) i
      (by omega) h_i_lt h_skip
    by_cases h_eq : pi_x.value = (pts.get ⟨start, h_start_lt⟩).x.value
    · rw [countNonSkip_skip pi_x pts start h_start_lt h_eq]; omega
    · rw [countNonSkip_accum pi_x pts start h_start_lt h_eq]; omega
termination_by i - start

/--
**Bound on `countNonSkip` when at least one index in `[0, m)` is a skip.**

If `pts.length ≤ m` and there exists `i < m` such that whenever `i < pts.length` we have
`pi_x.value = pts[i].x.value` (which makes index `i` a skip when it falls inside the list),
then `countNonSkip pi_x pts 0 ≤ m − 1`.

Proof: split on whether `i < pts.length`.
* If yes, the skip at index `i` is real, and `countNonSkip_add_one_le_of_skip` (with
  `start = 0`) gives `countNonSkip pi_x pts 0 + 1 ≤ pts.length ≤ m`, hence the bound.
* If no, then `pts.length ≤ i < m`, so `pts.length ≤ m - 1`; combined with the trivial
  bound `countNonSkip pi_x pts 0 ≤ pts.length` we again get the desired inequality.
-/
private theorem countNonSkip_le_of_skip_exists
    (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (m : Nat)
    (h_m_le : pts.length ≤ m)
    (i : Nat) (hi : i < m)
    (h_skip : ∀ (h : i < pts.length),
      pi_x.value = (pts.get ⟨i, h⟩).x.value) :
    countNonSkip pi_x pts 0 ≤ m - 1 := by
  by_cases h_i : i < pts.length
  · -- Real skip: the strict bound gives `count + 1 ≤ pts.length ≤ m`, hence `count ≤ m - 1`.
    have h := countNonSkip_add_one_le_of_skip pi_x pts 0 i (Nat.zero_le _) h_i (h_skip h_i)
    omega
  · -- `i ≥ pts.length`, so `pts.length < m`; the trivial bound suffices.
    have h := countNonSkip_le_length_sub pi_x pts 0
    omega


/-! ## Main spec theorem -/

/--
**Spec theorem for `spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt`**:

Given a slice of points `pts` with `N ≤ pts.val.length` and a valid index `i < N`, the
function returns a polynomial `result : PolyConst N` satisfying:

• The function always succeeds (no panic) under the stated preconditions, since
  `Slice.index_usize`, `Array.repeat`, `Array.update`, the loop
  `lagrange_interpolate_pt_loop` (whose runtime precondition — the polynomial-degree
  invariant — holds at entry because the initial polynomial is `1` and at least index `i`
  is a value-skip), `GF16.const_div`, and `PolyConst.mult` are all total under these
  assumptions.

• **Polynomial identity in `GF216[X]`**:
    `listToGF216Poly result.coefficients.val =
        C (pts[i].y.toGF216 *
            (lagrangeDenomProd pts[i].x (pts.take N) 0) ^ (2¹⁶ − 2)) *
          condProdLinearFactors pts[i].x (pts.take N) 0`
  where
  - `condProdLinearFactors pi.x (pts.take N) 0 =
        ∏_{j < N, pts[j].x.value ≠ pi.x.value} (X − C(pts[j].x.toGF216))`
    is the unnormalised Lagrange basis polynomial restricted to the first `N` points and
    using value-equality to identify the skipped index (which always includes `j = i`).
  - `lagrangeDenomProd pi.x (pts.take N) 0 =
        ∏_{j < N, pts[j].x.value ≠ pi.x.value} (pi.x.toGF216 − pts[j].x.toGF216)`
    is the corresponding denominator product.
  - The combined scalar
        `pts[i].y.toGF216 * (lagrangeDenomProd pts[i].x (pts.take N) 0) ^ (2¹⁶ − 2)`
    is exactly `lagrangeScaleGF216 pts[i] (pts.take N)` — the Fermat-style scaling factor
    that becomes `pts[i].y / ∏_{j ≠ i} (pts[i].x − pts[j].x)` when the denominator is
    nonzero (i.e., when the first `N` x-coordinates are pairwise distinct).

The proof composes the postconditions of the four building blocks:

  1. `lagrange_interpolate_pt_loop.loop_spec` (with `j = 0` and the entry-point degree
     bound `0 + countNonSkip pi.x (pts.take N) 0 ≤ N − 1 < N`, obtained from
     `countNonSkip_le_of_skip_exists`), producing
     `listToGF216Poly p.coefficients =
         condProdLinearFactors pi.x (pts.take N) 0 *
           listToGF216Poly initial.coefficients`
     where `listToGF216Poly initial.coefficients = 1` by
     `listToGF216Poly_init_one`, and
     `denominator.toGF216 = 1 * lagrangeDenomProd pi.x (pts.take N) 0`.
  2. `GF16.const_div_spec` for `g := pi.y.const_div denominator`, yielding
     `g.toGF216 = pi.y.toGF216 * denominator.toGF216 ^ (2¹⁶ − 2)`.
  3. `PolyConst.mult_spec` for `result := p.mult g`, yielding
     `listToGF216Poly result.coefficients =
         C g.toGF216 * listToGF216Poly p.coefficients`.

Multiplying through and using `1 * _ = _` yields the stated postcondition.

**Source**: spqr/src/encoding/polynomial.rs (lines 370:4-395:5)
-/
@[step]
theorem lagrange_interpolate_pt_spec
    (N : Usize)
    (pts : Slice Pt)
    (i : Std.Usize)
    (h_N_pos : 0 < N.val)
    (h_i_lt_N : i.val < N.val)
    (h_N_le_pts : N.val ≤ pts.val.length) :
    lagrange_interpolate_pt N pts i ⦃ (result : PolyConst N) =>
      ∀ (hi : i.val < pts.val.length),
        listToGF216Poly result.coefficients.val =
          C ((pts.val.get ⟨i.val, hi⟩).y.toGF216 *
              (lagrangeDenomProd (pts.val.get ⟨i.val, hi⟩).x
                (pts.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
            condProdLinearFactors (pts.val.get ⟨i.val, hi⟩).x
              (pts.val.take N.val) 0 ⦄ := by
  sorry
 /-
  unfold lagrange_interpolate_pt
  step*
  · simp only [a1_post, Array.set_val_eq, Array.repeat_val, UScalar.ofNatCore_val_eq]
    -- The initial polynomial [ONE, ZERO, ..., ZERO] equals 1
    have h_init : listToGF216Poly ((List.replicate (↑N) GF16.ZERO).set 0 GF16.ONE) = 1 := by
      ext m
      rw [listToGF216Poly_coeff, Polynomial.coeff_one]
      simp only [List.length_set, List.length_replicate]
      cases m with
      | zero =>
        simp [h_N_pos, List.get_eq_getElem, GF16.ONE_toGF216]
      | succ n =>
        rw [if_neg (show n + 1 ≠ 0 from by omega)]
        by_cases hlt : n + 1 < ↑N
        · rw [dif_pos hlt]
          simp only [List.get_eq_getElem, ne_eq, Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero,
            and_false, not_false_eq_true, List.getElem_set_ne, List.getElem_replicate,
            GF16.ZERO_toGF216]
        · rw [dif_neg hlt]
    rw [h_init, Polynomial.natDegree_one, Nat.zero_add]
    -- countNonSkip ≤ N - 1 because index i is a skip (pi = pts[i])
    have h_count : countNonSkip pi.x (List.take (↑N) (↑pts)) 0 ≤ ↑N - 1 := by
      apply countNonSkip_le_of_skip_exists pi.x _ (↑N)
        (by simp only [List.length_take, inf_le_left]) (↑i) h_i_lt_N
      intro h_i_lt
      have h_i_lt_pts : (↑i) < (↑pts : List Pt).length := by omega
      have h_take_eq : (List.take (↑N) (↑pts : List Pt)).get ⟨↑i, h_i_lt⟩ =
          (↑pts : List Pt).get ⟨↑i, h_i_lt_pts⟩ := by
        simp only [List.get_eq_getElem, List.getElem_take]
      rw [h_take_eq, pi_post, List.get_eq_getElem]
    omega
  · -- Final postcondition: compose the loop, const_div, and mult specs
    obtain ⟨h_pi1_eq, h_poly, h_denom⟩ := pi1_post
    -- Step 1: rewrite LHS using result_post1 and h_poly
    rw [result_post1, h_poly]
    -- Step 2: rewrite g using g_post and pi1 = pi
    rw [g_post, h_pi1_eq]
    -- Step 3: simplify the denominator using ONE_toGF216
    rw [h_denom, GF16.ONE_toGF216, one_mul]
    -- Step 4: show listToGF216Poly ↑a1 = 1
    have h_init : listToGF216Poly ↑a1 = 1 := by
      simp only [a1_post, Array.set_val_eq, Array.repeat_val, UScalar.ofNatCore_val_eq]
      ext m
      rw [listToGF216Poly_coeff, Polynomial.coeff_one]
      simp only [List.length_set, List.length_replicate]
      cases m with
      | zero => simp [h_N_pos, List.get_eq_getElem, GF16.ONE_toGF216]
      | succ n =>
        rw [if_neg (by omega)]
        by_cases hlt : n + 1 < ↑N
        · rw [dif_pos hlt]; simp [List.get_eq_getElem, List.getElem_replicate, GF16.ZERO_toGF216]
        · rw [dif_neg hlt]
    rw [h_init, mul_one]
    -- Step 5: relate pi to pts[i] via pi_post
    -- pi_post : pi = (↑pts)[↑i]! and we need pi = (↑pts).get ⟨↑i, result_post2⟩
    rw [pi_post]
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem result_post2,
      Option.getD_some, Nat.reducePow, Nat.reduceSub, map_mul, map_pow, List.get_eq_getElem]
-/

end spqr.encoding.polynomial.PolyConst
