/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
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
    all_goals simp_all
    grind
  · step*

end spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop
