/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.GF16.ConstMul

/-!
# Spec theorem for `PolyConst::mult_xdiff`: loop body 0

The Rust function `PolyConst::mult_xdiff` (in `src/encoding/polynomial.rs`, lines 415:4-454:5)
computes the product of a constant-sized polynomial `self` by the linear factor `(x − difference)`
in GF(2¹⁶)[X].  Since GF(2¹⁶) has characteristic 2, subtraction coincides with addition, so
`(x − difference) = (x + difference)`.

The multiplication is decomposed into two parts:
  1. `xp = x · self`:  shift every coefficient of `self` up by one position.
  2. `dp = difference · self`:  multiply every coefficient of `self` by `difference`.

The final result is `xp − dp` (equivalently `xp + dp` in characteristic 2), computed by a second
loop (loop 1).

This file specifies **loop body 0** — one step of the first loop (lines 430:12-440:13), which
simultaneously builds the `xp` and `dp` arrays.  The extracted Lean function
`encoding.polynomial.PolyConst.mult_xdiff_loop0.body` performs one iteration of the `while i < N`
loop:

  1. **Done** (`i1 ≥ N`): the loop terminates and `(xp, dp)` are returned unchanged.
  2. **Continue** (`i1 < N`):
     a. If `i1 < i` (where `i = N − 1`): sets `xp[i1 + 1] := a[i1]`, shifting the coefficient
        at position `i1` up by one degree for the `x · poly` contribution.
     b. Computes `dp[i1] := a[i1] · difference` via `const_mul`, filling in the `d · poly`
        contribution at position `i1`.
     c. Advances the loop counter: `i1' = i1 + 1`.

At the end of the full loop (after all `N` iterations), the arrays satisfy:
  - `xp[0] = 0`, and `xp[j+1] = a[j]` for `0 ≤ j < N − 1`  (i.e. `x · poly`).
  - `dp[j] = a[j] · difference` for `0 ≤ j < N`  (i.e. `difference · poly`).

In GF(2¹⁶) (characteristic 2), multiplication is carry-less polynomial multiplication modulo the
irreducible polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 430:12-440:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyConst.mult_xdiff_loop0

/--
**Spec theorem for `encoding.polynomial.PolyConst.mult_xdiff_loop0.body`**:

One step of the first loop in `PolyConst::mult_xdiff`, which simultaneously constructs the
`x · poly` array `xp` (shifted coefficients) and the `difference · poly` array `dp` (scaled
coefficients).  Given the original coefficient array `a` of size `N`, the field element
`difference`, the running arrays `xp` and `dp` (both of size `N`), and the loop counter `i1`,
the body processes one index:

• The function always succeeds (no panic) provided `i.val < N.val` holds, since all array
  accesses and updates are bounded by `N`, and the loop counter `i1 < N` is checked before any
  operation.

• In the **done** case (`i1 ≥ N`):
    `xp' = xp ∧ dp' = dp` — both arrays are returned unchanged.

• In the **cont** case (`i1 < N`):
    - The loop counter has advanced: `i2.val = i1.val + 1`.
    - The `dp` array is updated at position `i1` with the GF(2¹⁶) product:
        `dp1[i1].toGF216 = a[i1].toGF216 * difference.toGF216`
      where the multiplication is in `GF216 = GaloisField 2 16`.  All other positions are
      unchanged: `dp1[j]? = dp[j]?` for `j ≠ i1`.
    - When `i1 < i` (i.e. `i1 < N − 1`): the `xp` array is updated at position `i1 + 1`
      with the coefficient shift:
        `xp1[i1 + 1] = a[i1]`
      and all other positions are unchanged: `xp1[j]? = xp[j]?` for `j ≠ i1 + 1`.
    - When `i1 ≥ i` (i.e. `i1 = N − 1`): `xp1 = xp` — the `xp` array is left unchanged
      (position `N` would be out of bounds, and the leading coefficient was asserted to be
      zero by the overflow check).

**Source**: spqr/src/encoding/polynomial.rs (lines 430:12-440:13)
-/
@[step]
theorem body_spec
    {N : Usize}
    (i : Usize) (a : Array GF16 N)
    (difference : GF16) (xp : Array GF16 N)
    (dp : Array GF16 N) (i1 : Usize)
    (h_i_lt_N : i.val < N.val) :
    body i a difference xp dp i1 ⦃ cf =>
      match cf with
      | ControlFlow.done (xp', dp') =>
          xp' = xp ∧ dp' = dp ∧ ¬ (i1.val < N.val)
      | ControlFlow.cont (xp1, dp1, i2) =>
          i1.val < N.val ∧
          i2.val = i1.val + 1 ∧
          -- dp update: position i1 gets the GF(2¹⁶) product a[i1] * difference
          (∀ (h_idx : i1.val < dp1.val.length),
            (dp1.val.get ⟨i1.val, h_idx⟩).toGF216 =
              (a.val[i1.val]!).toGF216 * difference.toGF216) ∧
          (∀ (j : Nat), j ≠ i1.val → dp1.val[j]? = dp.val[j]?) ∧
          -- xp update: conditional coefficient shift
          (i1.val < i.val →
            (∀ (h_idx : i1.val + 1 < xp1.val.length),
              xp1.val.get ⟨i1.val + 1, h_idx⟩ = a.val[i1.val]!) ∧
            ∀ (j : Nat), j ≠ i1.val + 1 → xp1.val[j]? = xp.val[j]?) ∧
          (¬ i1.val < i.val → xp1 = xp) ⦄ := by
  unfold body
  by_cases h_lt : i1.val < N.val
  · -- Continue case: i1 < N
    simp only [UScalar.lt_equiv, h_lt, ↓reduceIte, not_true_eq_false, and_false,
      List.Vector.length_val, List.get_eq_getElem, getElem!_pos, forall_true_left, ne_eq, not_lt,
      true_and]
    by_cases h_lt_i : i1.val < i.val
    · -- xp shift case: i1 < i (= N − 1), so i1 + 1 < N
      simp only [h_lt_i, ↓reduceIte, bind_assoc, forall_const, isEmpty_Prop, not_le,
        IsEmpty.forall_iff, and_true]
      have h_i1p1_lt_N : i1.val + 1 < N.val := by omega
      step*
      all_goals simp_all
    · -- xp unchanged case: i1 ≥ i
      simp only [h_lt_i, ↓reduceIte, bind_tc_ok, IsEmpty.forall_iff, true_and]
      step*
      all_goals simp_all
  · -- Done case: i1 ≥ N
    step*

end spqr.encoding.polynomial.PolyConst.mult_xdiff_loop0
