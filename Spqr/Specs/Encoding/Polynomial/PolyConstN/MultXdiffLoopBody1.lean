/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.GF16.ConstSub

/-!
# Spec theorem for `PolyConst::mult_xdiff`: loop body 1

The Rust function `PolyConst::mult_xdiff` (in `src/encoding/polynomial.rs`, lines 415:4-454:5)
computes the product of a constant-sized polynomial `self` by the linear factor `(x − difference)`
in GF(2¹⁶)[X].  Since GF(2¹⁶) has characteristic 2, subtraction coincides with addition, so
`(x − difference) = (x + difference)`.

The multiplication is decomposed into two parts:
  1. `xp = x · self`:  shift every coefficient of `self` up by one position.
  2. `dp = difference · self`:  multiply every coefficient of `self` by `difference`.

The final result is `xp − dp` (equivalently `xp + dp` in characteristic 2), computed by a second
loop (loop 1).

This file specifies **loop body 1** — one step of the second loop (lines 446:12-451:13), which
computes the element-wise subtraction `xp[i] := xp[i] − dp[i]` in GF(2¹⁶).  The extracted Lean
function `encoding.polynomial.PolyConst.mult_xdiff_loop1.body` performs one iteration of the
`while i < N` loop:

  1. **Done** (`i ≥ N`): the loop terminates and `xp` is returned unchanged.
  2. **Continue** (`i < N`):
     a. Reads `xp[i]` and `dp[i]`.
     b. Computes `xp[i] := xp[i] − dp[i]` via `const_sub`, which in characteristic 2 is
        the same as XOR (addition).
     c. Updates `xp` at position `i` with the result.
     d. Advances the loop counter: `i1 = i + 1`.

At the end of the full loop (after all `N` iterations), the array satisfies:
  - `xp[j] = xp_old[j] − dp[j]` for `0 ≤ j < N`  (i.e. `x · poly − difference · poly`).

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition, and both are carry-less
polynomial XOR modulo the irreducible polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 446:12-451:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyConst.mult_xdiff_loop1

/--
**Spec theorem for `encoding.polynomial.PolyConst.mult_xdiff_loop1.body`**:

One step of the second loop in `PolyConst::mult_xdiff`, which performs the element-wise
subtraction `xp[i] := xp[i] − dp[i]` in GF(2¹⁶).  Given the `dp` array (scaled coefficients),
the running array `xp` (which initially holds the shifted coefficients), and the loop counter `i`,
the body processes one index:

• The function always succeeds (no panic) since all array accesses and updates are bounded by `N`,
  and the loop counter `i < N` is checked before any operation.

• In the **done** case (`i ≥ N`):
    `xp' = xp` — the array is returned unchanged.

• In the **cont** case (`i < N`):
    - The loop counter has advanced: `i1.val = i.val + 1`.
    - The `xp` array is updated at position `i` with the GF(2¹⁶) difference:
        `xp'[i].toGF216 = xp[i].toGF216 - dp[i].toGF216`
      where the subtraction is in `GF216 = GaloisField 2 16` (which coincides with addition
      in characteristic 2).  All other positions are unchanged:
        `xp'[j]? = xp[j]?` for `j ≠ i`.

**Source**: spqr/src/encoding/polynomial.rs (lines 446:12-451:13)
-/
@[step]
theorem body_spec
    {N : Usize}
    (dp : Array GF16 N)
    (xp : Array GF16 N) (i : Usize) :
    body dp xp i ⦃ cf =>
      match cf with
      | ControlFlow.done xp' =>
          xp' = xp ∧ ¬ (i.val < N.val)
      | ControlFlow.cont (xp', i1) =>
          i.val < N.val ∧
          i1.val = i.val + 1 ∧
          -- xp update: position i gets the GF(2¹⁶) difference xp[i] − dp[i]
          (∀ (h_idx : i.val < xp'.val.length),
            (xp'.val.get ⟨i.val, h_idx⟩).toGF216 =
              (xp.val[i.val]!).toGF216 - (dp.val[i.val]!).toGF216) ∧
          (∀ (j : Nat), j ≠ i.val → xp'.val[j]? = xp.val[j]?) ⦄ := by
  unfold body
  by_cases h_lt : i.val < N.val
  · -- Continue case: i < N
    simp only [UScalar.lt_equiv, h_lt, ↓reduceIte, not_true_eq_false, and_false,
      List.Vector.length_val, List.get_eq_getElem, getElem!_pos, forall_true_left, ne_eq, not_lt,
      true_and]
    step*
    all_goals simp_all
  · -- Done case: i ≥ N
    step*

end spqr.encoding.polynomial.PolyConst.mult_xdiff_loop1
