/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Gf.GF16.ConstMul

/-!
# Spec theorem for `PolyConst::mult`: loop body 0

The Rust function `PolyConst::mult` (in `src/encoding/polynomial.rs`, lines 398:4-410:5)
computes the scalar product of a constant-sized polynomial `self` by a field element `m`
in GF(2¹⁶)[X].  The result is a new polynomial whose coefficients are each multiplied by `m`.

Concretely, `mult self m` copies `self.coefficients` into a mutable array `out` and then runs
a `while i < N` loop that replaces each coefficient `out[i]` with `out[i].const_mul(m)`.

This file specifies **loop body 0** — one step of the loop (lines 403:8-408:9), which
updates one coefficient of the output array.  The extracted Lean function
`encoding.polynomial.PolyConst.mult_loop.body` performs one iteration:

  1. **Done** (`i ≥ N`): the loop terminates and the array `a` is returned unchanged.
  2. **Continue** (`i < N`):
     a. Reads `a[i]` (the current coefficient).
     b. Computes `g1 = a[i].const_mul(m)` via `const_mul`, multiplying the coefficient by `m`
        in GF(2¹⁶).
     c. Updates `a[i] := g1`.
     d. Advances the loop counter: `i1 = i + 1`.

At the end of the full loop (after all `N` iterations), the array satisfies:
  - `a[j].toGF216 = self.coefficients[j].toGF216 * m.toGF216` for `0 ≤ j < N`
    (i.e. every coefficient has been scaled by `m`).

In GF(2¹⁶) (characteristic 2), multiplication is carry-less polynomial multiplication modulo the
irreducible polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 403:8-408:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyConst.mult_loop

/--
**Spec theorem for `encoding.polynomial.PolyConst.mult_loop.body`**:

One step of the loop in `PolyConst::mult`, which performs scalar multiplication of each
coefficient by the field element `m` in GF(2¹⁶).  Given the coefficient array `a` of size `N`,
the field element `m`, and the loop counter `i`, the body processes one index:

• The function always succeeds (no panic) since all array accesses and updates are bounded by `N`,
  and the loop counter `i < N` is checked before any operation.

• In the **done** case (`i ≥ N`):
    `a' = a` — the array is returned unchanged.

• In the **cont** case (`i < N`):
    - The loop counter has advanced: `i1.val = i.val + 1`.
    - The array is updated at position `i` with the GF(2¹⁶) product:
        `a1[i].toGF216 = a[i].toGF216 * m.toGF216`
      where the multiplication is in `GF216 = GaloisField 2 16`.  All other positions are
      unchanged: `a1[j]? = a[j]?` for `j ≠ i`.

**Source**: spqr/src/encoding/polynomial.rs (lines 403:8-408:9)
-/
@[step]
theorem body_spec
    {N : Usize}
    (m : GF16) (i : Usize)
    (a : Array GF16 N) :
    body m i a ⦃ cf =>
      match cf with
      | ControlFlow.done a' =>
          a' = a ∧ ¬ (i.val < N.val)
      | ControlFlow.cont (i1, a1) =>
          i.val < N.val ∧
          i1.val = i.val + 1 ∧
          -- a update: position i gets the GF(2¹⁶) product a[i] * m
          (∀ (h_idx : i.val < a1.val.length),
            (a1.val.get ⟨i.val, h_idx⟩).toGF216 =
              (a.val[i.val]!).toGF216 * m.toGF216) ∧
          (∀ (j : Nat), j ≠ i.val → a1.val[j]? = a.val[j]?) ⦄ := by
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

end spqr.encoding.polynomial.PolyConst.mult_loop
