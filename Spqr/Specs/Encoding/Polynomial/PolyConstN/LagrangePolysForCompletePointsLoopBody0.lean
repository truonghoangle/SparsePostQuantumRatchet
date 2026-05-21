/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Gf.GF16.New
import Spqr.Specs.Encoding.Gf.GF16.ONE
/-!
# Spec theorem for `lagrange_polys_for_complete_points`: loop body 0

The Rust function `lagrange_polys_for_complete_points` (in `src/encoding/polynomial.rs`, lines
469:0-496:1) precomputes the array of Lagrange basis polynomials for the "complete points" —
evaluation points `0, 1, …, N−1` in GF(2¹⁶) with `y`-coordinate `GF16::ONE`.  The function begins
by constructing an array `ones` of `N` copies of `Pt { x: GF16::ZERO, y: GF16::ONE }`, then runs a
`while i < N` loop (lines 477:8-482:9) that sets `ones[i].x.value = i as u16` for each index `i`.

This file specifies **loop body 0** — one iteration of that initialisation loop.  The extracted
Lean function `encoding.polynomial.lagrange_polys_for_complete_points_loop0.body` performs one step:

  1. **Done** (`i ≥ N`): the loop terminates and the array `ones` is returned unchanged.
  2. **Continue** (`i < N`):
     a. Reads `ones[i]` and updates `ones[i].x.value := i` (cast from `usize` to `u16`).
     b. The `y` field of `ones[i]` is set to `GF16::ONE`.
     c. All other entries `ones[j]` for `j ≠ i` are left unchanged.
     d. Advances the loop counter: `i1 = i + 1`.

At the end of the full loop (after `N` iterations starting from `i = 0`), every entry satisfies:
  - `ones[j].x.value.val = j` — the raw `u16` bit pattern is the loop index.
  - `ones[j].y = GF16::ONE` — the `y`-coordinate is the multiplicative identity.

Semantically, `ones[j].x.toGF216 = Nat.toGF216 j` — the `j`-th distinct element of GF(2¹⁶) under
the canonical embedding `Nat.toGF216 = BinaryPoly.toGF216 ∘ natToBinaryPoly`.  These evaluation
points are subsequently used as the "complete points" for Lagrange interpolation in the second loop
of `lagrange_polys_for_complete_points`.

In GF(2¹⁶), the elements `0, 1, …, N−1` (for `N ≤ 2¹⁶`) are pairwise distinct because the
canonical map `Nat → GF(2¹⁶)` is injective on `{0, …, 2¹⁶ − 1}` (each natural number below `2¹⁶`
has a unique binary polynomial representative of degree < 16).

**Source**: spqr/src/encoding/polynomial.rs (lines 477:8-482:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop0

/--
**Spec theorem for `encoding.polynomial.lagrange_polys_for_complete_points_loop0.body`**:

One step of the initialisation loop in `lagrange_polys_for_complete_points`, which sets the
`x`-coordinate of `ones[i]` to the GF(2¹⁶) element with raw value `i`.  Given the point array
`ones` of size `N` and the loop counter `i`, the body processes one index:

• The function always succeeds (no panic) provided the preconditions hold, since:
    1. The array access `ones[i]` is bounded by `i < N`.
    2. The `usize`-to-`u16` cast is safe for `i.val < N.val ≤ 65536`.
    3. The array update `ones[i] := …` is in bounds.
    4. The increment `i + 1` does not overflow `usize`.

• In the **done** case (`i ≥ N`):
    `ones' = ones` — the array is returned unchanged and the loop terminates.

• In the **cont** case (`i < N`):
    - The loop counter has advanced: `i1.val = i.val + 1`.
    - The updated array `ones1` satisfies at position `i`:
        - `ones1[i].x.value.val = i.val` — the `x`-coordinate raw `u16` value equals the
          loop index.
        - `ones1[i].y = GF16.ONE` — the `y`-coordinate is set to the multiplicative identity.
    - All other positions are unchanged:
        `ones1.val[j]? = ones.val[j]?` for `j ≠ i.val`.
    - Equivalently, lifting the `x`-coordinate into `GF216`:
        `ones1[i].x.toGF216 = Nat.toGF216 i.val`
      where the right-hand side is the GF(2¹⁶) element represented by the natural number
      `i.val` under the canonical map `Nat.toGF216 = BinaryPoly.toGF216 ∘ natToBinaryPoly`.

**Source**: spqr/src/encoding/polynomial.rs (lines 477:8-482:9)
-/
@[step]
theorem body_spec
    {N : Usize}
    (ones : Array Pt N)
    (i : Usize)
    (h_N_bound : N.val ≤ 65536) :
    body ones i ⦃ cf =>
      match cf with
      | ControlFlow.done ones' =>
          ones' = ones ∧ ¬ (i.val < N.val)
      | ControlFlow.cont (ones1, i1) =>
          i.val < N.val ∧
          i1.val = i.val + 1 ∧
          (∀ (h_idx : i.val < ones1.val.length),
            (ones1.val.get ⟨i.val, h_idx⟩).x.value.val = i.val ∧
            (ones1.val.get ⟨i.val, h_idx⟩).y = GF16.ONE) ∧
          (∀ (j : Nat), j ≠ i.val → ones1.val[j]? = ones.val[j]?) ⦄ := by
  unfold body
  by_cases h_lt : i.val < N.val
  · -- Continue case: i < N
    simp only [UScalar.lt_equiv, h_lt, ↓reduceIte, not_true_eq_false, and_false,
      List.Vector.length_val, List.get_eq_getElem, forall_true_left, ne_eq,
      true_and]
    step*
    all_goals simp_all [UScalar.cast_val_eq]
    all_goals omega
  · -- Done case: i ≥ N
    step*

end spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop0
