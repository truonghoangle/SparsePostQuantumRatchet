/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.PolyConstN.LagrangeInterpolatePtLoop0
import Spqr.Specs.Encoding.Polynomial.PolyConstN.LagrangePolysForCompletePointsLoopBody1

/-!
# Spec theorem for `lagrange_polys_for_complete_points`: loop 1

The Rust function `lagrange_polys_for_complete_points` (in `src/encoding/polynomial.rs`, lines
469:0-496:1) precomputes the array of Lagrange basis polynomials for the "complete points" —
evaluation points `0, 1, …, N−1` in GF(2¹⁶) with `y`-coordinate `GF16::ONE`.  After the first loop
(loop 0, lines 477:8-482:9) initialises the point array `ones` so that `ones[j].x.value = j` and
`ones[j].y = GF16::ONE`, the second loop (loop 1, lines 488:8-493:9) fills the output array `out`
with the Lagrange basis polynomials:

```
while i < N {
    out[i] = PolyConst::<N>::lagrange_interpolate_pt(&ones, i);
    i += 1;
}
```

This file specifies **loop 1** — the `loop` fixed-point wrapper around the body
(`LagrangePolysForCompletePointsLoopBody1.body_spec`), which iterates over indices `i = 0, 1, …,
N−1` and fills each slot of `out` with the corresponding scaled Lagrange basis polynomial.

At each step, the body processes index `i`:
  1. **Done** (`i ≥ N`): the loop terminates and `out` is returned unchanged.
  2. **Continue** (`i < N`):
     a. Converts `ones` to a slice `s` via `Array.to_slice`.
     b. Calls `PolyConst.lagrange_interpolate_pt N s i` to compute the `i`-th scaled Lagrange
        basis polynomial for the evaluation points in `ones`.
     c. Updates `out[i] := pc` with the computed polynomial.
     d. Advances the loop counter: `i1 = i + 1`.

**Closed-form postcondition** (after all iterations from `i` to `N−1`):

  - **Processed positions** (`i ≤ j < N`): the `j`-th Lagrange basis polynomial has been stored:
      `listToGF216Poly (result[j].coefficients.val) =
         C (ones[j].y.toGF216 *
             (lagrangeDenomProd ones[j].x (ones.take N) 0) ^ (2¹⁶ − 2)) *
           condProdLinearFactors ones[j].x (ones.take N) 0`
    Semantically, each `result[j]` is the `j`-th term of the Lagrange interpolation formula for
    the points `ones[0], …, ones[N−1]`.

  - **Unprocessed positions** (`j < i`): the array is unchanged from the input:
      `result[j]? = out[j]?`

At the call site in `lagrange_polys_for_complete_points`, the loop starts with `i = 0`, so all
positions are processed and every entry contains the corresponding Lagrange basis polynomial.

When the `x`-coordinates are pairwise distinct (which they are for the "complete points"
`0, 1, …, N−1` in GF(2¹⁶)), the denominator `lagrangeDenomProd` is nonzero and the Fermat-style
exponentiation `(lagrangeDenomProd …) ^ (2¹⁶ − 2)` yields the multiplicative inverse, so the
scaling factor reduces to `ones[j].y / ∏_{k ≠ j} (ones[j].x − ones[k].x)`.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition (`a − b = a + b = a ⊕ b`),
so the linear factors `(X − ones[k].x)` and the differences `ones[j].x − ones[k].x` are
equivalently `(X + ones[k].x)` and `ones[j].x + ones[k].x`.

**Source**: spqr/src/encoding/polynomial.rs (lines 488:8-493:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop1

/-! ## Helper lemmas -/

/--
Transfer a `List.get`-indexed value through a `List.getElem?` equality.
If `xs[k]? = ys[k]?` and both indices are in bounds, then `xs.get ⟨k, _⟩ = ys.get ⟨k, _⟩`.
-/
private lemma list_get_of_getElem?_eq {T : Type} {xs ys : List T}
    {k : Nat}
    (h : xs[k]? = ys[k]?) (hx : k < xs.length) (hy : k < ys.length) :
    xs.get ⟨k, hx⟩ = ys.get ⟨k, hy⟩ := by
  have h1 : xs[k]? = some (xs.get ⟨k, hx⟩) := List.getElem?_eq_getElem hx
  have h2 : ys[k]? = some (ys.get ⟨k, hy⟩) := List.getElem?_eq_getElem hy
  rw [h1, h2] at h
  exact Option.some_injective _ h

/--
**Spec theorem for `encoding.polynomial.lagrange_polys_for_complete_points_loop1`**:

The full `while i < N` Lagrange basis polynomial computation loop in
`lagrange_polys_for_complete_points`, which fills `out[j]` with the `j`-th scaled Lagrange
basis polynomial for each index `j` from `i` to `N−1`.  Given the point array `ones` of size
`N`, the output array `out` of size `N`, and the starting index `i`, the loop processes all
indices from `i` to `N−1` and returns the completed array `result` satisfying:

• The function always succeeds (no panic) provided the preconditions hold, since all array
  accesses and updates are bounded by `N`, the `Array.to_slice` and
  `lagrange_interpolate_pt` calls succeed under the given constraints, and the loop counter
  `i < N` is checked before any operation.

• **Lagrange postcondition** (every position `j ∈ [i, N)` has been filled):
    `∀ j, i.val ≤ j → j < N.val →
      listToGF216Poly (result[j].coefficients.val) =
        C (ones[j].y.toGF216 *
            (lagrangeDenomProd ones[j].x (ones.take N) 0) ^ (2¹⁶ − 2)) *
          condProdLinearFactors ones[j].x (ones.take N) 0`
  Each `result[j]` is the `j`-th term of the standard Lagrange interpolation formula
  for the points `ones[0], …, ones[N−1]`.

• **Unchanged positions** (positions `j < i` are untouched):
    `∀ j, j < i.val → result[j]? = out[j]?`

**Source**: spqr/src/encoding/polynomial.rs (lines 488:8-493:9)
-/
@[step]
theorem loop_spec
    {N : Usize}
    (ones : Array Pt N)
    (out : Array (PolyConst N) N)
    (i : Usize)
    (h_N_pos : 0 < N.val)
    (h_i_le_N : i.val ≤ N.val) :
    lagrange_polys_for_complete_points_loop1 ones out i
      ⦃ result =>
        (∀ (j : Nat), i.val ≤ j → j < N.val →
          ∀ (hj : j < result.val.length) (hjo : j < ones.val.length),
            listToGF216Poly (result.val.get ⟨j, hj⟩).coefficients.val =
              C ((ones.val.get ⟨j, hjo⟩).y.toGF216 *
                  (lagrangeDenomProd (ones.val.get ⟨j, hjo⟩).x
                    (ones.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
                condProdLinearFactors (ones.val.get ⟨j, hjo⟩).x
                  (ones.val.take N.val) 0) ∧
        (∀ (j : Nat), j < i.val →
          result.val[j]? = out.val[j]?) ⦄ := by
  unfold lagrange_polys_for_complete_points_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : (Array (PolyConst N) N) × Usize) =>
                  N.val - p.2.val)
    (inv := fun (p : (Array (PolyConst N) N) × Usize) =>
        let out' := p.1
        let i' := p.2
        i.val ≤ i'.val ∧
        i'.val ≤ N.val ∧
        -- processed positions: Lagrange basis polynomials stored
        (∀ (j : Nat), i.val ≤ j → j < i'.val →
          ∀ (hj : j < out'.val.length) (hjo : j < ones.val.length),
            listToGF216Poly (out'.val.get ⟨j, hj⟩).coefficients.val =
              C ((ones.val.get ⟨j, hjo⟩).y.toGF216 *
                  (lagrangeDenomProd (ones.val.get ⟨j, hjo⟩).x
                    (ones.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
                condProdLinearFactors (ones.val.get ⟨j, hjo⟩).x
                  (ones.val.take N.val) 0) ∧
        -- non-processed positions: unchanged from input out
        (∀ (j : Nat), ¬(i.val ≤ j ∧ j < i'.val) →
          out'.val[j]? = out.val[j]?))
  · -- Body step: prove invariant is preserved and measure decreases
    rintro ⟨out', i'⟩
      ⟨h_i_le_i', h_i'_le_N, h_proc, h_rest⟩
    simp only [] at h_i_le_i' h_i'_le_N h_proc h_rest ⊢
    have h_body := body_spec ones out' i' h_N_pos
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done out_r =>
      -- Done case: loop terminates, array unchanged
      simp only [] at h_cf ⊢
      obtain ⟨h_eq, h_not_lt⟩ := h_cf
      subst h_eq
      push Not at h_not_lt
      -- i' ≥ N (from ¬(i' < N)), combined with i' ≤ N gives i' = N
      refine ⟨?_, ?_⟩
      · -- All positions i ≤ j < N were processed
        intro j hj hj_lt hj' hjo
        exact h_proc j hj (by omega) hj' hjo
      · -- Positions j < i unchanged
        intro j hj
        exact h_rest j (by intro ⟨h1, _⟩; omega)
    | ControlFlow.cont (out1, i1) =>
      -- Cont case: one more iteration processed
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_i1, h_upd, h_frame⟩ := h_cf
      constructor
      · -- Invariant preserved (4 conjuncts)
        refine ⟨by omega, by omega, ?_, ?_⟩
        · -- Processed positions extended by one
          intro j hj hj_lt_i1 hj' hjo
          by_cases hjk : j < i'.val
          · -- j was already processed: chain frame + old invariant
            have h_ne : j ≠ i'.val := by omega
            have h_fr := h_frame j h_ne
            have hj_old : j < out'.val.length := by
              simp only [List.Vector.length_val]; omega
            have h_get := list_get_of_getElem?_eq h_fr hj' hj_old
            simp only [List.get_eq_getElem] at h_get h_proc ⊢
            rw [h_get]; exact h_proc j hj hjk hj_old hjo
          · -- j = i': newly processed by body
            have hj_eq : j = i'.val := by omega
            subst hj_eq
            exact h_upd hj' hjo
        · -- Non-processed positions still unchanged
          intro j hj
          have h_ne : j ≠ i'.val := by
            intro heq; apply hj; subst heq; exact ⟨h_i_le_i', by omega⟩
          rw [h_frame j h_ne, h_rest j (by intro ⟨h1, h2⟩; exact hj ⟨h1, by omega⟩)]
      · -- Measure decreases
        omega
  · -- Initial invariant: no positions processed yet, all unchanged
    refine ⟨le_refl _, h_i_le_N, fun _ h1 h2 => absurd h2 (by grind), fun _ _ => rfl⟩

end spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop1
