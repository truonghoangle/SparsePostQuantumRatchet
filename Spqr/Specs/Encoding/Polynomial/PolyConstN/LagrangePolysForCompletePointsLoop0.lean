/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.PolyConstN.LagrangePolysForCompletePointsLoopBody0

/-!
# Spec theorem for `lagrange_polys_for_complete_points`: loop 0

The Rust function `lagrange_polys_for_complete_points` (in `src/encoding/polynomial.rs`, lines
469:0-496:1) precomputes the array of Lagrange basis polynomials for the "complete points" —
evaluation points `0, 1, …, N−1` in GF(2¹⁶) with `y`-coordinate `GF16::ONE`.  The function begins
by constructing an array `ones` of `N` copies of `Pt { x: GF16::ZERO, y: GF16::ONE }`, then runs a
`while i < N` loop (lines 477:8-482:9) that sets `ones[i].x.value = i as u16` for each index `i`.

This file specifies **loop 0** — the `loop` fixed-point wrapper around the body
(`LagrangePolysForCompletePointsLoopBody0.body_spec`), which iterates over indices `i = 0, 1, …,
N−1` and sets the `x`-coordinate of each point to the corresponding GF(2¹⁶) element.

At each step, the body processes index `i`:
  1. **Done** (`i ≥ N`): the loop terminates and `ones` is returned unchanged.
  2. **Continue** (`i < N`):
     a. Updates `ones[i].x.value := i` (cast from `usize` to `u16`).
     b. The `y` field of `ones[i]` is set to `GF16::ONE`.
     c. All other entries `ones[j]` for `j ≠ i` are left unchanged.
     d. Advances the loop counter: `i1 = i + 1`.

**Closed-form postcondition** (after all iterations from `i` to `N−1`):

  - **Processed positions** (`i ≤ j < N`): the `x`-coordinate has been set:
      `result[j].x.value.val = j` and `result[j].y = GF16.ONE`
    Equivalently, lifting the `x`-coordinate into `GF216`:
      `result[j].x.toGF216 = Nat.toGF216 j`.

  - **Unprocessed positions** (`j < i`): the array is unchanged from the input:
      `result[j]? = ones[j]?`

At the call site in `lagrange_polys_for_complete_points`, the loop starts with `i = 0`, so all
positions are processed and every entry satisfies `ones[j].x.value.val = j` and
`ones[j].y = GF16.ONE`.

In GF(2¹⁶), the elements `0, 1, …, N−1` (for `N ≤ 2¹⁶`) are pairwise distinct because the
canonical map `Nat → GF(2¹⁶)` is injective on `{0, …, 2¹⁶ − 1}` (each natural number below `2¹⁶`
has a unique binary polynomial representative of degree < 16).

**Source**: spqr/src/encoding/polynomial.rs (lines 477:8-482:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop0

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
**Spec theorem for `encoding.polynomial.lagrange_polys_for_complete_points_loop0`**:

The full `while i < N` initialisation loop in `lagrange_polys_for_complete_points`, which sets the
`x`-coordinate of each point `ones[j]` to the GF(2¹⁶) element with raw value `j`.  Given the
point array `ones` of size `N`, and the starting index `i`, the loop processes all indices from
`i` to `N−1` and returns the completed array `result` satisfying:

• The function always succeeds (no panic) provided the preconditions hold, since all array
  accesses and updates are bounded by `N`, and the loop counter `i < N` is checked before any
  operation.

• **Initialisation postcondition** (every position `j ∈ [i, N)` has been set):
    `∀ j, i.val ≤ j → j < N.val →
      result[j].x.value.val = j ∧ result[j].y = GF16.ONE`
  Equivalently, lifting the `x`-coordinate into `GF216`:
    `result[j].x.toGF216 = Nat.toGF216 j`.

• **Unchanged positions** (positions `j < i` are untouched):
    `∀ j, j < i.val → result[j]? = ones[j]?`

**Source**: spqr/src/encoding/polynomial.rs (lines 477:8-482:9)
-/
@[step]
theorem loop_spec
    {N : Usize}
    (ones : Array Pt N)
    (i : Usize)
    (h_N_bound : N.val ≤ 65536)
    (h_i_le_N : i.val ≤ N.val) :
    lagrange_polys_for_complete_points_loop0 ones i
      ⦃ result =>
        (∀ (j : Nat), i.val ≤ j → j < N.val →
          ∀ (hj : j < result.val.length),
            (result.val.get ⟨j, hj⟩).x.value.val = j ∧
            (result.val.get ⟨j, hj⟩).y = GF16.ONE) ∧
        (∀ (j : Nat), j < i.val →
          result.val[j]? = ones.val[j]?) ⦄ := by
  unfold lagrange_polys_for_complete_points_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : (Array Pt N) × Usize) =>
                  N.val - p.2.val)
    (inv := fun (p : (Array Pt N) × Usize) =>
        let ones' := p.1
        let i' := p.2
        i.val ≤ i'.val ∧
        i'.val ≤ N.val ∧
        -- processed positions: x set, y = ONE
        (∀ (j : Nat), i.val ≤ j → j < i'.val →
          ∀ (hj : j < ones'.val.length),
            (ones'.val.get ⟨j, hj⟩).x.value.val = j ∧
            (ones'.val.get ⟨j, hj⟩).y = GF16.ONE) ∧
        -- non-processed positions: unchanged from input ones
        (∀ (j : Nat), ¬(i.val ≤ j ∧ j < i'.val) →
          ones'.val[j]? = ones.val[j]?))
  · -- Body step: prove invariant is preserved and measure decreases
    rintro ⟨ones', i'⟩
      ⟨h_i_le_i', h_i'_le_N, h_proc, h_rest⟩
    simp only [] at h_i_le_i' h_i'_le_N h_proc h_rest ⊢
    have h_body := body_spec ones' i' h_N_bound
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done ones_r =>
      -- Done case: loop terminates, array unchanged
      simp only [] at h_cf ⊢
      obtain ⟨h_eq, h_not_lt⟩ := h_cf
      subst h_eq
      push Not at h_not_lt
      -- i' ≥ N (from ¬(i' < N)), combined with i' ≤ N gives i' = N
      refine ⟨?_, ?_⟩
      · -- All positions i ≤ j < N were processed
        intro j hj hj_lt hj'
        exact h_proc j hj (by omega) hj'
      · -- Positions j < i unchanged
        intro j hj
        exact h_rest j (by intro ⟨h1, _⟩; omega)
    | ControlFlow.cont (ones1, i1) =>
      -- Cont case: one more iteration processed
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_i1, h_upd, h_frame⟩ := h_cf
      constructor
      · -- Invariant preserved (4 conjuncts)
        refine ⟨by omega, by omega, ?_, ?_⟩
        · -- Processed positions extended by one
          intro j hj hj_lt_i1 hj'
          by_cases hjk : j < i'.val
          · -- j was already processed: chain frame + old invariant
            have h_ne : j ≠ i'.val := by omega
            have h_fr := h_frame j h_ne
            have hj_old : j < ones'.val.length := by
              simp only [List.Vector.length_val]; omega
            have h_get := list_get_of_getElem?_eq h_fr hj' hj_old
            simp only [List.get_eq_getElem] at h_get h_proc ⊢
            rw [h_get]; exact h_proc j hj hjk hj_old
          · -- j = i': newly processed by body
            have hj_eq : j = i'.val := by omega
            subst hj_eq
            exact h_upd hj'
        · -- Non-processed positions still unchanged
          intro j hj
          have h_ne : j ≠ i'.val := by
            intro heq; apply hj; subst heq; exact ⟨h_i_le_i', by omega⟩
          rw [h_frame j h_ne, h_rest j (by intro ⟨h1, h2⟩; exact hj ⟨h1, by omega⟩)]
      · -- Measure decreases
        omega
  · -- Initial invariant: no positions processed yet, all unchanged
    refine ⟨le_refl _, h_i_le_N, fun _ h1 h2 => absurd h2 (by grind), fun _ _ => rfl⟩

end spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop0
