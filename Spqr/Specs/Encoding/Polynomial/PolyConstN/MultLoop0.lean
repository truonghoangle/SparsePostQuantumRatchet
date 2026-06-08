/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.General
import Spqr.Specs.Encoding.Polynomial.PolyConstN.MultLoopBody0

/-!
# Spec theorem for `PolyConst::mult`: loop 0

The Rust function `PolyConst::mult` (in `src/encoding/polynomial.rs`, lines 398:4-410:5)
computes the scalar product of a constant-sized polynomial `self` by a field element `m`
in GF(2¹⁶)[X].  The result is a new polynomial whose coefficients are each multiplied by `m`.

Concretely, `mult self m` copies `self.coefficients` into a mutable array `out` and then runs
a `while i < N` loop that replaces each coefficient `out[i]` with `out[i].const_mul(m)`.

This file specifies **loop 0** — the `loop` fixed-point wrapper around the body
(`MultLoopBody0.body_spec`), which iterates over indices `i = 0, 1, …, N−1` and
scales each coefficient of the output array by the field element `m`.

At each step, the body processes index `i`:
  1. Reads `a[i]` (the current coefficient).
  2. Computes `g1 = a[i].const_mul(m)` via `const_mul`, multiplying the coefficient by `m`
     in GF(2¹⁶).
  3. Updates `a[i] := g1`.
  4. Advances the loop counter: `i' = i + 1`.

**Closed-form postcondition** (after all iterations from `i` to `N−1`):

  - **Processed positions** (`i ≤ j < N`): the GF(2¹⁶) scaling has been applied:
      `result[j].toGF216 = a[j].toGF216 * m.toGF216`
    where the multiplication is in `GF216 = GaloisField 2 16`.

  - **Unprocessed positions** (`j < i`): the array is unchanged from the input:
      `result[j]? = a[j]?`

At the call site in `mult`, the loop starts with `i = 0`, so all positions are processed
and the result is the complete element-wise scaling by `m`, giving the final polynomial
product `m · self`.

In GF(2¹⁶) (characteristic 2), multiplication is carry-less polynomial multiplication modulo the
irreducible polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 403:8-408:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyConst.mult_loop

/--
**Spec theorem for `encoding.polynomial.PolyConst.mult_loop`**:

The full loop in `PolyConst::mult`, which scales every coefficient of the array `a` by the
field element `m` in GF(2¹⁶).  Given the coefficient array `a` of size `N`, the field element
`m`, and the starting index `i`, the loop processes all indices from `i` to `N−1` and returns
the completed array `result` satisfying:

• The function always succeeds (no panic) since all array accesses and updates are bounded by `N`,
  and the loop counter `i < N` is checked before any operation.

• **Scaling postcondition** (every position `j ∈ [i, N)` holds the GF(2¹⁶) product):
    `∀ j, i.val ≤ j → j < N.val →
      result[j].toGF216 = a[j].toGF216 * m.toGF216`
  where the multiplication is in `GF216 = GaloisField 2 16`.

• **Unchanged positions** (positions `j < i` are untouched):
    `∀ j, j < i.val → result[j]? = a[j]?`

**Source**: spqr/src/encoding/polynomial.rs (lines 403:8-408:9)
-/
@[step]
theorem loop_spec
    {N : Usize}
    (m : GF16) (i : Usize)
    (a : Array GF16 N)
    (h_i_le_N : i.val ≤ N.val) :
    mult_loop m i a
      ⦃ result =>
        (∀ (j : Nat), i.val ≤ j → j < N.val →
          ∀ (hj : j < result.val.length),
            (result.val.get ⟨j, hj⟩).toGF216 =
              (a.val[j]!).toGF216 * m.toGF216) ∧
        (∀ (j : Nat), j < i.val →
          result.val[j]? = a.val[j]?) ⦄ := by
  unfold mult_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Usize × (Array GF16 N)) =>
                  N.val - p.1.val)
    (inv := fun (p : Usize × (Array GF16 N)) =>
        let i' := p.1
        let a' := p.2
        i.val ≤ i'.val ∧
        i'.val ≤ N.val ∧
        -- processed positions: scaling applied
        (∀ (j : Nat), i.val ≤ j → j < i'.val →
          ∀ (hj : j < a'.val.length),
            (a'.val.get ⟨j, hj⟩).toGF216 =
              (a.val[j]!).toGF216 * m.toGF216) ∧
        -- non-processed positions: unchanged from input a
        (∀ (j : Nat), ¬(i.val ≤ j ∧ j < i'.val) →
          a'.val[j]? = a.val[j]?))
  · -- Body step: prove invariant is preserved and measure decreases
    rintro ⟨i', a'⟩
      ⟨h_i_le_i', h_i'_le_N, h_a_proc, h_a_rest⟩
    simp only [] at h_i_le_i' h_i'_le_N h_a_proc h_a_rest ⊢
    have h_body := body_spec m i' a'
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done a_r =>
      -- Done case: loop terminates, array unchanged
      simp only [] at h_cf ⊢
      obtain ⟨h_a_eq, h_not_lt⟩ := h_cf
      subst h_a_eq
      push Not at h_not_lt
      -- i' ≥ N (from ¬(i' < N)), combined with i' ≤ N gives i' = N
      refine ⟨?_, ?_⟩
      · -- All positions i ≤ j < N were processed
        intro j hj hj_lt hj'
        exact h_a_proc j hj (by omega) hj'
      · -- Positions j < i unchanged
        intro j hj
        exact h_a_rest j (by intro ⟨h1, _⟩; omega)
    | ControlFlow.cont (i1, a1) =>
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
            have hj_old : j < a'.val.length := by
              simp only [List.Vector.length_val]; omega
            have h_get := list_get_of_getElem?_eq h_fr hj' hj_old
            simp only [List.get_eq_getElem] at h_get h_a_proc ⊢
            rw [h_get]; exact h_a_proc j hj hjk hj_old
          · -- j = i': newly processed by body
            have hj_eq : j = i'.val := by omega
            subst hj_eq
            -- From invariant: a'[i'] is still unchanged from input a
            have h_unchanged := h_a_rest i'.val
              (by intro ⟨_, h⟩; exact absurd h (lt_irrefl _))
            -- Both arrays have length N, so i' is in bounds for both
            have h_len_a' : i'.val < a'.val.length := by
              simp only [List.Vector.length_val]; omega
            have h_len_a : i'.val < a.val.length := by
              simp only [List.Vector.length_val]; omega
            -- Chain: a'[i']! = a[i']! (unchanged position)
            grind
        · -- Non-processed positions still unchanged
          intro j hj
          have h_ne : j ≠ i'.val := by
            intro heq; apply hj; subst heq; exact ⟨h_i_le_i', by omega⟩
          rw [h_frame j h_ne, h_a_rest j (by intro ⟨h1, h2⟩; exact hj ⟨h1, by omega⟩)]
      · -- Measure decreases
        omega
  · -- Initial invariant: no positions processed yet, all unchanged
    refine ⟨le_refl _, h_i_le_N, fun _ h1 h2 => absurd h2 (by grind), fun _ _ => rfl⟩

end spqr.encoding.polynomial.PolyConst.mult_loop
