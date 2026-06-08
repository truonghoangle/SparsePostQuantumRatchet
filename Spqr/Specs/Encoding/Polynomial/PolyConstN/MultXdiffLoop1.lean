/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.General
import Spqr.Specs.Encoding.Polynomial.PolyConstN.MultXdiffLoopBody1

/-!
# Spec theorem for `PolyConst::mult_xdiff`: loop 1

The Rust function `PolyConst::mult_xdiff` (in `src/encoding/polynomial.rs`, lines 415:4-454:5)
computes the product of a constant-sized polynomial `self` by the linear factor `(x − difference)`
in GF(2¹⁶)[X].  Since GF(2¹⁶) has characteristic 2, subtraction coincides with addition, so
`(x − difference) = (x + difference)`.

The multiplication is decomposed into two parts:
  1. `xp = x · self`:  shift every coefficient of `self` up by one position.
  2. `dp = difference · self`:  multiply every coefficient of `self` by `difference`.

The final result is `xp − dp` (equivalently `xp + dp` in characteristic 2), computed by a second
loop (loop 1).

This file specifies **loop 1** — the `loop` fixed-point wrapper around the body
(`MultXdiffLoopBody1.body_spec`), which iterates over indices `i = 0, 1, …, N−1` and computes
the element-wise subtraction `xp[i] := xp[i] − dp[i]` in GF(2¹⁶).

At each step, the body processes index `i`:
  1. Reads `xp[i]` and `dp[i]`.
  2. Computes `xp[i] := xp[i] − dp[i]` via `const_sub`, which in characteristic 2 is the same
     as XOR (addition).
  3. Advances the loop counter: `i' = i + 1`.

**Closed-form postcondition** (after all iterations from `i` to `N−1`):

  - **Processed positions** (`i ≤ j < N`): the GF(2¹⁶) subtraction has been applied:
      `xpR[j].toGF216 = xp[j].toGF216 − dp[j].toGF216`
    where the subtraction is in `GF216 = GaloisField 2 16` (which coincides with addition in
    characteristic 2).

  - **Unprocessed positions** (`j < i`): the array is unchanged from the input:
      `xpR[j]? = xp[j]?`

At the call site in `mult_xdiff`, the loop starts with `i = 0`, so all positions are processed
and the result is the complete element-wise subtraction `xp − dp`, giving the final polynomial
product `(x − difference) · self`.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition and is bitwise XOR:
  `a − b = a + b = a ⊕ b`,
so the `const_sub` used in the loop body is identical to XOR.

**Source**: spqr/src/encoding/polynomial.rs (lines 446:12-451:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyConst.mult_xdiff_loop1

/--
**Spec theorem for `encoding.polynomial.PolyConst.mult_xdiff_loop1`**:

The full second loop in `PolyConst::mult_xdiff`, which computes the element-wise subtraction
`xp[i] := xp[i] − dp[i]` in GF(2¹⁶).  Given the `dp` array (scaled coefficients) and the
running array `xp` (which initially holds the shifted coefficients from loop 0), the loop
processes all indices from `i` to `N−1` and returns the completed array `xpR` satisfying:

• The function always succeeds (no panic) since all array accesses and updates are bounded by `N`,
  and the loop counter `i < N` is checked before any operation.

• **Subtraction postcondition** (every position `j ∈ [i, N)` holds the GF(2¹⁶) difference):
    `∀ j, i.val ≤ j → j < N.val →
      xpR[j].toGF216 = xp[j].toGF216 − dp[j].toGF216`
  where the subtraction is in `GF216 = GaloisField 2 16` (which coincides with addition in
  characteristic 2).

• **Unchanged positions** (positions `j < i` are untouched):
    `∀ j, j < i.val → xpR[j]? = xp[j]?`

**Source**: spqr/src/encoding/polynomial.rs (lines 446:12-451:13)
-/
@[step]
theorem loop_spec
    {N : Usize}
    (xp : Array GF16 N)
    (dp : Array GF16 N) (i : Usize)
    (h_i_le_N : i.val ≤ N.val) :
    mult_xdiff_loop1 xp dp i
      ⦃ xpR =>
        (∀ (j : Nat), i.val ≤ j → j < N.val →
          ∀ (hj : j < xpR.val.length),
            (xpR.val.get ⟨j, hj⟩).toGF216 =
              (xp.val[j]!).toGF216 - (dp.val[j]!).toGF216) ∧
        (∀ (j : Nat), j < i.val →
          xpR.val[j]? = xp.val[j]?) ⦄ := by
  unfold mult_xdiff_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : (Array GF16 N) × Usize) =>
                  N.val - p.2.val)
    (inv := fun (p : (Array GF16 N) × Usize) =>
        let xp' := p.1
        let i' := p.2
        i.val ≤ i'.val ∧
        i'.val ≤ N.val ∧
        -- processed positions: subtraction applied
        (∀ (j : Nat), i.val ≤ j → j < i'.val →
          ∀ (hj : j < xp'.val.length),
            (xp'.val.get ⟨j, hj⟩).toGF216 =
              (xp.val[j]!).toGF216 - (dp.val[j]!).toGF216) ∧
        -- non-processed positions: unchanged from input xp
        (∀ (j : Nat), ¬(i.val ≤ j ∧ j < i'.val) →
          xp'.val[j]? = xp.val[j]?))
  · -- Body step: prove invariant is preserved and measure decreases
    rintro ⟨xp', i'⟩
      ⟨h_i_le_i', h_i'_le_N, h_xp_proc, h_xp_rest⟩
    simp only [] at h_i_le_i' h_i'_le_N h_xp_proc h_xp_rest ⊢
    have h_body := body_spec dp xp' i'
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done xp_r =>
      -- Done case: loop terminates, array unchanged
      simp only [] at h_cf ⊢
      obtain ⟨h_xp_eq, h_not_lt⟩ := h_cf
      subst h_xp_eq
      push Not at h_not_lt
      -- i' ≥ N (from ¬(i' < N)), combined with i' ≤ N gives i' = N
      refine ⟨?_, ?_⟩
      · -- All positions i ≤ j < N were processed
        intro j hj hj_lt hj'
        exact h_xp_proc j hj (by omega) hj'
      · -- Positions j < i unchanged
        intro j hj
        exact h_xp_rest j (by intro ⟨h1, _⟩; omega)
    | ControlFlow.cont (xp1, i2) =>
      -- Cont case: one more iteration processed
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_i2, h_xp_upd, h_xp_frame⟩ := h_cf
      constructor
      · -- Invariant preserved (4 conjuncts)
        refine ⟨by omega, by omega, ?_, ?_⟩
        · -- Processed positions extended by one
          intro j hj hj_lt_i2 hj'
          by_cases hjk : j < i'.val
          · -- j was already processed: chain frame + old invariant
            have h_ne : j ≠ i'.val := by omega
            have h_frame := h_xp_frame j h_ne
            have hj_old : j < xp'.val.length := by
              simp only [List.Vector.length_val]; omega
            have h_get := list_get_of_getElem?_eq h_frame hj' hj_old
            simp only [List.get_eq_getElem] at h_get h_xp_proc ⊢
            rw [h_get]; exact h_xp_proc j hj hjk hj_old
          · -- j = i': newly processed by body
            have hj_eq : j = i'.val := by omega
            subst hj_eq
            -- From invariant: xp'[i'] is still unchanged from input xp
            have h_unchanged := h_xp_rest i'.val
              (by intro ⟨_, h⟩; exact absurd h (lt_irrefl _))
            -- Both arrays have length N, so i' is in bounds for both
            have h_len_xp' : i'.val < xp'.val.length := by
              simp only [List.Vector.length_val]; omega
            have h_len_xp : i'.val < xp.val.length := by
              simp only [List.Vector.length_val]; omega
            -- Chain: xp'[i']! = xp[i']! (unchanged position)
            grind
        · -- Non-processed positions still unchanged
          intro j hj
          have h_ne : j ≠ i'.val := by
            intro heq; apply hj; subst heq; exact ⟨h_i_le_i', by omega⟩
          rw [h_xp_frame j h_ne, h_xp_rest j (by intro ⟨h1, h2⟩; exact hj ⟨h1, by omega⟩)]
      · -- Measure decreases
        omega
  · -- Initial invariant: no positions processed yet, all unchanged
    refine ⟨le_refl _, h_i_le_N, fun _ h1 h2 => absurd h2 (by grind), fun _ _ => rfl⟩

end spqr.encoding.polynomial.PolyConst.mult_xdiff_loop1
