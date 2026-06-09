/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.List
import Spqr.Specs.Encoding.Polynomial.PolyConstN.MultXdiffLoopBody0

/-!
# Spec theorem for `PolyConst::mult_xdiff`: loop 0

The Rust function `PolyConst::mult_xdiff` (in `src/encoding/polynomial.rs`, lines 415:4-454:5)
computes the product of a constant-sized polynomial `self` by the linear factor `(x − difference)`
in GF(2¹⁶)[X].  Since GF(2¹⁶) has characteristic 2, subtraction coincides with addition, so
`(x − difference) = (x + difference)`.

The multiplication is decomposed into two parts:
  1. `xp = x · self`:  shift every coefficient of `self` up by one position.
  2. `dp = difference · self`:  multiply every coefficient of `self` by `difference`.

The final result is `xp − dp` (equivalently `xp + dp` in characteristic 2), computed by a second
loop (loop 1).

This file specifies **loop 0** — the `loop` fixed-point wrapper around the body
(`MultXdiffLoopBody0.body_spec`), which iterates over indices `i1 = 0, 1, …, N−1` and
simultaneously constructs the `x · poly` array `xp` (shifted coefficients) and the
`difference · poly` array `dp` (scaled coefficients).

At each step, the body processes index `i1`:
  1. If `i1 < i` (where `i = N − 1`): sets `xp[i1 + 1] := a[i1]`, shifting the coefficient at
     position `i1` up by one degree.
  2. Computes `dp[i1] := a[i1] · difference` via `const_mul`, filling in the scaled coefficient.
  3. Advances the loop counter: `i1' = i1 + 1`.

**Closed-form postcondition** (after all `N` iterations):

  - **dp** (difference · poly): every position `j < N` holds the GF(2¹⁶) product:
      `dp[j].toGF216 = a[j].toGF216 * difference.toGF216`
    where the multiplication is in `GF216 = GaloisField 2 16`.

  - **xp** (x · poly): the shifted coefficients satisfy:
      `xp[j + 1] = a[j]`  for `0 ≤ j < N − 1`  (i.e., `j < i.val`)
    and position 0 (and any out-of-range positions) are unchanged from the input `xp`:
      `xp'[j]? = xp[j]?`  for `j = 0` or `j > i.val`

At the call site in `mult_xdiff`, both `xp` and `dp` are initialised to all-zero arrays
(`Array.repeat N GF16.ZERO`), so the "unchanged" position 0 holds `GF16.ZERO`, giving:
  - `xp'[0] = GF16.ZERO` and `xp'[j+1] = a[j]` for `j < N − 1`  (i.e., `x · poly`).
  - `dp'[j] = a[j] · difference` for all `j < N`  (i.e., `difference · poly`).

In GF(2¹⁶) (characteristic 2), multiplication is carry-less polynomial multiplication modulo the
irreducible polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 430:12-440:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyConst.mult_xdiff_loop0

/--
**Spec theorem for `encoding.polynomial.PolyConst.mult_xdiff_loop0`**:

The full first loop in `PolyConst::mult_xdiff`, which simultaneously constructs the `x · poly`
array `xp` (shifted coefficients) and the `difference · poly` array `dp` (scaled coefficients).
Given the original coefficient array `a` of size `N`, the field element `difference`, and the
running arrays `xp` and `dp` (both of size `N`), the loop processes all indices from `i1` to `N−1`
and returns the completed arrays `(xpR, dpR)` satisfying:

• The function always succeeds (no panic) provided `i.val < N.val` holds, since all array
  accesses and updates are bounded by `N`, and the loop counter `i1 < N` is checked before any
  operation.

• **dp postcondition** (every position holds the scaled coefficient):
    `∀ j < N, dpR[j].toGF216 = a[j].toGF216 * difference.toGF216`
  where the multiplication is in `GF216 = GaloisField 2 16`.

• **xp postcondition** (shifted coefficients):
    `∀ j < i.val, xpR[j + 1] = a[j]`
  where `i = N − 1`.

• **xp unchanged positions**:
    `∀ j, ¬(0 < j ∧ j ≤ i.val) → xpR[j]? = xp[j]?`
  In particular, position 0 is unchanged from the input `xp`.

**Source**: spqr/src/encoding/polynomial.rs (lines 430:12-440:13)
-/
@[step]
theorem loop_spec
    {N : Usize}
    (i : Usize) (a : Array GF16 N)
    (difference : GF16) (xp : Array GF16 N)
    (dp : Array GF16 N) (i1 : Usize)
    (h_i_lt_N : i.val < N.val)
    (h_i1_le_N : i1.val ≤ N.val)
    (h_dp_inv : ∀ (j : Nat), j < i1.val →
        ∀ (hj : j < dp.val.length),
          (dp.val.get ⟨j, hj⟩).toGF216 =
            (a.val[j]!).toGF216 * difference.toGF216)
    (h_xp_inv : ∀ (j : Nat), j < i1.val → j < i.val →
        ∀ (h_idx : j + 1 < xp.val.length),
          xp.val.get ⟨j + 1, h_idx⟩ = a.val[j]!) :
    mult_xdiff_loop0 i a difference xp dp i1
      ⦃ result =>
        let (xpR, dpR) := result
        (∀ (j : Nat), j < N.val →
          ∀ (hj : j < dpR.val.length),
            (dpR.val.get ⟨j, hj⟩).toGF216 =
              (a.val[j]!).toGF216 * difference.toGF216) ∧
        (∀ (j : Nat), j < i.val →
          ∀ (h_idx : j + 1 < xpR.val.length),
            xpR.val.get ⟨j + 1, h_idx⟩ = a.val[j]!) ∧
        (∀ (j : Nat), ¬(0 < j ∧ j ≤ i.val) →
          xpR.val[j]? = xp.val[j]?) ⦄ := by
  unfold mult_xdiff_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : (Array GF16 N) × (Array GF16 N) × Usize) =>
                  N.val - p.2.2.val)
    (inv := fun (p : (Array GF16 N) × (Array GF16 N) × Usize) =>
        let xp' := p.1
        let dp' := p.2.1
        let i1' := p.2.2
        i1'.val ≤ N.val ∧
        -- dp: processed positions contain the scaled coefficients
        (∀ (j : Nat), j < i1'.val →
          ∀ (hj : j < dp'.val.length),
            (dp'.val.get ⟨j, hj⟩).toGF216 =
              (a.val[j]!).toGF216 * difference.toGF216) ∧
        -- dp: unprocessed positions are unchanged from the input dp
        (∀ (j : Nat), i1'.val ≤ j → dp'.val[j]? = dp.val[j]?) ∧
        -- xp: shifted positions
        (∀ (j : Nat), j < i1'.val → j < i.val →
          ∀ (h_idx : j + 1 < xp'.val.length),
            xp'.val.get ⟨j + 1, h_idx⟩ = a.val[j]!) ∧
        -- xp: non-shifted positions are unchanged from the input xp
        (∀ (j : Nat), ¬(0 < j ∧ j ≤ i1'.val ∧ j ≤ i.val) →
          xp'.val[j]? = xp.val[j]?))
  · -- Body step: prove invariant is preserved and measure decreases
    rintro ⟨xp', dp', i1'⟩
      ⟨h_i1_le, h_dp_proc, h_dp_rest, h_xp_shift, h_xp_rest⟩
    simp only [] at h_i1_le h_dp_proc h_dp_rest h_xp_shift h_xp_rest ⊢
    have h_body := body_spec i a difference xp' dp' i1' h_i_lt_N
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done (xp_r, dp_r) =>
      -- Done case: loop terminates, arrays unchanged
      simp only [] at h_cf ⊢
      obtain ⟨h_xp_eq, h_dp_eq, h_not_lt⟩ := h_cf
      subst h_xp_eq; subst h_dp_eq
      push Not at h_not_lt
      -- i1' = N (from i1' ≤ N and i1' ≥ N)
      refine ⟨?_, ?_, ?_⟩
      · -- dp: all j < N processed
        intro j hj hj'
        exact h_dp_proc j (by omega) hj'
      · -- xp: all j < i shifted
        intro j hj h_idx
        exact h_xp_shift j (by omega) hj h_idx
      · -- xp: unchanged positions
        intro j hj
        apply h_xp_rest
        intro ⟨h1, h2, h3⟩
        exact hj ⟨h1, h3⟩
    | ControlFlow.cont (xp1, dp1, i2) =>
      -- Cont case: one more iteration processed
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_i2, h_dp_upd, h_dp_frame, h_xp_cond, h_xp_nocond⟩ := h_cf
      constructor
      · -- Invariant preserved (5 conjuncts)
        refine ⟨by omega, ?_, ?_, ?_, ?_⟩
        · -- dp: processed positions extended by one
          intro j hj hj'
          by_cases hjk : j < i1'.val
          · -- j was already processed: chain frame + old invariant
            have h_ne : j ≠ i1'.val := by omega
            have h_frame := h_dp_frame j h_ne
            have hj_old : j < dp'.val.length := by
              simp only [List.Vector.length_val]; omega
            have h_get := list_get_of_getElem?_eq h_frame hj' hj_old
            simp only [List.get_eq_getElem] at h_get h_dp_proc ⊢
            rw [h_get]; exact h_dp_proc j hjk hj_old
          · -- j = i1': newly processed by body
            have : j = i1'.val := by omega
            subst this; exact h_dp_upd hj'
        · -- dp: unprocessed positions still unchanged
          intro j hj
          have h_ne : j ≠ i1'.val := by omega
          rw [h_dp_frame j h_ne, h_dp_rest j (by omega)]
        · -- xp: shifted positions extended by one
          intro j hj_lt_i2 hj_lt_i h_idx
          by_cases h_i1_lt_i : i1'.val < i.val
          · -- body updated xp at position i1'+1
            obtain ⟨h_xp_at, h_xp_frame⟩ := h_xp_cond h_i1_lt_i
            by_cases hjk : j < i1'.val
            · -- j was already shifted: chain frame + old invariant
              have h_ne : j + 1 ≠ i1'.val + 1 := by omega
              have h_frame := h_xp_frame (j + 1) h_ne
              have hj_old : j + 1 < xp'.val.length := by
                simp only [List.Vector.length_val]; omega
              have h_get := list_get_of_getElem?_eq h_frame h_idx hj_old
              simp only [List.get_eq_getElem] at h_get h_xp_shift ⊢
              rw [h_get]; exact h_xp_shift j hjk hj_lt_i hj_old
            · -- j = i1': newly shifted by body
              have : j = i1'.val := by omega
              subst this; exact h_xp_at h_idx
          · -- body left xp unchanged (i1' ≥ i)
            have h_xp_eq := h_xp_nocond h_i1_lt_i
            push Not at h_i1_lt_i
            have : j < i1'.val := by omega
            simp only [h_xp_eq] at h_idx ⊢
            grind
        · -- xp: non-shifted positions still unchanged
          intro j hj
          by_cases h_i1_lt_i : i1'.val < i.val
          · -- body updated xp at position i1'+1
            obtain ⟨_, h_xp_frame⟩ := h_xp_cond h_i1_lt_i
            -- j ≠ i1'+1 (otherwise the new invariant condition would hold, contradicting hj)
            have h_ne : j ≠ i1'.val + 1 := by
              intro heq; apply hj; subst heq; exact ⟨by omega, by omega, by omega⟩
            -- Chain: xp1[j]? = xp'[j]? = xp[j]?
            rw [h_xp_frame j h_ne]
            apply h_xp_rest
            intro ⟨h1, h2, h3⟩; exact hj ⟨h1, by omega, h3⟩
          · -- body left xp unchanged (i1' ≥ i), so xp1 = xp'
            have h_xp_eq := h_xp_nocond h_i1_lt_i
            simp only [h_xp_eq]
            apply h_xp_rest
            intro ⟨h1, h2, h3⟩; exact hj ⟨h1, by omega, h3⟩
      · -- Measure decreases
        omega
  · -- Initial invariant
    refine ⟨h_i1_le_N, h_dp_inv, ?_, h_xp_inv, ?_⟩
    · intro j _; rfl
    · intro j _; rfl

end spqr.encoding.polynomial.PolyConst.mult_xdiff_loop0
