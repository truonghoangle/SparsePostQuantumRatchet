/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Basic.Defs
import Spqr.Math.Poly.Basic.Zero
import Spqr.Math.Poly.Coeff.Basic
import Spqr.Math.Poly.Coeff.ListOps
import Spqr.Math.Poly.CharTwo.Basic
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Math.Poly.Eval
import Spqr.Math.Poly.LinearFactors.Basic
import Spqr.Math.Poly.LinearFactors.Degree
import Spqr.Math.Poly.Lagrange.DenomProd
import Spqr.Math.Poly.Lagrange.BasisPoly
import Spqr.Math.Poly.Lagrange.InterpolantSum
import Spqr.Math.Poly.Horner.Defs
import Spqr.Math.Poly.Horner.Eval
import Spqr.Math.Poly.ExpectedTrailing.Defs
import Spqr.Math.Poly.ExpectedTrailing.Basic
import Spqr.Math.Poly.Identities.Basic
import Spqr.Math.Poly.Mathlib
import Spqr.Math.Poly.General

/-!
# Aeneas-related polynomial bridge results

Lemmas connecting Aeneas-extracted types (`GF16`, `Poly`, `Pt`, `Vec`, etc.) to the mathematical
polynomial library over `GF216 = GF(2¹⁶)`. These results bridge the implementation-level
representations with their mathematical interpretations and are used throughout the specification
proofs in `Spqr/Specs/Encoding/Polynomial`.

## Main statements

### Polynomial identity from loop 1
* `poly_identity_from_loop1`: the polynomial identity `listToGF216Poly v * (X - C g) = X * C s *
  listToGF216Poly coeffs` arising from the Horner-scheme loop in `lagrange_interpolate_complete`.

### Polynomial identity for `mult_xdiff_assign_trailing`
* `mult_xdiff_poly_identity`: closed-form for the in-place recurrence `v[i−1] −= v[i] * d`.

### Power-vector invariant
* `power_invariant_step`: appending `g = xs[n/2] * xs[n/2 + n%2]` extends the power vector.
* `initial_power_invariant`: `[GF16::ONE, x]` satisfies the power-vector invariant.

### Dot-product to evaluation bridge
* `dot_product_eq_eval`: dot product of coefficient and power vectors equals polynomial evaluation.
* `zero_toGF216_eq_empty_sum`: `GF16.ZERO.toGF216` equals an empty sum.
-/

open Aeneas Aeneas.Std Result Polynomial
open spqr.math.gf spqr.encoding.gf spqr.encoding.polynomial

namespace spqr.encoding.polynomial

/-! ## Polynomial identity from loop 1 (lagrange_interpolate_complete) -/

/--
**Mathematical polynomial identity from the Horner-scheme loop.**

Given a coefficient list `coeffs`, a result list `v` of the same length, a field element `g : GF16`,
a scale `s : GF216`, and the condition that:
• `v[0].toGF216 = 0` (zero constant term),
• `hornerAccum g coeffs 0 = 0` (evaluation at `g` is zero),
• `v[k].toGF216 = s * hornerAccum g coeffs k` for `k > 0`,

then:
  `listToGF216Poly v * (X - C g.toGF216) = X * C s * listToGF216Poly coeffs`

This identity captures the algebraic content of the Horner-scheme division + scaling in
`lagrange_interpolate_complete`.
-/
theorem poly_identity_from_loop1
    (coeffs v : List GF16)
    (g : GF16) (s : GF216)
    (hlen : v.length = coeffs.length)
    (hpos : 0 < coeffs.length)
    (hv0_zero : ∀ (h0 : 0 < v.length),
        (v.get ⟨0, h0⟩).toGF216 = 0)
    (hH0 : hornerAccum g coeffs 0 = 0)
    (hvk : ∀ k (hk : k < v.length), 0 < k →
        (v.get ⟨k, hk⟩).toGF216 =
          s * hornerAccum g coeffs k) :
    listToGF216Poly v * (X - C (g.toGF216)) =
      X * C s * listToGF216Poly coeffs := by
  rw [GF216Poly.sub_eq_add, mul_add, mul_comm (listToGF216Poly v) (C (g.toGF216)),
      show X * C s * listToGF216Poly coeffs =
        C s * (X * listToGF216Poly coeffs) from by ring]
  ext m
  simp only [coeff_add, coeff_C_mul]
  set α := g.toGF216
  by_cases hm0 : m = 0
  · subst hm0
    rw [coeff_mul_X_zero, coeff_X_mul_zero, zero_add, mul_zero]
    simp only [listToGF216Poly_coeff]
    split
    · rename_i h0v
      rw [hv0_zero h0v, mul_zero]
    · rename_i h0v; push Not at h0v; omega
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    have hcoeff_v_X : (listToGF216Poly v * X).coeff m =
        (listToGF216Poly v).coeff (m - 1) := by
      conv_lhs => rw [show m = m - 1 + 1 from by omega]
      rw [coeff_mul_X]
    have hcoeff_X_c : (X * listToGF216Poly coeffs).coeff m =
        (listToGF216Poly coeffs).coeff (m - 1) := by
      conv_lhs => rw [show m = m - 1 + 1 from by omega]
      rw [coeff_X_mul]
    rw [hcoeff_v_X, hcoeff_X_c]
    simp only [listToGF216Poly_coeff]
    by_cases hm_lt : m < coeffs.length
    · have hm1_lt_c : m - 1 < coeffs.length := by omega
      have hm1_lt_v : m - 1 < v.length := by omega
      have hm_lt_v : m < v.length := by omega
      rw [dif_pos hm1_lt_v, dif_pos hm_lt_v, dif_pos hm1_lt_c]
      by_cases hm1_zero : m - 1 = 0
      · have hm_eq_1 : m = 1 := by omega
        subst hm_eq_1; simp only [Nat.sub_self]
        rw [hv0_zero (by omega),
            hvk 1 (by omega) (by omega), zero_add]
        have hH0_unf :=
          hornerAccum_unfold g coeffs 0 (by omega)
        rw [hH0] at hH0_unf
        have hcoeff0 :
            (coeffs.get ⟨0, by omega⟩).toGF216 =
              α * hornerAccum g coeffs 1 :=
          GF216_eq_of_add_eq_zero hH0_unf.symm
        rw [hcoeff0]; ring
      · have hm1_pos : 0 < m - 1 := by omega
        rw [hvk (m - 1) hm1_lt_v hm1_pos,
            hvk m hm_lt_v hm_pos]
        rw [show s * hornerAccum g coeffs (m - 1) +
              α * (s * hornerAccum g coeffs m) =
            s * (hornerAccum g coeffs (m - 1) +
              α * hornerAccum g coeffs m) from by ring]
        congr 1
        have hm_succ : m - 1 + 1 = m := by omega
        have := hornerAccum_cancel g coeffs (m - 1) hm1_lt_c
        rw [hm_succ] at this
        exact this
    · push Not at hm_lt
      by_cases hm_eq : m = coeffs.length
      · subst hm_eq
        have hm1_lt_c : coeffs.length - 1 < coeffs.length :=
          by omega
        have hm1_lt_v : coeffs.length - 1 < v.length := by omega
        rw [dif_pos hm1_lt_v,
            dif_neg (show ¬(coeffs.length < v.length) from
              by omega),
            dif_pos hm1_lt_c]
        rw [mul_zero, add_zero]
        have hH_last :=
          hornerAccum_unfold g coeffs (coeffs.length - 1) hm1_lt_c
        have hsucc : coeffs.length - 1 + 1 = coeffs.length :=
          by omega
        rw [hsucc] at hH_last
        rw [hornerAccum_ge g coeffs coeffs.length (le_refl _)] at hH_last
        simp [mul_zero, add_zero] at hH_last
        have hH_last_get : (coeffs.get ⟨coeffs.length - 1, hm1_lt_c⟩).toGF216 =
            hornerAccum g coeffs (coeffs.length - 1) := by
          simp only [List.get_eq_getElem]; exact hH_last.symm
        rw [hH_last_get]
        by_cases h_pos : 0 < coeffs.length - 1
        · exact hvk (coeffs.length - 1) hm1_lt_v h_pos
        · have h0 : coeffs.length - 1 = 0 := by omega
          have hv_eq : v.get ⟨coeffs.length - 1, hm1_lt_v⟩ =
              v.get ⟨0, by omega⟩ := by
            congr 1; exact Fin.ext h0
          rw [show (v.get ⟨coeffs.length - 1, hm1_lt_v⟩).toGF216 =
              (v.get ⟨0, by omega⟩).toGF216 from by rw [hv_eq]]
          rw [hv0_zero (by omega), h0, hH0, mul_zero]
      · have hm_gt : coeffs.length < m := by omega
        rw [dif_neg (show ¬(m - 1 < v.length) from by omega),
            dif_neg (show ¬(m < v.length) from by omega),
            dif_neg (show ¬(m - 1 < coeffs.length) from by omega)]
        ring

/-! ## Polynomial identity for `mult_xdiff_assign_trailing` -/

/--
**Mathematical polynomial identity for `mult_xdiff_assign_trailing`.**

Given a coefficient list `cs`, a result list `rs` of the same length, a starting index `s ≥ 1`
with `s ≤ cs.length`, and a field element `d : GF16` such that:
• For carry-propagated positions (`s ≤ j + 1 ∧ j + 1 < cs.length`):
    `rs[j].toGF216 = cs[j].toGF216 − cs[j+1].toGF216 * d.toGF216`
• All other positions are unchanged (`rs[j]? = cs[j]?`),

then:
  `listToGF216Poly rs =
      listToGF216Poly cs −
      C(d.toGF216) · X^(s−1) · listToGF216Poly (cs.drop s)`
-/
theorem mult_xdiff_poly_identity
    (cs rs : List GF16) (s : Nat) (d : GF16)
    (h_s_pos : 1 ≤ s) (h_s_le : s ≤ cs.length)
    (h_len : rs.length = cs.length)
    (h_mod : ∀ j, s ≤ j + 1 → j + 1 < cs.length → ∀ hj : j < rs.length,
      (rs.get ⟨j, hj⟩).toGF216 = (cs[j]!).toGF216 - (cs[j + 1]!).toGF216 * d.toGF216)
    (h_same : ∀ j, ¬(s ≤ j + 1 ∧ j + 1 < cs.length) → rs[j]? = cs[j]?) :
    listToGF216Poly rs =
      listToGF216Poly cs -
      C d.toGF216 * X ^ (s - 1) * listToGF216Poly (cs.drop s) := by
  ext m
  rw [coeff_sub, listToGF216Poly_coeff, listToGF216Poly_coeff,
      show C d.toGF216 * X ^ (s - 1) * listToGF216Poly (cs.drop s) =
        C d.toGF216 * (listToGF216Poly (cs.drop s) * X ^ (s - 1)) by ring,
      coeff_C_mul, coeff_mul_X_pow']
  by_cases hm : m < cs.length
  · rw [dif_pos (show m < rs.length by omega), dif_pos hm]
    by_cases hs : s - 1 ≤ m
    · rw [if_pos hs, listToGF216Poly_coeff]
      by_cases hd : m - (s - 1) < (cs.drop s).length
      · rw [dif_pos hd]
        have h2 : m + 1 < cs.length := by rw [List.length_drop] at hd; omega
        have hmod := h_mod m (by omega) h2 (by omega)
        simp only [List.get_eq_getElem] at hmod ⊢
        rw [hmod, getElem!_pos cs m hm, getElem!_pos cs (m + 1) h2]
        have h_drop := list_get_drop_eq cs s (m - (s - 1)) hd
        simp only [List.get_eq_getElem] at h_drop
        rw [h_drop]; simp only [show s + (m - (s - 1)) = m + 1 from by omega]; ring
      · rw [dif_neg hd, mul_zero, sub_zero]
        have h_not : ¬(s ≤ m + 1 ∧ m + 1 < cs.length) := by
          rw [List.length_drop] at hd; push Not at hd ⊢; intro h1; omega
        exact congr_arg GF16.toGF216
          (list_get_of_getElem?_eq (h_same m h_not) (by omega) hm)
    · rw [if_neg hs, mul_zero, sub_zero]
      exact congr_arg GF16.toGF216
        (list_get_of_getElem?_eq (h_same m (by push Not; intro h1; omega)) (by omega) hm)
  · push Not at hm
    rw [dif_neg (by omega), dif_neg (by omega)]
    by_cases hs : s - 1 ≤ m
    · rw [if_pos hs, listToGF216Poly_coeff,
          dif_neg (by rw [List.length_drop]; omega), mul_zero]; ring
    · rw [if_neg hs]; ring

/-! ## Power-vector invariant -/

/--
**Euclidean-division identity**: `n / 2 + (n / 2 + n % 2) = n`.
-/
theorem div2_add_sum_eq (n : Nat) : n / 2 + (n / 2 + n % 2) = n := by
  have := Nat.div_add_mod n 2; omega

/--
**Power-vector invariant preservation.**

Appending `g = xs[n/2] * xs[n/2 + n%2]` to a power vector `xs` of length `n ≥ 2` that satisfies
`xs[j].toGF216 = x.toGF216 ^ j` for all `j < n` produces a vector of length `n + 1` satisfying the
same property for all `j < n + 1`.
-/
theorem power_invariant_step
    (x : GF16)
    (xs : List GF16)
    (g : GF16)
    (h_ge2 : 2 ≤ xs.length)
    (h_pow : ∀ j, j < xs.length → (xs[j]!).toGF216 = x.toGF216 ^ j)
    (h_g : g.toGF216 =
      (xs[xs.length / 2]!).toGF216 *
      (xs[xs.length / 2 + xs.length % 2]!).toGF216) :
    ∀ j, j < (xs ++ [g]).length → ((xs ++ [g])[j]!).toGF216 = x.toGF216 ^ j := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  have h_div2_lt : xs.length / 2 < xs.length := Nat.div_lt_self (by omega) (by omega)
  have h_sum_lt : xs.length / 2 + xs.length % 2 < xs.length := by
    have := Nat.div_add_mod xs.length 2; omega
  by_cases hlt : j < xs.length
  · have hlt' : j < (xs ++ [g]).length := by grind
    grind
  · have hj_eq : j = xs.length := by omega
    subst hj_eq
    have hlt' : xs.length < (xs ++ [g]).length := by grind
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
      lt_add_iff_pos_right, Order.lt_one_iff, getElem!_pos, le_refl, List.getElem_append_right,
      tsub_self, List.getElem_cons_zero]
    rw [h_g, h_pow _ h_div2_lt, h_pow _ h_sum_lt, ← pow_add, div2_add_sum_eq]

/--
**Initial power-vector invariant.**

The two-element vector `[GF16::ONE, x]` satisfies the power-vector invariant:
  `[ONE, x][j]!.toGF216 = x.toGF216 ^ j` for all `j < 2`.
-/
theorem initial_power_invariant (x : GF16) :
    ∀ j, j < [GF16.ONE, x].length →
      ([GF16.ONE, x][j]!).toGF216 = x.toGF216 ^ j := by
  intro j hj
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j
  · simp [GF16.ONE, GF16.toGF216, Nat.toGF216, natToBinaryPoly_one, map_one]
  · simp [pow_one]

/-! ## Dot-product to evaluation bridge -/

/--
**Dot-product to polynomial evaluation bridge.**

When the power vector `xs` satisfies `xs[j].toGF216 = x.toGF216 ^ j` for all `j < xs.length`,
and `n = v.length ≤ xs.length`, the dot product
  `∑ j ∈ Finset.range n, v[j]!.toGF216 * xs[j]!.toGF216`
equals the polynomial evaluation `(listToGF216Poly v).eval (x.toGF216)`.
-/
theorem dot_product_eq_eval
    (x : GF16) (v : List GF16) (xs : List GF16)
    (h_pow : ∀ j, j < xs.length → (xs[j]!).toGF216 = x.toGF216 ^ j)
    (h_len : v.length ≤ xs.length) :
    (∑ j ∈ Finset.range v.length,
      (v[j]!).toGF216 * (xs[j]!).toGF216) =
    (listToGF216Poly v).eval (x.toGF216) := by
  have h_sub : ∀ j ∈ Finset.range v.length,
      (v[j]!).toGF216 * (xs[j]!).toGF216 =
      (v[j]!).toGF216 * x.toGF216 ^ j := by
    intro j hj; rw [Finset.mem_range] at hj
    congr 1; exact h_pow j (by omega)
  rw [Finset.sum_congr rfl h_sub]
  have h_coeff : ∀ j ∈ Finset.range v.length,
      (v[j]!).toGF216 * x.toGF216 ^ j =
      (listToGF216Poly v).coeff j * x.toGF216 ^ j := by
    intro j hj
    congr 1; exact getElem_bang_toGF216_eq_coeff v j
  rw [Finset.sum_congr rfl h_coeff]
  exact (eval_eq_range_sum (listToGF216Poly v) (x.toGF216) v.length
    (fun j hj => listToGF216Poly_coeff_eq_zero v j hj)).symm

/--
**Zero accumulator equals empty sum.**
`GF16.ZERO.toGF216 = ∑ j ∈ Finset.range 0, f j` for any `f`.
-/
theorem zero_toGF216_eq_empty_sum
    (v xs : alloc.vec.Vec GF16) :
    GF16.ZERO.toGF216 = ∑ j ∈ Finset.range 0,
      (v.val[j]!).toGF216 * (xs.val[j]!).toGF216 := by
  simp [GF16.ZERO, GF16.toGF216, Nat.toGF216, natToBinaryPoly_zero, map_zero]

/--
**Max-2 length bound.**
If `n + 1 ≤ Usize.max`, then `max 2 n + 1 ≤ Usize.max`.
-/
theorem max_two_succ_le_usize_max (n : Nat) (h : n + 1 ≤ Usize.max) :
    Nat.max 2 n + 1 ≤ Usize.max := by
  simp only [Nat.max_def]
  split_ifs
  · exact h
  · scalar_tac

end spqr.encoding.polynomial
