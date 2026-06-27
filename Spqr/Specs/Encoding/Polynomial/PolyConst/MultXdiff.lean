/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Gf.GF16.ZERO
import Spqr.Specs.Encoding.Polynomial.PolyConst.MultXdiffLoop0
import Spqr.Specs.Encoding.Polynomial.PolyConst.MultXdiffLoop1

/-!
# Spec theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyConst<N>}::mult_xdiff`

The Rust function `PolyConst::mult_xdiff` (in `src/encoding/polynomial.rs`, lines 415:4-454:5)
computes the product of a constant-sized polynomial `self` by the linear factor `(x − difference)`
in GF(2¹⁶)[X].  Since GF(2¹⁶) has characteristic 2, subtraction coincides with addition, so
`(x − difference) = (x + difference)`.

The function first asserts that the leading coefficient `self.coefficients[N − 1]` is zero (since
multiplying by a linear factor increases the degree by one, and the result must still fit in the
fixed-size `N`-element array — the assertion ensures no overflow).

The multiplication is then decomposed into two phases:

  1. **Loop 0** (`mult_xdiff_loop0`, lines 430–440): Simultaneously constructs two arrays of
     size `N`:
     - `xp` representing `x · self` (shifted coefficients): `xp[0] = GF16.ZERO` and
       `xp[j+1] = a[j]` for `0 ≤ j < N−1`.
     - `dp` representing `difference · self` (scaled coefficients): `dp[j] = a[j] · difference`
       for `0 ≤ j < N`.

  2. **Loop 1** (`mult_xdiff_loop1`, lines 446–451): Computes the element-wise subtraction
     `xp[j] := xp[j] − dp[j]` for all `j < N`, producing the final result array:
       `result = xp − dp = (x · self) − (difference · self) = (x − difference) · self`

In characteristic 2, subtraction coincides with addition (both are bitwise XOR), so the
element-wise subtraction in loop 1 is identical to XOR, and `(x − difference) = (x + difference)`.

The Aeneas-extracted Lean function `encoding.polynomial.PolyConst.mult_xdiff` is a direct
composition of:
  1. `N - 1#usize` — computes the index of the leading coefficient.
  2. `Array.index_usize self.coefficients i` — reads the leading coefficient.
  3. `massert (¬ (g.value != 0#u16))` — asserts the leading coefficient is zero.
  4. `Array.repeat N GF16.ZERO` — initialises `xp` and `dp` to all-zero arrays.
  5. `encoding.polynomial.PolyConst.mult_xdiff_loop0 i a difference xp dp 0#usize` — loop 0.
  6. `encoding.polynomial.PolyConst.mult_xdiff_loop1 xp1 dp1 0#usize` — loop 1.
  7. `ok { coefficients := xp2 }` — wraps the final array in a `PolyConst`.

Since the top-level function introduces no additional logic beyond the assertion and array
initialisation, the postcondition is derived by composing the loop specifications
(`mult_xdiff_loop0.loop_spec` and `mult_xdiff_loop1.loop_spec`) with the characteristic-2
algebraic identity:
  `(x · self) − (difference · self) = (x − difference) · self`

**Coefficient-level analysis**:

After loop 0 (with `a := self.coefficients` and `d := difference`):
  - `dp1[j].toGF216 = a[j].toGF216 * d.toGF216` for all `j < N`
  - `xp1[j + 1] = a[j]` for `0 ≤ j < N − 1`
  - `xp1[0] = GF16.ZERO` (unchanged from initialisation)

After loop 1:
  - `xp2[j].toGF216 = xp1[j].toGF216 − dp1[j].toGF216` for all `j < N`

Combining:
  - For `j = 0`: `xp2[0].toGF216 = 0 − a[0].toGF216 · d.toGF216 = −d · a[0].toGF216`
  - For `0 < j < N`: `xp2[j].toGF216 = a[j−1].toGF216 − a[j].toGF216 · d.toGF216`

These match the coefficients of `(X − C d) · p` where `p = listToGF216Poly a.val`:
  - `((X − C d) · p).coeff 0 = −d · p.coeff 0 = −d · a[0].toGF216`
  - `((X − C d) · p).coeff j = p.coeff (j − 1) − d · p.coeff j`
    `= a[j−1].toGF216 − d · a[j].toGF216` for `j > 0`

For `j ≥ N`, the product has zero coefficients since `p` has degree `≤ N − 2`
(because `a[N−1].toGF216 = 0` by the precondition).

**Source**: spqr/src/encoding/polynomial.rs (lines 415:4-454:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyConst

/-! ## Helper lemmas -/

/--
**Polynomial identity lemma**: given the postconditions of loop 0 and loop 1 of `mult_xdiff`,
the result polynomial equals `(X - C d.toGF216) * listToGF216Poly a.val`.

This is the core algebraic fact; the main theorem `mult_xdiff_spec` simply composes the loop
specifications and delegates to this lemma.
-/
private lemma mult_xdiff_result_eq
    {N : Usize}
    (a : Array GF16 N) (d : GF16)
    (i : Usize)
    (xp1 dp1 xp2 : Array GF16 N)
    (h_N_pos : 0 < N.val)
    (h_i_val : i.val = N.val - 1)
    (h_leading_zero : (a.val[N.val - 1]!).value.val = 0)
    -- Loop 0 dp postcondition: every position holds the scaled coefficient
    (h_dp : ∀ (j : Nat), j < N.val →
      ∀ (hj : j < dp1.val.length),
        (dp1.val.get ⟨j, hj⟩).toGF216 =
          (a.val[j]!).toGF216 * d.toGF216)
    -- Loop 0 xp postcondition: shifted coefficients
    (h_xp_shift : ∀ (j : Nat), j < i.val →
      ∀ (h_idx : j + 1 < xp1.val.length),
        xp1.val.get ⟨j + 1, h_idx⟩ = a.val[j]!)
    -- Loop 0 xp postcondition: unchanged positions
    (h_xp_unch : ∀ (j : Nat), ¬(0 < j ∧ j ≤ i.val) →
      xp1.val[j]? = (Array.repeat N GF16.ZERO).val[j]?)
    -- Loop 1 postcondition: element-wise subtraction
    (h_sub : ∀ (j : Nat), 0 ≤ j → j < N.val →
      ∀ (hj : j < xp2.val.length),
        (xp2.val.get ⟨j, hj⟩).toGF216 =
          (xp1.val[j]!).toGF216 - (dp1.val[j]!).toGF216) :
    listToGF216Poly xp2.val =
      (X - C d.toGF216) * listToGF216Poly a.val := by
  apply listToGF216Poly_eq_of_coeffs
  · -- h_in: for each m < N, the m-th coefficient of xp2 matches the polynomial product
    intro m hm
    simp only [List.Vector.length_val] at hm
    -- Step 1: Rewrite xp2[m].toGF216 using loop 1 postcondition
    have h_m_xp2 : m < xp2.val.length := by simp [List.Vector.length_val]; omega
    rw [h_sub m (by omega) (by omega) h_m_xp2]
    -- Goal: (xp1[m]!).toGF216 - (dp1[m]!).toGF216 = ((X - C d.toGF216) * p).coeff m
    -- Step 2: Rewrite dp1[m]!.toGF216 using loop 0 dp postcondition
    have h_dp_m : (dp1.val[m]!).toGF216 = (a.val[m]!).toGF216 * d.toGF216 := by
      have h_m_dp : m < dp1.val.length := by simp [List.Vector.length_val]; omega
      rw [getElem!_pos dp1.val m h_m_dp]
      exact h_dp m (by omega) h_m_dp
    rw [h_dp_m]
    -- Goal: (xp1[m]!).toGF216 - (a[m]!).toGF216 * d.toGF216 =
    --       ((X - C d.toGF216) * p).coeff m
    -- Step 3: Expand the RHS polynomial coefficient
    rw [sub_mul, coeff_sub, coeff_C_mul, ← getElem!_toGF216_eq_coeff]
    -- Goal: (xp1[m]!).toGF216 - (a[m]!).toGF216 * d.toGF216 =
    --       (X * p).coeff m - d.toGF216 * (a[m]!).toGF216
    -- Step 4: Case split on m for the X * p coefficient
    cases m with
    | zero =>
      -- m = 0: (X * p).coeff 0 = 0
      rw [coeff_X_mul_zero]
      -- Goal: (xp1[0]!).toGF216 - (a[0]!).toGF216 * d.toGF216 =
      --       0 - d.toGF216 * (a[0]!).toGF216
      -- Show xp1[0]! = GF16.ZERO (unchanged from Array.repeat initialisation)
      have h_xp1_0 : (xp1.val[0]!).toGF216 = 0 := by
        have h_unch := h_xp_unch 0 (by omega)
        have h_len_xp1 : 0 < xp1.val.length := by
          simp [List.Vector.length_val]; omega
        have h_len_rep : 0 < (Array.repeat N GF16.ZERO).val.length := by
          simp [Array.repeat_val]; omega
        have h_eq := list_get_of_getElem?_eq h_unch h_len_xp1 h_len_rep
        rw [getElem!_pos xp1.val 0 h_len_xp1]
        simp_all
      rw [h_xp1_0]; ring
    | succ n =>
      -- m = n + 1: (X * p).coeff (n + 1) = p.coeff n
      rw [coeff_X_mul, ← getElem!_toGF216_eq_coeff]
      -- Goal: (xp1[n+1]!).toGF216 - (a[n+1]!).toGF216 * d.toGF216 =
      --       (a[n]!).toGF216 - d.toGF216 * (a[n+1]!).toGF216
      -- Show xp1[n+1] = a[n]! (shifted from loop 0)
      have h_xp1_succ : (xp1.val[n + 1]!).toGF216 = (a.val[n]!).toGF216 := by
        have h_n_lt_i : n < i.val := by rw [h_i_val]; omega
        have h_idx : n + 1 < xp1.val.length := by
          simp [List.Vector.length_val]; omega
        rw [getElem!_pos xp1.val (n + 1) h_idx]
        have h_shift := h_xp_shift n h_n_lt_i h_idx
        simp only [List.get_eq_getElem] at h_shift
        rw [h_shift]
      rw [h_xp1_succ]; ring
  · -- h_out: for m ≥ N, the polynomial coefficient is zero
    intro m hm
    simp only [List.Vector.length_val] at hm
    -- The C d * p part: p.coeff m = 0 since m ≥ N = a.val.length
    rw [sub_mul, coeff_sub, coeff_C_mul,
        listToGF216Poly_coeff_eq_zero _ m (by grind),
        mul_zero, sub_zero]
    -- Goal: (X * p).coeff m = 0
    cases m with
    | zero => omega -- impossible since m ≥ N > 0
    | succ n =>
      -- (X * p).coeff (n + 1) = p.coeff n
      rw [coeff_X_mul, listToGF216Poly_coeff]
      split
      · -- n < a.val.length: since n + 1 ≥ N and n < N, we have n = N - 1
        rename_i hn
        simp only [List.Vector.length_val] at hn
        have h_eq : n = N.val - 1 := by omega
        subst h_eq
        -- Need: (a.val.get ⟨N.val - 1, _⟩).toGF216 = 0
        -- This follows from h_leading_zero via GF16.toGF216_eq_zero
        apply GF16.toGF216_eq_zero
        simp only [List.get_eq_getElem]
        rw [← getElem!_pos a.val (N.val - 1) (by simp [List.Vector.length_val]; omega)]
        exact h_leading_zero
      · -- n ≥ a.val.length: coefficient is 0 by the dif_neg branch
        rfl

/--
**Spec theorem for `encoding.polynomial.PolyConst.mult_xdiff`**:

• The function succeeds (no panic) provided `0 < N.val` and the leading coefficient
  `self.coefficients[N − 1].value.val = 0`, since:
    1. `N − 1` does not underflow (`0 < N.val`).
    2. The array index `N − 1` is in bounds (`N − 1 < N`).
    3. The runtime assertion `self.coefficients[N − 1].value == 0` is satisfied.
    4. Both loop drivers (`mult_xdiff_loop0`, `mult_xdiff_loop1`) are total on arrays of
       size `N`, and all loop body operations (`const_mul`, `const_sub`, array indexing and
       update) are total on `GF16 × GF16` and bounded arrays.

• **Polynomial multiplication postcondition**:
    `listToGF216Poly result.coefficients.val =
       (X − C (difference.toGF216)) * listToGF216Poly self.coefficients.val`
  where `listToGF216Poly` interprets a `List GF16` as a polynomial in
  `GF216[X] = (GaloisField 2 16)[X]`, `X` is the indeterminate, and `C : GF216 →+* GF216[X]`
  is the constant-polynomial embedding.

  In GF(2¹⁶) (characteristic 2), `(X − C d) = (X + C d)`, so this equivalently states that
  the result is the product of `self` by the linear factor `(X + C (difference.toGF216))`.

  The proof composes the postconditions of the two sub-loops:
    - **Loop 0** (`mult_xdiff_loop0.loop_spec`): produces arrays `xp1` (x · self, shifted)
      and `dp1` (difference · self, scaled).
    - **Loop 1** (`mult_xdiff_loop1.loop_spec`): computes the element-wise subtraction
      `xp1 − dp1`, yielding `(x · self) − (difference · self) = (x − difference) · self`.

  The bridging from element-wise properties to the polynomial identity uses
  `listToGF216Poly_eq_of_coeffs`, matching each coefficient of `xp2` to the corresponding
  coefficient of `(X − C d) * p` via `getElem!_toGF216_eq_coeff`.

**Source**: spqr/src/encoding/polynomial.rs (lines 415:4-454:5)
-/
@[step]
theorem mult_xdiff_spec
    {N : Usize}
    (self : PolyConst N)
    (difference : GF16)
    (h_N_pos : 0 < N.val)
    (h_leading_zero : (self.coefficients.val[N.val - 1]!).value.val = 0) :
    mult_xdiff self difference ⦃ (result : PolyConst N) =>
      listToGF216Poly result.coefficients.val =
        (X - C (difference.toGF216)) * listToGF216Poly self.coefficients.val ⦄ := by
  unfold mult_xdiff
  step*
  · grind
  apply @mult_xdiff_result_eq N (self.coefficients) difference i xp1 dp1 xp2 h_N_pos i_post1
  all_goals simp_all

end spqr.encoding.polynomial.PolyConst
