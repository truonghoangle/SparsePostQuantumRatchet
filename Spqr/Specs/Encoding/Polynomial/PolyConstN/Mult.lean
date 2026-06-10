/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyConstN.MultLoop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyConst<N>}::mult`

The Rust function `PolyConst::mult` (in `src/encoding/polynomial.rs`, lines 398:4-410:5)
computes the scalar product of a constant-sized polynomial `self` by a field element `m`
in GF(2¹⁶)[X].  The result is a new polynomial whose coefficients are each multiplied by `m`.

Concretely, `mult self m` copies `self.coefficients` into a mutable array `out` and then runs
a `while i < N` loop that replaces each coefficient `out[i]` with `out[i].const_mul(m)`.

The Aeneas-extracted Lean function `encoding.polynomial.PolyConst.mult` is a direct
composition of:
  1. `encoding.polynomial.PolyConst.mult_loop m 0#usize self.coefficients` — the loop driver
     that scales every coefficient of `self.coefficients` by `m`.
  2. `ok { coefficients := a }` — wraps the scaled array back into a `PolyConst`.

Since the top-level function introduces no additional logic beyond the loop and wrapping,
the postcondition is derived by composing the loop specification (`mult_loop.loop_spec`)
with the algebraic identity:

  Scaling every coefficient of a polynomial by a field element `m` is equivalent to
  multiplying the polynomial by the constant polynomial `C m`:
    `listToGF216Poly result.coefficients.val =
       C (m.toGF216) * listToGF216Poly self.coefficients.val`

**Coefficient-level analysis**:

After the loop (starting at `i = 0`, so all `N` positions are processed):
  - `result[j].toGF216 = self.coefficients[j].toGF216 * m.toGF216` for all `j < N`

This matches the coefficients of `C (m.toGF216) * listToGF216Poly self.coefficients.val`:
  - `(C m.toGF216 · p).coeff j = m.toGF216 · p.coeff j = m.toGF216 · self.coefficients[j].toGF216`
  (using commutativity of multiplication in GF(2¹⁶))

In GF(2¹⁶) (characteristic 2), multiplication is carry-less polynomial multiplication modulo the
irreducible polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 398:4-410:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyConst

/-! ## Helper lemma -/

/--
**Polynomial identity lemma**: given the postconditions of the scalar multiplication loop,
the result polynomial equals `C (m.toGF216) * listToGF216Poly a.val`.

This is the core algebraic fact; the main theorem `mult_spec` simply composes the loop
specification and delegates to this lemma.
-/
private lemma mult_result_eq
    {N : Usize}
    (a : Array GF16 N) (m : GF16)
    (result : Array GF16 N)
    -- Loop postcondition: every position holds the GF(2¹⁶) product
    (h_scaled : ∀ (j : Nat), 0 ≤ j → j < N.val →
      ∀ (hj : j < result.val.length),
        (result.val.get ⟨j, hj⟩).toGF216 =
          (a.val[j]!).toGF216 * m.toGF216) :
    listToGF216Poly result.val =
      C (m.toGF216) * listToGF216Poly a.val := by
  apply listToGF216Poly_eq_of_coeffs
  · -- h_in: for each j < N, the j-th coefficient of result matches the scaled polynomial
    intro j hj
    simp only [List.Vector.length_val] at hj
    have h_j_result : j < result.val.length := by
      simp [List.Vector.length_val]; omega
    rw [h_scaled j (by omega) (by omega) h_j_result]
    rw [coeff_C_mul, ← getElem!_toGF216_eq_coeff]
    ring
  · -- h_out: for j ≥ N, the polynomial coefficient is zero
    intro j hj
    simp only [List.Vector.length_val] at hj
    rw [coeff_C_mul, listToGF216Poly_coeff_eq_zero _ j (by grind), mul_zero]

/--
**Spec theorem for `encoding.polynomial.PolyConst.mult`**:

• The function always succeeds (no panic) for any `PolyConst N` and `GF16` inputs, since
  the underlying `const_mul` and the loop driver are total on `GF16 × GF16`, and all
  array accesses are bounded by `N`.

• **Polynomial scalar multiplication postcondition**:
    `listToGF216Poly result.coefficients.val =
       C (m.toGF216) * listToGF216Poly self.coefficients.val`
  where `listToGF216Poly` interprets a `List GF16` as a polynomial in
  `GF216[X] = (GaloisField 2 16)[X]`, and `C : GF216 →+* GF216[X]`
  is the constant-polynomial embedding.

  The proof composes the postcondition of the sub-loop:
    - **Loop 0** (`mult_loop.loop_spec`): scales each coefficient `self.coefficients[j]`
      by `m`, yielding `result[j].toGF216 = self.coefficients[j].toGF216 * m.toGF216`
      for all `j < N`.

  The bridging from element-wise properties to the polynomial identity uses
  `listToGF216Poly_eq_of_coeffs`, matching each coefficient of the result to the
  corresponding coefficient of `C (m.toGF216) * listToGF216Poly self.coefficients.val`
  via `getElem!_toGF216_eq_coeff`.

**Source**: spqr/src/encoding/polynomial.rs (lines 398:4-410:5)
-/
@[step]
theorem mult_spec
    {N : Usize}
    (self : PolyConst N)
    (m : GF16) :
    mult self m ⦃ (result : PolyConst N) =>
      listToGF216Poly result.coefficients.val =
        C (m.toGF216) * listToGF216Poly self.coefficients.val ⦄ := by
  unfold mult
  step*
  apply @mult_result_eq N self.coefficients m a
  all_goals simp_all

end spqr.encoding.polynomial.PolyConst
