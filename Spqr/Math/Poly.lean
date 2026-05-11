/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Mathlib.RingTheory.Polynomial.Basic

/-! # GF(2¹⁶)[X] Polynomial Library

Consolidated definitions, lemmas, and theorems about polynomials
over `GF(2¹⁶) = GaloisField 2 16`, connecting the implementation type
`spqr.encoding.polynomial.Poly` (which stores coefficients as a vector
of `GF16` elements in ascending degree order) to the Mathlib
polynomial ring `GF216[X]`.

A `Poly` represents a polynomial over GF(2¹⁶) via its coefficient list:
  `coefficients = [a₀, a₁, …, aₙ]`
represents the polynomial `a₀ + a₁·X + … + aₙ·Xⁿ`.  The zero
polynomial is the unique polynomial with no terms (empty coefficient
list), and it evaluates to `0 : GF(2¹⁶)` at every point.

The bridge from the implementation to the mathematics is:

```
  Implementation Layer          Mathematical Layer
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  GF16 (value : U16)    ──────► GF216 = GF(2¹⁶)
          │    GF16toGF216         │
          │                        │
  Vec<GF16>             ──────► GF216[X]
          │    coeffsToGF216Poly   │
          │                        │
  Poly                  ──────► GF216[X]
               Poly.toGF216Poly
```

Conventions:
- `GF216`  = `GaloisField 2 16` (the finite field, from `Spqr.Math.Gf`).
- `GF216Poly` = `GF216[X]` (the univariate polynomial ring over GF(2¹⁶)).
- `GF16toGF216` maps a `spqr.encoding.gf.GF16` element (U16 value)
  to `GF216` via the `Nat.toGF216` bridge from `Spqr.Math.Gf`.
- `coeffsToGF216Poly` interprets a `List GF16` as a polynomial in
  `GF216[X]`.
- `Poly.toGF216Poly` is the canonical bridge from the Aeneas-extracted
  `spqr.encoding.polynomial.Poly` to the mathematical `GF216Poly`.
-/

open Aeneas Aeneas.Std Result
open Polynomial
open spqr.encoding.gf spqr.math.gf

abbrev GF216Poly := GF216[X]


namespace spqr.encoding.polynomial


/-! ## Constants -/

/-! ## Core definitions -/


/-- Interpret a list of `GF16` coefficients (in ascending degree order)
as a polynomial in `GF(2¹⁶)[X]`.

Given `cs = [a₀, a₁, …, aₙ]`, this produces:

  `C(GF16toGF216 a₀) + C(GF16toGF216 a₁)·X + … + C(GF16toGF216 aₙ)·Xⁿ`

where `C : GF216 →+* GF216[X]` is the constant-polynomial embedding.
The sum is indexed by `Fin cs.length`, ensuring well-typed access
to each coefficient. -/
noncomputable def coeffsToGF216Poly (cs : List spqr.encoding.gf.GF16) : GF216Poly :=
  ∑ i : Fin cs.length, C (GF16toGF216 (cs.get i)) * X ^ i.val

/-- Interpret a `Poly` as a mathematical polynomial in `GF(2¹⁶)[X]`.

This is the canonical bridge between the Aeneas-extracted
implementation type `spqr.encoding.polynomial.Poly` and the Mathlib
polynomial ring `GF216[X]`.  It reads the coefficient vector from
the `Poly` and maps each `GF16` coefficient through `GF16toGF216`.

This definition enables stating mathematical specifications for
functions like `Poly.zero`, `Poly.add_assign`, `Poly.compute_at`,
and `Poly.lagrange_interpolate` in terms of the algebraic properties
of `GF216[X]`. -/
noncomputable def Poly.toGF216Poly (p : Poly) : GF216Poly :=
  coeffsToGF216Poly p.coefficients.val

/-! ## Zero polynomial characterization -/

/-- **The empty coefficient list produces the zero polynomial.**

`coeffsToGF216Poly [] = 0` because `Fin 0` is empty, so the sum
over `Fin [].length` yields the additive identity. -/
lemma coeffsToGF216Poly_nil :
    coeffsToGF216Poly [] = 0 := by
  simp [coeffsToGF216Poly]

/-- **A `Poly` with an empty coefficient vector represents the zero
polynomial in `GF(2¹⁶)[X]`.**

This is the semantic content of `Poly.zero`: any `Poly` whose
`coefficients` list has length 0 maps to `0 : GF216Poly`.

Note: `Poly.zero_spec` (in
`Spqr/Specs/Encoding/Polynomial/Poly/Zero.lean`) now directly states
the mathematical postcondition:

  `zero capacity ⦃ fun result => result.toGF216Poly = 0 ⦄`

i.e. the Rust function `Poly::zero(capacity)` produces a value
whose mathematical interpretation is the zero polynomial in
GF(2¹⁶)[X].  This theorem remains useful as a standalone lemma
for any `Poly` with an empty coefficient vector, regardless of
how it was constructed. -/
theorem Poly.toGF216Poly_eq_zero (p : Poly)
    (h : p.coefficients.length = 0) :
    p.toGF216Poly = 0 := by
  unfold Poly.toGF216Poly
  have hnil : p.coefficients.val = [] :=
    List.eq_nil_of_length_eq_zero h
  rw [hnil]
  exact coeffsToGF216Poly_nil

/-! ## Coefficient characterization and basic lemmas of `coeffsToGF216Poly` -/

/-- The coefficient of `coeffsToGF216Poly cs` at position `m` is
`GF16toGF216 cs[m]` when `m < cs.length`, and `0` otherwise.

This parallels `natToGF2Poly_coeff` from `Spqr.Math.Gf`, lifting
the coefficient characterization from the bit level (GF(2)
polynomials representing individual field elements) to the
polynomial level (GF(2¹⁶) polynomials whose coefficients are
field elements). -/
lemma coeffsToGF216Poly_coeff (cs : List spqr.encoding.gf.GF16) (m : Nat) :
    (coeffsToGF216Poly cs).coeff m =
      if hm : m < cs.length
      then GF16toGF216 (cs.get ⟨m, hm⟩)
      else 0 := by
  unfold coeffsToGF216Poly
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow]
  split
  · rename_i hm
    rw [Finset.sum_eq_single_of_mem ⟨m, hm⟩ (Finset.mem_univ _)
        (fun ⟨j, hj⟩ _ hjm => by simp [show m ≠ j from fun h => hjm (Fin.ext h.symm)])]
    simp
  · rename_i hm
    push_neg at hm
    exact Finset.sum_eq_zero fun ⟨i, hi⟩ _ => by
      simp [show m ≠ i from by omega]

/-- Coefficients at positions `≥ cs.length` are zero.

This is a direct corollary of `coeffsToGF216Poly_coeff` and captures
the key invariant: the `Vec<GF16>` length bounds the support of the
polynomial.  In particular, the Rust constraint
`coefficients.len() ≤ MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 + 1`
implies that the polynomial has degree at most
`MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1`. -/
lemma coeffsToGF216Poly_coeff_eq_zero (cs : List spqr.encoding.gf.GF16)
    (m : Nat) (hm : cs.length ≤ m) :
    (coeffsToGF216Poly cs).coeff m = 0 := by
  rw [coeffsToGF216Poly_coeff]
  simp [show ¬(m < cs.length) from by omega]

/-- **`coeffsToGF216Poly [] = 0`** (simp-normal form). -/
@[simp]
lemma coeffsToGF216Poly_empty :
    coeffsToGF216Poly ([] : List spqr.encoding.gf.GF16) = 0 :=
  coeffsToGF216Poly_nil

/-! ## Singleton polynomial (degree-0 constant) -/

/-- A single-coefficient list `[a]` produces the constant polynomial
`C (GF16toGF216 a)` in `GF(2¹⁶)[X]`. -/
lemma coeffsToGF216Poly_singleton (a : spqr.encoding.gf.GF16) :
    coeffsToGF216Poly [a] = C (GF16toGF216 a) := by
  simp [coeffsToGF216Poly, Finset.univ_unique]

/-! ## Properties of `GF16toGF216` -/

/-- **`GF16toGF216` maps the zero GF16 element to `0 : GF216`.**

The zero element has `value.val = 0`, which encodes the natural
number `0`.  By `natToGF2Poly_zero` from `Spqr.Math.Gf`,
`natToGF2Poly 0 = 0`, and the ring homomorphism `φ` preserves
zero: `φ 0 = 0`. -/
lemma GF16toGF216_zero_val (g : spqr.encoding.gf.GF16) (h : g.value.val = 0) :
    GF16toGF216 g = 0 := by
  unfold GF16toGF216 Nat.toGF216
  rw [h]
  simp [natToGF2Poly_zero, map_zero]

/-- **`GF16toGF216` preserves the one element.**

The element with `value.val = 1` encodes the natural number `1`,
which corresponds to the constant polynomial `1` in GF(2)[X], and
maps to `1 : GF216` via `φ`. -/
lemma GF16toGF216_one_val (g : spqr.encoding.gf.GF16) (h : g.value.val = 1) :
    GF16toGF216 g = 1 := by
  unfold GF16toGF216 Nat.toGF216
  rw [h]
  simp [natToGF2Poly_one, map_one]

/-! ## Characteristic-2 facts in `GF216Poly` -/

/-- **GF(2¹⁶) has characteristic 2**: `(2 : GF216) = 0`.

Since `GF216 = GaloisField 2 16` is a field extension of `ZMod 2`,
it inherits characteristic 2.  This is the fundamental fact that
makes polynomial addition in the Rust implementation (coefficient-wise
XOR) correspond to polynomial addition in `GF216[X]`. -/
lemma GF216_two_eq_zero : (2 : GF216) = 0 :=
  CharP.cast_eq_zero GF216 2

/-- **In `GF216Poly`, every element is its own negation.**

This is a consequence of characteristic 2: `a + a = 0` implies
`-a = a`.  This parallels `zmod2_poly_neg_eq` from `Spqr.Math.Gf`,
now lifted from `GF2Poly` to `GF216Poly`. -/
lemma GF216Poly_neg_eq (a : GF216Poly) : -a = a := by
  have h : a + a = 0 := by
    ext n; simp only [coeff_add, coeff_zero]
    calc (a.coeff n) + (a.coeff n) = 2 * (a.coeff n) := by ring
      _ = 0 * (a.coeff n) := by rw [GF216_two_eq_zero]
      _ = 0 := by ring
  exact neg_eq_of_add_eq_zero_left h

/-- **In `GF216Poly`, subtraction equals addition.**

Direct consequence of `GF216Poly_neg_eq`: `a - b = a + (-b) = a + b`.
This mirrors `zmod2_poly_sub_eq_add` from `Spqr.Math.Gf`, and is the
algebraic reason that `GF16::sub` in the Rust implementation is
identical to `GF16::add` (both are XOR). -/
lemma GF216Poly_sub_eq_add (a b : GF216Poly) : a - b = a + b := by
  rw [sub_eq_add_neg, GF216Poly_neg_eq]

/-! ## Polynomial evaluation bridge -/

/-- Evaluate the mathematical interpretation of a `Poly` at a `GF16`
point.

This connects `Poly.compute_at` (which evaluates using Horner's
method in the implementation) to the mathematical `Polynomial.eval`
function from Mathlib.  The correspondence is:

  `Poly.evalAt p x = Polynomial.eval (GF16toGF216 x) (p.toGF216Poly)`

which says "evaluating the Poly at GF16 point x in the
implementation equals evaluating the corresponding GF216[X]
polynomial at the corresponding GF216 point". -/
noncomputable def Poly.evalAt (p : Poly) (x : spqr.encoding.gf.GF16) : GF216 :=
  (p.toGF216Poly).eval (GF16toGF216 x)

/-- **Evaluating the zero polynomial at any point gives `0 : GF216`.**

For any `Poly` with an empty coefficient list (such as the result
of `Poly.zero`), evaluation at any GF16 point yields `0`.  This is
the evaluation-level counterpart of `Poly.toGF216Poly_eq_zero`. -/
lemma Poly.evalAt_zero_poly (p : Poly) (x : spqr.encoding.gf.GF16)
    (h : p.coefficients.length = 0) :
    p.evalAt x = 0 := by
  unfold Poly.evalAt
  rw [Poly.toGF216Poly_eq_zero p h]
  simp

/-- **Evaluation of `coeffsToGF216Poly` equals the coefficient sum.**

Evaluating `coeffsToGF216Poly cs` at point `a` yields the sum
`∑ᵢ GF16toGF216(csᵢ) · a ^ i`, connecting the Mathlib `eval`
function to the explicit coefficient-power-sum computation used in
the implementation's `Poly.compute_at`.

This is the key linking lemma for verifying `Poly.compute_at`:
it says the mathematical evaluation of the polynomial agrees with
the sum-of-powers formula that the Rust function computes. -/
lemma coeffsToGF216Poly_eval (cs : List spqr.encoding.gf.GF16) (a : GF216) :
    (coeffsToGF216Poly cs).eval a =
      ∑ i : Fin cs.length,
        GF16toGF216 (cs.get i) * a ^ i.val := by
  unfold coeffsToGF216Poly
  simp [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]

/-! ## Linking lemmas: `Poly.toGF216Poly` and list operations -/

/-- **Extending the coefficient list by one element corresponds to
adding a new highest-degree term.**

If `cs ++ [a]` is the extended list, then
`coeffsToGF216Poly (cs ++ [a]) =
  coeffsToGF216Poly cs + C(GF16toGF216 a) · X^(cs.length)`.

This is the algebraic content of `Vec::push` on the coefficient vector:
appending a new coefficient extends the polynomial by one degree.
It is the key invariant for verifying `Poly.lagrange_interpolate_prepare`
and `Poly.lagrange_interpolate_complete`, which build polynomials
by successively pushing coefficients. -/
lemma coeffsToGF216Poly_append_singleton
    (cs : List spqr.encoding.gf.GF16) (a : spqr.encoding.gf.GF16) :
    coeffsToGF216Poly (cs ++ [a]) =
      coeffsToGF216Poly cs + C (GF16toGF216 a) * X ^ cs.length := by
  ext m
  simp only [coeffsToGF216Poly_coeff, coeff_add, coeff_C_mul, coeff_X_pow]
  by_cases hm1 : m < cs.length
  · -- m < cs.length < cs.length + 1: LHS = cs[m], RHS = cs[m] + 0
    have hm2 : m < (cs ++ [a]).length := by simp; omega
    have hm3 : m ≠ cs.length := by omega
    rw [dif_pos hm2, dif_pos hm1]
    simp only [hm3, if_false, mul_zero, add_zero]
    congr 1
    simp [List.get_eq_getElem, List.getElem_append_left hm1]
  · push_neg at hm1
    by_cases hm2 : m = cs.length
    · -- m = cs.length: LHS = a, RHS = 0 + a
      subst hm2
      have hlt : cs.length < (cs ++ [a]).length := by simp
      have hnotlt : ¬(cs.length < cs.length) := by omega
      rw [dif_pos hlt, dif_neg hnotlt]
      simp only [ite_true, mul_one, zero_add]
      congr 1
      simp [List.get_eq_getElem, List.getElem_append_right (Nat.le_refl cs.length)]
    · -- m > cs.length: LHS = 0, RHS = 0 + 0
      have hm3 : ¬(m < cs.length) := by omega
      have hm4 : ¬(m < (cs ++ [a]).length) := by simp; omega
      rw [dif_neg hm4, dif_neg hm3]
      simp [hm2]

/-! ## Polynomial addition (corresponds to `Poly.add_assign`) -/

/-- **Pointwise addition of equal-length coefficient lists corresponds
to polynomial addition in `GF216[X]`.**

If two coefficient lists have the same length and their GF16 values
are added pointwise (via XOR in the implementation), the resulting
polynomial is the sum of the two input polynomials.  This is the
algebraic specification for `Poly.add_assign` when both polynomials
have the same degree. -/
lemma coeffsToGF216Poly_add (cs ds : List spqr.encoding.gf.GF16)
    (hlen : cs.length = ds.length)
    (rs : List spqr.encoding.gf.GF16)
    (hrs : rs.length = cs.length)
    (hcoeff : ∀ i (hi : i < cs.length),
      GF16toGF216 (rs.get ⟨i, by omega⟩) =
        GF16toGF216 (cs.get ⟨i, hi⟩) +
        GF16toGF216 (ds.get ⟨i, by omega⟩)) :
    coeffsToGF216Poly rs =
      coeffsToGF216Poly cs + coeffsToGF216Poly ds := by
  ext m
  simp only [coeffsToGF216Poly_coeff, coeff_add]
  by_cases hm : m < cs.length
  · simp only [hm, show m < ds.length from by omega, show m < rs.length from by omega, dif_pos]
    exact hcoeff m hm
  · push_neg at hm
    simp [show ¬(m < cs.length) from by omega,
          show ¬(m < ds.length) from by omega,
          show ¬(m < rs.length) from by omega]

end spqr.encoding.polynomial
