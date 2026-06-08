/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
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
import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Mathlib-related polynomial results

Pure mathematical results about polynomials over `GF216 = GF(2¹⁶)` and generic commutative rings.
These results are independent of the Aeneas extraction and serve as the mathematical foundation
for the specification proofs in `Spqr/Specs/Encoding/Polynomial`.

## Main statements

### Characteristic-2 identities
* `GF216_eq_of_add_eq_zero`: in `GF(2¹⁶)`, `a + b = 0` implies `a = b`.

### Generic polynomial coefficient lemmas
* `coeff_zero_C_add_X_sub_C_mul`: constant term of `C(a) + (X − C(b)) · P`.
* `coeff_succ_C_add_X_sub_C_mul`: higher coefficients of `C(a) + (X − C(b)) · P`.

### Polynomial evaluation
* `eval_eq_range_sum`: polynomial evaluation as a finite range sum when high coefficients vanish.

### Injectivity of `toGF216` at zero
* `Nat_toGF216_eq_zero`: if `n.toGF216 = 0` and `n < 2^16`, then `n = 0`.
* `GF16.toGF216_eq_zero_imp`: if `g.toGF216 = 0`, then `g.value.val = 0`.

### Replicate-zero polynomial
* `listToGF216Poly_replicate_ZERO`: a list of `GF16.ZERO` replicas represents the zero polynomial.
-/

open Polynomial
open spqr.math.gf spqr.encoding.gf spqr.encoding.polynomial

namespace spqr.encoding.polynomial

/-! ## Characteristic-2 identities -/

/-- In `GF(2¹⁶)`, `a + b = 0` implies `a = b`.
This follows from `a + b = 0  ⟹  a = a + 0 = a + (b + b) = (a + b) + b = 0 + b = b`,
using the characteristic-2 identity `b + b = 0`. -/
theorem GF216_eq_of_add_eq_zero {a b : GF216} (h : a + b = 0) : a = b := by
  have : b + b = 0 := GF216.add_self_eq_zero b
  have hab : a = a + 0 := by ring
  rw [hab, ← this, ← add_assoc, h, zero_add]

/-! ## Generic polynomial coefficient lemmas -/

/-- Constant term of `C(a) + (X − C(b)) · P` is `a − b · P.coeff 0`. -/
theorem coeff_zero_C_add_X_sub_C_mul {R : Type*} [CommRing R]
    (a b : R) (P : R[X]) :
    (C a + (X - C b) * P).coeff 0 = a - b * P.coeff 0 := by
  rw [sub_mul, coeff_add, coeff_sub, coeff_C_zero, coeff_X_mul_zero, coeff_C_mul]
  ring

/-- Higher coefficients of `C(a) + (X − C(b)) · P`:
  `(C(a) + (X − C(b)) · P).coeff (n + 1) = P.coeff n − b · P.coeff (n + 1)`. -/
theorem coeff_succ_C_add_X_sub_C_mul {R : Type*} [CommRing R]
    (a b : R) (P : R[X]) (n : ℕ) :
    (C a + (X - C b) * P).coeff (n + 1) = P.coeff n - b * P.coeff (n + 1) := by
  rw [sub_mul, coeff_add, coeff_sub, coeff_X_mul, coeff_C_mul]
  have : (C a).coeff (n + 1) = 0 := by rw [coeff_C]; exact if_neg (by omega)
  rw [this]; ring

/-! ## Polynomial evaluation -/

/--
If all coefficients of `p` at positions `≥ n` are zero, then `p.eval a` equals the finite sum
`∑ j ∈ Finset.range n, p.coeff j * a ^ j`.  This extends `Polynomial.eval_eq_sum_range`
(which uses `natDegree + 1` as the upper bound) to any upper bound `n` beyond which all
coefficients vanish.
-/
theorem eval_eq_range_sum (p : GF216Poly) (a : GF216) (n : ℕ)
    (h : ∀ j, n ≤ j → p.coeff j = 0) :
    p.eval a = ∑ j ∈ Finset.range n, p.coeff j * a ^ j := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_subset
  · intro j hj
    rw [Finset.mem_range]
    by_contra h_ge; push Not at h_ge
    exact (Polynomial.mem_support_iff.mp hj) (h j h_ge)
  · intro j _ hj
    have : p.coeff j = 0 := by
      by_contra h_ne
      exact hj (Polynomial.mem_support_iff.mpr h_ne)
    rw [this, zero_mul]

/-! ## Injectivity of `toGF216` at zero -/

/-- If `n.toGF216 = 0` and `n < 2^16`, then `n = 0`.
Uses the kernel characterization of the ring homomorphism
`BinaryPoly.toGF216`: since `polyGF2` is irreducible in the PID
`BinaryPoly`, the ideal `(polyGF2)` is maximal, and
`ker BinaryPoly.toGF216 = (polyGF2)`.  Any element of
`ker BinaryPoly.toGF216` with degree `< 16` must therefore be
zero. -/
theorem Nat_toGF216_eq_zero
    {n : Nat} (hn : n < 2 ^ 16) (h : n.toGF216 = 0) : n = 0 := by
  open spqr.encoding.gf.unaccelerated in
  unfold Nat.toGF216 at h
  by_contra hn0
  have hne : natToBinaryPoly n ≠ 0 := fun h0 =>
    hn0 (natToBinaryPoly_inj
      (by rw [h0, natToBinaryPoly_zero] : natToBinaryPoly n = natToBinaryPoly 0))
  have hcoeff_zero : ∀ m, 16 ≤ m → (natToBinaryPoly n).coeff m = 0 := by
    intro m hm
    rw [natToBinaryPoly_coeff]
    simp [Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num : 0 < 2) hm))]
  have hnd : (natToBinaryPoly n).natDegree < 16 := by
    by_contra h_not
    push Not at h_not
    have h_lc : (natToBinaryPoly n).coeff (natToBinaryPoly n).natDegree ≠ 0 := by
      intro h0; exact hne (Polynomial.leadingCoeff_eq_zero.mp h0)
    exact h_lc (hcoeff_zero _ h_not)
  have hprime : Prime polyGF2 :=
    (UniqueFactorizationMonoid.irreducible_iff_prime).mp polyGF2_irreducible
  have hprime_ideal : (Ideal.span {polyGF2}).IsPrime :=
    (Ideal.span_singleton_prime polyGF2_monic.ne_zero).mpr hprime
  have hne_bot : Ideal.span ({polyGF2} : Set BinaryPoly) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact polyGF2_monic.ne_zero
  have hmax : (Ideal.span {polyGF2}).IsMaximal :=
    Ideal.IsPrime.isMaximal hprime_ideal hne_bot
  have hle : Ideal.span {polyGF2} ≤ RingHom.ker BinaryPoly.toGF216 :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (RingHom.mem_ker.mpr BinaryPoly.toGF216_polyGF2))
  have hker_eq : RingHom.ker BinaryPoly.toGF216 = Ideal.span {polyGF2} := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact heq.symm
    · exact absurd (hmax.out.2 _ hlt) (RingHom.ker_ne_top BinaryPoly.toGF216)
  have hmem : polyGF2 ∣ natToBinaryPoly n := by
    rwa [← Ideal.mem_span_singleton, ← hker_eq, RingHom.mem_ker]
  have := Polynomial.natDegree_le_of_dvd hmem hne
  rw [polyGF2_natDegree] at this
  omega

/-- If `g.toGF216 = 0`, then `g.value.val = 0`.
This is the reverse direction of `GF16.toGF216_zero_val`. -/
theorem GF16_toGF216_eq_zero_imp
    (g : GF16) (h : g.toGF216 = 0) :
    g.value.val = 0 := by
  unfold GF16.toGF216 at h
  exact Nat_toGF216_eq_zero (by have := g.value.hBounds; scalar_tac) h

/-! ## Replicate-zero polynomial -/

/-- A `List` of `n` copies of `GF16.ZERO` represents the zero polynomial in `GF216[X]`.
Since `GF16.ZERO.toGF216 = 0`, every term `C (cs[i].toGF216) * X ^ i` vanishes. -/
theorem listToGF216Poly_replicate_ZERO (n : Nat) :
    listToGF216Poly (List.replicate n GF16.ZERO) = 0 := by
  simp only [listToGF216Poly]
  apply Finset.sum_eq_zero
  intro i _
  simp only [List.get_eq_getElem, List.getElem_replicate, GF16.ZERO]
  simp [GF16.toGF216, Nat.toGF216, natToBinaryPoly_zero, map_zero]

end spqr.encoding.polynomial
