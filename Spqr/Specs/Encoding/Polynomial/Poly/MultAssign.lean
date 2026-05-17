/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Gf.ParallelMult

/-!
# Spec theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::mult_assign`

The Rust function `Poly::mult_assign` (in `src/encoding/polynomial.rs`, lines 250:4-252:5) implements
in-place polynomial scalar multiplication `self *= m` in GF(2¹⁶)[X].  It delegates to
`gf::parallel_mult`, which multiplies every coefficient of the polynomial by the scalar `m`:

```
fn mult_assign(&mut self, m: GF16) {
    gf::parallel_mult(m, &mut self.coefficients);
}
```

Concretely, `mult_assign self m`:
  1. Obtains a mutable reference to `self.coefficients` via `Vec::deref_mut`.
  2. Delegates to `encoding.gf.parallel_mult m coefficients`, which processes the coefficient slice
     in strides of two (via the hardware-accelerated or software carry-less multiplication
     `mul2_u16`), multiplying each coefficient by `m` in GF(2¹⁶), with a trailing-element fix-up
     for odd-length slices via `MulAssign<GF16> for GF16`.
  3. Writes the modified coefficients back into the `Poly` via the `deref_mut_back` closure.

After the operation, the result polynomial represents the scalar product `C(m) · self` in
`GF216[X] = (GaloisField 2 16)[X]`, where `C(m)` denotes the constant polynomial embedding of the
GF(2¹⁶) scalar `m`.

In GF(2¹⁶) (characteristic 2), multiplication is carry-less polynomial multiplication modulo the
irreducible polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

The Aeneas-extracted Lean function `encoding.polynomial.Poly.mult_assign` is a direct delegation:
  1. `alloc.vec.Vec.deref_mut self.coefficients` — obtains the coefficient slice and a back-closure.
  2. `encoding.gf.parallel_mult m s` — multiplies every element of the slice by `m` in GF(2¹⁶).
  3. `deref_mut_back s1` — reconstructs the `Vec` from the modified slice.
  4. Returns `{ coefficients := v }`.

Since the delegation introduces no additional logic beyond the `deref_mut`/`deref_mut_back` wrapper,
the postcondition is derived from the `parallel_mult` specification (`parallel_mult_spec`): every
coefficient of the result is the GF(2¹⁶) product of `m` with the corresponding original
coefficient, which at the polynomial level corresponds to scalar multiplication by
`C (m.toGF216)`.

**Source**: spqr/src/encoding/polynomial.rs (lines 250:4-252:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly

/--
**Spec theorem for `encoding.polynomial.Poly.mult_assign`**:

• The function always succeeds (no panic) provided the coefficient vector length satisfies
  `self.coefficients.val.length + 2 ≤ Usize.max`, since the underlying `parallel_mult` requires
  this bound for its stride-of-two loop (mirrors the Rust
  `#[requires(into.len() <= usize::MAX - 2)]` annotation on `parallel_mult`).

• **Polynomial scalar multiplication postcondition**:
    `result.toGF216Poly = C (m.toGF216) * self.toGF216Poly`
  where `toGF216Poly : Poly → GF216Poly` interprets the coefficient vector as a polynomial in
  `GF216[X] = (GaloisField 2 16)[X]`, and `C : GF216 →+* GF216[X]` is the constant-polynomial
  embedding.

  This states that scaling every coefficient by `m` in GF(2¹⁶) corresponds to multiplying the
  polynomial by the constant `C (m.toGF216)` in `GF216[X]`.  Equivalently, every coefficient
  `result.coefficients[j]` satisfies
    `result.coefficients[j].toGF216 = m.toGF216 * self.coefficients[j].toGF216`
  in GF(2¹⁶), and the coefficient vector length is preserved.

**Source**: spqr/src/encoding/polynomial.rs (lines 250:4-252:5)
-/
@[step]
theorem mult_assign_spec
    (self : Poly) (m : GF16)
    (h_len : self.coefficients.val.length + 2 ≤ Usize.max) :
    mult_assign self m ⦃ (result : Poly) =>
      result.coefficients.val.length = self.coefficients.val.length ∧
      result.toGF216Poly = C (m.toGF216) * self.toGF216Poly ⦄ := by
  unfold mult_assign
  simp only [alloc.vec.Vec.deref_mut, lift, bind_tc_ok]
  step*
  refine ⟨by simp_all [Slice.length], ?_⟩
  simp only [Poly.toGF216Poly]
  apply listToGF216Poly_eq_of_coeffs
  · intro j hj
    rw [coeff_C_mul, ← getElem_bang_toGF216_eq_coeff]
    simp only [List.get_eq_getElem, Slice.length] at *
    simp_all
    grind
  · intro j hj
    rw [coeff_C_mul, listToGF216Poly_coeff_eq_zero _ _ (by simp_all [Slice.length])]
    ring


end spqr.encoding.polynomial.Poly
