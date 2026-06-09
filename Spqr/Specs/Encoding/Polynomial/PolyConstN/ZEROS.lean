/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Coeff.ListOps
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Math.Poly.Eval
import Spqr.Math.Poly.Lagrange.InterpolantSum
import Spqr.Math.Poly.Horner.Eval
import Spqr.Math.Poly.ExpectedTrailing.Basic
import Spqr.Math.Poly.Identities.Basic
import Spqr.Specs.Encoding.Gf.GF16.ZERO

/-!
# Spec theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyConst<N>}::ZEROS`

In the polynomial encoding layer, `PolyConst<N>` represents a fixed-size polynomial of degree
`< N` over GF(2¹⁶), stored as an array of `N` coefficients of type `GF16`.  The constant `ZEROS`
constructs the zero polynomial — a `PolyConst N` whose coefficient array is filled entirely with
`GF16::ZERO`:
  `ZEROS = PolyConst { coefficients := [GF16::ZERO; N] }`

Each coefficient `GF16::ZERO` has underlying `u16` value `0`, which lifts into
`GF216 = GaloisField 2 16` via the canonical chain `Nat → BinaryPoly → GF216`
(i.e. `Nat.toGF216 = BinaryPoly.toGF216 ∘ natToBinaryPoly`) to the additive identity `0 : GF216`.
Consequently, the polynomial interpretation `listToGF216Poly (ZEROS N).coefficients.val` is the zero
polynomial `0 : GF216[X]` in the polynomial ring GF(2¹⁶)[X], since every term in the defining sum
`∑ i, C (cs[i].toGF216) * X ^ i` vanishes.

**Source**: spqr/src/encoding/polynomial.rs (lines 363:4-365:6)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf Polynomial

namespace spqr.encoding.polynomial.PolyConst

@[simp]
theorem ZEROS_coefficients (N : Usize) :
    (ZEROS N).coefficients = Array.repeat N GF16.ZERO := by
  simp [ZEROS]

@[simp]
theorem ZEROS_coefficients_val (N : Usize) :
    (ZEROS N).coefficients.val = List.replicate N.val GF16.ZERO := by
  simp [ZEROS, Array.repeat_val]

@[simp]
theorem ZEROS_toGF216Poly (N : Usize) :
    listToGF216Poly (ZEROS N).coefficients.val = 0 := by
  rw [ZEROS_coefficients_val]
  exact listToGF216Poly_replicate_ZERO N.val

/-- **Spec theorem for `encoding.polynomial.PolyConst.ZEROS`**:

• The constant `ZEROS N` is a pure definition (no panics) and always succeeds for any `N : Usize`.
• The underlying coefficient array consists of `N` copies of `GF16.ZERO`:
    `(ZEROS N).coefficients = Array.repeat N GF16.ZERO`
  and equivalently:
    `(ZEROS N).coefficients.val = List.replicate N.val GF16.ZERO`.
• Each coefficient satisfies `coefficients[j].toGF216 = 0` for all `j < N`,
  since `GF16.ZERO.toGF216 = 0`.
• Lifting the coefficient list into the polynomial ring `GF216[X]` via `listToGF216Poly` yields the
  zero polynomial:
    `listToGF216Poly result.coefficients.val = 0`
  This follows because every coefficient lifts to `0 : GF216`, so the defining sum
  `∑ i, C (cs[i].toGF216) * X ^ i` is a sum of zeros.

**Source**: spqr/src/encoding/polynomial.rs (lines 363:4-365:6)
-/
@[step]
theorem ZEROS_spec (N : Usize) :
    ok (ZEROS N) ⦃ (result : PolyConst N) =>
      listToGF216Poly result.coefficients.val = 0 ⦄ := by
  simp [listToGF216Poly_replicate_ZERO]

end spqr.encoding.polynomial.PolyConst
