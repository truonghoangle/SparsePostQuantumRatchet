/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
/-!
# Spec theorem for `spqr::encoding::polynomial::MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1`

Specification and proof for `encoding.polynomial.MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1`, the public
constant defining the highest degree polynomial that will appear in intermediate calculations for
Protocol V1 of the Sparse Post-Quantum Ratchet.

In Protocol V1, Lagrange interpolation is performed over at most 36 evaluation points, producing a
polynomial of degree at most 35. During the interpolation algorithm an intermediate product
polynomial of one degree higher is constructed, reaching degree 36. This constant records that
bound:
  `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 = 36#usize`

The constant is used in `hax_lib` annotations to constrain array sizes and loop bounds throughout
the polynomial encoding layer. It is unconditional and pure — its evaluation never fails and never
depends on any input.

**Source**: spqr/src/encoding/polynomial.rs (lines 75:0-75:60)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial

/-
natural language description:

• `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1` is a public module-level
  constant of type `usize`.
• It is defined as the literal `36`, recording the highest degree of
  any polynomial that Protocol V1 will construct during intermediate
  calculations (specifically during Lagrange interpolation, where
  a product polynomial of degree one higher than the stored maximum
  is temporarily needed).
• The constant is unconditional and pure — its evaluation never
  fails and never depends on any input.

natural language specs:

• The underlying `usize` value of
  `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1` is `36`:
    `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 = 36#usize`
  and equivalently as a natural number:
    `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1.val = 36`.
• Since a polynomial of degree `d` has `d + 1` coefficients,
  `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 + 1 = 37` gives the maximum
  number of coefficients in any intermediate polynomial during V1
  Lagrange interpolation.
• This constant is exactly one greater than
  `MAX_STORED_POLYNOMIAL_DEGREE_V1 = 35`, reflecting the extra
  degree introduced by the product accumulation step of the
  interpolation algorithm.
-/

/-- **The `usize` value of `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1` is `36#usize`**. -/
@[simp]
theorem MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1_eq :
    MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 = 36#usize := by
  simp [MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1]

/--
**The underlying natural-number value of `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1` is `36`**.
-/
@[simp]
theorem MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1_val :
    MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1.val = 36 := by
  simp

/--
**Spec and proof concerning `encoding.polynomial.MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1`**:

`MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1` is the constant `36 : usize`, recording the highest
polynomial degree arising in intermediate calculations during Protocol V1 Lagrange interpolation. A
polynomial of degree 36 has 37 coefficients, one more than the 36 coefficients of the maximum stored
polynomial (degree 35).

Concretely:

  `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1.val = 36`

The proof unfolds the definition and reduces the `usize` literal `36#usize` to its natural-number
value.

**Source**: spqr/src/encoding/polynomial.rs (lines 75:0-75:60)
-/
@[step]
theorem MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1_spec :
    ok MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 ⦃ (result : Std.Usize) =>
      result.val = 36 ⦄ := by
  simp

end spqr.encoding.polynomial
