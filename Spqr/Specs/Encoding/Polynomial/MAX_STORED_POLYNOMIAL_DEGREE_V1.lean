/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
/-!
# Spec theorem for `spqr::encoding::polynomial::MAX_STORED_POLYNOMIAL_DEGREE_V1`

Specification and proof for `encoding.polynomial.MAX_STORED_POLYNOMIAL_DEGREE_V1`, the public
constant defining the highest degree polynomial that will be stored for Protocol V1 of the Sparse
Post-Quantum Ratchet.

In Protocol V1, Lagrange interpolation is performed over at most 36 evaluation points, producing a
polynomial of degree at most 35. This constant records that bound:
  `MAX_STORED_POLYNOMIAL_DEGREE_V1 = 35#usize`

The constant is used in `hax_lib` annotations to constrain array sizes and loop bounds throughout
the polynomial encoding layer. It is unconditional and pure — its evaluation never fails and never
depends on any input.

**Source**: spqr/src/encoding/polynomial.rs (lines 69:0-69:54)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial

/-
natural language description:

• `MAX_STORED_POLYNOMIAL_DEGREE_V1` is a public module-level constant
  of type `usize`.
• It is defined as the literal `35`, recording the highest degree of
  any polynomial that Protocol V1 will store (as opposed to
  intermediate computation, which may reach degree 36).
• The constant is unconditional and pure — its evaluation never
  fails and never depends on any input.

natural language specs:

• The underlying `usize` value of `MAX_STORED_POLYNOMIAL_DEGREE_V1`
  is `35`:
    `MAX_STORED_POLYNOMIAL_DEGREE_V1 = 35#usize`
  and equivalently as a natural number:
    `MAX_STORED_POLYNOMIAL_DEGREE_V1.val = 35`.
• Since a polynomial of degree `d` has `d + 1` coefficients,
  `MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1 = 36` gives the maximum
  number of coefficients (and hence evaluation points) used in
  the V1 erasure-coding scheme.
-/

/-- **The `usize` value of `MAX_STORED_POLYNOMIAL_DEGREE_V1` is `35#usize`**. -/
@[simp]
theorem MAX_STORED_POLYNOMIAL_DEGREE_V1_eq :
    MAX_STORED_POLYNOMIAL_DEGREE_V1 = 35#usize := by
  simp [MAX_STORED_POLYNOMIAL_DEGREE_V1]

/--
**The underlying natural-number value of `MAX_STORED_POLYNOMIAL_DEGREE_V1` is `35`**.
-/
@[simp]
theorem MAX_STORED_POLYNOMIAL_DEGREE_V1_val :
    MAX_STORED_POLYNOMIAL_DEGREE_V1.val = 35 := by
  simp

/--
**Spec and proof concerning `encoding.polynomial.MAX_STORED_POLYNOMIAL_DEGREE_V1`**:

`MAX_STORED_POLYNOMIAL_DEGREE_V1` is the constant `35 : usize`, recording the highest polynomial
degree stored in Protocol V1. A polynomial of degree 35 has 36 coefficients, matching the maximum
number of Lagrange interpolation points used in V1.

Concretely:

  `MAX_STORED_POLYNOMIAL_DEGREE_V1.val = 35`

The proof unfolds the definition and reduces the `usize` literal `35#usize` to its natural-number
value.

**Source**: spqr/src/encoding/polynomial.rs (lines 69:0-69:54)
-/
@[step]
theorem MAX_STORED_POLYNOMIAL_DEGREE_V1_spec :
    ok MAX_STORED_POLYNOMIAL_DEGREE_V1 ⦃ (result : Std.Usize) =>
      result.val = 35 ⦄ := by
  simp

end spqr.encoding.polynomial
