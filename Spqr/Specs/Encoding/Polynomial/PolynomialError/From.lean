/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::{core::convert::From<spqr::encoding::polynomial::PolynomialError> for spqr::encoding::EncodingError}::from`

The `From<PolynomialError> for EncodingError` implementation is the canonical injection of
`PolynomialError` into the `EncodingError` sum type.  The function simply wraps its input `value`
in the `EncodingError.PolynomialError` constructor:
  `from(value) = ok (EncodingError.PolynomialError value)`

The conversion is unconditional and pure — it never fails, performs no computation on its input,
and preserves the `PolynomialError` payload verbatim.

**Source**: spqr/src/encoding.rs (lines 19:4-21:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.EncodingError.Insts.CoreConvertFromPolynomialError

@[simp]
theorem from_eq (value : encoding.polynomial.PolynomialError) :
    «from» value = ok (encoding.EncodingError.PolynomialError value) := by
  simp [«from»]

/-- **Spec theorem for `encoding.EncodingError.Insts.CoreConvertFromPolynomialError.from`**:

• The function always succeeds (no panic / no error) for any `PolynomialError` input.
• The result is exactly `EncodingError.PolynomialError value`, i.e. the `PolynomialError` variant
  of `EncodingError` carrying the original `value` unchanged.

In Hoare-triple form, calling `from value` produces an `EncodingError` `result` satisfying:
    `result = EncodingError.PolynomialError value`

This is the trivial embedding of the `PolynomialError` sum type into the larger `EncodingError`
sum type, and it follows directly from the definition.

**Source**: spqr/src/encoding.rs (lines 19:4-21:5)
-/
@[step]
theorem from_spec (value : encoding.polynomial.PolynomialError) :
    «from» value ⦃ (result : encoding.EncodingError) =>
      result = encoding.EncodingError.PolynomialError value ⦄ := by
  simp [«from»]

end spqr.encoding.EncodingError.Insts.CoreConvertFromPolynomialError
