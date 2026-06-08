/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::{From<PolynomialError> for EncodingError}::from`

`EncodingError` is the algebraic sum type

  `EncodingError ≃ PolynomialError  ⊕  {ChunkIndexDecodingError}  ⊕  {ChunkDataDecodingError}`

whose `PolynomialError`-branch carries a `PolynomialError` payload verbatim.  The `From` instance
realises the canonical injection of `PolynomialError` into this sum type, lifting a value through
the `EncodingError.PolynomialError` constructor.

The function proceeds in a single stage:
  1. Wrap the input `value : PolynomialError` in the `EncodingError.PolynomialError` constructor,
     producing `EncodingError.PolynomialError value`, and return it via `ok`.

It is total, pure, and never fails — no computation is performed on the payload, which is preserved
unchanged.

**Source**: spqr/src/encoding.rs (lines 19:4-21:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.EncodingError.Insts.CoreConvertFromPolynomialError

/-- **Spec theorem for `encoding.EncodingError.Insts.CoreConvertFromPolynomialError.from`**:

Canonical injection of `PolynomialError` into the `EncodingError` sum type, lifting `value` through
the `EncodingError.PolynomialError` constructor.

The function is the identity composed with `EncodingError.PolynomialError`, returning its result
through `ok`.

The result satisfies the constructor-level specification:
  `result = EncodingError.PolynomialError value`

This establishes that `from` realises — at the level of `Result encoding.EncodingError` — the
inclusion

  `ι : PolynomialError ↪ EncodingError,   ι value = EncodingError.PolynomialError value`

of `PolynomialError` into the algebraic sum `EncodingError`.

**Source**: spqr/src/encoding.rs (lines 19:4-21:5)
-/
@[step]
theorem from_spec (value : encoding.polynomial.PolynomialError) :
    «from» value ⦃ (result : encoding.EncodingError) =>
      result = encoding.EncodingError.PolynomialError value ⦄ := by
  unfold «from»
  step*

end spqr.encoding.EncodingError.Insts.CoreConvertFromPolynomialError
