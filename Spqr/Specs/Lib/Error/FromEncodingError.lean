/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::{impl From<encoding::EncodingError> for Error}::from`

This trait implementation injects an `encoding::EncodingError` into the top-level `spqr::Error`
enum by wrapping it in the `Error::EncodingDecoding` constructor.  The injection is lossless —
the original `EncodingError` value is preserved inside the `Error` variant.

This is one of two `From` trait implementations for `Error` that are extracted by Aeneas
(the third, `From<serialize::Error>`, is excluded due to a name clash; see Plan_lib.md §2a).

**Source**: spqr/src/lib.rs (lines 134:4-136:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.Error.Insts.CoreConvertFromEncodingError

/--
**Spec theorem for `spqr.Error.Insts.CoreConvertFromEncodingError.from`**:

• Takes an `encoding.EncodingError` value `e`.
• Wraps it in the `Error.EncodingDecoding` constructor.
• Returns `ok (Error.EncodingDecoding e)`.

• The function always succeeds (no panic) for any `EncodingError` input.
• The injection is lossless: the inner error value is preserved verbatim.

The result satisfies the injective constructor postcondition:

  `result = Error.EncodingDecoding e`

The proof unfolds `from` to expose the direct constructor application.

**Source**: spqr/src/lib.rs (lines 134:4-136:5)
-/
@[step]
theorem from_spec (e : encoding.EncodingError) :
    Error.Insts.CoreConvertFromEncodingError.from e ⦃ (result : Error) =>
      result = Error.EncodingDecoding e ⦄ := by
  unfold Error.Insts.CoreConvertFromEncodingError.from
  simp_all

end spqr.Error.Insts.CoreConvertFromEncodingError
