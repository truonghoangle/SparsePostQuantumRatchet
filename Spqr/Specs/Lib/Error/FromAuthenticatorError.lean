/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::{impl From<authenticator::Error> for Error}::from`

This trait implementation maps any `authenticator::Error` to the top-level `Error::MacVerifyFailed`
variant.  Unlike the `From<EncodingError>` impl, this mapping is **lossy** — the specific
authenticator error value is discarded and replaced by the generic `MacVerifyFailed` variant.

This design reflects the security principle that MAC verification failures should not leak
information about the specific failure mode to callers.

**Source**: spqr/src/lib.rs (lines 146:4-148:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.Error.Insts.CoreConvertFromError

/--
**Spec theorem for `spqr.Error.Insts.CoreConvertFromError.from`**:

• Takes an `authenticator.Error` value `_v` (the value is discarded).
• Returns `ok Error.MacVerifyFailed` regardless of the input.

• The function always succeeds (no panic) for any `authenticator.Error` input.
• The mapping is **constant**: all authenticator errors map to `MacVerifyFailed`.

The result satisfies the constant-mapping postcondition:

  `result = Error.MacVerifyFailed`

The proof unfolds `from` to expose the direct constant return.

**Source**: spqr/src/lib.rs (lines 146:4-148:5)
-/
@[step]
theorem from_spec (_v : authenticator.Error) :
    Error.Insts.CoreConvertFromError.from _v ⦃ (result : Error) =>
      result = Error.MacVerifyFailed ⦄ := by
  unfold Error.Insts.CoreConvertFromError.from
  simp_all

end spqr.Error.Insts.CoreConvertFromError
