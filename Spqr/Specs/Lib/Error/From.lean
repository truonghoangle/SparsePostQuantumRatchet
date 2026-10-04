/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for
# `spqr::{impl core::convert::From<spqr::encoding::EncodingError> for spqr::Error}::from`

Lifts an encoding error into `spqr::Error` via the `Error::EncodingDecoding` constructor.
A pure, infallible, injective constructor application.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.Error.Insts.CoreConvertFromEncodingError

/-- **Spec theorem for `spqr.Error.Insts.CoreConvertFromEncodingError.from`**:

• Wraps `e : encoding.EncodingError` in `Error.EncodingDecoding`.
• Always succeeds: returns `ok (Error.EncodingDecoding e)`.

Postcondition: `result = Error.EncodingDecoding e`. -/
@[step]
theorem from_spec (e : encoding.EncodingError) :
    «from» e ⦃ (result : Error) =>
      result = Error.EncodingDecoding e ⦄ := by
  unfold «from»
  simp

end spqr.Error.Insts.CoreConvertFromEncodingError

/-! # Spec theorem for `spqr::{impl From<authenticator::Error> for Error}::from`

Maps every `authenticator::Error` to `Error::MacVerifyFailed`. The mapping is
**lossy**: the specific authenticator error is discarded so MAC verification
failures do not leak their failure mode.

**Source**: spqr/src/lib.rs

## Note (LOW; spec-only — wrong error mapping)

The blanket mapping of **all** `authenticator::Error` variants to `Error.MacVerifyFailed` is
incorrect for the key-validation variants (`AuthenticatorRootKeyPresent/Missing`,
`AuthenticatorMacKeyPresent/Missing`). These represent **deserialisation failures** from
`from_pb`, not MAC verification failures. libsignal treats `MacVerifyFailed` as
`InvalidMessage` (triggers message-retry), whereas deserialisation errors should map to
`Error.StateDecode` which libsignal treats as `InvalidState` (triggers session-reset).

The theorem `from_maps_all_to_mac_verify_failed` documents the defect: even deserialisation-
class variants map to `MacVerifyFailed`. The theorem `from_wrong_mapping_for_key_errors`
demonstrates the specific incorrect mapping for each key-validation variant.
See `docs/listDefects.md`. -/

open Aeneas Aeneas.Std Result

namespace spqr.Error.Insts.CoreConvertFromError

/-- **Spec theorem for `spqr.Error.Insts.CoreConvertFromError.from`**:

• Discards the input `v : authenticator.Error`.
• Always succeeds: returns `ok Error.MacVerifyFailed` (constant mapping).

Postcondition: `result = Error.MacVerifyFailed`. -/
@[step]
theorem from_spec (v : authenticator.Error) :
    Error.Insts.CoreConvertFromError.from v ⦃ (result : Error) =>
      result = Error.MacVerifyFailed ⦄ := by
  unfold Error.Insts.CoreConvertFromError.from
  simp_all

/-- **All authenticator errors map to `MacVerifyFailed`, regardless of variant.**

This theorem makes the blanket mapping explicit: no matter which `authenticator.Error` variant
is provided, the result is always `Error.MacVerifyFailed`. For `InvalidCtMac` and `InvalidHdrMac`
this is correct. For the key-validation variants it is wrong
(see `from_wrong_mapping_for_key_errors`). -/
theorem from_maps_all_to_mac_verify_failed (v : authenticator.Error) :
    Error.Insts.CoreConvertFromError.from v ⦃ (result : Error) =>
      result = Error.MacVerifyFailed ∧ result ≠ Error.StateDecode ⦄ := by
  unfold Error.Insts.CoreConvertFromError.from
  simp_all

/-- **Key-validation variants incorrectly map to `MacVerifyFailed` instead of `StateDecode`.**

When construct `AuthenticatorRootKeyPresent/Missing` and
`AuthenticatorMacKeyPresent/Missing` during `from_pb` validation are fixed,
the `From` impl should map
them to `Error.StateDecode` (deserialisation failure) rather than `Error.MacVerifyFailed`
(bad message). This theorem proves the current mapping is wrong for each key-validation variant:
the result is `MacVerifyFailed` when it should be `StateDecode`.

**Expected fix in Rust** (`src/lib.rs` L145–148):
```
impl From<authenticator::Error> for Error {
    fn from(v: authenticator::Error) -> Self {
        match v {
            authenticator::Error::InvalidCtMac
            | authenticator::Error::InvalidHdrMac => Error::MacVerifyFailed,
            _ => Error::StateDecode,  // D36 fix
        }
    }
}
``` -/
theorem from_wrong_mapping_for_key_errors :
    (Error.Insts.CoreConvertFromError.from authenticator.Error.AuthenticatorRootKeyPresent
      ⦃ (r : Error) => r = Error.MacVerifyFailed ⦄) ∧
    (Error.Insts.CoreConvertFromError.from authenticator.Error.AuthenticatorRootKeyMissing
      ⦃ (r : Error) => r = Error.MacVerifyFailed ⦄) ∧
    (Error.Insts.CoreConvertFromError.from authenticator.Error.AuthenticatorMacKeyPresent
      ⦃ (r : Error) => r = Error.MacVerifyFailed ⦄) ∧
    (Error.Insts.CoreConvertFromError.from authenticator.Error.AuthenticatorMacKeyMissing
      ⦃ (r : Error) => r = Error.MacVerifyFailed ⦄) := by
  unfold Error.Insts.CoreConvertFromError.from
  simp_all

end spqr.Error.Insts.CoreConvertFromError
