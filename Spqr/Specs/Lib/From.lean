/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `From<EncodingError> for Error`

The `Error` enum contains, among other variants:
```rust
#[error("Encoding/Decoding error: {0}")]
EncodingDecoding(encoding::EncodingError),
```
The `From<encoding::EncodingError>` implementation is:
```rust
impl From<encoding::EncodingError> for Error {
    fn from(e: encoding::EncodingError) -> Error {
        Error::EncodingDecoding(e)
    }
}
```
After extraction the Lean definition is:
```
def Error.Insts.CoreConvertFromEncodingError.from
  (e : encoding.EncodingError) : Result Error := do
  ok (Error.EncodingDecoding e)
```

The function simply wraps an `encoding.EncodingError` in the `Error.EncodingDecoding` constructor.
It is unconditional and pure — it takes one argument, never fails, and always returns the
corresponding `Error` variant.

**Source**: spqr/src/lib.rs (lines 134:4-136:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-- **`from` unfolds to `Error.EncodingDecoding`**.

`Error.Insts.CoreConvertFromEncodingError.from e` always succeeds and returns
`Error.EncodingDecoding e`. -/
@[simp]
theorem from_encoding_error_eq (e : encoding.EncodingError) :
    Error.Insts.CoreConvertFromEncodingError.from e =
      ok (Error.EncodingDecoding e) := by
  simp [Error.Insts.CoreConvertFromEncodingError.from]

/--
**Spec theorem for `Error.Insts.CoreConvertFromEncodingError.from`**:

• The function always succeeds (no panic / no error) for any `encoding.EncodingError` input.
  It simply wraps the input in the `Error.EncodingDecoding` constructor, which is the Lean
  translation of the Rust `Error::EncodingDecoding(e)` variant.
• The postcondition states that the result is exactly `Error.EncodingDecoding e`, establishing
  that the `From` trait implementation faithfully lifts encoding errors into the top-level
  `Error` type without loss of information.
• The conversion is injective: distinct `EncodingError` values produce distinct `Error` values.

**Source**: spqr/src/lib.rs (lines 134:4-136:5)
-/
@[step]
theorem from_encoding_error_spec (e : encoding.EncodingError) :
    Error.Insts.CoreConvertFromEncodingError.from e
      ⦃ (result : Error) =>
        result = Error.EncodingDecoding e ⦄ := by
  unfold Error.Insts.CoreConvertFromEncodingError.from
  step*

/-!
# Spec theorem for `From<authenticator::Error> for Error`

The `Error` enum contains, among other variants:
```rust
#[error("MAC verification failed")]
MacVerifyFailed,
```
The `From<authenticator::Error>` implementation is:
```rust
impl From<authenticator::Error> for Error {
    fn from(_v: authenticator::Error) -> Self {
        Error::MacVerifyFailed
    }
}
```
After extraction the Lean definition is:
```
def Error.Insts.CoreConvertFromError.from
  (_v : authenticator.Error) : Result Error := do
  ok Error.MacVerifyFailed
```

Unlike the `From<encoding::EncodingError>` conversion above, this function is a **constant map**: it
discards the concrete `authenticator.Error` variant and unconditionally returns
`Error.MacVerifyFailed`.  The conversion is therefore lossy — all six `authenticator.Error`
constructors (`InvalidCtMac`, `InvalidHdrMac`, `AuthenticatorRootKeyPresent`,
`AuthenticatorRootKeyMissing`, `AuthenticatorMacKeyPresent`, `AuthenticatorMacKeyMissing`) are
mapped to the single `Error.MacVerifyFailed` variant, so the original error information is erased.

The function is unconditional and pure — it never fails, takes one (unused) argument, and always
returns the same `Error` variant.

**Source**: spqr/src/lib.rs (lines 146:4-148:5)
-/

/-- **`from` unfolds to `Error.MacVerifyFailed`**.

`Error.Insts.CoreConvertFromError.from _v` always succeeds and returns
`Error.MacVerifyFailed`, regardless of the input `_v`. -/
@[simp]
theorem from_authenticator_error_eq (_v : authenticator.Error) :
    Error.Insts.CoreConvertFromError.from _v =
      ok (Error.MacVerifyFailed) := by
  simp [Error.Insts.CoreConvertFromError.from]

/--
**Spec theorem for `Error.Insts.CoreConvertFromError.from`**:

• The function always succeeds (no panic / no error) for any `authenticator.Error` input.
  It ignores the input and unconditionally returns `Error.MacVerifyFailed`, which is the Lean
  translation of the Rust `Error::MacVerifyFailed` variant.
• The postcondition states that the result is exactly `Error.MacVerifyFailed`, independent of
  the input — establishing that the `From` trait implementation is a constant function that maps
  all authenticator errors to the MAC-verification-failure variant of the top-level `Error` type.
• Unlike `from_encoding_error_spec`, this conversion is **not** injective: distinct
  `authenticator.Error` values all produce the same `Error` value.

**Source**: spqr/src/lib.rs (lines 146:4-148:5)
-/
@[step]
theorem from_authenticator_error_spec (_v : authenticator.Error) :
    Error.Insts.CoreConvertFromError.from _v
      ⦃ (result : Error) =>
        result = Error.MacVerifyFailed ⦄ := by
  unfold Error.Insts.CoreConvertFromError.from
  step*

end spqr

/-!
# Spec theorem for `From<Version> for u8`

The `Version` enum has two variants:
```rust
pub enum Version {
    V0 = 0,
    V1 = 1,
}
```
The `From<Version> for u8` implementation converts a `Version` to its byte discriminant:
```rust
impl From<Version> for u8 {
    fn from(v: Version) -> u8 {
        match v {
            Version::V0 => 0,
            Version::V1 => 1,
        }
    }
}
```
After extraction the Lean definition is:
```
def U8.Insts.CoreConvertFromVersion.from
  (v : proto.pq_ratchet.Version) : Result Std.U8 := do
  match v with
  | proto.pq_ratchet.Version.V0 => ok 0#u8
  | proto.pq_ratchet.Version.V1 => ok 1#u8
```

The function is total and pure — it pattern-matches on the `Version` variant, returns `0` for `V0`
and `1` for `V1`, and never fails. It is the right inverse of `TryFrom<u8> for Version`: for each
variant `v`, `try_from (from v) = ok (Ok v)`.

**Source**: spqr/src/lib.rs (lines 190:4-195:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-- **`from V0` unfolds to `0`**.

`U8.Insts.CoreConvertFromVersion.from V0` always succeeds and returns `0#u8`. -/
@[simp]
theorem from_version_V0_eq :
    U8.Insts.CoreConvertFromVersion.from proto.pq_ratchet.Version.V0 =
      ok 0#u8 := by
  simp [U8.Insts.CoreConvertFromVersion.from]

/-- **`from V1` unfolds to `1`**.

`U8.Insts.CoreConvertFromVersion.from V1` always succeeds and returns `1#u8`. -/
@[simp]
theorem from_version_V1_eq :
    U8.Insts.CoreConvertFromVersion.from proto.pq_ratchet.Version.V1 =
      ok 1#u8 := by
  simp [U8.Insts.CoreConvertFromVersion.from]

/-- **Spec theorem for `U8.Insts.CoreConvertFromVersion.from`**:

Conversion of a `proto.pq_ratchet.Version` to its `u8` discriminant:
  • `V0 ↦ 0`
  • `V1 ↦ 1`

The function always succeeds (no panic / no error) for any `Version` input. The postcondition
states that the result is the byte corresponding to the input variant — establishing that the
`From` trait implementation faithfully serialises the `Version` enum to its numeric discriminant.

The conversion is injective: distinct `Version` values produce distinct `U8` values.
It is the right inverse of `TryFrom<u8> for Version`: for each variant `v`,
`try_from (from v) = ok (Ok v)`.

**Source**: spqr/src/lib.rs (lines 190:4-195:5)
-/
@[step]
theorem from_version_spec (v : proto.pq_ratchet.Version) :
    U8.Insts.CoreConvertFromVersion.from v
      ⦃ (result : Std.U8) =>
        result = match v with
          | .V0 => 0#u8
          | .V1 => 1#u8 ⦄ := by
  unfold U8.Insts.CoreConvertFromVersion.from
  step*

end spqr
