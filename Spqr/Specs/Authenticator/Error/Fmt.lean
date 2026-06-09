/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Lib.Fmt

/-!
# Spec theorem for `spqr::authenticator::{impl core::fmt::Debug for spqr::authenticator::Error}::fmt`

The `authenticator.Error` enum has six unit variants:
```rust
#[derive(Debug, thiserror::Error)]
pub enum Error {
    InvalidCtMac,
    InvalidHdrMac,
    AuthenticatorRootKeyPresent,
    AuthenticatorRootKeyMissing,
    AuthenticatorMacKeyPresent,
    AuthenticatorMacKeyMissing,
}
```
The `#[derive(Debug)]` attribute auto-generates the `fmt::Debug` implementation, which formats
each variant by writing its name as a string via `core.fmt.Formatter.write_str`. Since every
variant is a unit variant (no payload), no `debug_tuple_field1_finish` calls are needed.

After extraction the Lean definition is:
```
def authenticator.Error.Insts.CoreFmtDebug.fmt
  (self : authenticator.Error) (f : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  := do
  match self with
  | authenticator.Error.InvalidCtMac =>
    core.fmt.Formatter.write_str f (toStr "InvalidCtMac")
  | authenticator.Error.InvalidHdrMac =>
    core.fmt.Formatter.write_str f (toStr "InvalidHdrMac")
  | authenticator.Error.AuthenticatorRootKeyPresent =>
    core.fmt.Formatter.write_str f (toStr "AuthenticatorRootKeyPresent")
  | authenticator.Error.AuthenticatorRootKeyMissing =>
    core.fmt.Formatter.write_str f (toStr "AuthenticatorRootKeyMissing")
  | authenticator.Error.AuthenticatorMacKeyPresent =>
    core.fmt.Formatter.write_str f (toStr "AuthenticatorMacKeyPresent")
  | authenticator.Error.AuthenticatorMacKeyMissing =>
    core.fmt.Formatter.write_str f (toStr "AuthenticatorMacKeyMissing")
```

The function matches on the `authenticator.Error` variant and delegates to
`core.fmt.Formatter.write_str` with the variant's name. The function is total: it never panics
and always succeeds (assuming the underlying formatter operations succeed).

**Source**: spqr/src/authenticator.rs (lines 10:9-10:14, `#[derive(Debug, thiserror::Error)]`)
-/

open Aeneas Aeneas.Std Result

namespace spqr.authenticator.Error

/-- **`fmt` unfolds to `write_str` on the `InvalidCtMac` variant**.

When `self = authenticator.Error.InvalidCtMac`, the function simply writes the string
`"InvalidCtMac"` to the formatter via `core.fmt.Formatter.write_str`. -/
@[simp]
theorem fmt_InvalidCtMac (f : core.fmt.Formatter) :
    Insts.CoreFmtDebug.fmt authenticator.Error.InvalidCtMac f =
      core.fmt.Formatter.write_str f (toStr "InvalidCtMac") := by
  simp [Insts.CoreFmtDebug.fmt]

/-- **`fmt` unfolds to `write_str` on the `InvalidHdrMac` variant**.

When `self = authenticator.Error.InvalidHdrMac`, the function simply writes the string
`"InvalidHdrMac"` to the formatter via `core.fmt.Formatter.write_str`. -/
@[simp]
theorem fmt_InvalidHdrMac (f : core.fmt.Formatter) :
    Insts.CoreFmtDebug.fmt authenticator.Error.InvalidHdrMac f =
      core.fmt.Formatter.write_str f (toStr "InvalidHdrMac") := by
  simp [Insts.CoreFmtDebug.fmt]

/-- **`fmt` unfolds to `write_str` on the `AuthenticatorRootKeyPresent` variant**.

When `self = authenticator.Error.AuthenticatorRootKeyPresent`, the function simply writes the
string `"AuthenticatorRootKeyPresent"` to the formatter via
`core.fmt.Formatter.write_str`. -/
@[simp]
theorem fmt_AuthenticatorRootKeyPresent (f : core.fmt.Formatter) :
    Insts.CoreFmtDebug.fmt authenticator.Error.AuthenticatorRootKeyPresent f =
      core.fmt.Formatter.write_str f (toStr "AuthenticatorRootKeyPresent") := by
  simp [Insts.CoreFmtDebug.fmt]

/-- **`fmt` unfolds to `write_str` on the `AuthenticatorRootKeyMissing` variant**.

When `self = authenticator.Error.AuthenticatorRootKeyMissing`, the function simply writes the
string `"AuthenticatorRootKeyMissing"` to the formatter via
`core.fmt.Formatter.write_str`. -/
@[simp]
theorem fmt_AuthenticatorRootKeyMissing (f : core.fmt.Formatter) :
    Insts.CoreFmtDebug.fmt authenticator.Error.AuthenticatorRootKeyMissing f =
      core.fmt.Formatter.write_str f (toStr "AuthenticatorRootKeyMissing") := by
  simp [Insts.CoreFmtDebug.fmt]

/-- **`fmt` unfolds to `write_str` on the `AuthenticatorMacKeyPresent` variant**.

When `self = authenticator.Error.AuthenticatorMacKeyPresent`, the function simply writes the
string `"AuthenticatorMacKeyPresent"` to the formatter via
`core.fmt.Formatter.write_str`. -/
@[simp]
theorem fmt_AuthenticatorMacKeyPresent (f : core.fmt.Formatter) :
    Insts.CoreFmtDebug.fmt authenticator.Error.AuthenticatorMacKeyPresent f =
      core.fmt.Formatter.write_str f (toStr "AuthenticatorMacKeyPresent") := by
  simp [Insts.CoreFmtDebug.fmt]

/-- **`fmt` unfolds to `write_str` on the `AuthenticatorMacKeyMissing` variant**.

When `self = authenticator.Error.AuthenticatorMacKeyMissing`, the function simply writes the
string `"AuthenticatorMacKeyMissing"` to the formatter via
`core.fmt.Formatter.write_str`. -/
@[simp]
theorem fmt_AuthenticatorMacKeyMissing (f : core.fmt.Formatter) :
    Insts.CoreFmtDebug.fmt authenticator.Error.AuthenticatorMacKeyMissing f =
      core.fmt.Formatter.write_str f (toStr "AuthenticatorMacKeyMissing") := by
  simp [Insts.CoreFmtDebug.fmt]

/--
**Spec theorem for `authenticator.Error.Insts.CoreFmtDebug.fmt`**:

Structurally faithful debug formatter for `authenticator.Error`: the function is the canonical
case-analysis over the six unit constructors of `authenticator.Error`, dispatching each branch to
`core.fmt.Formatter.write_str` with the constructor's name.

The result satisfies the constructor-level specification (one branch per variant):
  * `InvalidCtMac` is sent to `core.fmt.Formatter.write_str f "InvalidCtMac"`.
  * `InvalidHdrMac` is sent to `core.fmt.Formatter.write_str f "InvalidHdrMac"`.
  * `AuthenticatorRootKeyPresent` is sent to
      `core.fmt.Formatter.write_str f "AuthenticatorRootKeyPresent"`.
  * `AuthenticatorRootKeyMissing` is sent to
      `core.fmt.Formatter.write_str f "AuthenticatorRootKeyMissing"`.
  * `AuthenticatorMacKeyPresent` is sent to
      `core.fmt.Formatter.write_str f "AuthenticatorMacKeyPresent"`.
  * `AuthenticatorMacKeyMissing` is sent to
      `core.fmt.Formatter.write_str f "AuthenticatorMacKeyMissing"`.

Concretely, the spec is the definitional equality:

  `fmt self f = match self with
                | InvalidCtMac                 => write_str f "InvalidCtMac"
                | InvalidHdrMac                => write_str f "InvalidHdrMac"
                | AuthenticatorRootKeyPresent  => write_str f "AuthenticatorRootKeyPresent"
                | AuthenticatorRootKeyMissing  => write_str f "AuthenticatorRootKeyMissing"
                | AuthenticatorMacKeyPresent   => write_str f "AuthenticatorMacKeyPresent"
                | AuthenticatorMacKeyMissing   => write_str f "AuthenticatorMacKeyMissing"`

This establishes that `fmt` realises — at the level of
`Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)` — the canonical
*structural* debug projection

  `δ : authenticator.Error → FormatterAction`

induced by the derived `#[derive(Debug)]` instance on the sum `authenticator.Error`: each
unit constructor is mapped to the formatter action that writes its name as a string.

**Source**: spqr/src/authenticator.rs (lines 10:9-10:14, `#[derive(Debug, thiserror::Error)]`)
-/
theorem fmt_spec
    (self : authenticator.Error) (f : core.fmt.Formatter) :
    authenticator.Error.Insts.CoreFmtDebug.fmt self f =
      (match self with
       | authenticator.Error.InvalidCtMac =>
         core.fmt.Formatter.write_str f (toStr "InvalidCtMac")
       | authenticator.Error.InvalidHdrMac =>
         core.fmt.Formatter.write_str f (toStr "InvalidHdrMac")
       | authenticator.Error.AuthenticatorRootKeyPresent =>
         core.fmt.Formatter.write_str f (toStr "AuthenticatorRootKeyPresent")
       | authenticator.Error.AuthenticatorRootKeyMissing =>
         core.fmt.Formatter.write_str f (toStr "AuthenticatorRootKeyMissing")
       | authenticator.Error.AuthenticatorMacKeyPresent =>
         core.fmt.Formatter.write_str f (toStr "AuthenticatorMacKeyPresent")
       | authenticator.Error.AuthenticatorMacKeyMissing =>
         core.fmt.Formatter.write_str f (toStr "AuthenticatorMacKeyMissing")) := by
  unfold authenticator.Error.Insts.CoreFmtDebug.fmt
  cases self <;> rfl

/--
**Totality theorem for `authenticator.Error.Insts.CoreFmtDebug.fmt`**:

• The function always succeeds (no panic / no error) for any `authenticator.Error` input and any
  formatter state. Every variant is a unit variant, so each branch delegates to
  `core.fmt.Formatter.write_str` with the variant's name as a string.
• The postcondition states that the result is `(Result.Ok (), f)`, i.e. the call always
  succeeds and returns the formatter unchanged. This follows from the Aeneas extraction model
  where `write_str` always returns `.ok (.Ok (), fmt)`.

**Source**: spqr/src/authenticator.rs (lines 10:9-10:14, `#[derive(Debug, thiserror::Error)]`)
-/
@[step]
theorem fmt_total (self : spqr.authenticator.Error) (f : core.fmt.Formatter) :
    spqr.authenticator.Error.Insts.CoreFmtDebug.fmt self f
      ⦃ (r : (core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) =>
        r = (core.result.Result.Ok (), f) ⦄ := by
  unfold Insts.CoreFmtDebug.fmt
  rcases self with _ | _ | _ | _ | _ | _ <;>
    simp_all [core.fmt.Formatter.write_str, WP.spec_ok]

end spqr.authenticator.Error

/-!
# Spec theorem for `spqr::authenticator::{impl core::fmt::Display for spqr::authenticator::Error}::fmt`

The `thiserror::Error` derive macro auto-generates the `fmt::Display` implementation from the
`#[error("…")]` attributes on each variant of `authenticator.Error`:
```rust
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Ciphertext MAC is invalid")]
    InvalidCtMac,
    #[error("Encapsulation key MAC is invalid")]
    InvalidHdrMac,
    #[error("Authenticator previous root key present when should be erased")]
    AuthenticatorRootKeyPresent,
    #[error("Authenticator previous root key missing")]
    AuthenticatorRootKeyMissing,
    #[error("Authenticator previous MAC key present when should be erased")]
    AuthenticatorMacKeyPresent,
    #[error("Authenticator previous MAC key missing")]
    AuthenticatorMacKeyMissing,
}
```
Unlike the `Debug` implementation (which writes the variant *name*), the `Display` implementation
writes the human-readable error *message* from the `#[error("…")]` attribute via
`core.fmt.Formatter.write_str`. Since every variant is a unit variant (no payload), no
interpolation or `debug_tuple_field1_finish` calls are needed.

After extraction the Lean definition is:
```
def authenticator.Error.Insts.CoreFmtDisplay.fmt
  (self : authenticator.Error) (__formatter : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  := do
  match self with
  | authenticator.Error.InvalidCtMac =>
    core.fmt.Formatter.write_str __formatter (toStr
      "Ciphertext MAC is invalid")
  | authenticator.Error.InvalidHdrMac =>
    core.fmt.Formatter.write_str __formatter (toStr
      "Encapsulation key MAC is invalid")
  | authenticator.Error.AuthenticatorRootKeyPresent =>
    core.fmt.Formatter.write_str __formatter (toStr
      "Authenticator previous root key present when should be erased")
  | authenticator.Error.AuthenticatorRootKeyMissing =>
    core.fmt.Formatter.write_str __formatter (toStr
      "Authenticator previous root key missing")
  | authenticator.Error.AuthenticatorMacKeyPresent =>
    core.fmt.Formatter.write_str __formatter (toStr
      "Authenticator previous MAC key present when should be erased")
  | authenticator.Error.AuthenticatorMacKeyMissing =>
    core.fmt.Formatter.write_str __formatter (toStr
      "Authenticator previous MAC key missing")
```

The function matches on the `authenticator.Error` variant and delegates to
`core.fmt.Formatter.write_str` with the human-readable error message from the `#[error("…")]`
attribute. The function is total: it never panics and always succeeds (assuming the underlying
formatter operations succeed).

**Source**: spqr/src/authenticator.rs (lines 10:16-10:32, `#[derive(thiserror::Error)]`)
-/

namespace spqr.authenticator.Error

/-- **`display_fmt` unfolds to `write_str` on the `InvalidCtMac` variant**.

When `self = authenticator.Error.InvalidCtMac`, the function writes the error message
`"Ciphertext MAC is invalid"` to the formatter via `core.fmt.Formatter.write_str`. -/
@[simp]
theorem display_fmt_InvalidCtMac (f : core.fmt.Formatter) :
    Insts.CoreFmtDisplay.fmt authenticator.Error.InvalidCtMac f =
      core.fmt.Formatter.write_str f (toStr "Ciphertext MAC is invalid") := by
  simp [Insts.CoreFmtDisplay.fmt]

/-- **`display_fmt` unfolds to `write_str` on the `InvalidHdrMac` variant**.

When `self = authenticator.Error.InvalidHdrMac`, the function writes the error message
`"Encapsulation key MAC is invalid"` to the formatter via `core.fmt.Formatter.write_str`. -/
@[simp]
theorem display_fmt_InvalidHdrMac (f : core.fmt.Formatter) :
    Insts.CoreFmtDisplay.fmt authenticator.Error.InvalidHdrMac f =
      core.fmt.Formatter.write_str f (toStr "Encapsulation key MAC is invalid") := by
  simp [Insts.CoreFmtDisplay.fmt]

/-- **`display_fmt` unfolds to `write_str` on the `AuthenticatorRootKeyPresent` variant**.

When `self = authenticator.Error.AuthenticatorRootKeyPresent`, the function writes the error
message `"Authenticator previous root key present when should be erased"` to the formatter via
`core.fmt.Formatter.write_str`. -/
@[simp]
theorem display_fmt_AuthenticatorRootKeyPresent (f : core.fmt.Formatter) :
    Insts.CoreFmtDisplay.fmt authenticator.Error.AuthenticatorRootKeyPresent f =
      core.fmt.Formatter.write_str f
        (toStr "Authenticator previous root key present when should be erased") := by
  simp [Insts.CoreFmtDisplay.fmt]

/-- **`display_fmt` unfolds to `write_str` on the `AuthenticatorRootKeyMissing` variant**.

When `self = authenticator.Error.AuthenticatorRootKeyMissing`, the function writes the error
message `"Authenticator previous root key missing"` to the formatter via
`core.fmt.Formatter.write_str`. -/
@[simp]
theorem display_fmt_AuthenticatorRootKeyMissing (f : core.fmt.Formatter) :
    Insts.CoreFmtDisplay.fmt authenticator.Error.AuthenticatorRootKeyMissing f =
      core.fmt.Formatter.write_str f
        (toStr "Authenticator previous root key missing") := by
  simp [Insts.CoreFmtDisplay.fmt]

/-- **`display_fmt` unfolds to `write_str` on the `AuthenticatorMacKeyPresent` variant**.

When `self = authenticator.Error.AuthenticatorMacKeyPresent`, the function writes the error
message `"Authenticator previous MAC key present when should be erased"` to the formatter via
`core.fmt.Formatter.write_str`. -/
@[simp]
theorem display_fmt_AuthenticatorMacKeyPresent (f : core.fmt.Formatter) :
    Insts.CoreFmtDisplay.fmt authenticator.Error.AuthenticatorMacKeyPresent f =
      core.fmt.Formatter.write_str f
        (toStr "Authenticator previous MAC key present when should be erased") := by
  simp [Insts.CoreFmtDisplay.fmt]

/-- **`display_fmt` unfolds to `write_str` on the `AuthenticatorMacKeyMissing` variant**.

When `self = authenticator.Error.AuthenticatorMacKeyMissing`, the function writes the error
message `"Authenticator previous MAC key missing"` to the formatter via
`core.fmt.Formatter.write_str`. -/
@[simp]
theorem display_fmt_AuthenticatorMacKeyMissing (f : core.fmt.Formatter) :
    Insts.CoreFmtDisplay.fmt authenticator.Error.AuthenticatorMacKeyMissing f =
      core.fmt.Formatter.write_str f
        (toStr "Authenticator previous MAC key missing") := by
  simp [Insts.CoreFmtDisplay.fmt]

/--
**Spec theorem for `authenticator.Error.Insts.CoreFmtDisplay.fmt`**:

Structurally faithful display formatter for `authenticator.Error`: the function is the canonical
case-analysis over the six unit constructors of `authenticator.Error`, dispatching each branch to
`core.fmt.Formatter.write_str` with the human-readable error message from the `#[error("…")]`
attribute.

The result satisfies the constructor-level specification (one branch per variant):
  * `InvalidCtMac` is sent to
      `core.fmt.Formatter.write_str f "Ciphertext MAC is invalid"`.
  * `InvalidHdrMac` is sent to
      `core.fmt.Formatter.write_str f "Encapsulation key MAC is invalid"`.
  * `AuthenticatorRootKeyPresent` is sent to
      `core.fmt.Formatter.write_str f "Authenticator previous root key present when should be erased"`.
  * `AuthenticatorRootKeyMissing` is sent to
      `core.fmt.Formatter.write_str f "Authenticator previous root key missing"`.
  * `AuthenticatorMacKeyPresent` is sent to
      `core.fmt.Formatter.write_str f "Authenticator previous MAC key present when should be erased"`.
  * `AuthenticatorMacKeyMissing` is sent to
      `core.fmt.Formatter.write_str f "Authenticator previous MAC key missing"`.

Concretely, the spec is the definitional equality:

  `fmt self f = match self with
                | InvalidCtMac                 => write_str f "Ciphertext MAC is invalid"
                | InvalidHdrMac                => write_str f "Encapsulation key MAC is invalid"
                | AuthenticatorRootKeyPresent  => write_str f "Authenticator previous root key present when should be erased"
                | AuthenticatorRootKeyMissing  => write_str f "Authenticator previous root key missing"
                | AuthenticatorMacKeyPresent   => write_str f "Authenticator previous MAC key present when should be erased"
                | AuthenticatorMacKeyMissing   => write_str f "Authenticator previous MAC key missing"`

This establishes that `fmt` realises — at the level of
`Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)` — the canonical
*structural* display projection

  `δ : authenticator.Error → FormatterAction`

induced by the derived `thiserror::Error` instance on the sum `authenticator.Error`: each
unit constructor is mapped to the formatter action that writes its error message as a string.

**Source**: spqr/src/authenticator.rs (lines 10:16-10:32, `#[derive(thiserror::Error)]`)
-/
theorem display_fmt_spec
    (self : authenticator.Error) (f : core.fmt.Formatter) :
    authenticator.Error.Insts.CoreFmtDisplay.fmt self f =
      (match self with
       | authenticator.Error.InvalidCtMac =>
         core.fmt.Formatter.write_str f
           (toStr "Ciphertext MAC is invalid")
       | authenticator.Error.InvalidHdrMac =>
         core.fmt.Formatter.write_str f
           (toStr "Encapsulation key MAC is invalid")
       | authenticator.Error.AuthenticatorRootKeyPresent =>
         core.fmt.Formatter.write_str f
           (toStr "Authenticator previous root key present when should be erased")
       | authenticator.Error.AuthenticatorRootKeyMissing =>
         core.fmt.Formatter.write_str f
           (toStr "Authenticator previous root key missing")
       | authenticator.Error.AuthenticatorMacKeyPresent =>
         core.fmt.Formatter.write_str f
           (toStr "Authenticator previous MAC key present when should be erased")
       | authenticator.Error.AuthenticatorMacKeyMissing =>
         core.fmt.Formatter.write_str f
           (toStr "Authenticator previous MAC key missing")) := by
  unfold authenticator.Error.Insts.CoreFmtDisplay.fmt
  cases self <;> rfl

/--
**Totality theorem for `authenticator.Error.Insts.CoreFmtDisplay.fmt`**:

• The function always succeeds (no panic / no error) for any `authenticator.Error` input and any
  formatter state. Every variant is a unit variant, so each branch delegates to
  `core.fmt.Formatter.write_str` with the variant's error message string.
• The postcondition states that the result is `(Result.Ok (), f)`, i.e. the call always
  succeeds and returns the formatter unchanged. This follows from the Aeneas extraction model
  where `write_str` always returns `.ok (.Ok (), fmt)`.

**Source**: spqr/src/authenticator.rs (lines 10:16-10:32, `#[derive(thiserror::Error)]`)
-/
@[step]
theorem display_fmt_total (self : spqr.authenticator.Error) (f : core.fmt.Formatter) :
    spqr.authenticator.Error.Insts.CoreFmtDisplay.fmt self f
      ⦃ (r : (core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) =>
        r = (core.result.Result.Ok (), f) ⦄ := by
  unfold Insts.CoreFmtDisplay.fmt
  rcases self with _ | _ | _ | _ | _ | _ <;>
    simp_all [core.fmt.Formatter.write_str, WP.spec_ok]

end spqr.authenticator.Error
