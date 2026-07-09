/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::SecretOutput::has_secret`

`SecretOutput::has_secret` is a boolean predicate that returns `true` if and only if the
`SecretOutput` value contains a secret — i.e., for the `Send(_)` or `Recv(_)` variants.
For the `None` variant, it returns `false`.

The Rust implementation uses `!matches!(self, Self::None)`, which Aeneas extracts as a
match producing a boolean flag that is then negated.

**Source**: spqr/src/lib.rs (lines 173:4-175:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.SecretOutput.has_secret`**:

• Takes a `SecretOutput` value `self`.
• Returns `true` if `self` is `Send(_)` or `Recv(_)`.
• Returns `false` if `self` is `None`.
• The function always succeeds (no panic) for any `SecretOutput` input.

The result satisfies the boolean predicate postcondition:

  `result = true ↔ self ≠ SecretOutput.None`

Equivalently:

  `(self = .None → result = false) ∧`
  `(self = .Send _ ∨ self = .Recv _ → result = true)`

**Source**: spqr/src/lib.rs (lines 173:4-175:5)
-/
@[step]
theorem SecretOutput.has_secret_spec (self : SecretOutput) :
    SecretOutput.has_secret self ⦃ (result : Bool) =>
      (self = .None → result = false) ∧
      (∀ s, self = .Send s → result = true) ∧
      (∀ s, self = .Recv s → result = true) ⦄ := by
  unfold SecretOutput.has_secret
  sorry

end spqr
