/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::SecretOutput::secret`

`SecretOutput::secret` extracts the inner secret from any non-`None` variant of `SecretOutput`.
Unlike `send_secret` and `recv_secret`, this accessor does not distinguish between the `Send` and
`Recv` variants — it returns `Some(&secret)` for both.  For the `None` variant, it returns `None`.

This is the direction-agnostic accessor used when the caller needs the shared secret regardless
of whether it was derived from a send or receive operation.

**Source**: spqr/src/lib.rs (lines 167:4-172:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.SecretOutput.secret`**:

• Takes a `SecretOutput` value `self`.
• Pattern-matches on `self`:
  - `Send(s)` → returns `some s`
  - `Recv(s)` → returns `some s`
  - `None`    → returns `none`
• The function always succeeds (no panic) for any `SecretOutput` input.
• This is the union of the `send_secret` and `recv_secret` projections:
    `secret self = send_secret self <|> recv_secret self`

The result satisfies the direction-agnostic projection postcondition:

  `(self = .Send s ∨ self = .Recv s → result = some s) ∧`
  `(self = .None → result = none)`

**Source**: spqr/src/lib.rs (lines 167:4-172:5)
-/
@[step]
theorem SecretOutput.secret_spec (self : SecretOutput) :
    SecretOutput.secret self ⦃ (result : Option (alloc.vec.Vec U8)) =>
      (∀ s, self = .Send s → result = some s) ∧
      (∀ s, self = .Recv s → result = some s) ∧
      (self = .None → result = none) ⦄ := by
  unfold SecretOutput.secret
  sorry

end spqr
