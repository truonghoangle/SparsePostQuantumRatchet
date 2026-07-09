/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::SecretOutput::recv_secret`

`SecretOutput::recv_secret` is a projection accessor on the `SecretOutput` enum.  It returns
`Some(&secret)` when the output is `Recv(secret)`, indicating that a shared secret was derived
that will be used to decrypt the next message received, and thus should be mixed into the
receiving chain.  For `Send(_)` and `None` variants, it returns `None`.

The function is a pure pattern match with no error paths — it always succeeds for any valid
`SecretOutput` value.

**Source**: spqr/src/lib.rs (lines 159:4-165:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.SecretOutput.recv_secret`**:

• Takes a `SecretOutput` value `self`.
• Pattern-matches on `self`:
  - `Send(_)` → returns `none`
  - `Recv(s)` → returns `some s`
  - `None`    → returns `none`
• The function always succeeds (no panic) for any `SecretOutput` input.

The result satisfies the projection postcondition:

  `(self = .Recv s → result = some s) ∧`
  `(self = .Send _ ∨ self = .None → result = none)`

**Source**: spqr/src/lib.rs (lines 159:4-165:5)
-/
@[step]
theorem SecretOutput.recv_secret_spec (self : SecretOutput) :
    SecretOutput.recv_secret self ⦃ (result : Option (alloc.vec.Vec U8)) =>
      (∀ s, self = .Recv s → result = some s) ∧
      (self = .None → result = none) ∧
      (∀ s, self = .Send s → result = none) ⦄ := by
  unfold SecretOutput.recv_secret
  sorry

end spqr
