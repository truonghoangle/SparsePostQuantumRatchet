/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::SecretOutput::send_secret`

The `SecretOutput` enum has three variants:
```rust
pub enum SecretOutput {
    None,
    Send(Secret),
    Recv(Secret),
}
```
where `Secret = Vec<u8>`. The method `send_secret` extracts the inner secret when the variant is
`Send`, returning `None` otherwise:
```rust
pub fn send_secret(&self) -> Option<&Secret> {
    match self {
        SecretOutput::Send(s) => Some(s),
        SecretOutput::Recv(_) => None,
        SecretOutput::None => None,
    }
}
```
After extraction the Lean definition is:
```
def SecretOutput.send_secret
  (self : SecretOutput) : Result (Option (alloc.vec.Vec Std.U8)) := do
  match self with
  | SecretOutput.None => ok none
  | SecretOutput.Send s => ok (some s)
  | SecretOutput.Recv _ => ok none
```

The function is total: it never panics and always succeeds. It acts as a projection from the
`Send` variant — returning `some s` when the input is `SecretOutput.Send s`, and `none` for both
`SecretOutput.None` and `SecretOutput.Recv _`.

**Source**: spqr/src/lib.rs (lines 152:4-158:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.SecretOutput

/-- **`send_secret` on `None` returns `none`**.

`SecretOutput.send_secret SecretOutput.None` always succeeds and returns `none`. -/
@[simp]
theorem send_secret_none :
    SecretOutput.send_secret SecretOutput.None = ok none := by
  simp [SecretOutput.send_secret]

/-- **`send_secret` on `Send s` returns `some s`**.

`SecretOutput.send_secret (SecretOutput.Send s)` always succeeds and returns the inner
payload `some s`. -/
@[simp]
theorem send_secret_send (s : alloc.vec.Vec Std.U8) :
    SecretOutput.send_secret (SecretOutput.Send s) = ok (some s) := by
  simp [SecretOutput.send_secret]

/-- **`send_secret` on `Recv r` returns `none`**.

`SecretOutput.send_secret (SecretOutput.Recv r)` always succeeds and returns `none`. -/
@[simp]
theorem send_secret_recv (r : alloc.vec.Vec Std.U8) :
    SecretOutput.send_secret (SecretOutput.Recv r) = ok none := by
  simp [SecretOutput.send_secret]

/--
**Spec theorem for `SecretOutput.send_secret`**:

• The function always succeeds (no panic / no error) for any `SecretOutput` input. It performs a
  simple pattern match: `Send s` maps to `some s`, while `None` and `Recv _` both map to `none`.
• The postcondition characterises the result as the projection of the `Send` variant:
    `result = match self with | .Send s => some s | _ => none`
  This establishes that `send_secret` faithfully extracts the secret payload from the `Send`
  variant and returns `none` for all other variants.
• The function is the left inverse of the `Send` constructor on the `Option` level:
  `send_secret (Send s) = ok (some s)` and `send_secret` is `none` otherwise.

**Source**: spqr/src/lib.rs (lines 152:4-158:5)
-/
@[step]
theorem send_secret_spec (self : spqr.SecretOutput) :
    spqr.SecretOutput.send_secret self
      ⦃ (result : Option (alloc.vec.Vec Std.U8)) =>
        result = match self with
          | .Send s => some s
          | _ => none ⦄ := by
  rcases self with _ | ⟨s⟩ | ⟨r⟩ <;>
    simp [SecretOutput.send_secret, WP.spec_ok]

end spqr.SecretOutput
