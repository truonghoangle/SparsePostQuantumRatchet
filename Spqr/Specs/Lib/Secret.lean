/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::SecretOutput::secret`

The `SecretOutput` enum has three variants:
```rust
pub enum SecretOutput {
    None,
    Send(Secret),
    Recv(Secret),
}
```
where `Secret = Vec<u8>`. The method `secret` extracts the inner secret when the variant is either
`Send` or `Recv`, returning `None` only for the `None` variant:
```rust
pub fn secret(&self) -> Option<&Secret> {
    match self {
        SecretOutput::Send(s) | SecretOutput::Recv(s) => Some(s),
        _ => None,
    }
}
```
After extraction the Lean definition is:
```
def SecretOutput.secret
  (self : SecretOutput) : Result (Option (alloc.vec.Vec Std.U8)) := do
  match self with
  | SecretOutput.None => ok none
  | SecretOutput.Send s => ok (some s)
  | SecretOutput.Recv s => ok (some s)
```

The function is total: it never panics and always succeeds. It acts as a combined projection from
the `Send` and `Recv` variants — returning `some s` when the input carries a secret payload
(`SecretOutput.Send s` or `SecretOutput.Recv s`), and `none` only for `SecretOutput.None`.

**Source**: spqr/src/lib.rs (lines 167:4-172:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.SecretOutput

/-- **`secret` on `None` returns `none`**.

`SecretOutput.secret SecretOutput.None` always succeeds and returns `none`. -/
@[simp]
theorem secret_none :
    SecretOutput.secret SecretOutput.None = ok none := by
  simp [SecretOutput.secret]

/-- **`secret` on `Send s` returns `some s`**.

`SecretOutput.secret (SecretOutput.Send s)` always succeeds and returns the inner
payload `some s`. -/
@[simp]
theorem secret_send (s : alloc.vec.Vec Std.U8) :
    SecretOutput.secret (SecretOutput.Send s) = ok (some s) := by
  simp [SecretOutput.secret]

/-- **`secret` on `Recv r` returns `some r`**.

`SecretOutput.secret (SecretOutput.Recv r)` always succeeds and returns the inner
payload `some r`. -/
@[simp]
theorem secret_recv (r : alloc.vec.Vec Std.U8) :
    SecretOutput.secret (SecretOutput.Recv r) = ok (some r) := by
  simp [SecretOutput.secret]

/--
**Spec theorem for `SecretOutput.secret`**:

• The function always succeeds (no panic / no error) for any `SecretOutput` input. It performs a
  simple pattern match: `Send s` and `Recv s` both map to `some s`, while `None` maps to `none`.
• The postcondition characterises the result as the projection of the secret payload:
    `result = match self with | .Send s => some s | .Recv s => some s | _ => none`
  This establishes that `secret` faithfully extracts the secret payload from any variant that
  carries one, and returns `none` only for the empty variant.
• The function subsumes both `send_secret` and `recv_secret`: it is the union of their projections,
  returning `some s` whenever either would.

**Source**: spqr/src/lib.rs (lines 167:4-172:5)
-/
@[step]
theorem secret_spec (self : spqr.SecretOutput) :
    spqr.SecretOutput.secret self
      ⦃ (result : Option (alloc.vec.Vec Std.U8)) =>
        result = match self with
          | .Send s => some s
          | .Recv s => some s
          | _ => none ⦄ := by
  rcases self with _ | ⟨s⟩ | ⟨r⟩ <;>
    simp [SecretOutput.secret, WP.spec_ok]

end spqr.SecretOutput
