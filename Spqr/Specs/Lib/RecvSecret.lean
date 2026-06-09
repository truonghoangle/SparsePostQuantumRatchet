/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::SecretOutput::recv_secret`

The `SecretOutput` enum has three variants:
```rust
pub enum SecretOutput {
    None,
    Send(Secret),
    Recv(Secret),
}
```
where `Secret = Vec<u8>`. The method `recv_secret` extracts the inner secret when the variant is
`Recv`, returning `None` otherwise:
```rust
pub fn recv_secret(&self) -> Option<&Secret> {
    match self {
        SecretOutput::Send(_) => None,
        SecretOutput::Recv(s) => Some(s),
        SecretOutput::None => None,
    }
}
```
After extraction the Lean definition is:
```
def SecretOutput.recv_secret
  (self : SecretOutput) : Result (Option (alloc.vec.Vec Std.U8)) := do
  match self with
  | SecretOutput.None => ok none
  | SecretOutput.Send _ => ok none
  | SecretOutput.Recv s => ok (some s)
```

The function is total: it never panics and always succeeds. It acts as a projection from the
`Recv` variant — returning `some s` when the input is `SecretOutput.Recv s`, and `none` for both
`SecretOutput.None` and `SecretOutput.Send _`.

**Source**: spqr/src/lib.rs (lines 159:4-165:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.SecretOutput

/-- **`recv_secret` on `None` returns `none`**.

`SecretOutput.recv_secret SecretOutput.None` always succeeds and returns `none`. -/
@[simp]
theorem recv_secret_none :
    SecretOutput.recv_secret SecretOutput.None = ok none := by
  simp [SecretOutput.recv_secret]

/-- **`recv_secret` on `Send s` returns `none`**.

`SecretOutput.recv_secret (SecretOutput.Send s)` always succeeds and returns `none`. -/
@[simp]
theorem recv_secret_send (s : alloc.vec.Vec Std.U8) :
    SecretOutput.recv_secret (SecretOutput.Send s) = ok none := by
  simp [SecretOutput.recv_secret]

/-- **`recv_secret` on `Recv r` returns `some r`**.

`SecretOutput.recv_secret (SecretOutput.Recv r)` always succeeds and returns the inner
payload `some r`. -/
@[simp]
theorem recv_secret_recv (r : alloc.vec.Vec Std.U8) :
    SecretOutput.recv_secret (SecretOutput.Recv r) = ok (some r) := by
  simp [SecretOutput.recv_secret]

/--
**Spec theorem for `SecretOutput.recv_secret`**:

• The function always succeeds (no panic / no error) for any `SecretOutput` input. It performs a
  simple pattern match: `Recv s` maps to `some s`, while `None` and `Send _` both map to `none`.
• The postcondition characterises the result as the projection of the `Recv` variant:
    `result = match self with | .Recv s => some s | _ => none`
  This establishes that `recv_secret` faithfully extracts the secret payload from the `Recv`
  variant and returns `none` for all other variants.
• The function is the left inverse of the `Recv` constructor on the `Option` level:
  `recv_secret (Recv s) = ok (some s)` and `recv_secret` is `none` otherwise.

**Source**: spqr/src/lib.rs (lines 159:4-165:5)
-/
@[step]
theorem recv_secret_spec (self : spqr.SecretOutput) :
    spqr.SecretOutput.recv_secret self
      ⦃ (result : Option (alloc.vec.Vec Std.U8)) =>
        result = match self with
          | .Recv s => some s
          | _ => none ⦄ := by
  rcases self with _ | ⟨s⟩ | ⟨r⟩ <;>
    simp [SecretOutput.recv_secret, WP.spec_ok]

end spqr.SecretOutput
