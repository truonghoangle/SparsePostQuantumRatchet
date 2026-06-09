/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::SecretOutput::has_secret`

The `SecretOutput` enum has three variants:
```rust
pub enum SecretOutput {
    None,
    Send(Secret),
    Recv(Secret),
}
```
where `Secret = Vec<u8>`. The method `has_secret` returns `true` when the variant carries a secret
payload (`Send` or `Recv`), and `false` only for the `None` variant:
```rust
pub fn has_secret(&self) -> bool {
    !matches!(self, Self::None)
}
```
After extraction the Lean definition is:
```
def SecretOutput.has_secret (self : SecretOutput) : Result Bool := do
  let b ←
    match self with
    | SecretOutput.None => ok true
    | SecretOutput.Send _ => ok false
    | SecretOutput.Recv _ => ok false
  ok (¬ b)
```

The function is total: it never panics and always succeeds. It is a Boolean discriminator on
`SecretOutput` — returning `true` whenever the variant is `Send` or `Recv` (i.e. the output carries
a secret), and `false` only for `SecretOutput.None`.

**Source**: spqr/src/lib.rs (lines 173:4-175:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.SecretOutput

/-- **`has_secret` on `None` returns `false`**.

`SecretOutput.has_secret SecretOutput.None` always succeeds and returns `false`. -/
@[simp]
theorem has_secret_none :
    SecretOutput.has_secret SecretOutput.None = ok false := by
  simp [SecretOutput.has_secret]

/-- **`has_secret` on `Send s` returns `true`**.

`SecretOutput.has_secret (SecretOutput.Send s)` always succeeds and returns `true`. -/
@[simp]
theorem has_secret_send (s : alloc.vec.Vec Std.U8) :
    SecretOutput.has_secret (SecretOutput.Send s) = ok true := by
  simp [SecretOutput.has_secret]

/-- **`has_secret` on `Recv r` returns `true`**.

`SecretOutput.has_secret (SecretOutput.Recv r)` always succeeds and returns `true`. -/
@[simp]
theorem has_secret_recv (r : alloc.vec.Vec Std.U8) :
    SecretOutput.has_secret (SecretOutput.Recv r) = ok true := by
  simp [SecretOutput.has_secret]

/--
**Spec theorem for `SecretOutput.has_secret`**:

• The function always succeeds (no panic / no error) for any `SecretOutput` input. It checks
  whether the variant is anything other than `None`: `Send _` and `Recv _` both map to `true`,
  while `None` maps to `false`.
• The postcondition characterises the result as the negation of the `None` check:
    `result = match self with | .None => false | _ => true`
  This establishes that `has_secret` faithfully reports whether a `SecretOutput` carries a secret
  payload.
• The function is the Boolean counterpart of `secret`: `has_secret self = true` if and only if
  `secret self` returns `some _`.

**Source**: spqr/src/lib.rs (lines 173:4-175:5)
-/
@[step]
theorem has_secret_spec (self : spqr.SecretOutput) :
    spqr.SecretOutput.has_secret self
      ⦃ (result : Bool) =>
        result = match self with
          | .None => false
          | _ => true ⦄ := by
  rcases self with _ | ⟨s⟩ | ⟨r⟩ <;>
    simp [SecretOutput.has_secret, WP.spec_ok]

end spqr.SecretOutput
