/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::SecretOutput::eq`

The `SecretOutput` enum has three variants:
```rust
#[derive(PartialEq, Debug)]
pub enum SecretOutput {
    None,
    Send(Secret),
    Recv(Secret),
}
```
where `Secret = Vec<u8>`. The `#[derive(PartialEq)]` attribute auto-generates structural equality:
two `SecretOutput` values are equal iff they are the same variant and, for `Send`/`Recv`, the inner
`Vec<u8>` payloads are pointwise equal.

After extraction the Lean definition is:
```
def SecretOutput.Insts.CoreCmpPartialEqSecretOutput.eq
  (self : SecretOutput) (other : SecretOutput) : Result Bool := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  if self1 = other1
  then
    match self with
    | SecretOutput.None => ok true
    | SecretOutput.Send __self_0 =>
      match other with
      | SecretOutput.None => ok true
      | SecretOutput.Send __arg1_0 =>
        alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 __self_0 __arg1_0
      | SecretOutput.Recv _ => ok true
    | SecretOutput.Recv __self_0 =>
      match other with
      | SecretOutput.None => ok true
      | SecretOutput.Send _ => ok true
      | SecretOutput.Recv __arg1_0 =>
        alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 __self_0 __arg1_0
  else ok false
```

The function first compares discriminants; when they differ the result is `false`. When they agree
the nested matches dispatch to:
  • `None` vs `None` → `true`
  • `Send(a)` vs `Send(b)` → `PartialEqVec.eq` on the payloads
  • `Recv(a)` vs `Recv(b)` → `PartialEqVec.eq` on the payloads
(The other inner branches are dead code since the discriminants already match.)

The function is total: it never panics and always succeeds.

**Source**: spqr/src/lib.rs (line 73, `#[derive(PartialEq, Debug)]`)
-/

open Aeneas Aeneas.Std Result

namespace spqr.SecretOutput

/--
**Spec theorem for `SecretOutput.Insts.CoreCmpPartialEqSecretOutput.eq`**:

• The function always succeeds (no panic / no error) for any pair of `SecretOutput` inputs. When
  the discriminants differ it short-circuits to `ok false`; when they agree it either returns
  `ok true` (for `None`–`None`) or delegates to `alloc.vec.partial_eq.PartialEqVec.eq` on the
  inner `Vec U8` payloads (for `Send`–`Send` and `Recv`–`Recv`), which is itself total.
• The result is `true` if and only if the two values are propositionally equal:
    `eq(self, other) = ok (self = other)`.
  This follows from the fact that the discriminant comparison exactly distinguishes the three
  variants, and `PartialEqVec.eq core.cmp.PartialEqU8` decides list equality for `Vec U8`.
• The relation is reflexive, symmetric, and transitive — i.e. it is a total equivalence relation,
  consistent with the `PartialEq` (and structurally derived `Eq`) trait in Rust.

**Source**: spqr/src/lib.rs (line 73, `#[derive(PartialEq, Debug)]`)
-/
@[step]
theorem eq_spec (self other : spqr.SecretOutput) :
    spqr.SecretOutput.Insts.CoreCmpPartialEqSecretOutput.eq self other
      ⦃ (result : Bool) =>
        result = true ↔ self = other ⦄ := by
  sorry

/--
Two `SecretOutput` elements are equal (as inductive values) if and only if they are the same
variant and, for `Send`/`Recv`, the inner `Vec U8` payloads have the same backing list. This
connects propositional equality of `SecretOutput` to the observable data it carries.
-/
theorem secretOutput_eq_iff (a b : spqr.SecretOutput) :
    a = b ↔
      match a, b with
      | .None, .None => True
      | .Send va, .Send vb => va.val = vb.val
      | .Recv va, .Recv vb => va.val = vb.val
      | _, _ => False := by
  constructor
  · intro h; subst h; cases a <;> simp
  · intro h
    cases a <;> cases b <;> simp_all
    all_goals (rename_i h; exact Subtype.ext h)

end spqr.SecretOutput
