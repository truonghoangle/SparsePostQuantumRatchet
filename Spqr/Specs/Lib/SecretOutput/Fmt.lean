/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::{impl core::fmt::Debug for spqr::SecretOutput}::fmt`

`SecretOutput` is the algebraic sum type

  `SecretOutput ≃ {None}  ⊕  Vec<u8>  ⊕  Vec<u8>`

whose `Debug` instance — derived in Rust via `#[derive(Debug, …)]` — is the *structural*
debug formatter: it dispatches on the constructor and delegates to the standard `core::fmt`
primitives that pretty-print each branch.

The function proceeds in three exhaustive cases, one per constructor of `SecretOutput`:
  1. `None` — emit the verbatim constructor name via
     `core.fmt.Formatter.write_str f "None"`.
  2. `Send v` — wrap the payload `v : Vec<u8>` in a `Dyn` carrying its
     `core.fmt.DebugShared (core.fmt.DebugVec core.fmt.DebugU8)` witness, and forward to
     `core.fmt.Formatter.debug_tuple_field1_finish` with the constructor name `"Send"`.
     This realises Rust's `f.debug_tuple("Send").field(v).finish()`.
  3. `Recv v` — wrap the payload `v : Vec<u8>` in a `Dyn` carrying the same
     `core.fmt.DebugShared (core.fmt.DebugVec core.fmt.DebugU8)` witness, and forward to
     `core.fmt.Formatter.debug_tuple_field1_finish` with the constructor name `"Recv"`.
     This realises Rust's `f.debug_tuple("Recv").field(v).finish()`.

Under the current (simplistic) Aeneas model of `core::fmt`, all three formatter primitives
return `(.Ok (), f)`.  Consequently the `Debug` formatter for `SecretOutput` always succeeds
and preserves the formatter state.

**Source**: spqr/src/lib.rs (line 73)
-/

open Aeneas Aeneas.Std Result

namespace spqr.SecretOutput.Insts.CoreFmtDebug

/--
**Spec theorem for `spqr.SecretOutput.Insts.CoreFmtDebug.fmt`**:

• Takes a `SecretOutput` value `self` and a `core.fmt.Formatter` value `f`.
• Pattern-matches on the variant of `self`:
  - `None` → delegates to `Formatter.write_str f "None"`
  - `Send(v)` → wraps `v` in `Dyn.mk _ (DebugShared (DebugVec DebugU8))` and delegates to
    `Formatter.debug_tuple_field1_finish f "Send"`
  - `Recv(v)` → wraps `v` in `Dyn.mk _ (DebugShared (DebugVec DebugU8))` and delegates to
    `Formatter.debug_tuple_field1_finish f "Recv"`
• Returns a pair `(core.result.Result Unit core.fmt.Error) × core.fmt.Formatter`.

• The function always succeeds (no panic) for any `SecretOutput` input and any `Formatter` state.

The result satisfies the formatting postcondition:

  `result.1 = .Ok ()  ∧  result.2 = f`

i.e. the debug formatting succeeds with `Ok(())` and the formatter is returned unchanged
(under the current Aeneas simplistic model of the `core::fmt` machinery).

The proof unfolds `fmt`, matches on `self`, and discharges each branch with `step*`.

**Source**: spqr/src/lib.rs (line 73)
-/
@[step]
theorem fmt_spec (self : spqr.SecretOutput) (f : core.fmt.Formatter) :
    fmt self f ⦃ (result : (core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) =>
      result.1 = .Ok () ∧ result.2 = f ⦄ := by
  unfold fmt
  match self with
  | .None =>
    simp only [core.fmt.Formatter.write_str]
    step*
  | .Send _ =>
    simp only [core.fmt.Formatter.debug_tuple_field1_finish]
    step*
  | .Recv _ =>
    simp only [core.fmt.Formatter.debug_tuple_field1_finish]
    step*

end spqr.SecretOutput.Insts.CoreFmtDebug
