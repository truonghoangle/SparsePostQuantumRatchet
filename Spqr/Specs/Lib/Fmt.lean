/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::{impl core::fmt::Debug for spqr::SecretOutput}::fmt`

The `SecretOutput` enum has three variants:
```rust
#[derive(PartialEq, Debug)]
pub enum SecretOutput {
    None,
    Send(Secret),
    Recv(Secret),
}
```
where `Secret = Vec<u8>`. The `#[derive(Debug)]` attribute auto-generates the `fmt::Debug`
implementation, which formats each variant as:
  • `None` → writes the string `"None"` via `core.fmt.Formatter.write_str`
  • `Send(v)` → writes a debug tuple `"Send"` with the inner `Vec<u8>` payload via
    `core.fmt.Formatter.debug_tuple_field1_finish`
  • `Recv(v)` → writes a debug tuple `"Recv"` with the inner `Vec<u8>` payload via
    `core.fmt.Formatter.debug_tuple_field1_finish`

After extraction the Lean definition is:
```
def SecretOutput.Insts.CoreFmtDebug.fmt
  (self : SecretOutput) (f : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  := do
  match self with
  | SecretOutput.None => core.fmt.Formatter.write_str f (toStr "None")
  | SecretOutput.Send __self_0 =>
    let __self_01 :=
      Dyn.mk _ (core.fmt.DebugShared (core.fmt.DebugVec core.fmt.DebugU8))
        __self_0
    core.fmt.Formatter.debug_tuple_field1_finish f (toStr "Send") __self_01
  | SecretOutput.Recv __self_0 =>
    let __self_01 :=
      Dyn.mk _ (core.fmt.DebugShared (core.fmt.DebugVec core.fmt.DebugU8))
        __self_0
    core.fmt.Formatter.debug_tuple_field1_finish f (toStr "Recv") __self_01
```

The function matches on the `SecretOutput` variant and delegates to the appropriate formatter
method. The function is total: it never panics and always succeeds (assuming the underlying
formatter operations succeed).

**Source**: spqr/src/lib.rs (line 73, `#[derive(PartialEq, Debug)]`)
-/

open Aeneas Aeneas.Std Result

/-! ### Step lemmas for formatter primitives

The Aeneas extraction models `core.fmt.Formatter.write_str` and
`core.fmt.Formatter.debug_tuple_field1_finish` as concrete definitions that
always succeed and return the formatter unchanged (a simplistic model of the
real Rust implementation which would modify the formatter's internal buffer).

The step lemmas below expose the result to the `step` tactic and to `simp`. -/

/-- **Step lemma for `core.fmt.Formatter.write_str`**:

The call always succeeds and returns `(Result.Ok (), f)` where `f` is the
(unchanged) formatter.  This is a simplistic model matching the Aeneas
extraction definition. -/
@[step]
theorem core.fmt.Formatter.write_str_spec (f : core.fmt.Formatter) (s : Str) :
    core.fmt.Formatter.write_str f s
      ⦃ (r : (core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) =>
        r = (core.result.Result.Ok (), f) ⦄ := by
  simp [core.fmt.Formatter.write_str, WP.spec_ok]

/-- **Step lemma for `core.fmt.Formatter.debug_tuple_field1_finish`**:

The call always succeeds and returns `(Result.Ok (), f)` where `f` is the
(unchanged) formatter.  This is a simplistic model matching the Aeneas
extraction definition. -/
@[step]
theorem core.fmt.Formatter.debug_tuple_field1_finish_spec
    (f : core.fmt.Formatter) (tag : Str)
    (field : Dyn (fun _dyn => core.fmt.Debug _dyn)) :
    core.fmt.Formatter.debug_tuple_field1_finish f tag field
      ⦃ (r : (core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) =>
        r = (core.result.Result.Ok (), f) ⦄ := by
  simp [core.fmt.Formatter.debug_tuple_field1_finish, WP.spec_ok]

namespace spqr.SecretOutput

/-- **`fmt` unfolds to `write_str` on the `None` variant**.

When `self = SecretOutput.None`, the function simply writes the string `"None"` to the formatter
via `core.fmt.Formatter.write_str`. -/
@[simp]
theorem fmt_none (f : core.fmt.Formatter) :
    Insts.CoreFmtDebug.fmt SecretOutput.None f =
      core.fmt.Formatter.write_str f (toStr "None") := by
  simp [Insts.CoreFmtDebug.fmt]

/-- **`fmt` unfolds to `debug_tuple_field1_finish` on the `Send` variant**.

When `self = SecretOutput.Send v`, the function wraps the payload in a `Dyn` value using
`core.fmt.DebugShared (core.fmt.DebugVec core.fmt.DebugU8)` and delegates to
`core.fmt.Formatter.debug_tuple_field1_finish` with the tag `"Send"`. -/
@[simp]
theorem fmt_send (v : alloc.vec.Vec Std.U8) (f : core.fmt.Formatter) :
    Insts.CoreFmtDebug.fmt (SecretOutput.Send v) f =
      core.fmt.Formatter.debug_tuple_field1_finish f (toStr "Send")
        (Dyn.mk _ (core.fmt.DebugShared (core.fmt.DebugVec core.fmt.DebugU8)) v) := by
  simp [Insts.CoreFmtDebug.fmt]

/-- **`fmt` unfolds to `debug_tuple_field1_finish` on the `Recv` variant**.

When `self = SecretOutput.Recv v`, the function wraps the payload in a `Dyn` value using
`core.fmt.DebugShared (core.fmt.DebugVec core.fmt.DebugU8)` and delegates to
`core.fmt.Formatter.debug_tuple_field1_finish` with the tag `"Recv"`. -/
@[simp]
theorem fmt_recv (v : alloc.vec.Vec Std.U8) (f : core.fmt.Formatter) :
    Insts.CoreFmtDebug.fmt (SecretOutput.Recv v) f =
      core.fmt.Formatter.debug_tuple_field1_finish f (toStr "Recv")
        (Dyn.mk _ (core.fmt.DebugShared (core.fmt.DebugVec core.fmt.DebugU8)) v) := by
  simp [Insts.CoreFmtDebug.fmt]

/--
**Spec theorem for `SecretOutput.Insts.CoreFmtDebug.fmt`**:

• The function always succeeds (no panic / no error) for any `SecretOutput` input and any
  formatter state. When called on `None` it delegates to `core.fmt.Formatter.write_str`; when
  called on `Send(v)` or `Recv(v)` it delegates to
  `core.fmt.Formatter.debug_tuple_field1_finish` with the appropriate variant name and a
  `Dyn`-wrapped payload.
• The postcondition states that the result is `(Result.Ok (), f)`, i.e. the call always
  succeeds and returns the formatter unchanged. This follows from the Aeneas extraction model
  where both `write_str` and `debug_tuple_field1_finish` always return `.ok (.Ok (), fmt)`.

**Source**: spqr/src/lib.rs (line 73, `#[derive(PartialEq, Debug)]`)
-/
@[step]
theorem fmt_spec (self : spqr.SecretOutput) (f : core.fmt.Formatter) :
    spqr.SecretOutput.Insts.CoreFmtDebug.fmt self f
      ⦃ (r : (core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) =>
        r = (core.result.Result.Ok (), f) ⦄ := by
  unfold Insts.CoreFmtDebug.fmt
  rcases self with _ | ⟨v⟩ | ⟨v⟩ <;>
    simp_all [core.fmt.Formatter.write_str, core.fmt.Formatter.debug_tuple_field1_finish,
              WP.spec_ok]

end spqr.SecretOutput
