/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `TryFrom<u8> for Version`

The `Version` enum has two variants:
```rust
pub enum Version {
    V0 = 0,
    V1 = 1,
}
```
The `TryFrom<u8>` implementation converts a raw byte to a `Version`, returning
an error for unrecognised values:
```rust
impl TryFrom<u8> for Version {
    type Error = String;
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Version::V0),
            1 => Ok(Version::V1),
            _ => Err("Expected 0 or 1".to_owned()),
        }
    }
}
```
After extraction the Lean definition is:
```
def proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String.try_from
  (value : Std.U8) :
  Result (core.result.Result proto.pq_ratchet.Version String)
  := do
  match value with
  | 0#uscalar => ok (core.result.Result.Ok proto.pq_ratchet.Version.V0)
  | 1#uscalar => ok (core.result.Result.Ok proto.pq_ratchet.Version.V1)
  | _ =>
    let s ←
      Str.Insts.AllocBorrowToOwnedString.to_owned
        (toStr "Expected 0 or 1")
    ok (core.result.Result.Err s)
```

The function is total for the valid inputs `0` and `1`, where it returns
`Ok V0` and `Ok V1` respectively. For any other input it returns `Err _`
(contingent on the `to_owned` axiom succeeding).

**Source**: spqr/src/lib.rs (lines 180:4-186:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.Version

/-- **`try_from 0` returns `Ok V0`**.

`try_from (0 : U8)` always succeeds and returns
`core.result.Result.Ok Version.V0`. -/
@[simp]
theorem try_from_zero :
    Insts.CoreConvertTryFromU8String.try_from (0#u8) =
      ok (core.result.Result.Ok proto.pq_ratchet.Version.V0) := by
  unfold Insts.CoreConvertTryFromU8String.try_from
  split
  · rfl
  · next heq => exact absurd heq (by decide)
  · next h1 _ => exfalso; exact h1 (by grind)

/-- **`try_from 1` returns `Ok V1`**.

`try_from (1 : U8)` always succeeds and returns
`core.result.Result.Ok Version.V1`. -/
@[simp]
theorem try_from_one :
    Insts.CoreConvertTryFromU8String.try_from (1#u8) =
      ok (core.result.Result.Ok proto.pq_ratchet.Version.V1) := by
  unfold Insts.CoreConvertTryFromU8String.try_from
  split
  · next heq => exact absurd heq (by decide)
  · rfl
  · next _ h2 => exfalso; exact h2 (by grind)

/--
**Spec theorem for `try_from` on `0`**:

When the input byte is `0`, the function always succeeds and returns
`Ok Version.V0`.

**Source**: spqr/src/lib.rs (lines 180:4-186:5)
-/
@[step]
theorem try_from_V0_spec :
    Insts.CoreConvertTryFromU8String.try_from (0#u8)
      ⦃ (result : core.result.Result
          proto.pq_ratchet.Version String) =>
        result =
          core.result.Result.Ok proto.pq_ratchet.Version.V0 ⦄ := by
  simp [WP.spec_ok]

/--
**Spec theorem for `try_from` on `1`**:

When the input byte is `1`, the function always succeeds and returns
`Ok Version.V1`.

**Source**: spqr/src/lib.rs (lines 180:4-186:5)
-/
@[step]
theorem try_from_V1_spec :
    Insts.CoreConvertTryFromU8String.try_from (1#u8)
      ⦃ (result : core.result.Result
          proto.pq_ratchet.Version String) =>
        result =
          core.result.Result.Ok proto.pq_ratchet.Version.V1 ⦄ := by
  simp [WP.spec_ok]

/--
**Spec theorem for `try_from` on valid version bytes**:

• The function always succeeds (no panic / no error) when the input byte
  is `0` or `1`. It returns `core.result.Result.Ok Version.V0` for `0`
  and `core.result.Result.Ok Version.V1` for `1`.
• The postcondition characterises the result as an `Ok` value carrying the
  corresponding `Version` variant:
    `try_from value = ok (Result.Ok v)` where `v` is determined by the
    input byte.
• This establishes that the `TryFrom<u8>` trait implementation faithfully
  maps the two valid version discriminants to their `Version` enum values
  without loss of information.
• The conversion is the left inverse of `From<Version> for u8`: for each
  `Version` variant, `try_from (from v) = ok (Ok v)`.

**Source**: spqr/src/lib.rs (lines 180:4-186:5)
-/
@[step]
theorem try_from_spec (v : proto.pq_ratchet.Version) :
    Insts.CoreConvertTryFromU8String.try_from
      (match v with
        | .V0 => 0#u8
        | .V1 => 1#u8)
      ⦃ (result : core.result.Result
          proto.pq_ratchet.Version String) =>
        result = core.result.Result.Ok v ⦄ := by
  rcases v with _ | _ <;> simp [WP.spec_ok]

end spqr.proto.pq_ratchet.Version
