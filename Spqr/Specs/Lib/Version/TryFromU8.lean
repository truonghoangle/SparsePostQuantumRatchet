/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::{impl TryFrom<u8, String> for Version}::try_from`

This trait implementation converts a `u8` byte value to a `Version` enum variant.  It implements
the `TryFrom<u8>` trait, mapping:

  - `0` → `Ok(Version::V0)`
  - `1` → `Ok(Version::V1)`
  - anything else → `Err("Expected 0 or 1")`

This is used in `msg_version` to parse the first byte of a serialized message into a protocol
version, and in `current_version` via `vn.min_version.try_into()`.

**Source**: spqr/src/lib.rs (lines 180:4-186:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String

/--
**Spec theorem for `spqr.proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String.try_from`**:

• Takes a `U8` value `value`.
• Pattern-matches on `value`:
  - `0` → returns `Ok(V0)`
  - `1` → returns `Ok(V1)`
  - otherwise → returns `Err("Expected 0 or 1")`
• The function always succeeds at the monadic level (no panic); errors are returned via
  `core.result.Result.Err`.

The result satisfies the version-parsing postcondition:

  `(value = 0 → result = Ok V0) ∧`
  `(value = 1 → result = Ok V1) ∧`
  `(value ≠ 0 ∧ value ≠ 1 → ∃ s, result = Err s)`

**Source**: spqr/src/lib.rs (lines 180:4-186:5)
-/
@[step]
theorem try_from_spec (value : U8) :
    try_from value ⦃ (result : core.result.Result proto.pq_ratchet.Version String) =>
      (value = 0#u8 → result = core.result.Result.Ok proto.pq_ratchet.Version.V0) ∧
      (value = 1#u8 → result = core.result.Result.Ok proto.pq_ratchet.Version.V1) ∧
      (value ≠ 0#u8 → value ≠ 1#u8 → ∃ s, result = core.result.Result.Err s) ⦄ := by
  unfold try_from
  sorry

end spqr.proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String
