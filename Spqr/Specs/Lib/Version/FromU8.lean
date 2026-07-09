/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::{impl From<Version> for u8}::from`

This trait implementation converts a `Version` enum variant to its `u8` representation.  It is
the (partial) inverse of `TryFrom<u8> for Version`:

  - `Version::V0` → `0u8`
  - `Version::V1` → `1u8`

The mapping is total and injective: every `Version` variant has a unique `u8` representation.
Together with `TryFrom<u8>`, it forms a round-trip:
  `TryFrom::try_from(From::from(v)) = Ok(v)`  for all `v : Version`.

**Source**: spqr/src/lib.rs (lines 190:4-195:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.U8.Insts.CoreConvertFromVersion

/--
**Spec theorem for `spqr.U8.Insts.CoreConvertFromVersion.from`**:

• Takes a `Version` value `v`.
• Pattern-matches on `v`:
  - `V0` → returns `0#u8`
  - `V1` → returns `1#u8`
• The function always succeeds (no panic) for any `Version` input.
• The mapping is injective: `from v₁ = from v₂ → v₁ = v₂`.

The result satisfies the version-to-byte postcondition:

  `(v = .V0 → result = 0#u8) ∧`
  `(v = .V1 → result = 1#u8)`

**Source**: spqr/src/lib.rs (lines 190:4-195:5)
-/
@[step]
theorem from_spec (v : proto.pq_ratchet.Version) :
    U8.Insts.CoreConvertFromVersion.from v ⦃ (result : U8) =>
      (v = .V0 → result = 0#u8) ∧
      (v = .V1 → result = 1#u8) ⦄ := by
  unfold U8.Insts.CoreConvertFromVersion.from
  sorry

end spqr.U8.Insts.CoreConvertFromVersion
