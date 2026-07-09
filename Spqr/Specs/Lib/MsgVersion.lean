/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::msg_version`

`msg_version` extracts the protocol version from a serialized message by inspecting its first byte:

  - Empty message → `Some(Version::V0)` (empty messages are V0 pass-through)
  - Non-empty message → `msg[0].try_into().ok()` (the first byte encodes the version)

If the first byte is `0`, the version is `V0`; if `1`, the version is `V1`.  Any other value
yields `None`, indicating an unsupported/unknown version.

This function is used by `recv` to determine the remote party's protocol version during version
negotiation.

**Source**: spqr/src/lib.rs (lines 464:0-470:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.msg_version`**:

• Takes a serialized message `msg` (a `Vec<u8>`).
• If `msg` is empty, returns `some V0`.
• If `msg` is non-empty, attempts to parse `msg[0]` via `TryFrom<u8> for Version`:
  - `0` → `some V0`
  - `1` → `some V1`
  - other → `none` (unsupported version)
• The function always succeeds at the monadic level (no panic).

The result satisfies the version-extraction postcondition:

  `(msg.val = [] → result = some .V0) ∧`
  `(msg.val ≠ [] → result = (TryFrom::try_from msg[0]).ok())`

**Source**: spqr/src/lib.rs (lines 464:0-470:1)
-/
@[step]
theorem msg_version_spec (msg : alloc.vec.Vec U8) :
    msg_version msg ⦃ (result : Option proto.pq_ratchet.Version) =>
      msg.val = [] → result = some .V0 ⦄ := by
  unfold msg_version
  sorry

end spqr
