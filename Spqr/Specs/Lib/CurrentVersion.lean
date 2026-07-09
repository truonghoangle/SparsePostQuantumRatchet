/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.DecodeState
/-!
# Spec theorem for `spqr::current_version`

`current_version` deserializes the protocol state and inspects it to determine the current version
negotiation status:

  1. Calls `decode_state(state)` to recover the `PqRatchetState`.
  2. Determines the version from `state_pb.inner`:
     - `None` → `Version::V0`
     - `Some(Inner::V1(_))` → `Version::V1`
  3. Checks `state_pb.version_negotiation`:
     - `None` → `NegotiationComplete(version)` — negotiation has concluded.
     - `Some(vn)` → `StillNegotiating { version, min_version: vn.min_version.try_into()? }` —
       negotiation is still in progress.

This function depends on `decode_state` (F21) and `TryFrom<i32> for Version` (protobuf enum
conversion).

**Source**: spqr/src/lib.rs (lines 249:0-262:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.current_version`**:

• Takes a serialized state `state` (a `Vec<u8>`).
• Deserializes via `decode_state`, then inspects `inner` and `version_negotiation`.
• Returns `Ok(NegotiationComplete(v))` if no version negotiation metadata is present.
• Returns `Ok(StillNegotiating { version, min_version })` if version negotiation is ongoing.
• Returns `Err(StateDecode)` if deserialization fails or if `min_version` cannot be parsed.

The result satisfies the version-query postcondition for the empty-state case:

  `state.val = [] → result = core.result.Result.Ok`
  `  (CurrentVersion.NegotiationComplete proto.pq_ratchet.Version.V0)`

i.e., an empty state (V0 disabled) yields `NegotiationComplete(V0)`.

**Source**: spqr/src/lib.rs (lines 249:0-262:1)
-/
@[step]
theorem current_version_spec (state : alloc.vec.Vec U8) :
    current_version state ⦃ (result : core.result.Result CurrentVersion Error) =>
      state.val = [] →
        result = core.result.Result.Ok
          (CurrentVersion.NegotiationComplete proto.pq_ratchet.Version.V0) ⦄ := by
  unfold current_version
  sorry

end spqr
