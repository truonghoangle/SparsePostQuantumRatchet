/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::state_version`

`state_version` extracts the protocol version from a deserialized `PqRatchetState` by inspecting
the `inner` field:

  - `inner = None`              → `Version::V0` (no inner state means protocol is disabled)
  - `inner = Some(Inner::V1(_))` → `Version::V1` (V1 inner state present)

This is a pure pattern match with no error paths.  It is used by `recv` to compare the local
state version against the remote message version during version negotiation.

**Source**: spqr/src/lib.rs (lines 457:0-462:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.state_version`**:

• Takes a deserialized `PqRatchetState` value `state`.
• Pattern-matches on `state.inner`:
  - `none` → returns `V0`
  - `some _` → returns `V1`
• The function always succeeds (no panic) for any valid `PqRatchetState` input.

The result satisfies the version-extraction postcondition:

  `(state.inner = none → result = .V0) ∧`
  `(state.inner ≠ none → result = .V1)`

**Source**: spqr/src/lib.rs (lines 457:0-462:1)
-/
@[step]
theorem state_version_spec (state : proto.pq_ratchet.PqRatchetState) :
    state_version state ⦃ (result : proto.pq_ratchet.Version) =>
      (state.inner = none → result = .V0) ∧
      (state.inner ≠ none → result = .V1) ⦄ := by
  unfold state_version
  sorry

end spqr
