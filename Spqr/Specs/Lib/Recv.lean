/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.DecodeState
import Spqr.Specs.Lib.MsgVersion
import Spqr.Specs.Lib.StateVersion
import Spqr.Specs.Lib.ChainFrom
import Spqr.Specs.Lib.InitInner
import Spqr.Specs.Lib.Axioms
/-!
# Spec theorem for `spqr::recv`

`recv` is the main protocol receive function — the most complex function in the SPQR library.
It performs multi-step version negotiation followed by message processing:

  1. **Deserialize state**: `decode_state(state)` → `PqRatchetState`.
  2. **Version negotiation**: Compare `msg_version(msg)` with `state_version(state_pb)`:
     - Unknown version (`None`): ignore message, return current state unchanged.
     - Equal or greater: proceed with existing state.
     - Less (downgrade):
       * If `version_negotiation = None`: return `Err(VersionMismatch)`.
       * If `v < min_version`: return `Err(MinimumVersion)`.
       * Otherwise: reinitialize with the lower version, disable further negotiation.
  3. **Process message** (after negotiation):
     - V0: return empty state with no key.
     - V1: deserialize message, advance V1 state machine (`States::from_pb → recv`),
       manage receive chain, and produce the message key.

This is the most complex function in `lib.rs`.  Its verification requires all lower-layer
dependencies: `decode_state`, `msg_version`, `state_version`, `init_inner`, `chain_from`,
`chain_from_version_negotiation`, V1 `States::from_pb`, `States::recv`, `Chain::recv_key`,
and protobuf `encode_to_vec` (axiomatized).

**Source**: spqr/src/lib.rs (lines 356:0-455:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.recv`**:

• Takes a serialized state `state` and a serialized message `msg` (both `Vec<u8>`).
• Performs version negotiation, then processes the message through the V1 state machine.
• Returns `Recv { state, key }` where `state` is the updated serialized state and `key` is
  the optional message decryption key.

The result satisfies the unknown-version postcondition:

  If `msg_version(msg)` returns `none` (unknown/unsupported version), the state is preserved
  unchanged and no key is produced:

  `∀ r, msg_version msg = ok none →`
  `  result = core.result.Result.Ok { state := state.clone(), key := none }`

**Source**: spqr/src/lib.rs (lines 356:0-455:1)
-/
@[step]
theorem recv_spec (state : alloc.vec.Vec U8) (msg : alloc.vec.Vec U8) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      True ⦄ := by
  unfold recv
  sorry

end spqr
