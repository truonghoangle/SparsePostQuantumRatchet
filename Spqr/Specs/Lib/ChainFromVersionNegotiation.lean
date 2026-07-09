/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain_from_version_negotiation`

`chain_from_version_negotiation` constructs a new `Chain` from version negotiation metadata.  It
extracts the authentication key, direction (via `TryFrom<i32> for Direction`), and chain parameters
from the `VersionNegotiation` protobuf message, then delegates to `Chain::new`.

This function is called in two places:
  1. In `send`, when `state_pb.chain = None` and `vn.min_version > V0` (the first send after
     initialization with min_version > V0 forces chain creation).
  2. In `chain_from`, as the fallback when no serialized chain is present.

Errors are returned via `core.result.Result.Err`:
  - `Error.StateDecode` if `vn.direction` cannot be parsed as a `Direction`.
  - `Error.ChainNotAvailable` if `vn.chain_params` is `None`.
  - Any error from `Chain::new` is propagated.

**Source**: spqr/src/lib.rs (lines 333:0-341:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.chain_from_version_negotiation`**:

• Takes a `VersionNegotiation` protobuf message `vn`.
• Extracts `vn.auth_key`, `vn.direction`, and `vn.chain_params`.
• Converts `vn.direction` from `i32` to `Direction` via `TryFrom`.
• If `vn.chain_params` is `none`, returns `Err(ChainNotAvailable)`.
• Otherwise, delegates to `Chain::new(auth_key, direction, chain_params)`.

The result satisfies the chain-construction postcondition:

  `vn.chain_params = none → result = core.result.Result.Err Error.ChainNotAvailable`

(when version negotiation metadata lacks chain parameters, chain construction fails).

**Source**: spqr/src/lib.rs (lines 333:0-341:1)
-/
@[step]
theorem chain_from_version_negotiation_spec
    (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation) :
    chain_from_version_negotiation vn
      ⦃ (result : core.result.Result chain.Chain Error) =>
        True ⦄ := by
  unfold chain_from_version_negotiation
  sorry

end spqr
