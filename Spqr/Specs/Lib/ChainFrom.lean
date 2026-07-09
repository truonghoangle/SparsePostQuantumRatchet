/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.ChainFromVersionNegotiation
/-!
# Spec theorem for `spqr::chain_from`

`chain_from` is a two-level fallback chain constructor:

  1. If `pb` (a serialized `Chain` protobuf) is `Some`, deserialize it via `Chain::from_pb`.
  2. If `pb` is `None`, fall back to version negotiation metadata:
     - If `vn` is `None`, return `Err(ChainNotAvailable)`.
     - If `vn` is `Some`, delegate to `chain_from_version_negotiation(vn)`.

This function is used by both `send` and `recv` to recover or construct the key chain from the
current protocol state.

**Source**: spqr/src/lib.rs (lines 343:0-354:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.chain_from`**:

• Takes an optional serialized chain `pb` and optional version negotiation metadata `vn`.
• If `pb = some pb₁`: deserializes `pb₁` via `Chain::from_pb`.
• If `pb = none ∧ vn = none`: returns `Err(ChainNotAvailable)`.
• If `pb = none ∧ vn = some vn₁`: delegates to `chain_from_version_negotiation(vn₁)`.

The result satisfies the chain-recovery postcondition:

  `(pb = none ∧ vn = none →`
  `  result = core.result.Result.Err Error.ChainNotAvailable)`

**Source**: spqr/src/lib.rs (lines 343:0-354:1)
-/
@[step]
theorem chain_from_spec
    (pb : Option proto.pq_ratchet.Chain)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation) :
    chain_from pb vn ⦃ (result : core.result.Result chain.Chain Error) =>
      (pb = none → vn = none →
        result = core.result.Result.Err Error.ChainNotAvailable) ⦄ := by
  unfold chain_from
  sorry

end spqr
