/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.DecodeState
import Spqr.Specs.Lib.Axioms
/-!
# Spec theorem for `spqr::send`

`send` is the main protocol send function.  It performs the following steps:

  1. **Deserialize state**: `decode_state(state)` → `PqRatchetState`.
  2. **V0 (disabled)**: If `inner = None`, return empty state/message with no key.
  3. **V1 (active)**: If `inner = Some(V1(pb))`:
     a. Deserialize and advance the V1 state machine: `States::from_pb(pb)?.send(rng)?`.
     b. Recover or construct the key chain from `state_pb.chain` / `version_negotiation`.
     c. If the chain exists and a new epoch secret is available, add it to the chain.
     d. Request a send key from the chain for the current epoch.
     e. Serialize the updated state, message, and optional message key.

The function carries the Rust annotation `#[hax_lib::fstar::verification_status(lax)]`, indicating
it is not yet fully verified in the F\* extraction either.

This is the most complex send-path function in the SPQR protocol.  Its verification requires:
  - `decode_state` (F21)
  - `chain_from_version_negotiation` (F17) / `chain_from` (F18)
  - `state_version` (F19)
  - V1 `States::from_pb`, `States::send`
  - `Chain::add_epoch`, `Chain::send_key`
  - Protobuf `encode_to_vec` (axiomatized)

**Source**: spqr/src/lib.rs (lines 265:0-326:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.send`**:

• Takes a serialized state `state`, a random number generator `rng`.
• Deserializes state, advances V1 state machine, manages key chain, serializes output.
• For V0 (empty state): returns `Send { state = [], msg = [], key = none }`.
• For V1: returns `Send { state = encoded_state, msg = serialized_msg, key = msg_key }`.

The result satisfies the V0 pass-through postcondition:

  `state.val = [] →`
  `  result.1 = core.result.Result.Ok { state := Vec.new, msg := Vec.new, key := none }`

**Source**: spqr/src/lib.rs (lines 265:0-326:1)
-/
@[step]
theorem send_spec {R : Type} (randrngRngInst : rand.rng.Rng R)
    (rand_coreCryptoRngInst : rand_core.CryptoRng R)
    (state : alloc.vec.Vec U8) (rng : R) :
    send randrngRngInst rand_coreCryptoRngInst state rng
      ⦃ (result : (core.result.Result Send Error) × R) =>
        state.val = [] →
          result.1 = core.result.Result.Ok
            { state := alloc.vec.Vec.new U8,
              msg := alloc.vec.Vec.new U8,
              key := none } ⦄ := by
  unfold send
  sorry

end spqr
