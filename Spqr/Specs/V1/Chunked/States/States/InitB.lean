/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Chunked.SendCt.NoHeaderReceived.New
/-!
# Spec theorem for `spqr::v1::chunked::states::{spqr::v1::chunked::states::States}::init_b`

`States.init_b` constructs the initial state for the **B-side** (ciphertext-sending side)
of the V1 chunked SPQR protocol.  It delegates to `NoHeaderReceived::new(auth_key)`, which
applies `initial_ratchet_step` — a single explicit HKDF ratchet step from a zero-initialized
authenticator at epoch 1 — and wraps the result in the `States.NoHeaderReceived` variant.

**Source**: spqr/src/v1/chunked/states.rs (lines 62:4-64:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.States

/--
**Spec theorem for `spqr.v1.chunked.states.States.init_b`**:

• Takes an `auth_key : Slice U8`.
• Delegates to `v1.chunked.send_ct.NoHeaderReceived.new auth_key`.
• Wraps the result in `States.NoHeaderReceived`.

The result satisfies:

  `∃ nhr, result = States.NoHeaderReceived nhr ∧
    nhr.uc.epoch = 1#u64 ∧
    initial_ratchet_step auth_key.val 1#u64 nhr.uc.auth`

**Source**: spqr/src/v1/chunked/states.rs (lines 62:4-64:5)
-/
@[step]
theorem init_b_spec (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max) :
    init_b auth_key ⦃ (result : v1.chunked.states.States) =>
      ∃ nhr, result = States.NoHeaderReceived nhr ∧
        nhr.uc.epoch = 1#u64 ∧
        initial_ratchet_step auth_key.val 1#u64 nhr.uc.auth ⦄ := by
  unfold init_b
  sorry

end spqr.v1.chunked.states.States
