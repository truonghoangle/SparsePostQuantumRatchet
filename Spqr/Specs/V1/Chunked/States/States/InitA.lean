/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Chunked.SendEk.KeysUnsampled.New
/-!
# Spec theorem for `spqr::v1::chunked::states::{spqr::v1::chunked::states::States}::init_a`

`States.init_a` constructs the initial state for the **A-side** (encapsulation-key-sending side)
of the V1 chunked SPQR protocol.  It delegates to `KeysUnsampled::new(auth_key)`, which
applies `initial_ratchet_step` — a single explicit HKDF ratchet step from a zero-initialized
authenticator at epoch 1 — and wraps the result in the `States.KeysUnsampled` variant.

**Source**: spqr/src/v1/chunked/states.rs (lines 58:4-60:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.States

/--
**Spec theorem for `spqr.v1.chunked.states.States.init_a`**:

• Takes an `auth_key : Slice U8`.
• Delegates to `v1.chunked.send_ek.KeysUnsampled.new auth_key`.
• Wraps the result in `States.KeysUnsampled`.

The result satisfies:

  `∃ ku, result = States.KeysUnsampled ku ∧
    ku.uc.epoch = 1#u64 ∧
    initial_ratchet_step auth_key.val 1#u64 ku.uc.auth`

**Source**: spqr/src/v1/chunked/states.rs (lines 58:4-60:5)
-/
@[step]
theorem init_a_spec (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max) :
    init_a auth_key ⦃ (result : v1.chunked.states.States) =>
      ∃ ku, result = States.KeysUnsampled ku ∧
        ku.uc.epoch = 1#u64 ∧
        initial_ratchet_step auth_key.val 1#u64 ku.uc.auth ⦄ := by
  unfold init_a
  sorry

end spqr.v1.chunked.states.States
