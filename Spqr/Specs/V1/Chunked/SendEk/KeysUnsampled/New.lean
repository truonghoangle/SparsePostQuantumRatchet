/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendEk.KeysUnsampled.New
/-!
# Spec theorem for `spqr::v1::chunked::send_ek::KeysUnsampled::new`

`KeysUnsampled.new` constructs the initial state for the encapsulation-key-sending side of the
V1 chunked SPQR protocol.  It delegates to `unchunked::KeysUnsampled::new(auth_key)`, which
applies `initial_ratchet_step` — a single HKDF ratchet step from a zero-initialized
authenticator — then wraps the result in the chunked `KeysUnsampled` struct.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 52:4-56:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.send_ek.KeysUnsampled

/--
**Spec theorem for `spqr.v1.chunked.send_ek.KeysUnsampled.new`**:

• Takes an `auth_key : Slice U8`.
• Delegates to `v1.unchunked.send_ek.KeysUnsampled.new auth_key`.
• Wraps the unchunked result in the chunked `KeysUnsampled` struct as `{ uc := ku }`.

The result satisfies:

  `result.uc.epoch = 1#u64`
  `initial_ratchet_step auth_key.val 1#u64 result.uc.auth`

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 52:4-56:5)
-/
@[step]
theorem new_spec (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max) :
    new auth_key ⦃ (result : v1.chunked.send_ek.KeysUnsampled) =>
      result.uc.epoch = 1#u64 ∧
      initial_ratchet_step auth_key.val 1#u64 result.uc.auth ⦄ := by
  unfold new
  sorry

end spqr.v1.chunked.send_ek.KeysUnsampled
