/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.New
/-!
# Spec theorem for `spqr::v1::unchunked::send_ek::KeysUnsampled::new`

`KeysUnsampled.new` constructs the initial state for the encapsulation-key-sending side of the
V1 unchunked SPQR protocol.  It is the entry point of the send-EK state machine and places
the sender into the `KeysUnsampled` state at epoch 1.

The constructor performs the following steps:

1. Clones the input byte-slice `auth_key` into a `Vec<u8>` via `to_vec`.
2. Applies `initial_ratchet_step` — a single HKDF ratchet step from a zero-initialized
   authenticator with the cloned key as shared secret at epoch 1:
   - `ikm  = ZERO_SALT ++ auth_key`
   - `info = PROTOCOL_LABEL ++ (1u64).to_be_bytes()`
   - `kdf_out = HKDF-SHA256(ZERO_SALT, ikm, info, 64)`
   - `root_key = kdf_out[0..32]`, `mac_key = kdf_out[32..64]`
3. Returns a `KeysUnsampled` struct with `epoch = 1` and the freshly initialised
   authenticator.

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 76:4-81:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ek.KeysUnsampled

/--
**Spec theorem for `spqr.v1.unchunked.send_ek.KeysUnsampled.new`**:

• Takes an `auth_key : Slice U8` — a byte-slice representing the initial authentication root key.
• Clones the slice into a `Vec U8` via `alloc.slice.Slice.to_vec`.
• Applies `initial_ratchet_step auth_key.val 1#u64` to derive the authenticator via explicit
  HKDF-SHA256 from a zero-initialized state at epoch 1.
• Returns a `KeysUnsampled` with `epoch = 1#u64` and the resulting authenticator.

• The function succeeds (no panic) whenever `auth_key.length ≤ U32.max`.

The result satisfies:

  `result.epoch = 1#u64`
  `initial_ratchet_step auth_key.val 1#u64 result.auth`

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 76:4-81:5)
-/
@[step]
theorem new_spec (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max) :
    new auth_key ⦃ (result : v1.unchunked.send_ek.KeysUnsampled) =>
      result.epoch = 1#u64 ∧
      initial_ratchet_step auth_key.val 1#u64 result.auth ⦄ := by
  unfold new
  sorry

end spqr.v1.unchunked.send_ek.KeysUnsampled
