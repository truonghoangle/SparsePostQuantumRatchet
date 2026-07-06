/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Chunked.SendEk.KeysUnsampled.New
/-!
# Spec theorem for `spqr::v1::chunked::states::{spqr::v1::chunked::states::States}::init_a`

`States.init_a` constructs the initial state for the **A-side** (encapsulation-key-sending side) of
the V1 chunked SPQR protocol.  It is the entry point for party A's state machine and places the
participant into the `KeysUnsampled` state at epoch 1, ready to sample ML-KEM 768 keys and begin
sending header chunks to party B.

The constructor performs the following steps:

1. Delegates to `v1::chunked::send_ek::KeysUnsampled::new(auth_key)` to construct the
   initial `KeysUnsampled` state, which itself:
   - Delegates to the unchunked `KeysUnsampled::new`, which clones the input byte-slice
     `auth_key` into a `Vec<u8>` via `to_vec`.
   - Calls `Authenticator::new(auth_key.to_vec(), 1)` to derive a pair of 32-byte keys
     (`root_key` and `mac_key`) via HKDF-SHA256, domain-separated by a fixed protocol label
     and epoch counter `1`.
   - Wraps the result in the chunked `KeysUnsampled` struct as `Self { uc }`.
2. Wraps the result in the `States.KeysUnsampled` variant of the `States` enum.

The by-value `init_a` introduces no additional logic beyond the delegation to the
`KeysUnsampled` constructor, so its postconditions for the authenticator fields are
inherited from the corresponding `KeysUnsampled.new` specification.

**Source**: spqr/src/v1/chunked/states.rs (lines 58:4-60:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.States

/--
**Spec theorem for `spqr.v1.chunked.states.States.init_a`**:

• Takes an `auth_key : Slice U8` — a byte-slice representing the initial authentication root key.
• Delegates to `v1.chunked.send_ek.KeysUnsampled.new auth_key`, which constructs the initial
  `KeysUnsampled` state for the encapsulation-key-sending side (epoch = 1, authenticator derived
  from `auth_key` via HKDF-SHA256).
• Wraps the resulting `KeysUnsampled` in the `States.KeysUnsampled` constructor to produce
  a value of the `States` enum.

• The function succeeds (no panic) whenever `auth_key.length ≤ U32.max`, ensuring that
  the key material does not overflow the HKDF input construction.

The result satisfies the following postconditions:

  `∃ ku, result = States.KeysUnsampled ku`
  `ku.uc.epoch = 1#u64`
  `ku.uc.auth.root_key.length = 32`
  `ku.uc.auth.mac_key.length  = 32`
  `∃ v, v.val = auth_key.val ∧ authenticator.Authenticator.new v 1#u64 = ok ku.uc.auth`

i.e. the result is the `KeysUnsampled` variant, whose inner unchunked state has epoch
initialised to 1, both key fields of the embedded authenticator are exactly 32 bytes, and the
authenticator is deterministically derived from the input `auth_key` via
`Authenticator.new(auth_key.to_vec(), 1)`, which feeds `auth_key` and epoch `1` into
HKDF-SHA256 to produce the 32-byte `root_key` and `mac_key`.

The proof unfolds `init_a` to expose the underlying `KeysUnsampled.new` call and discharges
the resulting goal with `step*`, which applies the already-registered `new_spec`.

**Source**: spqr/src/v1/chunked/states.rs (lines 58:4-60:5)
-/
@[step]
theorem init_a_spec (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max) :
    init_a auth_key ⦃ (result : v1.chunked.states.States) =>
      ∃ ku, result = States.KeysUnsampled ku ∧
        ku.uc.epoch = 1#u64 ∧
        ku.uc.auth.root_key.length = 32 ∧
        ku.uc.auth.mac_key.length = 32 ∧
        ∃ v, v.val = auth_key.val ∧
          authenticator.Authenticator.new v 1#u64 = ok ku.uc.auth ⦄ := by
  unfold init_a
  step*

end spqr.v1.chunked.states.States
