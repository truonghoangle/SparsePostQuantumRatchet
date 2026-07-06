/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Chunked.SendCt.NoHeaderReceived.New
/-!
# Spec theorem for `spqr::v1::chunked::states::{spqr::v1::chunked::states::States}::init_b`

`States.init_b` constructs the initial state for the **B-side** (ciphertext-sending side) of the
V1 chunked SPQR protocol.  It is the entry point for party B's state machine and places the
participant into the `NoHeaderReceived` state at epoch 1, ready to receive chunked header data
from party A.

The constructor performs the following steps:

1. Delegates to `v1::chunked::send_ct::NoHeaderReceived::new(auth_key)` to construct the
   initial `NoHeaderReceived` state, which itself:
   - Computes `HEADER_SIZE + MACSIZE` (the total byte length of the ML-KEM 768 header and
     its 32-byte authentication tag).
   - Constructs a `PolyDecoder` for the computed size.
   - Creates an unchunked `NoHeaderReceived` with `epoch = 1` and a freshly initialised
     authenticator whose `root_key` and `mac_key` are derived via HKDF-SHA256 from `auth_key`.
2. Wraps the result in the `States.NoHeaderReceived` variant of the `States` enum.

The by-value `init_b` introduces no additional logic beyond the delegation to the
`NoHeaderReceived` constructor, so its postconditions for the authenticator fields are
inherited from the corresponding `NoHeaderReceived.new` specification.

**Source**: spqr/src/v1/chunked/states.rs (lines 62:4-64:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.States

/--
**Spec theorem for `spqr.v1.chunked.states.States.init_b`**:

• Takes an `auth_key : Slice U8` — a byte-slice representing the initial authentication root key.
• Delegates to `v1.chunked.send_ct.NoHeaderReceived.new auth_key`, which constructs the initial
  `NoHeaderReceived` state for the ciphertext-sending side (epoch = 1, authenticator derived from
  `auth_key` via HKDF-SHA256).
• Wraps the resulting `NoHeaderReceived` in the `States.NoHeaderReceived` constructor to produce
  a value of the `States` enum.

• The function succeeds (no panic) whenever `auth_key.length ≤ U32.max`, ensuring that
  the key material does not overflow the HKDF input construction.

The result satisfies the following postconditions:

  `∃ nhr, result = States.NoHeaderReceived nhr`
  `nhr.uc.epoch = 1#u64`
  `nhr.uc.auth.root_key.length = 32`
  `nhr.uc.auth.mac_key.length  = 32`
  `∃ v, v.val = auth_key.val ∧ authenticator.Authenticator.new v 1#u64 = ok nhr.uc.auth`

i.e. the result is the `NoHeaderReceived` variant, whose inner unchunked state has epoch
initialised to 1, both key fields of the embedded authenticator are exactly 32 bytes, and the
authenticator is deterministically derived from the input `auth_key` via
`Authenticator.new(auth_key.to_vec(), 1)`, which feeds `auth_key` and epoch `1` into
HKDF-SHA256 to produce the 32-byte `root_key` and `mac_key`.

The proof unfolds `init_b` to expose the underlying `NoHeaderReceived.new` call and discharges
the resulting goal with `step*`, which applies the already-registered `new_spec`.

**Source**: spqr/src/v1/chunked/states.rs (lines 62:4-64:5)
-/
@[step]
theorem init_b_spec (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max) :
    init_b auth_key ⦃ (result : v1.chunked.states.States) =>
      ∃ nhr, result = States.NoHeaderReceived nhr ∧
        nhr.uc.epoch = 1#u64 ∧
        nhr.uc.auth.root_key.length = 32 ∧
        nhr.uc.auth.mac_key.length = 32 ∧
        ∃ v, v.val = auth_key.val ∧
          authenticator.Authenticator.new v 1#u64 = ok nhr.uc.auth ⦄ := by
  unfold init_b
  step*

end spqr.v1.chunked.states.States
