/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendCt.NoHeaderReceived.New
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
import Spqr.Specs.Aeneas.ResultExpect
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::NoHeaderReceived::new`

`NoHeaderReceived.new` constructs the initial state for the ciphertext-sending side of the
V1 chunked SPQR protocol.  It delegates to `unchunked::NoHeaderReceived::new(auth_key)`,
which applies `initial_ratchet_step` — a single HKDF ratchet step from a zero-initialized
authenticator — constructs a `PolyDecoder` for the header-plus-MAC size, and wraps the
result in the chunked `NoHeaderReceived` struct.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 71:4-79:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.send_ct.NoHeaderReceived

/--
**Spec theorem for `spqr.v1.chunked.send_ct.NoHeaderReceived.new`**:

• Takes an `auth_key : Slice U8`.
• Computes `HEADER_SIZE + MACSIZE`, constructs a `PolyDecoder`.
• Delegates to `v1.unchunked.send_ct.NoHeaderReceived.new auth_key`.
• Wraps the result in the chunked `NoHeaderReceived` struct.

The result satisfies:

  `result.uc.epoch = 1#u64`
  `initial_ratchet_step auth_key.val 1#u64 result.uc.auth`

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 71:4-79:5)
-/
@[step]
theorem new_spec (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max) :
    new auth_key ⦃ (result : v1.chunked.send_ct.NoHeaderReceived) =>
      result.uc.epoch = 1#u64 ∧
      initial_ratchet_step auth_key.val 1#u64 result.uc.auth ⦄ := by
  unfold new
  sorry

end spqr.v1.chunked.send_ct.NoHeaderReceived
