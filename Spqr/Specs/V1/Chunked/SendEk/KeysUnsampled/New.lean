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
V1 chunked SPQR protocol.  It is the entry point of the chunked send-EK state machine and places
the sender into the `KeysUnsampled` state.

The constructor performs the following steps:

1. Delegates to `unchunked::KeysUnsampled::new(auth_key)`, which clones the input byte-slice
   `auth_key` into a `Vec<u8>` via `to_vec`, then calls `Authenticator::new(auth_key.to_vec(), 1)`
   to derive a pair of 32-byte keys (`root_key` and `mac_key`) via HKDF-SHA256, domain-separated
   by a fixed protocol label and epoch counter `1`.
2. Wraps the resulting unchunked `KeysUnsampled` in the chunked `KeysUnsampled` struct as
   `Self { uc }`.

The by-value `new` introduces no additional logic beyond the delegation to the unchunked
constructor, so its postconditions for the authenticator fields are inherited from the
corresponding `unchunked.KeysUnsampled.new` specification.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 52:4-56:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.send_ek.KeysUnsampled

/--
**Spec theorem for `spqr.v1.chunked.send_ek.KeysUnsampled.new`**:

• Takes an `auth_key : Slice U8` — a byte-slice representing the initial authentication root key.
• Delegates to `v1.unchunked.send_ek.KeysUnsampled.new auth_key`, which clones the slice into
  a `Vec U8`, then feeds the cloned key and epoch `1` into HKDF-SHA256 to derive a pair of
  32-byte keys (`root_key` and `mac_key`), returning an unchunked `KeysUnsampled` with
  `epoch = 1#u64`.
• Wraps the unchunked result in the chunked `KeysUnsampled` struct as `{ uc := ku }`.

• The function succeeds (no panic) whenever `auth_key.length ≤ U32.max`, ensuring that
  the key material does not overflow the HKDF input construction.

The result satisfies the following postconditions:

  `result.uc.epoch = 1#u64`
  `result.uc.auth.root_key.length = 32`
  `result.uc.auth.mac_key.length  = 32`
  `∃ v, v.val = auth_key.val ∧ authenticator.Authenticator.new v 1#u64 = ok result.uc.auth`

i.e. the inner unchunked state has epoch initialised to 1, both key fields of the embedded
authenticator are exactly 32 bytes, and the authenticator is deterministically derived from
the input `auth_key` via `Authenticator.new(auth_key.to_vec(), 1)`, which feeds `auth_key`
and epoch `1` into HKDF-SHA256 to produce the 32-byte `root_key` and `mac_key`.

The proof unfolds `new` to expose the underlying `unchunked.KeysUnsampled.new` call and
discharges the resulting goal with `step*`, which applies the already-registered
`unchunked.KeysUnsampled.new_spec`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 52:4-56:5)
-/
@[step]
theorem new_spec (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max) :
    new auth_key ⦃ (result : v1.chunked.send_ek.KeysUnsampled) =>
      result.uc.epoch = 1#u64 ∧
      result.uc.auth.root_key.length = 32 ∧
      result.uc.auth.mac_key.length = 32 ∧
      ∃ v, v.val = auth_key.val ∧
        authenticator.Authenticator.new v 1#u64 = ok result.uc.auth ⦄ := by
  unfold new
  step*

end spqr.v1.chunked.send_ek.KeysUnsampled
