/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::NoHeaderReceived::new`

The `NoHeaderReceived` state is the initial state of the unchunked send-ciphertext protocol in
SPQR's v1 ratchet.  The `new` constructor initialises this state from a raw authentication key
(`auth_key : &[u8]`), proceeding in two steps:

  1. `alloc.slice.Slice.to_vec auth_key` — clone the authentication key slice into an owned
     `Vec<u8>`.
  2. `authenticator.Authenticator.new(cloned_key, 1)` — derive the initial authenticator from the
     cloned key and epoch 1.  Internally this performs an HMAC-based key derivation, producing
     both a `root_key` and a `mac_key` for the first epoch.

The resulting `NoHeaderReceived` struct carries:
  • `epoch = 1` — the protocol always begins at epoch 1.
  • `auth` — the freshly derived `Authenticator` seeded with the given key material.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 92:4-97:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.unchunked.send_ct.NoHeaderReceived

/-- **Spec theorem for `v1.unchunked.send_ct.NoHeaderReceived.new`**:

The constructor always sets the epoch to 1 — the canonical initial epoch of the unchunked
send-ciphertext state machine.  On success the returned `NoHeaderReceived` value satisfies
`result.epoch = 1`.

The proof composes:
  1. `alloc.slice.Slice.to_vec` — cloning of the input slice, producing an owned `Vec<u8>`.
  2. `authenticator.Authenticator.new` — HMAC-based authenticator derivation from the cloned key
     and epoch literal `1`.

Both sub-calls are stepped through monadic bind; the final `ok { epoch := 1#u64, auth := a }`
immediately yields the postcondition `result.epoch = 1#u64`.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 92:4-97:5)
-/
@[step]
theorem new_spec (auth_key : Slice Std.U8) :
    new auth_key ⦃ (result : v1.unchunked.send_ct.NoHeaderReceived) =>
      result.epoch = 1#u64 ⦄ := by
  unfold new
  step*

end spqr.v1.unchunked.send_ct.NoHeaderReceived
