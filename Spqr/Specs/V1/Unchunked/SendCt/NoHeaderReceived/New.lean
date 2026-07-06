/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.New
/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::NoHeaderReceived::new`

`NoHeaderReceived.new` constructs the initial state for the ciphertext-sending side of the
V1 unchunked SPQR protocol.  It is the entry point of the send-CT state machine and places
the sender into the `NoHeaderReceived` state at epoch 1.

The constructor performs the following steps:

1. Clones the input byte-slice `auth_key` into a `Vec<u8>` via `to_vec`.
2. Delegates to `Authenticator::new(auth_key.to_vec(), 1)`, which derives a pair of 32-byte
   keys (`root_key` and `mac_key`) via HKDF-SHA256, domain-separated by a fixed protocol label
   and epoch counter `1`.
3. Returns a `NoHeaderReceived` struct with `epoch = 1` and the freshly initialised
   authenticator.

The by-value `new` introduces no additional logic beyond the delegation to `Authenticator::new`,
so its postcondition for the authenticator fields is inherited from the corresponding
`Authenticator.new` specification.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 92:4-97:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ct.NoHeaderReceived

/--
**Spec theorem for `spqr.v1.unchunked.send_ct.NoHeaderReceived.new`**:

• Takes an `auth_key : Slice U8` — a byte-slice representing the initial authentication root key.
• Clones the slice into a `Vec U8` via `alloc.slice.Slice.to_vec`.
• Delegates to `authenticator.Authenticator.new v 1#u64`, which feeds the cloned key and
  epoch `1` into HKDF-SHA256 to derive a pair of 32-byte keys (`root_key` and `mac_key`).
• Returns a `NoHeaderReceived` with `epoch = 1#u64` and the resulting authenticator.

• The function succeeds (no panic) whenever `auth_key.length ≤ U32.max`, ensuring that
  the key material does not overflow the HKDF input construction.

The result satisfies the following postconditions:

  `result.epoch = 1#u64`
  `result.auth.root_key.length = 32`
  `result.auth.mac_key.length  = 32`
  `∃ v, v.val = auth_key.val ∧ authenticator.Authenticator.new v 1#u64 = ok result.auth`

i.e. the epoch is initialised to 1, both key fields of the embedded authenticator are exactly
32 bytes, and the authenticator is deterministically derived from the input `auth_key` via
`Authenticator.new(auth_key.to_vec(), 1)`, which feeds `auth_key` and epoch `1` into
HKDF-SHA256 to produce the 32-byte `root_key` and `mac_key`.

The proof unfolds `new` to expose the underlying `Authenticator.new` call and discharges the
resulting goal with `step*`, which applies the already-registered `Authenticator.new_spec`.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 92:4-97:5)
-/
@[step]
theorem new_spec (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max) :
    new auth_key ⦃ (result : v1.unchunked.send_ct.NoHeaderReceived) =>
      result.epoch = 1#u64 ∧
      result.auth.root_key.length = 32 ∧
      result.auth.mac_key.length = 32 ∧
      ∃ v, v.val = auth_key.val ∧
        authenticator.Authenticator.new v 1#u64 = ok result.auth ⦄ := by
  unfold new
  rw [WP.spec_equiv_exists]
  have h_tv := alloc.slice.Slice.to_vec_spec core.clone.CloneU8 auth_key
    (by intro x _; simp)
  obtain ⟨v, h_tv_eq, h_tv_post⟩ := WP.spec_imp_exists h_tv
  have h_v : v.length ≤ U32.max := by rw [← h_tv_post]; exact h_key
  obtain ⟨a, h_new_eq, h_rk, h_mk, _⟩ := WP.spec_imp_exists
    (authenticator.Authenticator.new_spec v 1#u64 h_v)
  exact ⟨⟨1#u64, a⟩, by simp [h_tv_eq, h_new_eq], rfl, h_rk, h_mk, v, by rw [h_tv_post], h_new_eq⟩

end spqr.v1.unchunked.send_ct.NoHeaderReceived
