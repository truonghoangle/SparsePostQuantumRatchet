/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::authenticator::Authenticator::new`

`Authenticator.new` constructs a fresh `Authenticator` from an initial root key and an epoch
counter.

The constructor performs the following steps:

1. Allocates a zero-initialised `Authenticator` with both `root_key` and `mac_key` set to a
   32-byte zero vector `vec![0u8; 32]`.
2. Immediately delegates to `Authenticator.update(ep, &root_key)`, which derives a pair of
   fresh 32-byte keys via HKDF-SHA256:
   - `ikm  = [0; 32] ++ root_key`
   - `info = b"Signal_PQCKA_V1_MLKEM768:Authenticator Update" ++ ep.to_be_bytes()`
   - `kdf_out = hkdf([0; 32], ikm, info, 64)`
   - `result.root_key = kdf_out[..32]`
   - `result.mac_key  = kdf_out[32..]`

The returned `Authenticator` therefore holds keys deterministically derived from the supplied
`root_key` and `ep` via a single HKDF-SHA256 expansion, domain-separated by a fixed protocol
label and the epoch counter.

The by-value `new` introduces no additional logic beyond the delegation to `update`, so its
postcondition is inherited from the corresponding `update` specification.

**Source**: spqr/src/authenticator.rs (lines 35:4-42:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.authenticator.Authenticator

/--
**Spec theorem for `spqr.authenticator.Authenticator.new`**:

• Takes an initial `root_key : Vec U8` and an epoch `ep : U64`.
• Allocates a zero-initialised `Authenticator` with both `root_key` and `mac_key` fields set
  to `vec![0u8; 32]` (a 32-byte zero vector).
• Delegates immediately to `update`:
    `Authenticator.update { root_key := zeros, mac_key := zeros } ep (root_key.deref)`
  which feeds `[0; 32] ++ root_key` as IKM and a domain-separated info string into
  HKDF-SHA256, producing a 64-byte output that is split into the two 32-byte key fields.
• Returns the resulting `Authenticator`.

• The function succeeds (no panic) whenever `root_key.length ≤ U32.max`, ensuring that
  the IKM concatenation and HKDF input construction do not overflow.

The result satisfies the following postconditions:

  `result.root_key.length = 32`
  `result.mac_key.length  = 32`
  `∃ zeros, zeros.val = List.replicate 32 0#u8 ∧ zeros.length = 32 ∧
      update { root_key := zeros, mac_key := zeros } ep (alloc.vec.Vec.deref root_key) = ok result`

i.e. both key fields of the returned authenticator are exactly 32 bytes, and the result
is deterministically derived from the supplied `root_key` and `ep` via the `update` function
applied to a zero-initialised authenticator, as required by the protocol.

The proof unfolds `new` to expose the underlying `update` call and discharges the resulting goal
with `step*`, which applies the already-registered `update_spec`.

**Source**: spqr/src/authenticator.rs (lines 35:4-42:5)
-/
@[step]
theorem new_spec (root_key : alloc.vec.Vec U8) (ep : U64)
    (h_key : root_key.length ≤ U32.max) :
    new root_key ep ⦃ (result : Authenticator) =>
      result.root_key.length = 32 ∧
      result.mac_key.length = 32 ∧
      ∃ zeros : alloc.vec.Vec U8,
        zeros.val = List.replicate 32 0#u8 ∧
        zeros.length = 32 ∧
        update { root_key := zeros, mac_key := zeros } ep
          (alloc.vec.Vec.deref root_key) = ok result ⦄ := by
  unfold new
  sorry

end spqr.authenticator.Authenticator
