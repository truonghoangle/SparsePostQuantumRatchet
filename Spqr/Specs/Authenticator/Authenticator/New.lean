/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.RatchetDefs
/-!
# Spec theorem for `spqr::authenticator::Authenticator::new`

`Authenticator.new` constructs a fresh `Authenticator` from an initial root key and an epoch
counter.

The constructor performs the following steps:

1. Allocates a zero-initialised `Authenticator` with both `root_key` and `mac_key` set to a
   32-byte zero vector `vec![0u8; 32]`.
2. Applies a single HKDF ratchet step from this zero state, computing:
   - `ikm  = ZERO_SALT ++ root_key`
   - `info = PROTOCOL_LABEL ++ ep.to_be_bytes()`
   - `kdf_out = HKDF-SHA256(salt = ZERO_SALT, ikm, info, L = 64)`
   - `result.root_key = kdf_out[0..32]`
   - `result.mac_key  = kdf_out[32..64]`

The returned `Authenticator` therefore holds keys deterministically derived from the supplied
`root_key` and `ep` via a single HKDF-SHA256 expansion, domain-separated by a fixed protocol
label (`PROTOCOL_LABEL`) and the epoch counter.

The postcondition is expressed via `initial_ratchet_step` from `Spqr/Specs/Lib/RatchetDefs.lean`,
which explicitly characterizes the HKDF computation rather than referencing the opaque
`Authenticator.update` function.

**Source**: spqr/src/authenticator.rs (lines 35:4-42:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.authenticator.Authenticator

/--
**Spec theorem for `spqr.authenticator.Authenticator.new`**:

• Takes an initial `root_key : Vec U8` and an epoch `ep : U64`.
• Allocates a zero-initialised `Authenticator` with both `root_key` and `mac_key` fields set
  to `vec![0u8; 32]` (a 32-byte zero vector, i.e. `ZERO_SALT`).
• Applies a single explicit HKDF ratchet step (`initial_ratchet_step`):
  - `ikm  = ZERO_SALT ++ root_key.val`
  - `info = PROTOCOL_LABEL ++ ep.to_be_bytes()`
  - `kdf_out = HKDF-SHA256(ZERO_SALT, ikm, info, 64)`
  - `result.root_key = kdf_out[0..32]`
  - `result.mac_key  = kdf_out[32..64]`
• Returns the resulting `Authenticator`.

• The function succeeds (no panic) whenever `root_key.length ≤ U32.max`, ensuring that
  the IKM concatenation and HKDF input construction do not overflow.

The result satisfies:

  `initial_ratchet_step root_key.val ep result`

which expands to:
  `result.root_key.length = 32 ∧ result.mac_key.length = 32 ∧
   ∃ zeros k, zeros.root_key.val = ZERO_SALT ∧ zeros.mac_key.val = ZERO_SALT ∧
     k.val = root_key.val ∧ ratchet_step_explicit zeros ep k result`

**Source**: spqr/src/authenticator.rs (lines 35:4-42:5)
-/
@[step]
theorem new_spec (root_key : alloc.vec.Vec U8) (ep : U64)
    (h_key : root_key.length ≤ U32.max) :
    new root_key ep ⦃ (result : Authenticator) =>
      initial_ratchet_step root_key.val ep result ⦄ := by
  unfold new
  sorry

end spqr.authenticator.Authenticator
