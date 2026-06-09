/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::authenticator::Authenticator::update`

In SPQR's post-quantum ratchet, the `Authenticator` provides HMAC-based message authentication for
ciphertexts and encapsulation-key headers.  The `update` method derives fresh cryptographic keys
from the current state and caller-supplied key material via HKDF-SHA-256.

The function proceeds in three stages:
  1. **IKM construction** — concatenate `self.root_key` with the caller-supplied key material `k`
     to form the HKDF input keying material.
  2. **Info construction** — concatenate the domain-separation string
     `"Signal_PQCKA_V1_MLKEM768:Authenticator Update"` with the big-endian encoding of the
     epoch `ep` to form the HKDF info parameter.
  3. **Key derivation** — invoke `kdf.hkdf_to_vec` with a 32-byte zero salt, the constructed IKM,
     the constructed info, and output length 64 to derive 64 bytes.  The first 32 bytes become the
     new `root_key` and the last 32 bytes become the new `mac_key`.

The result is a fresh `Authenticator` carrying the derived keys, establishing the cryptographic
state for the given epoch.

**Source**: spqr/src/authenticator.rs (lines 44:4-54:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.authenticator.Authenticator

/-- **Functional contract for `authenticator.Authenticator.update`**.

In the Rust implementation, `update` performs HKDF-SHA-256 key derivation:
  1. Concatenate `self.root_key` with the caller-supplied key material `k`.
  2. Concatenate the context string `"Signal_PQCKA_V1_MLKEM768:Authenticator Update"` with the
     big-endian encoding of the epoch `ep`.
  3. Derive 64 bytes via HKDF with a zero salt, splitting into `root_key := kdf_out[..32]` and
     `mac_key := kdf_out[32..]`.

The underlying `kdf.hkdf_to_vec` is axiomatised in the Aeneas extraction.  The only contract
`update` is supposed to satisfy is that it never panics (it merely performs a deterministic key
derivation).  We capture this here as a *definition* of the proposition that every concrete call
returns `ok a` for some resulting `Authenticator`.

Downstream specs take an instance of this proposition as a hypothesis rather than relying on an
axiom. -/
def update_ok : Prop :=
  ∀ (self : authenticator.Authenticator) (ep : Std.U64) (k : Slice Std.U8),
    ∃ a, authenticator.Authenticator.update self ep k = ok a

/-- **Step-style spec lemma for `authenticator.Authenticator.update`**.

Lifts the `update_ok` hypothesis into the `step` / `step*` machinery: under the assumption that
every call to `update` succeeds, we expose no information about the output beyond its mere
existence (`True`).  This is sufficient for downstream specs whose postconditions do not depend
on the specific byte contents of the derived keys.

The proof extracts the witness `a` from the `update_ok` hypothesis applied to the given arguments,
rewrites the goal to the `ok` case, and closes via `simp [WP.spec_ok]`.

**Source**: spqr/src/authenticator.rs (lines 44:4-54:5)
-/
@[step]
theorem update_spec
    (h : update_ok) (self : authenticator.Authenticator) (ep : Std.U64)
    (k : Slice Std.U8) :
    authenticator.Authenticator.update self ep k
      ⦃ (_ : authenticator.Authenticator) => True ⦄ := by
  obtain ⟨a, ha⟩ := h self ep k
  rw [ha]
  simp [WP.spec_ok]

end spqr.authenticator.Authenticator
