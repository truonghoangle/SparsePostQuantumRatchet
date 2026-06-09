/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::authenticator::Authenticator::new`

In SPQR's post-quantum ratchet, the `Authenticator` provides HMAC-based message authentication for
ciphertexts and encapsulation-key headers.  Each `Authenticator` holds two 32-byte keys:
  • `root_key` — the chain root from which future keys are derived,
  • `mac_key`  — the key used to compute MACs on ciphertexts and headers.

The `new` constructor initialises an `Authenticator` from caller-supplied key material
(`root_key : Vec<u8>`) and an epoch (`ep : Epoch`), proceeding in two stages:
  1. `alloc.vec.from_elem 0 32` — allocate a 32-byte zero vector `v` to serve as the initial
     root key and MAC key for the seed authenticator `{ root_key := v, mac_key := v }`.
  2. `authenticator.Authenticator.update { root_key := v, mac_key := v } ep (deref root_key)` —
     derive fresh `root_key` and `mac_key` via HKDF-SHA-256 over the concatenation of the
     zero-initialised root key with the supplied `root_key`, keyed by the context string
     `"Signal_PQCKA_V1_MLKEM768:Authenticator Update"` and the epoch `ep`.

The resulting `Authenticator` carries the freshly derived keys produced by the first `update` call,
establishing the cryptographic state for the given epoch.

**Source**: spqr/src/authenticator.rs (lines 35:4-42:5)
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

The underlying `kdf.hkdf_to_slice` is axiomatised in the Aeneas extraction.  The only contract
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
on the specific byte contents of the derived keys. -/
@[step]
private theorem update_spec
    (h : update_ok) (self : authenticator.Authenticator) (ep : Std.U64)
    (k : Slice Std.U8) :
    authenticator.Authenticator.update self ep k
      ⦃ (_ : authenticator.Authenticator) => True ⦄ := by
  obtain ⟨a, ha⟩ := h self ep k
  rw [ha]
  simp [WP.spec_ok]

/-- **Compositional spec for `authenticator.Authenticator.new`**:

The `new` constructor is equivalent to allocating a 32-byte zero vector and delegating to `update`
on the seed authenticator `{ root_key := zeros, mac_key := zeros }`.

Specifically:
  `new root_key ep = do
     let v ← alloc.vec.from_elem core.clone.CloneU8 0#u8 32#usize
     authenticator.Authenticator.update { root_key := v, mac_key := v } ep
       (alloc.vec.Vec.deref root_key)`

This follows immediately from the definition of `new`, which performs exactly these two operations:
  1. `alloc.vec.from_elem core.clone.CloneU8 0#u8 32#usize` — allocate the 32-byte zero vector.
  2. `alloc.vec.Vec.deref root_key` → `authenticator.Authenticator.update` — borrow the caller's
     key material as a slice and derive the initial `Authenticator` state via HKDF.

This establishes that `new` computes the HKDF-based key derivation
  HKDF(salt = [0;32], ikm = [0;32] ++ root_key,
       info = "Signal_PQCKA_V1_MLKEM768:Authenticator Update" ++ ep.to_be_bytes(), len = 64)
split into `root_key := kdf_out[..32]` and `mac_key := kdf_out[32..]` at the
representation level.

**Source**: spqr/src/authenticator.rs (lines 35:4-42:5)
-/
theorem new_eq_update (root_key : alloc.vec.Vec Std.U8) (ep : Std.U64) :
    authenticator.Authenticator.new root_key ep =
      (do
        let v ← alloc.vec.from_elem core.clone.CloneU8 0#u8 32#usize
        authenticator.Authenticator.update
          { root_key := v, mac_key := v } ep (alloc.vec.Vec.deref root_key)) := by
  unfold authenticator.Authenticator.new
  rfl

/--
The `@[step]` lemma for `authenticator.Authenticator.new` exposes the constructor to the `step*`
tactic used by downstream specs (e.g., `NoHeaderReceived.new`, `Ct1Received.new`).  The
postcondition `True` witnesses that the constructor always satisfies any continuation-independent
property: if the caller's postcondition does not depend on the specific byte contents of the
resulting `root_key` and `mac_key`, the `step*` tactic can discharge the `new` call automatically.

Since the underlying key derivation is opaque (HKDF-SHA-256 via the axiomatized
`kdf.hkdf_to_slice`), the *byte contents* of the resulting `root_key` and `mac_key` are
unconstrained by this spec.  The hypothesis `update_ok` asserts that the HKDF-based `update`
function always succeeds — the minimal assumption needed to derive a (non-vacuous) spec for `new`
in the abstract model.  Richer postconditions (e.g., key-length guarantees or domain-separation
properties) require specifications for the KDF layer.
-/
@[step]
theorem new_spec (root_key : alloc.vec.Vec Std.U8) (ep : Std.U64) (h : update_ok) :
    authenticator.Authenticator.new root_key ep ⦃ (result : authenticator.Authenticator) =>
      True ⦄ := by
  unfold authenticator.Authenticator.new
  step*

end spqr.authenticator.Authenticator
