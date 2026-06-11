/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Specs.Authenticator.JointDerivation

/-!
# Spec theorem for `spqr::authenticator::serialize::Authenticator::into_pb`

In SPQR's post-quantum ratchet, the `Authenticator` holds two 32-byte keys:
  • `root_key` — the chain root from which future keys are derived,
  • `mac_key`  — the key used to compute MACs on ciphertexts and headers.

The `into_pb` method serializes an `authenticator.Authenticator` into the corresponding protobuf
representation `proto.pq_ratchet.Authenticator`.  Both structures carry exactly the same two fields
(`root_key` and `mac_key`), so `into_pb` is a field-by-field move with no computation:
  ```rust
  pub fn into_pb(self) -> proto::pq_ratchet::Authenticator {
      proto::pq_ratchet::Authenticator {
          root_key: self.root_key,
          mac_key: self.mac_key,
      }
  }
  ```

The function is total (it never panics) and the resulting protobuf value preserves both keys
verbatim.

**Source**: spqr/src/authenticator/serialize.rs (lines 9:4-14:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.authenticator.serialize.Authenticator.into_pb

/-- **Spec theorem for `authenticator.serialize.Authenticator.into_pb`**:

The `into_pb` serializer converts an `authenticator.Authenticator` into the protobuf
representation `proto.pq_ratchet.Authenticator` by moving the `root_key` and `mac_key` fields
unchanged.

The postcondition captures the field-level round-trip identity:
  `result.root_key = self.root_key ∧ result.mac_key = self.mac_key`

The function is total — it always succeeds (wraps its output in `ok`) — because it performs a
pure structural copy with no allocation, cloning, or fallible operation.

This spec is a prerequisite for downstream serialization round-trip proofs (e.g., showing
`from_pb (into_pb auth) = auth` up to cloning) and is used as a `@[step]` lemma by higher-level
state-machine specs that serialise protocol states containing an `Authenticator`.

**Source**: spqr/src/authenticator/serialize.rs (lines 9:4-14:5)
-/
@[step]
theorem into_pb_spec (self : authenticator.Authenticator) :
    authenticator.serialize.Authenticator.into_pb self
      ⦃ (result : proto.pq_ratchet.Authenticator) =>
        result.root_key = self.root_key ∧ result.mac_key = self.mac_key ⦄ := by
  unfold authenticator.serialize.Authenticator.into_pb
  step*

/-- **`into_pb` preserves the joint-derivation invariant.**

If the input authenticator's `root_key` and `mac_key` satisfy
`jointly_derived`, then the output protobuf's `root_key` and `mac_key`
also satisfy `jointly_derived`. This follows directly from `into_pb_spec`
(which establishes field-level equality) and `jointly_derived_of_eq`. -/
@[step]
theorem into_pb_preserves_jointly_derived
    (self : authenticator.Authenticator)
    (h : authenticator.jointly_derived self.root_key self.mac_key) :
    authenticator.serialize.Authenticator.into_pb self
      ⦃ (result : proto.pq_ratchet.Authenticator) =>
        authenticator.jointly_derived result.root_key result.mac_key ⦄ := by
  apply WP.spec_mono (into_pb_spec self)
  intro result hres
  exact authenticator.jointly_derived_of_eq h hres.1 hres.2

end spqr.authenticator.serialize.Authenticator.into_pb
