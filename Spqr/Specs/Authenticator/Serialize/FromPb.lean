/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::authenticator::serialize::Authenticator::from_pb`

In SPQR's post-quantum ratchet, the `Authenticator` holds two 32-byte keys:
  • `root_key` — the chain root from which future keys are derived,
  • `mac_key`  — the key used to compute MACs on ciphertexts and headers.

The `from_pb` method deserializes a protobuf `proto.pq_ratchet.Authenticator` back into the
internal `authenticator.Authenticator` representation.  Both structures carry exactly the same two
fields (`root_key` and `mac_key`), so `from_pb` is a field-by-field clone with no computation:
  ```rust
  pub fn from_pb(pb: &proto::pq_ratchet::Authenticator) -> Self {
      Self {
          root_key: pb.root_key.clone(),
          mac_key: pb.mac_key.clone(),
      }
  }
  ```

The function is total (it never panics) and the resulting authenticator value preserves both keys
verbatim.

**Source**: spqr/src/authenticator/serialize.rs (lines 16:4-21:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.authenticator.serialize.Authenticator.from_pb

/--
Helper lemma: `alloc.vec.CloneVec.clone` specialised to `U8` always succeeds and returns the
vector unchanged, because `core.clone.CloneU8.clone x = ok x` for every `x : U8`.
-/
@[step]
private theorem clone_U8_spec (v : alloc.vec.Vec Std.U8) :
    alloc.vec.CloneVec.clone core.clone.CloneU8 v
      ⦃ (r : alloc.vec.Vec Std.U8) => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  apply WP.spec_mono
    (Slice.clone_spec (fun x _ => by rfl))
  intro v' h
  exact h.symm

/-- **Spec theorem for `authenticator.serialize.Authenticator.from_pb`**:

The `from_pb` deserializer converts a protobuf `proto.pq_ratchet.Authenticator` into the internal
`authenticator.Authenticator` representation by cloning the `root_key` and `mac_key` fields
unchanged.

The postcondition captures the field-level identity:
  `result.root_key = pb.root_key ∧ result.mac_key = pb.mac_key`

The function is total — it always succeeds (wraps its output in `ok`) — because it performs a
pure structural clone with no allocation failure, parsing, or fallible operation.

This spec is a prerequisite for downstream serialization round-trip proofs (e.g., showing
`from_pb (into_pb auth) = auth` up to cloning) and is used as a `@[step]` lemma by higher-level
state-machine specs that deserialise protocol states containing an `Authenticator`.

**Source**: spqr/src/authenticator/serialize.rs (lines 16:4-21:5)
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.Authenticator) :
    authenticator.serialize.Authenticator.from_pb pb
      ⦃ (result : authenticator.Authenticator) =>
        result.root_key = pb.root_key ∧ result.mac_key = pb.mac_key ⦄ := by
  unfold authenticator.serialize.Authenticator.from_pb
  step*

end spqr.authenticator.serialize.Authenticator.from_pb
