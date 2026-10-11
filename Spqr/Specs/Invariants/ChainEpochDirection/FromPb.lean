/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Invariants.Defs
import Spqr.Specs.Chain.ChainEpochDirection.FromPb
import Spqr.Specs.Chain.ChainEpochDirection.IntoPb
/-!
# `ChainEpochDirection::{from_pb, into_pb}` and `CedInv`: the persistence boundary

`from_pb` copies its protobuf fields verbatim and never fails, so it establishes `CedInv` **iff**
the blob already satisfies the corresponding byte-level predicate `PbCedInv`.  In particular:

* `cedInv_from_pb_iff` — the exact characterisation;
* `from_pb_not_cedInv` — for every blob violating `PbCedInv`, the loaded direction violates
  `CedInv`, i.e. the inductive argument of `Spqr.Specs.Invariants.Chain.Composition` does *not*
  restart after a reload;
* `into_pb_preserves_pbCedInv` / `into_pb_not_pbCedInv` — `into_pb` is likewise verbatim, so a
  violation persists across the save/load round trip.

Source: "spqr/src/chain.rs"
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainEpochDirection

/-- Byte-level image of `CedInv` on the protobuf message. -/
def PbCedInv (pb : proto.pq_ratchet.chain.epoch.EpochDirection) : Prop :=
  pb.next.length = 32 ∧ pb.prev.length % 36 = 0 ∧ pb.prev.length ≤ 36 * pb.ctr.val

/-- `from_pb` yields `CedInv` exactly when the blob satisfies `PbCedInv`. -/
theorem cedInv_from_pb_iff (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection Error) =>
      match result with
      | core.result.Result.Ok ced => (CedInv ced ↔ PbCedInv pb)
      | core.result.Result.Err _ => False ⦄ := by
  apply WP.spec_mono (from_pb_spec pb)
  intro result
  match result with
  | core.result.Result.Err _ =>
    intro h; simp [FunctionalModels.fromPb] at h
  | core.result.Result.Ok ced =>
    intro h
    have heq : ced = { ctr := pb.ctr, next := pb.next, prev := { data := pb.prev } } := by
      simp [FunctionalModels.fromPb] at h; exact h
    subst heq
    simp only [CedInv, PbCedInv]

/-- **Non-preservation**: a blob violating `PbCedInv` loads (with `Ok`) into a direction violating
`CedInv`.  No hypothesis of any `key`/`next_key` spec is then satisfiable. -/
theorem from_pb_not_cedInv (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_bad : ¬ PbCedInv pb) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection Error) =>
      match result with
      | core.result.Result.Ok ced => ¬ CedInv ced
      | core.result.Result.Err _ => False ⦄ := by
  apply WP.spec_mono (cedInv_from_pb_iff pb)
  intro result
  match result with
  | core.result.Result.Err _ => intro h; exact h
  | core.result.Result.Ok ced =>
    intro h_iff
    exact fun h => h_bad (h_iff.mp h)

/-- `into_pb` maps `CedInv` to `PbCedInv`. -/
theorem into_pb_preserves_pbCedInv (self : chain.ChainEpochDirection) (h_inv : CedInv self) :
    into_pb self ⦃ (pb : proto.pq_ratchet.chain.epoch.EpochDirection) => PbCedInv pb ⦄ := by
  apply WP.spec_mono (into_pb_spec self)
  intro pb h
  subst h
  simp only [FunctionalModels.intoPb, PbCedInv]
  exact h_inv

/-- **Persistence of the violation**: `into_pb` maps `¬ CedInv` to `¬ PbCedInv`, so a corrupted
direction is re-emitted corrupted (cf. `corrupted_state_roundtrips` in
`Spqr.Specs.Bugs.CorruptedBlobs`). -/
theorem into_pb_not_pbCedInv (self : chain.ChainEpochDirection) (h_bad : ¬ CedInv self) :
    into_pb self ⦃ (pb : proto.pq_ratchet.chain.epoch.EpochDirection) => ¬ PbCedInv pb ⦄ := by
  apply WP.spec_mono (into_pb_spec self)
  intro pb h
  subst h
  simp only [FunctionalModels.intoPb, PbCedInv]
  exact h_bad

end spqr.chain.ChainEpochDirection
