/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Invariants.Defs
import Spqr.Specs.Chain.ChainEpochDirection.Key
/-!
# `ChainEpochDirection::key` preserves `CedInv`

`cedKeyPost_preserves_cedInv` shows that the postcondition predicate `cedKeyPost` of
`ChainEpochDirection.key` maps `CedInv` to itself on all four control paths (equal, less,
jump-too-far, advance).  `key_spec_cedInv` re-packages `key_spec` so that its structural
hypotheses are replaced by `CedInv` and its arithmetic hypotheses by `CedCtrBound`/`ParamsBound`,
and its postcondition additionally asserts `CedInv` of the result.

Source: "spqr/src/chain.rs"
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainEpochDirection

/-- `cedKeyPost` is inductive for `CedInv`. -/
theorem cedKeyPost_preserves_cedInv
    (self self' : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (result : core.result.Result (alloc.vec.Vec U8) Error)
    (h_inv : CedInv self)
    (h_post : cedKeyPost self ats params result self') :
    CedInv self' := by
  obtain ⟨h_next, h_al, h_ctr⟩ := h_inv
  obtain ⟨h_eq, h_lt, h_jump, h_adv⟩ := h_post
  rcases lt_trichotomy ats self.ctr with h | h | h
  · obtain ⟨hc, hn, hres⟩ := h_lt h
    refine ⟨by rw [hn]; exact h_next, ?_, ?_⟩
    · split at hres
      · rcases hres with ⟨_, _, hp⟩ | ⟨_, _, hp, _⟩ <;> rw [hp] <;> exact h_al
      · exact hres.2.2.2.1
    · split at hres
      · rcases hres with ⟨_, _, hp⟩ | ⟨_, _, hp, _⟩ <;> rw [hp, hc] <;> exact h_ctr
      · rw [hres.2.2.1, hc]; omega
  · obtain ⟨_, rfl⟩ := h_eq h
    exact ⟨h_next, h_al, h_ctr⟩
  · by_cases hj : ats.val - self.ctr.val ≤ (chain.maxJump params).val
    · have hp := h_adv h hj
      simp only [cedKeyAdvancePost] at hp
      obtain ⟨_, hctr', hnext', _, hal', _, hle, _⟩ := hp
      refine ⟨hnext', hal', ?_⟩
      have : self'.ctr.val = ats.val := by rw [hctr']
      rw [this]
      have hlt : self.ctr.val < ats.val := (UScalar.lt_equiv _ _).mp h
      omega
    · obtain ⟨_, rfl⟩ := h_jump h (by omega)
      exact ⟨h_next, h_al, h_ctr⟩

/-- **Invariant-carrying spec for `spqr::chain::ChainEpochDirection::key`** (64-bit).

Under `CedInv self`, the fuel bound `CedCtrBound self` and `ParamsBound params ats`, the call
satisfies `cedKeyPost` and the resulting direction again satisfies `CedInv`. -/
theorem key_spec_cedInv (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_inv : CedInv self) (h_ctr : CedCtrBound self) (h_params : ParamsBound params ats)
    (h_platform : System.Platform.numBits = 64) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      cedKeyPost self ats params result.1 result.2 ∧
      CedInv result.2 ⦄ := by
  have h_pre : recvKeyPre params ats { send := self, recv := self } :=
    recvKeyPre_of_cedInv params ats _ h_inv h_ctr h_params h_platform
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := h_pre
  have h_spec := key_spec self ats params h1 h2 h3 h4 h5 h6 h7 (by scalar_tac) h8 h9 h_platform
  apply WP.spec_mono h_spec
  intro result h_post
  exact ⟨h_post, cedKeyPost_preserves_cedInv self result.2 ats params result.1 h_inv h_post⟩

end spqr.chain.ChainEpochDirection
