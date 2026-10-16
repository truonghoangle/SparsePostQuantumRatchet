/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Invariants.ChainEpochDirection.Key
import Spqr.Specs.Chain.Chain.RecvKey
/-!
# `Chain::recv_key` preserves `ChainInv`

`recvKeyPost_preserves_chainInv` shows that the postcondition predicate `recvKeyPost` of
`Chain.recv_key` is inductive for `ChainInv`, delegating the target slot to
`cedKeyPost_preserves_cedInv`.  `cedInv_recv_of_chainInv` shows that `ChainInv` discharges the
structural half of `recvKeyPre`; `recv_key_spec_chainInv` combines both with the arithmetic side
conditions into an invariant-carrying spec theorem.

Source: "spqr/src/chain.rs"
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- `recvKeyPost` is inductive for `ChainInv`. -/
theorem recvKeyPost_preserves_chainInv (self self' : chain.Chain) (epoch : U64) (index : U32)
    (result : core.result.Result (alloc.vec.Vec U8) Error)
    (h_inv : ChainInv self)
    (h_post : recvKeyPost self epoch index result self') :
    ChainInv self' := by
  obtain ⟨h_root, h_len1, h_se, h_diff, h_wf, h_slots⟩ := h_inv
  unfold recvKeyPost at h_post
  split at h_post
  · obtain ⟨_, rfl⟩ := h_post
    exact ⟨h_root, h_len1, h_se, h_diff, h_wf, h_slots⟩
  · rename_i h00
    obtain ⟨h_err, h_ok⟩ := h_post
    by_cases h_in : epoch.val ≤ self.current_epoch.val ∧
        self.current_epoch.val - epoch.val < self.links.length.val
    · obtain ⟨⟨_, hce, hse, hnr, _, hhd, hln, hbl, _, hoth⟩, hphys⟩ := h_ok h_in
      have hidx : sendIdx self' = sendIdx self := by
        simp only [sendIdx, hce, hse, hln]
      refine ⟨by rw [hnr]; exact h_root, by rw [hln]; exact h_len1,
        by rw [hce, hse]; exact h_se, by rw [hce, hse, hln]; exact h_diff,
        by rw [hhd, hln, hbl]; exact h_wf, ?_⟩
      intro j hj1 hj2 ce' hce'
      simp only [hhd, hln] at hj1 hj2
      rw [hidx, hhd]
      by_cases hj : j = self.links.head.val + recvKeyIdx self epoch
      · subst hj
        revert hphys
        cases h1 : self.links.buf.val[self.links.head.val + recvKeyIdx self epoch]? with
        | none => intro h; exact h.elim
        | some ce =>
          cases h2 : self'.links.buf.val[self.links.head.val + recvKeyIdx self epoch]? with
          | none => intro h; exact h.elim
          | some ce2 =>
            intro hep
            rw [hce'] at h2
            cases h2
            obtain ⟨hsend, hcedpost⟩ := hep
            obtain ⟨hr, hs1, hs2, hs3⟩ := h_slots _ hj1 hj2 ce h1
            exact ⟨ChainEpochDirection.cedKeyPost_preserves_cedInv _ _ _ _ _ hr hcedpost,
              by rw [hsend]; exact hs1, by rw [hsend]; exact hs2, by rw [hsend]; exact hs3⟩
      · rw [hoth j hj] at hce'
        exact h_slots j hj1 hj2 ce' hce'
    · have hout : epoch.val > self.current_epoch.val ∨
          self.current_epoch.val - epoch.val ≥ self.links.length.val := by omega
      obtain ⟨_, rfl⟩ := h_err hout
      exact ⟨h_root, h_len1, h_se, h_diff, h_wf, h_slots⟩

/-- `ChainInv` yields `CedInv` on the `recv` direction of the `recv_key` target slot. -/
theorem cedInv_recv_of_chainInv (self : chain.Chain) (epoch : U64)
    (h_inv : ChainInv self)
    (h_back : self.current_epoch.val - epoch.val < self.links.length.val) :
    match self.links.buf.val[self.links.head.val + recvKeyIdx self epoch]? with
    | none => True
    | some ce => CedInv ce.recv := by
  obtain ⟨_, _, _, _, _, h_slots⟩ := h_inv
  cases h : self.links.buf.val[self.links.head.val + recvKeyIdx self epoch]? with
  | none => trivial
  | some ce =>
    have hidx : recvKeyIdx self epoch < self.links.length.val := by
      simp only [recvKeyIdx]; omega
    exact (h_slots _ (by omega) (by omega) ce h).1

/-- **Invariant-carrying spec for `spqr::chain::Chain::recv_key`** (64-bit).

Under `ChainInv self`, `ParamsBound self.params index`, and the fuel bound `CedCtrBound` on the
target `recv` direction, the call satisfies `recvKeyPost` and preserves `ChainInv`. -/
theorem recv_key_spec_chainInv (self : chain.Chain) (epoch : U64) (index : U32)
    (h_inv : ChainInv self)
    (h_params : ParamsBound self.params index)
    (h_ctr : epoch.val ≤ self.current_epoch.val →
      self.current_epoch.val - epoch.val < self.links.length.val →
      match self.links.buf.val[self.links.head.val + recvKeyIdx self epoch]? with
      | none => True
      | some ce => CedCtrBound ce.recv)
    (h_64 : System.Platform.numBits = 64) :
    recv_key self epoch index ⦃ (result :
        (core.result.Result (alloc.vec.Vec U8) Error) × chain.Chain) =>
      recvKeyPost self epoch index result.1 result.2 ∧
      ChainInv result.2 ⦄ := by
  have h_diff_fits : epoch.val ≤ self.current_epoch.val →
      self.current_epoch.val - epoch.val ≤ Usize.max := by
    intro _
    rw [usize_max_eq_of_64 h_64]
    have : self.current_epoch.val < 2 ^ 64 := by scalar_tac
    omega
  have h_target : epoch.val ≤ self.current_epoch.val →
      self.current_epoch.val - epoch.val < self.links.length.val →
      match self.links.buf.val[self.links.head.val + recvKeyIdx self epoch]? with
      | none => True
      | some ce => recvKeyPre self.params index ce := by
    intro h_le h_back
    have h_struct := cedInv_recv_of_chainInv self epoch h_inv h_back
    have h_ctr' := h_ctr h_le h_back
    revert h_struct h_ctr'
    cases self.links.buf.val[self.links.head.val + recvKeyIdx self epoch]? with
    | none => intros; trivial
    | some ce =>
      intro h_struct h_ctr'
      exact recvKeyPre_of_cedInv self.params index ce h_struct h_ctr' h_params h_64
  apply WP.spec_mono (recv_key_spec self epoch index h_diff_fits h_inv.wf h_target)
  intro result h_post
  exact ⟨h_post, recvKeyPost_preserves_chainInv self result.2 epoch index result.1 h_inv h_post⟩

end spqr.chain.Chain
