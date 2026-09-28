/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Invariants.Defs
import Spqr.Specs.Chain.Chain.AddEpoch
/-!
# `Chain::add_epoch` preserves `ChainInv`

`chainInv_of_addEpochPost` shows that `ChainInv self` together with the structural conjuncts of
`add_epoch_spec`'s postcondition yields `ChainInv result`.  `add_epoch_spec_chainInv` packages
this as a spec theorem.  The hypothesis `h_epoch : epoch_secret.epoch = current_epoch + 1` is a
cross-component coupling with the v1 state machine and is *not* derivable from `ChainInv`; the
hypothesis `h_buf` is an artefact of the growing-list `VecDeque` model.

Source: "spqr/src/chain.rs"
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- The `add_epoch_spec` postcondition is inductive for `ChainInv`. -/
theorem chainInv_of_addEpochPost (self result : chain.Chain) (epoch_secret : EpochSecret)
    (h_epoch : epoch_secret.epoch.val = self.current_epoch.val + 1)
    (h_inv : ChainInv self)
    (hce : result.current_epoch = epoch_secret.epoch)
    (hse : result.send_epoch = self.send_epoch)
    (hnr : result.next_root.length = 32)
    (hln : result.links.length.val = self.links.length.val + 1)
    (hhd : result.links.head = self.links.head)
    (newEpoch : chain.ChainEpoch)
    (hbuf : result.links.buf.val = self.links.buf.val ++ [newEpoch])
    (h_new : newEpoch.send.prev.data.length = 0 ∧ newEpoch.send.next.length = 32 ∧
      newEpoch.recv.prev.data.length = 0 ∧ newEpoch.recv.next.length = 32) :
    ChainInv result := by
  obtain ⟨_, h_len1, h_se, h_diff, h_wf, h_slots⟩ := h_inv
  obtain ⟨hn2, hn3, hn5, hn6⟩ := h_new
  have hce' : result.current_epoch.val = self.current_epoch.val + 1 := by rw [hce, h_epoch]
  have hidx : sendIdx result = sendIdx self := by
    simp only [sendIdx, hce', hse, hln]; omega
  have hbl : result.links.buf.val.length = self.links.buf.val.length + 1 := by
    simp only [hbuf, List.length_append, List.length_singleton]
  refine ⟨hnr, by omega, by rw [hce', hse]; omega, by rw [hce', hse, hln]; omega,
    by rw [hhd, hln, hbl]; omega, ?_⟩
  intro j hj1 hj2 ce hcej
  simp only [hidx, hhd, hln] at *
  rw [hbuf] at hcej
  by_cases hj : j < self.links.buf.val.length
  · rw [List.getElem?_append_left hj] at hcej
    exact h_slots j hj1 (by omega) ce hcej
  · have hj' : j = self.links.buf.val.length := by
      have := List.getElem?_eq_some_iff.mp hcej
      simp only [List.length_append, List.length_singleton] at this
      omega
    subst hj'
    rw [List.getElem?_append_right (le_refl _)] at hcej
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hcej
    subst hcej
    exact ⟨⟨hn6, by rw [hn5], by rw [hn5]; omega⟩, by rw [hn2], by rw [hn2]; omega,
      fun _ => hn3⟩

/-- **Invariant-carrying spec for `spqr::chain::Chain::add_epoch`**. -/
theorem add_epoch_spec_chainInv (self : chain.Chain) (epoch_secret : EpochSecret)
    (h_epoch : epoch_secret.epoch.val = self.current_epoch.val + 1)
    (h_inv : ChainInv self)
    (h_buf : self.links.buf.val.length < Usize.max) :
    add_epoch self epoch_secret ⦃ (result : chain.Chain) =>
      ChainInv result ∧
      result.current_epoch = epoch_secret.epoch ∧
      result.send_epoch = self.send_epoch ∧
      result.params = self.params ⦄ := by
  have h_len : self.links.length.val ≤ self.links.buf.val.length := by
    have := h_inv.wf; omega
  apply WP.spec_mono (add_epoch_spec self epoch_secret h_epoch h_len h_buf)
  intro result h
  obtain ⟨_, hce, hse, hp, _, hnr, hln, hhd, hdir⟩ := h
  refine ⟨?_, hce, hse, hp⟩
  revert hdir
  cases self.dir with
  | A2B =>
    intro ⟨ne, hbuf, _, h2, _, h3, _, h5, _, h6⟩
    exact chainInv_of_addEpochPost self result epoch_secret h_epoch h_inv hce hse hnr hln hhd ne
      hbuf ⟨h2, h3, h5, h6⟩
  | B2A =>
    intro ⟨ne, hbuf, _, h2, _, h3, _, h5, _, h6⟩
    exact chainInv_of_addEpochPost self result epoch_secret h_epoch h_inv hce hse hnr hln hhd ne
      hbuf ⟨h2, h3, h5, h6⟩

end spqr.chain.Chain
