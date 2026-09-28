/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Invariants.Defs
import Spqr.Specs.Chain.Chain.SendKey
/-!
# `Chain::send_key` preserves `ChainInv`

`sendKeyPost_preserves_chainInv` is the only non-trivial preservation result: when the send epoch
moves, `send_key` pops the front of the deque (shifting `head`) and clears `send.next` of the
surviving earlier slots.  The postcondition `sendKeyDequePost` records the exact cleared window
via `clearedAt` and the new logical send index `sendKeyEi`, which is what allows the
`hs ≤ j → send.next.length = 32` conjunct of `SlotInv` to be re-established.

`sendNext_of_chainInv` shows `ChainInv` discharges the structural half of `h_target`;
`send_key_spec_chainInv` packages everything as an invariant-carrying spec theorem.

Source: "spqr/src/chain.rs"
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- `sendKeyPost` is inductive for `ChainInv`. -/
theorem sendKeyPost_preserves_chainInv (self self' : chain.Chain) (epoch : U64)
    (result : core.result.Result (U32 × alloc.vec.Vec U8) Error)
    (h_inv : ChainInv self)
    (h_post : sendKeyPost self epoch result self') :
    ChainInv self' := by
  obtain ⟨h_root, h_len1, h_se, h_diff, h_wf, h_slots⟩ := h_inv
  obtain ⟨h_dec, h_oor, h_ok⟩ := h_post
  by_cases h_lt : epoch.val < self.send_epoch.val
  · obtain ⟨_, rfl⟩ := h_dec h_lt
    exact ⟨h_root, h_len1, h_se, h_diff, h_wf, h_slots⟩
  · have h_ge : self.send_epoch.val ≤ epoch.val := by omega
    by_cases h_in : epoch.val ≤ self.current_epoch.val ∧
        self.current_epoch.val - epoch.val < self.links.length.val
    · obtain ⟨_, hce, hse, hnr, _, ⟨hhd, hln, hbl, _, _, hsame, hmoved, hout⟩, hslot⟩ :=
        h_ok h_ge h_in.1 h_in.2
      have hidx_val : sendKeyIdx self epoch =
          self.links.length.val - 1 - (self.current_epoch.val - epoch.val) := rfl
      have hei_le : sendKeyEi self epoch ≤ sendKeyIdx self epoch := by
        simp only [sendKeyEi]; split
        · exact le_refl _
        · exact Nat.min_le_left _ _
      have hsi_old : sendIdx self ≤ sendKeyIdx self epoch := by
        simp only [sendIdx, hidx_val]; omega
      have hsi_new : sendIdx self' = sendKeyEi self epoch := by
        simp only [sendIdx, hce, hse, hln]; omega
      refine ⟨by rw [hnr]; exact h_root, by omega, by rw [hce, hse]; exact h_in.1,
        by rw [hce, hse, hln]; omega, by rw [hhd, hln, hbl]; omega, ?_⟩
      intro j hj1 hj2 ce' hce'
      rw [hsi_new, hhd]
      rw [hhd] at hj1
      rw [hhd, hln] at hj2
      have hj1o : self.links.head.val ≤ j := by omega
      have hj2o : j < self.links.head.val + self.links.length.val := by omega
      rcases lt_trichotomy j (self.links.head.val + sendKeyIdx self epoch) with hjlt | hjeq | hjgt
      · by_cases hmv : self.send_epoch = self'.send_epoch
        · obtain ⟨_, _, hoth⟩ := hsame hmv
          rw [hoth j (by omega)] at hce'
          obtain ⟨hr, hs1, hs2, _⟩ := h_slots j hj1o hj2o ce' hce'
          refine ⟨hr, hs1, hs2, fun h => ?_⟩
          have : sendKeyEi self epoch = sendKeyIdx self epoch := by
            have : self.send_epoch = epoch := by rw [hmv, hse]
            simp only [sendKeyEi, if_pos this]
          omega
        · obtain ⟨ce0, _, h0, h0', hr, _, hctr, hprev⟩ := hmoved hmv j hj1 hjlt
          rw [hce'] at h0'; cases h0'
          obtain ⟨hr0, hs1, hs2, _⟩ := h_slots j hj1o hj2o ce0 h0
          refine ⟨by rw [hr]; exact hr0, by rw [hprev]; exact hs1,
            by rw [hprev, hctr]; exact hs2, fun h => absurd h (by omega)⟩
      · subst hjeq
        revert hslot
        cases h1 : self.links.buf.val[self.links.head.val + sendKeyIdx self epoch]? with
        | none => intro h; exact h.elim
        | some ce =>
          cases h2 : self'.links.buf.val[self.links.head.val + sendKeyIdx self epoch]? with
          | none => intro h; exact h.elim
          | some ce2 =>
            rintro ⟨i, _, _, hi, _, _, hrecv, hctr, hnl, _, hprev⟩
            rw [hce'] at h2; cases h2
            obtain ⟨hr, hs1, hs2, hs3⟩ := h_slots _ hj1o hj2o ce h1
            refine ⟨by rw [hrecv]; exact hr, by rw [hprev]; exact hs1, ?_, fun _ => ?_⟩
            · rw [hprev, hctr, hi]; omega
            · rw [hnl]; exact hs3 (by omega)
      · rw [hout j (Or.inr hjgt)] at hce'
        obtain ⟨hr, hs1, hs2, hs3⟩ := h_slots j hj1o hj2o ce' hce'
        exact ⟨hr, hs1, hs2, fun _ => hs3 (by omega)⟩
    · have hout : epoch.val > self.current_epoch.val ∨
          self.current_epoch.val - epoch.val ≥ self.links.length.val := by omega
      obtain ⟨_, rfl⟩ := h_oor h_ge hout
      exact ⟨h_root, h_len1, h_se, h_diff, h_wf, h_slots⟩

/-- `ChainInv` yields `send.next.length = 32` on the `send_key` target slot whenever
`send_epoch ≤ epoch ≤ current_epoch` and the epoch is still in the deque. -/
theorem sendNext_of_chainInv (self : chain.Chain) (epoch : U64)
    (h_inv : ChainInv self)
    (h_ge : self.send_epoch.val ≤ epoch.val) (h_le : epoch.val ≤ self.current_epoch.val)
    (h_back : self.current_epoch.val - epoch.val < self.links.length.val) :
    match self.links.buf.val[self.links.head.val + sendKeyIdx self epoch]? with
    | none => True
    | some ce => ce.send.next.length = 32 := by
  obtain ⟨_, _, _, _, _, h_slots⟩ := h_inv
  cases h : self.links.buf.val[self.links.head.val + sendKeyIdx self epoch]? with
  | none => trivial
  | some ce =>
    have hidx : sendKeyIdx self epoch < self.links.length.val := by
      simp only [sendKeyIdx]; omega
    have hsi : sendIdx self ≤ sendKeyIdx self epoch := by
      simp only [sendIdx, sendKeyIdx]; omega
    exact (h_slots _ (by omega) (by omega) ce h).2.2.2 (by omega)

/-- **Invariant-carrying spec for `spqr::chain::Chain::send_key`** (64-bit).

Under `ChainInv self` and the fuel bound `send.ctr < u32::MAX` on the target slot, the call
satisfies `sendKeyPost` and preserves `ChainInv`. -/
theorem send_key_spec_chainInv (self : chain.Chain) (epoch : U64)
    (h_inv : ChainInv self)
    (h_ctr : self.send_epoch.val ≤ epoch.val → epoch.val ≤ self.current_epoch.val →
      self.current_epoch.val - epoch.val < self.links.length.val →
      match self.links.buf.val[self.links.head.val + sendKeyIdx self epoch]? with
      | none => True
      | some ce => ce.send.ctr < U32.max)
    (h_64 : System.Platform.numBits = 64) :
    send_key self epoch ⦃ (result : (core.result.Result (U32 × alloc.vec.Vec U8) Error) ×
        chain.Chain) =>
      sendKeyPost self epoch result.1 result.2 ∧
      ChainInv result.2 ⦄ := by
  have h_diff_fits : self.send_epoch ≤ epoch.val → epoch.val ≤ self.current_epoch →
      self.current_epoch - epoch ≤ Usize.max := by
    intro _ _
    rw [usize_max_eq_of_64 h_64]
    have : self.current_epoch.val < 2 ^ 64 := by scalar_tac
    scalar_tac
  have h_target : self.send_epoch ≤ epoch → epoch ≤ self.current_epoch →
      self.current_epoch - epoch < self.links.length.val →
      match self.links.buf.val[self.links.head + sendKeyIdx self epoch]? with
      | none => True
      | some ce => ce.send.next.length = 32 ∧ ce.send.ctr < U32.max := by
    intro h_ge h_le h_back
    have h_ge' : self.send_epoch.val ≤ epoch.val := by scalar_tac
    have h_le' : epoch.val ≤ self.current_epoch.val := by scalar_tac
    have h_back' : self.current_epoch.val - epoch.val < self.links.length.val := by scalar_tac
    have h_next := sendNext_of_chainInv self epoch h_inv h_ge' h_le' h_back'
    have h_ctr' := h_ctr h_ge' h_le' h_back'
    revert h_next h_ctr'
    cases self.links.buf.val[self.links.head.val + sendKeyIdx self epoch]? with
    | none => intros; trivial
    | some ce => intro h_next h_ctr'; exact ⟨h_next, h_ctr'⟩
  apply WP.spec_mono (send_key_spec self epoch h_diff_fits h_inv.wf h_target)
  intro result h_post
  exact ⟨h_post, sendKeyPost_preserves_chainInv self result.2 epoch result.1 h_inv h_post⟩

end spqr.chain.Chain
