/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Invariants.Defs
import Spqr.Specs.Chain.Chain.New
/-!
# `Chain::new` establishes `ChainInv`

`chainInv_of_newPost` shows that the conjuncts of `new_spec`'s postcondition imply `ChainInv`;
`new_spec_chainInv` packages this into a spec theorem for `Chain.new`.

Source: "spqr/src/chain.rs"
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- The `new_spec` postcondition (structural conjuncts only) establishes `ChainInv`. -/
theorem chainInv_of_newPost (c : chain.Chain) (epoch : chain.ChainEpoch)
    (hce : c.current_epoch = 0#u64) (hse : c.send_epoch = 0#u64)
    (hnr : c.next_root.length = 32)
    (hln : c.links.length = 1#usize) (hhd : c.links.head = 0#usize)
    (hbuf : c.links.buf.val = [epoch])
    (h_ep : epoch.send.ctr = 0#u32 ∧ epoch.send.prev.data.length = 0 ∧
      epoch.send.next.length = 32 ∧ epoch.recv.ctr = 0#u32 ∧
      epoch.recv.prev.data.length = 0 ∧ epoch.recv.next.length = 32) :
    ChainInv c := by
  obtain ⟨_, h2, h3, _, h5, h6⟩ := h_ep
  refine ⟨hnr, by simp only [hln, UScalar.ofNatCore_val_eq, le_refl],
    by simp only [hce, hse, le_refl],
    by simp only [hce, hse, hln, UScalar.ofNatCore_val_eq, Nat.sub_self, Nat.lt_one_iff],
    by simp only [hhd, hln, hbuf, UScalar.ofNatCore_val_eq, List.length_singleton], ?_⟩
  intro j hj1 hj2 ce hj
  simp only [hhd, hln, UScalar.ofNatCore_val_eq] at hj1 hj2
  have : j = 0 := by omega
  subst this
  simp only [hbuf, List.getElem?_cons_zero, Option.some.injEq] at hj
  subst hj
  exact ⟨⟨h6, by rw [h5], by rw [h5]; omega⟩, by rw [h2], by rw [h2]; omega, fun _ => h3⟩

/-- **Invariant-carrying spec for `spqr::chain::Chain::new`**:
the freshly constructed chain satisfies `ChainInv`. -/
theorem new_spec_chainInv (initial_key : Slice U8) (dir : proto.pq_ratchet.Direction)
    (params : proto.pq_ratchet.ChainParams) :
    new initial_key dir params ⦃ (result : core.result.Result chain.Chain Error) =>
      match result with
      | .Ok chain => ChainInv chain
      | .Err _ => False ⦄ := by
  apply WP.spec_mono (new_spec initial_key dir params)
  intro result h
  match result with
  | .Err _ => exact h
  | .Ok c =>
    obtain ⟨_, hce, hse, _, _, hnr, hln, hhd, hrest⟩ := h
    revert hrest
    cases hbuf : c.links.buf.val with
    | nil => intro h; exact h.elim
    | cons epoch tl =>
      cases tl with
      | cons _ _ => intro h; exact h.elim
      | nil =>
        intro ⟨h1, h2, _, h3, h4, h5, _, h6⟩
        exact chainInv_of_newPost c epoch hce hse hnr hln hhd hbuf ⟨h1, h2, h3, h4, h5, h6⟩

end spqr.chain.Chain
