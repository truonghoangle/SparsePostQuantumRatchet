import Spqr.Specs.Chain.ChainEpochDirection.FromPb
import Spqr.Specs.Chain.ChainEpochDirection.Key
import Spqr.Specs.Chain.ChainParams.MaxOooKeysOrDefault

open Aeneas Aeneas.Std Result spqr chain.ChainEpochDirection

namespace Probe

private theorem bind_eq_ok_iff {α β : Type} (m : Result α) (f : α → Result β) (r : β) :
    (m >>= f) = ok r ↔ ∃ x, m = ok x ∧ f x = ok r := by
  cases m <;> simp [bind_tc_eq, bind_ok, bind_vis, bind_div, ok.injEq]

-- Probe 1: what does `key` unfold to / which cmp shape?
example (self : chain.ChainEpochDirection) (at1 : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_lt : at1.val < self.ctr.val)
    (h_bad : self.prev.data.length % 36 ≠ 0) :
    ∀ r, key self at1 params ≠ ok r := by
  intro r h
  unfold key at h
  simp only [lift, core.cmp.impls.OrdU32.cmp] at h
  rw [Nat.compare_eq_lt.mpr h_lt] at h
  sorry

-- Probe 2: trim_size overflow skeleton for D8
example (self : proto.pq_ratchet.ChainParams)
    (h_32bit : System.Platform.numBits = 32)
    (h_large : self.max_ooo_keys.val ≥ 390451573) :
    ∀ r, chain.ChainParams.trim_size self ≠ ok r := by
  intro r h
  unfold chain.ChainParams.trim_size chain.ChainParams.max_ooo_keys_or_default at h
  have h_pos : self.max_ooo_keys > 0#u32 := by scalar_tac
  simp only [h_pos, ite_true, bind_tc_ok, lift] at h
  sorry

end Probe
