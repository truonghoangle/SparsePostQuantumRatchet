/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Chain.Chain.Defs
/-!
# Global state invariants for `spqr::chain`

Defines the structural invariants that the Rust code in `spqr/src/chain.rs` relies on but never
states as a single predicate, together with the arithmetic side conditions that the individual
spec theorems require and that are *not* state invariants (see `docs/invariantsSPQR.md`).

* `CedInv` — per-direction invariant: `next.len = 32`, `prev.len % 36 = 0`,
  `prev.len ≤ 36·ctr`.
* `SlotInv` — per-epoch invariant; the send secret is only required to be present at or after
  the send epoch (it is cleared by `send_key` for earlier epochs).
* `ChainInv` — the global chain invariant: `next_root.len = 32`, at least one epoch,
  `send_epoch ≤ current_epoch < send_epoch + links.len`, deque well-formedness, and `SlotInv` on
  every logical slot.
* `CedCtrBound`, `ParamsBound` — fuel/configuration bounds (`hax_lib::assume!` in the source).

Source: "spqr/src/chain.rs"
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain

/-- Per-direction structural invariant of `ChainEpochDirection`. -/
def CedInv (ced : chain.ChainEpochDirection) : Prop :=
  ced.next.length = 32 ∧
  ced.prev.data.length % 36 = 0 ∧
  ced.prev.data.length ≤ 36 * ced.ctr.val

/-- Logical deque index of the send epoch: `links.len - 1 - (current_epoch - send_epoch)`. -/
def sendIdx (c : chain.Chain) : Nat :=
  c.links.length.val - 1 - (c.current_epoch.val - c.send_epoch.val)

/-- Per-slot invariant for the `ChainEpoch` at *physical* index `j`, where `hs` is the physical
index of the send epoch.  The `recv` direction always satisfies `CedInv`; the `send` direction
satisfies the history conjuncts unconditionally and the `next.len = 32` conjunct only for slots at
or after the send epoch. -/
def SlotInv (hs j : Nat) (ce : chain.ChainEpoch) : Prop :=
  CedInv ce.recv ∧
  ce.send.prev.data.length % 36 = 0 ∧
  ce.send.prev.data.length ≤ 36 * ce.send.ctr.val ∧
  (hs ≤ j → ce.send.next.length = 32)

/-- Global invariant of `Chain`. -/
def ChainInv (c : chain.Chain) : Prop :=
  c.next_root.length = 32 ∧
  1 ≤ c.links.length.val ∧
  c.send_epoch.val ≤ c.current_epoch.val ∧
  c.current_epoch.val - c.send_epoch.val < c.links.length.val ∧
  c.links.head.val + c.links.length.val = c.links.buf.val.length ∧
  (∀ j, c.links.head.val ≤ j → j < c.links.head.val + c.links.length.val →
    ∀ ce, c.links.buf.val[j]? = some ce → SlotInv (c.links.head.val + sendIdx c) j ce)

/-- Fuel bound on a direction counter (`hax_lib::assume!(self.ctr <= u32::MAX - 390451572)`).
Not a state invariant: a peer can advance `ctr` past it. -/
def CedCtrBound (ced : chain.ChainEpochDirection) : Prop :=
  ced.ctr.val ≤ U32.max - 390451572

/-- Configuration/request bounds required by `ChainEpochDirection.key` (64-bit variant). -/
def ParamsBound (params : proto.pq_ratchet.ChainParams) (index : U32) : Prop :=
  index.val ≤ U32.max - 390451572 ∧
  (chain.maxOoo params).val < 390451572 ∧
  index.val + (chain.maxOoo params).val ≤ U32.max

/-- `ChainInv` implies the deque well-formedness hypothesis `h_wf` used by the chain specs. -/
theorem ChainInv.wf {c : chain.Chain} (h : ChainInv c) :
    c.links.head.val + c.links.length.val ≤ c.links.buf.val.length :=
  le_of_eq h.2.2.2.2.1

/-- On a 64-bit platform, `Usize.max = 2 ^ 64 - 1`. -/
theorem usize_max_eq_of_64 (h : System.Platform.numBits = 64) : Usize.max = 2 ^ 64 - 1 := by
  have := Usize.max_succ_eq_pow; rw [h] at this; omega

/-- The structural invariant together with the arithmetic bounds discharges `recvKeyPre`. -/
theorem recvKeyPre_of_cedInv (params : proto.pq_ratchet.ChainParams) (index : U32)
    (ce : chain.ChainEpoch)
    (h_inv : CedInv ce.recv) (h_ctr : CedCtrBound ce.recv) (h_params : ParamsBound params index)
    (h_64 : System.Platform.numBits = 64) :
    recvKeyPre params index ce := by
  obtain ⟨h_next, h_al, h_le⟩ := h_inv
  obtain ⟨h_idx, h_ooo, h_sum⟩ := h_params
  have h_usize := usize_max_eq_of_64 h_64
  refine ⟨h_next, h_idx, h_ooo, h_ctr, ?_, ?_, h_al, h_le, h_sum, h_64⟩
  · have h_idx_lt : index.val < 2 ^ 32 := by scalar_tac
    have h_ctr_lt : ce.recv.ctr.val < 2 ^ 32 := by scalar_tac
    have h_usize' : (2 : Nat) ^ 64 - 1 = 18446744073709551615 := by norm_num
    rw [h_usize, h_usize']
    omega
  · simp only [CedCtrBound] at h_ctr
    scalar_tac

end spqr.chain
