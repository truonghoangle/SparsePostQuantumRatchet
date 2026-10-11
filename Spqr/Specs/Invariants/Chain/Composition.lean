/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Invariants.Chain.New
import Spqr.Specs.Invariants.Chain.AddEpoch
import Spqr.Specs.Invariants.Chain.SendKey
import Spqr.Specs.Invariants.Chain.RecvKey
/-!
# Composition: `ChainInv` is an inductive invariant of the in-memory `Chain` API

Models the operation sequences performed by `spqr::send` and `spqr::recv` in `spqr/src/lib.rs`
on a `Chain` value that is *not* re-loaded through `from_pb`, and proves that `ChainInv` holds on
every reachable state:

* `sendStep`  — `add_epoch?; send_key` (the `Some(chain)` branch of `spqr::send`);
* `recvStep`  — `add_epoch?; recv_key` (the tail of `spqr::recv`);
* `ChainStep` / `Reachable` — an inductive trace relation and its `ChainInv` soundness theorem.

All arithmetic side conditions (§3 of `docs/invariantsSPQR.md`) are carried as hypotheses of the
individual steps; they are fuel/configuration bounds, not state invariants.  The persistence
boundary is deliberately excluded: see `Spqr.Specs.Invariants.Chain.FromPb`.

Source: "spqr/src/lib.rs"
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- The chain-side effect of `spqr::send`: optionally advance the epoch, then derive a send key
for `epoch`. -/
noncomputable def sendStep (self : chain.Chain) (es : Option EpochSecret) (epoch : U64) :
    Result ((core.result.Result (U32 × alloc.vec.Vec U8) Error) × chain.Chain) := do
  let c ← match es with
    | none => ok self
    | some e => add_epoch self e
  send_key c epoch

/-- The chain-side effect of `spqr::recv`: optionally advance the epoch, then derive a receive
key for `(epoch, index)`. -/
noncomputable def recvStep (self : chain.Chain) (es : Option EpochSecret) (epoch : U64)
    (index : U32) :
    Result ((core.result.Result (alloc.vec.Vec U8) Error) × chain.Chain) := do
  let c ← match es with
    | none => ok self
    | some e => add_epoch self e
  recv_key c epoch index

/-- Fuel hypothesis for `add_epoch` (model artefact + cross-component coupling). -/
def AddEpochPre (self : chain.Chain) (es : Option EpochSecret) : Prop :=
  match es with
  | none => True
  | some e => e.epoch.val = self.current_epoch.val + 1 ∧ self.links.buf.val.length < Usize.max

/-- Optional `add_epoch` preserves `ChainInv` and keeps `send_epoch`/`params`. -/
theorem addEpochOpt_spec (self : chain.Chain) (es : Option EpochSecret)
    (h_inv : ChainInv self) (h_pre : AddEpochPre self es) :
    (match es with
      | none => ok self
      | some e => add_epoch self e) ⦃ (c : chain.Chain) =>
      ChainInv c ∧ c.send_epoch = self.send_epoch ∧ c.params = self.params ⦄ := by
  cases es with
  | none =>
    change WP.spec (ok self) _
    rw [WP.spec_ok]
    exact ⟨h_inv, rfl, rfl⟩
  | some e =>
    obtain ⟨h_epoch, h_buf⟩ := h_pre
    apply WP.spec_mono (add_epoch_spec_chainInv self e h_epoch h_inv h_buf)
    intro c ⟨h1, _, h3, h4⟩
    exact ⟨h1, h3, h4⟩

/-- **`sendStep` preserves `ChainInv`.**  The fuel bound on the target send counter is stated for
*every* slot of the intermediate chain (`∀ c`), since the slot is only known after the optional
`add_epoch`. -/
theorem sendStep_chainInv (self : chain.Chain) (es : Option EpochSecret) (epoch : U64)
    (h_inv : ChainInv self) (h_pre : AddEpochPre self es)
    (h_ctr : ∀ c : chain.Chain, ChainInv c →
      ∀ (j : Nat) (ce : chain.ChainEpoch), c.links.buf.val[j]? = some ce →
        ce.send.ctr < U32.max)
    (h_64 : System.Platform.numBits = 64) :
    sendStep self es epoch ⦃ (result : (core.result.Result (U32 × alloc.vec.Vec U8) Error) ×
        chain.Chain) =>
      ChainInv result.2 ⦄ := by
  unfold sendStep
  apply WP.spec_bind (addEpochOpt_spec self es h_inv h_pre)
  intro c ⟨hc, _, _⟩
  have h_ctr' : c.send_epoch.val ≤ epoch.val → epoch.val ≤ c.current_epoch.val →
      c.current_epoch.val - epoch.val < c.links.length.val →
      match c.links.buf.val[c.links.head.val + sendKeyIdx c epoch]? with
      | none => True
      | some ce => ce.send.ctr < U32.max := by
    intro _ _ _
    cases h : c.links.buf.val[c.links.head.val + sendKeyIdx c epoch]? with
    | none => trivial
    | some ce => exact h_ctr c hc _ ce h
  apply WP.spec_mono (send_key_spec_chainInv c epoch hc h_ctr' h_64)
  intro r ⟨_, h⟩
  exact h

/-- **`recvStep` preserves `ChainInv`.** -/
theorem recvStep_chainInv (self : chain.Chain) (es : Option EpochSecret) (epoch : U64)
    (index : U32)
    (h_inv : ChainInv self) (h_pre : AddEpochPre self es)
    (h_params : ParamsBound self.params index)
    (h_ctr : ∀ c : chain.Chain, ChainInv c →
      ∀ (j : Nat) (ce : chain.ChainEpoch), c.links.buf.val[j]? = some ce → CedCtrBound ce.recv)
    (h_64 : System.Platform.numBits = 64) :
    recvStep self es epoch index ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.Chain) =>
      ChainInv result.2 ⦄ := by
  unfold recvStep
  apply WP.spec_bind (addEpochOpt_spec self es h_inv h_pre)
  intro c ⟨hc, _, hp⟩
  have h_ctr' : epoch.val ≤ c.current_epoch.val →
      c.current_epoch.val - epoch.val < c.links.length.val →
      match c.links.buf.val[c.links.head.val + recvKeyIdx c epoch]? with
      | none => True
      | some ce => CedCtrBound ce.recv := by
    intro _ _
    cases h : c.links.buf.val[c.links.head.val + recvKeyIdx c epoch]? with
    | none => trivial
    | some ce => exact h_ctr c hc _ ce h
  rw [← hp] at h_params
  apply WP.spec_mono (recv_key_spec_chainInv c epoch index hc h_params h_ctr' h_64)
  intro r ⟨_, h⟩
  exact h

/-! ## Trace relation -/

/-- One in-memory chain transition, with its fuel/configuration side conditions attached. -/
inductive ChainStep : chain.Chain → chain.Chain → Prop
  | send (self c : chain.Chain) (es : Option EpochSecret) (epoch : U64)
      (r : core.result.Result (U32 × alloc.vec.Vec U8) Error)
      (h_pre : AddEpochPre self es)
      (h_ctr : ∀ c' : chain.Chain, ChainInv c' →
        ∀ (j : Nat) (ce : chain.ChainEpoch), c'.links.buf.val[j]? = some ce →
          ce.send.ctr < U32.max)
      (h_run : sendStep self es epoch = ok (r, c)) :
      ChainStep self c
  | recv (self c : chain.Chain) (es : Option EpochSecret) (epoch : U64) (index : U32)
      (r : core.result.Result (alloc.vec.Vec U8) Error)
      (h_pre : AddEpochPre self es)
      (h_params : ParamsBound self.params index)
      (h_ctr : ∀ c' : chain.Chain, ChainInv c' →
        ∀ (j : Nat) (ce : chain.ChainEpoch), c'.links.buf.val[j]? = some ce →
          CedCtrBound ce.recv)
      (h_run : recvStep self es epoch index = ok (r, c)) :
      ChainStep self c

/-- Chains reachable from a `Chain.new` result by finitely many `ChainStep`s. -/
inductive Reachable : chain.Chain → Prop
  | init (initial_key : Slice U8) (dir : proto.pq_ratchet.Direction)
      (params : proto.pq_ratchet.ChainParams) (c : chain.Chain)
      (h : new initial_key dir params = ok (core.result.Result.Ok c)) :
      Reachable c
  | step (c c' : chain.Chain) (h : Reachable c) (hs : ChainStep c c') : Reachable c'

/-- **Soundness of the composition**: every reachable in-memory chain satisfies `ChainInv`
(64-bit platform). -/
theorem chainInv_of_reachable (c : chain.Chain) (h : Reachable c)
    (h_64 : System.Platform.numBits = 64) :
    ChainInv c := by
  induction h with
  | init initial_key dir params c h =>
    have hs := new_spec_chainInv initial_key dir params
    rw [h, WP.spec_ok] at hs
    exact hs
  | step c c' _ hs ih =>
    cases hs with
    | send es epoch r h_pre h_ctr h_run =>
      have hsp := sendStep_chainInv c es epoch ih h_pre h_ctr h_64
      rw [h_run, WP.spec_ok] at hsp
      exact hsp
    | recv es epoch index r h_pre h_params h_ctr h_run =>
      have hsp := recvStep_chainInv c es epoch index ih h_pre h_params h_ctr h_64
      rw [h_run, WP.spec_ok] at hsp
      exact hsp

end spqr.chain.Chain
