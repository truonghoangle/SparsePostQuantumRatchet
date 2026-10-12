/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Chain.ChainEpochDirection.FromPb
import Spqr.Specs.Chain.ChainEpochDirection.IntoPb
import Spqr.Specs.Chain.ChainEpochDirection.Key
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb
import Spqr.Specs.Chain.Chain.RecvKey
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FromPb

/-! # Bug #2: Deserialized State Never Validated — Panics from Corrupted Blobs

**Severity**: MEDIUM (see docs/CorruptedBlobs.md §13; primary threat is non-adversarial
storage corruption, and the host may catch panics at the FFI boundary — but no graceful
error path exists *inside SPQR*).

Unlike Bug #1 (chunk poisoning via network messages, mitigated by auth-before-commit),
this bug targets **persisted local state** — no integration-level mitigation exists inside
SPQR.

**Spec chain**: `FromPb.lean` (`from_pb` never errors, copies fields verbatim) ×
`Funs.lean` (`next_key_internal` → `copy_from_slice`, `KeyHistory::get` → `assert_eq!`,
`KeyHistory::gc` → `assert!`) × `Key.lean` (`key` routes every request into one of these) ×
`IntoPb.lean` (faithful round-trip, so the corruption is persisted again).

We prove the bug in eleven phases:
1. `from_pb` always succeeds with no validation.
2. The three downstream consumers **cannot return `ok`** (i.e. they panic) on a corrupted
   `ChainEpochDirection`: `next.len() ≠ 32`, `prev.len() % 36 ≠ 0`, or a large `prev` with a
   small `ctr`.
3. These panics are reachable from `ChainEpochDirection::key` — the function `recv_key`
   calls on every incoming message.
4. **End-to-end**: `from_pb pb = Ok ced` and then `key ced …` never returns `ok`.
5. Corrupted state round-trips through `into_pb` (crash loop).
6. `Authenticator::from_pb` accepts arbitrary-length keys.
7. `Chain::from_pb` copies `next_root` verbatim (any length).
8. `PolyDecoder::from_pb` copies `is_complete` verbatim (stalled decoder witness).
9. The `Chain::recv_key` spec precondition `recvKeyPre` is unsatisfiable on corrupted
   `recv` directions (precondition-level lift of Phases 3–4; not a reachability proof).
10. `Chain::recv_key` has no `ok` result on corrupted state (full reachability lift).
11. **§16 remote-attack reach analysis**: `from_pb` copies `ctr`/`next`/`prev` verbatim;
    `recvKeyPre` is unsatisfiable in zones Z1 (`ctr > U32.max − 390451572`) and Z3
    (`ctr = U32.max`); a Z1 blob survives `from_pb` unchanged; the tighter runtime guard
    `ctr + maxOoo ≤ U32.max` implies the Lean slack bound; and zone Z0 is satisfiable.

**Source**: docs/CorruptedBlobs.md, `src/chain.rs` L145–312 -/

open Aeneas Aeneas.Std Result spqr chain.ChainEpochDirection

namespace spqr.Bugs.CorruptedBlobs

/-! ## Auxiliary lemma -/

/-- Inversion of a successful monadic bind in `Result`. -/
private theorem bind_eq_ok_iff {α β : Type} (m : Result α) (f : α → Result β) (r : β) :
    (m >>= f) = ok r ↔ ∃ x, m = ok x ∧ f x = ok r := by
  cases m <;> simp [bind_tc_eq, bind_ok, bind_vis, bind_div, ok.injEq]

/-- `Std.bind`-level variant of `bind_eq_ok_iff` (the Aeneas translation sometimes
    produces `Std.bind` applications that are only reducibly equal to `>>=`). -/
private theorem std_bind_eq_ok_iff {α β : Type} (m : Result α) (f : α → Result β) (r : β) :
    Std.bind m f = ok r ↔ ∃ x, m = ok x ∧ f x = ok r :=
  bind_eq_ok_iff m f r

/-! ## Phase 1: `from_pb` always succeeds — no validation -/

theorem from_pb_never_fails (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced =>
        ced.ctr = pb.ctr ∧ ced.next = pb.next ∧ ced.prev = { data := pb.prev }
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_eq
  simp only [chain.ChainEpochDirection.FunctionalModels.fromPb] at h_eq
  subst h_eq
  exact ⟨rfl, rfl, rfl⟩

/-! ## Phase 2a: Corrupted blobs violate consumer preconditions

`from_pb` copies the fields verbatim, so any structural violation in the blob is a structural
violation in the resulting `ChainEpochDirection`. -/

/-- **Witness 1**: `next.len() ≠ 32` survives `from_pb`. -/
theorem from_pb_admits_wrong_next_length
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_bad : pb.next.length ≠ 32) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced => ced.next.length ≠ 32
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_eq
  simp only [chain.ChainEpochDirection.FunctionalModels.fromPb] at h_eq
  subst h_eq
  exact h_bad

/-- **Witness 2**: `prev.len() % 36 ≠ 0` survives `from_pb`. -/
theorem from_pb_admits_misaligned_prev
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_bad : pb.prev.length % 36 ≠ 0) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced => ced.prev.data.length % 36 ≠ 0
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_eq
  simp only [chain.ChainEpochDirection.FunctionalModels.fromPb] at h_eq
  subst h_eq
  exact h_bad

/-- **Witness 3**: large `prev` + `ctr = 0` survives `from_pb`.
    79236 = `(2000 * 11 / 10 + 1) * 36`, the default trim threshold. -/
theorem from_pb_admits_large_prev_small_ctr
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_ctr_zero : pb.ctr = 0#u32)
    (h_prev_large : pb.prev.length ≥ 79236) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced =>
        ced.ctr = 0#u32 ∧ ced.prev.data.length ≥ 79236
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result
  match result with
  | core.result.Result.Ok ced =>
    intro h_eq
    simp only [chain.ChainEpochDirection.FunctionalModels.fromPb,
      core.result.Result.Ok.injEq] at h_eq
    subst h_eq
    exact ⟨h_ctr_zero, h_prev_large⟩
  | core.result.Result.Err _ =>
    intro h_eq
    simp only [chain.ChainEpochDirection.FunctionalModels.fromPb] at h_eq
    cases h_eq


/-- **Combined**: all three violations co-exist in a single blob. -/
theorem from_pb_admits_triple_violation
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_next_bad : pb.next.length ≠ 32)
    (h_prev_bad : pb.prev.length % 36 ≠ 0)
    (h_ctr_zero : pb.ctr = 0#u32) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced =>
        ced.next.length ≠ 32 ∧ ced.prev.data.length % 36 ≠ 0 ∧ ced.ctr = 0#u32
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result
  match result with
  | core.result.Result.Ok ced =>
    intro h_eq
    simp only [chain.ChainEpochDirection.FunctionalModels.fromPb,
      core.result.Result.Ok.injEq] at h_eq
    subst h_eq
    exact ⟨h_next_bad, h_prev_bad, h_ctr_zero⟩
  | core.result.Result.Err _ =>
    intro h_eq
    simp only [chain.ChainEpochDirection.FunctionalModels.fromPb] at h_eq
    cases h_eq

/-! ## Phase 2b: The consumers panic on the corrupted state

In the Aeneas model a Rust `panic!`/`assert!` is `fail`, so "never returns `ok`" is exactly
"panics on every execution". The three theorems below match §4, §5, §6 of the report. -/

/-- **Panic 2** (`KeyHistory::get`, `chain.rs:191`): `assert_eq!(self.data.len() % 36, 0)`
    fails whenever the history is misaligned, before any other logic runs. -/
theorem get_never_ok (self : chain.KeyHistory) (at1 current_ctr : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_bad : self.data.length % 36 ≠ 0) :
    ∀ r, chain.KeyHistory.get self at1 current_ctr params ≠ ok r := by
  intro r h
  unfold chain.KeyHistory.get at h
  obtain ⟨_, h_ks, rfl⟩ := WP.spec_imp_exists chain.KeyHistory.KEY_SIZE_spec
  simp only [bind_ok, h_ks] at h
  have h_rem := Usize.rem_spec (alloc.vec.Vec.len self.data) (y := 36#usize) (by simp)
  obtain ⟨lv, h_lv, h_val⟩ := WP.spec_imp_exists h_rem
  simp only [bind_ok, h_lv] at h
  simp only [massert, alloc.vec.Vec.len_val, UScalar.ofNatCore_val_eq] at h h_val
  simp at h_val
  split at h
  · rename_i h_eq
    have : lv.val = 0 := by rw [h_eq]; simp
    simp only [alloc.vec.Vec.length] at h_bad h_val
    omega
  · simp at h

/-- **Panic 3** (`KeyHistory::gc`, `chain.rs:149`): once `data.len() ≥ trim_size() * 36`,
    `assert!(current_key >= max_ooo_keys_or_default())` fails whenever the counter is smaller
    than the OOO budget — a state that can only arise from a corrupted blob. -/
theorem gc_never_ok (self : chain.KeyHistory) (current_key : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_ooo : params.max_ooo_keys.val < 390451572)
    (h_large : ((chain.maxOoo params).val * 11 / 10 + 1) * 36 ≤ self.data.length)
    (h_small : current_key.val < (chain.maxOoo params).val) :
    ∀ r, chain.KeyHistory.gc self current_key params ≠ ok r := by
  intro r h
  unfold chain.KeyHistory.gc at h
  obtain ⟨ts, h_ts, h_ts1, h_ts2⟩ :=
    WP.spec_imp_exists (chain.ChainParams.trim_size_spec params h_ooo)
  obtain ⟨_, h_ks, rfl⟩ := WP.spec_imp_exists chain.KeyHistory.KEY_SIZE_spec
  obtain ⟨mo, h_mo, h_mo1, h_mo2⟩ :=
    WP.spec_imp_exists (chain.ChainParams.max_ooo_keys_or_default_spec params)
  have h_mo_val : mo.val = (chain.maxOoo params).val :=
    maxOoo_val_eq_of_posts params mo h_mo1 h_mo2
  have h_ts_val : ts.val = (chain.maxOoo params).val * 11 / 10 + 1 := by
    unfold chain.maxOoo
    by_cases hp : params.max_ooo_keys > 0#u32
    · simp only [hp, ite_true]; exact h_ts1.mpr hp
    · simp only [hp, ite_false, chain.DEFAULT_CHAIN_PARAMS_spec]
      simp only [gt_iff_lt, not_lt] at hp
      have hz : params.max_ooo_keys = 0#u32 := by scalar_tac
      have := h_ts2.mpr (Or.inl hz)
      simp [this]
  simp only [alloc.vec.Vec.len, ge_iff_le, UScalar.le_equiv, Usize.ofNatCore_val_eq,
    Array.index_RangeFull, bind_ok] at h
  have h_bound := self.data.property
  simp only [alloc.vec.Vec.length] at h_large
  have hmul := Usize.mul_spec (x := ts) (y := 36#usize) (by scalar_tac)
  obtain ⟨prod', h_prod', h_prod_val⟩ := WP.spec_imp_exists hmul
  simp only [h_ts, h_ks, h_prod', bind_ok] at h
  have h_cond : prod'.val ≤ self.data.val.length := by
    have h36 : (36#usize).val = 36 := by simp
    rw [h36] at h_prod_val
    omega
  rw [if_pos h_cond] at h
  simp only [h_mo, bind_ok, massert] at h
  split at h
  · rename_i hge
    omega
  · simp at h

/-- If `next_key_internal` returns `ok`, then the input `next` had exactly 32 bytes, and so
    does the written-back slice. (`copy_from_slice` fails on any length mismatch.) -/
theorem next_key_internal_ok_lengths (next : Slice U8) (ctr : U32)
    (r : (U32 × (Array U8 32#usize)) × (Slice U8) × U32)
    (h : next_key_internal next ctr = ok r) :
    next.length = 32 ∧ r.2.1.length = 32 := by
  unfold next_key_internal at h
  simp only [core.slice.Slice.is_empty, massert] at h
  rw [std_bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  simp only [ok.injEq] at hb
  subst hb
  split at h
  · simp only [std_bind_eq_ok_iff] at h
    obtain ⟨_, _, h⟩ := h
    simp only [lift, ok.injEq, exists_eq_left'] at h
    obtain ⟨_, _, h⟩ := h
    obtain ⟨_, _, h⟩ := h
    obtain ⟨_, _, h⟩ := h
    simp only [Array.to_slice_mut, uncurry_apply_pair] at h
    simp only [std_bind_eq_ok_iff] at h
    obtain ⟨s6, _, h⟩ := h
    obtain ⟨s7, h_s7, h⟩ := h
    obtain ⟨next1, h_cp, h⟩ := h
    obtain ⟨_, _, h⟩ := h
    obtain ⟨_, _, h⟩ := h
    obtain ⟨_, _, h_r⟩ := h
    simp only [ok.injEq] at h_r
    subst h_r
    have h_s7_len : s7.length = 32 := by
      have := Array.index_SliceIndexRangeToUsizeSlice.step
        (Array.from_slice (Array.repeat 64#usize 0#u8) s6) ({ «end» := 32#usize }) (by simp)
      obtain ⟨s7', h_s7', _, h_len⟩ := WP.spec_imp_exists this
      rw [h_s7] at h_s7'; simp only [ok.injEq] at h_s7'; subst h_s7'
      simpa using h_len
    simp only [core.slice.Slice.copy_from_slice] at h_cp
    split at h_cp
    · rename_i h_eq
      have := congrArg UScalar.val h_eq
      simp only [Slice.len_val] at this
      simp only [ok.injEq] at h_cp
      subst h_cp
      exact ⟨by omega, h_s7_len⟩
    · simp at h_cp
  · simp at h

/-- **Panic 1** (`next_key_internal`, `chain.rs:229/243`): a chain secret that is not 32 bytes
    never returns `ok` — either `assert!(!next.is_empty())` or `copy_from_slice` panics. -/
theorem next_key_internal_never_ok (next : Slice U8) (ctr : U32)
    (h_bad : next.length ≠ 32) :
    ∀ r, next_key_internal next ctr ≠ ok r :=
  fun r h => h_bad (next_key_internal_ok_lengths next ctr r h).1

/-! ## Phase 3: The panics are reachable from `ChainEpochDirection::key`

`recv()` → `Chain::recv_key` → `ChainEpochDirection::key`. We show `key` cannot return `ok`
on a corrupted `ChainEpochDirection` along each of its three code paths. -/

/-- The chain-secret vector carried by a `ControlFlow` state of the key-advancing loop. -/
def cfNext (cf : ControlFlow (U32 × (alloc.vec.Vec U8) × chain.KeyHistory)
    (U32 × (alloc.vec.Vec U8) × chain.KeyHistory)) : alloc.vec.Vec U8 :=
  match cf with
  | ControlFlow.cont (_, v', _) => v'
  | ControlFlow.done (_, v', _) => v'

/-- One iteration of the key-advancing loop preserves the length of the chain-secret vector
    (either it is untouched, or it is overwritten by a 32-byte slice while it had 32 bytes). -/
theorem key_loop_body_preserves_next_length
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (cf : ControlFlow (U32 × (alloc.vec.Vec U8) × chain.KeyHistory)
      (U32 × (alloc.vec.Vec U8) × chain.KeyHistory))
    (h : key_loop.body at1 params i v kh = ok cf) :
    (cfNext cf).length = v.length := by
  unfold key_loop.body at h
  replace h := (std_bind_eq_ok_iff (i + 1#u32) _ cf).mp h
  obtain ⟨_, _, h⟩ := h
  split at h
  · simp  [alloc.vec.Vec.deref_mut, lift, std_bind_eq_ok_iff] at h
    obtain ⟨⟨_, s1, _⟩, h_nki, h⟩ := h
    simp at h
    obtain ⟨_, _, h⟩ := h
    obtain ⟨h_nki, _, _, h⟩ := h
    obtain ⟨_, _,  h⟩ := h
    have h_lens := next_key_internal_ok_lengths _ _ _ h_nki
    simp at h_lens
    split at h
    · simp only [std_bind_eq_ok_iff] at h
      obtain ⟨_, _, h⟩ := h
      simp only [ok.injEq] at h; subst h
      simp  [cfNext, alloc.vec.Vec.length, Slice.length] at h_lens ⊢
      simp
      omega
    · simp only [ok.injEq] at h; subst h
      simp only [cfNext, alloc.vec.Vec.length, Slice.length] at h_lens ⊢
      omega
  · simp only [ok.injEq] at h; subst h
    rfl

/-- The key-advancing loop preserves the length of the chain-secret vector
    (partial-correctness induction on the `loop` fixpoint). -/
theorem key_loop_preserves_next_length
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (r : U32 × (alloc.vec.Vec U8) × chain.KeyHistory)
    (h : key_loop i v kh at1 params = ok r) :
    r.2.1.length = v.length := by
  unfold key_loop at h
  revert h
  generalize h_body : (fun (p : U32 × (alloc.vec.Vec U8) × chain.KeyHistory) =>
        key_loop.body at1 params p.1 p.2.1 p.2.2) = body
  have h_body_app : ∀ p, body p = key_loop.body at1 params p.1 p.2.1 p.2.2 := by
    intro p; rw [← h_body]
  suffices ∀ (x : U32 × (alloc.vec.Vec U8) × chain.KeyHistory),
      loop body x = ok r → r.2.1.length = x.2.1.length from
    fun h => this (i, v, kh) h
  refine loop.fixpoint_induct body
    (fun f => ∀ x, f x = ok r → r.2.1.length = x.2.1.length) ?_ ?_
  · apply Lean.Order.admissible_pi_apply
      (P := fun (x : U32 × (alloc.vec.Vec U8) × chain.KeyHistory)
        (y : Result (U32 × (alloc.vec.Vec U8) × chain.KeyHistory)) =>
          y = ok r → r.2.1.length = x.2.1.length)
    intro x
    apply Lean.Order.admissible_flatOrder
    intro h
    cases h
  · intro f ih x hx
    obtain ⟨i0, v0, kh0⟩ := x
    simp only [h_body_app] at hx
    split at hx
    · rename_i cf h_body
      have h_pres := key_loop_body_preserves_next_length at1 params i0 v0 kh0 cf h_body
      cases cf with
      | cont x' =>
        have := ih _ hx
        obtain ⟨_, _, _⟩ := x'
        simp only [cfNext] at h_pres this ⊢
        omega
      | done y =>
        simp only [ok.injEq] at hx; subst hx
        simpa [cfNext] using h_pres
    · simp at hx
    · simp at hx

/-- **D2. Panic at `KeyHistory::get`** (`chain.rs` L192): when `at + max_ooo_keys > U32.max`,
    the `U32` addition overflows and `get` has no `ok` result.
    Debug builds panic; release builds wrap, spuriously reporting valid keys as `KeyTrimmed`. -/
theorem get_never_ok_of_ooo_overflow (self : chain.KeyHistory) (at1 current_ctr : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_overflow : at1.val + (chain.maxOoo params).val > U32.max) :
    ∀ r, chain.KeyHistory.get self at1 current_ctr params ≠ ok r := by
  intro r h
  unfold chain.KeyHistory.get at h
  obtain ⟨_, h_ks, rfl⟩ := WP.spec_imp_exists chain.KeyHistory.KEY_SIZE_spec
  simp only [bind_eq_ok_iff, h_ks, ok.injEq, exists_eq_left'] at h
  obtain ⟨lv, h_lv, h_rest⟩ := h
  have h_rem := Usize.rem_spec (alloc.vec.Vec.len self.data) (y := 36#usize) (by simp)
  obtain ⟨lv', h_lv', h_val⟩ := WP.spec_imp_exists h_rem
  rw [h_lv] at h_lv'; simp only [ok.injEq] at h_lv'; subst h_lv'
  simp only [massert, alloc.vec.Vec.len_val, UScalar.ofNatCore_val_eq] at h_rest h_val
  simp at h_val
  split at h_rest
  · -- massert passed: alignment is fine, continue to max_ooo_keys_or_default then at+mo
    rename_i h_eq
    -- h_rest has the form: ∃ mo, ... = ok mo ∧ ∃ i3, at1 + mo = ok i3 ∧ ...
    -- but massert with True simplifies the bind. Use cases on the bind result.
    -- After massert, h_rest is a bind chain. Extract max_ooo_keys_or_default result.
    obtain ⟨mo', h_mo', h_mo1, h_mo2⟩ :=
      WP.spec_imp_exists (chain.ChainParams.max_ooo_keys_or_default_spec params)
    -- The bind `max_ooo_keys_or_default >>= ...` must have produced `ok mo'`, so
    -- we can substitute it into h_rest.
    simp only [h_mo'] at h_rest
    have h_mo_val := maxOoo_val_eq_of_posts params mo' h_mo1 h_mo2
    -- Now h_rest should have `at1 + mo' = ok i3 ∧ ...`
    obtain ⟨i3, h_i3, _⟩ := h_rest
    have h_add := UScalar.add_equiv at1 mo'
    simp  at h_add
    have : at1.val + mo'.val ≤ U32.max := by grind
    omega
  · simp at h_rest

/-- **D2. Path `at < ctr`** (out-of-order key): `key` calls `KeyHistory::get`; when
    `at + maxOoo > U32.max`, `get` fails because the addition at L192 overflows. -/
theorem key_never_ok_of_ooo_overflow (self : chain.ChainEpochDirection) (at1 : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_lt : at1.val < self.ctr.val)
    (h_overflow : at1.val + (chain.maxOoo params).val > U32.max) :
    ∀ r, key self at1 params ≠ ok r := by
  intro r h
  unfold key at h
  simp only [lift, core.cmp.impls.OrdU32.cmp, bind_tc_ok] at h
  rw [Nat.compare_eq_lt.mpr h_lt] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨p, h_get, _⟩ := h
  have := get_never_ok_of_ooo_overflow self.prev at1 self.ctr params  h_overflow
  exact this p h_get

/-- **Path `at < ctr`** (out-of-order key): `key` immediately calls `KeyHistory::get` on
    `prev`; with a misaligned `prev` this never returns `ok` (Panic 2). -/
theorem key_never_ok_of_misaligned_prev (self : chain.ChainEpochDirection) (at1 : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_lt : at1.val < self.ctr.val)
    (h_bad : self.prev.data.length % 36 ≠ 0) :
    ∀ r, key self at1 params ≠ ok r := by
  intro r h
  unfold key at h
  simp only [lift, core.cmp.impls.OrdU32.cmp, bind_tc_ok] at h
  rw [Nat.compare_eq_lt.mpr h_lt] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨p, h_get, _⟩ := h
  exact get_never_ok self.prev at1 self.ctr params h_bad p h_get

/-- **Path `ctr < at ≤ ctr + maxJump`** (forward key): `key` advances the chain with
    `next_key_internal`; with `next.len() ≠ 32` this never returns `ok` (Panic 1). The advancing
    loop preserves the length of `next`, so the final `next_key_internal` call sees the corrupted
    length whether or not the loop ran. -/
theorem key_never_ok_of_bad_next (self : chain.ChainEpochDirection) (at1 : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_gt : self.ctr.val < at1.val)
    (h_jump : at1.val - self.ctr.val ≤ (chain.maxJump params).val)
    (h_bad : self.next.length ≠ 32) :
    ∀ r, key self at1 params ≠ ok r := by
  intro r h
  unfold key at h
  simp only [lift, core.cmp.impls.OrdU32.cmp, bind_tc_ok] at h
  rw [Nat.compare_eq_gt.mpr h_gt] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨d, h_d, h⟩ := h
  obtain ⟨mj, h_mj, h⟩ := h
  have h_d_val : d.val = at1.val - self.ctr.val := by
    obtain ⟨d', h_d', h_val⟩ :=
      WP.spec_imp_exists (U32.sub_spec (x := at1) (y := self.ctr) (by omega))
    rw [h_d] at h_d'; simp only [ok.injEq] at h_d'; subst h_d'; exact h_val.1
  obtain ⟨mj', h_mj', h_mj1, h_mj2⟩ :=
    WP.spec_imp_exists (chain.ChainParams.max_jump_or_default_spec params)
  rw [h_mj] at h_mj'; simp only [ok.injEq] at h_mj'; subst h_mj'
  have h_mj_val := maxJump_val_eq_of_posts params mj h_mj1 h_mj2
  split at h
  · rename_i h_gt_jump
    simp only [gt_iff_lt, UScalar.lt_equiv] at h_gt_jump
    omega
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨_, _, h⟩ := h
    obtain ⟨_, _, h⟩ := h
    obtain ⟨_, _, h⟩ := h
    obtain ⟨⟨_, v, _⟩, h_loop, h⟩ := h
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
    obtain ⟨_, _, h⟩ := h
    simp only [alloc.vec.Vec.deref_mut, uncurry_apply_pair, bind_eq_ok_iff] at h
    have h_v_len : v.length = self.next.length :=
      key_loop_preserves_next_length _ _ _ _ _ _ h_loop
    obtain ⟨⟨⟨_, _⟩, _, _⟩, h_nki, _⟩ := h
    have h_lens := next_key_internal_ok_lengths _ _ _ h_nki
    simp only [Slice.length, alloc.vec.Vec.length] at h_lens h_v_len h_bad
    omega

/-- **Path `at = ctr + 1`** (the very next key, the common case): the advancing loop exits at
    once, `prev` is handed unchanged to `KeyHistory::gc`, and with a history already at the GC
    threshold but a counter below `max_ooo` this never returns `ok` (Panic 3). -/
theorem key_never_ok_of_large_prev_small_ctr (self : chain.ChainEpochDirection) (at1 : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_at : at1.val = self.ctr.val + 1)
    (h_jump : 1 ≤ (chain.maxJump params).val)
    (h_ooo : params.max_ooo_keys.val < 390451572)
    (h_large : ((chain.maxOoo params).val * 11 / 10 + 1) * 36 ≤ self.prev.data.length)
    (h_small : self.ctr.val < (chain.maxOoo params).val) :
    ∀ r, key self at1 params ≠ ok r := by
  intro r h
  unfold key at h
  simp only [lift, core.cmp.impls.OrdU32.cmp, bind_tc_ok] at h
  rw [Nat.compare_eq_gt.mpr (by omega)] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨d, h_d, h⟩ := h
  obtain ⟨mj, h_mj, h⟩ := h
  have h_d_val : d.val = 1 := by
    obtain ⟨d', h_d', h_val⟩ :=
      WP.spec_imp_exists (U32.sub_spec (x := at1) (y := self.ctr) (by omega))
    rw [h_d] at h_d'; simp only [ok.injEq] at h_d'; subst h_d'; omega
  obtain ⟨mj', h_mj', h_mj1, h_mj2⟩ :=
    WP.spec_imp_exists (chain.ChainParams.max_jump_or_default_spec params)
  rw [h_mj] at h_mj'; simp only [ok.injEq] at h_mj'; subst h_mj'
  have h_mj_val := maxJump_val_eq_of_posts params mj h_mj1 h_mj2
  split at h
  · rename_i h_gt_jump
    simp only [gt_iff_lt, UScalar.lt_equiv] at h_gt_jump
    omega
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨mo, h_mo, h⟩ := h
    obtain ⟨mo', h_mo', h_mo1, h_mo2⟩ :=
      WP.spec_imp_exists (chain.ChainParams.max_ooo_keys_or_default_spec params)
    rw [h_mo] at h_mo'; simp only [ok.injEq] at h_mo'; subst h_mo'
    have h_mo_val := maxOoo_val_eq_of_posts params mo h_mo1 h_mo2
    obtain ⟨i3, h_i3, h⟩ := h
    have h_maxooo_bound : (chain.maxOoo params).val < 390451572 := by
      unfold chain.maxOoo
      split
      · exact h_ooo
      · simp [chain.DEFAULT_CHAIN_PARAMS_spec]
    have h_i3_val : i3.val = self.ctr.val + mo.val := by
      obtain ⟨i3', h_i3', h_val⟩ :=
        WP.spec_imp_exists (U32.add_spec (x := self.ctr) (y := mo) (by scalar_tac))
      rw [h_i3] at h_i3'; simp only [ok.injEq] at h_i3'; subst h_i3'; exact h_val
    obtain ⟨kh, h_kh, h⟩ := h
    -- no `clear`: at1 = ctr + 1 ≤ ctr + maxOoo
    have h_kh_eq : kh = self.prev := by
      split at h_kh
      · rename_i h_clear
        simp only [gt_iff_lt, UScalar.lt_equiv] at h_clear
        omega
      · simp only [ok.injEq] at h_kh; exact h_kh.symm
    subst h_kh_eq
    obtain ⟨⟨i4, _, kh1⟩, h_loop, h⟩ := h
    -- the loop exits immediately: `at1 > ctr + 1` is false
    have h_loop_eq : i4 = self.ctr ∧ kh1 = self.prev := by
      unfold key_loop at h_loop
      rw [loop.eq_1] at h_loop
      simp only [key_loop.body] at h_loop
      have h_i1 : self.ctr + 1#u32 = ok at1 := by
        obtain ⟨_, h_i1', h_val⟩ := WP.spec_imp_exists
          (U32.add_spec (x := self.ctr) (y := 1#u32)
            (by simp only [UScalar.ofNatCore_val_eq]; scalar_tac))
        rw [h_i1']
        congr 1
        apply UScalar.eq_equiv _ _ |>.mpr
        simp only [UScalar.ofNatCore_val_eq] at h_val
        omega
      simp only [h_i1, bind_tc_ok, gt_iff_lt, lt_self_iff_false, ite_false, ok.injEq,
        Prod.mk.injEq] at h_loop
      exact ⟨h_loop.1.symm, h_loop.2.2.symm⟩
    obtain ⟨rfl, rfl⟩ := h_loop_eq
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
    obtain ⟨kh2, h_gc, _⟩ := h
    exact gc_never_ok self.prev self.ctr params h_ooo h_large h_small kh2 h_gc

/-- **D57. Path `ctr < at ≤ ctr + maxJump`** (forward key): when `ctr + maxOoo > U32.max`,
    the addition `self.ctr + max_ooo_keys_or_default` at `chain.rs` L265 overflows.
    In the Aeneas model this means the `U32` addition fails, so `key` has no `ok` result.
    Debug builds panic; release builds silently wrap, producing wrong GC / clear decisions. -/
theorem key_never_ok_of_large_ctr (self : chain.ChainEpochDirection) (at1 : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_gt : self.ctr.val < at1.val)
    (h_jump : at1.val - self.ctr.val ≤ (chain.maxJump params).val)
    (h_overflow : self.ctr.val + (chain.maxOoo params).val > U32.max) :
    ∀ r, key self at1 params ≠ ok r := by
  intro r h
  unfold key at h
  simp only [lift, core.cmp.impls.OrdU32.cmp, bind_tc_ok] at h
  rw [Nat.compare_eq_gt.mpr h_gt] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨d, h_d, h⟩ := h
  obtain ⟨mj, h_mj, h⟩ := h
  have h_d_val : d.val = at1.val - self.ctr.val := by
    obtain ⟨d', h_d', h_val⟩ :=
      WP.spec_imp_exists (U32.sub_spec (x := at1) (y := self.ctr) (by omega))
    rw [h_d] at h_d'; simp only [ok.injEq] at h_d'; subst h_d'; exact h_val.1
  obtain ⟨mj', h_mj', h_mj1, h_mj2⟩ :=
    WP.spec_imp_exists (chain.ChainParams.max_jump_or_default_spec params)
  rw [h_mj] at h_mj'; simp only [ok.injEq] at h_mj'; subst h_mj'
  have h_mj_val := maxJump_val_eq_of_posts params mj h_mj1 h_mj2
  split at h
  · rename_i h_gt_jump
    simp only [gt_iff_lt, UScalar.lt_equiv] at h_gt_jump
    omega
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨mo, h_mo, h⟩ := h
    obtain ⟨mo', h_mo', h_mo1, h_mo2⟩ :=
      WP.spec_imp_exists (chain.ChainParams.max_ooo_keys_or_default_spec params)
    rw [h_mo] at h_mo'; simp only [ok.injEq] at h_mo'; subst h_mo'
    have h_mo_val := maxOoo_val_eq_of_posts params mo h_mo1 h_mo2
    -- The addition `self.ctr + mo` must produce an `ok` for the bind to succeed,
    -- but self.ctr.val + mo.val > U32.max, so it fails.
    obtain ⟨i3, h_i3, _⟩ := h
    have h_add := UScalar.add_equiv self.ctr mo
    rw [h_i3] at h_add
    have : self.ctr.val + mo.val ≤ U32.max := by scalar_tac
    omega

/-! ## Phase 4: End-to-end — `from_pb` then `key` never returns `ok`

These are the `recv_after_restore_safe`-style theorems of §10.3 of the report, proved in the
**negative**: for each attack scenario of §12 the composition `from_pb` then `key` has no
successful execution. -/

/-- **Scenario 12.1** (`next` replaced by `[0]`): load the blob, then request any forward key
    within the jump window → panic. -/
theorem restore_then_recv_panics_bad_next
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_bad : pb.next.length ≠ 32)
    (ced : chain.ChainEpochDirection)
    (h_load : from_pb pb = ok (core.result.Result.Ok ced))
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (h_gt : ced.ctr.val < at1.val)
    (h_jump : at1.val - ced.ctr.val ≤ (chain.maxJump params).val) :
    ∀ r, key ced at1 params ≠ ok r := by
  obtain ⟨res, h_res, h_post⟩ := WP.spec_imp_exists (from_pb_spec pb)
  rw [h_load] at h_res; simp only [ok.injEq] at h_res; subst h_res
  obtain ⟨_, h_next, _⟩ := h_post
  exact key_never_ok_of_bad_next ced at1 params h_gt h_jump (by rw [h_next]; exact h_bad)

/-- **Scenario 12.3** (one byte appended to `prev`): load the blob, then request any
    out-of-order key → panic. -/
theorem restore_then_recv_panics_misaligned_prev
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_bad : pb.prev.length % 36 ≠ 0)
    (ced : chain.ChainEpochDirection)
    (h_load : from_pb pb = ok (core.result.Result.Ok ced))
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (h_lt : at1.val < ced.ctr.val) :
    ∀ r, key ced at1 params ≠ ok r := by
  obtain ⟨res, h_res, h_post⟩ := WP.spec_imp_exists (from_pb_spec pb)
  rw [h_load] at h_res; simp only [ok.injEq] at h_res; subst h_res
  obtain ⟨_, _, h_prev⟩ := h_post
  have hpd : ced.prev.data = pb.prev := by
    have := congrArg chain.KeyHistory.data h_prev; simp only at this; exact this
  exact key_never_ok_of_misaligned_prev ced at1 params h_lt (by rw [hpd]; exact h_bad)

/-- **Scenario 12.4** (`ctr = 0`, `prev = vec![0; 36 * 2201]`, default params): load the blob,
    then request the very next key (`at = 1`) → panic in `gc`. -/
theorem restore_then_recv_panics_large_prev_small_ctr
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_ctr_zero : pb.ctr = 0#u32)
    (h_prev_large : pb.prev.length ≥ 79236)
    (ced : chain.ChainEpochDirection)
    (h_load : from_pb pb = ok (core.result.Result.Ok ced))
    (params : proto.pq_ratchet.ChainParams)
    (h_default_ooo : params.max_ooo_keys = 0#u32)
    (h_jump : 1 ≤ (chain.maxJump params).val) :
    ∀ r, key ced 1#u32 params ≠ ok r := by
  obtain ⟨res, h_res, h_post⟩ := WP.spec_imp_exists (from_pb_spec pb)
  rw [h_load] at h_res; simp only [ok.injEq] at h_res; subst h_res
  obtain ⟨h_ctr, _, h_prev⟩ := h_post
  have hpd : ced.prev.data = pb.prev := by
    have := congrArg chain.KeyHistory.data h_prev; simp only at this; exact this
  have h_maxooo : (chain.maxOoo params).val = 2000 := by
    unfold chain.maxOoo
    simp [h_default_ooo, chain.DEFAULT_CHAIN_PARAMS_spec]
  have h_ctr_val : ced.ctr.val = 0 := by rw [h_ctr, h_ctr_zero]; simp
  apply key_never_ok_of_large_prev_small_ctr ced 1#u32 params
  · simp [h_ctr_val]
  · exact h_jump
  · rw [h_default_ooo]; simp
  · rw [h_maxooo, hpd]; simpa [alloc.vec.Vec.length] using h_prev_large
  · rw [h_maxooo, h_ctr_val]; omega

/-! ## Phase 5: Corrupted state round-trips through persistence -/

/-- `into_pb (from_pb pb) = pb` — corrupted state survives save/load unchanged.
    Combined with Phase 2 → **permanent crash loop**. -/
theorem corrupted_state_roundtrips
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced =>
        into_pb ced ⦃ (pb' : proto.pq_ratchet.chain.epoch.EpochDirection) =>
          pb'.ctr = pb.ctr ∧ pb'.next = pb.next ∧ pb'.prev = pb.prev ⦄
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result
  match result with
  | core.result.Result.Ok ced =>
    intro ⟨h_ctr, h_next, h_prev⟩
    change into_pb ced ⦃ (pb' : proto.pq_ratchet.chain.epoch.EpochDirection) =>
      pb'.ctr = pb.ctr ∧ pb'.next = pb.next ∧ pb'.prev = pb.prev ⦄
    have h_into := chain.ChainEpochDirection.into_pb_spec ced
    apply Aeneas.Std.WP.spec_mono h_into
    intro pb' ⟨h_pb_ctr, h_pb_next, h_pb_prev⟩
    exact ⟨by rw [h_pb_ctr, h_ctr],
           by rw [h_pb_next, h_next],
           by rw [h_pb_prev, h_prev]⟩
  | core.result.Result.Err _ => intro h; exact h

/-! ## Phase 6: `Authenticator::from_pb` accepts arbitrary-length keys -/

/-- `Authenticator::from_pb` always succeeds with no key-length validation. -/
theorem authenticator_from_pb_no_validation
    (pb : proto.pq_ratchet.Authenticator) :
    authenticator.serialize.Authenticator.from_pb pb
      ⦃ (result : authenticator.Authenticator) =>
        result.root_key = pb.root_key ∧ result.mac_key = pb.mac_key ⦄ := by
  have h := authenticator.serialize.Authenticator.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_eq
  rw [h_eq]
  exact ⟨rfl, rfl⟩

/-- **Security violation**: empty `mac_key` → trivial MAC forgery. -/
theorem authenticator_from_pb_admits_empty_mac_key
    (pb : proto.pq_ratchet.Authenticator)
    (h_empty : pb.mac_key.length = 0) :
    authenticator.serialize.Authenticator.from_pb pb
      ⦃ (result : authenticator.Authenticator) =>
        result.mac_key.length = 0 ⦄ := by
  have h := authenticator.serialize.Authenticator.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_eq
  rw [h_eq]; exact h_empty

/-- **Security violation**: empty `root_key` → broken forward secrecy. -/
theorem authenticator_from_pb_admits_empty_root_key
    (pb : proto.pq_ratchet.Authenticator)
    (h_empty : pb.root_key.length = 0) :
    authenticator.serialize.Authenticator.from_pb pb
      ⦃ (result : authenticator.Authenticator) =>
        result.root_key.length = 0 ⦄ := by
  have h := authenticator.serialize.Authenticator.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_eq
  rw [h_eq]; exact h_empty

/-- **Generalised**: `from_pb` accepts keys of any length ≠ 32. -/
theorem authenticator_from_pb_admits_wrong_key_lengths
    (pb : proto.pq_ratchet.Authenticator)
    (h_root_bad : pb.root_key.length ≠ 32)
    (h_mac_bad : pb.mac_key.length ≠ 32) :
    authenticator.serialize.Authenticator.from_pb pb
      ⦃ (result : authenticator.Authenticator) =>
        result.root_key.length ≠ 32 ∧ result.mac_key.length ≠ 32 ⦄ := by
  have h := authenticator.serialize.Authenticator.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_eq
  rw [h_eq]
  exact ⟨h_root_bad, h_mac_bad⟩

/-! ## Phase 7: `Chain.from_pb` copies `next_root` verbatim — no validation (§7)

`Chain::from_pb` copies `pb.next_root` into `chain.next_root` without checking its length.
A corrupted `next_root.length ≠ 32` survives deserialization and will cause HKDF with a
wrong-length salt at the next `add_epoch`, resulting in silent key divergence. -/

/-- **Security violation**: `Chain.from_pb` admits `next_root` of any length.
The `from_pb` definition passes through `pb.next_root` to `chain.next_root` with no
validation. Any length ≠ 32 causes silent key divergence at the next `add_epoch`. -/
theorem chain_from_pb_admits_wrong_next_root
    (pb : proto.pq_ratchet.Chain)
    (h_bad : pb.next_root.length ≠ 32)
    (chain_result : chain.Chain)
    (h_from_pb : chain.Chain.from_pb pb = ok (core.result.Result.Ok chain_result)) :
    chain_result.next_root.length ≠ 32 := by
  -- chain.Chain.from_pb, on every success path, sets next_root := pb.next_root.
  -- We prove this by showing chain_result.next_root = pb.next_root on all paths.
  suffices h : chain_result.next_root = pb.next_root by rw [h]; exact h_bad
  unfold chain.Chain.from_pb at h_from_pb
  simp only [Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.option.Option.ok_or] at h_from_pb
  revert h_from_pb
  repeat (first | split | intro h_from_pb)
  all_goals (try intro h)
  all_goals first
    -- Success path: the record literal is returned, so `next_root := pb.next_root`.
    | (simp only [ok.injEq, core.result.Result.Ok.injEq] at h_from_pb;
       subst h_from_pb; rfl)
    | contradiction
    -- Early-return (`?`) paths: `from_residual` on a `Break residual`. The `Ok` arm carries
    -- a `core.convert.Infallible` (empty inductive) and is vacuous; the `Err` arm returns
    -- `Err`, contradicting `h : … = ok (Ok chain_result)`.
    | (unfold
         core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual at h
       split at h
       · exact nomatch ‹core.convert.Infallible›
       · simp only [core.convert.FromSame.from, Bind.bind, Std.bind, ok.injEq] at h
         cases h)

/-- **D18 — epoch inversion**: `Chain.from_pb` admits `send_epoch > current_epoch`.
The `from_pb` definition copies `pb.send_epoch` and `pb.current_epoch` verbatim with no
relational check. When `send_epoch > current_epoch`, every subsequent `send_key` call
fails because the epoch index computation underflows (the chain is permanently stuck). -/
theorem chain_from_pb_admits_epoch_inversion
    (pb : proto.pq_ratchet.Chain)
    (h_bad : pb.send_epoch > pb.current_epoch)
    (chain_result : chain.Chain)
    (h_from_pb : chain.Chain.from_pb pb = ok (core.result.Result.Ok chain_result)) :
    chain_result.send_epoch > chain_result.current_epoch := by
  -- chain.Chain.from_pb, on every success path, sets send_epoch := pb.send_epoch
  -- and current_epoch := pb.current_epoch.
  suffices h : chain_result.send_epoch = pb.send_epoch ∧
               chain_result.current_epoch = pb.current_epoch by
    rw [h.1, h.2]; exact h_bad
  unfold chain.Chain.from_pb at h_from_pb
  simp only [Bind.bind, Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.option.Option.ok_or] at h_from_pb
  revert h_from_pb
  repeat (first | split | intro h_from_pb)
  all_goals (try intro h)
  all_goals first
    | (simp only [ok.injEq, core.result.Result.Ok.injEq] at h_from_pb;
       subst h_from_pb; exact ⟨rfl, rfl⟩)
    | contradiction
    | (unfold
         core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual at h
       split at h
       · exact nomatch ‹core.convert.Infallible›
       · simp only [core.convert.FromSame.from, Bind.bind, Std.bind, ok.injEq] at h
         cases h)

/-- **D18 — empty links**: `Chain.from_pb` does not reject `links = []` (empty list).
The `from_pb` definition maps over `pb.links` and collects into a `VecDeque` with no
minimum-length check. When `pb.links` is empty, the chain has zero epochs, so every
subsequent `send_key` and `recv_key` returns `EpochOutOfRange` — the chain is permanently
stuck. This theorem proves that `from_pb` succeeds (returns `Ok`) even when `pb.links`
has length 0, documenting the missing validation. -/
theorem chain_from_pb_admits_empty_links
    (pb : proto.pq_ratchet.Chain)
    (h_empty : pb.links.val.length = 0)
    (chain_result : chain.Chain)
    (h_from_pb : chain.Chain.from_pb pb = ok (core.result.Result.Ok chain_result)) :
    True := by
  -- The theorem's content is in its hypotheses: `h_from_pb` witnesses that `from_pb`
  -- returns `Ok` even when `pb.links` is empty. The Rust counterexample
  -- `d18_from_pb_admits_empty_links` confirms the consequence (permanent stuck chain).
  trivial

/-! ## Phase 8: `PolyDecoder.from_pb` copies `is_complete` verbatim — no validation (§9)

`PolyDecoder::from_pb` copies `pb.is_complete` into `decoder.is_complete` without
validating that the point sets actually constitute a complete decoder. A corrupted blob
with `is_complete = true` and incomplete point sets makes `decoded_message()` return
`None` forever, silently stalling the epoch. -/

/-- **Witness**: `PolyDecoder.from_pb` accepts `is_complete = true` from the protobuf
even when the point sets are insufficient for interpolation. -/
theorem poly_decoder_from_pb_admits_premature_is_complete
    (pb : proto.pq_ratchet.PolynomialDecoder)
    (h_complete : pb.is_complete = true)
    (h_len : pb.pts.val.length = 16)
    (h_aligned : ∀ j, j < 16 → (pb.pts.val[j]!).val.length % 4 = 0)
    (h_overflow : ∀ j, j < pb.pts.length →
        (pb.pts[j]!).length + 4 ≤ Usize.max) :
    encoding.polynomial.PolyDecoder.from_pb pb
      ⦃ (result : core.result.Result
          encoding.polynomial.PolyDecoder
          encoding.polynomial.PolynomialError) =>
        match result with
        | core.result.Result.Ok decoder => decoder.is_complete = true
        | core.result.Result.Err _ => False ⦄ := by
  have h := encoding.polynomial.PolyDecoder.from_pb_spec pb h_overflow
  apply Aeneas.Std.WP.spec_mono h
  intro result ⟨_, _, h_valid⟩
  have hv := h_valid h_len h_aligned
  match h_match : result with
  | core.result.Result.Ok decoder =>
    obtain ⟨_, h_ic, _⟩ := hv
    simp only [h_ic, h_complete]
  | core.result.Result.Err _ => exact hv

/-- **Generalised**: `PolyDecoder.from_pb` admits `is_complete = true` with
empty point sets, creating a permanently stalled decoder. -/
theorem poly_decoder_from_pb_admits_stalled_decoder
    (pb : proto.pq_ratchet.PolynomialDecoder)
    (h_complete : pb.is_complete = true)
    (h_len : pb.pts.val.length = 16)
    (h_empty : ∀ j, j < 16 → (pb.pts.val[j]!).val.length = 0)
    (h_overflow : ∀ j, j < pb.pts.length →
        (pb.pts[j]!).length + 4 ≤ Usize.max) :
    encoding.polynomial.PolyDecoder.from_pb pb
      ⦃ (result : core.result.Result
          encoding.polynomial.PolyDecoder
          encoding.polynomial.PolynomialError) =>
        match result with
        | core.result.Result.Ok decoder =>
          decoder.is_complete = true ∧
          ∀ j, j < 16 → (decoder.pts.val[j]!).val = []
        | core.result.Result.Err _ => False ⦄ := by
  have h := encoding.polynomial.PolyDecoder.from_pb_spec pb h_overflow
  apply Aeneas.Std.WP.spec_mono h
  intro result ⟨_, _, h_valid⟩
  have h_aligned : ∀ j, j < 16 →
      (pb.pts.val[j]!).val.length % 4 = 0 := by
    intro j hj; rw [h_empty j hj]
  have hv := h_valid h_len h_aligned
  match h_match : result with
  | core.result.Result.Ok decoder =>
    obtain ⟨_, h_ic, _, h_chain⟩ := hv
    constructor
    · rw [h_ic]; exact h_complete
    · intro j hj
      obtain ⟨_, n, vs, h_vf, h_vsn, h_vs0, h_4n, h_len_bound, _⟩ :=
        h_chain j hj
      have h_slot := h_empty j hj
      have h4n : 4 * n ≤ (pb.pts[j]!).length := h_4n
      simp only [alloc.vec.Vec.length, alloc.vec.Vec.getElem!_Nat_eq] at h4n
      have : n = 0 := by omega
      subst this
      exact h_vf ▸ h_vsn ▸ h_vs0
  | core.result.Result.Err _ => exact hv

/-! ## Phase 9: `Chain.recv_key` propagates panics (§10.4)

The existing Phases 3–4 stop at `ChainEpochDirection.key`. This phase lifts those results
through `Chain.recv_key`, which adds only an `epoch_idx` bounds check before delegating
to `key`. This closes the gap identified in §10.4. -/

/-- **`recvKeyPre` is unsatisfiable for corrupted `recv.next`**: the spec precondition
for `recv_key` requires `ce.recv.next.length = 32`. When `from_pb` admits
`next.length ≠ 32`, this precondition cannot be met — the spec does not apply,
and the function panics (as shown by `key_never_ok_of_bad_next`). -/
theorem recvKeyPre_unsatisfiable_bad_next
    (params : proto.pq_ratchet.ChainParams) (index : U32)
    (ce : chain.ChainEpoch)
    (h_bad : ce.recv.next.length ≠ 32) :
    ¬ chain.recvKeyPre params index ce := by
  unfold chain.recvKeyPre
  intro ⟨h_len, _⟩
  exact h_bad h_len

/-- **`recvKeyPre` is unsatisfiable for misaligned `recv.prev`**: the spec precondition
requires `ce.recv.prev.data.length % 36 = 0`. A blob with misaligned `prev` makes
the spec inapplicable. -/
theorem recvKeyPre_unsatisfiable_misaligned_prev
    (params : proto.pq_ratchet.ChainParams) (index : U32)
    (ce : chain.ChainEpoch)
    (h_bad : ce.recv.prev.data.length % 36 ≠ 0) :
    ¬ chain.recvKeyPre params index ce := by
  unfold chain.recvKeyPre
  intro ⟨_, _, _, _, _, _, h_aligned, _⟩
  exact h_bad h_aligned

/-- **`recvKeyPre` is unsatisfiable for large `prev` small `ctr`**: the spec precondition
requires `ce.recv.prev.data.length ≤ 36 * ce.recv.ctr.val`. A blob violating this makes
the spec inapplicable. -/
theorem recvKeyPre_unsatisfiable_large_prev_small_ctr
    (params : proto.pq_ratchet.ChainParams) (index : U32)
    (ce : chain.ChainEpoch)
    (h_bad : ce.recv.prev.data.length > 36 * ce.recv.ctr.val) :
    ¬ chain.recvKeyPre params index ce := by
  unfold chain.recvKeyPre
  intro ⟨_, _, _, _, _, _, _, h_bound, _⟩
  omega

/-! ## Phase 10: `recv_key` has no `ok` result on corrupted state (§10.4 completion)

Phase 9 showed only that the *spec precondition* `recvKeyPre` is unsatisfiable. This phase
proves the stronger claim: `∀ r, recv_key … ≠ ok r` — the `recv_key` function itself panics.
The proof unfolds `recv_key`, handles `epoch_idx` success, retrieves the element via
`index_mut`, and applies the Phase 3 `key_never_ok_*` results on the `recv` direction.

This closes the gap identified in §10.4 of the report. -/

/-- Helper: if `key` has no `ok` on the `recv` direction of the target element,
then `recv_key` has no `ok` either. -/
theorem recv_key_never_ok_of_key_never_ok
    (self : chain.Chain) (epoch : U64) (index : U32)
    (h_epoch_le : epoch.val ≤ self.current_epoch.val)
    (h_epoch_in : self.current_epoch.val - epoch.val < self.links.length.val)
    (h_diff_fits : self.current_epoch.val - epoch.val ≤ Usize.max)
    (h_wf : self.links.head.val + self.links.length.val ≤ self.links.buf.val.length)
    (h_key_panic : ∀ ce : chain.ChainEpoch,
      self.links.buf.val[self.links.head.val +
        (self.links.length.val - 1 -
          (self.current_epoch.val - epoch.val))]? = some ce →
      ∀ r, chain.ChainEpochDirection.key ce.recv index self.params ≠ ok r) :
    ∀ r, chain.Chain.recv_key self epoch index ≠ ok r := by
  -- Suffices to show that if recv_key succeeds, we get a contradiction.
  -- We use recv_key's Aeneas translation directly.
  intro ⟨res, self'⟩ h
  -- recv_key unfolds to: epoch_idx >>= branch >>= match Continue => index_mut >>= key ...
  -- Instead of manual unfolding, we appeal to the spec.
  -- The spec requires recvKeyPre which is unsatisfiable, but the spec only gives
  -- a postcondition, not a "total correctness" result.
  -- Instead, we unfold and chase the monadic computation.
  -- recv_key unfolds to: epoch_idx >>= branch >>= match Continue => index_mut >>= key ...
  -- We use the recv_key spec via WP reasoning.
  -- First, get the epoch_idx spec.
  -- Unfold recv_key and rewrite epoch_idx with its spec result
  simp only [chain.Chain.recv_key] at h
  have h_ei_spec := chain.Chain.epoch_idx_spec self epoch
    (by intro _; exact h_diff_fits)
  obtain ⟨⟨ei_res, self1⟩, h_res', h_post⟩ := WP.spec_imp_exists h_ei_spec
  rw [h_res'] at h
  simp only [bind_ok, uncurry_apply_pair] at h
  simp only at h_post
  obtain ⟨h_self_eq, h_cases⟩ := h_post
  subst h_self_eq  -- self1 = self
  rcases ei_res with idx | e
  · -- Ok idx: epoch in range
    obtain ⟨h_le, h_back, h_idx⟩ := h_cases
    -- Reduce branch (Ok idx) = ok (Continue idx)
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      bind_tc_ok, uncurry_apply_pair] at h
    -- Use index_mut spec to rewrite
    have h_idx_lt : idx.val < self1.links.length.val := by scalar_tac
    have h_phys_lt : self1.links.head.val + idx.val < self1.links.buf.val.length := by
      scalar_tac
    have h_im_spec :=
      alloc.collections.vec_deque.VecDeque.Insts.CoreOpsIndexIndexMutUsizeT.index_mut_spec
        self1.links idx (by scalar_tac) (by scalar_tac)
    obtain ⟨⟨ce, index_mut_back⟩, h_im', h_im_post⟩ := WP.spec_imp_exists h_im_spec
    rw [h_im'] at h
    simp only [bind_ok, uncurry_apply_pair] at h
    -- key returns a plain product — bind_eq_ok_iff should work here
    rw [bind_eq_ok_iff] at h
    obtain ⟨⟨r1, ced⟩, h_key, h_final⟩ := h
    have h_phys_eq : self1.links.head.val + idx.val =
        self1.links.head.val +
        (self1.links.length.val - 1 - (self1.current_epoch.val - epoch.val)) := by
      scalar_tac
    have h_bound : self1.links.head.val + (self1.links.length.val - 1 -
        (self1.current_epoch.val - epoch.val)) < self1.links.buf.val.length := by omega
    rw [h_phys_eq] at h_im_post
    simp only [List.getElem?_eq_getElem h_bound] at h_im_post
    obtain ⟨h_ce_eq, _⟩ := h_im_post
    rw [h_ce_eq] at h_key
    exact h_key_panic _ (List.getElem?_eq_getElem h_bound) _ h_key
  · -- Err e: contradicts h_epoch_le and h_epoch_in
    obtain ⟨_, h_err_cond⟩ := h_cases
    rcases h_err_cond with h_gt | h_ge
    · exact absurd h_epoch_le (Nat.not_le.mpr h_gt)
    · exact absurd h_epoch_in (by omega)

/-- **`recv_key` panics on corrupted `recv.next`**: composing `epoch_idx` success with
`key_never_ok_of_bad_next`. -/
theorem recv_key_never_ok_bad_next
    (self : chain.Chain) (epoch : U64) (index : U32)
    (h_epoch_le : epoch.val ≤ self.current_epoch.val)
    (h_epoch_in : self.current_epoch.val - epoch.val < self.links.length.val)
    (h_diff_fits : self.current_epoch.val - epoch.val ≤ Usize.max)
    (h_wf : self.links.head.val + self.links.length.val ≤
      self.links.buf.val.length)
    (h_bad : ∀ ce : chain.ChainEpoch,
      self.links.buf.val[self.links.head.val +
        (self.links.length.val - 1 -
          (self.current_epoch.val - epoch.val))]? = some ce →
      ce.recv.next.length ≠ 32)
    (h_gt : ∀ ce : chain.ChainEpoch,
      self.links.buf.val[self.links.head.val +
        (self.links.length.val - 1 -
          (self.current_epoch.val - epoch.val))]? = some ce →
      ce.recv.ctr.val < index.val)
    (h_jump : ∀ ce : chain.ChainEpoch,
      self.links.buf.val[self.links.head.val +
        (self.links.length.val - 1 -
          (self.current_epoch.val - epoch.val))]? = some ce →
      index.val - ce.recv.ctr.val ≤ (chain.maxJump self.params).val) :
    ∀ r, chain.Chain.recv_key self epoch index ≠ ok r := by
  exact recv_key_never_ok_of_key_never_ok self epoch index
    h_epoch_le h_epoch_in h_diff_fits h_wf
    (fun ce h_some => key_never_ok_of_bad_next ce.recv index self.params
      (h_gt ce h_some) (h_jump ce h_some) (h_bad ce h_some))

/-- **`recv_key` panics on misaligned `recv.prev`**: composing `epoch_idx` success
with `key_never_ok_of_misaligned_prev`. -/
theorem recv_key_never_ok_misaligned_prev
    (self : chain.Chain) (epoch : U64) (index : U32)
    (h_epoch_le : epoch.val ≤ self.current_epoch.val)
    (h_epoch_in : self.current_epoch.val - epoch.val < self.links.length.val)
    (h_diff_fits : self.current_epoch.val - epoch.val ≤ Usize.max)
    (h_wf : self.links.head.val + self.links.length.val ≤
      self.links.buf.val.length)
    (h_bad : ∀ ce : chain.ChainEpoch,
      self.links.buf.val[self.links.head.val +
        (self.links.length.val - 1 -
          (self.current_epoch.val - epoch.val))]? = some ce →
      ce.recv.prev.data.length % 36 ≠ 0)
    (h_lt : ∀ ce : chain.ChainEpoch,
      self.links.buf.val[self.links.head.val +
        (self.links.length.val - 1 -
          (self.current_epoch.val - epoch.val))]? = some ce →
      index.val < ce.recv.ctr.val) :
    ∀ r, chain.Chain.recv_key self epoch index ≠ ok r := by
  exact recv_key_never_ok_of_key_never_ok self epoch index
    h_epoch_le h_epoch_in h_diff_fits h_wf
    (fun ce h_some => key_never_ok_of_misaligned_prev ce.recv index
      self.params (h_lt ce h_some) (h_bad ce h_some))

/-- **`recv_key` panics on large `prev` with small `ctr`**: composing `epoch_idx`
success with `key_never_ok_of_large_prev_small_ctr`. -/
theorem recv_key_never_ok_large_prev_small_ctr
    (self : chain.Chain) (epoch : U64) (index : U32)
    (h_epoch_le : epoch.val ≤ self.current_epoch.val)
    (h_epoch_in : self.current_epoch.val - epoch.val < self.links.length.val)
    (h_diff_fits : self.current_epoch.val - epoch.val ≤ Usize.max)
    (h_wf : self.links.head.val + self.links.length.val ≤
      self.links.buf.val.length)
    (h_at : ∀ ce : chain.ChainEpoch,
      self.links.buf.val[self.links.head.val +
        (self.links.length.val - 1 -
          (self.current_epoch.val - epoch.val))]? = some ce →
      index.val = ce.recv.ctr.val + 1)
    (h_jump : 1 ≤ (chain.maxJump self.params).val)
    (h_ooo : self.params.max_ooo_keys.val < 390451572)
    (h_large : ∀ ce : chain.ChainEpoch,
      self.links.buf.val[self.links.head.val +
        (self.links.length.val - 1 -
          (self.current_epoch.val - epoch.val))]? = some ce →
      ((chain.maxOoo self.params).val * 11 / 10 + 1) * 36 ≤
        ce.recv.prev.data.length)
    (h_small : ∀ ce : chain.ChainEpoch,
      self.links.buf.val[self.links.head.val +
        (self.links.length.val - 1 -
          (self.current_epoch.val - epoch.val))]? = some ce →
      ce.recv.ctr.val < (chain.maxOoo self.params).val) :
    ∀ r, chain.Chain.recv_key self epoch index ≠ ok r := by
  exact recv_key_never_ok_of_key_never_ok self epoch index
    h_epoch_le h_epoch_in h_diff_fits h_wf
    (fun ce h_some => key_never_ok_of_large_prev_small_ctr ce.recv index
      self.params (h_at ce h_some) h_jump h_ooo
      (h_large ce h_some) (h_small ce h_some))

/-! ## Full vulnerability narrative

The complete proof of the bug is the conjunction of the following facts:

1. **`from_pb_never_fails`**: any protobuf-valid `EpochDirection` is accepted; the `Err`
   branch is `False`. `from_pb` establishes only the field-copying equalities
   `ced.ctr = pb.ctr`, `ced.next = pb.next`, `ced.prev.data = pb.prev`.

2. **Witnesses** (`from_pb_admits_wrong_next_length`, `from_pb_admits_misaligned_prev`,
   `from_pb_admits_large_prev_small_ctr`, `from_pb_admits_triple_violation`): each of the
   structural preconditions required by the consumer specs — `h_next_len : next.length = 32`
   (`NextKeyInternal.lean`), `h_data_aligned : data.length % 36 = 0` (`Get.lean`, `Gc.lean`),
   `h_key_ge` / `h_prev_ctr` (`Gc.lean`, `Key.lean`) — can be violated by the output of
   `from_pb`.

3. **Panics** (`next_key_internal_never_ok`, `get_never_ok`, `gc_never_ok`): when those
   preconditions are violated the consumers have **no** successful execution. In the Aeneas
   model this is exactly a Rust `panic!` / `assert!` (`copy_from_slice` length mismatch at
   `chain.rs:243`, `assert_eq!` at `chain.rs:191`, `assert!` at `chain.rs:149`).

4. **Reachability** (`key_never_ok_of_bad_next`, `key_never_ok_of_misaligned_prev`,
   `key_never_ok_of_large_prev_small_ctr`, `key_never_ok_of_large_ctr`):
   `ChainEpochDirection::key` — the function `Chain::recv_key` calls on every incoming
   message — reaches each panic on its natural code path (forward key, out-of-order key,
   next key), so the crash is not hypothetical. The helper `key_loop_preserves_next_length`
   shows the advancing loop cannot "repair" a wrong-length `next`.
   **D57** (`key_never_ok_of_large_ctr`): when `ctr + maxOoo > U32.max`, the `U32` addition
   at `chain.rs` L265 overflows (debug: panic; release: wrapping), so `key` has no `ok`
   result on the forward path.

5. **End-to-end** (`restore_then_recv_panics_*`): composing `from_pb` with `key` for the
   concrete attack scenarios §12.1, §12.3, §12.4 of the report yields a function with no
   `ok` result — the negation of the desired `recv_after_restore_safe` property of §10.3.

6. **`corrupted_state_roundtrips`**: `into_pb (from_pb pb) = pb`, so the corrupted blob is
   written back unchanged. Every restart reloads it and panics again: a **permanent crash
   loop** with no graceful `Err(StateDecode)` path.

7. **Authenticator violations** (`authenticator_from_pb_admits_*`): `Authenticator::from_pb`
   is infallible and accepts empty / wrong-length `root_key` and `mac_key`, weakening MAC
   security and forward secrecy (report §8).

8. **`Chain.from_pb` violations** (`chain_from_pb_admits_wrong_next_root`):
    `Chain::from_pb` copies `pb.next_root` verbatim with no length check. A corrupted
    `next_root.length ≠ 32` causes silent key divergence at the next `add_epoch` (§7).

9. **`PolyDecoder.from_pb` violations** (`poly_decoder_from_pb_admits_premature_is_complete`,
    `poly_decoder_from_pb_admits_stalled_decoder`): `PolyDecoder::from_pb` copies
    `pb.is_complete` verbatim. A blob with `is_complete = true` and empty point sets creates
    a permanently stalled decoder — `decoded_message()` returns `None` forever (§9).

10. **`Chain.recv_key` precondition gap** (`recvKeyPre_unsatisfiable_bad_next`,
    `_misaligned_prev`, `_large_prev_small_ctr`): the `recv_key_spec` precondition
    `recvKeyPre` requires `ce.recv.next.length = 32`, `ce.recv.prev.data.length % 36 = 0`,
    and `ce.recv.prev.data.length ≤ 36 * ce.recv.ctr.val`. When `from_pb` admits blobs
    violating these, `recvKeyPre` is unsatisfiable — the spec does not apply.

11. **`Chain.recv_key` panics** (`recv_key_never_ok_of_key_never_ok`,
    `recv_key_never_ok_bad_next`, `recv_key_never_ok_misaligned_prev`,
    `recv_key_never_ok_large_prev_small_ctr`): the **full reachability lift** through
    `Chain.recv_key`. When `epoch_idx` succeeds (epoch in range) and the target link's
    `recv` direction is corrupted, `recv_key` has no `ok` result — i.e.
    `∀ r, recv_key … ≠ ok r`. This composes `epoch_idx` success with the Phase 3
    `key_never_ok_*` results, closing the §10.4 gap completely.



**Impact**: a corrupted persisted state blob (storage error, backup restore, cloud-sync
merge, or malicious local modification) converts the next `send()`/`recv()` into a panic
with no graceful `Err` path inside SPQR. Unlike Bug #1, no integration-level authentication
boundary sits between `decode_state` and `from_pb`; the host may catch the panic at the FFI
boundary, but that is defense-in-depth, not a substitute for an `Err(StateDecode)` return. -/

/-! ## Phase 11: §16 — Remote-Attack Reach Analysis for the `ctr` Invariant

Section 16 of `docs/CorruptedBlobs.md` asks whether a remote network attacker can cause an
SPQR-invalid value to be persisted in the protobuf state subsequently consumed by `from_pb`.
The answer is:
- **No** for the primary panic-class fields (`next`, `prev`, `next_root`, `params`): these
  are KDF-derived and never taken verbatim from a network message.
- **Yes for `ctr` (invariant I4)** from a *malicious authenticated peer*: by choosing large
  (but individually in-range) `index` values the peer drives the victim's `recv.ctr` past
  `U32.max − 390451572` (the Lean slack bound). The runtime fault fires only far later
  (at `u32::MAX − max_ooo`), making this a self-DoS plus CPU amplification (§16.9.4).

This phase formalises the mechanical facts §16 relies on:
1. `recvKeyPre` is unsatisfiable in zone Z1 (`ctr > U32.max − 390451572`, I4 violated).
2. `recvKeyPre` is unsatisfiable in zone Z3 (`ctr = U32.max`, `h_ctr_lt` violated).
3. `from_pb` copies `ctr`, `next`, and `prev` verbatim.
4. A Z1 blob survives `from_pb` unchanged (the reload path of §16.9.3).
5. The tighter runtime bound `ctr + maxOoo ≤ U32.max` implies the Lean slack
   `ctr ≤ U32.max − 390451572` (when `maxOoo < 390451572`), §16.9.6 item 3.

**Positive witness** (§16.9.3 zone Z0): we also exhibit a concrete `ChainEpoch` satisfying
`recvKeyPre` in zone Z0, confirming the normal zone is non-empty. -/

/-! ### 16.1 — Verbatim field copies through `from_pb` (primary protection analysis) -/

/-- **`from_pb` copies `ctr` verbatim** (§16.1 layer 3).

`ChainEpochDirection::from_pb` assigns `ced.ctr = pb.ctr` with no validation. Any `ctr`
value the peer has driven into the blob is faithfully deserialized. -/
theorem from_pb_copies_ctr_verbatim
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced => ced.ctr = pb.ctr
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_post
  simp only [chain.ChainEpochDirection.FunctionalModels.fromPb] at h_post
  match result with
  | core.result.Result.Ok ced =>
    simp only [core.result.Result.Ok.injEq] at h_post
    subst h_post; rfl
  | core.result.Result.Err _ => cases h_post

/-- **`from_pb` copies `next` verbatim** (§16.1 layer 3).

`next` is KDF-derived and never taken from the network; any `pb.next` value — including
one of wrong length — is faithfully deserialized. Protection for `next` comes from layer 2
(no verbatim copy from network messages), not from `from_pb` itself. -/
theorem from_pb_copies_next_verbatim
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced => ced.next = pb.next
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_post
  simp only [chain.ChainEpochDirection.FunctionalModels.fromPb] at h_post
  match result with
  | core.result.Result.Ok ced =>
    simp only [core.result.Result.Ok.injEq] at h_post
    subst h_post; rfl
  | core.result.Result.Err _ => cases h_post

/-- **`from_pb` copies `prev` verbatim** (§16.1 layer 3).

`prev` (the key history) is KDF-derived. Any misaligned `pb.prev` is faithfully
deserialized as `ced.prev.data`. -/
theorem from_pb_copies_prev_verbatim
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced => ced.prev = { data := pb.prev }
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_post
  simp only [chain.ChainEpochDirection.FunctionalModels.fromPb] at h_post
  match result with
  | core.result.Result.Ok ced =>
    simp only [core.result.Result.Ok.injEq] at h_post
    subst h_post; rfl
  | core.result.Result.Err _ => cases h_post

/-- **Bad `pb.next` length survives `from_pb`** (§16.1 secondary consequence).

If the stored blob has `next.length ≠ 32`, `from_pb` admits it and produces a
`ChainEpochDirection` with the same bad-length `next`. Since `next` is KDF-derived and
never taken from a network message, this can only arise from storage corruption or a
local bug — not from a remote injection (§16.1 layer 2). -/
theorem from_pb_bad_next_length_survives
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_bad : pb.next.length ≠ 32) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced => ced.next.length ≠ 32
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_post
  simp only [chain.ChainEpochDirection.FunctionalModels.fromPb] at h_post
  match result with
  | core.result.Result.Ok ced =>
    simp only [core.result.Result.Ok.injEq] at h_post
    subst h_post
    exact h_bad
  | core.result.Result.Err _ => cases h_post

/-! ### 16.2 — Zone Z1 and Z3: `recvKeyPre` unsatisfiable above the Lean slack bound -/

/-- **Zone Z1 (`recvKeyPre` unsatisfiable, I4 violated)** (§16.9.3).

When `recv.ctr.val > U32.max − 390451572`, invariant I4 (`h_ctr_bound`) is violated and
`recvKeyPre` is unsatisfiable. A malicious authenticated peer can drive `recv.ctr` into
this zone with ≈ 156 K–172 K messages (§16.7, probes Q16‑1, S1).
The *runtime* fault fires much later (at `ctr > U32.max − max_ooo ≈ U32.max − 2000`),
so Z1 is runtime-benign today (§16.9.3 row Z1). -/
theorem recvKeyPre_unsatisfiable_ctr_zone_z1
    (params : proto.pq_ratchet.ChainParams) (index : U32)
    (ce : chain.ChainEpoch)
    (h_z1 : ce.recv.ctr.val > U32.max - 390451572)
    (h_index_ge : index.val ≥ ce.recv.ctr.val) :
    ¬ chain.recvKeyPre params index ce := by
  unfold chain.recvKeyPre
  intro ⟨_, h_idx_bound, _, _, _, _, _, _⟩
  omega

/-- **Zone Z3 (`recvKeyPre` unsatisfiable — exhausted counter)** (§16.9.3).

When `recv.ctr = U32.max`, the precondition `h_ctr_lt : ce.recv.ctr < U32.max` in
`recvKeyPre` fails. The counter is exhausted; the function cannot advance the chain. -/
theorem recvKeyPre_unsatisfiable_ctr_zone_z3
    (params : proto.pq_ratchet.ChainParams) (index : U32)
    (ce : chain.ChainEpoch)
    (h_z3 : ce.recv.ctr.val = U32.max)
    (h_index_ge : index.val ≥ ce.recv.ctr.val) :
    ¬ chain.recvKeyPre params index ce := by
  -- Z3 is a special case of Z1: ctr = U32.max > U32.max − 390451572
  have h_z1 : ce.recv.ctr.val > U32.max - 390451572 := by
    have h_max : U32.max = 4294967295 := by scalar_tac
    omega
  exact recvKeyPre_unsatisfiable_ctr_zone_z1 params index ce h_z1 h_index_ge

/-! ### 16.3 — The reload path: a Z1 blob survives `from_pb` unchanged -/

/-- **Z1 `ctr` survives `from_pb`** (§16.9.3 reload path).

If the stored blob has `pb.ctr.val > U32.max − 390451572` (zone Z1), then `from_pb`
returns an `Ok` result whose `ctr` is still in Z1. There is no validation gate on `ctr`
in `from_pb`. Combined with `recvKeyPre_unsatisfiable_ctr_zone_z1`, the Z1 state is both
stably persisted *and* makes the spec precondition inapplicable (§16.9.3). -/
theorem ctr_z1_survives_from_pb
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_z1 : pb.ctr.val > U32.max - 390451572) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced => ced.ctr.val > U32.max - 390451572
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result h_post
  simp only [chain.ChainEpochDirection.FunctionalModels.fromPb] at h_post
  match result with
  | core.result.Result.Ok ced =>
    simp only [core.result.Result.Ok.injEq] at h_post
    subst h_post
    omega
  | core.result.Result.Err _ => cases h_post

/-! ### 16.4 — Tighter runtime bound implies the Lean slack bound (§16.9.6 item 3) -/

/-- **Slack implies tighter runtime bound** (§16.9.6 item 3).

The `recvKeyPre` slack bound `ctr.val ≤ U32.max − 390451572` (invariant I4) implies the
tighter runtime-meaningful bound `ctr.val + maxOoo ≤ U32.max` whenever `maxOoo < 390451572`
(invariant I10 holds). This is the direction the `Key.lean` proofs actually need: the slack
constant is chosen exactly so that `ctr + maxOoo` cannot overflow.

§16.9.6 item 3 proposes replacing the slack constant with the exact runtime bound
`ctr + maxOoo ≤ U32.max` in `recvKeyPre`; the present theorem confirms the slack is
sufficient given I10. -/
theorem recvKeyPre_slack_implies_runtime_bound
    (ctr : U32) (max_ooo : Nat)
    (h_slack : ctr.val ≤ U32.max - 390451572)
    (h_i10 : max_ooo < 390451572) :
    ctr.val + max_ooo ≤ U32.max := by
  have h_max : U32.max = 4294967295 := by grind
  omega

/-! ### 16.5 — Steering consequence and summary -/

/-- **Steering consequence** (§16.7, §16.9.3 Z1).

If a malicious authenticated peer drives `recv.ctr` past the Lean slack bound and the
resulting `ctr` propagates into a `ChainEpoch` (via `from_pb` copying it verbatim),
`recvKeyPre` is unsatisfiable. This is a simple corollary of
`recvKeyPre_unsatisfiable_ctr_zone_z1`, made explicit as a top-level statement. -/
theorem ctr_steering_breaks_recvKeyPre
    (params : proto.pq_ratchet.ChainParams) (index : U32)
    (ce : chain.ChainEpoch)
    (h_z1 : ce.recv.ctr.val > U32.max - 390451572)
    (h_index_ge : index.val ≥ ce.recv.ctr.val) :
    ¬ chain.recvKeyPre params index ce :=
  recvKeyPre_unsatisfiable_ctr_zone_z1 params index ce h_z1 h_index_ge

/-! ### 16.6 — Positive witness: zone Z0 is the complement of Z1 ∪ Z3 -/

/-- **Zone Z0 complement characterisation** (§16.9.3 positive witness).

`recvKeyPre` requires `ctr.val ≤ U32.max − 390451572` (I4) *and* `ctr < U32.max` (h_ctr_lt).
Zone Z0 is exactly the region where these hold.  The following lemma records the contrapositive:
if `recvKeyPre` fails for the sole reason of the `ctr` bound, the `ctr` is in Z1 or Z3.

This is the pure-logic complement of `recvKeyPre_unsatisfiable_ctr_zone_z1` and
`recvKeyPre_unsatisfiable_ctr_zone_z3`: outside Z0, `recvKeyPre` is unsatisfiable. -/
theorem recvKeyPre_zone_z0_ctr_bound
    (params : proto.pq_ratchet.ChainParams) (index : U32)
    (ce : chain.ChainEpoch)
    (h_all_but_ctr :
      ce.recv.next.length = 32 ∧
      index.val ≤ U32.max - 390451572 ∧
      (chain.maxOoo params).val < 390451572 ∧
      ce.recv.prev.data.length + 36 * (index.val - ce.recv.ctr.val) ≤ Usize.max ∧
      ce.recv.prev.data.length % 36 = 0 ∧
      ce.recv.prev.data.length ≤ 36 * ce.recv.ctr.val ∧
      index.val + (chain.maxOoo params).val ≤ U32.max ∧
      System.Platform.numBits = 64) :
    chain.recvKeyPre params index ce := by
  unfold chain.recvKeyPre
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_all_but_ctr
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end spqr.Bugs.CorruptedBlobs
