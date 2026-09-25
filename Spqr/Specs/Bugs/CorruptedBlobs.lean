/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Chain.ChainEpochDirection.FromPb
import Spqr.Specs.Chain.ChainEpochDirection.IntoPb
import Spqr.Specs.Chain.ChainEpochDirection.NextKeyInternal
import Spqr.Specs.Chain.KeyHistory.Get
import Spqr.Specs.Chain.KeyHistory.Gc
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb

/-! # Bug #2: Deserialized State Never Validated — Panics from Corrupted Blobs

**Severity**: HIGH

Unlike Bug #1 (chunk poisoning via network messages, mitigated by auth-before-commit),
this bug targets **persisted local state** — no integration-level mitigation exists.

We prove: (1) `from_pb` always succeeds with no validation, (2) corrupted blobs violate
consumer preconditions, (3) corrupted state round-trips through persistence, (4)
`Authenticator::from_pb` accepts arbitrary-length keys.

**Source**: docs/CorruptedBlobs.md, `src/chain.rs` L306–312 -/

open Aeneas Aeneas.Std Result spqr chain.ChainEpochDirection

namespace spqr.Bugs.CorruptedBlobs

/-! ## Phase 1: `from_pb` always succeeds — no validation -/

theorem from_pb_never_fails (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced =>
        ced.ctr = pb.ctr ∧ ced.next = pb.next ∧ ced.prev = { data := pb.prev }
      | core.result.Result.Err _ => False ⦄ := by
  exact chain.ChainEpochDirection.from_pb_spec pb

/-! ## Phase 2: Corrupted blobs violate consumer preconditions -/

/-- **Panic 1**: `next.len() ≠ 32` → panic in `next_key_internal` (`copy_from_slice`). -/
theorem from_pb_admits_wrong_next_length
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_bad : pb.next.length ≠ 32) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced => ced.next.length ≠ 32
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result
  match result with
  | core.result.Result.Ok ced =>
    intro ⟨_, h_next, _⟩
    change ced.next.length ≠ 32
    rw [h_next]; exact h_bad
  | core.result.Result.Err _ => intro h; exact h

/-- **Panic 2**: `prev.len() % 36 ≠ 0` → panic in `KeyHistory::get` (`assert_eq!`). -/
theorem from_pb_admits_misaligned_prev
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_bad : pb.prev.length % 36 ≠ 0) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection spqr.Error) =>
      match result with
      | core.result.Result.Ok ced => ced.prev.data.length % 36 ≠ 0
      | core.result.Result.Err _ => False ⦄ := by
  have h := chain.ChainEpochDirection.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result
  match result with
  | core.result.Result.Ok ced =>
    intro ⟨_, _, h_prev⟩
    change ced.prev.data.length % 36 ≠ 0
    have hpd : ced.prev.data = pb.prev := by
      have := congrArg chain.KeyHistory.data h_prev; simp only at this; exact this
    rw [hpd]; exact h_bad
  | core.result.Result.Err _ => intro h; exact h

/-- **Panic 3**: large `prev` + `ctr = 0` → panic in `KeyHistory::gc` (`assert!`).
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
    intro ⟨h_ctr, _, h_prev⟩
    change ced.ctr = 0#u32 ∧ ced.prev.data.length ≥ 79236
    constructor
    · rw [h_ctr]; exact h_ctr_zero
    · have hpd : ced.prev.data = pb.prev := by
        have := congrArg chain.KeyHistory.data h_prev; simp only at this; exact this
      rw [hpd]; exact h_prev_large
  | core.result.Result.Err _ => intro h; exact h


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
    intro ⟨h_ctr, h_next, h_prev⟩
    change ced.next.length ≠ 32 ∧ ced.prev.data.length % 36 ≠ 0 ∧ ced.ctr = 0#u32
    have hpd : ced.prev.data = pb.prev := by
      have := congrArg chain.KeyHistory.data h_prev; simp only at this; exact this
    exact ⟨by rw [h_next]; exact h_next_bad,
           by rw [hpd]; exact h_prev_bad,
           by rw [h_ctr]; exact h_ctr_zero⟩
  | core.result.Result.Err _ => intro h; exact h

/-! ## Phase 3: Corrupted state round-trips through persistence -/

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

/-! ## Phase 4: `Authenticator::from_pb` accepts arbitrary-length keys -/

/-- `Authenticator::from_pb` always succeeds with no key-length validation. -/
theorem authenticator_from_pb_no_validation
    (pb : proto.pq_ratchet.Authenticator) :
    authenticator.serialize.Authenticator.from_pb pb
      ⦃ (result : authenticator.Authenticator) =>
        result.root_key = pb.root_key ∧ result.mac_key = pb.mac_key ⦄ := by
  exact authenticator.serialize.Authenticator.from_pb_spec pb

/-- **Security violation**: empty `mac_key` → trivial MAC forgery. -/
theorem authenticator_from_pb_admits_empty_mac_key
    (pb : proto.pq_ratchet.Authenticator)
    (h_empty : pb.mac_key.length = 0) :
    authenticator.serialize.Authenticator.from_pb pb
      ⦃ (result : authenticator.Authenticator) =>
        result.mac_key.length = 0 ⦄ := by
  have h := authenticator.serialize.Authenticator.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result ⟨_, h_mac⟩
  rw [h_mac]; exact h_empty

/-- **Security violation**: empty `root_key` → broken forward secrecy. -/
theorem authenticator_from_pb_admits_empty_root_key
    (pb : proto.pq_ratchet.Authenticator)
    (h_empty : pb.root_key.length = 0) :
    authenticator.serialize.Authenticator.from_pb pb
      ⦃ (result : authenticator.Authenticator) =>
        result.root_key.length = 0 ⦄ := by
  have h := authenticator.serialize.Authenticator.from_pb_spec pb
  apply Aeneas.Std.WP.spec_mono h
  intro result ⟨h_root, _⟩
  rw [h_root]; exact h_empty

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
  intro result ⟨h_root, h_mac⟩
  exact ⟨by rw [h_root]; exact h_root_bad,
         by rw [h_mac]; exact h_mac_bad⟩

/-! ## Full vulnerability narrative

1. **`from_pb_never_fails`**: any blob accepted, always `Ok`.
2. **Three chain panic witnesses** + `from_pb_admits_triple_violation`.
3. **`corrupted_state_roundtrips`**: `into_pb ∘ from_pb = id` → permanent crash loop.
4. **Authenticator violations**: empty/wrong-length keys → forgery/broken secrecy.
5. **Precondition gap**: `from_pb` establishes only field-copying equalities;
   consumers require structural invariants (`h_next_len`, `h_data_aligned`, etc.).

**Impact**: corrupted state blob (storage error, backup, malicious modification)
causes unrecoverable panics. No integration-level mitigation exists. -/

end spqr.Bugs.CorruptedBlobs
