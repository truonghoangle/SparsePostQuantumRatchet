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

/-! # Bug #2: Deserialized Chain State Never Validated — Panics from Corrupted Blobs

**Severity**: HIGH

**Spec chain**: `ChainEpochDirection/FromPb.lean` (no validation) ×
`NextKeyInternal.lean` (requires `next.length = 32`) ×
`KeyHistory/Get.lean` (requires `data.length % 36 = 0`) ×
`KeyHistory/Gc.lean` (requires `max_ooo ≤ current_key`).

We prove:
1. `from_pb` accepts **any** protobuf blob without validation (always `Ok`).
2. Concrete corrupted blobs violate each consumer's precondition.
3. Round-trip `into_pb ∘ from_pb` is identity — corrupted state persists faithfully.

**Source**: docs/reportI.md §2, `src/chain.rs` L306–312 -/

open Aeneas Aeneas.Std Result spqr chain.ChainEpochDirection

namespace spqr.Bugs.CorruptedBlobs

/-! ## Phase 1: `from_pb` always succeeds — no validation -/

/-- `from_pb` never returns `Err`. Any protobuf blob passes through unchecked.
    The spec `from_pb_spec` proves the inner `core.result.Result` is always `Ok`;
    we lift this into an existential for convenient downstream use. -/
theorem from_pb_never_fails (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection Error) =>
      match result with
      | core.result.Result.Ok ced =>
        ced.ctr = pb.ctr ∧ ced.next = pb.next ∧ ced.prev = { data := pb.prev }
      | core.result.Result.Err _ => False ⦄ := by
  exact chain.ChainEpochDirection.from_pb_spec pb

/-! ## Phase 2: Concrete corrupted blobs violate consumer preconditions -/

/-- **Panic 1**: `next.len() ≠ 32` → panic in `next_key_internal` at `copy_from_slice`
    (Rust L243). Precondition `h_next_len : next.length = 32` violated.

    `from_pb` accepts a blob with `next` of arbitrary length (here 16). The resulting
    `ced.next.length = 16 ≠ 32`, but `next_key_internal_spec` requires
    `h_next_len : next.length = 32`. The Rust code panics at
    `next.copy_from_slice(&genr8r[..32])`. -/
theorem from_pb_admits_wrong_next_length
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_bad : pb.next.length = 16) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection Error) =>
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
    rw [h_next]; omega
  | core.result.Result.Err _ => intro h; exact h

/-- **Panic 2**: `prev.len() % 36 ≠ 0` → panic in `KeyHistory::get` at `assert_eq!`
    (Rust L191). Precondition `h_data_aligned : self.data.length % 36 = 0` violated. -/
theorem from_pb_admits_misaligned_prev
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_bad : pb.prev.length % 36 ≠ 0) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection Error) =>
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
    rw [h_prev]; exact h_bad
  | core.result.Result.Err _ => intro h; exact h

/-- **Panic 3**: large `prev` + small `ctr` → panic in `KeyHistory::gc` at `assert!`
    (Rust L149). `ctr = 0 < 2000 = max_ooo`, but `data.len() ≥ trim_threshold`.
    79236 = `(2000 * 11 / 10 + 1) * 36`, the default trim threshold. -/
theorem from_pb_admits_large_prev_small_ctr
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (h_ctr_zero : pb.ctr = 0#u32)
    (h_prev_large : pb.prev.length ≥ 79236) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection Error) =>
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
    exact ⟨by rw [h_ctr]; exact h_ctr_zero, by rw [h_prev]; exact h_prev_large⟩
  | core.result.Result.Err _ => intro h; exact h

/-! ## Phase 3: Corrupted state round-trips faithfully through persistence -/

/-- `into_pb (from_pb pb)` produces the original `pb` — corrupted state survives
    a save/load cycle unchanged. The invalid fields are never corrected or sanitised. -/
theorem corrupted_state_roundtrips
    (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection Error) =>
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

/-! ## Full vulnerability narrative

The complete proof is the conjunction of three facts:

1. **`from_pb_never_fails`**: `from_pb` accepts any blob, always returns `Ok`.

2. **Three panic witnesses**:
   - `from_pb_admits_wrong_next_length`: `next.length ≠ 32` → panic in `next_key_internal`
   - `from_pb_admits_misaligned_prev`: `prev.length % 36 ≠ 0` → panic in `KeyHistory::get`
   - `from_pb_admits_large_prev_small_ctr`: large prev + small ctr → panic in `KeyHistory::gc`

3. **`corrupted_state_roundtrips`**: `into_pb ∘ from_pb = id`, so corrupted state
   re-persists on save → **permanent crash loop** on every restart. -/

end spqr.Bugs.CorruptedBlobs
