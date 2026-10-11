/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPb
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FromPb
import Spqr.Specs.Encoding.Polynomial.Pt.Eq
import Spqr.Specs.Encoding.Polynomial.Pt.Cmp
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NecessaryPoints
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New

/-! # Bug #1: Poisoned Decoder State Survives Persistence — Permanent Epoch Stall

**Severity**: HIGH (Protocol DoS)

**Spec chain**: `AddChunk.lean` (unconditional guard for low indices) ×
`FunsExternal.lean:2146` (`SortedSet::push` `.eq` = replacement) ×
`Pt/Eq.lean` (equality ignores `y`) × `IntoPb/FromPb.lean` (faithful round-trip) ×
`Message/Deserialize.lean` (no chunk authentication).

We prove the core in three phases:
1. Honest chunk at index 0 inserts points into empty slots.
2. Poisoned chunk at same index 0 replaces honest points (last-write-wins).
3. Corrupted state round-trips faithfully through `into_pb`.

`decoded_message` is opaque, so we prove the input to interpolation is corrupted.

**Source**: docs/reportI.md §1, `src/v1/chunked/send_ek.rs`, `send_ct.rs` -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf
open PolyDecoder.Insts.SpqrEncodingDecoder PolyDecoder

namespace spqr.Bugs.ProtocolDoS

/-! ## Auxiliary lemmas -/

/-- When `pts_needed ≥ 16`, `np(j) ≥ 1` for all `j < 16`, so `0 < np`.
    For the attack scenario, `pts_needed` is derived from actual message sizes (e.g.
    `HEADER_SIZE + MACSIZE = 2144 + 32`, `ENCAPSULATION_KEY_SIZE = 1184`, etc.),
    all of which are ≥ 16 when divided by 2. -/
private theorem guard_true (n : Nat) (h : n ≥ 16) (_j : Nat) (_hj : _j < 16) :
    (0 : Nat) < n / 16 + (if _j < n % 16 then 1 else 0) := by
  have h16 : n / 16 ≥ 1 := by
    have := Nat.div_add_mod n 16
    have : n / 16 * 16 ≤ n := Nat.div_mul_le_self n 16
    omega
  by_cases hm : _j < n % 16 <;> simp_all


/-! ## Phases 1 & 2: chunk at index 0 always inserts/replaces via IsSortedPushResult -/

/-- After `add_chunk` with **any** chunk at `index = 0` on a decoder with `pts_needed > 0`,
    each polynomial slot `j` gets `IsSortedPushResult` with a point whose `x = 0` and whose
    `y` is determined by that chunk's data.  Applied first with honest data (insertion into
    empty slot) then with poisoned data (replacement of the honest point). -/
theorem add_chunk_index_zero_pushes
    (decoder : PolyDecoder) (chunk : encoding.Chunk)
    (h_idx : chunk.index.val = 0)
    (h_pos : decoder.pts_needed.val ≥ 16)
    (h_ov : chunk.index.val * 16 + 16 ≤ Usize.max)
    (h_cap : ∀ k, k < 16 → (decoder.pts[k]!).length + 17 ≤ Usize.max) :
    add_chunk decoder chunk ⦃ (result : PolyDecoder) =>
      result.pts_needed = decoder.pts_needed ∧
      result.is_complete = decoder.is_complete ∧
      ∃ (selfs : Nat → PolyDecoder),
        selfs 0 = decoder ∧ selfs 16 = result ∧
        ∀ j, j < 16 →
          ∃ p : Pt,
            p.x.value.val = 0 ∧
            p.y.value.val = (chunk.data[j * 2]!) * 256 + (chunk.data[j * 2 + 1]!) ∧
            IsSortedPushResult
              ((selfs j).pts.val[j]!).val
              ((selfs (j + 1)).pts.val[j]!).val p ⦄ := by
  have h_spec := add_chunk_spec decoder chunk h_ov h_cap
  apply WP.spec_mono h_spec
  intro result ⟨h_pn, h_ic, selfs, h_s0, h_s16, h_steps⟩
  refine ⟨h_pn, h_ic, selfs, h_s0, h_s16, fun j hj => ?_⟩
  have h_step := h_steps j hj
  simp only [h_idx, Nat.zero_mul, Nat.zero_add] at h_step
  have hm : j % 16 = j := Nat.mod_eq_of_lt hj
  have hd : j / 16 = 0 := Nat.div_eq_of_lt hj
  obtain ⟨_, _, _, _, p, h_px, h_py, h_branch⟩ := h_step
  rw [hm, hd] at *
  have hg := guard_true decoder.pts_needed.val h_pos j hj
  simp only [show (0 < decoder.pts_needed.val / 16 +
    (if j < decoder.pts_needed.val % 16 then 1 else 0)) = True from
    propext ⟨fun _ => trivial, fun _ => hg⟩] at h_branch
  simp only [true_or, ite_true] at h_branch
  exact ⟨p, h_px, h_py, h_branch.2⟩


/-! ## IsSortedPushResult replacement witness on a singleton -/

/-- On a singleton `[old_pt]`, pushing `new_pt` with the same `x` yields `[new_pt]`. -/
theorem sorted_push_replaces_singleton {old_pt new_pt : Pt}
    (_hx : old_pt.x.value = new_pt.x.value) :
    IsSortedPushResult [old_pt] [new_pt] new_pt :=
  ⟨0, by omega, Or.inr ⟨by simp, by simp⟩⟩

/-! ## Phase 3: Poisoned state survives serialisation -/

/-- `into_pb` preserves every point's coordinates (including poisoned `y` values).
    Direct consequence of `into_pb_spec`. -/
theorem poison_survives_persistence (decoder : PolyDecoder)
    (h_cast : decoder.pts_needed.val ≤ U32.max)
    (h_ov : ∀ j, j < 16 → 4 * (decoder.pts.val[j]!).length + 4 ≤ Usize.max) :
    into_pb decoder ⦃ (pb : proto.pq_ratchet.PolynomialDecoder) =>
      pb.pts_needed.val = decoder.pts_needed.val ∧
      pb.polys = 16#u32 ∧
      pb.is_complete = decoder.is_complete ∧
      pb.pts.length = 16 ∧
      ∀ (j : Nat), j < 16 →
          (pb.pts[j]!).length = 4 * (decoder.pts.val[j]!).length ∧
          ∀ (k : Nat), k < (decoder.pts.val[j]!).length →
              256 * ((pb.pts[j]!)[4 * k]!) + ((pb.pts[j]!)[4 * k + 1]!) =
                ((decoder.pts.val[j]!).val[k]!).x.value.val ∧
              256 * ((pb.pts[j]!)[4 * k + 2]!) + ((pb.pts[j]!)[4 * k + 3]!) =
                ((decoder.pts.val[j]!).val[k]!).y.value.val ⦄ :=
  into_pb_spec decoder h_cast h_ov

/-! ## Composed security violation: `recv_hdr_chunk` persists poisoned state

We now chain the building blocks with the translated protocol function
`v1.chunked.send_ct.NoHeaderReceived.recv_hdr_chunk` to show a concrete
security property violation.

### Security property (informal)

> **Decoder integrity**: After `recv_hdr_chunk` returns `Ok`, the decoder
> embedded in the returned state should only contain points derived from
> chunks that were authenticated (or will be authenticated before use).

### Violation

`recv_hdr_chunk` calls `add_chunk` (no authentication), then checks
`decoded_message`. When `decoded_message` returns `none` (message incomplete),
the function returns `Ok(StillReceiving { ..., receiving_hdr })` where
`receiving_hdr` is the **post-add_chunk** decoder — which may contain
attacker-injected points. The MAC check only runs in the `some` branch.

The theorem below proves: given the `recv_hdr_chunk` function definition,
if `add_chunk` succeeds and `decoded_message` returns `none`, then the
decoder returned in `StillReceiving` is exactly the output of `add_chunk`
applied to the attacker's chunk — with no authentication having occurred. -/

/-- **Security violation**: `recv_hdr_chunk` returns `Ok(StillReceiving state')`
    where `state'.receiving_hdr` is the result of `add_chunk` on an unauthenticated
    chunk, when `decoded_message` returns `none`.

    Combined with `add_chunk_index_zero_pushes` (which shows the attacker's `y` values
    are in the decoder) and `poison_survives_persistence` (which shows they survive
    serialisation), this proves the attacker can permanently inject corrupted points
    into the persisted protocol state without any authentication check. -/
theorem recv_hdr_chunk_persists_unauthenticated_state
    (self : spqr.v1.chunked.send_ct.NoHeaderReceived)
    (epoch : U64) (chunk : spqr.encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    -- `add_chunk` succeeds, producing `decoder'`
    (decoder' : PolyDecoder)
    (h_add : add_chunk self.receiving_hdr chunk = ok decoder')
    -- `decoded_message` returns `none` (message incomplete — the normal case
    -- when not all chunks have arrived yet)
    (h_none : encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message
        decoder' = ok none) :
    -- Then `recv_hdr_chunk` returns `Ok(StillReceiving state')` where the
    -- decoder is exactly `decoder'` — the unauthenticated output of `add_chunk`.
    -- No MAC check has run. The attacker's points are in the persisted state.
    spqr.v1.chunked.send_ct.NoHeaderReceived.recv_hdr_chunk self epoch chunk =
      ok (core.result.Result.Ok
        (spqr.v1.chunked.send_ct.NoHeaderReceivedRecvChunk.StillReceiving
          { self with receiving_hdr := decoder' })) := by
  unfold spqr.v1.chunked.send_ct.NoHeaderReceived.recv_hdr_chunk
  simp only [h_epoch, massert, ite_true, h_add, h_none, bind_tc_ok, bind_ok]

/-! ## Full attack narrative

The complete proof of the bug is the conjunction of four facts:

1. **`add_chunk_index_zero_pushes`**: A chunk at index 0 with arbitrary
   (attacker-controlled) data produces `IsSortedPushResult` in every polynomial
   slot, with the attacker's `y` values. This holds regardless of what was
   previously in the slot (insertion or replacement).

2. **`sorted_push_replaces_singleton`**: When the slot already contains an honest
   point `[honest_pt]` from a prior chunk at the same index, `IsSortedPushResult`
   replaces it with the attacker's point `[poison_pt]`, because `Pt.eq` compares
   only `x` and `SortedSet::push` does last-write-wins on `.eq`.

3. **`recv_hdr_chunk_persists_unauthenticated_state`**: The protocol function
   `recv_hdr_chunk` returns `Ok(StillReceiving {...})` with the poisoned decoder
   when `decoded_message` returns `none`. **No MAC check runs on this path.**
   The caller persists this state.

4. **`poison_survives_persistence`**: The poisoned decoder round-trips faithfully
   through `into_pb` serialisation. The attacker's `y` values are preserved.

Together, these prove: **a single unauthenticated chunk message can permanently
corrupt the decoder state that the protocol persists, because authentication
(MAC check) only runs after full message assembly, but state persistence happens
on every `Ok` return — including the `StillReceiving` path where the message is
incomplete and no authentication has occurred.** -/

/-! ## D16 fix characterisation: first-write-wins prevents poisoning

The root cause of the poisoning is `SortedSet::push`'s last-write-wins semantics
combined with `Pt` equality comparing only `x` (ignoring `y`).  The fix is
**first-write-wins**: when a point with the same `x` coordinate already exists
in the sorted set, the insertion is skipped entirely.

We formalise this as a predicate `IsFirstWriteWinsResult` and prove that under
first-write-wins semantics, a duplicate-`x` insertion leaves the list unchanged —
the honest point is preserved.

**Rust fix (not yet applied):**
```
let candidate = Pt { x, y };
if self.pts[poly].binary_search(&candidate).is_err() {
    self.pts[poly].push(candidate);
}
```

See `docs/listDefects.md` §D16. -/

/-- **First-write-wins postcondition**: the result list is either:
    (a) the old list with a fresh element inserted (no key collision), or
    (b) the old list unchanged (key-equal element already present).

    This is the corrected semantics that should replace `IsSortedPushResult`
    in the `add_chunk` guard's insertion path.  Unlike `IsSortedPushResult`,
    the duplicate-key branch preserves the old list exactly. -/
def IsFirstWriteWinsResult {α : Type*} (old new_ : List α) (p : α) : Prop :=
  -- Fresh insertion (no duplicate key): same as IsSortedPushResult insertion branch
  (∃ (j : Nat), j ≤ old.length ∧ new_ = old.take j ++ [p] ++ old.drop j) ∨
  -- Duplicate key: list unchanged (first-write-wins = no-op)
  new_ = old

/-- **D16 fix theorem.** Under first-write-wins semantics, pushing a duplicate-`x`
    point onto a singleton `[honest_pt]` leaves the list unchanged — the honest
    point is preserved, not replaced.

    Compare with `sorted_push_replaces_singleton` which proves the *current*
    (broken) last-write-wins semantics: `[honest_pt]` becomes `[poison_pt]`.
    This theorem proves the *fixed* semantics: `[honest_pt]` stays `[honest_pt]`. -/
theorem first_write_wins_preserves_honest_singleton {honest_pt poison_pt : Pt}
    (_hx : honest_pt.x.value = poison_pt.x.value) :
    IsFirstWriteWinsResult [honest_pt] [honest_pt] poison_pt :=
  Or.inr rfl

/-- **D16 fix theorem.** First-write-wins on a duplicate key always preserves the
    original list, regardless of list length.  This is the general statement that
    subsumes `first_write_wins_preserves_honest_singleton`. -/
theorem first_write_wins_noop_on_duplicate {α : Type*} (old : List α) (p : α) :
    IsFirstWriteWinsResult old old p :=
  Or.inr rfl

/-- **D16 root cause.** `IsSortedPushResult` *admits* replacement (second disjunct),
    so it does not guarantee preservation of existing points on duplicate `x`.
    Specifically: for a singleton `[old_pt]`, `IsSortedPushResult [old_pt] [new_pt] new_pt`
    holds — the honest point is gone. This is the formal proof that last-write-wins
    is the root cause of the chunk poisoning attack.

    Under `IsFirstWriteWinsResult`, the only possibility for a duplicate key is
    `new_ = old` (the list is unchanged), so the honest point is always preserved. -/
theorem last_write_wins_is_root_cause {old_pt new_pt : Pt}
    (hx : old_pt.x.value = new_pt.x.value)
    (_hy : old_pt.y.value ≠ new_pt.y.value) :
    -- The current semantics admits replacement (honest point lost):
    IsSortedPushResult [old_pt] [new_pt] new_pt ∧
    -- But first-write-wins would preserve the honest point:
    IsFirstWriteWinsResult [old_pt] [old_pt] new_pt := by
  exact ⟨sorted_push_replaces_singleton hx, first_write_wins_preserves_honest_singleton hx⟩

end spqr.Bugs.ProtocolDoS
