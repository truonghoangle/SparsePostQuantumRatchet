/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunkLoopBody0

/-!
# Spec theorem for `PolyDecoder::add_chunk`: loop 0

The extracted Lean function
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop` is the full
point-absorption loop inside `PolyDecoder::add_chunk`.  Given a `Range<usize>` iterator over
`0..16`, the current decoder state `self`, and a `Chunk` (containing a 16-bit chunk index and 32
bytes of evaluation data), the loop repeatedly invokes the per-iteration body
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop.body`, which at each
step:

  1. Calls `next` on the range iterator to obtain the loop index `i ∈ {0, …, 15}`.
  2. Computes a GF(2¹⁶) evaluation point from the chunk's data bytes:
       `x = GF16::new(chunk.index)`                    — the x-coordinate is the chunk index,
       `y = GF16::new((data[2i] << 8) + data[2i+1])`  — the y-coordinate is big-endian decoded.
  3. Conditionally pushes `Pt { x, y }` into `self.pts[i]`:
       - if `chunk.index < necessary_points(self, i)`, or
       - if `self.pts[i].len() < necessary_points(self, i)`,
     the point is pushed via `SortedSet::push`; otherwise the state is unchanged.

**Loop invariant**: after processing iterations up to `iter'`, the decoder state satisfies:

  * `iter'.end = iter.end` — the iterator end is unchanged across iterations.
  * `iter.start.val ≤ iter'.start.val ≤ iter'.end.val` — the cursor only advances and never
    exceeds the iterator end.
  * `self'.pts_needed = self.pts_needed` — the point budget is preserved.
  * `self'.is_complete = self.is_complete` — the completion flag is preserved.
  * Each per-polynomial sorted-set slot's capacity bound is maintained:
    `∀ k, k < 16 → (self'.pts.val[k]!).length + 1 ≤ Usize.max`.
  * Each already-processed slot `k ∈ [iter.start, iter'.start)` has a corresponding GF(2¹⁶)
    evaluation point `p` with `p.x.value = chunk.index` and
    `p.y.value.val = 256 * data[2k] + data[2k+1]`, and either the point was pushed
    (`self'.pts.val[k]!.val = self.pts.val[k]!.val ++ [p]`) or the slot is unchanged.
  * Each not-yet-processed slot `k ∉ [iter.start, iter'.start)` is unchanged:
    `self'.pts.val[k]! = self.pts.val[k]!`.

At loop termination (`iter'.start.val ≥ iter'.end.val`), the decoder's key fields are
unchanged:

  `result.pts_needed = self.pts_needed`
  `result.is_complete = self.is_complete`

Additionally, each slot `k` in the iterator range `[iter.start, iter.end)` has a corresponding
GF(2¹⁶) evaluation point `p` such that `p.x.value = chunk.index` and
`p.y.value.val = 256 * data[2k] + data[2k+1]`, and either the point was pushed
(`result.pts.val[k]!.val = self.pts.val[k]!.val ++ [p]`) or the slot is unchanged.
Slots outside the iterator range remain untouched:
`result.pts.val[k]! = self.pts.val[k]!`.

This directly reflects the Rust loop invariant
  `self.pts.len() == 16 && self.pts_needed == initial_pts_needed`.
(The `pts.len() == 16` part is structural in Lean since `pts : Array (SortedSet Pt) 16#usize`.)

Since `0 ≤ i < 16`, the modular/division decomposition
  `total_idx = chunk.index * 16 + i`,  `poly = total_idx % 16`,  `poly_idx = total_idx / 16`
simplifies to `poly = i` (the loop index) and `poly_idx = chunk.index.val` (the chunk index),
so each iteration touches a distinct slot `i` of the `pts` array.  This means each slot is
extended by at most one point across the entire loop.

The body spec (`body_spec` from `AddChunkLoopBody0.lean`) discharges one step of this loop; this
file lifts it through `loop.spec_decr_nat` (with measure `iter'.end.val − iter'.start.val`) to
give the full loop postcondition.

**Source**: spqr/src/encoding/polynomial.rs (lines 882:8-903:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

/-! ## Spec theorem for the add_chunk point-absorption loop -/

/-- **Spec theorem for
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop`**:

The full point-absorption loop inside `PolyDecoder::add_chunk`.  Given a range iterator `iter`
over loop indices, the current decoder state `self`, and a `Chunk` containing 32 bytes of
evaluation data together with a 16-bit chunk index, the loop drives the body to completion and
returns the updated decoder state.

• The function always succeeds (no panic) provided the preconditions hold: the iterator range end
  does not exceed 16 (`iter.end.val ≤ 16`), the cursor does not exceed the end
  (`iter.start.val ≤ iter.end.val`), the chunk index multiplication does not overflow Usize
  (`chunk.index * 16 + 16 ≤ Usize.max`), and each sorted-set slot in `self.pts` has sufficient
  capacity headroom (`(self.pts.val[k]!).length + 2 ≤ Usize.max`).

• **Loop postcondition**:
  The decoder's key fields are preserved through all iterations:
    `result.pts_needed = self.pts_needed`,
    `result.is_complete = self.is_complete`.

  Each slot `k` in the iterator range `[iter.start, iter.end)` has a corresponding GF(2¹⁶)
  evaluation point `p` constructed from the chunk data:
    `p.x.value = chunk.index`  — the chunk index as a GF(2¹⁶) element,
    `p.y.value.val = 256 * data[2k] + data[2k+1]`  — big-endian decoded y-coordinate.
  and either:
    (a) the point was pushed: `result.pts.val[k]!.val = self.pts.val[k]!.val ++ [p]`, or
    (b) the slot is unchanged: `result.pts.val[k]! = self.pts.val[k]!`.

  Slots outside the iterator range are unchanged:
    `∀ k, k < iter.start.val ∨ iter.end.val ≤ k → result.pts.val[k]! = self.pts.val[k]!`.

  This corresponds to the Rust loop:
  ```rust
  for i in 0usize..16 {
      let total_idx = (chunk.index as usize) * 16 + i;
      let poly = total_idx % 16;       // = i
      let poly_idx = total_idx / 16;   // = chunk.index
      let x = GF16::new(poly_idx as u16);
      let y1 = chunk.data[i * 2] as u16;
      let y2 = chunk.data[i * 2 + 1] as u16;
      let y = GF16::new((y1 << 8) + y2);
      if poly_idx < self.necessary_points(i)
          || self.pts[poly].len() < self.necessary_points(i)
      {
          self.pts[poly].push(Pt { x, y });
      }
  }
  ```

  and the Rust ensures clause:
  ```rust
  #[hax_lib::ensures(|_| future(self).pts_needed == self.pts_needed)]
  ```

This establishes that the full `add_chunk` loop faithfully processes all 16 evaluation points
from the chunk's serialized data and conditionally absorbs them into the decoder's per-polynomial
point sets via the opaque `SortedSet::push` operation, while preserving the decoder's
`pts_needed` and `is_complete` fields, and recording per-slot point absorption.

This follows from composing:
  1. `body_spec`: one step of the loop either terminates (iterator exhausted) or decodes a single
     GF(2¹⁶) evaluation point from the chunk data and conditionally pushes it onto the appropriate
     sorted set, preserving `pts_needed` and `is_complete`.
  2. `loop.spec_decr_nat`: lifts the body spec through the decreasing measure
     `iter'.end.val − iter'.start.val`.

**Source**: spqr/src/encoding/polynomial.rs (lines 882:8-903:9)
-/
@[step]
theorem loop_spec
    (iter : core.ops.range.Range Std.Usize)
    (self : encoding.polynomial.PolyDecoder) (chunk : encoding.Chunk)
    (h_end_le : iter.end.val ≤ 16)
    (h_start_le : iter.start ≤ iter.end)
    (h_idx_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_room : ∀ k, k < 16 →
      (self.pts.val[k]!).length + 2 ≤ Usize.max) :
    add_chunk_loop iter self chunk ⦃ (result : encoding.polynomial.PolyDecoder) =>
      result.pts_needed = self.pts_needed ∧
      result.is_complete = self.is_complete ∧
      (∀ k, iter.start.val ≤ k → k < iter.end →
        ∃ (p : Pt),
          p.x.value = chunk.index ∧
          p.y.value.val = 256 * (chunk.data[k * 2]!) + (chunk.data[k * 2 + 1]!) ∧
          (result.pts.val[k]!.val = self.pts.val[k]!.val ++ [p] ∨
           result.pts.val[k]! = self.pts.val[k]!)) ∧
      (∀ k, k < iter.start.val ∨ iter.end.val ≤ k →
        result.pts.val[k]! = self.pts.val[k]!) ⦄ := by
  unfold add_chunk_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × PolyDecoder) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × PolyDecoder) =>
        let self' := p.2
        p.1.end = iter.end ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ p.1.end.val ∧
        self'.pts_needed = self.pts_needed ∧
        self'.is_complete = self.is_complete ∧
        (∀ k, k < 16 → (self'.pts.val[k]!).length + 1 ≤ Usize.max) ∧
        (∀ k, iter.start.val ≤ k → k < p.1.start.val →
          ∃ (p : Pt),
            p.x.value = chunk.index ∧
            p.y.value.val =
              256 * (chunk.data[k * 2]!) +
              (chunk.data[k * 2 + 1]!) ∧
            (self'.pts.val[k]!.val =
                self.pts.val[k]!.val ++ [p] ∨
             self'.pts.val[k]! = self.pts.val[k]!)) ∧
        (∀ k, k < iter.start.val ∨ p.1.start.val ≤ k →
          self'.pts.val[k]! = self.pts.val[k]!))
  · rintro ⟨iter', self'⟩ ⟨h_end', h_orig_le, h_start_le', h_pts_needed', h_is_complete',
                            h_push_room', h_processed, h_unchanged⟩
    simp only [] at h_end' h_orig_le h_start_le' h_pts_needed' h_is_complete' h_push_room'
                    h_processed h_unchanged ⊢
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_end_le' : iter'.end.val ≤ 16 := by omega
    have h_body := body_spec chunk iter' self' h_end_le' h_idx_overflow
      (fun h => h_push_room' iter'.start.val h)
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done self'' =>
      simp only [] at h_cf ⊢
      obtain ⟨h_eq, h_done⟩ := h_cf
      subst h_eq
      have h_ge : iter'.end.val ≤ iter'.start.val := by scalar_tac
      exact ⟨h_pts_needed', h_is_complete',
             fun k hlo hhi => h_processed k hlo (by omega),
             fun k hk => h_unchanged k (by omega)⟩
    | ControlFlow.cont (iter'', self'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, h_pts_needed1, h_is_complete1,
              p_body, hpx, hpy, h_pts_change⟩ := h_cf
      refine ⟨⟨by rw [h_end1]; exact h_end',
              by omega,
              by grind,
              by rw [h_pts_needed1]; exact h_pts_needed',
              by rw [h_is_complete1]; exact h_is_complete',
              fun k hk => ?_,
              fun k hlo hhi => ?_,
              fun k hk => ?_⟩,
              by grind⟩
      · rcases h_pts_change with ⟨_h_slot, h_other⟩ | h_no_push
        · by_cases hk_eq : k = iter'.start.val
          · subst hk_eq
            simp only [Array.getElem!_Usize_eq] at _h_slot
            have h_unch := h_unchanged iter'.start.val (Or.inr (le_refl _))
            have h_orig := h_push_room iter'.start.val (by omega)
            have h_len_eq : (self'.pts.val[iter'.start.val]!).length =
                           (self.pts.val[iter'.start.val]!).length := by rw [h_unch]
            have h_len_inc : (self''.pts.val[iter'.start.val]!).length =
                            (self'.pts.val[iter'.start.val]!).length + 1 := by
              simp only [alloc.vec.Vec.length]
              have := congr_arg List.length _h_slot
              simp only [List.length_append, List.length_cons, List.length_nil] at this
              omega
            omega
          · have h_ne : Usize.ofNatCore k (by scalar_tac) ≠ iter'.start := by
              grind [UScalar.neq_to_neq_val]
            have h_eq := h_other (Usize.ofNatCore k (by scalar_tac)) h_ne
            simp only [Array.getElem!_Usize_eq, Usize.ofNatCore_val_eq] at h_eq
            simp only [h_eq]
            exact h_push_room' k hk
        · subst h_no_push
          exact h_push_room' k hk
      · by_cases hk_eq : k = iter'.start.val
        · subst hk_eq
          have h_unch := h_unchanged iter'.start.val (Or.inr (le_refl _))
          refine ⟨p_body, hpx, hpy, ?_⟩
          rcases h_pts_change with ⟨h_slot, _⟩ | h_no_push
          · left
            simp only [Array.getElem!_Usize_eq] at h_slot
            rw [h_unch] at h_slot
            exact h_slot
          · right
            rw [h_no_push]
            exact h_unch
        · have h_start_val : iter''.start.val = iter'.start.val + 1 := by scalar_tac
          have hk_lt : k < iter'.start.val := by omega
          obtain ⟨p_old, hpx_old, hpy_old, h_change_old⟩ := h_processed k hlo hk_lt
          refine ⟨p_old, hpx_old, hpy_old, ?_⟩
          rcases h_pts_change with ⟨_, h_other⟩ | h_no_push
          · have h_k_ne : (Usize.ofNatCore k (by scalar_tac)) ≠ iter'.start := by
              grind [UScalar.neq_to_neq_val]
            have h_eq := h_other (Usize.ofNatCore k (by scalar_tac)) h_k_ne
            simp only [Array.getElem!_Usize_eq, Usize.ofNatCore_val_eq] at h_eq
            rcases h_change_old with h_left | h_right
            · left; rw [h_eq]; exact h_left
            · right; rw [h_eq]; exact h_right
          · rw [h_no_push]
            exact h_change_old
      · have h_start_val : iter''.start.val = iter'.start.val + 1 := by scalar_tac
        have h_unch_self' : self'.pts.val[k]! = self.pts.val[k]! := by
          apply h_unchanged
          rcases hk with hlt | hge
          · exact Or.inl hlt
          · exact Or.inr (by omega)
        have h_self''_eq : self''.pts.val[k]! = self'.pts.val[k]! := by
          rcases h_pts_change with ⟨_, h_other⟩ | h_no_push
          · by_cases hk16 : k < 16
            · have h_k_ne : (Usize.ofNatCore k (by scalar_tac)) ≠ iter'.start := by
                grind [UScalar.neq_to_neq_val]
              have h_eq := h_other (Usize.ofNatCore k (by scalar_tac)) h_k_ne
              simp only [Array.getElem!_Usize_eq, Usize.ofNatCore_val_eq] at h_eq
              exact h_eq
            · have hbound'' : self''.pts.val.length ≤ k := by
                have h := self''.pts.property; scalar_tac
              have hbound' : self'.pts.val.length ≤ k := by
                have h := self'.pts.property; scalar_tac
              simp only [List.getElem!_eq_getElem?_getD]
              rw [List.getElem?_eq_none hbound'', List.getElem?_eq_none hbound']
          · rw [h_no_push]
        rw [h_self''_eq]
        exact h_unch_self'
  · exact ⟨rfl, le_refl _, h_start_le, rfl, rfl,
           fun k hk => by have := h_push_room k hk; grind,
           fun k hlo hhi => by grind,
           fun k _ => rfl⟩

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop
