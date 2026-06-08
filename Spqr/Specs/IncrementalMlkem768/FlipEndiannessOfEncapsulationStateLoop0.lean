/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Specs.IncrementalMlkem768.FlipEndiannessOfEncapsulationStateLoopBody0

/-!
# Spec theorem for `flip_endianness_of_encapsulation_state`: loop 0

The Rust function `flip_endianness_of_encapsulation_state` (in `src/incremental_mlkem768.rs`,
lines 143:0-151:1) takes an `EncapsulationState` (`Vec<u8>`) and byte-swaps each consecutive
pair of bytes in the first `len − 32` positions, correcting an endianness mismatch
(cryspen/libcrux#1275).

This file specifies **loop 0** — the full byte-swap loop (lines 147:4-149:5).  The extracted
Lean function `incremental_mlkem768.flip_endianness_of_encapsulation_state_loop` repeatedly
invokes the loop body (`flip_endianness_of_encapsulation_state_loop.body`), which at each step:

  1. Calls `IteratorStepBy.next` on the step-by-2 iterator over the range `0..(len − 32)`.
  2. If the iterator yields an index `i`, swaps `fixed_es[i]` and `fixed_es[i + 1]`.
  3. If the iterator is exhausted, returns the byte vector unchanged.

**Loop invariant**: after processing iterations up to `iter'`, the byte vector satisfies:

  * `fixed_es'.length = fixed_es.length` — the vector length is preserved.
  * `iter'.iter.«end» = iter.iter.«end»` — the inner range's end is unchanged.
  * `iter'.step_by = iter.step_by` — the step size is unchanged.
  * `iter'.iter.start.val % 2 = 0` — the inner range's start remains even.
  * For every even `j ∈ [iter.iter.start.val, iter'.iter.start.val)`:
      `fixed_es'.val[j]? = fixed_es.val[j + 1]?`  and
      `fixed_es'.val[j + 1]? = fixed_es.val[j]?`
  * For every `j ≥ iter'.iter.start.val`:
      `fixed_es'.val[j]? = fixed_es.val[j]?`
  * For every `j < iter.iter.start.val`:
      `fixed_es'.val[j]? = fixed_es.val[j]?`

At loop termination (`iter'.iter.start.val ≥ iter'.iter.«end».val`), the invariant implies
the full postcondition: every even-indexed byte pair `(j, j+1)` for
`iter.iter.start.val ≤ j < iter.iter.«end».val` has been swapped, and all positions outside
the range are untouched.

The proof lifts the body through `loop.spec_decr_nat` with measure
`iter'.iter.«end».val − iter'.iter.start.val`, maintaining the byte-swap invariant.

**Source**: spqr/src/incremental_mlkem768.rs (lines 147:4-149:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768.flip_endianness_of_encapsulation_state_loop

/--
Helper lemma: `skipN` on a `Range<usize>` iterator preserves the range's `end` field and
yields a `start` that is at least as large as the original.

By induction on `n`: each `IteratorRange.next` either advances `start` by 1 (when
`start < end`) or leaves it unchanged (when `start ≥ end`), and always preserves `end`.
-/
private theorem skipN_Range_Usize_props
    (range : core.ops.range.Range Std.Usize) (n : Nat) :
    ∀ range', core.iter.adapters.step_by.skipN
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      range n = ok range' →
      range'.«end» = range.«end» ∧ range'.start.val ≥ range.start.val := by
  induction n generalizing range with
  | zero =>
    intro range' h
    simp only [core.iter.adapters.step_by.skipN] at h
    grind
  | succ n ih =>
    intro range' h
    simp only [core.iter.adapters.step_by.skipN] at h
    obtain ⟨opt, range1, hnext, h_none, h_some⟩ :=
      core.iter.range.IteratorRange.next_Usize_spec range
    rw [hnext] at h; simp only [bind_tc_ok] at h
    cases opt with
    | none =>
      -- When next returns none, skipN returns range1 immediately
      simp only at h
      have h_not_lt : ¬(range.start.val < range.«end».val) := by
        intro hlt; exact absurd (h_some hlt).1 (by simp)
      obtain ⟨_, heq⟩ := h_none h_not_lt
      grind
    | some _ =>
      -- When next returns some, skipN recurses with range1 for n steps
      simp only at h
      have h_lt : range.start.val < range.«end».val := by
        by_contra hlt
        grind
      obtain ⟨_, h_start1, h_end1⟩ := h_some h_lt
      obtain ⟨h_end', h_ge'⟩ := ih range1 range' h
      exact ⟨by rw [h_end', h_end1], by omega⟩

/--
Helper lemma: when the remaining range has room (`start + n ≤ end`), `skipN n` advances
`start` by exactly `n` and preserves `end`.

This gives the precise post-state of the inner range iterator after the skip portion of
`IteratorStepBy.next`, enabling the loop proof to track the iterator advance exactly.
-/
private theorem skipN_Range_Usize_advance
    (range : core.ops.range.Range Std.Usize) (n : Nat)
    (h_le : range.start.val + n ≤ range.«end».val) :
    ∃ range', core.iter.adapters.step_by.skipN
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      range n = ok range' ∧
      range'.«end» = range.«end» ∧
      range'.start.val = range.start.val + n := by
  induction n generalizing range with
  | zero => exact ⟨range, rfl, rfl, by omega⟩
  | succ n ih =>
    simp only [core.iter.adapters.step_by.skipN]
    obtain ⟨opt, range1, hnext, h_none, h_some⟩ :=
      core.iter.range.IteratorRange.next_Usize_spec range
    rw [hnext]; simp only [bind_tc_ok]
    -- Since start + (n+1) ≤ end, we have start < end
    have h_lt : range.start.val < range.«end».val := by omega
    cases opt with
    | none =>
      -- Contradiction: start < end but next returned none
      exfalso; exact absurd (h_none (by grind)).1 ((h_some h_lt).1 ▸ by grind)
    | some _ =>
      simp only
      obtain ⟨_, h_start1, h_end1⟩ := h_some h_lt
      have h_le' : range1.start.val + n ≤ range1.«end».val := by
        rw [h_start1, h_end1]; omega
      obtain ⟨range', h_skip, h_end', h_start'⟩ := ih range1 h_le'
      exact ⟨range', h_skip, by rw [h_end', h_end1], by rw [h_start', h_start1]; omega⟩

/-- **Spec theorem for `incremental_mlkem768.flip_endianness_of_encapsulation_state_loop`**:

The full byte-swap loop of `flip_endianness_of_encapsulation_state`.  Given the step-by-2
iterator `iter` (wrapping a `Range<usize>` over `0..(len − 32)`) and the initial byte vector
`fixed_es`, the loop repeatedly invokes the body — which swaps the bytes at positions `i` and
`i + 1` for each yielded even index `i` — until the iterator is exhausted.

Requires:
  • `iter.iter.«end».val + 1 ≤ fixed_es.length` — positions `i` and `i + 1` are valid whenever
    the iterator yields `i`.
  • `iter.iter.start.val ≤ iter.iter.«end».val` — the range is non-inverted.
  • `iter.iter.start.val % 2 = 0` and `iter.iter.«end».val % 2 = 0` — start and end are even,
    ensuring the step-by-2 advance stays aligned.
  • `iter.step_by.val = 2` — the step-by parameter matches the Rust `step_by(2)`.

Postcondition on the returned `result : alloc.vec.Vec Std.U8`:
  - **Length preservation**: `result.length = fixed_es.length`.
  - **Byte-swap**: for every even `j` with `iter.iter.start.val ≤ j < iter.iter.«end».val`:
      `result.val[j]? = fixed_es.val[j + 1]?`
      `result.val[j + 1]? = fixed_es.val[j]?`
  - **Frame (ahead)**: for every `j ≥ iter.iter.«end».val`:
      `result.val[j]? = fixed_es.val[j]?`
  - **Frame (behind)**: for every `j < iter.iter.start.val`:
      `result.val[j]? = fixed_es.val[j]?`

**Source**: spqr/src/incremental_mlkem768.rs (lines 147:4-149:5)
-/
@[step]
theorem loop_spec
    (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
    (fixed_es : alloc.vec.Vec Std.U8)
    (h_in_bounds : iter.iter.«end».val + 1 ≤ fixed_es.length)
    (h_start_le : iter.iter.start.val ≤ iter.iter.«end».val)
    (h_start_even : iter.iter.start.val % 2 = 0)
    (h_end_even : iter.iter.«end».val % 2 = 0)
    (h_step : iter.step_by.val = 2) :
    flip_endianness_of_encapsulation_state_loop iter fixed_es ⦃ (result : alloc.vec.Vec Std.U8) =>
      result.length = fixed_es.length ∧
      (∀ j, iter.iter.start.val ≤ j → j < iter.iter.«end».val → j % 2 = 0 →
        result.val[j]? = fixed_es.val[j + 1]? ∧
        result.val[j + 1]? = fixed_es.val[j]?) ∧
      (∀ j, j ≥ iter.iter.«end».val →
        result.val[j]? = fixed_es.val[j]?) ∧
      (∀ j, j < iter.iter.start.val →
        result.val[j]? = fixed_es.val[j]?) ⦄ := by
  unfold flip_endianness_of_encapsulation_state_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize) ×
                       alloc.vec.Vec Std.U8) =>
      p.1.iter.«end».val - p.1.iter.start.val)
    (inv := fun (p : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize) ×
                      alloc.vec.Vec Std.U8) =>
      let iter' := p.1
      let fixed_es' := p.2
      iter'.iter.«end» = iter.iter.«end» ∧
      iter'.step_by = iter.step_by ∧
      fixed_es'.length = fixed_es.length ∧
      iter.iter.start.val ≤ iter'.iter.start.val ∧
      iter'.iter.start.val ≤ iter'.iter.«end».val ∧
      iter'.iter.start.val % 2 = 0 ∧
      iter'.iter.«end».val + 1 ≤ fixed_es'.length ∧
      (∀ j, iter.iter.start.val ≤ j → j < iter'.iter.start.val → j % 2 = 0 →
        fixed_es'.val[j]? = fixed_es.val[j + 1]? ∧
        fixed_es'.val[j + 1]? = fixed_es.val[j]?) ∧
      (∀ j, j ≥ iter'.iter.start.val →
        fixed_es'.val[j]? = fixed_es.val[j]?) ∧
      (∀ j, j < iter.iter.start.val →
        fixed_es'.val[j]? = fixed_es.val[j]?))
  · -- Step case: body preserves invariant or produces final result
    rintro ⟨iter', fixed_es'⟩
      ⟨h_end', h_step', h_len', h_ge', h_le', h_even', h_bounds',
       h_swap', h_frame', h_behind'⟩
    simp only [] at *
    -- Unfold the body and handle the StepBy.next
    unfold body
    simp only [core.iter.adapters.step_by.IteratorStepBy.next]
    obtain ⟨opt, range', hnext, h_none, h_some⟩ :=
      core.iter.range.IteratorRange.next_Usize_spec iter'.iter
    rw [hnext]; simp only [bind_tc_ok]
    by_cases h_lt : iter'.iter.start.val < iter'.iter.«end».val
    · -- Continue case: the inner range yields i = iter'.iter.start
      obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
      rw [h_opt_eq]
      have h_i_lt : iter'.iter.start.val < fixed_es'.length := by omega
      have h_i1_lt : iter'.iter.start.val + 1 < fixed_es'.length := by omega
      -- Handle the skipN call (advancing the underlying Range by step_by - 1 = 1)
      have h_room : range'.start.val + (iter'.step_by.val - 1) ≤ range'.«end».val := by
        rw [h_step', h_step, h_start1, h_end1]; grind
      obtain ⟨iter_skip, h_skipN, h_skip_end, h_skip_start⟩ :=
        skipN_Range_Usize_advance range' (iter'.step_by.val - 1) h_room
      rw [h_skipN]; simp only [bind_tc_ok]
      -- Step through the Vec operations (i+1, index, index, index_mut, index_mut)
      step -- i + 1#usize
      step -- Vec.index ... fixed_es' i1 (read b_hi at position i+1)
      step -- Vec.index ... fixed_es' i  (read b_lo at position i)
      step -- Vec.index_mut ... fixed_es' i (get mutable ref at position i)
      have h_set_len : ∀ x, (fixed_es'.set iter'.iter.start x).length = fixed_es'.length :=
        fun _ => alloc.vec.Vec.set_length ..
      step -- Vec.index_mut ... fixed_es1 i1 (get mutable ref at position i+1)
      · simp_all
      -- Show: invariant preserved ∧ measure decreased
      constructor
      · -- Invariant for new state
        have h_new_start : iter_skip.start.val = iter'.iter.start.val + 2 := by
          rw [h_skip_start, h_start1, h_step', h_step]
        have h_new_end : iter_skip.«end» = iter.iter.«end» := by
          rw [h_skip_end, h_end1, h_end']
        grind
      · -- Measure decreased
        simp_all
        grind
    · -- Done case: the inner range is exhausted
      obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
      rw [h_opt_eq]
      -- result = fixed_es' (body returns the vector unchanged)
      refine ⟨h_len', ?_, ?_, h_behind'⟩
      · -- swap: follows from invariant since iter'.start ≥ iter'.end = iter.end
        intro j hj1 hj2 hj3
        exact h_swap' j hj1 (by grind) hj3
      · -- frame: follows from invariant since iter'.start ≥ iter.end
        intro j hj
        exact h_frame' j (by grind)
  · -- Base case: initial state satisfies the invariant
    refine ⟨rfl, rfl, rfl, le_refl _, h_start_le, h_start_even, h_in_bounds,
            fun j _ hj2 _ => absurd hj2 (by grind), fun j hj => rfl,
            fun j hj => rfl⟩

end spqr.incremental_mlkem768.flip_endianness_of_encapsulation_state_loop
