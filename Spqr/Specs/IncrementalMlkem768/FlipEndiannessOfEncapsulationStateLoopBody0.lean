/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Specs.Aeneas.RangeIteratorNext

/-!
# Spec theorem for `flip_endianness_of_encapsulation_state`: loop body 0

The Rust function `flip_endianness_of_encapsulation_state` (in `src/incremental_mlkem768.rs`,
lines 143:0-151:1) takes an `EncapsulationState` (`Vec<u8>`) and byte-swaps each consecutive
pair of bytes in the first `len − 32` positions, correcting an endianness mismatch
(cryspen/libcrux#1275).

Concretely, `flip_endianness_of_encapsulation_state` clones the input byte vector, then runs
a `for i in (0..fixed_es.len() - 32).step_by(2)` loop that swaps `fixed_es[i]` and
`fixed_es[i + 1]` in each iteration.

This file specifies **loop body 0** — one step of the byte-swap loop (lines 147:4-149:5).
The extracted Lean function
`incremental_mlkem768.flip_endianness_of_encapsulation_state_loop.body` performs one iteration:

  1. **Done** (`none`): the step-by-2 iterator over the range `0..(len − 32)` is exhausted and
     the byte vector `fixed_es` is returned unchanged.
  2. **Continue** (`some i`):
     a. Reads the byte at position `i + 1`: `b_hi = fixed_es[i + 1]`.
     b. Reads the byte at position `i`: `b_lo = fixed_es[i]`.
     c. Mutably writes `b_hi` into position `i` of `fixed_es`.
     d. Mutably writes `b_lo` into position `i + 1` of `fixed_es`.
     e. Returns the updated vector with the iterator advanced by 2 positions.

At the end of the full loop (after all iterations), every pair of bytes at positions `2k, 2k+1`
for `0 ≤ 2k < len − 32` has been swapped, flipping the byte order of each 16-bit word in the
non-header portion of the encapsulation state.

**Source**: spqr/src/incremental_mlkem768.rs (lines 147:4-149:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768.flip_endianness_of_encapsulation_state_loop

/--
**Spec theorem for `incremental_mlkem768.flip_endianness_of_encapsulation_state_loop.body`**:

One step of the byte-swap loop in `flip_endianness_of_encapsulation_state`, which swaps the
bytes at positions `i` and `i + 1` in the byte vector `fixed_es`.  Given the step-by-2 range
iterator `iter` (wrapping a `Range<usize>` over `0..(len − 32)`) and the current byte vector
`fixed_es`, the body retrieves the next even index `i` from the iterator and either terminates
or performs the swap:

• The function always succeeds (no panic) provided the precondition holds: the inner range's
  upper bound satisfies `iter.iter.«end».val + 1 ≤ fixed_es.length`, ensuring that both
  positions `i` and `i + 1` are valid indices whenever the iterator yields a value `i`
  (since `i.val < iter.iter.«end».val` implies `i.val + 1 ≤ iter.iter.«end».val`, and
  therefore `i.val + 1 < fixed_es.length`).

• In the **done** case (iterator exhausted, inner range `start ≥ end`):
    `fixed_es' = fixed_es` — the byte vector is returned unchanged, and the inner range
    condition is negated: `¬ (iter.iter.start.val < iter.iter.«end».val)`.

• In the **cont** case (received index `i = iter.iter.start` from the step-by iterator):
    - `iter.iter.start.val < iter.iter.«end».val` — the inner range was not exhausted.
    - The byte vector length is preserved:
        `fixed_es'.length = fixed_es.length`.
    - The bytes at positions `i` and `i + 1` are swapped:
        `fixed_es'.val[iter.iter.start.val]? = fixed_es.val[iter.iter.start.val + 1]?`
        `fixed_es'.val[iter.iter.start.val + 1]? = fixed_es.val[iter.iter.start.val]?`
    - All other positions are unchanged:
        `∀ j, j ≠ iter.iter.start.val → j ≠ iter.iter.start.val + 1 →
          fixed_es'.val[j]? = fixed_es.val[j]?`

**Source**: spqr/src/incremental_mlkem768.rs (lines 147:4-149:5)
-/
@[step]
theorem body_spec
    (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
    (fixed_es : alloc.vec.Vec Std.U8)
    (h_in_bounds : iter.iter.«end».val + 1 ≤ fixed_es.length) :
    body iter fixed_es ⦃ cf =>
      match cf with
      | ControlFlow.done fixed_es' =>
          fixed_es' = fixed_es ∧ ¬ (iter.iter.start.val < iter.iter.«end».val)
      | ControlFlow.cont (iter1, fixed_es') =>
          iter.iter.start.val < iter.iter.«end».val ∧
          fixed_es'.length = fixed_es.length ∧
          fixed_es'.val[iter.iter.start.val]? =
            fixed_es.val[iter.iter.start.val + 1]? ∧
          fixed_es'.val[iter.iter.start.val + 1]? =
            fixed_es.val[iter.iter.start.val]? ∧
          (∀ j, j ≠ iter.iter.start.val → j ≠ iter.iter.start.val + 1 →
            fixed_es'.val[j]? = fixed_es.val[j]?) ⦄ := by
  unfold body
  -- Unfold the StepBy.next into the underlying Range iterator's next + skipN
  simp only [core.iter.adapters.step_by.IteratorStepBy.next]
  -- Decompose the underlying Range<usize> iterator's next
  obtain ⟨opt, range', hnext, h_none, h_some⟩ :=
    core.iter.range.IteratorRange.next_Usize_spec iter.iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.iter.start.val < iter.iter.«end».val
  · -- Continue case: the inner range yields some i = iter.iter.start
    obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    simp only [bind_tc_ok]
    -- i = iter.iter.start, i + 1 is within bounds
    have h_i_lt : iter.iter.start.val < fixed_es.length := by omega
    have h_i1_lt : iter.iter.start.val + 1 < fixed_es.length := by omega
    sorry
  · -- Done case: the inner range is exhausted
    obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.incremental_mlkem768.flip_endianness_of_encapsulation_state_loop
