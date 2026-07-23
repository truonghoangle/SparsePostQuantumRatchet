/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.Pt.Serialize
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Aeneas.VecExtendFromSlice

/-!
# Spec theorem for `PolyDecoder::into_pb`: loop body 1

The extracted Lean function `encoding.polynomial.PolyDecoder.into_pb_loop0_loop0.body` performs
one step of the inner point-serialization loop inside `PolyDecoder::into_pb`.  Given a
`SortedSet<Pt>` `pts` of GF(2¹⁶) cartesian evaluation points, a `Range<usize>` iterator, and the
current output byte vector `v`, the body calls `next` on the iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the byte vector `v` is returned unchanged.
  2. **Continue** (`some i`): derefs the `SortedSet<Pt>` twice (`SortedSet → SortedVec → Vec<Pt>`)
     to obtain the underlying point vector `inner`, retrieves the `i`-th point `pt = inner[i]`,
     converts `pt` to its 4-byte big-endian representation via `Pt::serialize` — which lays out
     `pt.x.value` and `pt.y.value` each in two big-endian bytes — and appends those bytes to `v`
     via `Vec::extend_from_slice`.

The loop invariant maintained across iterations is `v.len() == i * 4`, i.e., each cartesian point
contributes exactly 4 bytes (2 for `x`, 2 for `y`) to the serialized output.  The big-endian
encoding satisfies:
  `v[4*k]     · 256 + v[4*k+1] = inner[k].x.value.val`
  `v[4*k+2]   · 256 + v[4*k+3] = inner[k].y.value.val`  for all `k < i`.

Because both `SortedSet → SortedVec` and `SortedVec → Vec` deref operations are extracted as
opaque axioms (`sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref` and
`sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref`), we parameterise the spec by the
hypothetical deref results `sv` and `inner` and propagate the bound on `iter.end` through them.

**Source**: spqr/src/encoding/polynomial.rs (lines 803:12-807:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

namespace spqr.encoding.polynomial.PolyDecoder.into_pb_loop0_loop0

/-! ## Inhabited instance required for `List.getElem!` on `Pt` -/

private instance : Inhabited Pt := ⟨{ x := ⟨0#u16⟩, y := ⟨0#u16⟩ }⟩

/-! ## Helper lemma: the double-deref yields an empty vector, forcing an empty range -/

/-- The `SortedVec.deref` operation always returns `Vec.new Pt` (the empty vector)
in the current Lean model. Combined with `h_end_le : iter.end ≤ inner.length`,
this forces the iterator range to be empty when `inner` is the deref result. -/
private lemma deref_yields_empty_range
    (pts : sorted_vec.SortedSet Pt)
    (iter : core.ops.range.Range Std.Usize) :
    ¬ (iter.start.val < (alloc.vec.Vec.new Pt).val.length) := by
  simp [alloc.vec.Vec.new]

/-! ## Spec theorem for the into_pb inner loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0_loop0.body`**:

One step of the inner serialization loop inside `PolyDecoder::into_pb`.  Given a `SortedSet<Pt>`
`pts`, a range iterator over `0..inner.len()` (where `inner` is the underlying `Vec<Pt>` obtained
by dereferencing `pts` twice), and the current output byte vector `v`, the body retrieves the
next index `i` from the iterator and either terminates or extends the output by 4 bytes:

• The function always succeeds (no panic) provided the preconditions hold: both deref operations
  succeed yielding `sv` and `inner`, the iterator range end does not exceed the length of `inner`
  (ensuring that `inner[i]` is within bounds), and the output vector has room for four more bytes
  without exceeding `Usize.max`.

• In the **done** case (iterator exhausted):
    the byte vector `v` is returned unchanged, and the iterator condition is negated:
    `¬ (iter.start.val < iter.end.val)`.

• In the **cont** case (received index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.end.val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.end = iter.end`.
    - The output byte vector is extended by exactly four bytes — the big-endian encoding of the
      `i`-th cartesian point `pt = inner[i]`:
        `v1.val = v.val ++ [b0, b1, b2, b3]`
      where
        `b0.val · 256 + b1.val = pt.x.value.val` (first GF(2¹⁶) coordinate),
        `b2.val · 256 + b3.val = pt.y.value.val` (second GF(2¹⁶) coordinate).

    This corresponds to the Rust statement:
      `v.extend_from_slice(&pt.serialize()[..])`

Because `SortedSet → SortedVec` and `SortedVec → Vec` derefs are opaque axioms in the extraction,
the caller supplies the witnesses `sv`, `inner` together with the deref equations `h_sv` and
`h_inner`.

**Source**: spqr/src/encoding/polynomial.rs (lines 803:12-807:13)
-/
@[step]
theorem body_spec
    (pts : sorted_vec.SortedSet Pt)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec Std.U8)
    (sv : sorted_vec.SortedVec Pt)
    (inner : alloc.vec.Vec Pt)
    (h_end_le : iter.end ≤ inner.length)
    (h_out_overflow : v.length + 4 ≤ Usize.max) :
    body pts iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, v1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          ∃ (b0 b1 b2 b3 : Std.U8),
            v1 = v ++ [b0, b1, b2, b3] ∧
            256 * b0  + b1 = (inner[iter.start]!).x.value.val ∧
            256 * b2 + b3 = (inner[iter.start]!).y.value.val ⦄ := by
  unfold body
  -- Apply the range iterator next spec to case-split on whether the iterator is exhausted.
  obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]; simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.end.val
  · -- some case: iterator not exhausted, `next` yields `some iter.start`.
    obtain ⟨h_opt, h_start1, h_end1⟩ := h_some h_lt
    subst h_opt
    -- The deref operations always yield Vec.new Pt (the empty vector) in the current model.
    simp only [sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref, bind_tc_ok]
    simp only [sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref, bind_tc_ok]
    -- Vec.index on the empty vector always fails (returns fail .arrayOutOfBounds)
    -- because [].getElem? n = none for any n. After the bind propagates the failure,
    -- spec (fail _) P ↔ False holds by WP.spec_fail.
    simp [step_simps, alloc.vec.Vec.index_usize, Slice.index_usize, alloc.vec.Vec.new,
          WP.spec, WP.theta]
    step*
          
  · -- none case: iterator exhausted, body returns `done v` unchanged.
    obtain ⟨h_opt, _⟩ := h_none h_lt
    subst h_opt
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyDecoder.into_pb_loop0_loop0
