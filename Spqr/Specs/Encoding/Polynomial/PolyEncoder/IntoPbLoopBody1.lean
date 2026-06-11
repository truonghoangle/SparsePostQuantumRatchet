/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Pt.Serialize
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Aeneas.VecExtendFromSlice

/-!
# Spec theorem for `PolyEncoder::into_pb`: loop body 1

The extracted Lean function `encoding.polynomial.PolyEncoder.into_pb_loop0_loop0.body` performs one
step of the inner coefficient-serialization loop inside `PolyEncoder::into_pb`.  Given a vector
`pts` of GF(2¹⁶) elements (the `.value` entries of a `Point`), a `Range<usize>` iterator, and the
current output byte vector `v`, the body calls `next` on the iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the byte vector `v` is returned unchanged.
  2. **Continue** (`some i`): retrieves the `i`-th GF(2¹⁶) element `pt = pts[i]`, converts
     `pt.value : u16` to its 2-byte big-endian representation via `u16::to_be_bytes`, and appends
     those bytes to `v` via `Vec::extend_from_slice`.

The loop invariant maintained across iterations is `v.len() == 2 * i`, i.e., each GF(2¹⁶) element
contributes exactly 2 bytes to the serialized output.  The big-endian encoding satisfies:
  `v[2*k] * 256 + v[2*k+1] = pts[k].value.val`  for all `k < i`.

**Source**: spqr/src/encoding/polynomial.rs (lines 556:20-560:21)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.into_pb_loop0_loop0

/-! ## Helper: `RangeFull` indexing on an array yields its slice -/

@[simp, step_simps]
private theorem array_index_rangeFull_ok {T : Type} {N : Usize}
    (a : Array T N) :
    core.array.Array.index
      (core.ops.index.IndexSlice
        (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice T))
      a () =
    ok a.to_slice :=
  rfl

/-! ## Helper: big-endian byte arithmetic for a `u16` value -/

/-- If `[b0, b1]` is the 2-byte big-endian encoding of a `u16` value `x`, then
`b0 * 256 + b1 = x`. -/
private theorem be_bytes_arith (x : Std.U16) (b0 b1 : Std.U8)
    (h : List.map (@UScalar.mk UScalarTy.U8) x.bv.toBEBytes = [b0, b1]) :
    b0.val * 256 + b1.val = x.val := by
  have h0 : b0 = (List.map (@UScalar.mk UScalarTy.U8) x.bv.toBEBytes)[0]! := by rw [h]; simp
  have h1 : b1 = (List.map (@UScalar.mk UScalarTy.U8) x.bv.toBEBytes)[1]! := by rw [h]; simp
  subst h0 h1
  simp only [Std.UScalar.val]
  simp [BitVec.toBEBytes, BitVec.toLEBytes, Nat.shiftRight_eq_div_pow]
  grind

/-! ## Spec theorem for the into_pb inner loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb_loop0_loop0.body`**:

One step of the inner serialization loop inside `PolyEncoder::into_pb`.  Given the GF(2¹⁶) element
vector `pts` (the `.value` entries of a `Point`), a range iterator over `0..pts.len()`, and the
current output byte vector `v`, the body retrieves the next index `i` from the iterator and either
terminates or extends the output:

• The function always succeeds (no panic) provided the preconditions hold: the iterator range end
  does not exceed the length of `pts` (ensuring that `pts[i]` is within bounds), and the output
  vector has room for two more bytes without exceeding `Usize.max`.

• In the **done** case (iterator exhausted):
    the byte vector `v` is returned unchanged, and the iterator condition is negated:
    `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The output byte vector is extended by exactly two bytes — the big-endian encoding of the
      `i`-th GF(2¹⁶) element's `u16` value:
        `v1.val = v.val ++ [hi, lo]`
      where `hi.val * 256 + lo.val = (pts.val[iter.start.val]!).value.val`.

    This corresponds to the Rust statement:
      `v.extend_from_slice(&pt.value.to_be_bytes()[..])`

**Source**: spqr/src/encoding/polynomial.rs (lines 556:20-560:21)
-/
@[step]
theorem body_spec
    (pts : alloc.vec.Vec encoding.gf.GF16)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec Std.U8)
    (h_end_le : iter.«end».val ≤ pts.val.length)
    (h_out_overflow : v.val.length + 2 ≤ Usize.max) :
    body pts iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, v1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          ∃ (hi lo : Std.U8),
            v1.val = v.val ++ [hi, lo] ∧
            hi.val * 256 + lo.val =
              (pts.val[iter.start.val]!).value.val ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt : iter.start.val < pts.val.length := by omega
    step*
    -- Decompose the 2-byte big-endian array into individual bytes
    obtain ⟨b0, b1, h_a_eq⟩ : ∃ b0 b1, a.val = [b0, b1] :=
      match a.val, a.property with | [b0, b1], _ => ⟨b0, b1, rfl⟩
    refine ⟨h_lt, h_start1, h_end1, b0, b1, ?_, ?_⟩
    · simp_all [Array.to_slice]
    · simp_all only [List.getElem!_eq_getElem?_getD]
      grind [be_bytes_arith]
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyEncoder.into_pb_loop0_loop0
