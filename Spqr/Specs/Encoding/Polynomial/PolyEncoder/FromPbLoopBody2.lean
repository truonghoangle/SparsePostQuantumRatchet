/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Pt.Deserialize

/-!
# Spec theorem for `PolyEncoder::from_pb`: loop body 2

In the `EncoderState::Points` branch of `PolyEncoder::from_pb`, an inner loop iterates over
byte pairs in a serialized point vector `pts`, reconstructing GF(2¹⁶) elements from their
big-endian two-byte encoding.  Each field element is represented as a 16-bit unsigned integer,
and the big-endian decoding satisfies `value = hi * 256 + lo` where `hi` and `lo` are the
high and low bytes respectively.

The extracted Lean function `encoding.polynomial.PolyEncoder.from_pb_loop1_loop0.body` performs
one step of this inner byte-deserialization loop.  Given the serialized byte vector `pts`, a
`Range<usize>` iterator over `0..(pts.len() / 2)`, and the current output vector of `GF16`
values `v`, the body calls `next` on the range iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the loop terminates with `()`.
  2. **Continue** (`some k`): computes `j = k * 2`, reads the two bytes `pts[j]` and `pts[j+1]`,
     converts them from big-endian to a `u16` via `u16::from_be_bytes`, wraps the result as a
     `GF16` via `GF16::new`, and pushes it onto `v`.

The function proceeds in two stages:
  1. `core.iter.range.IteratorRange.next iter` — advances the range iterator, yielding the current
     index `k` (when `k < pts.len() / 2`) or `none` (when the range is exhausted).
  2. Byte-pair reconstruction: reads `pts[2*k]` and `pts[2*k+1]`, converts to `u16` via
     `from_be_bytes`, wraps as `GF16::new`, and appends to `v` via `Vec::push`.

**Source**: spqr/src/encoding/polynomial.rs (lines 599:16-602:17)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.from_pb_loop1_loop0

/-! ## Helper lemma: Range<usize> iterator `next` specification -/

/--
The range iterator `next` always returns `ok` and either provides the current `start` value (when
`start < end`) or `none` (when `start ≥ end`).  This is the concrete specification for the
`core.ops.range.Range<usize>` iterator used in the Rust `for k in 0..(pts.len() / 2)` loop.
-/
private lemma IteratorRange_next_Usize_post
    (range : core.ops.range.Range Std.Usize) :
    ∃ opt range',
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range
        = ok (opt, range') ∧
      (¬ range.start.val < range.«end».val →
          opt = none ∧ range' = range) ∧
      (range.start.val < range.«end».val →
          opt = some range.start ∧
          range'.start.val = range.start.val + 1 ∧
          range'.«end» = range.«end») := by
  simp only [core.iter.range.IteratorRange.next]
  simp only [liftFun2, liftFun1, core.clone.impls.CloneUsize.clone, bind_tc_ok, not_lt]
  have h_lt_iff :
      (core.cmp.impls.PartialOrdUsize.lt range.start range.«end» = true) =
      (range.start.val < range.«end».val) := by
    simp [core.cmp.impls.PartialOrdUsize.lt]
  simp only [h_lt_iff]
  by_cases hlt : range.start.val < range.«end».val
  · rw [if_pos hlt]
    have hbound : range.start.val + 1 ≤ Usize.max := by
      have := range.«end».hBounds; scalar_tac
    refine ⟨some range.start,
            {range with start := ⟨range.start.val + 1, by scalar_tac⟩},
            ?_, ?_, ?_⟩
    · simp only [core.iter.range.StepUsize.forward_checked, bind_tc_ok]
      have hca := Usize.checked_add_bv_spec range.start 1#usize
      rcases heq : Usize.checked_add range.start 1#usize with _ | z
      · rw [heq] at hca; scalar_tac
      · simp only
        rw [heq] at hca
        obtain ⟨_, hval, _⟩ := hca
        have hzval : z.val = range.start.val + 1 := by scalar_tac
        congr 4
        exact UScalar.eq_of_val_eq hzval
    · intro h; omega
    · intro _; exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hlt]
    exact ⟨none, range, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd h hlt⟩

/-! ## Helper: `GF16::new` preserves the raw `u16` value -/

/--
`GF16::new value` always succeeds and produces a `GF16` whose underlying `u16` field is exactly
`value`.  This is the raw-value version of the spec; we use it here to relate the deserialized
GF(2¹⁶) element directly to the input bytes.
-/
@[step]
private lemma GF16_new_value_spec (value : U16) :
    encoding.gf.GF16.new value ⦃ (result : encoding.gf.GF16) =>
      result.value = value ⦄ := by
  simp [encoding.gf.GF16.new]

/-! ## Spec theorem for the from_pb inner byte-deserialization loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb_loop1_loop0.body`**:

One step of the inner byte-deserialization loop inside the `EncoderState::Points` branch of
`PolyEncoder::from_pb`.  Given the serialized byte vector `pts`, a range iterator over
`0..(pts.len() / 2)`, and the current output vector of `GF16` values `v`, the body retrieves the
next index `k` from the iterator and either terminates or extends the output:

• The function always succeeds (no panic) provided the preconditions hold: the iterator range end
  satisfies `2 * iter.«end».val ≤ pts.val.length` (ensuring that `pts[2*k]` and `pts[2*k+1]` are
  within bounds for every `k < iter.«end».val`), the iterator start does not exceed the end,
  and the output vector length plus the remaining range does not exceed `Usize.max`.

• In the **done** case (iterator exhausted):
    the loop terminates with `()`, and the iterator condition is negated:
    `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `k = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The output vector is extended by exactly one `GF16` element — the big-endian reconstruction
      of the two bytes `pts[2*k]` and `pts[2*k+1]`:
        `v1.val = v.val ++ [g]`
      where `g.value.val = (pts.val[2 * iter.start.val]!).val * 256 +
                            (pts.val[2 * iter.start.val + 1]!).val`.

    This corresponds to the Rust body:
    ```rust
    for k in 0..(pts.len() / 2) {
        let j = k * 2;
        v.push(GF16::new(u16::from_be_bytes([pts[j], pts[j + 1]])));
    }
    ```

This establishes that one step of the inner loop faithfully reconstructs a GF(2¹⁶) element from
its big-endian two-byte encoding and appends it to the accumulator vector.

This follows from composing:
  1. `IteratorRange_next_Usize_post`: the range iterator either yields the element at the current
     position and advances the cursor, or signals exhaustion.
  2. `GF16_new_value_spec`: the `GF16::new` wrapper preserves the raw `u16` value.

**Source**: spqr/src/encoding/polynomial.rs (lines 599:16-602:17)
-/
@[step]
theorem body_spec
    (pts : alloc.vec.Vec Std.U8)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec encoding.gf.GF16)
    (h_end_le : 2 * iter.«end».val ≤ pts.val.length)
    (h_start_le : iter.start.val ≤ iter.«end».val)
    (h_overflow : v.val.length + (iter.«end».val - iter.start.val) ≤ Usize.max) :
    body pts iter v ⦃ cf =>
      match cf with
      | ControlFlow.done () =>
          ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, v1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          ∃ (g : encoding.gf.GF16),
            v1.val = v.val ++ [g] ∧
            g.value.val =
              (pts.val[2 * iter.start.val]!).val * 256 +
              (pts.val[2 * iter.start.val + 1]!).val ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := IteratorRange_next_Usize_post iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_2k_lt : 2 * iter.start.val < pts.val.length := by omega
    have h_2k1_lt : 2 * iter.start.val + 1 < pts.val.length := by omega
    have h_v_overflow : v.val.length + 1 ≤ Usize.max := by omega
    step*
    exact ⟨h_lt, h_start1, h_end1, g, v1_post, by
      simp_all [Array.make, Nat.mul_comm]⟩
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact h_lt

end spqr.encoding.polynomial.PolyEncoder.from_pb_loop1_loop0
