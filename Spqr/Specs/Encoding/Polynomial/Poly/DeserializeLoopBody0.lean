/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Pt.Deserialize

/-!
# Spec theorem for `Poly::deserialize`: loop body 0

The extracted Lean function `encoding.polynomial.Poly.deserialize_loop.body` performs one step of the
coefficient deserialization loop.  It calls `next` on the `Range<usize>` iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the coefficient vector `coefficients` is
     returned unchanged.
  2. **Continue** (`some i`): computes `j = i * 2`, reads the two bytes `serialized[j]` and
     `serialized[j+1]`, converts them from big-endian to a `u16` via `u16::from_be_bytes`,
     wraps the result as a `GF16` via `GF16::new`, and pushes it onto the `coefficients` vector.

The loop invariant maintained across iterations is `coefficients.len() == i`, i.e., each iteration
contributes exactly one GF(2¹⁶) coefficient reconstructed from two consecutive bytes.  The
big-endian decoding satisfies:
  `coefficients[k].value.val = serialized[2*k].val * 256 + serialized[2*k+1].val`
for all `k < iter.start`.

**Source**: spqr/src/encoding/polynomial.rs (lines 347:8-350:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.Poly.deserialize_loop

/-! ## Helper lemma: Range<usize> iterator `next` specification -/

/--
The range iterator `next` always returns `ok` and either provides the current `start` value (when
`start < end`) or `none` (when `start ≥ end`).  This is the concrete specification for the
`core.ops.range.Range<usize>` iterator used in the Rust
`for i in 0..(serialized.len() / 2)` loop.
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
`value`.  This is the raw-value version of the spec (which gives the `toGF216` interpretation);
we use it here to relate the deserialized coefficient directly to the input bytes.
-/
@[step]
private lemma GF16_new_value_spec (value : U16) :
    encoding.gf.GF16.new value ⦃ (result : encoding.gf.GF16) =>
      result.value = value ⦄ := by
  simp [encoding.gf.GF16.new]

/-! ## Spec theorem for the deserialize loop body -/

/-- **Spec theorem for `encoding.polynomial.Poly.deserialize_loop.body`**:

One step of the `Poly::deserialize` deserialization loop.  Given the serialized byte slice
`serialized`, a range iterator over `0..(serialized.len() / 2)`, and the current coefficient
vector `coefficients`, the body retrieves the next index `i` from the iterator and either
terminates or extends the coefficient vector:

• The function always succeeds (no panic) provided the preconditions hold: the iterator range end
  satisfies `2 * iter.«end».val ≤ serialized.val.length` (ensuring that `serialized[2*i]` and
  `serialized[2*i+1]` are within bounds for every `i < iter.«end».val`), and the coefficient
  vector has room for one more element without exceeding `Usize.max`.

• In the **done** case (iterator exhausted):
    the coefficient vector `coefficients` is returned unchanged, and the iterator condition is
    negated: `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The coefficient vector is extended by exactly one `GF16` element — the big-endian
      reconstruction of the two bytes `serialized[2*i]` and `serialized[2*i+1]`:
        `coefficients1.val = coefficients.val ++ [g]`
      where `g.value.val = (serialized.val[2 * iter.start.val]!).val * 256 +
                            (serialized.val[2 * iter.start.val + 1]!).val`.

    This corresponds to the Rust statement:
      `coefficients.push(GF16::new(u16::from_be_bytes([serialized[j], serialized[j+1]])))`

**Source**: spqr/src/encoding/polynomial.rs (lines 347:8-350:9)
-/
@[step]
theorem body_spec
    (serialized : Slice Std.U8)
    (iter : core.ops.range.Range Std.Usize)
    (coefficients : alloc.vec.Vec encoding.gf.GF16)
    (h_end_le : 2 * iter.«end».val ≤ serialized.val.length)
    (h_coeff_overflow : coefficients.val.length + 1 ≤ Usize.max) :
    body serialized iter coefficients ⦃ cf =>
      match cf with
      | ControlFlow.done coefficients' =>
          coefficients' = coefficients ∧ ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, coefficients1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          ∃ (g : encoding.gf.GF16),
            coefficients1.val = coefficients.val ++ [g] ∧
            g.value.val =
              (serialized.val[2 * iter.start.val]!).val * 256 +
              (serialized.val[2 * iter.start.val + 1]!).val ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := IteratorRange_next_Usize_post iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_2i_lt : 2 * iter.start.val < serialized.val.length := by omega
    have h_2i1_lt : 2 * iter.start.val + 1 < serialized.val.length := by omega
    step*
    exact ⟨h_lt, h_start1, h_end1, g, coefficients1_post, by
      simp_all [Array.make, Nat.mul_comm]⟩
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.Poly.deserialize_loop
