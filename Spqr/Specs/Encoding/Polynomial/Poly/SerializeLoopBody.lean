/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Pt.Serialize
import Spqr.Specs.Aeneas.RangeIteratorNext

/-!
# Spec theorem for `Poly::serialize`: loop body 0

The extracted Lean function `encoding.polynomial.Poly.serialize_loop.body` performs one step of the
coefficient serialization loop.  It calls `next` on the `Range<usize>` iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the output byte vector `out` is returned
     unchanged.
  2. **Continue** (`some i`): retrieves the `i`-th GF(2¹⁶) coefficient `c = v[i]`, converts
     `c.value : u16` to its 2-byte big-endian representation via `u16::to_be_bytes`, and appends
     those bytes to `out` via `Vec::extend_from_slice`.

The loop invariant maintained across iterations is `out.len() == 2 * i`, i.e., each coefficient
contributes exactly 2 bytes to the serialized output.  The big-endian encoding satisfies:
  `out[2*j] * 256 + out[2*j+1] = v[j].value.val`  for all `j < i`.

**Source**: spqr/src/encoding/polynomial.rs (lines 333:8-337:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.Poly.serialize_loop

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

/-! ## Helper: `extend_from_slice` specialised to `U8` -/

/--
**Spec for `alloc.vec.Vec.extend_from_slice` specialised to `U8`**:

The `core.clone.Clone` instance for `U8` (`core.clone.CloneU8`) has `clone x = ok x` for every `x`,
hence the elementwise `Slice.clone` on `s` returns `ok s` and the resulting vector is exactly
`v.val ++ s.val`.  The precondition `v.val.length + s.val.length ≤ Usize.max` discharges the
overflow guard in the body of `extend_from_slice`.
-/
@[step]
private lemma extend_from_slice_U8_spec
    (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s
      ⦃ (r : alloc.vec.Vec U8) => r.val = v.val ++ s.val ⦄ := by
  have h_clone_x :
      ∀ x ∈ s.val, core.clone.CloneU8.clone x = ok x := by
    intros _ _; rfl
  have h_slclone :
      Slice.clone core.clone.CloneU8.clone s = ok s := by
    obtain ⟨s', h_eq, hs⟩ := WP.spec_imp_exists (Slice.clone_spec h_clone_x)
    rw [h_eq, ← hs]
  unfold alloc.vec.Vec.extend_from_slice
  have hlen : v.length + s.length ≤ Usize.max := h
  rw [dif_pos hlen]
  grind

/-! ## Spec theorem for the serialize loop body -/

/-- **Spec theorem for `encoding.polynomial.Poly.serialize_loop.body`**:

One step of the `Poly::serialize` serialization loop.  Given the coefficient vector `v`, a range
iterator over `0..v.len()`, and the current output byte vector `out`, the body retrieves the next
index `i` from the iterator and either terminates or extends the output:

• The function always succeeds (no panic) provided the preconditions hold: the iterator range end
  does not exceed the coefficient vector length (ensuring that `v[i]` is within bounds), and the
  output vector has room for two more bytes without exceeding `Usize.max`.

• In the **done** case (iterator exhausted):
    the byte vector `out` is returned unchanged, and the iterator condition is negated:
    `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The output byte vector is extended by exactly two bytes — the big-endian encoding of the
      `i`-th coefficient's `u16` value:
        `out1.val = out.val ++ [hi, lo]`
      where `hi.val * 256 + lo.val = (v.val[iter.start.val]!).value.val`.

    This corresponds to the Rust statement:
      `out.extend_from_slice(&self.coefficients[i].value.to_be_bytes()[..])`

**Source**: spqr/src/encoding/polynomial.rs (lines 333:8-337:9)
-/
@[step]
theorem body_spec
    (v : alloc.vec.Vec encoding.gf.GF16)
    (iter : core.ops.range.Range Std.Usize)
    (out : alloc.vec.Vec Std.U8)
    (h_end_le : iter.«end».val ≤ v.val.length)
    (h_out_overflow : out.val.length + 2 ≤ Usize.max) :
    body v iter out ⦃ cf =>
      match cf with
      | ControlFlow.done out' =>
          out' = out ∧ ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, out1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          ∃ (hi lo : Std.U8),
            out1.val = out.val ++ [hi, lo] ∧
            hi.val * 256 + lo.val =
              (v.val[iter.start.val]!).value.val ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt : iter.start.val < v.val.length := by omega
    step*
    -- Decompose the 2-byte big-endian array into individual bytes
    obtain ⟨b0, b1, h_a_eq⟩ : ∃ b0 b1, a.val = [b0, b1] :=
      match a.val, a.property with | [b0, b1], _ => ⟨b0, b1, rfl⟩
    refine ⟨h_lt, h_start1, h_end1, b0, b1, ?_, ?_⟩
    · simp_all [Array.to_slice]
    · simp_all [Array.to_slice]
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.Poly.serialize_loop
