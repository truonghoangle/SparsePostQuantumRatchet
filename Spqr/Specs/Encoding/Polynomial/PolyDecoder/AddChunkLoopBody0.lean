/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NecessaryPoints
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Aeneas.GF16New

/-!
# Spec theorem for `PolyDecoder::add_chunk`: loop body 0

The extracted Lean function
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop.body` performs one
step of the point-absorption loop inside `PolyDecoder::add_chunk`.  Given a `Chunk` (containing a
16-bit chunk index and 32 bytes of evaluation data), a `Range<usize>` iterator over `0..16`, and
the current decoder state `self`, the body calls `next` on the range iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the decoder state is returned unchanged.
  2. **Continue** (`some i`): computes the GF(2¹⁶) evaluation point from the chunk's data bytes:
       `x = GF16::new(chunk.index)`                    — the x-coordinate is the chunk index,
       `y = GF16::new((data[2i] << 8) + data[2i+1])`  — the y-coordinate is big-endian decoded.
     Then conditionally pushes `Pt { x, y }` into `self.pts[i]`:
       - if `chunk.index < necessary_points(self, i)`, or
       - if `self.pts[i].len() < necessary_points(self, i)`,
     the point is pushed via `SortedSet::push`; otherwise the state is unchanged.

Since `0 ≤ i < 16`, the modular/division decomposition
  `total_idx = chunk.index * 16 + i`,  `poly = total_idx % 16`,  `poly_idx = total_idx / 16`
simplifies to `poly = i` (the loop index) and `poly_idx = chunk.index.val` (the chunk index).

In GF(2¹⁶) — the Galois field with 65 536 elements — each field element is represented as a
polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned integer.
A cartesian point `Pt = (x, y)` packs two such elements; its 2-byte y-value serialization
satisfies the big-endian decoding invariant
  `y.value = data[2i] · 256 + data[2i+1]`.

The body spec composes:
  1. `IteratorRange.next` — to advance the range iterator.
  2. Usize arithmetic: `total_idx = chunk.index * 16 + i`, `poly = total_idx % 16`,
     `poly_idx = total_idx / 16`.  Since `0 ≤ i < 16`, these simplify to `poly = i` and
     `poly_idx = chunk.index.val`.
  3. `UScalar.cast` — to convert between `U16` / `U8` and `Usize` representations.
  4. `GF16.new` — to wrap raw `U16` values as GF(2¹⁶) field elements.
  5. `Array.index_usize` — to read chunk data bytes at positions `2*i` and `2*i+1`.
  6. `PolyDecoder.necessary_points` (spec from `NecessaryPoints.lean`) — to compute the
     per-polynomial point budget via Euclidean division of `pts_needed` across 16 polynomials.
  7. `sorted_vec.SortedSet.push` — to conditionally append the point to the sorted set
     (when the push condition is satisfied).
  8. `Array.index_mut_usize` and record-update — to store the updated sorted set back into
     the `pts` array.

The key invariant preserved by each iteration is:
  `self1.pts_needed = self.pts_needed ∧ self1.is_complete = self.is_complete`
which directly reflects the Rust loop invariant
  `self.pts.len() == 16 && self.pts_needed == initial_pts_needed`.
(The `pts.len() == 16` part is structural in Lean since `pts : Array (SortedSet Pt) 16#usize`.)

**Source**: spqr/src/encoding/polynomial.rs (lines 882:8-903:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

/-! ## Inhabited instance for `SortedSet Pt` slots -/

/--
`Array (SortedSet Pt) 16#usize` slots need an `Inhabited` default for `getElem!` (`[·]!`) on
the underlying list of sorted sets.  We borrow the `default` inhabitant provided by the
existing `Inhabited (SortedSet T)` instance.
-/
instance : Inhabited (sorted_vec.SortedSet Pt) := ⟨alloc.vec.Vec.new Pt⟩

/-! ## Helper: y-value big-endian decoding -/

/-- Prove the big-endian y-value equation for GF(2¹⁶) decoding.
    Given `y.value = i9` and
    `i9.val = data[2i] <<< 8 % U16.size + data[2i+1]`,
    show `y.value.val = 256 * data[2i]?.getD default + data[2i+1]?.getD default`.
-/
private theorem y_value_big_endian
    (data : Std.Array U8 32#usize) (i : Nat) (h_i : i < 16)
    (i9 : U16) (y : GF16)
    (y_post : y.value = i9)
    (i9_post : i9.val = ((↑data : List U8)[i * 2]'(by
    have : (↑data : List U8).length = 32 := data.property; omega)).val <<< 8 % U16.size +
      ((↑data : List U8)[i * 2 + 1]'(by
      have : (↑data : List U8).length = 32 := data.property; omega)).val) :
    y.value.val =
      256 * ((↑data : List U8)[i * 2]?.getD default).val +
      ((↑data : List U8)[i * 2 + 1]?.getD default).val := by
  have h_len : (↑data : List U8).length = 32 := data.property
  have h1 : i * 2 < (↑data : List U8).length := by omega
  have h2 : i * 2 + 1 < (↑data : List U8).length := by omega
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
      Option.getD_some, Option.getD_some]
  rw [y_post, i9_post, Nat.shiftLeft_eq]
  have hv : (↑(↑data : List U8)[i * 2] : Nat) ≤ 255 := by scalar_tac
  have h_size : U16.size = 65536 := by scalar_tac
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-! ## Spec theorem for the add_chunk loop body -/

/-- **Spec theorem for
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop.body`**:

One step of the point-absorption loop inside `PolyDecoder::add_chunk`.  Given a `Chunk`
(containing a 16-bit chunk index and 32 bytes of evaluation data), a range iterator over
`0..16`, and the current decoder state `self`, the body retrieves the next loop index `i` from
the iterator and either terminates or processes the `i`-th evaluation point from the chunk.

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end does not exceed 16, the chunk index multiplication does not overflow Usize, and each
  sorted set in `self.pts` has room for one more element.

• In the **done** case (iterator exhausted):
    the decoder state is returned unchanged: `self' = self`,
    and the iterator condition is negated: `¬ (iter.start.val < iter.end.val)`.

• In the **cont** case (received index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.end.val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.end = iter.end`.
    - The decoder's key fields are preserved:
        `self1.pts_needed = self.pts_needed`,
        `self1.is_complete = self.is_complete`.
    - There exists a point `p : Pt` constructed from the chunk data:
        `p.x.value.val = chunk.index.val`
          (the chunk index, interpreted as a GF(2¹⁶) element),
        `p.y.value.val = data[2·i] · 256 + data[2·i+1]`
          (the big-endian byte decoding of two consecutive data bytes).
    - Either:
        (a) a push occurred — the sorted set at slot `i` was extended by `p` and all other
            slots are unchanged, or
        (b) the decoder state is unchanged (`self1 = self`).

    This corresponds to the Rust body:
    ```rust
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
    ```

This establishes that one step of the `add_chunk` loop faithfully computes a GF(2¹⁶)
evaluation point from the chunk's serialized data and conditionally absorbs it into the
decoder's per-polynomial point set via the opaque `SortedSet::push` operation, while
preserving the decoder's `pts_needed` and `is_complete` fields.

**Source**: spqr/src/encoding/polynomial.rs (lines 882:8-903:9)
-/
@[step]
theorem body_spec
    (chunk : encoding.Chunk) (iter : core.ops.range.Range Std.Usize)
    (self : encoding.polynomial.PolyDecoder)
    (h_end_le : iter.end.val ≤ 16)
    (h_idx_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_room : ∀ k, k < 16 →
      (self.pts.val[k]!).length + 1 ≤ Usize.max) :
    body chunk iter self ⦃ cf =>
      match cf with
      | ControlFlow.done self' =>
          self' = self ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, self1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          self1.pts_needed = self.pts_needed ∧
          self1.is_complete = self.is_complete ∧
          ∃ (p : Pt),
            p.x.value = chunk.index ∧
            p.y.value.val =
              256 * (chunk.data[iter.start.val * 2]!) +
              (chunk.data[iter.start.val * 2 + 1]!) ∧
            ((self1.pts[iter.start]!.val =
                self.pts[iter.start]!.val ++ [p] ∧
              ∀ k, k ≠ iter.start →
                self1.pts[k]! = self.pts[k]!)
             ∨ self1 = self) ⦄ := by
  unfold body
  obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_16 : iter.start.val < 16 := by omega
    have h_mod : (chunk.index.val * 16 + iter.start.val) % 16 = iter.start.val := by omega
    have h_div : (chunk.index.val * 16 + iter.start.val) / 16 = chunk.index.val := by omega
    have h_push := h_push_room iter.start.val h_i_lt_16
    step*
    · simp_all
    · simp_all only [alloc.vec.Vec.length, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        getElem!_pos, Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and,
        implies_true,  and_self, UScalarTy.U16_numBits_eq,
        UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
        UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq, Nat.reduceLeDiff,
        Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv, Bvify.U8.UScalar_bv, UScalar.lt_equiv,
        Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Array.getElem!_Usize_eq,
        Array.set_val_eq, List.length_set, List.getElem_set_self, List.append_cancel_left_eq,
        List.cons.injEq, and_true, ne_eq, UScalar.neq_to_neq_val, Nat.not_eq, not_false_eq_true,
        lt_or_lt_iff_ne, true_or, or_true, List.set_getElem?_neq, true_and]
      refine ⟨{ x, y }, ?_, ?_, Or.inl rfl⟩
      · scalar_tac
      · exact y_value_big_endian chunk.data iter.start.val h_i_lt_16 i9 y y_post i9_post
    · simp_all only [alloc.vec.Vec.length, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        getElem!_pos, Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and,
        implies_true,  and_self, UScalarTy.U16_numBits_eq,
        UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
        UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq, Nat.reduceLeDiff,
        Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv, Bvify.U8.UScalar_bv, UScalar.lt_equiv, not_lt,
        alloc.vec.Vec.len, Usize.ofNatCore_val_eq, Array.getElem!_Nat_eq,
        List.getElem!_eq_getElem?_getD, Array.getElem!_Usize_eq, Array.set_val_eq, List.length_set,
        List.getElem_set_self, List.append_cancel_left_eq, List.cons.injEq, and_true, ne_eq,
        UScalar.neq_to_neq_val, Nat.not_eq, not_false_eq_true, lt_or_lt_iff_ne, true_or, or_true,
        List.set_getElem?_neq, true_and]
      refine ⟨{ x, y }, ?_, ?_, Or.inl rfl⟩
      · scalar_tac
      · exact y_value_big_endian chunk.data iter.start.val h_i_lt_16 i9 y y_post i9_post
    · simp_all only [alloc.vec.Vec.length, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        getElem!_pos, Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and,
        implies_true,  and_self,  UScalarTy.U16_numBits_eq,
        UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
        UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq, Nat.reduceLeDiff,
        Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv, Bvify.U8.UScalar_bv, UScalar.lt_equiv, not_lt,
        alloc.vec.Vec.len, Usize.ofNatCore_val_eq, Array.getElem!_Nat_eq,
        List.getElem!_eq_getElem?_getD, Array.getElem!_Usize_eq, List.self_eq_append_right,
        List.cons_ne_self, ne_eq, UScalar.neq_to_neq_val, and_true, or_true, true_and]
      refine ⟨{ x, y }, ?_, ?_⟩
      · scalar_tac
      · exact y_value_big_endian chunk.data iter.start.val h_i_lt_16 i9 y y_post i9_post
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop
