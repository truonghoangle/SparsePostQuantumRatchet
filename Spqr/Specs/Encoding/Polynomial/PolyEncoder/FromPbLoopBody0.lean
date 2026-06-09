/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.Poly.Deserialize

/-!
# Spec theorem for `PolyEncoder::from_pb`: loop body 0

The extracted Lean function `encoding.polynomial.PolyEncoder.from_pb_loop0.body` performs one step
of the outer polynomial-deserialization loop inside `PolyEncoder::from_pb`.  Given the protobuf
index `i` (of type `U32`), the vector of serialized byte vectors `v` (corresponding to `pb.polys`),
a `Range<usize>` iterator, and the current output array of 16 `Poly` values, the body calls `next`
on the iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the result is
     `Ok(PolyEncoder { idx: i, s: EncoderState::Polys(out) })`, wrapping the fully deserialized
     polynomial array.
  2. **Continue** (`some j`): retrieves the `j`-th serialized byte vector from `v`, deserializes
     it into a `Poly` via `Poly::deserialize`, and updates `out[j]` with the result.

Each deserialized polynomial satisfies the big-endian byte-decoding invariant: for each
coefficient index `k`, the coefficient's `u16` value equals
  `serialized[2*k] * 256 + serialized[2*k+1]`
where `serialized` is the byte vector `v[j]`.

The body spec composes:
  1. `IteratorRange.next` — to advance the outer range iterator.
  2. `alloc.vec.Vec.index` — to retrieve the `j`-th serialized byte vector from `v`.
  3. `alloc.vec.Vec.deref` — to convert the byte vector to a slice.
  4. `Poly.deserialize` (deserialization spec from `Deserialize.lean`) — to decode the byte slice
     into a `Poly` over GF(2¹⁶).
  5. `Array.update` — to store the deserialized polynomial in the output array.

**Source**: spqr/src/encoding/polynomial.rs (lines 614:12-617:72)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.from_pb_loop0

/-! ## Inhabited instances -/

/--
`Poly` wraps a `Vec<GF16>` of coefficients.  An `Inhabited` instance is required so that
`getElem!` (`[·]!`) on arrays/lists of `Poly` has a well-defined default value.  We use the empty
coefficient vector as the canonical default.
-/
instance : Inhabited encoding.polynomial.Poly := ⟨⟨alloc.vec.Vec.new _⟩⟩

/-! ## Spec theorem for the from_pb outer loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb_loop0.body`**:

One step of the outer deserialization loop inside `PolyEncoder::from_pb` (the `pb.polys` branch).
Given the protobuf index `i`, the vector of serialized byte vectors `v` (from `pb.polys`), a range
iterator over `0..NUM_POLYS`, and the current output array of 16 `Poly` values, the body retrieves
the next index `j` from the iterator and either terminates or extends the output:

• The function always succeeds (no panic) provided the preconditions hold: the iterator range end
  does not exceed the vector length or the array size (16), and each serialized byte vector is
  non-empty, has even length, and can be deserialized without overflow.

• In the **done** case (iterator exhausted):
    the result is `Ok(PolyEncoder { idx := i, s := Polys(out) })` and the iterator condition
    is negated: `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `j = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The output array is updated at position `j` with the deserialized polynomial:
        there exists a `Poly` `poly` such that
        `poly.coefficients.val.length = (v.val[j]!).val.length / 2`
      and for every `k < (v.val[j]!).val.length / 2`:
        `∃ g, poly.coefficients.val[k]? = some g ∧
          g.value.val = (v.val[j]!).val[2*k]!.val * 256 + (v.val[j]!).val[2*k+1]!.val`

    This corresponds to the Rust body:
    ```rust
    for i in 0..NUM_POLYS {
        out[i] = Poly::deserialize(&pb.polys[i])?;
    }
    ```

**Source**: spqr/src/encoding/polynomial.rs (lines 614:12-617:72)
-/
@[step]
theorem body_spec
    (i : Std.U32)
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (iter : core.ops.range.Range Std.Usize)
    (out : Array encoding.polynomial.Poly 16#usize)
    (h_end_le_v : iter.«end».val ≤ v.val.length)
    (h_end_le_16 : iter.«end».val ≤ 16)
    (h_nonempty : ∀ (j : Nat), j < v.val.length →
        (v.val[j]!).val.length ≠ 0)
    (h_even : ∀ (j : Nat), j < v.val.length →
        (v.val[j]!).val.length % 2 = 0)
    (h_overflow : ∀ (j : Nat), j < v.val.length →
        (v.val[j]!).val.length / 2 + 1 ≤ Usize.max) :
    body i v iter out ⦃ cf =>
      match cf with
      | ControlFlow.done result =>
          result = core.result.Result.Ok
            { idx := i, s := encoding.polynomial.EncoderState.Polys out } ∧
          ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, out') =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          ∃ (poly : encoding.polynomial.Poly),
            out'.val[iter.start.val]! = poly ∧
            (∀ k, k ≠ iter.start.val → out'.val[k]! = out.val[k]!) ∧
            poly.coefficients.val.length =
              (v.val[iter.start.val]!).val.length / 2 ∧
            (∀ (k : Nat),
              k < (v.val[iter.start.val]!).val.length / 2 →
              ∃ (g : encoding.gf.GF16),
                poly.coefficients.val[k]? = some g ∧
                g.value.val =
                  ((v.val[iter.start.val]!).val[2 * k]!).val * 256 +
                  ((v.val[iter.start.val]!).val[2 * k + 1]!).val) ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_j_lt_v : iter.start.val < v.val.length := by omega
    have h_j_lt_16 : iter.start.val < 16 := by omega
    have h_ne := h_nonempty iter.start.val h_j_lt_v
    have h_ev := h_even iter.start.val h_j_lt_v
    have h_ov := h_overflow iter.start.val h_j_lt_v
    step*
    · simp_all [alloc.vec.Vec.deref]
    · simp_all [alloc.vec.Vec.deref]
    · split
      · simp_all only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq, bind_tc_ok,
        List.getElem!_eq_getElem?_getD]
        step*
        simp_all only [getElem?_pos, Option.getD_some, ne_eq, List.length_eq_zero_iff,
          Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and, implies_true, and_self,
          not_false_eq_true, Option.some.injEq, exists_eq_left',
          core.result.Result.Ok.injEq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
          getElem!_pos,  true_and]
        subst a_post
        have hderef : ∀ (w : alloc.vec.Vec Std.U8), w.deref.val = w.val := fun _ => rfl
        simp only [hderef] at r_post2 r_post3
        constructor
        · -- out'.val[iter.start.val]! = r
          simp [*]
          grind
        · constructor-- ∀ k, k ≠ iter.start.val → out'.val[k]! = out.val[k]!
          · simp_all
          · intro k hne
            simp [*]
      · simp_all [alloc.vec.Vec.deref]
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyEncoder.from_pb_loop0
