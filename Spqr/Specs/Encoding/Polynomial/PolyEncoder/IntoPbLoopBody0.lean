/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPbLoop1

/-!
# Spec theorem for `PolyEncoder::into_pb`: loop body 0

The extracted Lean function `encoding.polynomial.PolyEncoder.into_pb_loop0.body` performs one step
of the outer point-serialization loop inside `PolyEncoder::into_pb`.  Given a fixed-size array
`points` of 16 `Point` values (each containing a vector of GF(2¹⁶) coefficients), a
`Range<usize>` iterator, and the current output vector of byte vectors `v`, the body calls `next`
on the iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the output vector `v` is returned unchanged.
  2. **Continue** (`some j`): retrieves the `j`-th `Point` from `points`, serializes its `.value`
     field (a vector of GF(2¹⁶) elements) into a byte vector using the inner coefficient-
     serialization loop (`into_pb_loop0_loop0`), and pushes the resulting byte vector onto `v`.

The loop invariant maintained across iterations is `v.val.length == iter.start.val`, i.e., each
`Point` contributes exactly one serialized byte vector to the output.  Each byte vector contains
the 2-byte big-endian encoding of every GF(2¹⁶) coefficient in the corresponding `Point`'s value
vector:
  `serialized.val[2*k] * 256 + serialized.val[2*k+1] = point.value[k].value.val`

The body spec composes:
  1. `IteratorRange.next` — to advance the outer range iterator.
  2. `Array.index_usize` — to retrieve the `j`-th point.
  3. `into_pb_loop0_loop0` (inner loop spec from `IntoPbLoop1.lean`) — to serialize the point's
     GF(2¹⁶) coefficients into a byte vector.
  4. `Vec.push` — to append the serialized byte vector to the output.

**Source**: spqr/src/encoding/polynomial.rs (lines 551:16-562:17)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.into_pb_loop0

/-! ## Inhabited instance for `Point` -/

/--
`Point` wraps a `Vec<GF16>`.  An `Inhabited` instance is required so that `getElem!` (`[·]!`)
on arrays/lists of `Point` has a well-defined default value.  We use the empty coefficient vector
as the canonical default.
-/
instance : Inhabited encoding.polynomial.Point := ⟨⟨alloc.vec.Vec.new _⟩⟩

/-! ## Spec theorem for the into_pb outer loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb_loop0.body`**:

One step of the outer serialization loop inside `PolyEncoder::into_pb`.  Given the fixed-size array
`points` of 16 `Point` values, a range iterator over `0..points.len()`, and the current output
vector of serialized byte vectors `v`, the body retrieves the next index `j` from the iterator and
either terminates or extends the output:

• The function always succeeds (no panic) provided the preconditions hold: the iterator range end
  does not exceed the array length (ensuring that `points[j]` is within bounds), the output vector
  has room for one more entry without exceeding `Usize.max`, and each point's GF(2¹⁶) coefficient
  vector can be serialized without overflow.

• In the **done** case (iterator exhausted):
    the output vector `v` is returned unchanged, and the iterator condition is negated:
    `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `j = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The output vector is extended by exactly one entry — the serialized byte vector for the
      `j`-th point's GF(2¹⁶) coefficients:
        `v1.val = v.val ++ [serialized]`
      where `serialized` is the result of the inner serialization loop (`into_pb_loop0_loop0`)
      applied to `points[j].value`, satisfying:
        `serialized.val.length = 2 * (points[j].value).val.length`
      and for every `k < (points[j].value).val.length`:
        `∃ hi lo, serialized.val[2*k]? = some hi ∧ serialized.val[2*k+1]? = some lo ∧
          hi.val * 256 + lo.val = ((points[j].value).val[k]!).value.val`

    This corresponds to the Rust body:
    ```rust
    let pts = &points[j].value;
    let mut v = Vec::<u8>::with_capacity(2 * pts.len());
    for i in 0..pts.len() {
        let pt = pts[i];
        v.extend_from_slice(&pt.value.to_be_bytes()[..]);
    }
    out.pts.push(v);
    ```

**Source**: spqr/src/encoding/polynomial.rs (lines 551:16-562:17)
-/
@[step]
theorem body_spec
    (points : Array encoding.polynomial.Point 16#usize)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h_end_le : iter.«end».val ≤ points.val.length)
    (h_out_overflow : v.val.length + 1 ≤ Usize.max)
    (h_inner_overflow : ∀ (j : Nat), j < points.val.length →
        2 * (points.val[j]!).value.val.length + 2 ≤ Usize.max) :
    body points iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, v1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          ∃ (serialized : alloc.vec.Vec Std.U8),
            v1.val = v.val ++ [serialized] ∧
            serialized.val.length =
              2 * (points.val[iter.start.val]!).value.val.length ∧
            ∀ (k : Nat),
              k < (points.val[iter.start.val]!).value.val.length →
              ∃ (hi lo : Std.U8),
                serialized.val[2 * k]? = some hi ∧
                serialized.val[2 * k + 1]? = some lo ∧
                hi.val * 256 + lo.val =
                  ((points.val[iter.start.val]!).value.val[k]!).value.val ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_j_lt : iter.start.val < points.val.length := by omega
    have h_inner := h_inner_overflow iter.start.val h_j_lt
    step*
    · simp_all
      grind
    · simp_all [alloc.vec.Vec.with_capacity]
    · simp_all
      grind
    · simp_all
      grind
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyEncoder.into_pb_loop0
