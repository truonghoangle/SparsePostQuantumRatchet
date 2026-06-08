/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.FromPbLoop2
import Spqr.Specs.Aeneas.RangeIteratorNext

/-!
# Spec theorem for `PolyEncoder::from_pb`: loop body 1

In GF(2¹⁶) — the Galois field with 65 536 elements — each field element is represented as a
polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned integer.
The big-endian two-byte encoding satisfies `value = hi * 256 + lo` where `hi` and `lo` are the
high and low bytes respectively.

The extracted Lean function `encoding.polynomial.PolyEncoder.from_pb_loop1.body` performs one step
of the outer point-deserialization loop inside `PolyEncoder::from_pb` (the `EncoderState::Points`
branch).  Given the protobuf index `i` (of type `U32`), the vector of serialized byte vectors `v`
(corresponding to `pb.pts`), a `Range<usize>` iterator, and the current output array of 16 `Point`
values, the body calls `next` on the iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the result is
     `Ok(PolyEncoder { idx: i, s: EncoderState::Points(out) })`, wrapping the fully deserialized
     point array.
  2. **Error** (`some j` with odd-length byte vector): retrieves the `j`-th serialized byte vector
     from `v`; if its length is odd, returns `Err(SerializationInvalid)`.
  3. **Continue** (`some j` with even-length byte vector): runs the inner byte-deserialization loop
     (`from_pb_loop1_loop0`) to reconstruct GF(2¹⁶) elements from byte pairs, constructs a
     `Point { value: v_deserialized }`, and stores it in `out[j]`.

Each deserialized GF(2¹⁶) element satisfies the big-endian byte-decoding invariant: for each
index `k`, the element's `u16` value equals
  `serialized[2*k] * 256 + serialized[2*k+1]`
where `serialized` is the byte vector `v[j]`.

The function proceeds in several stages:
  1. `core.iter.range.IteratorRange.next iter` — advances the outer range iterator, yielding the
     current index `j` (when `j < NUM_POLYS`) or `none` (when the range is exhausted).
  2. `alloc.vec.Vec.index v j` — retrieves the `j`-th serialized byte vector from `v`.
  3. Parity check: `pts.len() % 2 != 0` — validates that the byte vector has even length.
  4. `from_pb_loop1_loop0` (inner loop spec from `FromPbLoop2.lean`) — deserializes all byte pairs
     in `pts` into GF(2¹⁶) elements, accumulating them into a fresh `Vec<GF16>`.
  5. `Array.update` — stores the deserialized `Point { value: v_deserialized }` in the output array
     at position `j`.

**Source**: spqr/src/encoding/polynomial.rs (lines 593:12-606:73)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.from_pb_loop1

/-! ## Inhabited instances -/

/--
`Point` wraps a `Vec<GF16>` of values.  An `Inhabited` instance is required so that
`getElem!` (`[·]!`) on arrays/lists of `Point` has a well-defined default value.  We use the empty
value vector as the canonical default.
-/
instance : Inhabited encoding.polynomial.Point := ⟨⟨alloc.vec.Vec.new _⟩⟩

/-! ## Spec theorem for the from_pb outer loop body (Points branch) -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb_loop1.body`**:

One step of the outer point-deserialization loop inside `PolyEncoder::from_pb` (the `pb.pts`
branch).  Given the protobuf index `i`, the vector of serialized byte vectors `v` (from `pb.pts`),
a range iterator over `0..NUM_POLYS`, and the current output array of 16 `Point` values, the body
retrieves the next index `j` from the iterator and either terminates or extends the output:

• The function always succeeds (no panic) provided the preconditions hold: the iterator range end
  does not exceed the vector length or the array size (16), each serialized byte vector has even
  length, and the deserialized length does not overflow.

• In the **done** case (iterator exhausted):
    the result is `Ok(PolyEncoder { idx := i, s := Points(out) })` and the iterator condition
    is negated: `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `j = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The output array is updated at position `j` with a deserialized point:
        there exists a `Point` `pt` such that
        `pt.value.val.length = (v.val[j]!).val.length / 2`
      and for every `k < (v.val[j]!).val.length / 2`:
        `∃ g, pt.value.val[k]? = some g ∧
          g.value.val = (v.val[j]!).val[2*k]!.val * 256 +
                        (v.val[j]!).val[2*k+1]!.val`

    This corresponds to the Rust body:
    ```rust
    for i in 0..NUM_POLYS {
        let pts = &pb.pts[i];
        if pts.len() % 2 != 0 {
            return Err(PolynomialError::SerializationInvalid);
        }
        let mut v = Vec::<GF16>::with_capacity(pts.len() / 2);
        for k in 0..(pts.len() / 2) {
            let j = k * 2;
            v.push(GF16::new(u16::from_be_bytes([pts[j], pts[j + 1]])));
        }
        hax_lib::assume!(v.len() <= MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1);
        out[i] = Point { value: v };
    }
    ```

This establishes that one step of the outer loop faithfully reconstructs a `Point` from its
serialized byte representation by deserializing each byte pair into a GF(2¹⁶) element via
big-endian decoding, and stores the result in the output array.

This follows from composing:
  1. `IteratorRange_next_Usize_post`: the range iterator either yields the element at the current
     position and advances the cursor, or signals exhaustion.
  2. `from_pb_loop1_loop0.loop_spec` (from `FromPbLoop2.lean`): the inner byte-deserialization
     loop faithfully reconstructs all GF(2¹⁶) elements from their big-endian two-byte encodings.

**Source**: spqr/src/encoding/polynomial.rs (lines 593:12-606:73)
-/
@[step]
theorem body_spec
    (i : Std.U32)
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (iter : core.ops.range.Range Std.Usize)
    (out : Array encoding.polynomial.Point 16#usize)
    (h_end_le_v : iter.«end».val ≤ v.val.length)
    (h_end_le_16 : iter.«end».val ≤ 16)
    (h_even : ∀ (j : Nat), j < v.val.length →
        (v.val[j]!).val.length % 2 = 0)
    (h_overflow : ∀ (j : Nat), j < v.val.length →
        (v.val[j]!).val.length / 2 ≤ Usize.max) :
    body i v iter out ⦃ cf =>
      match cf with
      | ControlFlow.done result =>
          result = core.result.Result.Ok
            { idx := i,
              s := encoding.polynomial.EncoderState.Points out } ∧
          ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, out') =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          ∃ (pt : encoding.polynomial.Point),
            out'.val[iter.start.val]! = pt ∧
            (∀ k, k ≠ iter.start.val →
              out'.val[k]! = out.val[k]!) ∧
            pt.value.val.length =
              (v.val[iter.start.val]!).val.length / 2 ∧
            (∀ (k : Nat),
              k < (v.val[iter.start.val]!).val.length / 2 →
              ∃ (g : encoding.gf.GF16),
                pt.value.val[k]? = some g ∧
                g.value.val =
                  ((v.val[iter.start.val]!).val[2 * k]!).val * 256 +
                  ((v.val[iter.start.val]!).val[2 * k + 1]!).val) ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ :=
    core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · -- cont case: iterator not exhausted
    obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_j_lt_v : iter.start.val < v.val.length := by omega
    have h_j_lt_16 : iter.start.val < 16 := by omega
    have h_ev := h_even iter.start.val h_j_lt_v
    have h_ov := h_overflow iter.start.val h_j_lt_v
    step*
    · -- goal 1: overflow precondition for inner loop
      simp only [alloc.vec.Vec.with_capacity, alloc.vec.Vec.len] at *
      grind
    · simp  [alloc.vec.Vec.with_capacity, alloc.vec.Vec.len] at *
      · grind
    · -- goal 2: cont case postcondition
      simp_all  [alloc.vec.Vec.with_capacity, alloc.vec.Vec.len]
  · -- done case: iterator exhausted
    obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyEncoder.from_pb_loop1
