/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt
import Spqr.Specs.Aeneas.RangeIteratorNext

/-!
# Spec theorem for `PolyEncoder::chunk_at`: loop body 0

The Rust method `PolyEncoder::chunk_at` (in `src/encoding/polynomial.rs`, lines 694–710) serializes
one "chunk" of 16 polynomial evaluations into a 32-byte vector.  The loop (lines 697:8–705:9)
iterates `i` over `0..16` and, at each step, computes:
  `total_idx = (idx as usize) * 16 + i`
  `poly      = total_idx % 16`
  `poly_idx  = total_idx / 16`
  `p         = self.point_at(poly, poly_idx).value`
then appends `(p >> 8) as u8` and `p as u8` to the output byte vector.

Since `0 ≤ i < 16`, the modular/division decomposition simplifies to `poly = i` (the loop index)
and `poly_idx = idx.val` (the chunk index).  Thus the loop body evaluates the `i`-th polynomial at
the chunk index and serializes the GF(2¹⁶) result as two big-endian bytes.

The extracted Lean function `encoding.polynomial.PolyEncoder.chunk_at_loop.body` performs one step
of this serialization loop.  Given a chunk index `idx : U16`, a `Range<usize>` iterator, the
encoder state `self`, and the current output byte vector `out`, the body calls `next` on the
iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the encoder state and output vector are
     returned unchanged.
  2. **Continue** (`some i`): evaluates `self.point_at(i, idx)` to obtain a GF(2¹⁶) value `g`,
     and appends the 2-byte big-endian encoding of `g.value` to `out`:
       `out' = out ++ [hi, lo]`  where  `hi * 256 + lo = g.value`.

The loop invariant maintained across iterations is `out.len() == 2 * i`, i.e., each polynomial
evaluation contributes exactly 2 bytes to the serialized output.  The big-endian encoding satisfies:
  `out[2*j] * 256 + out[2*j+1] = point_at(j, idx).value.val`  for all `j < i`.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the
16-bit encodings; multiplication is carry-less polynomial multiplication modulo the irreducible
polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

The body spec composes:
  1. `IteratorRange.next` — to advance the range iterator.
  2. Usize arithmetic: `total_idx = idx * 16 + i`, `poly = total_idx % 16`,
     `poly_idx = total_idx / 16`.
  3. `PolyEncoder.point_at` (spec from `PointAt.lean`) — to evaluate the polynomial at the given
     point in GF(2¹⁶).
  4. Bit-shift and cast: `(g.value >>> 8) as u8` (high byte), `g.value as u8` (low byte).
  5. Two `Vec::push` calls — to append the big-endian bytes to the output.

**Source**: spqr/src/encoding/polynomial.rs (lines 697:8-705:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder.chunk_at_loop

/-! ## Inhabited instances -/

/--
`Poly` wraps a `Vec<GF16>` of coefficients.  An `Inhabited` instance is required so that
`getElem!` (`[·]!`) on arrays/lists of `Poly` has a well-defined default value.  We use the empty
coefficient vector as the canonical default.
-/
instance : Inhabited encoding.polynomial.Poly := ⟨⟨alloc.vec.Vec.new _⟩⟩

/--
`Point` wraps a `Vec<GF16>`.  An `Inhabited` instance is required so that `getElem!` (`[·]!`)
on arrays/lists of `Point` has a well-defined default value.  We use the empty value vector
as the canonical default.
-/
instance : Inhabited encoding.polynomial.Point := ⟨⟨alloc.vec.Vec.new _⟩⟩


/-- **Spec theorem for `encoding.polynomial.PolyEncoder.chunk_at_loop.body`**:

One step of the chunk serialization loop inside `PolyEncoder::chunk_at`.  Given the chunk index
`idx : U16`, a range iterator over `0..16`, the encoder state `self`, and the current output byte
vector `out`, the body retrieves the next loop index `i` from the iterator and either terminates
or extends the output:

• The function always succeeds (no panic) provided the preconditions hold: the iterator range end
  does not exceed 16, the total index computation does not overflow Usize, the output vector has
  room for two more bytes, and the encoder state satisfies the admissibility conditions required by
  `point_at` (admissible point vector lengths for the Points state, bounded coefficient lengths for
  the Polys state).

• In the **done** case (iterator exhausted):
    the encoder state and output vector are returned unchanged, and the iterator condition is
    negated: `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The output byte vector is extended by exactly two bytes — the big-endian encoding of
      the GF(2¹⁶) value `g` returned by `point_at(i, idx.val)` where `i = iter.start.val`:
        `out1.val = out.val ++ [hi, lo]`
      where `hi.val * 256 + lo.val = g.value.val`.
    - The encoder state `self1` preserves its `idx` field (`self1.idx = self.idx`), and the
      returned GF(2¹⁶) value `g` is consistent with the encoder's state:
      · **Points, cache hit** (`idx.val < pts[i].value.len()`):
          `g = pts[i].value[idx.val]` and `self1 = self`.
      · **Points, cache miss** (all points are interpolated into polynomials):
          `g.toGF216 = polys'[i].toGF216Poly.eval (idx.val.toGF216)`.
      · **Polys**: `g.toGF216 = polys[i].toGF216Poly.eval (idx.val.toGF216)` and `self1 = self`.

    This corresponds to the Rust body:
    ```rust
    let total_idx = (idx as usize) * 16 + i;
    let poly = total_idx % 16;
    let poly_idx = total_idx / 16;
    let p = self.point_at(poly, poly_idx).value;
    out.push((p >> 8) as u8);
    out.push(p as u8);
    ```

**Source**: spqr/src/encoding/polynomial.rs (lines 697:8-705:9)
-/
@[step]
theorem body_spec
    (idx : Std.U16) (iter : core.ops.range.Range Std.Usize)
    (self : encoding.polynomial.PolyEncoder) (out : alloc.vec.Vec Std.U8)
    (h_end_le : iter.«end».val ≤ 16)
    (h_idx_overflow : idx.val * 16 + 16 ≤ Usize.max)
    (h_out_overflow : out.val.length + 2 ≤ Usize.max)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts.val[j]!).value.val.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_polys : ∀ polys, self.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys.val[j]!).coefficients.val.length + 1 ≤ Usize.max) :
    body idx iter self out ⦃ cf =>
      match cf with
      | ControlFlow.done (self', out') =>
          self' = self ∧ out' = out ∧ ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, self1, out1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          ∃ (g : encoding.gf.GF16) (hi lo : Std.U8),
            out1.val = out.val ++ [hi, lo] ∧
            hi.val * 256 + lo.val = g.value.val ∧
            self1.idx = self.idx ∧
            match self.s with
            | .Points pts =>
                if idx.val < (pts.val[iter.start.val]!).value.val.length then
                  g = (pts.val[iter.start.val]!).value.val[idx.val]! ∧
                  self1 = self
                else
                  ∃ (polys' : Array encoding.polynomial.Poly 16#usize),
                    self1.s = encoding.polynomial.EncoderState.Polys polys' ∧
                    g.toGF216 =
                      (polys'.val[iter.start.val]!).toGF216Poly.eval
                        (idx.val.toGF216)
            | .Polys polys =>
                g.toGF216 =
                  (polys.val[iter.start.val]!).toGF216Poly.eval
                    (idx.val.toGF216) ∧
                self1 = self ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ :=
    core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · -- cont case: iterator not exhausted
    obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_16 : iter.start.val < 16 := by omega
    -- The total_idx arithmetic: since i < 16, poly = i and poly_idx = idx.val
    -- We need: (idx.val * 16 + i) % 16 = i  and  (idx.val * 16 + i) / 16 = idx.val
    have h_mod : (idx.val * 16 + iter.start.val) % 16 = iter.start.val := by omega
    have h_div : (idx.val * 16 + iter.start.val) / 16 = idx.val := by omega
    have h_i_mod_self : iter.start.val % 16 = iter.start.val := by omega
    step*
    · grind
    · simp_all
    -- Remaining goal: ∃ g_1, byte_eq ∧ match_on_self.s
      have h_i_mod : iter.start.val % 16 = iter.start.val := by omega
      refine ⟨g, ?_, ?_⟩
      · -- byte encoding: ↑(UScalar.cast U8 i3) * 256 + ↑(UScalar.cast U8 g.value) = ↑g.value
        simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, Nat.reducePow,
                  i3_post1, Nat.shiftRight_eq_div_pow]
        grind
      · -- match case from g_post with `% 16` simplified
        simp only [h_i_mod] at g_post
        convert g_post.2 using 2 <;> simp_all
  · -- done case: iterator exhausted
    obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, rfl, h_lt⟩

end spqr.encoding.polynomial.PolyEncoder.chunk_at_loop
