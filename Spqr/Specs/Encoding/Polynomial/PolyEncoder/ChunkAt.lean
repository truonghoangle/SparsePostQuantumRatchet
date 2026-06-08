/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.Basic.Defs
import Spqr.Math.Poly.Basic.Zero
import Spqr.Math.Poly.Coeff.Basic
import Spqr.Math.Poly.Coeff.ListOps
import Spqr.Math.Poly.CharTwo.Basic
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Math.Poly.Eval
import Spqr.Math.Poly.LinearFactors.Basic
import Spqr.Math.Poly.LinearFactors.Degree
import Spqr.Math.Poly.Lagrange.DenomProd
import Spqr.Math.Poly.Lagrange.BasisPoly
import Spqr.Math.Poly.Lagrange.InterpolantSum
import Spqr.Math.Poly.Horner.Defs
import Spqr.Math.Poly.Horner.Eval
import Spqr.Math.Poly.ExpectedTrailing.Defs
import Spqr.Math.Poly.ExpectedTrailing.Basic
import Spqr.Math.Poly.Identities.Basic
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAtLoop0
import Spqr.Specs.Aeneas.TryFromSliceToArray
import Spqr.Specs.Aeneas.VecIndexRangeFull
import Spqr.Specs.Aeneas.ResultExpect

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::chunk_at`

The method `PolyEncoder::chunk_at` serializes one "chunk" of 16 polynomial evaluations into a
32-byte `Chunk`.  Given a mutable reference to the encoder state and a chunk index `idx : U16`,
the function:

  1. Allocates an output byte vector `out` with capacity 32.
  2. Iterates `i` over `0..16`, at each step computing
       `total_idx = (idx as usize) * 16 + i`
       `poly      = total_idx % 16 = i`
       `poly_idx  = total_idx / 16 = idx.val`
     and evaluating `self.point_at(i, idx.val)` to obtain a GF(2¹⁶) value `g`.
     The 2-byte big-endian encoding of `g.value` is appended to `out`:
       `out ← out ++ [(g.value >> 8) as u8, g.value as u8]`
  3. Converts the resulting 32-byte vector to a fixed-size array `[u8; 32]` via
     `try_into().expect("should be exactly 32 bytes")`.
  4. Returns `Chunk { index: idx, data: array }` together with the (possibly updated)
     encoder state.

Since each of the 16 iterations contributes exactly 2 bytes, the output vector has length
exactly 32 at the end of the loop, and the `try_into` conversion always succeeds.

The function composes:
  1. `chunk_at_loop` — the serialization loop driving `chunk_at_loop.body` through all 16
     polynomial evaluations.
  2. `Vec::index` with `RangeFull` — to obtain a slice `&[u8]` of the output vector.
  3. `<[u8; 32] as TryFrom<&[u8]>>::try_from` — to convert the 32-byte slice to a fixed-size
     array.
  4. `Result::expect` — to unwrap the (always-`Ok`) conversion result.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the
16-bit encodings; multiplication is carry-less polynomial multiplication modulo the irreducible
polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 694:4-710:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder

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

/-! ## Spec theorems -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.chunk_at`** (byte-level):

Serializes one chunk of 16 polynomial evaluations into a 32-byte `Chunk`.  The postcondition
captures the byte-level encoding of the GF(2¹⁶) evaluation values.

The result satisfies:
  * `chunk.index = idx` — the chunk index is preserved in the output.
  * `chunk.data.val.length = 32` — the data array contains exactly 32 bytes.
  * `self'.idx = self.idx` — the encoder's chunk index field is preserved.
  * If the encoder was initially in the `Polys` state, the encoder state is unchanged:
      `∀ polys, self.s = .Polys polys → self' = self`.
  * For every `j ∈ [0, 16)`, the big-endian encoding invariant holds:
      `∃ g hi lo, chunk.data.val[2*j]? = some hi ∧
        chunk.data.val[2*j+1]? = some lo ∧
        hi.val * 256 + lo.val = g.value.val`

This follows from composing:
  1. `chunk_at_loop.loop_spec`: the serialization loop produces a 32-byte vector with the
     big-endian encoding invariant for each of the 16 evaluations.
  2. `alloc.vec.Vec.index_RangeFull_spec`: `Vec::index` with `RangeFull` returns a slice
     whose elements are exactly the vector's elements.
  3. `TryFromArrayCopySlice.try_from_spec`: the 32-byte slice is converted to a fixed-size
     array `[u8; 32]` preserving all elements.
  4. `core.result.Result.expect_ok_spec`: unwraps the (always-`Ok`) conversion result.

    This corresponds to the Rust function:
    ```rust
    pub fn chunk_at(&mut self, idx: u16) -> Chunk {
        let mut out = Vec::with_capacity(32);
        for i in 0..16 {
            let total_idx = (idx as usize) * 16 + i;
            let poly = total_idx % 16;
            let poly_idx = total_idx / 16;
            let p = self.point_at(poly, poly_idx).value;
            out.push((p >> 8) as u8);
            out.push(p as u8);
        }
        Chunk {
            index: idx,
            data: (&out[..]).try_into().expect("should be exactly 32 bytes"),
        }
    }
    ```

**Source**: spqr/src/encoding/polynomial.rs (lines 694:4-710:5)
-/
theorem chunk_at_spec_nat
    (self : encoding.polynomial.PolyEncoder) (idx : Std.U16)
    (h_idx_overflow : idx.val * 16 + 16 ≤ Usize.max)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts.val[j]!).value.val.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ (polys : Array encoding.polynomial.Poly 16#usize),
        ∀ (j : Nat), j < 16 →
          (polys.val[j]!).coefficients.val.length + 1 ≤ Usize.max) :
    chunk_at self idx ⦃ ((chunk, self') :
        encoding.Chunk × encoding.polynomial.PolyEncoder) =>
      chunk.index = idx ∧
      chunk.data.val.length = 32 ∧
      self'.idx = self.idx ∧
      (∀ polys, self.s = .Polys polys → self' = self) ∧
      (∀ (j : Nat), j < 16 →
        ∃ (g : encoding.gf.GF16) (hi lo : Std.U8),
          chunk.data.val[2 * j]? = some hi ∧
          chunk.data.val[2 * j + 1]? = some lo ∧
          hi.val * 256 + lo.val = g.value.val) ⦄ := by
  unfold chunk_at
  step*
  · simp [alloc.vec.Vec.with_capacity]
    grind
  · simp_all  [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
      List.length_nil]
  simp  [core.result.Result.expect]
  split
  · simp_all
    grind  -- Establish that r.val = out1.val (via s)
  · simp_all

/--
For any encoder state, `chunk_at self idx` returns a `Chunk` whose `index` field equals `idx` and
whose `data` array contains exactly 32 bytes — the concatenation of the 2-byte big-endian encodings
of 16 GF(2¹⁶) polynomial evaluations.  The encoder's chunk index field `idx` is preserved, and if
the encoder was in the `Polys` state, the state is entirely unchanged.

This theorem lifts the byte-level postcondition of `chunk_at_spec_nat` to a form suitable for
composition in higher-level proofs (e.g. `next_chunk`, `encode_bytes_base`), dropping the explicit
byte-encoding invariant while retaining the structural and state-preservation properties.
-/
@[step]
theorem chunk_at_spec
    (self : encoding.polynomial.PolyEncoder) (idx : Std.U16)
    (h_idx_overflow : idx.val * 16 + 16 ≤ Usize.max)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts.val[j]!).value.val.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ (polys : Array encoding.polynomial.Poly 16#usize),
        ∀ (j : Nat), j < 16 →
          (polys.val[j]!).coefficients.val.length + 1 ≤ Usize.max) :
    chunk_at self idx ⦃ ((chunk, self') :
        encoding.Chunk × encoding.polynomial.PolyEncoder) =>
      chunk.index = idx ∧
      chunk.data.val.length = 32 ∧
      self'.idx = self.idx ∧
      (∀ polys, self.s = .Polys polys → self' = self) ⦄ := by
  have h_raw := chunk_at_spec_nat self idx h_idx_overflow h_admissible h_coeff_bound
  apply WP.spec_mono h_raw
  intro (chunk, self') ⟨h_index, h_len, h_idx, h_stable, _⟩
  exact ⟨h_index, h_len, h_idx, h_stable⟩

end spqr.encoding.polynomial.PolyEncoder
