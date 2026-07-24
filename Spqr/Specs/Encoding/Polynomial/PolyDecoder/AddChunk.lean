/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunkLoop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{impl spqr::encoding::Decoder for spqr::encoding::polynomial::PolyDecoder}::add_chunk`

The extracted Lean function
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk` is the top-level entry
point of the `Decoder::add_chunk` implementation for `PolyDecoder`.  It absorbs one `Chunk`
(containing a 16-bit chunk index and 32 bytes of evaluation data) into the decoder's
per-polynomial point sets by running the point-absorption loop over the fixed index range
`0..16`:

  `add_chunk self chunk = add_chunk_loop { start := 0, end := 16 } self chunk`

The function introduces no additional logic beyond fixing the iterator range and delegating to
`add_chunk_loop`, so its postcondition is inherited from the corresponding `add_chunk_loop`
specification (`loop_spec` from `AddChunkLoop0.lean`), specialised to the concrete iterator
`{ start := 0, end := 16 }`.

In GF(2¹⁶) — the Galois field with 65 536 elements — each field element is represented as a
polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned integer.  A
cartesian point `Pt = (x, y)` packs two such elements.  For each loop index `k ∈ {0, …, 15}` the
decoder decodes an evaluation point from the chunk's serialized data:

  `x = GF16::new(chunk.index)`                    — the x-coordinate is the chunk index,
  `y = GF16::new((data[2k] << 8) + data[2k+1])`  — the y-coordinate is big-endian decoded,

and conditionally absorbs `Pt { x, y }` into `self.pts[k]` (via the opaque `SortedSet::push`)
whenever the point is needed or has a small index.

Since the whole range `0..16` is traversed, every slot `k < 16` of the `pts` array is visited
exactly once and extended by at most one point, while slots `k ≥ 16` (structurally absent, since
`pts : Array (SortedSet Pt) 16#usize`) are untouched.

This directly reflects the Rust ensures clause
  `#[hax_lib::ensures(|_| future(self).pts_needed == self.pts_needed)]`
together with the loop invariant
  `self.pts.len() == 16 && self.pts_needed == initial_pts_needed`.
(The `pts.len() == 16` part is structural in Lean.)

The proof unfolds `add_chunk` to expose the underlying `add_chunk_loop` call over the concrete
range `{ start := 0, end := 16 }` and discharges the resulting goal with the already-registered
`add_chunk_loop.loop_spec`, whose preconditions (`iter.end.val ≤ 16`,
`iter.start.val ≤ iter.end.val`) hold trivially for `0..16`.

**Source**: spqr/src/encoding/polynomial.rs (lines 879:4-904:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-! ## Spec theorem for `add_chunk` -/

/-- **Spec theorem for
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk`**:

The top-level `Decoder::add_chunk` for `PolyDecoder`.  Given the current decoder state `self` and
a `Chunk` containing 32 bytes of evaluation data together with a 16-bit chunk index, the function
runs the point-absorption loop over `0..16` and returns the updated decoder state.

• The function always succeeds (no panic) provided the preconditions hold: the chunk index
  multiplication does not overflow Usize (`chunk.index * 16 + 16 ≤ Usize.max`), and each
  sorted-set slot in `self.pts` has sufficient capacity headroom
  (`(self.pts.val[k]!).length + 2 ≤ Usize.max`).

• **Postcondition**:
  The decoder's key fields are preserved through all iterations:
    `result.pts_needed = self.pts_needed`,
    `result.is_complete = self.is_complete`.

  Each slot `k < 16` has a corresponding GF(2¹⁶) evaluation point `p` constructed from the chunk
  data:
    `p.x.value = chunk.index`  — the chunk index as a GF(2¹⁶) element,
    `p.y.value.val = 256 * data[2k] + data[2k+1]`  — big-endian decoded y-coordinate.
  and either:
    (a) the point was pushed: `result.pts.val[k]!.val = self.pts.val[k]!.val ++ [p]`, or
    (b) the slot is unchanged: `result.pts.val[k]! = self.pts.val[k]!`.

  (Slots `k ≥ 16` need no clause: `pts` has exactly 16 elements, so both sides collapse to the
  `Inhabited` default and are trivially equal.)

  This corresponds to the Rust function:
  ```rust
  #[hax_lib::ensures(|_| future(self).pts_needed == self.pts_needed)]
  fn add_chunk(&mut self, chunk: &Chunk) {
      for i in 0usize..16 {
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
      }
  }
  ```

This establishes that `add_chunk` faithfully processes all 16 evaluation points from the chunk's
serialized data and conditionally absorbs them into the decoder's per-polynomial point sets via
the opaque `SortedSet::push` operation, while preserving the decoder's `pts_needed` and
`is_complete` fields, and recording per-slot point absorption.

The proof unfolds `add_chunk` to expose the underlying `add_chunk_loop` call over the concrete
range `{ start := 0, end := 16 }` and specialises the already-registered
`add_chunk_loop.loop_spec`.

**Source**: spqr/src/encoding/polynomial.rs (lines 879:4-904:5)
-/
@[step]
theorem add_chunk_spec
    (self : encoding.polynomial.PolyDecoder) (chunk : encoding.Chunk)
    (h_idx_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_room : ∀ k, k < 16 →
      (self.pts.val[k]!).length + 2 ≤ Usize.max) :
    add_chunk self chunk ⦃ (result : encoding.polynomial.PolyDecoder) =>
      result.pts_needed = self.pts_needed ∧
      result.is_complete = self.is_complete ∧
      (∀ k, k < 16 →
        ∃ (p : Pt),
          p.x.value = chunk.index ∧
          p.y.value.val = 256 * (chunk.data[k * 2]!) + (chunk.data[k * 2 + 1]!) ∧
          (result.pts.val[k]!.val = self.pts.val[k]!.val ++ [p] ∨
           result.pts.val[k]! = self.pts.val[k]!)) ⦄ := by
  unfold add_chunk
  have h := add_chunk_loop.loop_spec { start := 0#usize, «end» := 16#usize } self chunk
    (by scalar_tac) (by scalar_tac) h_idx_overflow h_push_room
  apply WP.spec_mono h
  rintro result ⟨h_pn, h_ic, h_proc, _h_unch⟩
  refine ⟨h_pn, h_ic, fun k hk => h_proc k (Nat.zero_le k) (by scalar_tac)⟩

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
