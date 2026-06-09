/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf16.Field
import Spqr.Specs.Aeneas.GF16New
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NecessaryPoints

/-!
# Spec theorem for `PolyDecoder::add_chunk`: loop body 0

In GF(2¹⁶) — the Galois field with 65 536 elements — each field element is represented as a
polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned integer.  A
cartesian evaluation point `Pt = (x, y)` packs two such elements.

The extracted Lean function
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop.body` performs one
step of the chunk-absorption loop inside `PolyDecoder::add_chunk`.  Given a `Chunk` (a 32-byte
data buffer tagged with a `u16` field `index`), a range iterator over `0..16`, and the current
decoder state `self`, the body proceeds in two stages:

  1. `IteratorRange.next` on `iter` — either signals **done** (the iterator is exhausted and
     `self` is returned unchanged) or yields the next slot index `i = iter.start`.
  2. In the **cont** case, the absolute point index
       `total_idx = chunk.index · 16 + i`
     is split into a polynomial slot `poly = total_idx % 16` and an evaluation argument
     `poly_idx = total_idx / 16`; the next pair of bytes in `chunk.data` is decoded into the
     GF(2¹⁶) cartesian point
       `Pt { x = GF16(poly_idx),
             y = GF16(chunk.data[2·i] · 256 + chunk.data[2·i+1]) }`
     and *conditionally* pushed onto `self.pts[poly]`:
       - if `poly_idx < self.necessary_points(i)`, push unconditionally;
       - otherwise, deref `self.pts[poly]` twice (`SortedSet → SortedVec → Vec<Pt>`) and push
         only when the current point set still has fewer than `necessary_points(i)` elements.

The loop invariant maintained by `add_chunk` in the Rust source is
   `self.pts.len() == 16 && self.pts_needed == initial_pts_needed`
(see `src/encoding/polynomial.rs`, lines 883–885).  The first conjunct is automatic because
`self.pts : Array (SortedSet Pt) 16#usize` in the extraction.  The second conjunct says that
the body preserves `pts_needed`; the body also preserves `is_complete`, since only the `pts`
field is ever mutated.

**Source**: spqr/src/encoding/polynomial.rs (lines 882:8-903:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

/-- **Spec theorem for
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop.body`**:

One step of the chunk-absorption loop inside `PolyDecoder::add_chunk`.  Given a `Chunk`, a
range iterator over `0..16`, and the current decoder state `self`, the body retrieves the next
slot index `i` from the iterator and either terminates or conditionally extends one of the 16
`SortedSet<Pt>` slots with a freshly decoded GF(2¹⁶) cartesian point.

The body spec composes:
  1. `IteratorRange.next` — to advance the range iterator over slot indices `0..16`.
  2. Arithmetic on `Usize`/`U16` — to compute `total_idx`, `poly`, `poly_idx`, `y1`, `y2`,
     `y1 << 8`, and the GF(2¹⁶) coordinates.  All intermediate values fit without overflow:
     - `chunk.index.val · 16 + iter.start.val ≤ 65535 · 16 + 15 < Usize.max`;
     - `poly_idx = total_idx / 16 ≤ chunk.index.val ≤ U16.max`;
     - `y1 < 256`, hence `y1 << 8 < 65536`, and `(y1 << 8) + y2 ≤ U16.max`.
  3. `encoding.gf.GF16.new` (spec from `Aeneas/GF16New.lean`) — to build the GF(2¹⁶)
     coordinates of the new point.
  4. `PolyDecoder.necessary_points` (spec from `NecessaryPoints.lean`) — to compute the number
     of points the slot still needs.
  5. `Array.index_mut_usize` / `Array.index_usize` — to access `self.pts[poly]`.  These succeed
     because `poly = total_idx % 16 < 16 = self.pts.length`.
  6. `sorted_vec.SortedSet.push` — the extracted opaque model, whose `push_spec` axiom simply
     discharges the call as `ok ((0, none), default)`.

Because the `else` branch dereferences `self.pts[poly]` through the opaque axioms
`SortedSet → SortedVec → Vec<Pt>`, we parameterise the spec by deref witnesses `sv` and
`inner` together with the per-call equations `h_sv` and `h_inner` (guarded by `iter.start.val <
iter.«end».val`, so they are vacuously true in the done case).

The postcondition then asserts:

• **done case** (iterator exhausted):
    `self' = self ∧ ¬ (iter.start.val < iter.«end».val)`.

• **cont case** (received slot index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted;
    - the iterator has advanced by one: `iter1.start.val = iter.start.val + 1` and
      `iter1.«end» = iter.«end»`;
    - the loop invariant of `add_chunk` (`src/encoding/polynomial.rs`, line 884) is preserved:
      `self'.pts_needed = self.pts_needed` and `self'.is_complete = self.is_complete`, while
      `self'.pts` is the original array with at most one of its 16 slots replaced (by the
      opaque-model `default : SortedSet Pt`).

This corresponds to the Rust body:
```rust
for i in 0usize..16 {
    let total_idx = (chunk.index as usize) * 16 + i;
    let poly = total_idx % 16;
    let poly_idx = total_idx / 16;
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
```

This establishes that one step of the `add_chunk` loop preserves the `pts_needed` /
`is_complete` invariant of `PolyDecoder` while absorbing a single byte pair of the chunk into
the appropriate polynomial slot.

**Source**: spqr/src/encoding/polynomial.rs (lines 882:8-903:9)
-/
@[step]
theorem body_spec
    (chunk : encoding.Chunk)
    (iter : core.ops.range.Range Std.Usize)
    (self : encoding.polynomial.PolyDecoder)
    (h_end_le_16 : iter.«end».val ≤ 16)
    (sv : sorted_vec.SortedVec Pt)
    (inner : alloc.vec.Vec Pt)
    (_h_sv : ∀ (_ : iter.start.val < iter.«end».val),
        sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
          Pt.Insts.CoreCmpOrd
          (self.pts.val[(chunk.index.val * 16 + iter.start.val) % 16]!)
          = ok sv)
    (_h_inner : ∀ (_ : iter.start.val < iter.«end».val),
        sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
          Pt.Insts.CoreCmpOrd sv = ok inner) :
    body chunk iter self ⦃ cf =>
      match cf with
      | ControlFlow.done self' =>
          self' = self ∧ ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, self') =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          self'.pts_needed = self.pts_needed ∧
          self'.is_complete = self.is_complete ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ :=
    core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · -- cont case: iterator yields the current slot index `i`
    obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    simp [bind_tc_ok]
    have h_i_lt_16 : iter.start.val < 16 := by omega
    have h_chunk_idx_le : chunk.index.val ≤ UScalar.max .U16 := by
      have := chunk.index.hBounds; grind
    -- Discharge the opaque derefs using the supplied witnesses
    step*
  · -- done case: iterator exhausted
    obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop
