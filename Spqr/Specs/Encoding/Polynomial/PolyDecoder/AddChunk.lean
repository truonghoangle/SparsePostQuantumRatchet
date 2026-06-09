/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunkLoop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::add_chunk`

In GF(2¹⁶) — the Galois field with 65 536 elements — each field element is represented as a
polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned integer.  A
cartesian evaluation point `Pt = (x, y)` packs two such elements, and a `PolyDecoder` maintains
a fixed-size array `pts : [SortedSet<Pt>; 16]` of 16 such point sets, together with a target
point count `pts_needed : Usize` and an `is_complete : bool` flag.

The function `PolyDecoder::add_chunk` absorbs one 32-byte `Chunk` (tagged with a `u16` field
`index`) into the decoder state.  It proceeds in a single stage:
  1. The chunk-absorption loop `add_chunk_loop` iterates over the 16 slot indices
     `0..16` and, at each step, conditionally pushes a freshly decoded GF(2¹⁶) cartesian point
     onto the appropriate `SortedSet<Pt>` slot.

The Rust source asserts the loop invariant
   `self.pts.len() == 16 && self.pts_needed == initial_pts_needed`
(see `src/encoding/polynomial.rs`, lines 883–885).  The first conjunct is automatic since
`self.pts : Array (SortedSet Pt) 16#usize` in the extraction; the second conjunct expresses
the function-level postcondition documented in the Rust source at line 878:
   `future(self).pts_needed == self.pts_needed`.
Furthermore, since `add_chunk` only ever mutates the `pts` field, it also preserves
`is_complete`.

**Source**: spqr/src/encoding/polynomial.rs (lines 879:4-904:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- **Spec theorem for
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk`**:

Absorption of a single 32-byte `Chunk` into the `PolyDecoder` state.  The function delegates
entirely to `add_chunk_loop` with the fixed range iterator `{ start := 0, end := 16 }`, which
drives the 16-step chunk-absorption loop to completion.

• **Postcondition** (function-level ensures clause of `PolyDecoder::add_chunk`, see
  `src/encoding/polynomial.rs`, line 878):
    `result.pts_needed = self.pts_needed ∧ result.is_complete = self.is_complete`.

  The first conjunct is the Rust postcondition `future(self).pts_needed == self.pts_needed`.
  The second conjunct is automatic since the body never mutates `is_complete`.

Because both `SortedSet → SortedVec` and `SortedVec → Vec<Pt>` deref operations are extracted
as opaque axioms (`sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref` and
`sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref`), we parameterise the spec by
state-and-index-dependent witnesses `sv` and `inner` together with the universally quantified
per-state deref equations `h_sv` and `h_inner`.

This follows from composing:
  1. `add_chunk_loop.loop_spec`: the loop drives the body to completion while preserving
     `pts_needed` and `is_complete`, starting from the initial iterator
     `{ start := 0, end := 16 }` (whose start `0 ≤ 16` and end `16 ≤ 16` discharge the
     preconditions).

This establishes that `add_chunk` faithfully maintains the decoder-state invariant
`pts_needed`/`is_complete` while absorbing each byte pair of the input chunk into the
appropriate GF(2¹⁶) cartesian-point slot.

**Source**: spqr/src/encoding/polynomial.rs (lines 879:4-904:5)
-/
@[step]
theorem add_chunk_spec
    (self : encoding.polynomial.PolyDecoder)
    (chunk : encoding.Chunk)
    (sv : encoding.polynomial.PolyDecoder → Nat → sorted_vec.SortedVec Pt)
    (inner : encoding.polynomial.PolyDecoder → Nat → alloc.vec.Vec Pt)
    (h_sv : ∀ (s : encoding.polynomial.PolyDecoder) (i : Nat),
        sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
          Pt.Insts.CoreCmpOrd
          (s.pts.val[(chunk.index.val * 16 + i) % 16]!) = ok (sv s i))
    (h_inner : ∀ (s : encoding.polynomial.PolyDecoder) (i : Nat),
        sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
          Pt.Insts.CoreCmpOrd (sv s i) = ok (inner s i)) :
    add_chunk self chunk ⦃ (result : encoding.polynomial.PolyDecoder) =>
      result.pts_needed = self.pts_needed ∧
      result.is_complete = self.is_complete ⦄ := by
  unfold add_chunk
  step*

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
