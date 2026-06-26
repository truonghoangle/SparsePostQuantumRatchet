/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunkLoopBody0

/-!
# Spec theorem for `PolyDecoder::add_chunk`: loop 0

In GF(2¹⁶) — the Galois field with 65 536 elements — each field element is represented as a
polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned integer.  A
cartesian evaluation point `Pt = (x, y)` packs two such elements.

The extracted Lean function
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop` is the
chunk-absorption loop inside `PolyDecoder::add_chunk`.  Given a range iterator over slot
indices `0..16`, the current decoder state `self`, and the input `Chunk`, the loop repeatedly
invokes
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop.body`, which at each
step:

  1. Calls `next` on the range iterator to obtain the current slot index `i`.
  2. Computes
       `total_idx = chunk.index · 16 + i`,
       `poly     = total_idx % 16`,
       `poly_idx = total_idx / 16`.
  3. Decodes the next pair of bytes in `chunk.data` into the GF(2¹⁶) cartesian point
       `Pt { x = GF16(poly_idx),
             y = GF16(chunk.data[2·i] · 256 + chunk.data[2·i+1]) }`.
  4. Conditionally pushes the resulting point onto `self.pts[poly]` (either unconditionally when
     `poly_idx < self.necessary_points(i)`, or only when the slot still has fewer than
     `necessary_points(i)` elements).

**Loop invariant**: across iterations the fields `pts_needed` and `is_complete` of the running
decoder state are unchanged — only the `pts` array can be mutated.  This is the loop invariant
asserted in the Rust source at `src/encoding/polynomial.rs`, line 884.

The body spec (`body_spec` from `AddChunkLoopBody0.lean`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`iter'.«end».val − iter'.start.val`) to give the full loop postcondition.

Because both `SortedSet → SortedVec` and `SortedVec → Vec<Pt>` deref operations are extracted as
opaque axioms (`sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref` and
`sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref`), we parameterise the spec by
state-and-index-dependent witnesses `sv` and `inner` together with the universally quantified
per-state deref equations.

**Source**: spqr/src/encoding/polynomial.rs (lines 882:8-903:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

/-- **Spec theorem for
`encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop`**:

The full chunk-absorption loop inside `PolyDecoder::add_chunk`.  Given a range iterator `iter`
over slot indices, the current decoder state `self`, the input `Chunk`, and the per-state
double-deref witnesses `sv` and `inner`, the loop drives the body to completion and returns the
updated decoder.

• The function always succeeds (no panic) provided the preconditions hold: the iterator end
  does not exceed `16` (`iter.«end».val ≤ 16`), the cursor does not exceed the end
  (`iter.start.val ≤ iter.«end».val`), and for every reachable decoder state `s` and slot
  index `i` the two opaque derefs of `s.pts[(chunk.index · 16 + i) % 16]` return `ok (sv s i)`
  and `ok (inner s i)` respectively.

• **Loop postcondition** (loop invariant of `PolyDecoder::add_chunk`, see
  `src/encoding/polynomial.rs`, line 884):
    `result.pts_needed = self.pts_needed ∧ result.is_complete = self.is_complete`.

  The first conjunct `self.pts.len() == 16` from the Rust loop invariant is automatic since
  `self.pts : Array (SortedSet Pt) 16#usize` in the extraction; the second conjunct says the
  loop preserves `pts_needed`.  Furthermore, since only `self.pts` is ever mutated, the body
  also preserves `is_complete`, and so does the whole loop.

  This corresponds to the Rust loop:
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

This follows from composing:
  1. `body_spec`: one step of the loop either terminates (iterator exhausted) or extends one
     slot of `self.pts` while preserving `pts_needed` and `is_complete`, advancing the cursor
     by one.
  2. `loop.spec_decr_nat`: lifts the body spec through the decreasing measure
     `iter'.«end».val − iter'.start.val`.

This establishes that the `add_chunk` chunk-absorption loop faithfully maintains the
decoder-state invariant `pts_needed`/`is_complete` while absorbing each byte pair of the input
chunk into the appropriate GF(2¹⁶) cartesian-point slot.

**Source**: spqr/src/encoding/polynomial.rs (lines 882:8-903:9)
-/
@[step]
theorem loop_spec
    (iter : core.ops.range.Range Std.Usize)
    (self : encoding.polynomial.PolyDecoder)
    (chunk : encoding.Chunk)
    (h_end_le_16 : iter.«end».val ≤ 16)
    (h_start_le : iter.start.val ≤ iter.«end».val)
    (sv : encoding.polynomial.PolyDecoder → Nat → sorted_vec.SortedVec Pt)
    (inner : encoding.polynomial.PolyDecoder → Nat → alloc.vec.Vec Pt)
    (h_sv : ∀ (s : encoding.polynomial.PolyDecoder) (i : Nat),
        sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
          Pt.Insts.CoreCmpOrd
          (s.pts.val[(chunk.index.val * 16 + i) % 16]!) = ok (sv s i))
    (h_inner : ∀ (s : encoding.polynomial.PolyDecoder) (i : Nat),
        sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
          Pt.Insts.CoreCmpOrd (sv s i) = ok (inner s i))
    (h_push_ok : ∀ (s : encoding.polynomial.PolyDecoder) (i : Nat),
        i < iter.«end».val →
        (s.pts.val[(chunk.index.val * 16 + i) % 16]!).val.length + 1 ≤ Usize.max) :
    encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop
        iter self chunk
      ⦃ (result : encoding.polynomial.PolyDecoder) =>
        result.pts_needed = self.pts_needed ∧
        result.is_complete = self.is_complete ⦄ := by
  unfold encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                         encoding.polynomial.PolyDecoder) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                     encoding.polynomial.PolyDecoder) =>
        let iter' := p.1
        let self' := p.2
        iter'.«end» = iter.«end» ∧
        iter.start.val ≤ iter'.start.val ∧
        iter'.start.val ≤ iter'.«end».val ∧
        self'.pts_needed = self.pts_needed ∧
        self'.is_complete = self.is_complete)
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', self'⟩ ⟨h_end', h_orig_le, h_start_le', h_pts_needed', h_complete'⟩
    simp only [] at h_end' h_orig_le h_start_le' h_pts_needed' h_complete' ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_end_le_16' : iter'.«end».val ≤ 16 := by omega
    have h_body :=
      body_spec chunk iter' self' h_end_le_16'
        (sv self' iter'.start.val) (inner self' iter'.start.val)
        (fun _ => h_sv self' iter'.start.val)
        (fun _ => h_inner self' iter'.start.val)
        (fun h_lt => h_push_ok self' iter'.start.val (by omega))
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done self'' =>
      simp only [] at h_cf ⊢
      obtain ⟨h_self_eq, _⟩ := h_cf
      subst h_self_eq
      exact ⟨h_pts_needed', h_complete'⟩
    | ControlFlow.cont (iter'', self'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, h_pts1, h_comp1⟩ := h_cf
      refine ⟨⟨by rw [h_end1]; exact h_end',
              by omega,
              by grind,
              by rw [h_pts1]; exact h_pts_needed',
              by rw [h_comp1]; exact h_complete'⟩,
              by grind⟩
  · -- Initial state satisfies the invariant
    exact ⟨rfl, le_refl _, h_start_le, rfl, rfl⟩

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop
