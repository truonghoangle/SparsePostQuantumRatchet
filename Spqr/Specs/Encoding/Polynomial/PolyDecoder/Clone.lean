/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::polynomial::{impl Clone for PolyDecoder}::clone`

A `PolyDecoder` wraps three fields:
  • `pts_needed : usize` — the number of evaluation points still needed for decoding.
  • `pts : [SortedSet<Pt>; 16]` — a fixed-size array of 16 sorted sets of evaluation points,
     one per polynomial.
  • `is_complete : bool` — whether the decoder has collected enough points to decode.

The derived `Clone` implementation field-wise clones each component:
  1. `CloneUsize.clone` for `pts_needed` (identity on `usize`).
  2. `core.array.CloneArray.clone` with the `SortedSet<Pt>` clone instance for `pts`.
  3. `CloneBool.clone` for `is_complete` (identity on `bool`).

Because `Pt` is `Copy` — and its derived `Clone::clone` returns the argument unchanged — the
element-wise clone of each `SortedSet<Pt>` is the identity, and therefore the array-level and
struct-level clones are both observationally the identity:
  `clone(self) = ok self`

**Source**: spqr/src/encoding/polynomial.rs (lines 741:9-741:14, `#[derive(Clone)]`)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.PolyDecoder

/-- `SortedSet<Pt>` clone is the identity.

Since `Pt` is `Copy` (its `Clone::clone` returns `ok self`), the `SortedSet<Pt>` clone — which is
an external axiom in the Aeneas extraction — is observationally the identity.  We postulate this
because `sorted_vec.SortedSet.Insts.CoreCloneClone.clone` is opaque (extracted as an external
function). -/
axiom clone_sorted_set_pt_id
    (x : sorted_vec.SortedSet encoding.polynomial.Pt) :
    sorted_vec.SortedSet.Insts.CoreCloneClone.clone
      encoding.polynomial.Pt.Insts.CoreCloneClone
      encoding.polynomial.Pt.Insts.CoreCmpOrd x = ok x

/-- The array-level `[SortedSet<Pt>; 16]` clone is the identity.

This lifts `clone_sorted_set_pt_id` through `core.array.CloneArray.clone_spec` so that `step*` can
process the array-clone step in the main `PolyDecoder.clone` proof. -/
@[step]
private lemma clone_array_sorted_set_pt_spec
    (pts : Array (sorted_vec.SortedSet encoding.polynomial.Pt) 16#usize) :
    core.array.CloneArray.clone
      (sorted_vec.SortedSet.Insts.CoreCloneClone
        encoding.polynomial.Pt.Insts.CoreCloneClone
        encoding.polynomial.Pt.Insts.CoreCmpOrd) pts
    ⦃ (pts' : Array (sorted_vec.SortedSet encoding.polynomial.Pt) 16#usize) =>
      pts' = pts ⦄ := by
  apply WP.spec_mono
    (core.array.CloneArray.clone_spec _ pts (fun x _ => clone_sorted_set_pt_id x))
  intro pts' h
  exact h.symm

/--
**Spec theorem for `encoding.polynomial.PolyDecoder.Insts.CoreCloneClone.clone`**:

• The function always succeeds (no panic / no error) for any `PolyDecoder` input, since
  `CloneUsize.clone`, `CloneBool.clone`, and the per-element `SortedSet<Pt>` clone are all total.
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `PolyDecoder`.  This
  follows because every field-level clone returns its argument unchanged:
    - `usize` and `bool` are primitive `Copy` types whose `Clone::clone` is the identity.
    - Each `SortedSet<Pt>` element is cloned via the identity (`clone_sorted_set_pt_id`), so
      `core.array.CloneArray.clone` over the 16-element array is the identity
      (`clone_array_sorted_set_pt_spec`).
  The struct reconstruction `{ pts_needed := i, pts := a, is_complete := b }` then recovers
  `self` by η-expansion of the three-field structure.

**Source**: spqr/src/encoding/polynomial.rs (lines 741:9-741:14, `#[derive(Clone)]`)
-/
@[step]
theorem clone_spec (self : encoding.polynomial.PolyDecoder) :
    Insts.CoreCloneClone.clone self ⦃ (result : encoding.polynomial.PolyDecoder) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  simp only [core.clone.impls.CloneUsize.clone, core.clone.impls.CloneBool.clone]
  simp only [lift]
  apply WP.spec_bind (Pₘ := fun a => a = self.pts)
  · exact clone_array_sorted_set_pt_spec self.pts
  · intro a ha
    simp  [WP.spec_ok]
    subst ha
    simp

end spqr.encoding.polynomial.PolyDecoder
