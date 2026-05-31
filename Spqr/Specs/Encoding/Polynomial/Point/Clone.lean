/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::polynomial::{impl Clone for Point}::clone`

A `Point` wraps a single `Vec<GF16>` representing an evaluation-data vector.  The derived `Clone`
implementation clones that inner vector element-wise and rewraps it in a fresh `Point`.

Because `GF16` is `Copy` — and its derived `Clone::clone` returns the argument unchanged — the
clone is observationally the identity:
  `clone(self) = ok self`

**Source**: spqr/src/encoding/polynomial.rs (lines 512:9-512:14, `#[derive(Clone)]`)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.Point

/--
**Spec theorem for `encoding.polynomial.Point.Insts.CoreCloneClone.clone`**:

• The function always succeeds (no panic / no error) for any `Point` input, since the underlying
  `alloc.vec.CloneVec.clone` reduces to `Slice.clone` and each element-wise clone
  `GF16.Insts.CoreCloneClone.clone x = ok x` is total.
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `Point`.  This follows
  because `GF16` is `Copy` and its derived `Clone::clone` returns its argument unchanged, so the
  list-level clone produces the same underlying value list and the wrapping
  `{ value := v }` reconstructs `self` by η-expansion of the single-field structure.

**Source**: spqr/src/encoding/polynomial.rs (lines 512:9-512:14, `#[derive(Clone)]`)
-/
@[step]
private lemma clone_GF16_id (x : encoding.gf.GF16) :
    encoding.gf.GF16.Insts.CoreCloneClone.clone x ⦃ (r : encoding.gf.GF16) =>
      r = x ⦄ := by
  simp [encoding.gf.GF16.Insts.CoreCloneClone.clone]

@[step]
private lemma clone_vec_GF16_spec (v : alloc.vec.Vec encoding.gf.GF16) :
    alloc.vec.CloneVec.clone encoding.gf.GF16.Insts.CoreCloneClone v
      ⦃ (r : alloc.vec.Vec encoding.gf.GF16) => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  apply WP.spec_mono
    (Slice.clone_spec (fun x _ => by
      simp [encoding.gf.GF16.Insts.CoreCloneClone.clone]))
  intro v' h
  exact h.symm

@[step]
theorem clone_spec (self : encoding.polynomial.Point) :
    Insts.CoreCloneClone.clone self ⦃ (result : encoding.polynomial.Point) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  step*
  rw [v_post]

end spqr.encoding.polynomial.Point
