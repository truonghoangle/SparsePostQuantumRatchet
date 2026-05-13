/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Poly

/-!
# Spec theorem for `spqr::encoding::polynomial::{impl Clone for Poly}::clone`

In particular, the mathematical polynomial interpretation `Poly.toGF216Poly : Poly → GF216Poly`
into the Mathlib polynomial ring `GF216[X] = (GaloisField 2 16)[X]` is preserved exactly:
  `result.toGF216Poly = self.toGF216Poly`.

**Source**: spqr/src/encoding/polynomial.rs (lines 77:9-77:14, `#[derive(Clone, PartialEq)]`)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.Poly

/--
**Spec theorem for `encoding.polynomial.Poly.Insts.CoreCloneClone.clone`**:

• The function always succeeds (no panic / no error) for any `Poly` input, since the underlying
  `alloc.vec.CloneVec.clone` reduces to `Slice.clone` and each elementwise clone
  `GF16.Insts.CoreCloneClone.clone x = ok x` is total.
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `Poly`.  This follows
  because `GF16` is `Copy` and its derived `Clone::clone` returns its argument unchanged, so the
  list-level clone produces the same underlying coefficient list and the wrapping
  `{ coefficients := v }` reconstructs `self` by η-expansion of the single-field structure.

**Source**: spqr/src/encoding/polynomial.rs (lines 77:9-77:14, `#[derive(Clone, PartialEq)]`)
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
theorem clone_spec (self : encoding.polynomial.Poly) :
    Insts.CoreCloneClone.clone self ⦃ (result : encoding.polynomial.Poly) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  step*
  rw [v_post]

/--
**Corollary**: cloning a `Poly` preserves its mathematical polynomial interpretation in
`GF216[X] = (GaloisField 2 16)[X]`.

Since the Rust-level clone is observationally the identity (by `clone_spec`), the canonical bridge
`Poly.toGF216Poly : Poly → GF216Poly` is trivially preserved.  This is the polynomial-ring
counterpart of `clone_spec` and is the form most useful when reasoning about callers that interpret
the cloned `Poly` algebraically (e.g. as the `template` in `lagrange_interpolate`, whose Lagrange
algebraic identity is stated in terms of `template.toGF216Poly`).
-/
theorem clone_toGF216Poly_spec (self : encoding.polynomial.Poly) :
    Insts.CoreCloneClone.clone self ⦃ (result : encoding.polynomial.Poly) =>
      result.toGF216Poly = self.toGF216Poly ⦄ := by
  apply WP.spec_mono (clone_spec self)
  intro result h
  rw [h]

end spqr.encoding.polynomial.Poly
