/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorems for `{Clone for GF16}::clone` and `Vec<GF16>::clone`

In the spqr crate, `GF16` is `Copy`, so its derived `Clone::clone` returns the argument unchanged.
This makes `Vec<GF16>::clone` (via `alloc::vec::CloneVec::clone`) also the identity on the
underlying coefficient list.

These specifications are used in:
  - `Point::clone` (`Spqr.Specs.Encoding.Polynomial.Point.Clone`)
  - `Poly::clone` (`Spqr.Specs.Encoding.Polynomial.Poly.Clone`)

**Source**: spqr/src/encoding/gf.rs (derived Clone for GF16)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.gf.GF16.Insts.CoreCloneClone

/--
**Spec theorem for `encoding.gf.GF16.Insts.CoreCloneClone.clone`**:

`GF16::clone` always succeeds and returns its argument unchanged, since `GF16` is `Copy`.

**Source**: spqr/src/encoding/gf.rs (derived Clone for GF16)
-/
@[step]
theorem clone_id (x : spqr.encoding.gf.GF16) :
    spqr.encoding.gf.GF16.Insts.CoreCloneClone.clone x ⦃ (r : spqr.encoding.gf.GF16) =>
      r = x ⦄ := by
  simp [spqr.encoding.gf.GF16.Insts.CoreCloneClone.clone]

end spqr.encoding.gf.GF16.Insts.CoreCloneClone

namespace Aeneas.Std.alloc.vec.CloneVec

/--
**Spec theorem for `alloc.vec.CloneVec.clone` specialised to `GF16`**:

Cloning a `Vec<GF16>` always succeeds and returns the vector unchanged, because the elementwise
`GF16::clone` is the identity.

**Source**: alloc/src/vec/mod.rs (Vec::clone), spqr/src/encoding/gf.rs
-/
@[step]
theorem clone_GF16_spec (v : alloc.vec.Vec spqr.encoding.gf.GF16) :
    alloc.vec.CloneVec.clone spqr.encoding.gf.GF16.Insts.CoreCloneClone v
      ⦃ (r : alloc.vec.Vec spqr.encoding.gf.GF16) => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  apply WP.spec_mono
    (Slice.clone_spec (fun x _ => by
      simp [spqr.encoding.gf.GF16.Insts.CoreCloneClone.clone]))
  intro v' h
  exact h.symm

end Aeneas.Std.alloc.vec.CloneVec
