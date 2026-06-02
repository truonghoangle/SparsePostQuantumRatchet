/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorems for `alloc::vec::Vec::extend_from_slice`

In Rust, `Vec::extend_from_slice(&self, other: &[T])` appends the contents of a slice to a vector
by cloning each element.  When the element type's `Clone` implementation is the identity (as for
`u8` and `GF16`), the resulting vector is exactly `v ++ s`.

The Aeneas-extracted Lean function `alloc.vec.Vec.extend_from_slice` takes a `Clone` instance,
the vector, and the slice, and returns the extended vector.

This specification is used in serialization loop bodies throughout
`Spqr.Specs.Encoding.Polynomial` (e.g. `Poly::serialize`, `PolyEncoder::into_pb`).

**Source**: alloc/src/vec/mod.rs (Vec::extend_from_slice)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.alloc.vec.Vec

/--
**Spec theorem for `alloc.vec.Vec.extend_from_slice` specialised to `U8`**:

The `core.clone.Clone` instance for `U8` (`core.clone.CloneU8`) has `clone x = ok x` for every `x`,
hence the elementwise `Slice.clone` on `s` returns `ok s` and the resulting vector is exactly
`v.val ++ s.val`.  The precondition `v.val.length + s.val.length ≤ Usize.max` discharges the
overflow guard in the body of `extend_from_slice`.

**Source**: alloc/src/vec/mod.rs (Vec::extend_from_slice)
-/
@[step]
theorem extend_from_slice_U8_spec
    (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s
      ⦃ (r : alloc.vec.Vec U8) => r.val = v.val ++ s.val ⦄ := by
  have h_clone_x :
      ∀ x ∈ s.val, core.clone.CloneU8.clone x = ok x := by
    intros _ _; rfl
  have h_slclone :
      Slice.clone core.clone.CloneU8.clone s = ok s := by
    obtain ⟨s', h_eq, hs⟩ := WP.spec_imp_exists (Slice.clone_spec h_clone_x)
    rw [h_eq, ← hs]
  unfold alloc.vec.Vec.extend_from_slice
  have hlen : v.length + s.length ≤ Usize.max := h
  rw [dif_pos hlen]
  grind

/--
**Spec theorem for `alloc.vec.Vec.extend_from_slice` specialised to `GF16`**:

The `core.clone.Clone` instance for `GF16` has `clone x = ok x` for every `x`,
hence the elementwise `Slice.clone` on `s` returns `ok s` and the resulting vector is exactly
`v.val ++ s.val`.  The precondition `v.val.length + s.val.length ≤ Usize.max` discharges the
overflow guard in the body of `extend_from_slice`.

**Source**: alloc/src/vec/mod.rs (Vec::extend_from_slice)
-/
@[step]
theorem extend_from_slice_GF16_spec
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (s : Slice spqr.encoding.gf.GF16)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice
        spqr.encoding.gf.GF16.Insts.CoreCloneClone v s
      ⦃ (r : alloc.vec.Vec spqr.encoding.gf.GF16) =>
        r.val = v.val ++ s.val ⦄ := by
  have h_clone_x :
      ∀ x ∈ s.val,
        spqr.encoding.gf.GF16.Insts.CoreCloneClone.clone x = ok x := by
    intros _ _
    simp [spqr.encoding.gf.GF16.Insts.CoreCloneClone.clone]
  have h_slclone :
      Slice.clone spqr.encoding.gf.GF16.Insts.CoreCloneClone.clone s = ok s := by
    obtain ⟨s', h_eq, hs⟩ := WP.spec_imp_exists (Slice.clone_spec h_clone_x)
    rw [h_eq, ← hs]
  unfold alloc.vec.Vec.extend_from_slice
  have hlen : v.length + s.length ≤ Usize.max := h
  rw [dif_pos hlen]
  grind

end Aeneas.Std.alloc.vec.Vec
