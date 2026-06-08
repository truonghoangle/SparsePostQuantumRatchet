/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `core::slice::Slice::clone_from_slice`

In Rust's standard library, `slice.clone_from_slice(src)` copies the contents of `src` into `slice`,
overwriting the existing elements.  When the element type's `Clone` implementation is the identity
(as for `u8`), the result is a slice whose contents equal those of `src`.

The Aeneas-extracted Lean function `core.slice.Slice.clone_from_slice` mirrors this behavior.

This is used in `Pt::serialize` where the big-endian byte representation of a `u16` is copied into
a sub-slice of the output array.

**Source**: core/src/slice/mod.rs (Slice::clone_from_slice)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.slice.Slice

/--
**Spec theorem for `core.slice.Slice.clone_from_slice` specialised to `U8`**:

`clone_from_slice` for `u8` copies the source slice into the destination, returning a slice whose
contents and length equal those of the source.

**Source**: core/src/slice/mod.rs (Slice::clone_from_slice)
-/
@[step]
theorem clone_from_slice_U8_spec
    (dst src : Slice Std.U8) :
    core.slice.Slice.clone_from_slice core.clone.CloneU8 dst src
    ⦃ result =>
      result.val = src.val ∧ result.length = src.length ⦄ := by
  unfold core.slice.Slice.clone_from_slice
  apply WP.spec_mono (Slice.clone_spec (fun x _ => by simp))
  intro s' h
  subst h
  exact ⟨rfl, rfl⟩

end Aeneas.Std.core.slice.Slice
