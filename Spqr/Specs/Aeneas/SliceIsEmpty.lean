/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `core::slice::{[@T]}::is_empty`

In Rust's standard library, `slice.is_empty()` returns `true` when the slice has length zero,
and `false` otherwise.

The Aeneas-extracted Lean function `core.slice.Slice.is_empty` mirrors this behavior.  This is
used in `Poly::lagrange_interpolate` to check whether the input point slice is empty before
proceeding with the interpolation algorithm.

**Source**: core/src/slice/mod.rs (Slice::is_empty)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.Specs.SliceIsEmpty

/--
**Spec theorem for `core.slice.Slice.is_empty`**:

The function always succeeds and returns a `Bool` equal to `(s.val.length = 0)`.

**Source**: core/src/slice/mod.rs (Slice::is_empty)
-/
@[step]
theorem slice_is_empty_spec {T : Type} (s : Slice T) :
    core.slice.Slice.is_empty s ⦃ (b : Bool) =>
      b = (s.val.length = 0) ⦄ := by
  unfold core.slice.Slice.is_empty
  simp only [WP.spec_ok]
  rcases h : s.val.length with _ | n
  · simp [h]
  · simp [h]

end Aeneas.Std.Specs.SliceIsEmpty
