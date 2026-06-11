/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `<[T; N] as TryFrom<&[T]>>::try_from`

In Rust's standard library, `<[T; N] as TryFrom<&[T]>>::try_from(slice)` attempts to convert a
slice `&[T]` into a fixed-size array `[T; N]`.  It succeeds with `Ok(array)` when
`slice.len() == N`, and fails otherwise.

When the element type has a `Copy` (clone) that is the identity (as for all scalar types), the
resulting array contains exactly the same elements as the input slice.

The Aeneas-extracted Lean function `core.array.TryFromArrayCopySlice.try_from` mirrors this
behavior.  This is used in deserialization code (e.g. `Pt::deserialize`) to handle the
`.try_into().unwrap()` idiom for converting sub-slices to fixed-size arrays.

**Source**: core/src/array/mod.rs (TryFrom impl for [T; N])
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.array.TryFromArrayCopySlice

/--
**Spec theorem for `core.array.TryFromArrayCopySlice.try_from`**:

When the input slice `s` has length exactly `N` and the type's `Copy` (clone) is the identity
(as for all scalar types), `try_from` succeeds with `Ok a` where `a.val = s.val`.

**Source**: core/src/array/mod.rs (TryFrom impl for [T; N])
-/
@[step]
theorem try_from_spec {T : Type} (N : Usize) (copyInst : core.marker.Copy T)
    (s : Slice T)
    (h_len : s.length = N) :
    core.array.TryFromArrayCopySlice.try_from N copyInst s ⦃ result =>
      ∃ (a : Array T N), result = .Ok a ∧ a.val = s.val ⦄ := by
  unfold core.array.TryFromArrayCopySlice.try_from
  simp only [dif_pos h_len, WP.spec_ok]
  exact ⟨⟨s.val, by scalar_tac⟩, rfl, rfl⟩

end Aeneas.Std.core.array.TryFromArrayCopySlice
