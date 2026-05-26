/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `core::slice::{[@T]}::iter`

The Rust method `core::slice::{[@T]}::iter` (in the standard library,
`core/src/slice/mod.rs`) creates an immutable iterator over the elements of a
slice `&[T]`.  It returns an `Iter<'_, T>` that yields shared references `&T`
to each element in order from front to back.

The Aeneas-extracted Lean function `core.slice.Slice.iter` constructs a
`core.slice.iter.Iter T` value by pairing the input slice with an initial
index of `0`:

```
@[rust_fun "core::slice::{[@T]}::iter"]
def core.slice.Slice.iter {T : Type} (s : Slice T)
    : Result (core.slice.iter.Iter T) :=
  ok ⟨ s, 0 ⟩
```

The function is total (never panics) for any valid `Slice T` input.  The
resulting iterator preserves the underlying slice data verbatim and begins
iteration at position zero.

This is a foundational building block used pervasively across the codebase,
including in `const_polys_to_polys` (in `src/encoding/polynomial.rs`,
lines 465:0-467:1) where it creates the slice iterator that is subsequently
mapped over with the `|x| x.to_poly()` closure and collected into a
`Vec<Poly>`.

**Postcondition**:
  - **Slice preservation**: `result.slice = s`
  - **Initial index**: `result.i = 0`

**Source**: core/src/slice/mod.rs (core library)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.slice.Slice

/--
**Spec theorem for `core.slice.Slice.iter`**:

• Takes a `Slice T` — a length-bounded list representing a Rust slice `&[T]`.
• Returns a `core.slice.iter.Iter T` whose `slice` field is the original
  input and whose `i` field (the iteration cursor) is `0`.

• The function always succeeds (no panic) for any `Slice T` input, since it
  merely constructs the pair `⟨s, 0⟩` without any fallible operations.

The postcondition captures both structural invariants:

  `result.slice = s`  — the iterator wraps the same slice data.
  `result.i = 0`      — iteration begins at the first element.

The proof unfolds `core.slice.Slice.iter` to expose the underlying `ok ⟨s, 0⟩`
constructor and discharges the resulting goal with `step*`.

**Source**: core/src/slice/mod.rs (core library)
-/
@[step]
theorem iter_spec {T : Type} (s : Slice T) :
    core.slice.Slice.iter s ⦃ (result : core.slice.iter.Iter T) =>
      result.slice = s ∧ result.i = 0 ⦄ := by
  unfold core.slice.Slice.iter
  step*

end Aeneas.Std.core.slice.Slice
