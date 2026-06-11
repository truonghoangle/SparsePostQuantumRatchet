/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorems for `alloc::vec::{core::ops::deref::Deref<Vec<T>, [T]>}::deref`

The Rust trait implementation `Deref<Vec<T>, [T]>` for `Vec<T>` provides the `deref` method, which
converts a `&Vec<T>` into a `&[T]` (a slice reference).  After Aeneas extraction, this becomes the
pure function

```
alloc.vec.Vec.deref {T : Type} (v : alloc.vec.Vec T) : Slice T :=
  ⟨ v.val, v.property ⟩
```

Since both `Vec T` and `Slice T` are defined as `{ l : List T // l.length ≤ Usize.max }`, the
operation is a definitional identity on the underlying data: it merely repackages the same list and
its length-bound proof into the `Slice` wrapper.

In the polynomial pipeline, `Vec.deref` is used extensively to pass `Vec Poly`, `Vec GF16`, or
`Vec U8` arguments to functions expecting `Slice` inputs — for example, `Poly.lagrange_sum`,
`parallel_mult`, and `core.slice.Slice.iter`.  The theorems below ensure that all data is preserved
verbatim through the conversion.

**Key properties**:
  - **Totality**: the function is pure (marked `-canFail -lift`); it never panics or fails.
  - **Data identity**: `(Vec.deref v).val = v.val`
  - **Length preservation**: `(Vec.deref v).val.length = v.val.length`

**Source**: alloc/vec (Aeneas built-in, `Aeneas.Std.Vec`)
-/

open Aeneas Aeneas.Std Result

namespace alloc.vec.Vec

/--
**Spec theorem for `alloc.vec.Vec.deref` — data identity**:

• Takes a `Vec T` value `v`, wrapping a `List T` whose length is bounded by `Usize.max`.
• Returns a `Slice T` whose underlying list is *identical* to `v.val`.
• This holds definitionally: `Vec.deref` constructs `⟨v.val, v.property⟩`, so `.val` on the
  result is exactly `.val` on the input.

This is the fundamental building block for all downstream reasoning about `Vec.deref` calls in
the polynomial pipeline — once the data identity is established, properties such as length
preservation and elementwise equality follow immediately.
-/
@[simp]
theorem deref_val {T : Type} (v : alloc.vec.Vec T) :
    (alloc.vec.Vec.deref v).val = v.val := by
  rfl

/--
**Spec theorem for `alloc.vec.Vec.deref` — length preservation**:

The resulting slice has exactly the same length as the input vector:
  `(Vec.deref v).val.length = v.val.length`

This is an immediate consequence of `deref_val` but is stated separately for convenience in proofs
where length information is needed without unfolding the full data identity.
-/
@[simp]
theorem deref_length {T : Type} (v : alloc.vec.Vec T) :
    (alloc.vec.Vec.deref v).val.length = v.val.length := by
  rfl

end alloc.vec.Vec
