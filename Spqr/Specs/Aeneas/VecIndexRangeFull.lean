/-
<<<<<<< HEAD
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
=======
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

<<<<<<< HEAD
/-!
# Spec theorem for `alloc.vec.Vec.index` with `RangeFull`

Indexing a `Vec<T>` with `..` (RangeFull) returns the entire vector as a slice — an identity
operation since `Vec T` and `Slice T` are definitionally equal in Aeneas.

**Source**: alloc/src/vec/mod.rs (Index impl for Vec)
-/

open Aeneas Aeneas.Std Result spqr

/--
**Spec theorem for `alloc.vec.Vec.index` with `RangeFull`**:

Always succeeds and returns a slice whose element list equals the vector's.
-/
=======
/-! # Spec theorem for `alloc.vec.Vec.index` with `RangeFull`

`Vec.index` with `..` returns the full vector as a slice (identity in Aeneas). -/

open Aeneas Aeneas.Std Result spqr

/-- **Spec theorem for `alloc.vec.Vec.index` with `RangeFull`**:
always succeeds, returning the vector's elements. -/
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
@[step]
theorem alloc.vec.Vec.index_RangeFull_spec {T : Type} (v : alloc.vec.Vec T) :
    alloc.vec.Vec.index
      (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice T) v ()
<<<<<<< HEAD
    ⦃ s => s.val = v.val ⦄ := by
=======
    ⦃ (s : Slice T) => s.val = v.val ⦄ := by
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
  unfold alloc.vec.Vec.index
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index
  simp [WP.spec_ok]
