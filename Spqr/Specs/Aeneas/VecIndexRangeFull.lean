/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

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
@[step]
theorem alloc.vec.Vec.index_RangeFull_spec {T : Type} (v : alloc.vec.Vec T) :
    alloc.vec.Vec.index
      (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice T) v ()
    ⦃ s => s.val = v.val ⦄ := by
  unfold alloc.vec.Vec.index
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index
  simp [WP.spec_ok]
