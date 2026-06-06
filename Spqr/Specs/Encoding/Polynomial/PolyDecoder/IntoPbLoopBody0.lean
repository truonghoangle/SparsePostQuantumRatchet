/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPbLoop1
import Spqr.Specs.Aeneas.SliceIteratorNext

/-!
# Spec theorem for `PolyDecoder::into_pb`: loop body 0

The extracted Lean function `encoding.polynomial.PolyDecoder.into_pb_loop0.body` performs one step
of the outer point-set-serialization loop inside `PolyDecoder::into_pb`.  Given a slice iterator
over `SortedSet<Pt>` values (each representing a sorted set of GF(2¹⁶) cartesian evaluation
points), and the current output vector of byte vectors `v`, the body calls `next` on the slice
iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the output vector `v` is returned unchanged.
  2. **Continue** (`some pts`): dereferences the `SortedSet<Pt>` `pts` twice (through
     `SortedSet → SortedVec → Vec<Pt>`) to obtain the underlying point vector `inner`,
     serializes all cartesian points in `inner` into a byte vector using the inner
     point-serialization loop (`into_pb_loop0_loop0`), and pushes the resulting byte vector
     onto `v`.

The loop invariant maintained across iterations is `v.val.length == processed`, i.e., each
`SortedSet<Pt>` contributes exactly one serialized byte vector to the output.  Each byte vector
contains the 4-byte big-endian encoding of every cartesian point's `x` and `y` coordinates:
  `serialized[4·k]   · 256 + serialized[4·k+1] = inner[k].x.value.val`
  `serialized[4·k+2] · 256 + serialized[4·k+3] = inner[k].y.value.val`

The body spec composes:
  1. `IteratorSliceIter.next` — to advance the slice iterator over `SortedSet<Pt>` elements.
  2. `SortedSet → SortedVec → Vec<Pt>` deref operations (opaque axioms) — to obtain the
     underlying point vector from the yielded `SortedSet<Pt>`.
  3. `into_pb_loop0_loop0` (inner loop spec from `IntoPbLoop1.lean`) — to serialize the points'
     GF(2¹⁶) cartesian coordinates into a byte vector.
  4. `Vec.push` — to append the serialized byte vector to the output.

Because both `SortedSet → SortedVec` and `SortedVec → Vec` deref operations are extracted as
opaque axioms (`sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref` and
`sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref`), we parameterise the spec by the
hypothetical deref results `sv` and `inner` and propagate the bounds through them.

**Source**: spqr/src/encoding/polynomial.rs (lines 800:8-809:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.into_pb_loop0

/-! ## Inhabited instance for `Pt` -/

/--
`Pt` wraps two `GF16` values `(x, y)`.  An `Inhabited` instance is required so that `getElem!`
(`[·]!`) on lists of `Pt` has a well-defined default value.  We use the zero point as the
canonical default.
-/
instance : Inhabited Pt :=
  ⟨{ x := ⟨0#u16⟩, y := ⟨0#u16⟩ }⟩

/-! ## Spec theorem for the into_pb outer loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0.body`**:

One step of the outer serialization loop inside `PolyDecoder::into_pb`.  Given a slice iterator
over `SortedSet<Pt>` values and the current output vector of serialized byte vectors `v`, the
body retrieves the next `SortedSet<Pt>` from the slice iterator and either terminates or extends
the output:

• The function always succeeds (no panic) provided the preconditions hold: both deref operations
  on the current `SortedSet<Pt>` element succeed (yielding `sv` and `inner`), the output vector
  has room for one more entry without exceeding `Usize.max`, and the underlying point vector
  can be serialized without overflow.

• In the **done** case (iterator exhausted):
    the output vector `v` is returned unchanged, and the iterator condition is negated:
    `¬ (iter.i < iter.slice.val.length)`.

• In the **cont** case (received `pts = iter.slice[iter.i]` from the slice iterator):
    - `iter.i < iter.slice.val.length` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.i = iter.i + 1`,
        `iter1.slice = iter.slice`.
    - The output vector is extended by exactly one entry — the serialized byte vector for the
      cartesian points in `inner` (the double-deref of `pts`):
        `v1.val = v.val ++ [serialized]`
      where `serialized` is the result of the inner serialization loop (`into_pb_loop0_loop0`)
      applied to `pts`, satisfying:
        `serialized.val.length = 4 * inner.val.length`
      and for every `k < inner.val.length`:
        `∃ b0 b1 b2 b3,
           serialized.val[4*k]?   = some b0 ∧ serialized.val[4*k+1]? = some b1 ∧
           serialized.val[4*k+2]? = some b2 ∧ serialized.val[4*k+3]? = some b3 ∧
           b0.val · 256 + b1.val = (inner.val[k]!).x.value.val ∧
           b2.val · 256 + b3.val = (inner.val[k]!).y.value.val`

    This corresponds to the Rust body:
    ```rust
    let mut v = Vec::<u8>::with_capacity(4 * pts.len());
    for i in 0..pts.len() {
        let pt = &pts[i];
        v.extend_from_slice(&pt.serialize()[..]);
    }
    out.pts.push(v);
    ```

**Source**: spqr/src/encoding/polynomial.rs (lines 800:8-809:9)
-/
@[step]
theorem body_spec
    (iter : core.slice.iter.Iter (sorted_vec.SortedSet Pt))
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (sv : sorted_vec.SortedVec Pt)
    (inner : alloc.vec.Vec Pt)
    (h_sv : ∀ (_ : iter.i < iter.slice.val.length),
      sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
        Pt.Insts.CoreCmpOrd (iter.slice.val[iter.i]) = ok sv)
    (h_inner :
      sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
        Pt.Insts.CoreCmpOrd sv = ok inner)
    (h_out_overflow : v.val.length + 1 ≤ Usize.max)
    (h_overflow : 4 * inner.val.length + 4 ≤ Usize.max) :
    body iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬(iter.i < iter.slice.val.length)
      | ControlFlow.cont (iter1, v1) =>
          iter.i < iter.slice.val.length ∧
          iter1.i = iter.i + 1 ∧
          iter1.slice = iter.slice ∧
          ∃ (serialized : alloc.vec.Vec Std.U8),
            v1.val = v.val ++ [serialized] ∧
            serialized.val.length = 4 * inner.val.length ∧
            ∀ (k : Nat), k < inner.val.length →
              ∃ (b0 b1 b2 b3 : Std.U8),
                serialized.val[4 * k]?     = some b0 ∧
                serialized.val[4 * k + 1]? = some b1 ∧
                serialized.val[4 * k + 2]? = some b2 ∧
                serialized.val[4 * k + 3]? = some b3 ∧
                b0.val * 256 + b1.val =
                  (inner.val[k]!).x.value.val ∧
                b2.val * 256 + b3.val =
                  (inner.val[k]!).y.value.val ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ :=
    core.slice.iter.IteratorSliceIter.next_post iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.i < iter.slice.val.length
  · obtain ⟨h_opt_eq, h_i1, h_slice1⟩ := h_some h_lt
    subst h_opt_eq
    have h_sv_inst := h_sv h_lt
    simp_all
    step*
    · simp_all [alloc.vec.Vec.with_capacity]
    · simp_all
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    subst h_opt_eq
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyDecoder.into_pb_loop0
