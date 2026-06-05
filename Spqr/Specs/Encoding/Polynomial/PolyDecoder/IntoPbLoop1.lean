/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.General
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPbLoopBody1

/-!
# Spec theorem for `PolyDecoder::into_pb`: loop 1

The extracted Lean function `encoding.polynomial.PolyDecoder.into_pb_loop0_loop0` is the inner
point-serialization loop inside `PolyDecoder::into_pb`.  Given a `SortedSet<Pt>` `pts` of
GF(2¹⁶) cartesian evaluation points (whose underlying `Vec<Pt>` is obtained by dereferencing
twice through `SortedSet → SortedVec → Vec<Pt>` to yield `inner`), a `Range<usize>` iterator over
`0..inner.len()`, and the current output byte vector `v`, the loop repeatedly invokes
`encoding.polynomial.PolyDecoder.into_pb_loop0_loop0.body`, which at each step:

  1. Calls `next` on the `Range<usize>` iterator to obtain the current index `i`.
  2. Derefs `pts` twice to obtain the underlying point vector `inner` and retrieves
     `pt = inner[i]`.
  3. Converts `pt : Pt` to its 4-byte big-endian representation via `Pt::serialize` — which lays
     out `pt.x.value : u16` and `pt.y.value : u16` each as two big-endian bytes.
  4. Appends those four bytes to `v` via `Vec::extend_from_slice`.

**Loop invariant**: after processing iterations up to `iter'`, the output byte vector satisfies:

  * `out'.val.length = 4 * iter'.start.val` — each cartesian point contributes exactly 4 bytes
    (2 for `x`, 2 for `y`).
  * `iter'.«end» = iter.«end»` — the iterator end is unchanged across iterations.
  * For every `j ∈ [0, iter'.start.val)`, the big-endian encoding holds:
      `∃ b0 b1 b2 b3,
         out'.val[4*j]?   = some b0 ∧ out'.val[4*j+1]? = some b1 ∧
         out'.val[4*j+2]? = some b2 ∧ out'.val[4*j+3]? = some b3 ∧
         b0.val · 256 + b1.val = (inner.val[j]!).x.value.val ∧
         b2.val · 256 + b3.val = (inner.val[j]!).y.value.val`

At loop termination (`iter'.start.val ≥ iter'.«end».val`), the output vector contains the
complete serialization of all cartesian points in `inner.val[0..iter.«end».val]`.

The body spec (`body_spec` from `IntoPbLoopBody1.lean`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`iter'.«end».val − iter'.start.val`) to give the full loop postcondition.

Because both `SortedSet → SortedVec` and `SortedVec → Vec` deref operations are extracted as
opaque axioms (`sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref` and
`sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref`), we parameterise the spec by the
hypothetical deref results `sv` and `inner` and propagate the bound on `iter.«end»` through them.

In GF(2¹⁶) (characteristic 2), each field element is stored as a `u16`, and the big-endian
encoding satisfies `hi · 256 + lo = value` where `hi` and `lo` are the high and low bytes
respectively; a `Pt` packs two such elements `(x, y)`.

**Source**: spqr/src/encoding/polynomial.rs (lines 803:12-807:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.into_pb_loop0_loop0

/-! ## Spec theorem for the into_pb inner serialization loop -/

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0_loop0`**:

The full inner point-serialization loop inside `PolyDecoder::into_pb`.  Given a `SortedSet<Pt>`
`pts` (whose double-deref yields the `Vec<Pt>` `inner` via the witnesses `sv` and `inner`),
a range iterator `iter` over indices into `inner`, and the current output byte vector `v`,
the loop drives the body to completion and returns the serialized byte vector.

• The function always succeeds (no panic) provided the preconditions hold: both deref operations
  succeed yielding `sv` and `inner`, the iterator range end does not exceed the point-vector
  length, the output vector length equals `4 * iter.start.val` (each previously processed point
  contributed exactly 4 bytes), and the total serialization does not overflow `Usize.max`.

• **Loop postcondition**:
  - `result.val.length = 4 * iter.«end».val` — the output contains exactly four bytes per
    cartesian point in the range.
  - For every `j < iter.«end».val`, the big-endian encoding invariant holds:
      `∃ b0 b1 b2 b3,
         result.val[4*j]?   = some b0 ∧ result.val[4*j+1]? = some b1 ∧
         result.val[4*j+2]? = some b2 ∧ result.val[4*j+3]? = some b3 ∧
         b0.val · 256 + b1.val = (inner.val[j]!).x.value.val ∧
         b2.val · 256 + b3.val = (inner.val[j]!).y.value.val`

    This corresponds to the Rust loop:
    ```rust
    for i in 0..pts.len() {
        let pt = pts[i];
        v.extend_from_slice(&pt.serialize()[..]);
    }
    ```

Because `SortedSet → SortedVec` and `SortedVec → Vec` derefs are opaque axioms in the extraction,
the caller supplies the witnesses `sv`, `inner` together with the deref equations `h_sv` and
`h_inner`.  The proof lifts the body spec through `loop.spec_decr_nat` with measure
`iter'.«end».val − iter'.start.val`, maintaining the byte-encoding invariant.

**Source**: spqr/src/encoding/polynomial.rs (lines 803:12-807:13)
-/
@[step]
theorem loop_spec
    (pts : sorted_vec.SortedSet Pt)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec Std.U8)
    (sv : sorted_vec.SortedVec Pt)
    (inner : alloc.vec.Vec Pt)
    (h_sv :
      sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
        Pt.Insts.CoreCmpOrd pts = ok sv)
    (h_inner :
      sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
        Pt.Insts.CoreCmpOrd sv = ok inner)
    (h_end_le : iter.«end».val ≤ inner.val.length)
    (h_out_len : v.val.length = 4 * iter.start.val)
    (h_start_le : iter.start.val ≤ iter.«end».val)
    (h_overflow : 4 * inner.val.length + 4 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start.val →
        ∃ (b0 b1 b2 b3 : Std.U8),
          v.val[4 * j]?     = some b0 ∧
          v.val[4 * j + 1]? = some b1 ∧
          v.val[4 * j + 2]? = some b2 ∧
          v.val[4 * j + 3]? = some b3 ∧
          b0.val * 256 + b1.val = (inner.val[j]!).x.value.val ∧
          b2.val * 256 + b3.val = (inner.val[j]!).y.value.val) :
    into_pb_loop0_loop0 iter pts v ⦃ (result : alloc.vec.Vec Std.U8) =>
      result.val.length = 4 * iter.«end».val ∧
      ∀ (j : Nat), j < iter.«end».val →
        ∃ (b0 b1 b2 b3 : Std.U8),
          result.val[4 * j]?     = some b0 ∧
          result.val[4 * j + 1]? = some b1 ∧
          result.val[4 * j + 2]? = some b2 ∧
          result.val[4 * j + 3]? = some b3 ∧
          b0.val * 256 + b1.val = (inner.val[j]!).x.value.val ∧
          b2.val * 256 + b3.val = (inner.val[j]!).y.value.val ⦄ := by
  unfold into_pb_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize × alloc.vec.Vec Std.U8) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize × alloc.vec.Vec Std.U8) =>
        let iter' := p.1
        let out' := p.2
        iter'.«end» = iter.«end» ∧
        iter'.start.val ≤ iter'.«end».val ∧
        out'.val.length = 4 * iter'.start.val ∧
        (∀ (j : Nat), j < iter'.start.val →
          ∃ (b0 b1 b2 b3 : Std.U8),
            out'.val[4 * j]?     = some b0 ∧
            out'.val[4 * j + 1]? = some b1 ∧
            out'.val[4 * j + 2]? = some b2 ∧
            out'.val[4 * j + 3]? = some b3 ∧
            b0.val * 256 + b1.val = (inner.val[j]!).x.value.val ∧
            b2.val * 256 + b3.val = (inner.val[j]!).y.value.val))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', out'⟩ ⟨h_end', h_start_le', h_out_len', h_pre'⟩
    simp only [] at h_end' h_start_le' h_out_len' h_pre' ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_body :=
      body_spec pts iter' out' sv inner h_sv h_inner (by omega) (by omega)
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done out'' =>
      simp only [] at h_cf ⊢
      obtain ⟨h_out_eq, h_not_lt⟩ := h_cf
      subst h_out_eq
      exact ⟨by omega, fun j hj => h_pre' j (by omega)⟩
    | ControlFlow.cont (iter'', out'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, b0, b1, b2, b3, h_out_eq, h_encx, h_ency⟩ := h_cf
      have h_end1_val : iter''.«end».val = iter'.«end».val := by rw [h_end1]
      constructor
      · -- Invariant is preserved
        refine ⟨by rw [h_end1]; exact h_end',
               by omega,
               by rw [h_out_eq]; simp [h_out_len']; omega,
               fun j hj => ?_⟩
        by_cases hj_lt : j < iter'.start.val
        · -- Previously serialized bytes: index falls in the prefix out'.val
          obtain ⟨b0', b1', b2', b3', hb0', hb1', hb2', hb3', hencx', hency'⟩ :=
            h_pre' j hj_lt
          refine ⟨b0', b1', b2', b3', ?_, ?_, ?_, ?_, hencx', hency'⟩
          · rw [h_out_eq, getElem?_append_of_lt _ _ (by omega)]; exact hb0'
          · rw [h_out_eq, getElem?_append_of_lt _ _ (by omega)]; exact hb1'
          · rw [h_out_eq, getElem?_append_of_lt _ _ (by omega)]; exact hb2'
          · rw [h_out_eq, getElem?_append_of_lt _ _ (by omega)]; exact hb3'
        · -- Newly appended bytes: j = iter'.start.val
          have hj_eq : j = iter'.start.val := by omega
          subst hj_eq
          refine ⟨b0, b1, b2, b3, ?_, ?_, ?_, ?_, h_encx, h_ency⟩
          · rw [h_out_eq, show 4 * iter'.start.val = out'.val.length from by omega,
                List.getElem?_append_right (le_refl _)]
            simp
          · rw [h_out_eq, show 4 * iter'.start.val + 1 = out'.val.length + 1 from by omega,
                List.getElem?_append_right (by omega)]
            simp
          · rw [h_out_eq, show 4 * iter'.start.val + 2 = out'.val.length + 2 from by omega,
                List.getElem?_append_right (by omega)]
            simp
          · rw [h_out_eq, show 4 * iter'.start.val + 3 = out'.val.length + 3 from by omega,
                List.getElem?_append_right (by omega)]
            simp
      · -- Measure decreases
        omega
  · -- Initial state satisfies the invariant
    exact ⟨rfl, h_start_le, h_out_len, h_pre⟩

end spqr.encoding.polynomial.PolyDecoder.into_pb_loop0_loop0
