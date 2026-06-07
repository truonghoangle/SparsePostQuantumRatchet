/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.General
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPbLoopBody0

/-!
# Spec theorem for `PolyDecoder::into_pb`: loop 0

The extracted Lean function `encoding.polynomial.PolyDecoder.into_pb_loop0` is the outer
point-set-serialization loop inside `PolyDecoder::into_pb`.  Given a slice iterator over
`SortedSet<Pt>` values (each representing a sorted set of GF(2¹⁶) cartesian evaluation points)
and the current output vector of byte vectors `v`, the loop repeatedly invokes
`encoding.polynomial.PolyDecoder.into_pb_loop0.body`, which at each step:

  1. Calls `next` on the slice iterator to obtain the current `SortedSet<Pt>` `pts`.
  2. Derefs `pts` twice (through `SortedSet → SortedVec → Vec<Pt>`) to obtain the underlying
     point vector `inner`.
  3. Serializes all cartesian points in `inner` into a byte vector using the inner
     point-serialization loop (`into_pb_loop0_loop0`), each point contributing 4 bytes — two
     big-endian bytes for the GF(2¹⁶) coordinate `x` and two for `y`.
  4. Pushes the resulting byte vector onto the output vector `v`.

**Loop invariant**: after processing iterations up to `iter'`, the output vector of byte vectors
satisfies:

  * `out'.val.length = iter'.i` — each `SortedSet<Pt>` contributes exactly one serialized byte
    vector.
  * `iter'.slice = iter.slice` — the iterator slice is unchanged across iterations.
  * For every `j ∈ [0, iter'.i)`, the `j`-th entry is the 4-byte-per-point big-endian
    serialization of the cartesian points in `inner j` (the double-deref of
    `iter.slice.val[j]`):
      `∃ serialized, out'.val[j]? = some serialized ∧
        serialized.val.length = 4 * (inner j).val.length ∧
        ∀ k < (inner j).val.length,
          ∃ b0 b1 b2 b3,
            serialized.val[4*k]?   = some b0 ∧ serialized.val[4*k+1]? = some b1 ∧
            serialized.val[4*k+2]? = some b2 ∧ serialized.val[4*k+3]? = some b3 ∧
            b0.val · 256 + b1.val = ((inner j).val[k]!).x.value.val ∧
            b2.val · 256 + b3.val = ((inner j).val[k]!).y.value.val`

At loop termination (`iter'.i ≥ iter'.slice.val.length`), the output vector contains the
complete serialization of all `SortedSet<Pt>` values in `iter.slice`.

The body spec (`body_spec` from `IntoPbLoopBody0.lean`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`iter'.slice.val.length − iter'.i`) to give the full loop postcondition.

Because both `SortedSet → SortedVec` and `SortedVec → Vec` deref operations are extracted as
opaque axioms (`sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref` and
`sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref`), we parameterise the spec by
index-dependent witnesses `sv : Nat → SortedVec Pt` and `inner : Nat → Vec Pt`, together with
the per-index deref equations.

In GF(2¹⁶) (characteristic 2), each field element is stored as a `u16`, and the big-endian
encoding of a cartesian point `Pt = (x, y)` satisfies `b0 · 256 + b1 = x.value`,
`b2 · 256 + b3 = y.value`.

**Source**: spqr/src/encoding/polynomial.rs (lines 800:8-809:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.into_pb_loop0

/-! ## Spec theorem for the into_pb outer serialization loop -/

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0`**:

The full outer point-set-serialization loop inside `PolyDecoder::into_pb`.  Given a slice
iterator `iter` over `SortedSet<Pt>` values (with per-index double-deref witnesses
`sv` and `inner`) and the current output vector of serialized byte vectors `v`, the loop drives
the body to completion and returns the output vector.

• The function always succeeds (no panic) provided the preconditions hold: for every index
  `k < iter.slice.val.length`, both deref operations on `iter.slice.val[k]` succeed yielding
  `sv k` and `inner k`; the output vector length equals the current iterator position
  (each previously processed `SortedSet<Pt>` contributed exactly one serialized byte vector);
  the total number of output entries does not overflow `Usize.max`; and each underlying point
  vector can be serialized without overflow.

• **Loop postcondition**:
  - `result.val.length = iter.slice.val.length` — the output contains exactly one serialized
    byte vector per `SortedSet<Pt>` in the slice.
  - For every `j < iter.slice.val.length`, the `j`-th entry is the big-endian serialization
    of the cartesian points in `inner j`:
      `∃ serialized, result.val[j]? = some serialized ∧
        serialized.val.length = 4 * (inner j).val.length ∧
        ∀ k < (inner j).val.length,
          ∃ b0 b1 b2 b3,
            serialized.val[4*k]?   = some b0 ∧ serialized.val[4*k+1]? = some b1 ∧
            serialized.val[4*k+2]? = some b2 ∧ serialized.val[4*k+3]? = some b3 ∧
            b0.val · 256 + b1.val = ((inner j).val[k]!).x.value.val ∧
            b2.val · 256 + b3.val = ((inner j).val[k]!).y.value.val`

    This corresponds to the Rust loop:
    ```rust
    for pts in self.pts.iter() {
        let mut v = Vec::<u8>::with_capacity(4 * pts.len());
        for i in 0..pts.len() {
            let pt = &pts[i];
            v.extend_from_slice(&pt.serialize()[..]);
        }
        out.pts.push(v);
    }
    ```

Because `SortedSet → SortedVec` and `SortedVec → Vec` derefs are opaque axioms in the
extraction, the caller supplies the index-parameterised witnesses `sv` and `inner` together
with the per-index deref equations `h_sv` and `h_inner`.  The proof lifts the body spec
through `loop.spec_decr_nat` with measure `iter'.slice.val.length − iter'.i`, maintaining the
point-set-serialization invariant.

**Source**: spqr/src/encoding/polynomial.rs (lines 800:8-809:9)
-/
@[step]
theorem loop_spec
    (iter : core.slice.iter.Iter (sorted_vec.SortedSet Pt))
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (sv : Nat → sorted_vec.SortedVec Pt)
    (inner : Nat → alloc.vec.Vec Pt)
    (h_sv : ∀ (k : Nat) (h : k < iter.slice.val.length),
      sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
        Pt.Insts.CoreCmpOrd (iter.slice.val[k]'h) = ok (sv k))
    (h_inner : ∀ (k : Nat), k < iter.slice.val.length →
      sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
        Pt.Insts.CoreCmpOrd (sv k) = ok (inner k))
    (h_out_len : v.val.length = iter.i)
    (h_i_le : iter.i ≤ iter.slice.val.length)
    (h_overflow : iter.slice.val.length + 1 ≤ Usize.max)
    (h_inner_overflow : ∀ (k : Nat), k < iter.slice.val.length →
        4 * (inner k).val.length + 4 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.i →
        ∃ (serialized : alloc.vec.Vec Std.U8),
          v.val[j]? = some serialized ∧
          serialized.val.length = 4 * (inner j).val.length ∧
          ∀ (k : Nat), k < (inner j).val.length →
            ∃ (b0 b1 b2 b3 : Std.U8),
              serialized.val[4 * k]?     = some b0 ∧
              serialized.val[4 * k + 1]? = some b1 ∧
              serialized.val[4 * k + 2]? = some b2 ∧
              serialized.val[4 * k + 3]? = some b3 ∧
              b0.val * 256 + b1.val = ((inner j).val[k]!).x.value.val ∧
              b2.val * 256 + b3.val = ((inner j).val[k]!).y.value.val) :
    into_pb_loop0 iter v ⦃ (result : alloc.vec.Vec (alloc.vec.Vec Std.U8)) =>
      result.val.length = iter.slice.val.length ∧
      ∀ (j : Nat), j < iter.slice.val.length →
        ∃ (serialized : alloc.vec.Vec Std.U8),
          result.val[j]? = some serialized ∧
          serialized.val.length = 4 * (inner j).val.length ∧
          ∀ (k : Nat), k < (inner j).val.length →
            ∃ (b0 b1 b2 b3 : Std.U8),
              serialized.val[4 * k]?     = some b0 ∧
              serialized.val[4 * k + 1]? = some b1 ∧
              serialized.val[4 * k + 2]? = some b2 ∧
              serialized.val[4 * k + 3]? = some b3 ∧
              b0.val * 256 + b1.val = ((inner j).val[k]!).x.value.val ∧
              b2.val * 256 + b3.val = ((inner j).val[k]!).y.value.val ⦄ := by
  unfold into_pb_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter (sorted_vec.SortedSet Pt) ×
                       alloc.vec.Vec (alloc.vec.Vec Std.U8)) =>
                  p.1.slice.val.length - p.1.i)
    (inv := fun (p : core.slice.iter.Iter (sorted_vec.SortedSet Pt) ×
                     alloc.vec.Vec (alloc.vec.Vec Std.U8)) =>
        let iter' := p.1
        let out' := p.2
        iter'.slice = iter.slice ∧
        iter'.i ≤ iter'.slice.val.length ∧
        out'.val.length = iter'.i ∧
        (∀ (j : Nat), j < iter'.i →
          ∃ (serialized : alloc.vec.Vec Std.U8),
            out'.val[j]? = some serialized ∧
            serialized.val.length = 4 * (inner j).val.length ∧
            ∀ (k : Nat), k < (inner j).val.length →
              ∃ (b0 b1 b2 b3 : Std.U8),
                serialized.val[4 * k]?     = some b0 ∧
                serialized.val[4 * k + 1]? = some b1 ∧
                serialized.val[4 * k + 2]? = some b2 ∧
                serialized.val[4 * k + 3]? = some b3 ∧
                b0.val * 256 + b1.val = ((inner j).val[k]!).x.value.val ∧
                b2.val * 256 + b3.val = ((inner j).val[k]!).y.value.val))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', out'⟩ ⟨h_slice', h_i_le', h_out_len', h_pre'⟩
    simp only [] at h_slice' h_i_le' h_out_len' h_pre' ⊢
    have h_slice_len : iter'.slice.val.length = iter.slice.val.length := by
      rw [h_slice']
    have h_body :=
      body_spec iter' out' (sv iter'.i) (inner iter'.i)
        (fun h_lt => by
          revert h_lt
          rw [h_slice']
          intro h_lt
          exact h_sv iter'.i h_lt)
        (fun h_lt => h_inner iter'.i (by rw [← h_slice_len]; exact h_lt))
        (by
          have h1 : out'.val.length = iter'.i := h_out_len'
          have h2 : iter'.i ≤ iter'.slice.val.length := h_i_le'
          have h3 : iter'.slice.val.length = iter.slice.val.length := h_slice_len
          have h4 : iter.slice.val.length + 1 ≤ Usize.max := h_overflow
          omega)
        (fun h_lt => h_inner_overflow iter'.i (by rw [← h_slice_len]; exact h_lt))
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done out'' =>
      simp only [] at h_cf ⊢
      obtain ⟨h_out_eq, h_not_lt⟩ := h_cf
      subst h_out_eq
      refine ⟨by omega, fun j hj => h_pre' j ?_⟩
      rw [h_slice_len] at h_not_lt
      omega
    | ControlFlow.cont (iter'', out'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_i1, h_slice1, serialized, h_out_eq, h_ser_len, h_ser_encode⟩ := h_cf
      have h_slice1_len : iter''.slice.val.length = iter'.slice.val.length := by
        rw [h_slice1]
      constructor
      · -- Invariant is preserved
        refine ⟨by rw [h_slice1]; exact h_slice',
               by omega,
               by rw [h_out_eq, List.length_append, List.length_singleton, h_out_len', h_i1],
               fun j hj => ?_⟩
        by_cases hj_lt : j < iter'.i
        · -- Previously serialized byte vectors: index falls in the prefix out'.val
          obtain ⟨ser', hser', hser_len', hser_enc'⟩ := h_pre' j hj_lt
          refine ⟨ser', ?_, hser_len', hser_enc'⟩
          rw [h_out_eq, getElem?_append_of_lt _ _ (by omega)]
          exact hser'
        · -- Newly appended byte vector: j = iter'.i
          have hj_eq : j = iter'.i := by omega
          subst hj_eq
          refine ⟨serialized, ?_, h_ser_len, h_ser_encode⟩
          rw [h_out_eq, show iter'.i = out'.val.length from by omega,
              List.getElem?_append_right (le_refl _)]
          simp
      · -- Measure decreases
        omega
  · -- Initial state satisfies the invariant
    exact ⟨rfl, h_i_le, h_out_len, h_pre⟩

end spqr.encoding.polynomial.PolyDecoder.into_pb_loop0
