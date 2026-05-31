/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPbLoopBody0

/-!
# Spec theorem for `PolyEncoder::into_pb`: loop 0

The extracted Lean function `encoding.polynomial.PolyEncoder.into_pb_loop0` is the outer
point-serialization loop inside `PolyEncoder::into_pb`.  Given a fixed-size array `points` of 16
`Point` values (each containing a vector of GF(2¹⁶) coefficients), a `Range<usize>` iterator over
`0..points.len()`, and the current output vector of byte vectors `v`, the loop repeatedly invokes
`encoding.polynomial.PolyEncoder.into_pb_loop0.body`, which at each step:

  1. Calls `next` on the `Range<usize>` iterator to obtain the current index `j`.
  2. Retrieves the `j`-th `Point` from `points`.
  3. Serializes its `.value` field (a vector of GF(2¹⁶) elements) into a byte vector using the
     inner coefficient-serialization loop (`into_pb_loop0_loop0`).
  4. Pushes the resulting byte vector onto the output vector `v`.

**Loop invariant**: after processing iterations up to `iter'`, the output vector of byte vectors
satisfies:

  * `out'.val.length = iter'.start.val` — each `Point` contributes exactly one serialized byte
    vector.
  * `iter'.«end» = iter.«end»` — the iterator end is unchanged across iterations.
  * For every `j ∈ [0, iter'.start.val)`, the `j`-th entry is the serialized form of the `j`-th
    point's GF(2¹⁶) coefficients:
      `∃ serialized, out'.val[j]? = some serialized ∧
        serialized.val.length = 2 * (points.val[j]!).value.val.length ∧
        ∀ k < (points.val[j]!).value.val.length,
          ∃ hi lo, serialized.val[2*k]? = some hi ∧ serialized.val[2*k+1]? = some lo ∧
            hi.val * 256 + lo.val = ((points.val[j]!).value.val[k]!).value.val`

At loop termination (`iter'.start.val ≥ iter'.«end».val`), the output vector contains the
complete serialization of all points in `points[0..iter.«end».val]`.

The body spec (`body_spec` from `IntoPbLoopBody0.lean`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`iter'.«end».val − iter'.start.val`) to give the full loop postcondition.

In GF(2¹⁶) (characteristic 2), each field element is stored as a `u16`, and the big-endian
encoding satisfies `hi * 256 + lo = value` where `hi` and `lo` are the high and low bytes
respectively.

**Source**: spqr/src/encoding/polynomial.rs (lines 551:16-562:17)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.into_pb_loop0

/-! ## Helper lemma: `getElem?` preservation under list append -/

/--
When index `i` falls within the first list `l₁`, indexing into the concatenation `l₁ ++ l₂`
returns the same element as indexing into `l₁` alone.  This is used to show that previously
serialized byte vectors are preserved when a new byte vector is appended.
-/
private lemma getElem?_append_of_lt {α : Type}
    (l₁ l₂ : List α) {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂)[i]? = l₁[i]? :=
  List.getElem?_append_left h

/-! ## Spec theorem for the into_pb outer serialization loop -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb_loop0`**:

The full outer serialization loop inside `PolyEncoder::into_pb`.  Given the fixed-size array
`points` of 16 `Point` values, a range iterator `iter` over indices into `points`, and the
current output vector of serialized byte vectors `v`, the loop drives the body to completion
and returns the output vector.

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end does not exceed the array length, the output vector length equals `iter.start.val` (each
  previously processed point contributed exactly one serialized byte vector), the total number
  of output entries does not overflow `Usize.max`, and each point's GF(2¹⁶) coefficient vector
  can be serialized without overflow.

• **Loop postcondition**:
  - `result.val.length = iter.«end».val` — the output contains exactly one serialized byte
    vector per point in the range.
  - For every `j < iter.«end».val`, the `j`-th entry is the serialized form of the `j`-th
    point's GF(2¹⁶) coefficients:
      `∃ serialized, result.val[j]? = some serialized ∧
        serialized.val.length = 2 * (points.val[j]!).value.val.length ∧
        ∀ k < (points.val[j]!).value.val.length,
          ∃ hi lo, serialized.val[2*k]? = some hi ∧ serialized.val[2*k+1]? = some lo ∧
            hi.val * 256 + lo.val = ((points.val[j]!).value.val[k]!).value.val`

    This corresponds to the Rust loop:
    ```rust
    for j in 0..points.len() {
        let pts = &points[j].value;
        let mut v = Vec::<u8>::with_capacity(2 * pts.len());
        for i in 0..pts.len() {
            let pt = pts[i];
            v.extend_from_slice(&pt.value.to_be_bytes()[..]);
        }
        out.pts.push(v);
    }
    ```

The proof lifts the body spec through `loop.spec_decr_nat` with measure
`iter'.«end».val − iter'.start.val`, maintaining the point-serialization invariant.

**Source**: spqr/src/encoding/polynomial.rs (lines 551:16-562:17)
-/
@[step]
theorem loop_spec
    (points : Array encoding.polynomial.Point 16#usize)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h_end_le : iter.«end».val ≤ points.val.length)
    (h_out_len : v.val.length = iter.start.val)
    (h_start_le : iter.start.val ≤ iter.«end».val)
    (h_overflow : points.val.length + 1 ≤ Usize.max)
    (h_inner_overflow : ∀ (j : Nat), j < points.val.length →
        2 * (points.val[j]!).value.val.length + 2 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start.val →
        ∃ (serialized : alloc.vec.Vec Std.U8),
          v.val[j]? = some serialized ∧
          serialized.val.length =
            2 * (points.val[j]!).value.val.length ∧
          ∀ (k : Nat),
            k < (points.val[j]!).value.val.length →
            ∃ (hi lo : Std.U8),
              serialized.val[2 * k]? = some hi ∧
              serialized.val[2 * k + 1]? = some lo ∧
              hi.val * 256 + lo.val =
                ((points.val[j]!).value.val[k]!).value.val) :
    into_pb_loop0 iter points v ⦃ (result : alloc.vec.Vec (alloc.vec.Vec Std.U8)) =>
      result.val.length = iter.«end».val ∧
      ∀ (j : Nat), j < iter.«end».val →
        ∃ (serialized : alloc.vec.Vec Std.U8),
          result.val[j]? = some serialized ∧
          serialized.val.length =
            2 * (points.val[j]!).value.val.length ∧
          ∀ (k : Nat),
            k < (points.val[j]!).value.val.length →
            ∃ (hi lo : Std.U8),
              serialized.val[2 * k]? = some hi ∧
              serialized.val[2 * k + 1]? = some lo ∧
              hi.val * 256 + lo.val =
                ((points.val[j]!).value.val[k]!).value.val ⦄ := by
  unfold into_pb_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                       alloc.vec.Vec (alloc.vec.Vec Std.U8)) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                     alloc.vec.Vec (alloc.vec.Vec Std.U8)) =>
        let iter' := p.1
        let out' := p.2
        iter'.«end» = iter.«end» ∧
        iter'.start.val ≤ iter'.«end».val ∧
        out'.val.length = iter'.start.val ∧
        (∀ (j : Nat), j < iter'.start.val →
          ∃ (serialized : alloc.vec.Vec Std.U8),
            out'.val[j]? = some serialized ∧
            serialized.val.length =
              2 * (points.val[j]!).value.val.length ∧
            ∀ (k : Nat),
              k < (points.val[j]!).value.val.length →
              ∃ (hi lo : Std.U8),
                serialized.val[2 * k]? = some hi ∧
                serialized.val[2 * k + 1]? = some lo ∧
                hi.val * 256 + lo.val =
                  ((points.val[j]!).value.val[k]!).value.val))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', out'⟩ ⟨h_end', h_start_le', h_out_len', h_pre'⟩
    simp only [] at h_end' h_start_le' h_out_len' h_pre' ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_body := body_spec points iter' out' (by omega) (by omega) h_inner_overflow
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
      obtain ⟨h_lt, h_start1, h_end1, serialized, h_out_eq, h_ser_len, h_ser_encode⟩ := h_cf
      have h_end1_val : iter''.«end».val = iter'.«end».val := by rw [h_end1]
      constructor
      · -- Invariant is preserved
        refine ⟨by rw [h_end1]; exact h_end',
               by omega,
               by rw [h_out_eq]; simp [h_out_len']; omega,
               fun j hj => ?_⟩
        by_cases hj_lt : j < iter'.start.val
        · -- Previously serialized byte vectors: index falls in the prefix out'.val
          obtain ⟨ser', hser', hser_len', hser_enc'⟩ := h_pre' j hj_lt
          refine ⟨ser', ?_, hser_len', hser_enc'⟩
          rw [h_out_eq, getElem?_append_of_lt _ _ (by omega)]
          exact hser'
        · -- Newly appended byte vector: j = iter'.start.val
          have hj_eq : j = iter'.start.val := by omega
          subst hj_eq
          refine ⟨serialized, ?_, h_ser_len, h_ser_encode⟩
          rw [h_out_eq, show iter'.start.val = out'.val.length from by omega,
              List.getElem?_append_right (le_refl _)]
          simp
      · -- Measure decreases
        omega
  · -- Initial state satisfies the invariant
    exact ⟨rfl, h_start_le, h_out_len, h_pre⟩

end spqr.encoding.polynomial.PolyEncoder.into_pb_loop0
