/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.General
import Spqr.Specs.Encoding.Polynomial.Poly.DeserializeLoopBody0

/-!
# Spec theorem for `Poly::deserialize`: loop 0

The Rust function `Poly::deserialize` (in `src/encoding/polynomial.rs`, lines 342:4-353:5)
deserializes a byte slice into a polynomial's GF(2¹⁶) coefficient vector by decoding each
pair of consecutive bytes as a big-endian `u16` value, wrapped as a `GF16` element.

This file specifies **loop 0** — the full top-level `deserialize_loop` that drives the
iterator-driven deserialization body to completion.  The extracted Lean function
`encoding.polynomial.Poly.deserialize_loop` repeatedly invokes
`encoding.polynomial.Poly.deserialize_loop.body`, which at each step:

  1. Calls `next` on the `Range<usize>` iterator to obtain the current index `i`.
  2. Computes `j = i * 2` and reads `serialized[j]` and `serialized[j+1]`.
  3. Converts the two bytes from big-endian to a `u16` via `u16::from_be_bytes`.
  4. Wraps the result as a `GF16` via `GF16::new` and pushes it onto the `coefficients` vector.

**Loop invariant**: after processing iterations up to `iter'`, the coefficient vector
satisfies:

  * `coefficients'.val.length = iter'.start.val` — each iteration contributes exactly one
    GF(2¹⁶) coefficient.
  * `iter'.«end» = iter.«end»` — the iterator end is unchanged across iterations.
  * For every `j ∈ [0, iter'.start.val)`, the big-endian decoding holds:
      `∃ g, coefficients'.val[j]? = some g ∧
        g.value.val = (serialized.val[2*j]!).val * 256 + (serialized.val[2*j+1]!).val`

At loop termination (`iter'.start.val ≥ iter'.«end».val`), the coefficient vector contains
the complete deserialization of all byte pairs in `serialized.val[0..2*iter.«end».val]`.

The body spec (`deserialize_loop.body_spec`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`iter'.«end».val − iter'.start.val`) to give the full loop postcondition.

In GF(2¹⁶) (characteristic 2), each field element is stored as a `u16`, and the big-endian
encoding satisfies `hi * 256 + lo = value` where `hi` and `lo` are the high and low bytes
respectively.  This loop is the inverse of the serialization loop.

**Source**: spqr/src/encoding/polynomial.rs (lines 347:8-350:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.Poly.deserialize_loop

/-! ## Spec theorem for the deserialize loop -/

/-- **Spec theorem for `encoding.polynomial.Poly.deserialize_loop`**:

The full `Poly::deserialize` coefficient deserialization loop.  Given the serialized byte
slice `serialized`, a range iterator `iter` over `0..(serialized.len() / 2)`, and the current
coefficient vector `coefficients`, the loop drives the body to completion and returns the
deserialized coefficient vector.

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end satisfies `2 * iter.«end».val ≤ serialized.val.length` (ensuring that byte pairs are
  in bounds), the coefficient vector length equals `iter.start.val` (each previously processed
  byte pair contributed exactly one coefficient), and the total deserialization does not
  overflow `Usize.max`.

• **Loop postcondition**:
  - `result.val.length = iter.«end».val` — the coefficient vector contains exactly one
    GF(2¹⁶) element per byte pair in the range.
  - For every `j < iter.«end».val`, the big-endian decoding invariant holds:
      `∃ g, result.val[j]? = some g ∧
        g.value.val = (serialized.val[2*j]!).val * 256 + (serialized.val[2*j+1]!).val`

    This corresponds to the Rust loop:
    ```rust
    for i in 0..(serialized.len() / 2) {
        let j = i * 2;
        coefficients.push(GF16::new(u16::from_be_bytes([serialized[j], serialized[j+1]])));
    }
    ```

The proof lifts the body spec through `loop.spec_decr_nat` with measure
`iter'.«end».val − iter'.start.val`, maintaining the coefficient-decoding invariant.

**Source**: spqr/src/encoding/polynomial.rs (lines 347:8-350:9)
-/
@[step]
theorem loop_spec
    (serialized : Slice Std.U8)
    (iter : core.ops.range.Range Std.Usize)
    (coefficients : alloc.vec.Vec encoding.gf.GF16)
    (h_end_le : 2 * iter.«end».val ≤ serialized.val.length)
    (h_coeff_len : coefficients.val.length = iter.start.val)
    (h_start_le : iter.start.val ≤ iter.«end».val)
    (h_overflow : iter.«end».val + 1 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start.val →
        ∃ (g : encoding.gf.GF16),
          coefficients.val[j]? = some g ∧
          g.value.val =
            (serialized.val[2 * j]!).val * 256 +
            (serialized.val[2 * j + 1]!).val) :
    deserialize_loop iter serialized coefficients ⦃ (result : alloc.vec.Vec encoding.gf.GF16) =>
      result.val.length = iter.«end».val ∧
      ∀ (j : Nat), j < iter.«end».val →
        ∃ (g : encoding.gf.GF16),
          result.val[j]? = some g ∧
          g.value.val =
            (serialized.val[2 * j]!).val * 256 +
            (serialized.val[2 * j + 1]!).val ⦄ := by
  unfold deserialize_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize × alloc.vec.Vec encoding.gf.GF16) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize × alloc.vec.Vec encoding.gf.GF16) =>
        let iter' := p.1
        let coefficients' := p.2
        iter'.«end» = iter.«end» ∧
        iter'.start.val ≤ iter'.«end».val ∧
        coefficients'.val.length = iter'.start.val ∧
        (∀ (j : Nat), j < iter'.start.val →
          ∃ (g : encoding.gf.GF16),
            coefficients'.val[j]? = some g ∧
            g.value.val =
              (serialized.val[2 * j]!).val * 256 +
              (serialized.val[2 * j + 1]!).val))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', coefficients'⟩ ⟨h_end', h_start_le', h_coeff_len', h_pre'⟩
    simp only [] at h_end' h_start_le' h_coeff_len' h_pre' ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_body := body_spec serialized iter' coefficients' (by omega) (by omega)
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done coefficients'' =>
      simp only [] at h_cf ⊢
      obtain ⟨h_coeff_eq, h_not_lt⟩ := h_cf
      subst h_coeff_eq
      exact ⟨by omega, fun j hj => h_pre' j (by omega)⟩
    | ControlFlow.cont (iter'', coefficients'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, g, h_coeff_eq, h_encode⟩ := h_cf
      have h_end1_val : iter''.«end».val = iter'.«end».val := by rw [h_end1]
      constructor
      · -- Invariant is preserved
        refine ⟨by rw [h_end1]; exact h_end',
               by omega,
               by rw [h_coeff_eq]; simp [h_coeff_len']; omega,
               fun j hj => ?_⟩
        by_cases hj_lt : j < iter'.start.val
        · -- Previously deserialized coefficients: index falls in the prefix coefficients'.val
          obtain ⟨g', hg', henc'⟩ := h_pre' j hj_lt
          refine ⟨g', ?_, henc'⟩
          rw [h_coeff_eq, getElem?_append_of_lt _ _ (by omega)]; exact hg'
        · -- Newly appended coefficient: j = iter'.start.val
          have hj_eq : j = iter'.start.val := by omega
          subst hj_eq
          refine ⟨g, ?_, h_encode⟩
          rw [h_coeff_eq, show iter'.start.val = coefficients'.val.length from by omega,
              List.getElem?_append_right (le_refl _)]
          simp
      · -- Measure decreases
        omega
  · -- Initial state satisfies the invariant
    exact ⟨rfl, h_start_le, h_coeff_len, h_pre⟩

end spqr.encoding.polynomial.Poly.deserialize_loop
