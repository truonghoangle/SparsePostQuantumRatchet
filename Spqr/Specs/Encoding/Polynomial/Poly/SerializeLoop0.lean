/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.List
import Spqr.Specs.Encoding.Polynomial.Poly.SerializeLoopBody

/-!
# Spec theorem for `Poly::serialize`: loop 0

The Rust function `Poly::serialize` (in `src/encoding/polynomial.rs`, lines 329:4-340:5)
serializes a polynomial's GF(2¹⁶) coefficient vector into a byte vector by encoding each
coefficient's `u16` value as two big-endian bytes.

This file specifies **loop 0** — the full top-level `serialize_loop` that drives the
iterator-driven serialization body to completion.  The extracted Lean function
`encoding.polynomial.Poly.serialize_loop` repeatedly invokes
`encoding.polynomial.Poly.serialize_loop.body`, which at each step:

  1. Calls `next` on the `Range<usize>` iterator to obtain the current index `i`.
  2. Retrieves the `i`-th GF(2¹⁶) coefficient `c = v[i]`.
  3. Converts `c.value : u16` to its 2-byte big-endian representation via
     `u16::to_be_bytes`.
  4. Appends those bytes to the output vector `out` via `Vec::extend_from_slice`.

**Loop invariant**: after processing iterations up to `iter'`, the output byte vector
satisfies:

  * `out'.val.length = 2 * iter'.start.val` — each coefficient contributes exactly 2 bytes.
  * `iter'.«end» = iter.«end»` — the iterator end is unchanged across iterations.
  * For every `j ∈ [0, iter'.start.val)`, the big-endian encoding holds:
      `∃ hi lo, out'.val[2*j]? = some hi ∧ out'.val[2*j+1]? = some lo ∧
        hi.val * 256 + lo.val = (v.val[j]!).value.val`

At loop termination (`iter'.start.val ≥ iter'.«end».val`), the output vector contains the
complete serialization of all coefficients in `v.val[0..iter.«end».val]`.

The body spec (`serialize_loop.body_spec`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`iter'.«end».val − iter'.start.val`) to give the full loop postcondition.

In GF(2¹⁶) (characteristic 2), each field element is stored as a `u16`, and the big-endian
encoding satisfies `hi * 256 + lo = value` where `hi` and `lo` are the high and low bytes
respectively.

**Source**: spqr/src/encoding/polynomial.rs (lines 333:8-337:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.Poly.serialize_loop

/-! ## Spec theorem for the serialize loop -/

/-- **Spec theorem for `encoding.polynomial.Poly.serialize_loop`**:

The full `Poly::serialize` coefficient serialization loop.  Given the coefficient vector `v`,
a range iterator `iter` over indices into `v`, and the current output byte vector `out`, the
loop drives the body to completion and returns the serialized byte vector.

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end does not exceed the coefficient vector length, the output vector length equals
  `2 * iter.start.val` (each previously processed coefficient contributed exactly 2 bytes),
  and the total serialization does not overflow `Usize.max`.

• **Loop postcondition**:
  - `result.val.length = 2 * iter.«end».val` — the output contains exactly two bytes per
    coefficient in the range.
  - For every `j < iter.«end».val`, the big-endian encoding invariant holds:
      `∃ hi lo, result.val[2*j]? = some hi ∧ result.val[2*j+1]? = some lo ∧
        hi.val * 256 + lo.val = (v.val[j]!).value.val`

    This corresponds to the Rust loop:
    ```rust
    for i in 0..self.coefficients.len() {
        let c = self.coefficients[i];
        out.extend_from_slice(&c.value.to_be_bytes()[..]);
    }
    ```

The proof lifts the body spec through `loop.spec_decr_nat` with measure
`iter'.«end».val − iter'.start.val`, maintaining the byte-encoding invariant.

**Source**: spqr/src/encoding/polynomial.rs (lines 333:8-337:9)
-/
@[step]
theorem loop_spec
    (v : alloc.vec.Vec encoding.gf.GF16)
    (iter : core.ops.range.Range Std.Usize)
    (out : alloc.vec.Vec Std.U8)
    (h_end_le : iter.«end».val ≤ v.val.length)
    (h_out_len : out.val.length = 2 * iter.start.val)
    (h_start_le : iter.start.val ≤ iter.«end».val)
    (h_overflow : 2 * v.val.length + 2 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start.val →
        ∃ (hi lo : Std.U8),
          out.val[2 * j]? = some hi ∧
          out.val[2 * j + 1]? = some lo ∧
          hi.val * 256 + lo.val = (v.val[j]!).value.val) :
    serialize_loop iter v out ⦃ (result : alloc.vec.Vec Std.U8) =>
      result.val.length = 2 * iter.«end».val ∧
      ∀ (j : Nat), j < iter.«end».val →
        ∃ (hi lo : Std.U8),
          result.val[2 * j]? = some hi ∧
          result.val[2 * j + 1]? = some lo ∧
          hi.val * 256 + lo.val = (v.val[j]!).value.val ⦄ := by
  unfold serialize_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize × alloc.vec.Vec Std.U8) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize × alloc.vec.Vec Std.U8) =>
        let iter' := p.1
        let out' := p.2
        iter'.«end» = iter.«end» ∧
        iter'.start.val ≤ iter'.«end».val ∧
        out'.val.length = 2 * iter'.start.val ∧
        (∀ (j : Nat), j < iter'.start.val →
          ∃ (hi lo : Std.U8),
            out'.val[2 * j]? = some hi ∧
            out'.val[2 * j + 1]? = some lo ∧
            hi.val * 256 + lo.val = (v.val[j]!).value.val))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', out'⟩ ⟨h_end', h_start_le', h_out_len', h_pre'⟩
    simp only [] at h_end' h_start_le' h_out_len' h_pre' ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_body := body_spec v iter' out' (by omega) (by omega)
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
      obtain ⟨h_lt, h_start1, h_end1, hi, lo, h_out_eq, h_encode⟩ := h_cf
      have h_end1_val : iter''.«end».val = iter'.«end».val := by rw [h_end1]
      constructor
      · -- Invariant is preserved
        refine ⟨by rw [h_end1]; exact h_end',
               by omega,
               by rw [h_out_eq]; simp [h_out_len']; omega,
               fun j hj => ?_⟩
        by_cases hj_lt : j < iter'.start.val
        · -- Previously serialized bytes: index falls in the prefix out'.val
          obtain ⟨hi', lo', hhi', hlo', henc'⟩ := h_pre' j hj_lt
          refine ⟨hi', lo', ?_, ?_, henc'⟩
          · rw [h_out_eq, getElem?_append_of_lt _ _ (by omega)]; exact hhi'
          · rw [h_out_eq, getElem?_append_of_lt _ _ (by omega)]; exact hlo'
        · -- Newly appended bytes: j = iter'.start.val
          have hj_eq : j = iter'.start.val := by omega
          subst hj_eq
          refine ⟨hi, lo, ?_, ?_, h_encode⟩
          · rw [h_out_eq, show 2 * iter'.start.val = out'.val.length from by omega,
                List.getElem?_append_right (le_refl _)]
            simp
          · rw [h_out_eq, show 2 * iter'.start.val + 1 = out'.val.length + 1 from by omega,
                List.getElem?_append_right (by omega)]
            simp
      · -- Measure decreases
        omega
  · -- Initial state satisfies the invariant
    exact ⟨rfl, h_start_le, h_out_len, h_pre⟩

end spqr.encoding.polynomial.Poly.serialize_loop
