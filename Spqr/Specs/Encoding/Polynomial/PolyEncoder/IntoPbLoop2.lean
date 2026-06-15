/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPbLoopBody2

/-!
# Spec theorem for `PolyEncoder::into_pb`: loop 2

The extracted Lean function `encoding.polynomial.PolyEncoder.into_pb_loop1` is the
polynomial-serialization loop inside `PolyEncoder::into_pb` (the `EncoderState::Polys` branch).
Given a slice iterator over an array of 16 `Poly` values (each containing a vector of GF(2¹⁶)
coefficients) and the current output vector of byte vectors `v`, the loop repeatedly invokes
`encoding.polynomial.PolyEncoder.into_pb_loop1.body`, which at each step:

  1. Calls `next` on the slice iterator to obtain the current `Poly` value.
  2. Serializes the polynomial's `.coefficients` field (a vector of GF(2¹⁶) elements) into a byte
     vector using `Poly::serialize`.
  3. Pushes the resulting byte vector onto the output vector `v`.

**Loop invariant**: after processing iterations up to `iter'`, the output vector of byte vectors
satisfies:

  * `out'.val.length = iter'.i` — each `Poly` contributes exactly one serialized byte vector.
  * `iter'.slice = iter.slice` — the slice reference is unchanged across iterations.
  * For every `j ∈ [0, iter'.i)`, the `j`-th entry is the serialized form of the `j`-th
    polynomial's GF(2¹⁶) coefficients:
      `∃ serialized, out'.val[j]? = some serialized ∧
        serialized.val.length = 2 * (iter.slice.val[j]!).coefficients.val.length ∧
        ∀ k < (iter.slice.val[j]!).coefficients.val.length,
          ∃ hi lo, serialized.val[2*k]? = some hi ∧ serialized.val[2*k+1]? = some lo ∧
            hi.val * 256 + lo.val = ((iter.slice.val[j]!).coefficients.val[k]!).value.val`

At loop termination (the slice iterator is exhausted, `iter'.i ≥ iter'.slice.val.length`), the
output vector contains the complete serialization of all polynomials in the slice.

The body spec (`body_spec` from `IntoPbLoopBody2.lean`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`iter'.slice.val.length − iter'.i`) to give the full loop postcondition.

In GF(2¹⁶) (characteristic 2), each field element is stored as a `u16`, and the big-endian
encoding satisfies `hi * 256 + lo = value` where `hi` and `lo` are the high and low bytes
respectively.

**Source**: spqr/src/encoding/polynomial.rs (lines 565:16-567:17)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.into_pb_loop1

/-! ## Spec theorem for the into_pb polynomial-serialization loop -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb_loop1`**:

The full polynomial-serialization loop inside `PolyEncoder::into_pb` (the `EncoderState::Polys`
branch).  Given a slice iterator `iter` over the array of 16 `Poly` values and the current output
vector of serialized byte vectors `v`, the loop drives the body to completion and returns the
output vector.

• The function always succeeds (no panic) provided the preconditions hold: the slice length
  plus one does not exceed `Usize.max`, the output vector length equals `iter.i` (each
  previously processed polynomial contributed exactly one serialized byte vector), and each
  polynomial's GF(2¹⁶) coefficient vector can be serialized without overflow.

• **Loop postcondition**:
  - `result.val.length = iter.slice.val.length` — the output contains exactly one serialized byte
    vector per polynomial in the slice.
  - For every `j < iter.slice.val.length`, the `j`-th entry is the serialized form of the `j`-th
    polynomial's GF(2¹⁶) coefficients:
      `∃ serialized, result.val[j]? = some serialized ∧
        serialized.val.length = 2 * (iter.slice.val[j]!).coefficients.val.length ∧
        ∀ k < (iter.slice.val[j]!).coefficients.val.length,
          ∃ hi lo, serialized.val[2*k]? = some hi ∧ serialized.val[2*k+1]? = some lo ∧
            hi.val * 256 + lo.val = ((iter.slice.val[j]!).coefficients.val[k]!).value.val`

    This corresponds to the Rust loop:
    ```rust
    for poly in polys.iter() {
        out.polys.push(poly.serialize());
    }
    ```

The proof lifts the body spec through `loop.spec_decr_nat` with measure
`iter'.slice.val.length − iter'.i`, maintaining the polynomial-serialization invariant.

**Source**: spqr/src/encoding/polynomial.rs (lines 565:16-567:17)
-/
@[step]
theorem loop_spec
    (iter : core.slice.iter.Iter encoding.polynomial.Poly)
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h_out_len : v.length = iter.i)
    (h_start_le : iter.i ≤ iter.slice.length)
    (h_overflow : iter.slice.length + 1 ≤ Usize.max)
    (h_ser_overflow : ∀ j < iter.slice.length,
        2 * (iter.slice[j]!).degree + 2 ≤ Usize.max)
    (h_pre : ∀ j < iter.i,
          (v[j]!).length = 2 * (iter.slice[j]!).degree ∧
          ∀ k < (iter.slice[j]!).degree,
              256 * (v[j]!)[2 * k]! + (v[j]!)[2 * k + 1]! =
                ((iter.slice[j]!).coefficients[k]!).value.val) :
    into_pb_loop1 iter v ⦃ (result : alloc.vec.Vec (alloc.vec.Vec Std.U8)) =>
      result.length = iter.slice.length ∧
      ∀ j < iter.slice.length,
          (result[j]!).length =
            2 * (iter.slice[j]!).degree ∧
          ∀ k < (iter.slice[j]!).degree,
              256 * (result[j]!)[2 * k]! + (result[j]!)[2 * k + 1]! =
                ((iter.slice[j]!).coefficients[k]!).value.val ⦄ := by
  unfold into_pb_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter encoding.polynomial.Poly ×
                       alloc.vec.Vec (alloc.vec.Vec Std.U8)) =>
                  p.1.slice.length - p.1.i)
    (inv := fun (p : core.slice.iter.Iter encoding.polynomial.Poly ×
                     alloc.vec.Vec (alloc.vec.Vec Std.U8)) =>
        let iter' := p.1
        let out' := p.2
        iter'.slice = iter.slice ∧
        iter'.i ≤ iter'.slice.length ∧
        out'.length = iter'.i ∧
        (∀ j < iter'.i,
            (out'[j]!).length =
              2 * (iter.slice[j]!).degree ∧
            ∀ k < (iter.slice[j]!).degree,
                256 * (out'[j]!)[2 * k]!+ (out'[j]!)[2 * k + 1]! =
                  ((iter.slice[j]!).coefficients[k]!).value.val))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', out'⟩ ⟨h_slice', h_start_le', h_out_len', h_pre'⟩
    simp only [] at h_slice' h_start_le' h_out_len' h_pre' ⊢
    have h_slice_len : iter'.slice.val.length = iter.slice.val.length := by rw [h_slice']
    have h_body := body_spec iter' out' (by grind) (by rw [h_slice']; exact h_ser_overflow)
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done out'' =>
      simp only [] at h_cf ⊢
      obtain ⟨h_out_eq, h_not_lt⟩ := h_cf
      subst h_out_eq
      simp_all
      grind
    | ControlFlow.cont (iter'', out'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_i1, h_slice1, serialized, h_out_eq, h_ser_len, h_ser_encode⟩ := h_cf
      have h_slice1_len : iter''.slice.val.length = iter'.slice.val.length := by rw [h_slice1]
      rw [h_slice'] at h_ser_len h_ser_encode
      constructor
      · -- Invariant is preserved
        refine ⟨by rw [h_slice1]; exact h_slice',
               by grind,
               by grind,
               fun j hj => ?_⟩
        by_cases hj_lt : j < iter'.i
        · -- Previously serialized byte vectors: index falls in the prefix out'.val
          grind
        · -- Newly appended byte vector: j = iter'.i
          grind
      · -- Measure decreases
        grind
  · -- Initial state satisfies the invariant
    exact ⟨rfl, h_start_le, h_out_len, h_pre⟩

end spqr.encoding.polynomial.PolyEncoder.into_pb_loop1
