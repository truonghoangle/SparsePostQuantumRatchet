/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.NUM_POLYS
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAtLoop0
import Spqr.Specs.Encoding.Polynomial.Poly.ComputeAt

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::point_at`

The method `PolyEncoder::point_at` returns the GF(2¹⁶) evaluation of the `poly`-th polynomial at
the point with index `idx`.  A `PolyEncoder` holds either an array of 16 evaluation-data `Point`s
(`EncoderState::Points`) or an array of 16 interpolated `Poly`s (`EncoderState::Polys`).

The function handles two encoder states and proceeds as follows:
  1. `EncoderState::Polys(polys)` — the polynomials are already stored.  The function directly
     evaluates `polys[poly].compute_at(GF16::new(idx as u16))`.
  2. `EncoderState::Points(pts)` — only cached evaluation data is stored.
     a. If `idx < pts[poly].value.len()`, the cached value `pts[poly].value[idx]` is returned
        directly (fast path, no state transition).
     b. Otherwise, all 16 point vectors are converted to Lagrange interpolating polynomials
        via `point_at_loop` (iterating over `0..NUM_POLYS`), the encoder state transitions to
        `EncoderState::Polys(polys)`, and the requested value is computed via
        `polys[poly].compute_at(GF16::new(idx as u16))`.

The Points→Polys conversion composes:
  1. `point_at_loop` — Lagrange interpolation for all 16 points via `Poly::from_complete_points`.
  2. `Poly::compute_at` — polynomial evaluation at the requested point in GF(2¹⁶).

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the
16-bit encodings; multiplication is carry-less polynomial multiplication modulo the irreducible
polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 624:4-667:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder

/-! ## Inhabited instances -/

/--
`Poly` wraps a `Vec<GF16>` of coefficients.  An `Inhabited` instance is required so that
`getElem!` (`[·]!`) on arrays/lists of `Poly` has a well-defined default value.  We use the empty
coefficient vector as the canonical default.
-/
instance : Inhabited encoding.polynomial.Poly := ⟨⟨alloc.vec.Vec.new _⟩⟩

/--
`Point` wraps a `Vec<GF16>`.  An `Inhabited` instance is required so that `getElem!` (`[·]!`)
on arrays/lists of `Point` has a well-defined default value.  We use the empty value vector
as the canonical default.
-/
instance : Inhabited encoding.polynomial.Point := ⟨⟨alloc.vec.Vec.new _⟩⟩

/-! ## Spec theorems -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.point_at`** (Lagrange-sum level):

Returns the GF(2¹⁶) evaluation of the `poly`-th polynomial at index `idx`.  The postcondition
preserves the Lagrange-sum interpolation structure from the conversion loop.

The result satisfies one of three cases depending on the encoder state:

• **Polys branch** (`self.s = Polys polys`):
    The result is the evaluation of the stored polynomial:
      `result.toGF216 = (polys[poly]).toGF216Poly.eval (idx.val.toGF216)`
    and the encoder state is unchanged (`self' = self`).

• **Points branch, cache hit** (`self.s = Points pts`, `idx.val < pts[poly].value.len()`):
    The result is the cached evaluation value:
      `result = pts[poly].value[idx]`
    and the encoder state is unchanged (`self' = self`).

• **Points branch, cache miss** (`self.s = Points pts`, `idx.val ≥ pts[poly].value.len()`):
    The encoder state transitions to `Polys polys'` where each `polys'[j]` is the Lagrange
    interpolating polynomial through the evaluation points of `pts[j]`:
      `polys'[j].toGF216Poly =
         ∑ k ∈ Finset.range (pts[j].value.len()),
           C ((pts[j].value[k]).toGF216) * (lagrange_polys_j[k]).toGF216Poly`
    and the result is the polynomial evaluation:
      `result.toGF216 = (polys'[poly]).toGF216Poly.eval (idx.val.toGF216)`

This follows from composing:
  1. `point_at_loop.loop_spec`: Lagrange interpolation for all 16 points.
  2. `Poly.compute_at_spec`:  `compute_at p x ⦃ r => r.toGF216 = p.evalAt x ⦄`.

**Source**: spqr/src/encoding/polynomial.rs (lines 624:4-667:5)
-/
theorem point_at_spec_nat
    (self : encoding.polynomial.PolyEncoder) (poly idx : Std.Usize)
    (h_poly : poly.val < 16)
    (h_idx_u16 : idx.val ≤ UScalar.max .U16)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts.val[j]!).value.val.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_polys : ∀ polys, self.s = .Polys polys →
        (polys.val[poly.val]!).coefficients.val.length + 1 ≤ Usize.max) :
    point_at self poly idx
      ⦃ ((result, self') : encoding.gf.GF16 × encoding.polynomial.PolyEncoder) =>
        self'.idx = self.idx ∧
        match self.s with
        | .Points pts =>
            if idx.val < (pts.val[poly.val]!).value.val.length then
              result = (pts.val[poly.val]!).value.val[idx.val]! ∧
              self' = self
            else
              ∃ (polys' : Array encoding.polynomial.Poly 16#usize),
                self'.s = encoding.polynomial.EncoderState.Polys polys' ∧
                (∀ (j : Nat), j < 16 →
                  ∃ (p : encoding.polynomial.Poly),
                    polys'.val[j]! = p ∧
                    ∃ (lagrange_polys : Slice Poly),
                      (pts.val[j]!).value.val.length ≤
                        lagrange_polys.val.length ∧
                      (p.toGF216Poly =
                        ∑ k ∈ Finset.range
                            (pts.val[j]!).value.val.length,
                          C (((pts.val[j]!).value.val[k]!).toGF216) *
                            (lagrange_polys.val[k]!).toGF216Poly)) ∧
                result.toGF216 =
                  (polys'.val[poly.val]!).toGF216Poly.eval
                    (idx.val.toGF216)
        | .Polys polys =>
            result.toGF216 =
              (polys.val[poly.val]!).toGF216Poly.eval
                (idx.val.toGF216) ∧
            self' = self ⦄ := by
  unfold point_at
  cases h : self.s with
  | Points pts =>
    have h_adm := h_admissible pts h
    simp only [h]
    sorry
  | Polys polys =>
    have h_coeff := h_coeff_polys polys h
    simp only [h]
    sorry

/--
For any encoder state, the result of `point_at self poly idx` evaluates the `poly`-th polynomial
at the GF(2¹⁶) point `idx.val.toGF216`.  This theorem lifts the Lagrange-sum postcondition of
`point_at_spec_nat` to the simplified polynomial evaluation form, dropping the explicit
interpolation structure:

• **Polys**: `result.toGF216 = (polys[poly]).toGF216Poly.eval (idx.val.toGF216)`, state unchanged.
• **Points, cache hit**: `result = pts[poly].value[idx]`, state unchanged.
• **Points, cache miss**: there exist interpolated polynomials `polys'` such that
    `result.toGF216 = (polys'[poly]).toGF216Poly.eval (idx.val.toGF216)`
    and the state transitions to `Polys polys'`.

Specializing `Poly.toGF216Poly.eval` to the canonical polynomial evaluation in
`GF216[X] = (GaloisField 2 16)[X]` recovers the intended field-level computation.
-/
@[step]
theorem point_at_spec
    (self : encoding.polynomial.PolyEncoder) (poly idx : Std.Usize)
    (h_poly : poly.val < 16)
    (h_idx_u16 : idx.val ≤ UScalar.max .U16)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts.val[j]!).value.val.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_polys : ∀ polys, self.s = .Polys polys →
        (polys.val[poly.val]!).coefficients.val.length + 1 ≤ Usize.max) :
    point_at self poly idx
      ⦃ ((result, self') : encoding.gf.GF16 × encoding.polynomial.PolyEncoder) =>
        self'.idx = self.idx ∧
        match self.s with
        | .Points pts =>
            if idx.val < (pts.val[poly.val]!).value.val.length then
              result = (pts.val[poly.val]!).value.val[idx.val]! ∧
              self' = self
            else
              ∃ (polys' : Array encoding.polynomial.Poly 16#usize),
                self'.s = encoding.polynomial.EncoderState.Polys polys' ∧
                result.toGF216 =
                  (polys'.val[poly.val]!).toGF216Poly.eval
                    (idx.val.toGF216)
        | .Polys polys =>
            result.toGF216 =
              (polys.val[poly.val]!).toGF216Poly.eval
                (idx.val.toGF216) ∧
            self' = self ⦄ := by
  have h_raw := point_at_spec_nat self poly idx h_poly h_idx_u16 h_admissible h_coeff_polys
  apply WP.spec_mono h_raw
  intro (result, self') ⟨h_idx_eq, h_data⟩
  refine ⟨h_idx_eq, ?_⟩
  cases h : self.s with
  | Points pts =>
    simp only [h] at h_data ⊢
    by_cases h_lt : idx.val < (pts.val[poly.val]!).value.val.length
    · simp only [h_lt, ↓reduceIte] at h_data ⊢
      exact h_data
    · simp only [h_lt, ↓reduceIte] at h_data ⊢
      obtain ⟨polys', h_state, _, h_eval⟩ := h_data
      exact ⟨polys', h_state, h_eval⟩
  | Polys polys =>
    simp only [h] at h_data ⊢
    exact h_data

end spqr.encoding.polynomial.PolyEncoder
