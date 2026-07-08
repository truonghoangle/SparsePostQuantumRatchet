/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAtLoopBody0
import Spqr.Math.Poly.Lagrange.CompletePoints

/-!
# Spec theorem for `PolyEncoder::point_at`: loop 0

The extracted Lean function `encoding.polynomial.PolyEncoder.point_at_loop` is the
point-to-polynomial conversion loop inside `PolyEncoder::point_at`.  Given a fixed-size array
`pts` of 16 `Point` values (each wrapping a `Vec<GF16>` of evaluation data over GF(2¹⁶)), a
`Range<usize>` iterator over `0..NUM_POLYS`, and the current output array of 16 `Poly` values,
the loop repeatedly invokes `encoding.polynomial.PolyEncoder.point_at_loop.body`, which at each
step:

  1. Calls `next` on the `Range<usize>` iterator to obtain the current index `i`.
  2. Retrieves the `i`-th `Point` from `pts`.
  3. Constructs evaluation points `Pt { x: GF16::new(j as u16), y: pts[i].value[j] }` for each
     `j < pts[i].value.len()` via an enumerate-map-collect pipeline.
  4. Calls `Poly::from_complete_points` on the resulting `Vec<Pt>` to obtain the unique Lagrange
     interpolating polynomial.
  5. Stores the result in `polys[i]`.

**Loop invariant**: after processing iterations up to `iter'`, the output array of `Poly` values
satisfies:

  * `iter'.«end» = iter.«end»` — the iterator end is unchanged across iterations.
  * `iter'.start.val ≤ iter'.«end».val` — the start never exceeds the end.
  * For every `j ∈ [0, iter'.start.val)`, the `j`-th entry is the Lagrange interpolating
    polynomial through the evaluation points of `pts[j]`:
      `∃ poly len,
          len.val = (pts.val[j]!).value.val.length ∧
          polys'.val[j]! = poly ∧
          poly.toGF216Poly =
            ∑ k ∈ Finset.range (pts.val[j]!).value.val.length,
              C (((pts.val[j]!).value.val[k]!).toGF216) *
                scaledLagrangeBasis len k`

At loop termination (`iter'.start.val ≥ iter'.«end».val`), the output array contains the
complete set of Lagrange interpolating polynomials for all points in `pts[0..iter.«end».val]`.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the
16-bit encodings; multiplication is carry-less polynomial multiplication modulo the irreducible
polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

The body spec (`body_spec` from `PointAtLoopBody0.lean`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`iter'.«end».val − iter'.start.val`) to give the full loop postcondition.

**Source**: spqr/src/encoding/polynomial.rs (lines 636:12-658:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial.PolyEncoder.point_at_loop

/-! ## Inhabited instance -/

/--
`Poly` wraps a `Vec<GF16>` of coefficients.  An `Inhabited` instance is required so that
`getElem!` (`[·]!`) on arrays/lists of `Poly` has a well-defined default value.  We use the empty
coefficient vector as the canonical default.
-/
instance : Inhabited encoding.polynomial.Poly := ⟨⟨alloc.vec.Vec.new _⟩⟩

/-! ## Spec theorem for the point_at conversion loop -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.point_at_loop`**:

The full point-to-polynomial conversion loop inside `PolyEncoder::point_at`.  Given the
fixed-size array `pts` of 16 `Point` values, a range iterator `iter` over indices, and the
current output array of 16 `Poly` values, the loop drives the body to completion and returns
the output array of interpolating polynomials.

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end does not exceed the array size (16), each point's value vector has an admissible length
  (one of 0, 1, 3, 5, 30, 34, or 36 — the protocol-V1 sizes for which precomputed Lagrange
  basis arrays are shipped statically), and the pre-existing entries in the output array
  already satisfy the interpolation invariant.

• **Loop postcondition**:
  - For every `j < iter.«end».val`, the `j`-th polynomial in the output array is the Lagrange
    interpolating polynomial through the evaluation points of `pts[j]`:
      `∃ poly len,
          len.val = (pts.val[j]!).value.val.length ∧
          polys'.val[j]! = poly ∧
          poly.toGF216Poly =
            ∑ k ∈ Finset.range (pts.val[j]!).value.val.length,
              C (((pts.val[j]!).value.val[k]!).toGF216) *
                scaledLagrangeBasis len k`

    This corresponds to the Rust loop:
    ```rust
    for i in 0..NUM_POLYS {
        let pt_vec = pts[i].value.iter().enumerate()
            .map(|(x, y)| Pt { x: GF16::new(x as u16), y: *y })
            .collect::<Vec<Pt>>();
        hax_lib::assume!(pt_vec.len() == 0 || ... || pt_vec.len() == 36);
        let res = Poly::from_complete_points(&pt_vec);
        hax_lib::assume!(res.is_ok());
        polys[i] = res.expect("pt_vec should be complete");
    }
    ```

The proof lifts the body spec through `loop.spec_decr_nat` with measure
`iter'.«end».val − iter'.start.val`, maintaining the Lagrange-interpolation invariant.

**Source**: spqr/src/encoding/polynomial.rs (lines 636:12-658:13)
-/
@[step]
theorem loop_spec
    (pts : Array encoding.polynomial.Point 16#usize)
    (iter : core.ops.range.Range Std.Usize)
    (polys : Array encoding.polynomial.Poly 16#usize)
    (h_end_le_16 : iter.«end».val ≤ 16)
    (h_start_le : iter.start.val ≤ iter.«end».val)
    (h_admissible : ∀ (j : Nat), j < 16 →
        let len := (pts.val[j]!).value.val.length
        len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
        len = 30 ∨ len = 34 ∨ len = 36)
    (h_pre : ∀ (j : Nat), j < iter.start.val →
        ∃ (poly : encoding.polynomial.Poly) (len : Usize),
          len.val = (pts.val[j]!).value.val.length ∧
          polys.val[j]! = poly ∧
          (poly.toGF216Poly =
            ∑ k ∈ Finset.range
                (pts.val[j]!).value.val.length,
              C (((pts.val[j]!).value.val[k]!).toGF216) *
                scaledLagrangeBasis len k)) :
    point_at_loop iter pts polys ⦃ (polys' : Array encoding.polynomial.Poly 16#usize) =>
      ∀ (j : Nat), j < iter.«end».val →
        ∃ (poly : encoding.polynomial.Poly) (len : Usize),
          len.val = (pts.val[j]!).value.val.length ∧
          polys'.val[j]! = poly ∧
          (poly.toGF216Poly =
            ∑ k ∈ Finset.range
                (pts.val[j]!).value.val.length,
              C (((pts.val[j]!).value.val[k]!).toGF216) *
                scaledLagrangeBasis len k) ⦄ := by
  unfold point_at_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                       Array encoding.polynomial.Poly 16#usize) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                     Array encoding.polynomial.Poly 16#usize) =>
        let iter' := p.1
        let polys' := p.2
        iter'.«end» = iter.«end» ∧
        iter'.start.val ≤ iter'.«end».val ∧
        (∀ (j : Nat), j < iter'.start.val →
          ∃ (poly : encoding.polynomial.Poly) (len : Usize),
            len.val = (pts.val[j]!).value.val.length ∧
            polys'.val[j]! = poly ∧
            (poly.toGF216Poly =
              ∑ k ∈ Finset.range
                  (pts.val[j]!).value.val.length,
                C (((pts.val[j]!).value.val[k]!).toGF216) *
                  scaledLagrangeBasis len k)))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', polys'⟩ ⟨h_end', h_start_le', h_pre'⟩
    simp only [] at h_end' h_start_le' h_pre' ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_body := body_spec pts iter' polys' (by omega) h_admissible
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done polys'' =>
      simp only [] at h_cf ⊢
      obtain ⟨h_out_eq, h_not_lt⟩ := h_cf
      subst h_out_eq
      exact fun j hj => h_pre' j (by grind)
    | ControlFlow.cont (iter'', polys'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, poly, h_poly_eq, h_preserve, len,
              h_len_val, h_sum⟩ := h_cf
      constructor
      · -- Invariant is preserved
        refine ⟨by rw [h_end1]; exact h_end',
               by grind,
               fun j hj => ?_⟩
        by_cases hj_lt : j < iter'.start.val
        · -- Previously processed: j is in the prefix
          obtain ⟨poly', len', h_len_val', h_eq', h_lp_sum'⟩ := h_pre' j hj_lt
          exact ⟨poly', len', h_len_val', (h_preserve j (by omega)).trans h_eq', h_lp_sum'⟩
        · -- Newly processed: j = iter'.start.val
          have hj_eq : j = iter'.start.val := by omega
          subst hj_eq
          exact ⟨poly, len, h_len_val, h_poly_eq, h_sum⟩
      · -- Measure decreases
        grind
  · -- Initial state satisfies the invariant
    exact ⟨rfl, h_start_le, h_pre⟩

end spqr.encoding.polynomial.PolyEncoder.point_at_loop
