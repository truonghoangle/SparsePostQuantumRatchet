/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeSum
import Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePointsLoopBody0

/-!
# Spec theorem for `Poly::from_complete_points`: loop 0

The Rust function `Poly::from_complete_points` (in `src/encoding/polynomial.rs`, lines
292:4-327:5) reconstructs the unique polynomial of degree `< pts.len()` that interpolates a
set of "complete" points — points whose `x`-coordinates fully fill the contiguous range
`[0, pts.len())` in GF(2¹⁶) (cast from `usize` to `u16`).  The protocol-V1 admissible sizes
are `0, 1, 3, 5, 30, 34, 36`, and for each of these a precomputed array of Lagrange basis
polynomials (`COMPLETE_POINTS_POLYS_N`) is shipped statically so that the heavy
Lagrange-denominator computation can be avoided at runtime.

After the iterator-driven validation prologue

```rust
for (i, pt) in pts.iter().enumerate() {
    if pt.x.value != i as u16 {
        return Err(());
    }
}
```

the function selects the precomputed basis array by `pts.len()` and delegates the linear
combination

   `out = Σ_{i = 0}^{pts.len() − 1} pts[i].y · polys[i]`

to `Poly::lagrange_sum` (in `GF216[X] = (GaloisField 2 16)[X]`).

This file specifies **loop 0** — the full top-level `from_complete_points_loop` that drives
the iterator-driven validation/computation body to completion.  The extracted Lean function
`encoding.polynomial.Poly.from_complete_points_loop` performs:

  1. Repeatedly invoke
     `encoding.polynomial.Poly.from_complete_points_loop.body pts iter`, advancing the
     `Enumerate<SliceIter<Pt>>` iterator one position per `cont` and either:
       * exiting with `Err(())` as soon as some
         `pts[i].x.value.val ≠ i.val` is detected, or
       * exiting with `Ok(p)` once the iterator is exhausted, where `p` is the
         GF(2¹⁶)[X] Lagrange linear combination computed via
         `Poly::lagrange_sum pts polys` with `polys` being the basis array
         corresponding to `pts.len()` (one of `COMPLETE_POINTS_POLYS_N`).

The body spec (`from_complete_points_loop.body_spec`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`pts.val.length − iter.iter.i`) to give the full loop postcondition.

**Loop invariant**: after processing iterations up to `iter'`, the partial validation
holds for every already-consumed index, and the slice that the iterator refers to is
unchanged (`iter'.iter.slice = pts`):

  * `iter'.iter.slice = pts` — the slice the iterator refers to is the original `pts`.
  * `iter'.iter.i ≤ pts.val.length` — the iterator position never exceeds the slice length.
  * `iter'.count.val ≤ UScalar.max .U16` — the count stays within `u16` range.
  * `iter'.count.val = iter'.iter.i` — the enumerator count equals the iterator position.
  * For every `j ∈ [0, iter'.iter.i)`, the validation predicate holds:
      `(pts.val.get ⟨j, _⟩).x.value.val = j`.

At loop termination, two cases arise:

  * **Validation success** (`Ok p`): the iterator is exhausted, i.e. every
    `pts[j].x.value.val = j` for `j < pts.val.length`, and `p` is the GF(2¹⁶)[X] Lagrange
    linear combination
      `p.toGF216Poly =
         Σ_{j ∈ Finset.range pts.val.length} C ((pts[j]!).y.toGF216) · (polys[j]!).toGF216Poly`
    where `polys = COMPLETE_POINTS_POLYS_{pts.len()}` (after `const_polys_to_polys`).

  * **Validation failure** (`Err ()`): there exists some `j < pts.val.length` with
    `(pts[j]!).x.value.val ≠ j`.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of
the 16-bit encodings (`a + b = a − b = a ⊕ b`); multiplication is carry-less polynomial
multiplication modulo the irreducible polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).
The protocol-V1 size restriction (`pts.len() ∈ {0, 1, 3, 5, 30, 34, 36}`) is propagated
through the body spec; outside this set the body uses a fallback
`lagrange_polys_for_complete_points`-based computation, but the high-level Lagrange-sum
postcondition is preserved for every admissible size.

**Source**: spqr/src/encoding/polynomial.rs (lines 293:8-327:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly core.iter.adapters.enumerate core.slice.iter
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial.Poly.from_complete_points_loop

/--
**Spec theorem for `encoding.polynomial.Poly.from_complete_points_loop`**:

The full `Poly::from_complete_points` validation/computation loop.  Given an
`Enumerate<SliceIter<Pt>>` iterator `iter` (typically the freshly-allocated iterator at
position `iter.iter.i = 0`, `iter.count.val = 0`) and the underlying points slice `pts`
(satisfying `iter.iter.slice = pts`), the loop drives the body to completion and returns
one of:

• The function always succeeds (no panic) provided the preconditions hold.

• **Loop postcondition** — case split on the returned `core.result.Result`:

  - **`Ok p` (validation success and Lagrange sum)**: every consumed slot satisfied the
    validation predicate `pts[j].x.value.val = j`, and the returned polynomial `p` is
    the GF(2¹⁶)[X] Lagrange linear combination.

  - **`Err ()` (validation failure)**: some consumed slot `j < pts.val.length` had
    `(pts.val[j]!).x.value.val ≠ j`.

The proof lifts the body spec through `loop.spec_decr_nat` with measure
`pts.val.length − iter.iter.i`, maintaining the iterator-state invariant.

**Source**: spqr/src/encoding/polynomial.rs (lines 293:8-327:5)
-/
@[step]
theorem loop_spec
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_count : iter.count.val ≤ UScalar.max .U16)
    (h_count_eq : iter.count.val = iter.iter.i)
    (h_slice_eq : iter.iter.slice = pts)
    (h_i_le : iter.iter.i ≤ pts.val.length)
    (h_pts_len : pts.val.length ≤ UScalar.max .U16)
    (h_len_ok : pts.val.length = 0 ∨ pts.val.length = 1 ∨ pts.val.length = 3 ∨
                pts.val.length = 5 ∨ pts.val.length = 30 ∨ pts.val.length = 34 ∨
                pts.val.length = 36)
    (h_pre : ∀ (j : Nat), j < iter.iter.i →
        ∀ (hj : j < pts.val.length),
          (pts.val.get ⟨j, hj⟩).x.value.val = j) :
    from_complete_points_loop iter pts ⦃ (result : core.result.Result Poly Unit) =>
      match result with
      | core.result.Result.Ok p =>
          (∀ (j : Nat) (hj : j < pts.val.length),
            (pts.val.get ⟨j, hj⟩).x.value.val = j) ∧
          ∃ (polys : Slice Poly),
            pts.val.length ≤ polys.val.length ∧
            (p.toGF216Poly = ∑ j ∈ Finset.range pts.val.length,
              C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly) ∧
            (pts.val.length = 0 →
              polys.val.length = 0 ∧ p.toGF216Poly = 0) ∧
            (pts.val.length ≠ 0 →
              polys.val.length = pts.val.length ∧
              ∃ (N : Usize) (ones1 : Array Pt N),
                N.val = pts.val.length ∧
                (∀ (j : Nat), j < N.val →
                  ∀ (hj : j < ones1.val.length),
                    (ones1.val.get ⟨j, hj⟩).x.value.val = j ∧
                    (ones1.val.get ⟨j, hj⟩).y = GF16.ONE) ∧
                (∀ (j : Nat), j < N.val →
                  ∀ (hj : j < polys.val.length)
                    (hjo : j < ones1.val.length),
                    (polys.val.get ⟨j, hj⟩).toGF216Poly =
                      C ((ones1.val.get ⟨j, hjo⟩).y.toGF216 *
                          (lagrangeDenomProd (ones1.val.get ⟨j, hjo⟩).x
                            (ones1.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
                        condProdLinearFactors (ones1.val.get ⟨j, hjo⟩).x
                          (ones1.val.take N.val) 0))
      | core.result.Result.Err () =>
          ∃ (j : Nat) (hj : j < pts.val.length),
            (pts.val.get ⟨j, hj⟩).x.value.val ≠ j ⦄ := by
  unfold from_complete_points_loop
  apply loop.spec_decr_nat
    (measure := fun iter' => pts.val.length - iter'.iter.i)
    (inv := fun iter' =>
      iter'.iter.slice = pts ∧
      iter'.iter.i ≤ pts.val.length ∧
      iter'.count.val ≤ UScalar.max .U16 ∧
      iter'.count.val = iter'.iter.i ∧
      (∀ (j : Nat), j < iter'.iter.i →
        ∀ (hj : j < pts.val.length),
          (pts.val.get ⟨j, hj⟩).x.value.val = j))
  · -- Step: the body preserves the invariant or produces the final result
    intro iter' ⟨h_slice', h_i_le', h_count', h_count_eq', h_pre'⟩
    have h_body := body_spec pts iter' h_count' h_slice' h_len_ok
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done (core.result.Result.Ok p) =>
      simp only [] at h_cf ⊢
      obtain ⟨h_not_lt, polys, h_polys_len, h_sum, h_zero, h_nonzero⟩ := h_cf
      exact ⟨fun j hj => h_pre' j (by omega) hj,
             polys, h_polys_len, h_sum, h_zero, h_nonzero⟩
    | ControlFlow.done (core.result.Result.Err ()) =>
      simp only [] at h_cf ⊢
      obtain ⟨h_i_lt, h_neq⟩ := h_cf
      exact ⟨iter'.iter.i, h_i_lt, by omega⟩
    | ControlFlow.cont iter'' =>
      simp only [] at h_cf ⊢
      obtain ⟨h_i_lt, h_val_eq, h_iter_i, h_iter_slice, h_iter_count⟩ := h_cf
      constructor
      · -- Invariant is preserved
        exact ⟨h_iter_slice, by omega, by omega, by omega, fun j hj hj_lt => by
          by_cases hj_lt' : j < iter'.iter.i
          · exact h_pre' j hj_lt' hj_lt
          · have hj_eq : j = iter'.iter.i := by omega
            subst hj_eq
            exact h_val_eq.trans h_count_eq'⟩
      · -- Measure decreases
        omega
  · -- Initial state satisfies the invariant
    exact ⟨h_slice_eq, h_i_le, h_count, h_count_eq, h_pre⟩

end spqr.encoding.polynomial.Poly.from_complete_points_loop
