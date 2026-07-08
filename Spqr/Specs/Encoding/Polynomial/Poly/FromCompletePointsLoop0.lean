/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
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
the iterator-driven validation/computation body to completion.

**Source**: spqr/src/encoding/polynomial.rs (lines 293:8-327:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly core.iter.adapters.enumerate core.slice.iter
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial.Poly.from_complete_points_loop

/--
**Spec theorem for `encoding.polynomial.Poly.from_complete_points_loop`**:

The full `Poly::from_complete_points` validation/computation loop.

The `Ok` postcondition uses `scaledLagrangeBasis (Slice.len pts) j` to express the
Lagrange interpolation sum directly, without existentially quantifying the intermediate
`polys` slice.

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
          p.toGF216Poly = ∑ j ∈ Finset.range pts.val.length,
            C ((pts.val[j]!).y.toGF216) * scaledLagrangeBasis (Slice.len pts) j
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
      obtain ⟨h_not_lt, h_sum⟩ := h_cf
      exact ⟨fun j hj => h_pre' j (by omega) hj, h_sum⟩
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
