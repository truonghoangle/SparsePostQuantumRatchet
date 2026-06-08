/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.Basic.Defs
import Spqr.Math.Poly.Basic.Zero
import Spqr.Math.Poly.Coeff.Basic
import Spqr.Math.Poly.Coeff.ListOps
import Spqr.Math.Poly.CharTwo.Basic
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Math.Poly.Eval
import Spqr.Math.Poly.LinearFactors.Basic
import Spqr.Math.Poly.LinearFactors.Degree
import Spqr.Math.Poly.Lagrange.DenomProd
import Spqr.Math.Poly.Lagrange.BasisPoly
import Spqr.Math.Poly.Lagrange.InterpolantSum
import Spqr.Math.Poly.Horner.Defs
import Spqr.Math.Poly.Horner.Eval
import Spqr.Math.Poly.ExpectedTrailing.Defs
import Spqr.Math.Poly.ExpectedTrailing.Basic
import Spqr.Math.Poly.Identities.Basic
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeSum
import Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePointsLoop0
import Spqr.Specs.Encoding.Polynomial.LagrangePolysForCompletePoints
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_1
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_3
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_5
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_30
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_34
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_36

/-!
# Spec theorem for `spqr::encoding::polynomial::{Poly}::from_complete_points`

The Rust function `Poly::from_complete_points` (in `src/encoding/polynomial.rs`,
lines 292:4-327:5) reconstructs the unique polynomial of degree `< pts.len()`
that interpolates a set of "complete" points — points whose `x`-coordinates
fully fill the contiguous range `[0, pts.len())` in GF(2¹⁶) (cast from `usize`
to `u16`):

```rust
fn from_complete_points(pts: &[Pt]) -> Result<Poly, ()> {
    for (i, pt) in pts.iter().enumerate() {
        if pt.x.value != i as u16 {
            return Err(());
        }
    }
    let polys = match pts.len() as u64 {
        0  => vec![],
        1  => const_polys_to_polys(&COMPLETE_POINTS_POLYS_1),
        3  => const_polys_to_polys(&COMPLETE_POINTS_POLYS_3),
        5  => const_polys_to_polys(&COMPLETE_POINTS_POLYS_5),
        30 => const_polys_to_polys(&COMPLETE_POINTS_POLYS_30),
        34 => const_polys_to_polys(&COMPLETE_POINTS_POLYS_34),
        36 => const_polys_to_polys(&COMPLETE_POINTS_POLYS_36),
        _  => { /* fallback: lagrange_polys_for_complete_points */ }
    };
    Ok(Self::lagrange_sum(pts, &polys))
}
```

The Aeneas-extracted Lean function `encoding.polynomial.Poly.from_complete_points`
performs:

  1. `core.slice.Slice.iter pts` — obtains a `SliceIter<Pt>` starting at index 0.
  2. `core.slice.iter.IteratorSliceIter.enumerate i` — wraps the slice iterator
     into an `Enumerate<SliceIter<Pt>>` with `count = 0`.
  3. `encoding.polynomial.Poly.from_complete_points_loop iter pts` — drives the
     iterator-based validation/computation loop body to completion, either
     short-circuiting with `Err(())` as soon as some `pts[i].x.value ≠ i as u16`
     is detected, or returning `Ok(p)` where
       `p = Σ_{j = 0}^{pts.len()−1} pts[j].y · polys[j]`
     in `GF216[X] = (GaloisField 2 16)[X]`, with `polys` being the precomputed
     Lagrange basis array corresponding to `pts.len()`.

The protocol-V1 admissible sizes are `pts.len() ∈ {0, 1, 3, 5, 30, 34, 36}`, and
for each of these a precomputed array of Lagrange basis polynomials
(`COMPLETE_POINTS_POLYS_N`) is shipped statically so that the heavy
Lagrange-denominator computation can be avoided at runtime.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is
bitwise XOR of the 16-bit encodings (`a + b = a − b = a ⊕ b`); multiplication
is carry-less polynomial multiplication modulo the irreducible polynomial
`x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

This top-level wrapper introduces no additional logic beyond the iterator
setup (`Slice.iter` followed by `Enumerate`), so its postcondition is
inherited verbatim from the corresponding `from_complete_points_loop`
specification, instantiated at the freshly-allocated iterator
`iter.iter.i = 0`, `iter.count.val = 0`, `iter.iter.slice = pts`.

**Precondition**: `pts.val.length ≤ UScalar.max .U16` (= 65535) is required
because the loop body casts the iteration index from `Usize` to `U16` via
`UScalar.cast .U16 i`; without this bound the cast would overflow.

**Source**: spqr/src/encoding/polynomial.rs (lines 292:4-327:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly core.iter.adapters.enumerate core.slice.iter
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial.Poly

/--
**Spec theorem for `encoding.polynomial.Poly.from_complete_points`**:

• Takes a slice `pts : Slice Pt` of points in GF(2¹⁶) × GF(2¹⁶).
• Requires `pts.val.length ≤ UScalar.max .U16` so that the `Usize → U16`
  cast of each iteration index does not overflow.
• Allocates a fresh `SliceIter<Pt>` at position `0` via `core.slice.Slice.iter pts`
  and wraps it into an `Enumerate<SliceIter<Pt>>` with `count = 0` via
  `IteratorSliceIter.enumerate`.
• Delegates immediately to
    `from_complete_points_loop iter pts`
  which drives the iterator-based validation/computation body to completion.

• The function always succeeds (no panic) for any input slice `pts` satisfying
  the length precondition, since:
    1. `Slice.iter` is total on `Slice T`, producing an iterator at position `0`.
    2. `IteratorSliceIter.enumerate` is total, producing an `Enumerate` with
       `count = 0`.
    3. The loop spec (`from_complete_points_loop.loop_spec`) is total under the
       trivial initial-iterator preconditions
       (`iter.count.val = 0 ≤ UScalar.max .U16`, `iter.count.val = iter.iter.i = 0`,
       `iter.iter.slice = pts`, `iter.iter.i = 0 ≤ pts.val.length`, and the
       per-index validation hypothesis is vacuous for `j < 0`).

• **Postcondition** — case split on the returned `core.result.Result`:

  - **`Ok p` (validation success and Lagrange sum)**: every slot of `pts`
    satisfied the validation predicate `pts[j].x.value.val = j`, and the
    returned polynomial `p` is the GF(2¹⁶)[X] Lagrange linear combination
      `p.toGF216Poly =
         ∑ j ∈ Finset.range pts.val.length,
           C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly`
    where `polys` is the basis slice corresponding to `pts.len()`
    (one of `COMPLETE_POINTS_POLYS_N` after `const_polys_to_polys`), with the
    additional structural guarantees inherited from the loop spec:
      * `pts.val.length ≤ polys.val.length`;
      * `pts.val.length = 0 → polys.val.length = 0 ∧ p.toGF216Poly = 0`;
      * for the admissible non-zero sizes
        (`pts.val.length ∈ {1, 3, 5, 30, 34, 36}`),
        `polys.val.length = pts.val.length` and the basis array `ones1`
        satisfies the "complete points" identities
        `ones1[j].x.value.val = j ∧ ones1[j].y = GF16.ONE`
        together with the explicit Lagrange-basis polynomial identities.

  - **`Err ()` (validation failure)**: there exists some `j < pts.val.length`
    with `(pts.val[j]!).x.value.val ≠ j` — the slice is not in "complete points"
    form, and the function short-circuits as in the original Rust source.

The proof unfolds `from_complete_points` to expose the underlying
`Slice.iter`, `IteratorSliceIter.enumerate`, and `from_complete_points_loop`
calls, simplifies the iterator setup via `simp only`, and then applies
`from_complete_points_loop.loop_spec` at the trivial initial iterator state
via `WP.spec_mono`.

**Source**: spqr/src/encoding/polynomial.rs (lines 292:4-327:5)
-/
@[step]
theorem from_complete_points_spec
    (pts : Slice Pt)
    (h_len_ok : pts.val.length = 0 ∨ pts.val.length = 1 ∨ pts.val.length = 3 ∨
                pts.val.length = 5 ∨ pts.val.length = 30 ∨ pts.val.length = 34 ∨
                pts.val.length = 36) :
    from_complete_points pts ⦃ (result : core.result.Result Poly Unit) =>
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
  have h_pts_len : pts.val.length ≤ UScalar.max .U16 := by
    grind
  unfold from_complete_points
  simp only [core.slice.Slice.iter,
             core.slice.iter.IteratorSliceIter.enumerate, bind_tc_ok]
  exact from_complete_points_loop.loop_spec pts _
    (by simp) (by simp) rfl (by grind) h_pts_len h_len_ok
    (by intro j hj; grind)


/--
**Spec theorem for `encoding.polynomial.Poly.from_complete_points` (non-admissible sizes)**:

When `pts.val.length` is NOT one of the admissible sizes `{0, 1, 3, 5, 30, 34, 36}`,
the function cannot return `Ok` (because the `none` branch panics for non-admissible
sizes). If the function succeeds at all, it must return `Err ()`, meaning there is a
validation failure at some index.

Two additional preconditions are required beyond the non-admissibility hypothesis:

• `h_pts_len`: the slice length fits in a `U16`, so that each iterator-count → `U16`
  cast is exact and validation comparisons are faithful.

• `h_exists`: there exists at least one validation failure. Without this, the function
  reaches the exhausted-iterator branch and panics (`fail panic`), making the WP
  (total correctness) spec unprovable.

**Source**: spqr/src/encoding/polynomial.rs (lines 292:4-327:5)
-/
@[step]
theorem from_complete_points_Not_spec
    (pts : Slice Pt)
    (h_pts_len : pts.val.length ≤ UScalar.max .U16)
    (h_exists : ∃ (j : Nat) (hj : j < pts.val.length),
        (pts.val.get ⟨j, hj⟩).x.value.val ≠ j) :
    from_complete_points pts ⦃ (result : core.result.Result Poly Unit) =>
      match result with
      | core.result.Result.Ok p =>
          False
      | core.result.Result.Err () =>
          ∃ (j : Nat) (hj : j < pts.val.length),
            (pts.val.get ⟨j, hj⟩).x.value.val ≠ j ⦄ := by
  unfold from_complete_points
  simp only [core.slice.Slice.iter,
             core.slice.iter.IteratorSliceIter.enumerate, bind_tc_ok]
  unfold from_complete_points_loop
  apply loop.spec_decr_nat
    (measure := fun iter' => pts.val.length - iter'.iter.i)
    (inv := fun iter' =>
      iter'.iter.slice = pts ∧
      iter'.count.val ≤ UScalar.max .U16 ∧
      iter'.count.val = iter'.iter.i ∧
      (∀ (j : Nat), j < iter'.iter.i →
        ∀ (hj : j < pts.val.length),
          (pts.val.get ⟨j, hj⟩).x.value.val = j) ∧
      (∃ (k : Nat), iter'.iter.i ≤ k ∧ k < pts.val.length ∧
        ∀ (hk : k < pts.val.length),
          (pts.val.get ⟨k, hk⟩).x.value.val ≠ k))
  · -- Step: body preserves invariant or returns Err
    intro iter' ⟨h_slice', h_count', h_count_eq', h_pre', k, h_k_ge, h_k_lt, h_k_neq⟩
    have h_in_bounds : iter'.iter.i < pts.val.length := by omega
    have h_body := from_complete_points_loop.body_spec_inbounds pts iter'
      h_count' h_slice' h_in_bounds
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done (core.result.Result.Ok _) =>
      exact h_cf.elim
    | ControlFlow.done (core.result.Result.Err ()) =>
      simp only [] at h_cf ⊢
      -- Validation failed at iter'.iter.i
      exact ⟨iter'.iter.i, h_in_bounds, by rw [h_count_eq'] at h_cf; exact h_cf⟩
    | ControlFlow.cont iter'' =>
      simp only [] at h_cf ⊢
      obtain ⟨h_val_eq, h_iter_i, h_iter_slice, h_iter_count⟩ := h_cf
      constructor
      · -- Invariant preserved
        refine ⟨h_iter_slice, ?_, ?_, ?_, ?_⟩
        · -- count ≤ max .U16
          omega
        · -- count = iter.i
          omega
        · -- all previous validated
          intro j hj hj_lt
          by_cases hj' : j < iter'.iter.i
          · exact h_pre' j hj' hj_lt
          · have : j = iter'.iter.i := by omega
            subst this
            rw [h_count_eq'] at h_val_eq
            exact h_val_eq
        · -- future failure still exists
          have h_k_ne : k ≠ iter'.iter.i := by
            intro heq; subst heq
            rw [h_count_eq'] at h_val_eq
            exact h_k_neq h_k_lt h_val_eq
          exact ⟨k, by omega, h_k_lt, h_k_neq⟩
      · -- Measure decreases
        omega
  · -- Initial invariant
    obtain ⟨j, hj, h_neq⟩ := h_exists
    refine ⟨rfl, by simp, by simp, ?_, j, ?_, hj, fun _ => h_neq⟩
    · intro j' hj'; simp at hj'
    · simp

end spqr.encoding.polynomial.Poly
