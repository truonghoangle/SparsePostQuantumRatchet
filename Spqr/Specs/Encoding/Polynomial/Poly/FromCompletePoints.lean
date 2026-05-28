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

**Source**: spqr/src/encoding/polynomial.rs (lines 292:4-327:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly core.iter.adapters.enumerate core.slice.iter
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial.Poly

/--
**Spec theorem for `encoding.polynomial.Poly.from_complete_points`**:

• Takes a slice `pts : Slice Pt` of points in GF(2¹⁶) × GF(2¹⁶).
• Allocates a fresh `SliceIter<Pt>` at position `0` via `core.slice.Slice.iter pts`
  and wraps it into an `Enumerate<SliceIter<Pt>>` with `count = 0` via
  `IteratorSliceIter.enumerate`.
• Delegates immediately to
    `from_complete_points_loop iter pts`
  which drives the iterator-based validation/computation body to completion.

• The function always succeeds (no panic) for any input slice `pts`, since:
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
calls, then discharges the resulting goal with `step*`, which applies the
already-registered `from_complete_points_loop.loop_spec` at the trivial initial
iterator state.

**Source**: spqr/src/encoding/polynomial.rs (lines 292:4-327:5)
-/
@[step]
theorem from_complete_points_spec
    (pts : Slice Pt) :
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
  unfold from_complete_points
  step*

end spqr.encoding.polynomial.Poly
