/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.Poly.Zero
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeSumLoop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::lagrange_sum`

The Rust function `Poly::lagrange_sum` (in `src/encoding/polynomial.rs`, lines 277:4-285:5) is the
internal helper used by `lagrange_polynomial_from_complete_points`.  Given a slice of points
`pts : &[Pt]` together with a parallel slice of "basis" polynomials `polys : &[Poly]` (one
polynomial per point), it computes the GF(2¹⁶)[X] linear combination

  `out = Σ_{i = 0}^{pts.len() − 1} pts[i].y · polys[i]`

by initialising `out` to the zero polynomial of capacity `pts.len()` and then iterating

```
for i in 0..pts.len() {
    let mut p = polys[i].clone();
    p.mult_assign(pts[i].y);
    out.add_assign(&p);
}
```

Concretely, the Aeneas-extracted Lean function `encoding.polynomial.Poly.lagrange_sum`:

  1. Computes `i := pts.len()`.
  2. Allocates the running accumulator `out := Poly::zero(i)` — a `Poly` with an empty coefficient
     vector and the given capacity hint (see `Zero.zero_spec`).
  3. Re-computes the slice length `i1 := pts.len()` (this is duplicated by the extraction; it has
     no effect on the meaning).
  4. Delegates to `encoding.polynomial.Poly.lagrange_sum_loop` with the range `0..pts.len()`,
     the points slice `pts`, the basis-polynomials slice `polys`, and the empty initial
     accumulator `out`.

Since the top-level function introduces no additional logic beyond the zero-polynomial allocation
and the loop delegation, its postcondition is composed from:
  - **`Zero.zero_spec`**: establishes that `out.coefficients.val.length = 0` and
    `out.toGF216Poly = 0`.  The empty-coefficient-vector fact discharges the
    `h_out_M : out.coefficients.val.length ≤ M` precondition of the loop, and the
    `toGF216Poly = 0` fact discharges the `h_sum` initial partial-sum invariant at
    `iter.start = 0` (the empty sum is `0`).
  - **`LagrangeSumLoop0.loop_spec`**: runs the accumulation loop from `i = 0` to
    `i = pts.len()`, ending with the running accumulator equal to the full Lagrange
    linear combination over `Finset.range (max 0 pts.len()) = Finset.range pts.len()`.

Combining the two gives the final result:
  `result.toGF216Poly =
       ∑ j ∈ Finset.range pts.val.length,
         C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly`
in `GF216[X] = (GaloisField 2 16)[X]`.  This is exactly the GF(2¹⁶)[X] Lagrange linear combination
used to assemble the interpolating polynomial of
`lagrange_polynomial_from_complete_points`.

The Rust code reads `polys[i]` for every `i < pts.len()`, so the spec requires that `polys` be at
least as long as `pts`.  Each basis polynomial `polys[i]` is scaled by `pts[i].y` via
`mult_assign` (which requires `polys[i].coefficients.val.length + 2 ≤ Usize.max`, see
`MultAssign.mult_assign_spec`) and then accumulated into `out` via `add_assign` (which requires
the combined coefficient length to fit in `Usize`, see `AddAssign.add_assign_spec`).  Both
preconditions are uniformly dischargeable from a single bound `M` on the coefficient-vector lengths
of the `polys[i]` together with the bound `M + M ≤ Usize.max`, since the running accumulator's
coefficient-vector length stays uniformly bounded by `M` throughout the loop (the body's
strengthened length post-condition gives `out'.length = max out.length polys[i].length`).

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the
16-bit encodings:
  `a + b = a − b = a ⊕ b`,
and multiplication is carry-less polynomial multiplication modulo the irreducible polynomial
`x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 277:4-285:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly

/--
**Spec theorem for `spqr.encoding.polynomial.Poly.lagrange_sum`**:


Given a slice of points `pts : Slice Pt`, a parallel slice of basis polynomials
`polys : Slice Poly` covering at least every index `i < pts.len()`, and a uniform bound `M` on the
coefficient-vector lengths of those basis polynomials, the function returns a polynomial `result`
whose mathematical content in `GF216[X] = (GaloisField 2 16)[X]` is the Lagrange linear combination

  `result.toGF216Poly =
       ∑ j ∈ Finset.range pts.val.length,
         C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly`.

• The function always succeeds (no panic) provided the preconditions hold, since
  `Poly::zero` is total and the loop body (`lagrange_sum_loop.body_spec`) is total when each
  `polys[i]` admits the GF(2¹⁶) scalar multiplication
  (`polys[i].coefficients.val.length + 2 ≤ Usize.max`) and the running accumulator's combined
  length with the scaled contribution stays within `Usize.max` — both ensured by the uniform
  bound `M` and the constraint `M + M ≤ Usize.max`.

• **Polynomial-level Lagrange-sum postcondition**:
    `result.toGF216Poly =
         ∑ j ∈ Finset.range pts.val.length,
           C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly`
  where `C : GF216 →+* GF216[X]` is the constant-polynomial embedding,
  `toGF216Poly : Poly → GF216Poly` interprets the coefficient vector as a polynomial in
  `GF216[X]`, and the `+` and `*` on the right-hand side are polynomial addition and
  multiplication in `GF216[X]` (with addition coinciding with subtraction in characteristic 2,
  i.e. coefficient-wise XOR).

The preconditions are:

* `h_len_le`: `pts.val.length ≤ polys.val.length` — the basis-polynomials slice is at least as
  long as the points slice, so each read `polys[i]` for `i < pts.len()` is in range.
* `h_M_bound`: `M + M ≤ Usize.max` — bounds `M` so that the combined length of any two
  bounded coefficient vectors fits in `Usize`, and a fortiori so that the stride-of-two
  `parallel_mult` precondition `length + 2 ≤ Usize.max` of `mult_assign` is satisfied.
* `h_polys_M`: every basis polynomial `polys[i]` (for `i < polys.val.length`) has
  coefficient-vector length bounded by `M`.

**Source**: spqr/src/encoding/polynomial.rs (lines 277:4-285:5)
-/
@[step]
theorem lagrange_sum_spec
    (pts : Slice Pt)
    (polys : Slice Poly)
    (h_len_le : pts.val.length ≤ polys.val.length)
    (h_polys : ∀ i, i < pts.val.length →
        (polys.val[i]!).coefficients.val.length + 2 ≤ Usize.max) :
    lagrange_sum pts polys ⦃ (result : Poly) =>
        result.toGF216Poly = ∑ j ∈ Finset.range pts.val.length,
          C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly ⦄ := by
  unfold lagrange_sum
  step with zero_spec' (Slice.len pts) as ⟨out, h_out_len, h_out_zero⟩
  -- Discharge the loop preconditions from the uniform bound `M` and the empty initial
  -- accumulator produced by `Poly::zero`.
  have h_end_le_pts : (Slice.len pts).val ≤ pts.val.length := by simp
  have h_end_le_polys : (Slice.len pts).val ≤ polys.val.length := by
    grind
  have h_out : out.coefficients.val.length < Usize.max := by
    rw [h_out_len]
    grind
  -- The loop's `h_polys` precondition is parameterised by `iter.«end».val`, which here
  -- is `(Slice.len pts).val = pts.val.length`, matching `h_polys` directly.
  have h_polys' : ∀ i, i < (Slice.len pts).val →
      (polys.val[i]!).coefficients.val.length + 2 ≤ Usize.max := by
    intro i hi
    apply h_polys i
    simpa using hi
  have h_sum_init :
      out.toGF216Poly = ∑ j ∈ Finset.range (0#usize).val,
        C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly := by
    rw [h_out_zero]; simp
  -- Apply the loop spec and reduce the `max` in its postcondition.
  apply WP.spec_mono (lagrange_sum_loop.loop_spec pts polys
    { start := 0#usize, «end» := Slice.len pts } out
    h_end_le_pts h_end_le_polys h_out h_polys' h_sum_init)
  intro result h_result
  have h_max : max (0#usize).val (Slice.len pts).val = pts.val.length := by simp
  rw [h_max] at h_result
  exact h_result

end spqr.encoding.polynomial.Poly
