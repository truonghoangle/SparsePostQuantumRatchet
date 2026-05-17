/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeSumLoopBody0

/-!
# Spec theorem for `Poly::lagrange_sum`: loop 0

The Rust function `Poly::lagrange_sum` (in `src/encoding/polynomial.rs`, lines 277:4-285:5) is the
internal helper used by `lagrange_polynomial_from_complete_points`.  Given a list of points
`pts : &[Pt]` together with a parallel list of "basis" polynomials `polys : &[Poly]` (one polynomial
per point), it forms the GF(2¹⁶)[X] linear combination

  `out = Σ_{i = 0}^{pts.len() − 1} pts[i].y · polys[i]`

by initialising `out` to the zero polynomial of length `pts.len()` and then iterating

```
for i in 0..pts.len() {
    let mut p = polys[i].clone();
    p.mult_assign(pts[i].y);
    out.add_assign(&p);
}
```

This file specifies the **full loop** — the `loop` fixed-point wrapper around the body
(`LagrangeSumLoopBody0.body_spec`).  The loop consumes the `Range<usize>` iterator from `0` to
`pts.len()`, extending the running Lagrange linear combination by one scaled basis polynomial per
iteration until the iterator is exhausted.  At each step:

  1. The iterator yields the next index `i` (starting from 0).
  2. The body clones `polys[i]` into a scratch polynomial `p`, scales it in place by
     `pts[i].y` via `mult_assign` — giving a polynomial whose `GF216[X]` interpretation is
     `C(pts[i].y.toGF216) · polys[i].toGF216Poly` — and then accumulates this scaled
     contribution into `out` via `add_assign`, which at the polynomial level satisfies
     `out'.toGF216Poly = out.toGF216Poly + C(pts[i].y.toGF216) · polys[i].toGF216Poly`.

After all iterations, the accumulator holds the full Lagrange sum:
  `out.toGF216Poly =
      ∑ j ∈ Finset.range pts.len(),
        C ((pts[j]!).y.toGF216) * (polys[j]!).toGF216Poly`
in `GF216[X] = (GaloisField 2 16)[X]`.

**Loop invariant**: after processing iterations up to index `i`, the accumulator satisfies:
  * `iter.«end» = iter₀.«end»` — the range end is unchanged throughout the loop.
  * `iter₀.start.val ≤ iter.start.val` — the iterator position only increases.
  * `iter.start.val ≤ max iter₀.start.val iter₀.«end».val` — the iterator stays within the
    original bounds.
  * `out.coefficients.val.length ≤ M` — the running accumulator's coefficient-vector length is
    uniformly bounded by `M`, ensuring the combined-length precondition of `add_assign` is
    dischargeable at every iteration.
  * `out.toGF216Poly =
        ∑ j ∈ Finset.range iter.start.val,
          C ((pts[j]!).y.toGF216) * (polys[j]!).toGF216Poly` —
    the accumulator holds the partial Lagrange sum of the first `iter.start.val` scaled
    basis polynomials.

Each step extends the partial sum by one additional term via the identity
  `∑ j ∈ range (i + 1), f j = (∑ j ∈ range i, f j) + f i`  (`Finset.sum_range_succ`)
applied to `f j = C(pts[j].y.toGF216) * polys[j].toGF216Poly`.  At loop termination, the complete
sum gives the Lagrange linear combination
  `Σ_{i < pts.len()} C(pts[i].y.toGF216) · polys[i].toGF216Poly`
in `GF216[X]`.

The preconditions are exactly the loop invariants maintained by the surrounding
`for i in 0..pts.len()` Rust loop, together with the length bounds inherited from
`mult_assign_spec` and `add_assign_spec`:

  * `h_end_le_pts`: `iter.«end».val ≤ pts.val.length` — the range end does not exceed the
    points slice length, so each `pts[i]` read is in range.
  * `h_end_le_polys`: `iter.«end».val ≤ polys.val.length` — the range end does not exceed the
    basis-polynomials slice length, so each `polys[i]` read is in range.
  * `h_polys_M`: every basis polynomial `polys[i]` has coefficient-vector length ≤ `M`.
  * `h_out_M`: the initial accumulator `out` has coefficient-vector length ≤ `M`.
  * `h_M_bound`: `M + M ≤ Usize.max` — bounding `M` so that the combined length of any two
    bounded coefficient vectors fits in `Usize`, and a fortiori so that the stride-of-two
    `parallel_mult` precondition `length + 2 ≤ Usize.max` of `mult_assign` is satisfied.
  * `h_sum`: the partial-sum invariant holds for the initial `out`.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the
16-bit encodings:
  `a + b = a − b = a ⊕ b`,
and multiplication is carry-less polynomial multiplication modulo the irreducible polynomial
`x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 279:8-283:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly.lagrange_sum_loop

/-! ## Helper lemma for the partial-sum invariant -/

/--
**Partial-sum extension.**

Adding one more scaled basis polynomial to a partial Lagrange sum over `Finset.range n` yields the
partial sum over `Finset.range (n + 1)`.  This is the key identity for the accumulation loop
invariant:
  `(∑ j ∈ Finset.range n, f j) + f n = ∑ j ∈ Finset.range (n + 1), f j`
where `f j = C ((pts[j]!).y.toGF216) * (polys[j]!).toGF216Poly` is the `j`-th Lagrange term in
`GF216[X]`.

This is a direct consequence of `Finset.sum_range_succ` from Mathlib.  The wrapper is provided for
readability and to fix the summand to the specific scaled-basis-polynomial form used in the loop
invariant.
-/
private lemma partial_sum_step
    (pts : List spqr.encoding.polynomial.Pt)
    (polys : List spqr.encoding.polynomial.Poly)
    (n : Nat) :
    (∑ j ∈ Finset.range n,
      C ((pts[j]!).y.toGF216) * (polys[j]!).toGF216Poly) +
      C ((pts[n]!).y.toGF216) * (polys[n]!).toGF216Poly =
    ∑ j ∈ Finset.range (n + 1),
      C ((pts[j]!).y.toGF216) * (polys[j]!).toGF216Poly :=
  (Finset.sum_range_succ _ _).symm

/--
**Spec theorem for `encoding.polynomial.Poly.lagrange_sum_loop`**:

The full `Poly::lagrange_sum` accumulation loop.  Given a `Range<usize>` iterator, the points
slice `pts`, the parallel basis-polynomials slice `polys`, and an initial accumulator `out`
satisfying the partial-Lagrange-sum invariant
  `out.toGF216Poly =
       ∑ j ∈ Finset.range iter.start.val,
         C ((pts[j]!).y.toGF216) * (polys[j]!).toGF216Poly`,
the loop adds one scaled basis polynomial per iteration until the iterator is exhausted,
returning the completed accumulator `result` satisfying:

• The function always succeeds (no panic) provided the preconditions hold, since the loop body
  (`lagrange_sum_loop.body_spec`) is total when each `polys[i]` admits the GF(2¹⁶) scalar
  multiplication (length `+ 2 ≤ Usize.max`) and the running accumulator's combined length with
  the scaled contribution stays within `Usize.max` — both ensured by the uniform bound `M` and
  the constraint `M + M ≤ Usize.max`.

• **Polynomial-level Lagrange-sum postcondition**:
    `result.toGF216Poly =
         ∑ j ∈ Finset.range (max iter.start.val iter.«end».val),
           C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly`
  The result accumulator holds the Lagrange linear combination of the basis polynomials, scaled
  by the corresponding point y-coordinates, over the appropriate range in
  `GF216[X] = (GaloisField 2 16)[X]`.

  When called from `lagrange_sum` with `iter.start = 0`, `iter.end = pts.len()`,
  `out = Poly::zero(pts.len())`, and the points and basis polynomials as supplied, this gives:
    `result.toGF216Poly =
         ∑ j ∈ Finset.range (pts.val.length),
           C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly`
  which is exactly the GF(2¹⁶)[X] Lagrange interpolation linear combination used to assemble
  the interpolating polynomial of `lagrange_polynomial_from_complete_points`.

**Source**: spqr/src/encoding/polynomial.rs (lines 279:8-283:9)
-/
@[step]
theorem loop_spec
    (pts : Slice spqr.encoding.polynomial.Pt)
    (polys : Slice spqr.encoding.polynomial.Poly)
    (iter : core.ops.range.Range Std.Usize)
    (out : encoding.polynomial.Poly)
    (h_end_le_pts : iter.«end».val ≤ pts.val.length)
    (h_end_le_polys : iter.«end».val ≤ polys.val.length)
    (h_out : out.coefficients.val.length < Usize.max)
    (h_polys : ∀ i, i < iter.«end».val →
        (polys.val[i]!).coefficients.val.length + 2 ≤  Usize.max)
    (h_sum : out.toGF216Poly = ∑ j ∈ Finset.range iter.start.val,
      C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly) :
    lagrange_sum_loop iter pts polys out
      ⦃ (result : encoding.polynomial.Poly) =>
        result.toGF216Poly = ∑ j ∈ Finset.range (max iter.start.val iter.«end».val),
          C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly ⦄ := by
  unfold lagrange_sum_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                        encoding.polynomial.Poly) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                      encoding.polynomial.Poly) =>
        p.1.«end» = iter.«end» ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ max iter.start.val iter.«end».val ∧
        p.2.coefficients.val.length < Usize.max ∧
        p.2.toGF216Poly = ∑ j ∈ Finset.range p.1.start.val,
          C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly)
  · -- Body step: prove invariant is preserved and measure decreases
    rintro ⟨iter', out'⟩
      ⟨h_end', h_start_le', h_bound', h_out_M', h_sum'⟩
    simp only [] at h_end' h_start_le' h_bound' h_out_M' h_sum' ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    -- Discharge body-spec preconditions from the invariant and the uniform bound `M`.
    have h_end_le_pts' : iter'.«end».val ≤ pts.val.length := by omega
    have h_end_le_polys' : iter'.«end».val ≤ polys.val.length := by omega
    -- The uniform bound `h_polys` ranges over all `i < iter.«end».val`.  Since
    -- `iter'.«end» = iter.«end»`, whenever the body requests the precondition
    -- (under `iter'.start.val < iter'.«end».val`) we can supply it directly.
    have h_poly_len' : ∀ (_hi : iter'.start.val < iter'.«end».val),
        (polys.val[iter'.start.val]!).coefficients.val.length + 2 ≤ Usize.max := by
      intro hi
      exact h_polys iter'.start.val (by rw [h_end'] at hi; exact hi)

    have h_max_len' : ∀ (_hi : iter'.start.val < iter'.«end».val),
        max out'.coefficients.val.length
          (polys.val[iter'.start.val]!).coefficients.val.length < Usize.max := by
      intro hi
      have := h_polys iter'.start.val (by rw [h_end'] at hi; exact hi)
      grind
    -- Apply the body spec from LagrangeSumLoopBody0
    have h_body := body_spec pts polys iter' out'
      h_end_le_pts' h_end_le_polys' h_poly_len' h_max_len'
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done result =>
      -- Done case: iterator exhausted, result = out'
      simp only [] at h_cf ⊢
      obtain ⟨h_eq, h_not_lt⟩ := h_cf
      subst h_eq
      push Not at h_not_lt
      rw [h_end'] at h_not_lt
      -- max iter.start.val iter.«end».val = iter'.start.val
      have h_max_eq : max iter.start.val iter.«end».val = iter'.start.val :=
        Nat.le_antisymm (max_le h_start_le' h_not_lt) h_bound'
      rw [h_max_eq]
      exact h_sum'
    | ControlFlow.cont (iter1, out1) =>
      -- Cont case: one more scaled basis polynomial accumulated
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, h_len1, h_out1⟩ := h_cf
      -- In the cont branch the iterator must have actually advanced, so
      -- `iter'.start.val < iter'.«end».val = iter.«end».val ≤ polys.val.length`.
      have h_i_lt_polys : iter'.start.val < polys.val.length := by omega
      have h_i_lt_end : iter'.start.val < iter.«end».val := by
        rw [← h_end']; omega
      have h_polys_le := h_polys iter'.start.val h_i_lt_end
      constructor
      · -- Invariant preserved (5 conjuncts)
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · -- iter1.end = iter.end
          rw [h_end1, h_end']
        · -- iter.start ≤ iter1.start
          rw [h_start1]; omega
        · -- iter1.start ≤ max(iter.start, iter.end)
          rw [h_start1]
          have h_lt_end : iter'.start.val + 1 ≤ iter.«end».val := by omega
          have := le_max_right iter.start.val iter.«end».val
          omega
        · -- out1.coefficients.val.length ≤ M
          -- The body's strengthened length post-condition gives
          --   `out1.length = max out'.length (polys[i]).length`,
          -- and both factors are bounded by M (`h_out_M'`, `h_polys_le`).
          rw [h_len1]
          grind
        · -- Partial-Lagrange-sum invariant preserved
          rw [h_out1, h_sum', h_start1]
          exact partial_sum_step pts.val polys.val iter'.start.val
      · -- Measure decreases
        rw [h_start1, h_end1]
        omega
  · -- Initial invariant
    exact ⟨rfl, le_refl _, le_max_left _ _, h_out, h_sum⟩

end spqr.encoding.polynomial.Poly.lagrange_sum_loop
