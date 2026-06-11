/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.Poly.Zero
import Spqr.Specs.Encoding.Polynomial.Poly.AddAssign
import Spqr.Specs.Encoding.Polynomial.Poly.MultAssign
import Spqr.Specs.Encoding.Polynomial.Poly.Clone
import Spqr.Specs.Aeneas.RangeIteratorNext

/-!
# Spec theorem for `Poly::lagrange_sum`: loop body 0

The Rust function `Poly::lagrange_sum`  is the internal helper used by
`lagrange_polynomial_from_complete_points`.  Given a list of points`pts : &[Pt]` together with
a parallel list of "basis" polynomials `polys : &[Poly]` (one polynomial per point), it forms
the GF(2¹⁶)[X] linear combination

  `out = Σ_{i = 0}^{pts.len() − 1} pts[i].y · polys[i]`

by initialising `out` to the zero polynomial of length `pts.len()`.


The invariant maintained by loop is that after processing iterations up to index `i`, the
accumulator satisfies:
  `out.toGF216Poly = Σ_{j < iter.start.val} C(pts[j].y.toGF216) · polys[j].toGF216Poly`
Each step extends this partial sum by one additional term:
  `out'.toGF216Poly = out.toGF216Poly + C(pts[i].y.toGF216) · polys[i].toGF216Poly`

At loop termination, the complete sum gives the Lagrange linear combination
`Σ_{i < pts.len()} C(pts[i].y) · polys[i]` in `GF216[X] = (GaloisField 2 16)[X]`.

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

/--
**Spec theorem for `encoding.polynomial.Poly.lagrange_sum_loop.body`**:

One step of the `Poly::lagrange_sum` accumulation loop.  Given the slices `pts` and `polys` (the
points and their associated basis polynomials), a range iterator over the remaining indices, and
the current accumulator polynomial `out`, the body retrieves the next index `i` from the iterator
and either terminates or extends the partial Lagrange sum:

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end does not exceed either slice's length, ensuring that `Slice.index_usize` reads at position
  `i` are within bounds for both `pts` and `polys`; the coefficient vector of the basis polynomial
  `polys[i]` admits the GF(2¹⁶) scalar multiplication
  (`polys[i].coefficients.val.length + 2 ≤ Usize.max`, matching the precondition of
  `mult_assign_spec`); and the combined length of `out` and the scaled contribution stays within
  `Usize.max` so that the in-place addition cannot overflow (matching the precondition of
  `add_assign_spec`).

• In the **done** case (iterator exhausted):
    the accumulator `out` is returned unchanged, and the iterator
    condition is negated: `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by exactly one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The accumulator is updated by one additional Lagrange term in
      `GF216[X] = (GaloisField 2 16)[X]`:
        `out1.toGF216Poly =
            out.toGF216Poly +
            C ((pts.val[iter.start.val]!).y.toGF216) *
              (polys.val[iter.start.val]!).toGF216Poly`
      where `C : GF216 →+* GF216[X]` is the constant-polynomial
      embedding, `toGF216Poly : Poly → GF216Poly` interprets the
      coefficient vector as a polynomial in `GF216[X]`, and the `+`
      and `*` on the right-hand side are polynomial addition and
      multiplication in `GF216[X]` (with addition coinciding with
      subtraction in characteristic 2, i.e. coefficient-wise XOR).

    Under the loop invariant
      `out.toGF216Poly =
          Σ_{j < iter.start.val} C(pts[j].y.toGF216) · polys[j].toGF216Poly`,
    this gives
      `out1.toGF216Poly =
          Σ_{j ≤ iter.start.val} C(pts[j].y.toGF216) · polys[j].toGF216Poly`,
    extending the partial Lagrange-sum invariant by one term.

**Source**: spqr/src/encoding/polynomial.rs (lines 279:8-283:9)
-/
@[step]
theorem body_spec
    (pts : Slice Pt)
    (polys : Slice Poly)
    (iter : core.ops.range.Range Usize)
    (out : Poly)
    (h_end_le_pts : iter.«end».val ≤ pts.val.length)
    (h_end_le_polys : iter.«end».val ≤ polys.val.length)
    (h_poly_len : ∀ (_hi : iter.start.val < iter.«end».val),
        (polys.val[iter.start.val]!).coefficients.val.length + 2 ≤ Usize.max)
    (h_max_len : ∀ (_hi : iter.start.val < iter.«end».val),
        max out.coefficients.val.length
          (polys.val[iter.start.val]!).coefficients.val.length < Usize.max) :
    body pts polys iter out ⦃ cf =>
      match cf with
      | ControlFlow.done out' =>
          out' = out ∧ ¬ (iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, out1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          out1.coefficients.val.length =
            max out.coefficients.val.length
                (polys.val[iter.start.val]!).coefficients.val.length ∧
          out1.toGF216Poly =
            out.toGF216Poly +
            C ((pts.val[iter.start.val]!).y.toGF216) *
              (polys.val[iter.start.val]!).toGF216Poly ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_pts : iter.start.val < pts.val.length := by omega
    have h_i_lt_polys : iter.start.val < polys.val.length := by omega
    have h_p_len := h_poly_len h_lt
    have h_a_len := h_max_len h_lt
    step*
    · grind
    · grind
    · grind
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.Poly.lagrange_sum_loop

/-!
# Spec theorem for `Poly::lagrange_sum`: loop 0

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

**Source**: spqr/src/encoding/polynomial.rs (lines 279:8-283:9)
-/


namespace spqr.encoding.polynomial.Poly.lagrange_sum_loop

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
    (pts : Slice Pt)
    (polys : Slice Poly)
    (iter : core.ops.range.Range Usize)
    (out : Poly)
    (h_end_le_pts : iter.«end».val ≤ pts.val.length)
    (h_end_le_polys : iter.«end».val ≤ polys.val.length)
    (h_out : out.coefficients.val.length < Usize.max)
    (h_polys : ∀ i, i < iter.«end».val →
        (polys.val[i]!).coefficients.val.length + 2 ≤  Usize.max)
    (h_sum : out.toGF216Poly = ∑ j ∈ Finset.range iter.start.val,
      C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly) :
    lagrange_sum_loop iter pts polys out
      ⦃ (result : Poly) =>
        result.toGF216Poly = ∑ j ∈ Finset.range (max iter.start.val iter.«end».val),
          C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly ⦄ := by
  unfold lagrange_sum_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize ×
                        Poly) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize ×
                      Poly) =>
        p.1.«end» = iter.«end» ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ max iter.start.val iter.«end».val ∧
        p.2.coefficients.val.length < Usize.max ∧
        p.2.toGF216Poly = ∑ j ∈ Finset.range p.1.start.val,
          C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly)
  · rintro ⟨iter', out'⟩
      ⟨h_end', h_start_le', h_bound', h_out_M', h_sum'⟩
    simp only [] at h_end' h_start_le' h_bound' h_out_M' h_sum' ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_end_le_pts' : iter'.«end».val ≤ pts.val.length := by omega
    have h_end_le_polys' : iter'.«end».val ≤ polys.val.length := by omega
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
    have h_body := body_spec pts polys iter' out'
      h_end_le_pts' h_end_le_polys' h_poly_len' h_max_len'
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done result =>
      simp only [] at h_cf ⊢
      obtain ⟨h_eq, h_not_lt⟩ := h_cf
      subst h_eq
      push Not at h_not_lt
      rw [h_end'] at h_not_lt
      have h_max_eq : max iter.start.val iter.«end».val = iter'.start.val :=
        Nat.le_antisymm (max_le h_start_le' h_not_lt) h_bound'
      rw [h_max_eq]
      exact h_sum'
    | ControlFlow.cont (iter1, out1) =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, h_len1, h_out1⟩ := h_cf
      have h_i_lt_polys : iter'.start.val < polys.val.length := by omega
      have h_i_lt_end : iter'.start.val < iter.«end».val := by
        rw [← h_end']; omega
      have h_polys_le := h_polys iter'.start.val h_i_lt_end
      constructor
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [h_end1, h_end']
        · rw [h_start1]; omega
        · rw [h_start1]
          have h_lt_end : iter'.start.val + 1 ≤ iter.«end».val := by omega
          have := le_max_right iter.start.val iter.«end».val
          omega
        · rw [h_len1]
          grind
        · rw [h_out1, h_sum', h_start1]
          apply (Finset.sum_range_succ _ _).symm
      · rw [h_start1, h_end1]
        omega
  · exact ⟨rfl, le_refl _, le_max_left _ _, h_out, h_sum⟩

end spqr.encoding.polynomial.Poly.lagrange_sum_loop

/-!
# Spec theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::lagrange_sum`


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
the combined coefficient length to fit in `Usize`, see `AddAssign.add_assign_spec`).

**Source**: spqr/src/encoding/polynomial.rs (lines 277:4-285:5)
-/

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
  step with zero_spec (Slice.len pts) as ⟨out, h_out_len, h_out_zero⟩
  have h_end_le_pts : (Slice.len pts).val ≤ pts.val.length := by simp
  have h_end_le_polys : (Slice.len pts).val ≤ polys.val.length := by
    grind
  have h_out : out.coefficients.val.length < Usize.max := by
    rw [h_out_len]
    grind
  have h_polys' : ∀ i, i < (Slice.len pts).val →
      (polys.val[i]!).coefficients.val.length + 2 ≤ Usize.max := by
    intro i hi
    apply h_polys i
    simpa using hi
  have h_sum_init :
      out.toGF216Poly = ∑ j ∈ Finset.range (0#usize).val,
        C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly := by
    rw [h_out_zero]; simp
  apply WP.spec_mono (lagrange_sum_loop.loop_spec pts polys
    { start := 0#usize, «end» := Slice.len pts } out
    h_end_le_pts h_end_le_polys h_out h_polys' h_sum_init)
  intro result h_result
  have h_max : max (0#usize).val (Slice.len pts).val = pts.val.length := by simp
  rw [h_max] at h_result
  exact h_result

end spqr.encoding.polynomial.Poly
