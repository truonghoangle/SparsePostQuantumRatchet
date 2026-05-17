/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.Poly.AddAssign
import Spqr.Specs.Encoding.Polynomial.Poly.MultAssign
import Spqr.Specs.Encoding.Polynomial.Poly.Clone

/-!
# Spec theorem for `Poly::lagrange_sum`: loop body 0

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

This file specifies the **loop body** — a single step of the above iteration.  The extracted Lean
function `encoding.polynomial.Poly.lagrange_sum_loop.body` performs one step: it calls `next` on the
`Range<usize>` iterator and either:

  1. **Done** (`none`): the iterator is exhausted, and the accumulator polynomial `out` is returned
     unchanged.
  2. **Continue** (`some i`): retrieves `p = polys[i]` via `Slice.index_usize`, clones it into a
     fresh scratch polynomial `p1` (the derived `Clone::clone` is observationally the identity on
     `Poly`, see `Clone.clone_spec`), retrieves the point `p2 = pts[i]`, scales the scratch
     polynomial in place via `p3 = p1.mult_assign(p2.y)` — which performs GF(2¹⁶) coefficient-wise
     scalar multiplication and at the polynomial level satisfies
     `p3.toGF216Poly = C(p2.y.toGF216) · p1.toGF216Poly` (see `MultAssign.mult_assign_spec`) — and
     finally accumulates the scaled contribution into `out` via `out1 = out.add_assign(p3)`, which
     at the polynomial level satisfies `out1.toGF216Poly = out.toGF216Poly + p3.toGF216Poly` (see
     `AddAssign.add_assign_spec`).

The invariant maintained by this loop is that after processing iterations up to index `i`, the
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


instance : Inhabited spqr.encoding.polynomial.Pt :=
  ⟨{ x := default, y := default }⟩

instance : Inhabited spqr.encoding.polynomial.Poly :=
  ⟨{ coefficients := alloc.vec.Vec.new _ }⟩

-- The long identifier cannot be broken across lines; suppress
-- the line-length linter for the lemma statement and proof.
/--
The range iterator `next` always returns `ok` and either provides the current `start` value (when
`start < end`) or `none` (when `start ≥ end`).  This is the concrete specification for the
`core.ops.range.Range<usize>` iterator used in the Rust `for i in 0..pts.len()` loop.
-/
private lemma IteratorRange_next_Usize_post
    (range : core.ops.range.Range Std.Usize) :
    ∃ opt range',
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range
        = ok (opt, range') ∧
      (¬ range.start.val < range.«end».val →
          opt = none ∧ range' = range) ∧
      (range.start.val < range.«end».val →
          opt = some range.start ∧
          range'.start.val = range.start.val + 1 ∧
          range'.«end» = range.«end») := by
  simp only [core.iter.range.IteratorRange.next]
  simp only [liftFun2, liftFun1, core.clone.impls.CloneUsize.clone, bind_tc_ok, not_lt]
  have h_lt_iff :
      (core.cmp.impls.PartialOrdUsize.lt range.start range.«end» = true) =
      (range.start.val < range.«end».val) := by
    simp [core.cmp.impls.PartialOrdUsize.lt]
  simp only [h_lt_iff]
  by_cases hlt : range.start.val < range.«end».val
  · rw [if_pos hlt]
    have hbound : range.start.val + 1 ≤ Usize.max := by
      have := range.«end».hBounds; scalar_tac
    refine ⟨some range.start,
            {range with start := ⟨range.start.val + 1, by scalar_tac⟩},
            ?_, ?_, ?_⟩
    · simp only [core.iter.range.StepUsize.forward_checked, bind_tc_ok]
      have hca := Usize.checked_add_bv_spec range.start 1#usize
      rcases heq : Usize.checked_add range.start 1#usize with _ | z
      · rw [heq] at hca; scalar_tac
      · simp only
        rw [heq] at hca
        obtain ⟨_, hval, _⟩ := hca
        have hzval : z.val = range.start.val + 1 := by scalar_tac
        congr 4
        exact UScalar.eq_of_val_eq hzval
    · intro h; omega
    · intro _; exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hlt]
    exact ⟨none, range, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd h hlt⟩

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

The preconditions are exactly the loop invariants maintained by the surrounding `for i in
0..pts.len()` Rust loop together with the length bounds inherited from `mult_assign` and
`add_assign`:

* `iter.«end».val ≤ pts.val.length` — the range end does not exceed
  the points slice length, so `pts[i]` is always a valid read.
* `iter.«end».val ≤ polys.val.length` — the range end does not
  exceed the basis-polynomials slice length, so `polys[i]` is always
  a valid read.
* `(polys.val[iter.start.val]!).coefficients.val.length + 2 ≤ Usize.max`
  — the basis polynomial at the current index admits the GF(2¹⁶)
  stride-of-two scalar multiplication used by `parallel_mult`.
* `out.coefficients.val.length +
    (polys.val[iter.start.val]!).coefficients.val.length ≤ Usize.max`
  — the in-place polynomial addition can accommodate the combined
  length of the running accumulator and the scaled contribution
  without overflowing the underlying `Vec`.

**Source**: spqr/src/encoding/polynomial.rs (lines 279:8-283:9)
-/
@[step]
theorem body_spec
    (pts : Slice spqr.encoding.polynomial.Pt)
    (polys : Slice spqr.encoding.polynomial.Poly)
    (iter : core.ops.range.Range Std.Usize)
    (out : encoding.polynomial.Poly)
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
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := IteratorRange_next_Usize_post iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · -- Continue case: iterator yields some i = iter.start
    obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    -- Key index bounds from the preconditions
    have h_i_lt_pts : iter.start.val < pts.val.length := by omega
    have h_i_lt_polys : iter.start.val < polys.val.length := by omega
    have h_p_len := h_poly_len h_lt
    have h_a_len := h_max_len h_lt
    -- Step through indexing, clone, indexing, mult_assign, and add_assign
    step*
  · -- Done case: iterator exhausted
    obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.Poly.lagrange_sum_loop
