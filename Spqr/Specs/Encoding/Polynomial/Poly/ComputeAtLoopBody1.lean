/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.GF16.Mul
import Spqr.Specs.Encoding.Gf.GF16.AddAssign

/-!
# Spec theorem for `Poly::compute_at`: loop body 1

The extracted Lean function `encoding.polynomial.Poly.compute_at_loop1.body` performs one step: 
it calls `next` on the `Range<usize>` iterator and either:

  1. **Done** (`none`): the iterator is exhausted, and the accumulator `out` is returned unchanged.
  2. **Continue** (`some i`): retrieves the coefficient `g = v[i]` and the power `g1 = xs[i]`,
     computes their GF(2¹⁶) product `g2 = g * g1`, and adds it to the accumulator via
     `out += g2`.

The invariant maintained by this loop is that after processing iterations up to index `i`, the
accumulator satisfies:
  `out.toGF216 = Σ_{j < iter.start.val} (v[j].toGF216 * xs[j].toGF216)`
Each step extends this partial sum by one additional term:
  `out' = out + v[i] * xs[i]`

When the power-vector invariant `xs[j].toGF216 = x.toGF216 ^ j` holds (established by loop 0), the
partial sum equals `Σ_{j < i} coeff[j] * x^j`, i.e. the polynomial evaluation up to the `i`-th
term.  At loop termination, the complete sum gives `p(x) = Σ_{j=0}^{n-1} coeff[j] * x^j`.

In GF(2¹⁶), multiplication is carry-less polynomial multiplication modulo the irreducible polynomial
`x¹⁶ + x¹² + x³ + x + 1` (0x1100b), and addition is bitwise XOR.

**Source**: spqr/src/encoding/polynomial.rs (lines 269:8-271:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly.compute_at_loop1

-- The long identifier cannot be broken across lines; suppress
-- the line-length linter for the lemma statement and proof.
/--
The range iterator `next` always returns `ok` and either provides the current `start` value (when
`start < end`) or `none` (when `start ≥ end`).  This is the concrete specification for the
`core.ops.range.Range<usize>` iterator used in the Rust `for i in 0..self.coefficients.len()` loop.
-/
private lemma IteratorRange_next_Usize_post
    (range : core.ops.range.Range Usize) :
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
**Spec theorem for `encoding.polynomial.Poly.compute_at_loop1.body`**:

One step of the `Poly::compute_at` accumulation loop.  Given a range iterator, the coefficient
vector `v`, the power vector `xs`, and the current accumulator `out`, the body retrieves the next
index `i` from the iterator and either terminates or extends the partial sum:

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end does not exceed either vector's length, ensuring that the vector indexing at position `i`
  is within bounds for both `v` and `xs`.

• In the **done** case (iterator exhausted):
    the accumulator `out` is returned unchanged, and the iterator condition is negated:
    `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The accumulator is updated by one additional term:
        `out1.toGF216 = out.toGF216 +
          (v.val[iter.start.val]!).toGF216 *
          (xs.val[iter.start.val]!).toGF216`
      where `v[i]` is the `i`-th coefficient and `xs[i]` is the `i`-th power of `x`.

    Under the loop invariant `out.toGF216 = Σ_{j < iter.start.val} v[j].toGF216 * xs[j].toGF216`,
    this gives `out1.toGF216 = Σ_{j ≤ iter.start.val} v[j].toGF216 * xs[j].toGF216`, extending the
    partial-sum invariant by one term.

The preconditions are exactly the loop invariants maintained by the surrounding `for i in
0..self.coefficients.len()` Rust loop:

* `iter.«end».val ≤ v.val.length` — the range end does not exceed the
  coefficient vector length.
* `iter.«end».val ≤ xs.val.length` — the range end does not exceed the
  power vector length.

**Source**: spqr/src/encoding/polynomial.rs (lines 269:8-271:9)
-/
@[step]
theorem body_spec
    (v : alloc.vec.Vec GF16)
    (xs : alloc.vec.Vec GF16)
    (iter : core.ops.range.Range Usize)
    (out : GF16)
    (h_v_len : iter.«end».val ≤ v.val.length)
    (h_xs_len : iter.«end».val ≤ xs.val.length) :
    body v xs iter out ⦃ cf =>
      match cf with
      | ControlFlow.done out' =>
          out' = out ∧ ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, out1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          out1.toGF216 = out.toGF216 +
            (v.val[iter.start.val]!).toGF216 *
            (xs.val[iter.start.val]!).toGF216 ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := IteratorRange_next_Usize_post iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_v : iter.start.val < v.val.length := by omega
    have h_i_lt_xs : iter.start.val < xs.val.length := by omega
    step*
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.Poly.compute_at_loop1
