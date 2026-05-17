/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Poly.ComputeAtLoopBody1

/-!
# Spec theorem for `Poly::compute_at`: loop 1

The loop consumes the `Range<usize>` iterator from `0` to
`self.coefficients.len()`, adding one coefficient–power product to the accumulator per iteration
until the iterator is exhausted.  At each step:

  1. The iterator yields the next index `i` (starting from 0).
  2. The body retrieves the coefficient `g = v[i]` and the power `g1 = xs[i]`, computes their
     GF(2¹⁶) product `g2 = g * g1`, and adds it to the accumulator via `out += g2`.

After all iterations, the accumulator holds the full dot product:
  `out.toGF216 = ∑ j ∈ Finset.range n, v[j].toGF216 * xs[j].toGF216`

**Loop invariant**: after processing iterations up to index `i`, the accumulator satisfies:
  * `iter.«end» = iter₀.«end»` — the range end is unchanged throughout the loop.
  * `iter₀.start.val ≤ iter.start.val` — the iterator position only increases.
  * `iter.start.val ≤ max iter₀.start.val iter₀.«end».val` — the iterator stays within the
    original bounds.
  * `out.toGF216 = ∑ j ∈ Finset.range iter.start.val, (v[j]!).toGF216 * (xs[j]!).toGF216` —
    the accumulator holds the partial sum of the first `iter.start.val` coefficient–power products.

Each step extends the partial sum by one additional term via the identity:
  `∑ j ∈ range (i + 1), f j = (∑ j ∈ range i, f j) + f i`  (`Finset.sum_range_succ`)

When the power-vector invariant `xs[j].toGF216 = x.toGF216 ^ j` holds (established by loop 0), the
partial sum equals `∑_{j < i} coeff[j] · x^j`, i.e. the polynomial evaluation up to the `i`-th
term.  At loop termination, the complete sum gives `p(x) = ∑_{j=0}^{n−1} coeff[j] · x^j`.

The preconditions are exactly the loop invariants maintained by the surrounding
`for i in 0..self.coefficients.len()` Rust loop:

  * `h_v_len`: `iter.«end».val ≤ v.val.length` — the range end does not exceed the coefficient
    vector length.
  * `h_xs_len`: `iter.«end».val ≤ xs.val.length` — the range end does not exceed the power vector
    length.
  * `h_sum`: the partial-sum invariant holds for the initial `out`.

In GF(2¹⁶), multiplication is carry-less polynomial multiplication modulo the irreducible polynomial
`x¹⁶ + x¹² + x³ + x + 1` (0x1100b), and addition is bitwise XOR.

**Source**: spqr/src/encoding/polynomial.rs (lines 269:8-271:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly.compute_at_loop1

/--
**Spec theorem for `encoding.polynomial.Poly.compute_at_loop1`**:

The full `Poly::compute_at` accumulation loop.  Given a `Range<usize>` iterator, the coefficient
vector `v`, the power vector `xs`, and an initial accumulator `out` satisfying the partial-sum
invariant `out.toGF216 = ∑ j ∈ Finset.range iter.start.val, v[j].toGF216 * xs[j].toGF216`, the loop
adds one coefficient–power product per iteration until the iterator is exhausted, returning the
completed accumulator `result` satisfying:

• The function always succeeds (no panic) provided the preconditions hold, since the loop body
  (`compute_at_loop1.body_spec`) is total when the vector indices are within bounds.

• **Dot-product postcondition**:
    `result.toGF216 = ∑ j ∈ Finset.range (max iter.start.val iter.«end».val),
        (v.val[j]!).toGF216 * (xs.val[j]!).toGF216`
  The result accumulator holds the dot product of the coefficient and power vectors over the
  appropriate range in `GF216 = GaloisField 2 16`.

  When called from `compute_at` with `iter.start = 0`, `iter.end = self.coefficients.len()`,
  `out = GF16::ZERO`, `v = self.coefficients`, and `xs` the power vector from loop 0, this gives:
    `result.toGF216 = ∑ j ∈ Finset.range (self.coefficients.len()),
        (self.coefficients[j]!).toGF216 * (xs[j]!).toGF216`
  which, combined with the power-vector invariant `xs[j].toGF216 = x.toGF216 ^ j`, yields the
  polynomial evaluation `p(x) = ∑_{j=0}^{n−1} coeff[j] · x^j`.

**Source**: spqr/src/encoding/polynomial.rs (lines 269:8-271:9)
-/
@[step]
theorem loop_spec
    (v : alloc.vec.Vec GF16)
    (xs : alloc.vec.Vec GF16)
    (iter : core.ops.range.Range Usize)
    (out : GF16)
    (h_v_len : iter.«end».val ≤ v.val.length)
    (h_xs_len : iter.«end».val ≤ xs.val.length)
    (h_sum : out.toGF216 = ∑ j ∈ Finset.range iter.start.val,
      (v.val[j]!).toGF216 * (xs.val[j]!).toGF216) :
    compute_at_loop1 iter v xs out
      ⦃ (result : GF16) =>
        result.toGF216 = ∑ j ∈ Finset.range (max iter.start.val iter.«end».val),
          (v.val[j]!).toGF216 * (xs.val[j]!).toGF216 ⦄ := by
  unfold compute_at_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × GF16) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize × GF16) =>
        p.1.«end» = iter.«end» ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ max iter.start.val iter.«end».val ∧
        p.2.toGF216 = ∑ j ∈ Finset.range p.1.start.val,
          (v.val[j]!).toGF216 * (xs.val[j]!).toGF216)
  · rintro ⟨iter', out'⟩
      ⟨h_end', h_start_le', h_bound', h_sum'⟩
    simp only [] at h_end' h_start_le' h_bound' h_sum' ⊢
    have h_body := body_spec v xs iter' out'
      (by rw [h_end']; exact h_v_len) (by rw [h_end']; exact h_xs_len)
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
      obtain ⟨h_lt, h_start1, h_end1, h_out1⟩ := h_cf
      constructor
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h_end1, h_end']
        · rw [h_start1]; omega
        · rw [h_start1]
          have h_lt_end : iter'.start.val + 1 ≤ iter.«end».val := by
            have : iter'.«end».val = iter.«end».val := by rw [h_end']
            omega
          have := le_max_right iter.start.val iter.«end».val
          omega
        · rw [h_out1, h_sum', h_start1]
          apply (Finset.sum_range_succ _ _).symm
      · rw [h_start1, h_end1]
        have : iter'.«end».val = iter.«end».val := by rw [h_end']
        omega
  · exact ⟨rfl, le_refl _, le_max_left _ _, h_sum⟩

end spqr.encoding.polynomial.Poly.compute_at_loop1
