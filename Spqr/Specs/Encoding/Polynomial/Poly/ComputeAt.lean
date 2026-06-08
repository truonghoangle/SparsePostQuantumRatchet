/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
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
import Spqr.Math.Poly.Aeneas.DotProduct
import Spqr.Math.Poly.Aeneas.PowerVector
import Spqr.Math.Poly.Mathlib
import Spqr.Specs.Encoding.Gf.GF16.Mul
import Spqr.Specs.Encoding.Gf.GF16.AddAssign
import Spqr.Specs.Aeneas.RangeIteratorNext

/-!
# Spec theorem for `Poly::compute_at`: loop body 0

The extracted Lean function `encoding.polynomial.Poly.compute_at_loop0.body` performs one step:
it calls `next` on the `Range<usize>` iterator and either:

  1. **Done** (`none`): the iterator is exhausted, and the vector `xs` is returned unchanged.
  2. **Continue** (`some i`): retrieves `a = xs[i / 2]` and `b = xs[i / 2 + i % 2]`, computes
     their GF(2¹⁶) product `g = a * b`, and appends `g` to `xs` via `Vec::push`.

The invariant maintained by this loop is that `xs[j].toGF216 = x.toGF216 ^ j` for all
`j < xs.length`, and `xs.length = i`.  The body step exploits the identity:
  `x^i = x^(i/2) · x^(i/2 + i%2)`
which holds because `i/2 + (i/2 + i%2) = i` for all natural numbers `i`:

  * When `i` is even: `x^i = (x^(i/2))²`.
  * When `i` is odd:  `x^i = x^((i−1)/2) · x^((i+1)/2)`.

In GF(2¹⁶), multiplication is carry-less polynomial multiplication modulo the irreducible polynomial
`x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 260:8-265:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly.compute_at_loop0


/--
**Spec theorem for `encoding.polynomial.Poly.compute_at_loop0.body`**:

One step of the `Poly::compute_at` power-vector construction loop.  Given a range iterator and the
current power vector `xs`, the body retrieves the next index `i` from the iterator and either
terminates or extends `xs`:

• The function always succeeds (no panic) provided the preconditions hold: the loop invariant
  `iter.start.val = xs.val.length` with `iter.start.val ≥ 2` ensures that the vector indexing at
  positions `i / 2` and `i / 2 + i % 2` is within bounds (since both indices are strictly less than
  `xs.length` when `xs.length ≥ 2`), and `xs.val.length + 1 ≤ Usize.max` ensures that `Vec::push`
  can accommodate the new element.

• In the **done** case (iterator exhausted):
    the vector `xs` is returned unchanged, and the iterator condition is negated:
    `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The vector is extended by exactly one element:
        `xs1.val = xs.val ++ [g]`
      where `g : GF16` is the GF(2¹⁶) product of the elements at positions `xs.length / 2`
      and `xs.length / 2 + xs.length % 2`:
        `g.toGF216 = (xs.val[xs.val.length / 2]!).toGF216 *
                     (xs.val[xs.val.length / 2 + xs.val.length % 2]!).toGF216`

    Under the loop invariant `xs[j].toGF216 = x.toGF216 ^ j` for all `j < xs.length`, this gives
    `g.toGF216 = x.toGF216 ^ (xs.length / 2) * x.toGF216 ^ (xs.length / 2 + xs.length % 2)
               = x.toGF216 ^ xs.length`, extending the power-vector invariant by one position.

The preconditions are exactly the loop invariants maintained by the surrounding `for i in
2..self.coefficients.len()` Rust loop:

* `iter.start.val ≥ 2` — the range starts at 2, and the iterator
  position only increases.
* `iter.start.val = xs.val.length` — the vector length tracks the
  iterator position (the Rust `loop_invariant` annotation).
* `xs.val.length + 1 ≤ Usize.max` — the vector can accommodate
  one more element.

**Source**: spqr/src/encoding/polynomial.rs (lines 260:8-265:9)
-/
@[step]
theorem body_spec
    (iter : core.ops.range.Range Std.Usize)
    (xs : alloc.vec.Vec encoding.gf.GF16)
    (h_ge2 : 2 ≤ iter.start.val)
    (h_inv : iter.start.val = xs.val.length)
    (h_len : xs.val.length + 1 ≤ Usize.max) :
    body iter xs ⦃ cf =>
      match cf with
      | ControlFlow.done xs' =>
          xs' = xs ∧ ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, xs1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          ∃ (g : encoding.gf.GF16),
            xs1.val = xs.val ++ [g] ∧
            g.toGF216 =
              (xs.val[xs.val.length / 2]!).toGF216 *
              (xs.val[xs.val.length / 2 + xs.val.length % 2]!).toGF216 ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_div2_lt : iter.start.val / 2 < xs.val.length := by
      rw [← h_inv]; exact Nat.div_lt_self (by omega) (by omega)
    have h_sum_lt : iter.start.val / 2 + iter.start.val % 2 < xs.val.length := by
      rw [← h_inv];
      grind
    step*
    grind
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.Poly.compute_at_loop0

/-!
# Spec theorem for `Poly::compute_at`: loop 0

The loop consumes the `Range<usize>` iterator from `2` to
`self.coefficients.len()`, extending the power vector `xs` by one element per iteration until the
iterator is exhausted.  At each step:

  1. The iterator yields the next index `i` (starting from 2).
  2. The body retrieves `a = xs[i / 2]` and `b = xs[i / 2 + i % 2]`, computes their GF(2¹⁶)
     product `g = a * b`, and appends `g` to `xs` via `Vec::push`.

After all iterations, the vector `xs` contains `max(initial_length, end)` elements, where each
entry `xs[j]` holds the `j`-th power of `x` in GF(2¹⁶).

**Loop invariant**: after processing iterations up to index `i`, the vector `xs` satisfies:
  * `xs.val.length = iter.start.val` — the vector length tracks the iterator position.
  * `∀ j < xs.val.length, (xs.val[j]!).toGF216 = x.toGF216 ^ j` — each entry `xs[j]` holds the
    `j`-th power of `x` in GF(2¹⁶).

At each step, the body exploits the identity `x^i = x^(i/2) · x^(i/2 + i%2)` to compute the next
power from previously computed powers, extending the invariant by one position:

  * When `i` is even: `x^i = (x^(i/2))²`.
  * When `i` is odd:  `x^i = x^((i−1)/2) · x^((i+1)/2)`.

The preconditions are exactly the loop invariants maintained by the surrounding
`for i in 2..self.coefficients.len()` Rust loop:

  * `h_ge2`: `iter.start.val ≥ 2` — the range starts at 2, and the iterator position only
    increases.
  * `h_inv`: `iter.start.val = xs.val.length` — the vector length tracks the iterator position.
  * `h_pow`: the power-vector invariant holds for the initial `xs`.
  * `h_len`: `max(xs.val.length, iter.end) + 1 ≤ Usize.max` — the vector can accommodate all
    elements up to the maximum length without overflowing.

In GF(2¹⁶), multiplication is carry-less polynomial multiplication modulo the irreducible polynomial
`x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

**Source**: spqr/src/encoding/polynomial.rs (lines 260:8-265:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly.compute_at_loop0


/-! ## Helper lemmas for the power-vector invariant -/

/--
**Spec theorem for `encoding.polynomial.Poly.compute_at_loop0`**:

The full `Poly::compute_at` power-vector construction loop.  Given a `Range<usize>` iterator and an
initial power vector `xs` satisfying `xs[j].toGF216 = x.toGF216 ^ j` for all `j < xs.length`, the
loop extends `xs` by one element per iteration until the iterator is exhausted, returning the
completed power vector `result` satisfying:

• The function always succeeds (no panic) provided the preconditions hold, since the loop body
  (`compute_at_loop0.body_spec`) is total when the vector length stays within `Usize.max`.

• **Power-vector postcondition**:
    `∀ j, j < result.val.length → (result.val[j]!).toGF216 = x.toGF216 ^ j`
  Every entry `result[j]` holds the `j`-th power of `x` in `GF216 = GaloisField 2 16`.

• **Length postcondition**:
    `result.val.length = max xs.val.length iter.«end».val`
  The result vector has exactly `max(initial_length, end)` elements.  When called from `compute_at`
  with `iter.start = 2`, `iter.end = self.coefficients.len()`, and `xs = [GF16::ONE, x]`, this gives
  `result.val.length = max 2 (self.coefficients.len()) = self.coefficients.len()` (assuming the
  polynomial has degree ≥ 1, i.e., at least 2 coefficients).

**Source**: spqr/src/encoding/polynomial.rs (lines 260:8-265:9)
-/
@[step]
theorem loop_spec
    (x : GF16)
    (iter : core.ops.range.Range Usize)
    (xs : alloc.vec.Vec GF16)
    (h_ge2 : 2 ≤ iter.start.val)
    (h_inv : iter.start.val = xs.val.length)
    (h_pow : ∀ j, j < xs.val.length → (xs.val[j]!).toGF216 = x.toGF216 ^ j)
    (h_len : max xs.val.length iter.«end».val + 1 ≤ Usize.max) :
    compute_at_loop0 iter xs
      ⦃ (result : alloc.vec.Vec GF16) =>
        (∀ j, j < result.val.length → (result.val[j]!).toGF216 = x.toGF216 ^ j) ∧
        result.val.length = max xs.val.length iter.«end».val ⦄ := by
  unfold compute_at_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize ×
                        alloc.vec.Vec GF16) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize ×
                     alloc.vec.Vec GF16) =>
        p.1.«end» = iter.«end» ∧
        2 ≤ p.1.start.val ∧
        p.1.start.val = p.2.val.length ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ max iter.start.val iter.«end».val ∧
        p.2.val.length + 1 ≤ Usize.max ∧
        (∀ j, j < p.2.val.length → (p.2.val[j]!).toGF216 = x.toGF216 ^ j))
  · rintro ⟨iter', xs'⟩
      ⟨h_end', h_ge2', h_inv', h_start_le', h_bound', h_len', h_pow'⟩
    simp only [] at h_end' h_ge2' h_inv' h_start_le' h_bound' h_len' h_pow' ⊢
    have h_body := body_spec iter' xs' h_ge2' h_inv' h_len'
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done result =>
      simp only [] at h_cf ⊢
      obtain ⟨h_eq, h_not_lt⟩ := h_cf
      subst h_eq
      push Not at h_not_lt
      rw [h_end'] at h_not_lt
      refine ⟨h_pow', ?_⟩
      apply Nat.le_antisymm
      · have : iter'.start.val ≤ max iter.start.val iter.«end».val := h_bound'
        rw [h_inv] at this
        grind
      · grind
    | ControlFlow.cont (iter1, xs1) =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, g, h_xs1, h_g⟩ := h_cf
      constructor
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [h_end1, h_end']
        · rw [h_start1]; omega
        · rw [h_start1, h_xs1, List.length_append, List.length_singleton, h_inv']
        · rw [h_start1]; omega
        · rw [h_start1]
          have h_lt_end : iter'.start.val + 1 ≤ iter.«end».val := by
            have : iter'.«end».val = iter.«end».val := by rw [h_end']
            omega
          have := le_max_right iter.start.val iter.«end».val
          omega
        · rw [h_xs1, List.length_append, List.length_singleton]
          have h_lt_end : iter'.start.val + 1 ≤ iter.«end».val := by
            have : iter'.«end».val = iter.«end».val := by rw [h_end']
            omega
          have := le_max_right xs.val.length iter.«end».val
          omega
        · rw [h_xs1]
          apply power_invariant_step x xs'.val g
          · grind
          · grind
          · grind
      · rw [h_start1, h_end1]
        have : iter'.«end».val = iter.«end».val := by rw [h_end']
        omega
  · refine ⟨rfl, h_ge2, h_inv, le_refl _, le_max_left _ _, ?_, h_pow⟩
    have := le_max_left xs.val.length iter.«end».val
    grind

end spqr.encoding.polynomial.Poly.compute_at_loop0

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
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_v : iter.start.val < v.val.length := by omega
    have h_i_lt_xs : iter.start.val < xs.val.length := by omega
    step*
    grind
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.Poly.compute_at_loop1

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

/-!
# Spec theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::compute_at`

The Rust function `Poly::compute_at` (in `src/encoding/polynomial.rs`, lines 255:4-273:5) evaluates
a polynomial at a given point `x` in GF(2¹⁶).  Given a polynomial `self` with coefficient vector
`[a₀, a₁, …, aₙ₋₁]` and a field element `x : GF16`, it computes:

  `p(x) = a₀ + a₁·x + a₂·x² + … + aₙ₋₁·xⁿ⁻¹`

The implementation proceeds in two phases:

  1. **Power-vector construction** (loop 0, lines 260:8-265:9): builds a vector `xs` of successive
     powers of `x` in GF(2¹⁶):
     ```
     let mut xs = Vec::with_capacity(self.coefficients.len());
     xs.push(GF16::ONE);
     xs.push(x);
     for i in 2..self.coefficients.len() {
         let a = xs[i / 2];
         let b = xs[(i / 2) + (i % 2)];
         xs.push(a * b);
     }
     ```
     After this phase, `xs[j] = x^j` for all `j < max(2, n)`, exploiting the square-and-multiply
     identity `x^i = x^(i/2) · x^(i/2 + i%2)`.

  2. **Dot-product accumulation** (loop 1, lines 269:8-271:9): computes the inner product of the
     coefficient vector and the power vector:
     ```
     let mut out = GF16::ZERO;
     for i in 0..self.coefficients.len() {
         out += self.coefficients[i] * xs[i];
     }
     ```
     After this phase, `out = Σ_{j=0}^{n-1} a_j · x^j = p(x)`.

The function returns `out`, the GF(2¹⁶) evaluation of the polynomial at `x`.

Concretely, the Aeneas-extracted Lean function `encoding.polynomial.Poly.compute_at`:
  1. Computes `i := self.coefficients.len()` (the coefficient count `n`).
  2. Creates an empty vector `xs := Vec::with_capacity(n)`.
  3. Pushes `GF16::ONE` (= x⁰) and `x` (= x¹) into `xs`, giving `xs = [1, x]`.
  4. Delegates to `encoding.polynomial.Poly.compute_at_loop0` with the range `2..n` and initial
     vector `xs`, which extends `xs` with `xs[j] = x^j` for `j = 2, …, max(2, n) − 1`.
  5. Delegates to `encoding.polynomial.Poly.compute_at_loop1` with the range `0..n`, coefficient
     vector `self.coefficients`, power vector `xs`, and initial accumulator `GF16::ZERO`, which
     computes the dot product `Σ_{j=0}^{n-1} coeff[j] · x^j`.

Since the top-level function introduces no additional logic beyond the two loop delegations and the
initial vector setup, the postcondition is composed from the loop specifications:
  - **Loop 0** (`compute_at_loop0.loop_spec`): establishes the power-vector invariant
    `xs[j].toGF216 = x.toGF216 ^ j` for all `j < max(2, n)`.
  - **Loop 1** (`compute_at_loop1.loop_spec`): establishes the dot-product postcondition
    `out.toGF216 = Σ_{j < n} coeff[j].toGF216 * xs[j].toGF216`.

Combining these with the bridge lemma `dot_product_eq_eval` (which substitutes the power-vector
invariant and connects the `Finset.sum` to the Mathlib polynomial evaluation) yields the final
result:
  `result.toGF216 = (self.toGF216Poly).eval (x.toGF216) = self.evalAt x`.

In GF(2¹⁶), multiplication is carry-less polynomial multiplication modulo the irreducible polynomial
`x¹⁶ + x¹² + x³ + x + 1` (0x1100b), and addition is bitwise XOR.

**Source**: spqr/src/encoding/polynomial.rs (lines 255:4-273:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.math.gf
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly


/--
**Spec theorem for `encoding.polynomial.Poly.compute_at`**:

• The function always succeeds (no panic) provided the coefficient vector length satisfies
  `self.coefficients.val.length + 1 ≤ Usize.max`, ensuring that the power vector `xs` can grow
  to hold `max(2, n)` elements and the loop indices stay within `Usize` bounds.  The two initial
  `Vec::push` operations require `0 < Usize.max` and `1 < Usize.max`, both of which are trivially
  satisfied.

• **Polynomial evaluation postcondition**:
    `(result.toGF216 : GF216) = self.evalAt x`
  where `Poly.evalAt p x = (p.toGF216Poly).eval (x.toGF216)` evaluates the mathematical
  interpretation of the polynomial `p` in `GF216[X] = (GaloisField 2 16)[X]` at the GF(2¹⁶)
  lift of the point `x`.

  Equivalently, this states that the GF(2¹⁶) value returned by the Rust implementation equals
  the Mathlib polynomial evaluation:
    `result.toGF216 = (listToGF216Poly self.coefficients.val).eval (x.toGF216)`
  which is `∑_{j=0}^{n−1} coeff[j].toGF216 · x.toGF216^j` in `GF216 = GaloisField 2 16`.

**Source**: spqr/src/encoding/polynomial.rs (lines 255:4-273:5)
-/
@[step]
theorem compute_at_spec
    (self : Poly) (x : GF16)
    (h_len : self.coefficients.val.length + 1 ≤ Usize.max) :
    compute_at self x ⦃ (result : GF16) =>
      result.toGF216  = self.evalAt x ⦄ := by
  unfold compute_at
  step
  · simp only [alloc.vec.Vec.with_capacity]
    grind
  step
  · simp_all [alloc.vec.Vec.with_capacity]
    grind
  have h_pow_init := initial_power_invariant x
  have h_xs2_val : xs2.val = [GF16.ONE, x] := by
    have h_wc : (alloc.vec.Vec.with_capacity GF16
                    self.coefficients.len).val = [] := by
      simp [alloc.vec.Vec.with_capacity]
    rw [xs2_post, result_post, h_wc]; simp
  have h_xs2_len : xs2.val.length = 2 := by rw [h_xs2_val]; rfl
  have h_xs2_pow : ∀ j, j < xs2.val.length →
      (xs2.val[j]!).toGF216 = x.toGF216 ^ j := by
    rw [h_xs2_val]; exact h_pow_init
  step with compute_at_loop0.loop_spec x
    { start := 2#usize, «end» := self.coefficients.len }
    xs2 (by scalar_tac) h_xs2_len.symm h_xs2_pow (by
      rw [h_xs2_len]
      change Nat.max 2 self.coefficients.val.length + 1 ≤ Usize.max
      simp only [Nat.max_def]
      split_ifs with hcond
      · exact h_len
      · scalar_tac) as ⟨xs3, h_xs3_pow, h_xs3_len⟩
  have h_xs3_ge : self.coefficients.val.length ≤ xs3.val.length := by
    have hle := h_xs3_len
    change self.coefficients.val.length ≤ xs3.val.length
    rw [hle, h_xs2_len]; exact le_max_right _ _
  apply WP.spec_mono (compute_at_loop1.loop_spec self.coefficients xs3
    { start := 0#usize, «end» := self.coefficients.len }
    GF16.ZERO (by simp) h_xs3_ge (by
      simp [GF16.ZERO, GF16.toGF216, Nat.toGF216]))
  intro result h_result
  have h_max : max (0#usize).val (self.coefficients.len).val =
      self.coefficients.val.length := by
    simp
  rw [h_max] at h_result
  rw [h_result]
  exact dot_product_eq_eval x self.coefficients.val xs3.val h_xs3_pow h_xs3_ge

end spqr.encoding.polynomial.Poly
