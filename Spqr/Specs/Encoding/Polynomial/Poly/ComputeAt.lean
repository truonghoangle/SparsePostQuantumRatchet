/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.Poly.ComputeAtLoop0
import Spqr.Specs.Encoding.Polynomial.Poly.ComputeAtLoop1

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


/-! ## Helper lemmas -/

/--
**Initial power-vector invariant.**

The two-element vector `[GF16::ONE, x]` satisfies the power-vector invariant:
  `[ONE, x][j]!.toGF216 = x.toGF216 ^ j` for all `j < 2`.

This establishes the precondition for loop 0, ensuring that the initial entries `x⁰ = 1` and
`x¹ = x` are correctly represented before the loop extends the vector to higher powers.
-/
private lemma initial_power_invariant (x : encoding.gf.GF16) :
    ∀ j, j < [GF16.ONE, x].length →
      ([GF16.ONE, x][j]!).toGF216 = x.toGF216 ^ j := by
  intro j hj
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j
  · simp [GF16.ONE, GF16.toGF216, Nat.toGF216, natToBinaryPoly_one, map_one]
  · simp [pow_one]

/--
**Polynomial evaluation via range sum.**

If all coefficients of `p` at positions `≥ n` are zero, then `p.eval a` equals the finite sum
`∑ j ∈ Finset.range n, p.coeff j * a ^ j`.  This extends the standard
`Polynomial.eval_eq_sum_range` (which uses `natDegree + 1` as the upper bound) to any upper bound
`n` beyond which all coefficients vanish.
-/
private lemma eval_eq_range_sum (p : GF216Poly) (a : GF216) (n : ℕ)
    (h : ∀ j, n ≤ j → p.coeff j = 0) :
    p.eval a = ∑ j ∈ Finset.range n, p.coeff j * a ^ j := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_subset
  · intro j hj
    rw [Finset.mem_range]
    by_contra h_ge; push Not at h_ge
    exact (Polynomial.mem_support_iff.mp hj) (h j h_ge)
  · intro j _ hj
    have : p.coeff j = 0 := by
      by_contra h_ne
      exact hj (Polynomial.mem_support_iff.mpr h_ne)
    rw [this, zero_mul]

/--
**Dot-product to polynomial evaluation bridge.**

When the power vector `xs` satisfies the power-vector invariant `xs[j].toGF216 = x.toGF216 ^ j` for
all `j < xs.length`, and `n = v.length ≤ xs.length`, the dot product
  `∑ j ∈ Finset.range n, v[j]!.toGF216 * xs[j]!.toGF216`
equals the polynomial evaluation
  `(listToGF216Poly v).eval (x.toGF216)`.

This is the key bridge connecting the computational result of the two loops (power-vector
construction + dot-product accumulation) to the mathematical polynomial evaluation in
`GF216 = GaloisField 2 16`.  The proof proceeds in three steps:

  1. **Substitute power invariant**: replace each `(xs[j]!).toGF216` by `x.toGF216 ^ j`.
  2. **Rewrite coefficients**: replace each `(v[j]!).toGF216` by `(listToGF216Poly v).coeff j`
     using the `getElem_bang_toGF216_eq_coeff` bridge from `Spqr.Math.Poly`.
  3. **Connect to evaluation**: the resulting `∑ j ∈ range n, p.coeff j * x ^ j` equals
     `p.eval x` by `eval_eq_range_sum` (since `p.coeff j = 0` for `j ≥ n`).
-/
private lemma dot_product_eq_eval
    (x : encoding.gf.GF16)
    (v : List encoding.gf.GF16)
    (xs : List encoding.gf.GF16)
    (h_pow : ∀ j, j < xs.length → (xs[j]!).toGF216 = x.toGF216 ^ j)
    (h_len : v.length ≤ xs.length) :
    (∑ j ∈ Finset.range v.length,
      (v[j]!).toGF216 * (xs[j]!).toGF216) =
    (listToGF216Poly v).eval (x.toGF216) := by
  -- Step 1: Substitute power invariant into the dot product
  have h_sub : ∀ j ∈ Finset.range v.length,
      (v[j]!).toGF216 * (xs[j]!).toGF216 =
      (v[j]!).toGF216 * x.toGF216 ^ j := by
    intro j hj; rw [Finset.mem_range] at hj
    congr 1; exact h_pow j (by omega)
  rw [Finset.sum_congr rfl h_sub]
  -- Step 2: Rewrite getElem! to polynomial coefficients
  have h_coeff : ∀ j ∈ Finset.range v.length,
      (v[j]!).toGF216 * x.toGF216 ^ j =
      (listToGF216Poly v).coeff j * x.toGF216 ^ j := by
    intro j hj
    congr 1; exact getElem_bang_toGF216_eq_coeff v j
  rw [Finset.sum_congr rfl h_coeff]
  -- Step 3: Connect the range sum to polynomial evaluation
  exact (eval_eq_range_sum (listToGF216Poly v) (x.toGF216) v.length
    (fun j hj => listToGF216Poly_coeff_eq_zero v j hj)).symm

/--
**Max-2 length bound.**

If `n + 1 ≤ Usize.max`, then `max 2 n + 1 ≤ Usize.max`. This is used to discharge the length
precondition of `compute_at_loop0.loop_spec` when the initial vector has length 2.
-/
private lemma max_two_succ_le_usize_max (n : Nat) (h : n + 1 ≤ Usize.max) :
    Nat.max 2 n + 1 ≤ Usize.max := by
  simp only [Nat.max_def]
  split_ifs
  · exact h
  · scalar_tac

/--
**Zero accumulator equals empty sum.**

`GF16.ZERO.toGF216 = ∑ j ∈ Finset.range 0, f j` for any `f`, since the sum over an empty range
is zero and `GF16.ZERO` maps to `0 : GF216`.
-/
private lemma zero_toGF216_eq_empty_sum
    (v xs : alloc.vec.Vec encoding.gf.GF16) :
    GF16.ZERO.toGF216 = ∑ j ∈ Finset.range 0,
      (v.val[j]!).toGF216 * (xs.val[j]!).toGF216 := by
  simp [GF16.ZERO, GF16.toGF216, Nat.toGF216, natToBinaryPoly_zero, map_zero]

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
    have h_wc : (alloc.vec.Vec.with_capacity encoding.gf.GF16
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
