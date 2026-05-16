/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Poly.ComputeAtLoopBody0

/-!
# Spec theorem for `Poly::compute_at`: loop 0

The Rust function `Poly::compute_at` (in `src/encoding/polynomial.rs`, lines 255:4-273:5) evaluates
a polynomial at a given point `x` in GF(2¹⁶).  The first loop (loop 0, lines 260:8-265:9) builds a
vector `xs` of successive powers of `x`:

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

This file specifies the **full loop** — the `loop` fixed-point wrapper around the body
(`ComputeAtLoopBody0.body_spec`).  The loop consumes the `Range<usize>` iterator from `2` to
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
**Euclidean-division identity**: for any natural number `n`, `n / 2 + (n / 2 + n % 2) = n`.

This is the key arithmetic identity used to show that `x^(n/2) · x^(n/2 + n%2) = x^n`.  The proof
exploits the Euclidean-division identity `n = (n / 2) · 2 + n % 2`, from which
`n / 2 + (n / 2 + n % 2) = 2 · (n / 2) + n % 2 = n`.
-/
private lemma div2_add_sum_eq (n : Nat) : n / 2 + (n / 2 + n % 2) = n := by
  have := Nat.div_add_mod n 2
  omega

/--
**Power-vector invariant preservation.**

Appending `g = xs[n/2] * xs[n/2 + n%2]` to a power vector `xs` of length `n ≥ 2` that satisfies
`xs[j].toGF216 = x.toGF216 ^ j` for all `j < n` produces a vector of length `n + 1` satisfying the
same property for all `j < n + 1`.

For `j < n`, the element is inherited from `xs` (the append does not change existing elements).
For `j = n`, the new element satisfies:
  `g.toGF216 = x.toGF216 ^ (n/2) · x.toGF216 ^ (n/2 + n%2) = x.toGF216 ^ n`
by the Euclidean-division identity `n/2 + (n/2 + n%2) = n` and the power law `x^a · x^b = x^(a+b)`.
-/
private lemma power_invariant_step
    (x : encoding.gf.GF16)
    (xs : List encoding.gf.GF16)
    (g : encoding.gf.GF16)
    (h_ge2 : 2 ≤ xs.length)
    (h_pow : ∀ j, j < xs.length → (xs[j]!).toGF216 = x.toGF216 ^ j)
    (h_g : g.toGF216 =
      (xs[xs.length / 2]!).toGF216 *
      (xs[xs.length / 2 + xs.length % 2]!).toGF216) :
    ∀ j, j < (xs ++ [g]).length → ((xs ++ [g])[j]!).toGF216 = x.toGF216 ^ j := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  have h_div2_lt : xs.length / 2 < xs.length := Nat.div_lt_self (by omega) (by omega)
  have h_sum_lt : xs.length / 2 + xs.length % 2 < xs.length := by
    have := Nat.div_add_mod xs.length 2; omega
  by_cases hlt : j < xs.length
  · -- Existing element: inherited from xs
    have hlt' : j < (xs ++ [g]).length := by grind
    grind
  · -- New element at position xs.length
    have hj_eq : j = xs.length := by omega
    subst hj_eq
    have hlt' : xs.length < (xs ++ [g]).length := by grind
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
      lt_add_iff_pos_right, Order.lt_one_iff, getElem!_pos, Std.le_refl, List.getElem_append_right,
      tsub_self, List.getElem_cons_zero]
    rw [h_g, h_pow _ h_div2_lt, h_pow _ h_sum_lt, ← pow_add, div2_add_sum_eq]


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
    (x : encoding.gf.GF16)
    (iter : core.ops.range.Range Std.Usize)
    (xs : alloc.vec.Vec encoding.gf.GF16)
    (h_ge2 : 2 ≤ iter.start.val)
    (h_inv : iter.start.val = xs.val.length)
    (h_pow : ∀ j, j < xs.val.length → (xs.val[j]!).toGF216 = x.toGF216 ^ j)
    (h_len : max xs.val.length iter.«end».val + 1 ≤ Usize.max) :
    compute_at_loop0 iter xs
      ⦃ (result : alloc.vec.Vec encoding.gf.GF16) =>
        (∀ j, j < result.val.length → (result.val[j]!).toGF216 = x.toGF216 ^ j) ∧
        result.val.length = max xs.val.length iter.«end».val ⦄ := by
  unfold compute_at_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                        alloc.vec.Vec encoding.gf.GF16) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                     alloc.vec.Vec encoding.gf.GF16) =>
        p.1.«end» = iter.«end» ∧
        2 ≤ p.1.start.val ∧
        p.1.start.val = p.2.val.length ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ max iter.start.val iter.«end».val ∧
        p.2.val.length + 1 ≤ Usize.max ∧
        (∀ j, j < p.2.val.length → (p.2.val[j]!).toGF216 = x.toGF216 ^ j))
  · -- Body step: prove invariant is preserved and measure decreases
    rintro ⟨iter', xs'⟩
      ⟨h_end', h_ge2', h_inv', h_start_le', h_bound', h_len', h_pow'⟩
    simp only [] at h_end' h_ge2' h_inv' h_start_le' h_bound' h_len' h_pow' ⊢
    -- Apply the body spec from ComputeAtLoopBody0
    have h_body := body_spec iter' xs' h_ge2' h_inv' h_len'
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done result =>
      -- Done case: iterator exhausted, result = xs'
      simp only [] at h_cf ⊢
      obtain ⟨h_eq, h_not_lt⟩ := h_cf
      subst h_eq
      push Not at h_not_lt
      rw [h_end'] at h_not_lt
      refine ⟨h_pow', ?_⟩
      -- result.val.length = max xs.val.length iter.«end».val
      apply Nat.le_antisymm
      · -- iter'.start ≤ max(...)
        have : iter'.start.val ≤ max iter.start.val iter.«end».val := h_bound'
        rw [h_inv] at this
        grind
      · -- max(...) ≤ iter'.start
        grind
    | ControlFlow.cont (iter1, xs1) =>
      -- Cont case: one more element appended
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, g, h_xs1, h_g⟩ := h_cf
      constructor
      · -- Invariant preserved (7 conjuncts)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- iter1.end = iter.end
          rw [h_end1, h_end']
        · -- 2 ≤ iter1.start
          rw [h_start1]; omega
        · -- iter1.start = xs1.length
          rw [h_start1, h_xs1, List.length_append, List.length_singleton, h_inv']
        · -- iter.start ≤ iter1.start
          rw [h_start1]; omega
        · -- iter1.start ≤ max(...)
          rw [h_start1]
          have h_lt_end : iter'.start.val + 1 ≤ iter.«end».val := by
            have : iter'.«end».val = iter.«end».val := by rw [h_end']
            omega
          have := le_max_right iter.start.val iter.«end».val
          omega
        · -- xs1.length + 1 ≤ Usize.max
          rw [h_xs1, List.length_append, List.length_singleton]
          have h_lt_end : iter'.start.val + 1 ≤ iter.«end».val := by
            have : iter'.«end».val = iter.«end».val := by rw [h_end']
            omega
          have := le_max_right xs.val.length iter.«end».val
          omega
        · -- Power invariant preserved
          rw [h_xs1]
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
