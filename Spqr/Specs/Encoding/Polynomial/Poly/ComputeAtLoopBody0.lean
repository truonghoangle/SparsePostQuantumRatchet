/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.GF16.Mul

/-!
# Spec theorem for `Poly::compute_at`: loop body 0

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

This file specifies the **loop body** — a single step of the above iteration.  The extracted Lean
function `encoding.polynomial.Poly.compute_at_loop0.body` performs one step: it calls `next` on the
`Range<usize>` iterator and either:

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


-- The long identifier cannot be broken across lines; suppress
-- the line-length linter for the lemma statement and proof.
/--
The range iterator `next` always returns `ok` and either provides the current `start` value (when
`start < end`) or `none` (when `start ≥ end`).  This is the concrete specification for the
`core.ops.range.Range<usize>` iterator used in the Rust `for i in 2..self.coefficients.len()` loop.
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
**Auxiliary lemma**: for `n ≥ 2`, we have `n / 2 + n % 2 < n`.

This ensures that the second vector index `xs[i/2 + i%2]` is within bounds when the loop
invariant `i = xs.length` holds and `i ≥ 2`.  The proof exploits the Euclidean-division identity
`n = (n / 2) * 2 + n % 2`, from which `n − (n / 2 + n % 2) = n / 2 ≥ 1` when `n ≥ 2`.
-/
private lemma div2_add_mod2_lt (n : Nat) (h : 2 ≤ n) : n / 2 + n % 2 < n := by
  have := Nat.div_add_mod n 2
  omega

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
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := IteratorRange_next_Usize_post iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · -- Continue case: iterator yields some i = iter.start
    obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    -- Key arithmetic bounds from the loop invariant
    have h_div2_lt : iter.start.val / 2 < xs.val.length := by
      rw [← h_inv]; exact Nat.div_lt_self (by omega) (by omega)
    have h_sum_lt : iter.start.val / 2 + iter.start.val % 2 < xs.val.length := by
      rw [← h_inv]; exact div2_add_mod2_lt _ h_ge2
    -- Step through division, indexing, modulo, addition, indexing, multiplication, and push
    step*
  · -- Done case: iterator exhausted
    obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.Poly.compute_at_loop0
