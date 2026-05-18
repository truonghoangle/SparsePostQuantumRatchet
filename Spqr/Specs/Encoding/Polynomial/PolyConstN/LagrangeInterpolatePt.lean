/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Gf.GF16.ConstDiv
import Spqr.Specs.Encoding.Polynomial.PolyConstN.Mult
import Spqr.Specs.Encoding.Polynomial.PolyConstN.LagrangeInterpolatePtLoop0

/-! # Spec theorem for
`spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyConst<N>}::lagrange_interpolate_pt`

Given a slice of evaluation points `pts : &[Pt]` and an index `i < N ≤ pts.len()`, the Rust
function `PolyConst::lagrange_interpolate_pt` (in `src/encoding/polynomial.rs`, lines 370:4-395:5)
returns the i-th scaled Lagrange basis polynomial over GF(2¹⁶) packed into a fixed-size
`PolyConst N` whose coefficient array has exactly `N` slots.  Unlike the heap-backed `Poly`
variant (`Poly::lagrange_interpolate_pt`), this version is `const fn`, allocates no `Vec`, and
relies on a tight static degree bound: every intermediate polynomial fits in `N` coefficients
because the leading slot `coefficients[N − 1]` is maintained zero throughout the loop.

Concretely the Aeneas-extracted Lean function
`encoding.polynomial.PolyConst.lagrange_interpolate_pt` proceeds as follows:

1. **Read the interpolation point**: `pi := pts[i]` via `Slice.index_usize`.

2. **Initialise the unit polynomial**: build an `Array GF16 N` filled with `GF16.ZERO` and
   overwrite position `0` with `GF16.ONE`, yielding the coefficient list
     `[ONE, ZERO, …, ZERO]`,
   which represents the constant polynomial `1 ∈ GF216[X]`.  This is the multiplicative
   identity of the loop's running product.

3. **Build the unnormalised basis polynomial and the denominator** by calling
     `lagrange_interpolate_pt_loop pts pi {coefficients := a1} GF16.ONE 0#usize`
   (see `LagrangeInterpolatePtLoop0`).  After all `N` iterations, the loop returns
   `(pi1, p, denominator)` with `pi1 = pi` and
   - `listToGF216Poly p.coefficients =
        condProdLinearFactors pi.x (pts.take N) 0`        — the running poly, started at `1`.
   - `denominator.toGF216 =
        lagrangeDenomProd pi.x (pts.take N) 0`             — the denominator, started at `1`.

   Here `condProdLinearFactors pi.x (pts.take N) 0 = ∏_{j < N, pts[j].x.value ≠ pi.x.value}
   (X − C(pts[j].x.toGF216))` and `lagrangeDenomProd pi.x (pts.take N) 0 =
   ∏_{j < N, pts[j].x.value ≠ pi.x.value} (pi.x.toGF216 − pts[j].x.toGF216)` are the
   value-skip Lagrange products restricted to the first `N` points.  Index `j = i` is always
   skipped because `pi.x.value = pts[i].x.value`.

4. **Fermat-style division**: compute
     `g := pi.y.const_div denominator`,
   whose specification (`GF16.const_div_spec`) gives at the GF(2¹⁶) level
     `g.toGF216 = pi.y.toGF216 * denominator.toGF216 ^ (2¹⁶ − 2)`.
   When `denominator ≠ 0` Fermat's little theorem in GF(2¹⁶) makes the exponent
   `2¹⁶ − 2` the multiplicative inverse, so `g = pi.y / denominator`.

5. **Scale the basis polynomial**: return `p.mult(g)`, which (via `PolyConst.mult_spec`)
   yields a polynomial whose `GF216[X]` interpretation is `C g.toGF216 ·
   listToGF216Poly p.coefficients`.

The net effect is to produce a polynomial `result` such that

  `listToGF216Poly result.coefficients
       = C (pi.y.toGF216 *
            (lagrangeDenomProd pi.x (pts.take N) 0) ^ (2¹⁶ − 2)) *
         condProdLinearFactors pi.x (pts.take N) 0`

in `GF216[X]`, which — using `lagrangeScaleGF216 pi (pts.take N) =
pi.y.toGF216 * (lagrangeDenomProd pi.x (pts.take N) 0) ^ (2¹⁶ − 2)` — collapses to

  `listToGF216Poly result.coefficients
       = C (lagrangeScaleGF216 pi (pts.take N)) *
         condProdLinearFactors pi.x (pts.take N) 0`.

When the first `N` x-coordinates are pairwise distinct, `condProdLinearFactors` coincides with
the classical Lagrange basis polynomial `∏_{j ≠ i} (X − pts[j].x)` and the denominator is
non-zero, so the right-hand side is the i-th term of the standard Lagrange interpolation
formula passing through `(pi.x, pi.y)`.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition (`a − b = a + b = a ⊕ b`),
so the linear factors `(X − pts[j].x)` and the differences `pi.x − pts[j].x` are equivalently
`(X + pts[j].x)` and `pi.x + pts[j].x`.

**Source**: spqr/src/encoding/polynomial.rs (lines 370:4-395:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop
  (condProdLinearFactors countNonSkip countNonSkip_skip countNonSkip_accum
   countNonSkip_ge)

namespace spqr.encoding.polynomial.PolyConst

/-! ## Helper lemmas for the initial state -/

/--
**The freshly-initialised coefficient array represents the constant polynomial `1`.**

After `let a := Array.repeat N GF16.ZERO` and `a1 := Array.update a 0 GF16.ONE`, the underlying
list is `[ONE, ZERO, ZERO, …, ZERO]` with `N` entries.  Mapping through `listToGF216Poly` and
using `GF16.toGF216_zero_val` / `GF16.toGF216_one_val` at each coefficient position, every
coefficient at degree `≥ 1` is zero and the constant coefficient is `1`, so the resulting
`GF216[X]` element is `C 1 = 1`.
-/
private theorem listToGF216Poly_init_one
    {N : Usize} (a1 : Array GF16 N)
    (h_len : a1.val.length = N.val)
    (h0 : (a1.val[0]!).value.val = 1)
    (h_rest : ∀ j, 0 < j → j < N.val → (a1.val[j]!).value.val = 0) :
    listToGF216Poly a1.val = (1 : GF216Poly) := by
  -- We compare coefficient-by-coefficient.  At every position `m`:
  -- * `(1 : GF216Poly).coeff m` is `1` if `m = 0` and `0` otherwise.
  -- * `(listToGF216Poly a1.val).coeff m` is `(a1.val[m]!).toGF216` (via
  --   `getElem_bang_toGF216_eq_coeff`, which folds the out-of-bounds case to the
  --   `GF16` default — whose `toGF216` is also `0`).
  -- The hypotheses `h0` and `h_rest` exactly say that the underlying `value.val`
  -- equals `1` at position `0` and `0` elsewhere, so `GF16.toGF216_one_val` /
  -- `GF16.toGF216_zero_val` close each case.
  apply Polynomial.ext
  intro m
  cases m with
  | zero =>
    -- `(1 : GF216Poly).coeff 0 = 1` and the LHS coefficient is
    -- `(a1.val[0]!).toGF216 = 1` by `h0`.
    rw [Polynomial.coeff_one_zero, ← getElem_bang_toGF216_eq_coeff]
    exact GF16.toGF216_one_val _ h0
  | succ n =>
    -- The RHS coefficient is `0`.
    have h_one : (1 : GF216Poly).coeff (n + 1) = 0 := by
      rw [Polynomial.coeff_one]; simp
    rw [h_one]
    by_cases hlt : n + 1 < a1.val.length
    · -- In-bounds: use `h_rest`.
      rw [← getElem_bang_toGF216_eq_coeff]
      apply GF16.toGF216_zero_val
      exact h_rest (n + 1) (Nat.succ_pos n) (h_len ▸ hlt)
    · -- Out-of-bounds: the coefficient is zero by length bound.
      push Not at hlt
      exact listToGF216Poly_coeff_eq_zero a1.val (n + 1) hlt

/--
**The freshly-initialised coefficient array has zero leading coefficient when `N ≥ 2`.**

Since position `N − 1 ≥ 1` of `a1 = [ONE, ZERO, …, ZERO]` is `GF16.ZERO`, the underlying
`u16` value is `0`.  This is the precondition needed to feed `mult_xdiff` (and hence the
loop body) inside `lagrange_interpolate_pt_loop`.
-/
private theorem init_leading_zero
    {N : Usize} (a1 : Array GF16 N)
    (h_N_ge_two : 2 ≤ N.val)
    (h_rest : ∀ j, 0 < j → j < N.val → (a1.val[j]!).value.val = 0) :
    (a1.val[N.val - 1]!).value.val = 0 := by
  exact h_rest (N.val - 1) (by omega) (by omega)


/-! ## Helper lemma: degree bound for the initial state

The loop spec (`lagrange_interpolate_pt_loop.loop_spec`) requires the polynomial-degree
invariant
    `(listToGF216Poly p.coefficients.val).natDegree +
        countNonSkip pi.x (pts.val.take N.val) j.val < N.val`.

At the entry point `(p, j) = ({coefficients := a1}, 0)`, the initial polynomial is the
constant `1` so its `natDegree` is `0`, and `countNonSkip pi.x (pts.val.take N.val) 0` is at
most `N.val − 1` because index `i < N.val` is always a skip (`pi.x.value = pts[i].x.value`).
-/

/-! ### Helper lemmas for the `countNonSkip` bound

The original axiom statement used `m ≤ pts.length`, but the conclusion
`countNonSkip pi_x pts 0 ≤ m - 1` is only valid when the segment `pts` itself has length at
most `m` (since `countNonSkip` counts over the full list `[0, pts.length)`, not just `[0, m)`).
We therefore strengthen the hypothesis to `pts.length ≤ m`; in the actual call site we have
`pts = pts.val.take N.val` with `(pts.val.take N.val).length = N.val = m`, so the new
hypothesis holds with equality and the lemma is used in exactly the intended way.
-/

/--
**Trivial bound**: `countNonSkip pi_x pts start ≤ pts.length - start` for all `start`.

By induction on the natural well-founded measure `pts.length - start`: in the recursive case
we use either `countNonSkip_skip` (count is preserved) or `countNonSkip_accum` (count grows
by exactly `1`), and in either case the recursive IH together with `omega` closes the goal.
-/
private lemma countNonSkip_le_length_sub
    (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat) :
    countNonSkip pi_x pts start ≤ pts.length - start := by
  by_cases h_lt : start < pts.length
  · have ih := countNonSkip_le_length_sub pi_x pts (start + 1)
    by_cases h_eq : pi_x.value = (pts.get ⟨start, h_lt⟩).x.value
    · rw [countNonSkip_skip pi_x pts start h_lt h_eq]; omega
    · rw [countNonSkip_accum pi_x pts start h_lt h_eq]; omega
  · rw [countNonSkip_ge pi_x pts start (by omega)]; omega
termination_by pts.length - start

/--
**Strict bound when a skip exists**: if `start ≤ i < pts.length` and `pi_x.value =
pts[i].x.value` (i.e., index `i` is a skip), then
`countNonSkip pi_x pts start + 1 ≤ pts.length - start`.

Proof by induction on `i - start`:
* If `start = i`, the current iteration is a skip, so the count is preserved
  (`countNonSkip_skip`) and the result follows from `countNonSkip_le_length_sub` applied at
  `start + 1`.
* If `start < i`, we recurse on `start + 1`; whether the current iteration is a skip or an
  accumulate, `omega` combines the recursive IH with the appropriate unfolding lemma.
-/
private lemma countNonSkip_add_one_le_of_skip
    (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (i : Nat) (h_start_le : start ≤ i) (h_i_lt : i < pts.length)
    (h_skip : pi_x.value = (pts.get ⟨i, h_i_lt⟩).x.value) :
    countNonSkip pi_x pts start + 1 ≤ pts.length - start := by
  by_cases h_eq_si : start = i
  · -- Base: the current iteration `start = i` is itself the skip.
    subst h_eq_si
    rw [countNonSkip_skip pi_x pts start h_i_lt h_skip]
    have := countNonSkip_le_length_sub pi_x pts (start + 1)
    omega
  · -- Step: recurse at `start + 1`, then case on whether `start` is a skip or accumulate.
    have h_start_lt_i : start < i := by omega
    have h_start_lt : start < pts.length := by omega
    have ih := countNonSkip_add_one_le_of_skip pi_x pts (start + 1) i
      (by omega) h_i_lt h_skip
    by_cases h_eq : pi_x.value = (pts.get ⟨start, h_start_lt⟩).x.value
    · rw [countNonSkip_skip pi_x pts start h_start_lt h_eq]; omega
    · rw [countNonSkip_accum pi_x pts start h_start_lt h_eq]; omega
termination_by i - start

/--
**Bound on `countNonSkip` when at least one index in `[0, m)` is a skip.**

If `pts.length ≤ m` and there exists `i < m` such that whenever `i < pts.length` we have
`pi_x.value = pts[i].x.value` (which makes index `i` a skip when it falls inside the list),
then `countNonSkip pi_x pts 0 ≤ m − 1`.

Proof: split on whether `i < pts.length`.
* If yes, the skip at index `i` is real, and `countNonSkip_add_one_le_of_skip` (with
  `start = 0`) gives `countNonSkip pi_x pts 0 + 1 ≤ pts.length ≤ m`, hence the bound.
* If no, then `pts.length ≤ i < m`, so `pts.length ≤ m - 1`; combined with the trivial
  bound `countNonSkip pi_x pts 0 ≤ pts.length` we again get the desired inequality.
-/
private theorem countNonSkip_le_of_skip_exists
    (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (m : Nat)
    (h_m_le : pts.length ≤ m)
    (i : Nat) (hi : i < m)
    (h_skip : ∀ (h : i < pts.length),
      pi_x.value = (pts.get ⟨i, h⟩).x.value) :
    countNonSkip pi_x pts 0 ≤ m - 1 := by
  by_cases h_i : i < pts.length
  · -- Real skip: the strict bound gives `count + 1 ≤ pts.length ≤ m`, hence `count ≤ m - 1`.
    have h := countNonSkip_add_one_le_of_skip pi_x pts 0 i (Nat.zero_le _) h_i (h_skip h_i)
    omega
  · -- `i ≥ pts.length`, so `pts.length < m`; the trivial bound suffices.
    have h := countNonSkip_le_length_sub pi_x pts 0
    omega


/-! ## Main spec theorem -/

/--
**Spec theorem for `spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt`**:

Given a slice of points `pts` with `N ≤ pts.val.length` and a valid index `i < N`, the
function returns a polynomial `result : PolyConst N` satisfying:

• The function always succeeds (no panic) under the stated preconditions, since
  `Slice.index_usize`, `Array.repeat`, `Array.update`, the loop
  `lagrange_interpolate_pt_loop` (whose runtime precondition — the polynomial-degree
  invariant — holds at entry because the initial polynomial is `1` and at least index `i`
  is a value-skip), `GF16.const_div`, and `PolyConst.mult` are all total under these
  assumptions.

• **Polynomial identity in `GF216[X]`**:
    `listToGF216Poly result.coefficients.val =
        C (pts[i].y.toGF216 *
            (lagrangeDenomProd pts[i].x (pts.take N) 0) ^ (2¹⁶ − 2)) *
          condProdLinearFactors pts[i].x (pts.take N) 0`
  where
  - `condProdLinearFactors pi.x (pts.take N) 0 =
        ∏_{j < N, pts[j].x.value ≠ pi.x.value} (X − C(pts[j].x.toGF216))`
    is the unnormalised Lagrange basis polynomial restricted to the first `N` points and
    using value-equality to identify the skipped index (which always includes `j = i`).
  - `lagrangeDenomProd pi.x (pts.take N) 0 =
        ∏_{j < N, pts[j].x.value ≠ pi.x.value} (pi.x.toGF216 − pts[j].x.toGF216)`
    is the corresponding denominator product.
  - The combined scalar
        `pts[i].y.toGF216 * (lagrangeDenomProd pts[i].x (pts.take N) 0) ^ (2¹⁶ − 2)`
    is exactly `lagrangeScaleGF216 pts[i] (pts.take N)` — the Fermat-style scaling factor
    that becomes `pts[i].y / ∏_{j ≠ i} (pts[i].x − pts[j].x)` when the denominator is
    nonzero (i.e., when the first `N` x-coordinates are pairwise distinct).

The proof composes the postconditions of the four building blocks:

  1. `lagrange_interpolate_pt_loop.loop_spec` (with `j = 0` and the entry-point degree
     bound `0 + countNonSkip pi.x (pts.take N) 0 ≤ N − 1 < N`, obtained from
     `countNonSkip_le_of_skip_exists`), producing
     `listToGF216Poly p.coefficients =
         condProdLinearFactors pi.x (pts.take N) 0 *
           listToGF216Poly initial.coefficients`
     where `listToGF216Poly initial.coefficients = 1` by
     `listToGF216Poly_init_one`, and
     `denominator.toGF216 = 1 * lagrangeDenomProd pi.x (pts.take N) 0`.
  2. `GF16.const_div_spec` for `g := pi.y.const_div denominator`, yielding
     `g.toGF216 = pi.y.toGF216 * denominator.toGF216 ^ (2¹⁶ − 2)`.
  3. `PolyConst.mult_spec` for `result := p.mult g`, yielding
     `listToGF216Poly result.coefficients =
         C g.toGF216 * listToGF216Poly p.coefficients`.

Multiplying through and using `1 * _ = _` yields the stated postcondition.

**Source**: spqr/src/encoding/polynomial.rs (lines 370:4-395:5)
-/
@[step]
theorem lagrange_interpolate_pt_spec
    (N : Usize)
    (pts : Slice Pt)
    (i : Std.Usize)
    (h_N_pos : 0 < N.val)
    (h_i_lt_N : i.val < N.val)
    (h_N_le_pts : N.val ≤ pts.val.length) :
    lagrange_interpolate_pt N pts i ⦃ (result : PolyConst N) =>
      ∀ (hi : i.val < pts.val.length),
        listToGF216Poly result.coefficients.val =
          C ((pts.val.get ⟨i.val, hi⟩).y.toGF216 *
              (lagrangeDenomProd (pts.val.get ⟨i.val, hi⟩).x
                (pts.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
            condProdLinearFactors (pts.val.get ⟨i.val, hi⟩).x
              (pts.val.take N.val) 0 ⦄ := by
  unfold lagrange_interpolate_pt
  step*
  · trace_state
    sorry
  · trace_state
    sorry

end spqr.encoding.polynomial.PolyConst
