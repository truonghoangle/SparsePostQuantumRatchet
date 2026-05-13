/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.Poly.Zero
import Spqr.Specs.Encoding.Gf.GF16.Eq
import Spqr.Specs.Encoding.Gf.GF16.ONE
import Spqr.Specs.Encoding.Gf.GF16.ZERO
import Spqr.Specs.Encoding.Polynomial.Poly.MultXdiffAssignTrailing

/-!
# Spec theorem for `lagrange_interpolate_prepare`: loop body 0

Given a slice of points `pts` and an offset (= `pts.len()`), the function
`Poly::lagrange_interpolate_prepare` builds the polynomial
  `∏_{j=0}^{offset−1} (x − pts[j].x)`
by starting with the constant `1` at position `offset` in the coefficient vector and successively
multiplying the trailing sub-polynomial by `(x − pts[i].x)` for `i = 0, 1, …, offset − 1`.

Concretely, `lagrange_interpolate_prepare(pts)` calls `Poly::zero(pts.len() + 1)`, resizes the
coefficient vector to `offset + 1` entries filled with `GF16::ZERO`, sets `p.coefficients[offset] =
GF16::ONE`, and then runs the `for i in 0..offset` loop driver
`encoding.polynomial.Poly.lagrange_interpolate_prepare_loop`, performing `offset` iterations of the
body function specified below.

Each step of the loop body (this function):

1. Retrieves the next index `i` from the range iterator `0..offset`.
2. If the iterator is exhausted (`none`), returns `done` with the current polynomial — the
   construction is complete.
3. Otherwise, looks up `pi = pts[i]`, computes the start position `i1 = offset − i`, and calls
   `mult_xdiff_assign_trailing(i1, pi.x)` to multiply the trailing sub-polynomial `p[offset−i..]` by
   `(x − pi.x)`, then returns `cont` with the updated iterator and polynomial.

Since GF(2¹⁶) has characteristic 2, subtraction coincides with addition:
  `(x − pts[i].x) = (x + pts[i].x) = (x ⊕ pts[i].x)`

The multiplication `self[start..] *= (x − difference)` is performed by the recurrence:
  `v[j − 1] −= v[j] * difference`  for `j` in `start..l`
where `l = self.coefficients.len()`.

The key invariant maintained by the outer loop is:
- `p.coefficients.len() = offset + 1` (vector length is preserved).
- After `i` iterations, the trailing sub-polynomial `p[offset−i..]` represents `∏_{j=0}^{i−1} (x −
  pts[j].x)`.

**Source**: spqr/src/encoding/polynomial.rs (lines 155:8-159:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf
instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

instance : Inhabited spqr.encoding.polynomial.Pt where
  default := ⟨⟨0#u16⟩, ⟨0#u16⟩⟩


namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop


/--
The range iterator `next` always returns `ok` and either provides the current `start` value (when
`start < end`) or `none` (when `start ≥ end`).  This is the concrete specification for the
`core.ops.range.Range<usize>` iterator used in the Rust `for i in 0..offset` loop.
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
**Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_prepare_loop.body`**:

One step of the polynomial construction `∏_{j=0}^{offset−1} (x − pts[j].x)`.  Given a point slice
`pts`, an offset value (= number of points), a range iterator over `0..offset`, and the current
polynomial `p`, the body processes the next index from the iterator:

• The function always succeeds (no panic) for any valid inputs satisfying the preconditions, since
  `Slice.index_usize`, `Usize` subtraction, and `mult_xdiff_assign_trailing` are total on bounded
  integers within range.
• In the `done` case (iterator exhausted):
    `result = p` (polynomial unchanged) and the iterator is
    exhausted: `¬ (iter.start.val < iter.end.val)`.
• In the `cont` case (index `i` processed):
    - The iterator has advanced by one:
        `iter'.start = iter.start + 1`, `iter'.end = iter.end`.
    - The coefficient vector length is preserved:
        `p'.coefficients.length = p.coefficients.length`.
    - For carry-propagated positions `j` with
      `(offset − iter.start) ≤ j + 1` and
      `j + 1 < p.coefficients.length`:
        `p'.toGF216.coefficients[j] =
            p.toGF216.coefficients[j] −
            p.toGF216.coefficients[j+1] *
              pts[iter.start].x.toGF216`
      where the subtraction on the right-hand side is in
      `GF216 = GaloisField 2 16` (which, in characteristic 2,
      coincides with addition).
    - All other positions are unchanged:
        `p'.coefficients[j]? = p.coefficients[j]?`.

The postcondition propagates the closed-form specification of `mult_xdiff_assign_trailing` (from
`Spqr.Specs.Encoding.Polynomial.Poly.MultXdiffAssignTrailing`) through the body, substituting `start
= offset − i` and `difference = pts[i].x`.  This forms the foundation for the full loop invariant
proved at the loop level.

**Source**: spqr/src/encoding/polynomial.rs (lines 155:8-159:9)
-/
@[step]
theorem body_spec
    (pts : Slice encoding.polynomial.Pt)
    (offset : Std.Usize)
    (iter : core.ops.range.Range Std.Usize)
    (p : encoding.polynomial.Poly)
    (h_end_le_pts : iter.«end».val ≤ pts.val.length)
    (h_end_le_offset : iter.«end».val ≤ offset.val)
    (h_offset_lt_len : offset.val < p.coefficients.val.length) :
    body pts offset iter p ⦃ cf =>
      match cf with
      | ControlFlow.done r =>
          r = p ∧ ¬ (iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, p1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          p1.coefficients.val.length = p.coefficients.val.length ∧
          (∀ (j : Nat),
            offset.val - iter.start.val ≤ j + 1 →
            j + 1 < p.coefficients.val.length →
            ∀ (hj : j < p1.coefficients.val.length),
              (p1.coefficients.val.get ⟨j, hj⟩).toGF216 =
                (p.coefficients.val[j]!).toGF216 -
                (p.coefficients.val[j + 1]!).toGF216 *
                  (pts.val[iter.start.val]!).x.toGF216) ∧
          (∀ (j : Nat),
            ¬(offset.val - iter.start.val ≤ j + 1 ∧
              j + 1 < p.coefficients.val.length) →
            p1.coefficients.val[j]? = p.coefficients.val[j]?) ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext, h_none, h_some⟩ := IteratorRange_next_Usize_post iter
  rw [hnext]; simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]; simp only
    have h_i_lt_pts : iter.start.val < pts.val.length := by omega
    have h_i_lt_offset : iter.start.val < offset.val := by omega
    step*
    all_goals simp_all
  · obtain ⟨h_opt_eq, h_range_eq⟩ := h_none (by omega)
    rw [h_opt_eq]; simp only [WP.spec_ok]
    exact ⟨trivial, by omega⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop

/-!
# Spec theorem for `lagrange_interpolate_prepare`: loop 0

Given a slice of points `pts` and an offset (= `pts.len()`), the function
`Poly::lagrange_interpolate_prepare` builds the polynomial
  `∏_{j=0}^{offset−1} (x − pts[j].x)`
by starting with the constant `1` at position `offset` in the coefficient vector and successively
multiplying the trailing sub-polynomial by `(x − pts[i].x)` for `i = 0, 1, …, offset − 1`.

This file specifies the full loop (the `loop` fixed-point wrapper around the body), providing a
closed-form postcondition that characterises the entire output polynomial after all iterations.  The
per-iteration specification is in
`Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolatePrepareLoopBoby0`.

Concretely, `lagrange_interpolate_prepare(pts)` calls `Poly::zero(pts.len() + 1)`, resizes the
coefficient vector to `offset + 1` entries filled with `GF16::ZERO`, sets `p.coefficients[offset] =
GF16::ONE`, and then runs the `for i in 0..offset` loop driver
`encoding.polynomial.Poly.lagrange_interpolate_prepare_loop`, performing `offset` iterations of the
body function.

Each step of the loop body calls `mult_xdiff_assign_trailing(offset − i, pts[i].x)` to multiply the
trailing sub-polynomial `p[offset−i..]` by `(x − pts[i].x)`, with the carry propagating into the
next lower position.

Since GF(2¹⁶) has characteristic 2, subtraction coincides with addition:
  `(x − pts[i].x) = (x + pts[i].x) = (x ⊕ pts[i].x)`

The key invariant maintained by the outer loop is:
- `p.coefficients.len() = offset + 1` (vector length is preserved).
- `p.coefficients[offset] = GF16::ONE` (leading coefficient unchanged, since
  `mult_xdiff_assign_trailing` never modifies the last position when `len = offset + 1`).
- After `i` iterations, the trailing sub-polynomial `p[offset−i..]` represents `∏_{j=0}^{i−1} (x −
  pts[j].x)`.

**Closed-form postcondition**:

After the loop completes with range `iter.start..iter.end`:

1. The coefficient vector length is preserved:
     `result.coefficients.length = p.coefficients.length`.
2. The leading coefficient (position `offset`) is unchanged:
     `result.coefficients[offset]? = p.coefficients[offset]?`.
3. The leading coefficient at position `offset` is preserved
   under `GF16.toGF216` (the map from the implementation type
   `GF16` to the mathematical field `GF216 = GF(2¹⁶)`):
     `result.toGF216.coefficients[offset] =
        p.toGF216.coefficients[offset]`.
4. All positions outside the modified range
   `[offset − iter.end, offset − 1]` are unchanged:
     `result.coefficients[j]? = p.coefficients[j]?`
   for `j` not in `{k | offset − iter.end ≤ k ∧ k < offset}`.
5. **Trailing polynomial identity** (NEW): For each position
   `m` in the trailing sub-polynomial range
   `[offset − (iter.end − iter.start), offset]`, the coefficient
   at that position in the result matches the `m`-th coefficient
   of the expected trailing polynomial
   `expectedTrailingPoly p.coefficients pts offset iter.start k`,
   which is defined by the recurrence:
     `S₀ = C(p[offset].toGF216)`
     `S_{k+1} = C(p[offset−(k+1)].toGF216) +
                (X − C(pts[iter.start+k].x.toGF216)) · Sₖ`

The correctness of each step relies on the body specification
(`LagrangeInterpolatePrepareLoopBoby0.body_spec`), which guarantees that each call to
`mult_xdiff_assign_trailing` preserves the vector length and only modifies positions in the carry
range `[offset − i − 1, offset − 1]`, leaving the leading coefficient at position `offset` unchanged
(since `offset + 1 = len` means position `offset` is never in the carry range `j + 1 < len`).

**Source**: spqr/src/encoding/polynomial.rs (lines 155:8-159:9)
-/

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop

open Polynomial

private lemma list_get_of_getElem?_eq {T : Type} {xs ys : List T}
    {k : Nat}
    (h : xs[k]? = ys[k]?) (hx : k < xs.length) (hy : k < ys.length) :
    xs.get ⟨k, hx⟩ = ys.get ⟨k, hy⟩ := by
  have h1 : xs[k]? = some (xs.get ⟨k, hx⟩) := List.getElem?_eq_getElem hx
  have h2 : ys[k]? = some (ys.get ⟨k, hy⟩) := List.getElem?_eq_getElem hy
  rw [h1, h2] at h
  exact Option.some_injective _ h

/-!
## Mathematical specification functions

The following definitions capture the mathematical content of the loop: `prodLinearFactors` is the
target product polynomial, and `expectedTrailingPoly` tracks the evolving trailing sub-polynomial
through each iteration of the loop, accounting for the initial coefficients of `p`.
-/

/--
**Product of linear factors** `∏_{j=start}^{stop−1} (X − C(pts[j].x.toGF216))`.

This is the target polynomial that `lagrange_interpolate_prepare` constructs.  It returns `1` when
`start ≥ stop` or `start ≥ pts.length` (empty product).
-/
noncomputable def prodLinearFactors
    (pts : List Pt) (start stop : Nat) : GF216Poly :=
  if h : start < stop ∧ start < pts.length then
    (X - C ((pts.get ⟨start, h.2⟩).x.toGF216)) *
      prodLinearFactors pts (start + 1) stop
  else 1
termination_by stop - start

/--
When `start ≥ stop` or `start ≥ pts.length`, the product is `1` (empty product).
-/
@[simp]
lemma prodLinearFactors_base (pts : List Pt) (start stop : Nat)
    (h : ¬(start < stop ∧ start < pts.length)) :
    prodLinearFactors pts start stop = 1 := by
  unfold prodLinearFactors; rw [dif_neg h]

/-- One-step unfolding of `prodLinearFactors` from the left. -/
lemma prodLinearFactors_step (pts : List Pt) (start stop : Nat)
    (h1 : start < stop) (h2 : start < pts.length) :
    prodLinearFactors pts start stop =
      (X - C ((pts.get ⟨start, h2⟩).x.toGF216)) *
        prodLinearFactors pts (start + 1) stop := by
  conv_lhs => unfold prodLinearFactors
  rw [dif_pos ⟨h1, h2⟩]

/--
One-step unfolding of `prodLinearFactors` from the right (snoc form).  Uses commutativity of
polynomial multiplication.
-/
private lemma prodLinearFactors_snoc_aux (pts : List Pt) (stop : Nat)
    (h2 : stop < pts.length) :
    ∀ d s, s + d = stop → s ≤ stop →
      prodLinearFactors pts s (stop + 1) =
        prodLinearFactors pts s stop *
          (X - C ((pts.get ⟨stop, h2⟩).x.toGF216)) := by
  intro d
  induction d with
  | zero =>
    intro s hs hle
    have hseq : stop = s := by omega
    subst hseq
    rw [prodLinearFactors_step pts stop (stop + 1) (by omega) h2,
        prodLinearFactors_base pts (stop + 1) (stop + 1) (by omega),
        prodLinearFactors_base pts stop stop (by omega)]
    ring
  | succ n ih =>
    intro s hs hle
    rw [prodLinearFactors_step pts s (stop + 1) (by omega) (by omega),
        prodLinearFactors_step pts s stop (by omega) (by omega)]
    rw [ih (s + 1) (by omega) (by omega)]
    ring

lemma prodLinearFactors_snoc (pts : List Pt) (start stop : Nat)
    (h1 : start ≤ stop) (h2 : stop < pts.length) :
    prodLinearFactors pts start (stop + 1) =
      prodLinearFactors pts start stop *
        (X - C ((pts.get ⟨stop, h2⟩).x.toGF216)) :=
  prodLinearFactors_snoc_aux pts stop h2 (stop - start) start (by omega) h1

/-- Evaluation of `prodLinearFactors` at a root is zero. -/
lemma prodLinearFactors_eval_root (pts : List Pt) (start stop : Nat)
    (j : Nat) (hj1 : start ≤ j) (hj2 : j < stop) (hj3 : j < pts.length) :
    (prodLinearFactors pts start stop).eval
      ((pts.get ⟨j, hj3⟩).x.toGF216) = 0 := by
  -- Induction on the number of linear factors (stop - start)
  suffices h : ∀ (d : Nat) (start : Nat), stop - start = d → start ≤ j →
      (prodLinearFactors pts start stop).eval
        ((pts.get ⟨j, hj3⟩).x.toGF216) = 0 from
    h (stop - start) start rfl hj1
  intro d
  induction d with
  | zero => intro start hd; omega
  | succ n ih =>
    intro start hd hj1'
    rw [prodLinearFactors_step pts start stop (by omega) (by omega)]
    simp only [eval_mul]
    by_cases hjs : j = start
    · subst hjs; simp [eval_sub, eval_X, eval_C]
    · have := ih (start + 1) (by omega) (by omega)
      rw [this]; ring

/--
**Expected trailing sub-polynomial** after `k` iterations.

Defined by the recurrence:
  `S₀ = C(p_coeffs[offset]!.toGF216)`
  `S_{k+1} = C(p_coeffs[offset − (k + 1)]!.toGF216) +
             (X − C(pts[iter_start + k]!.x.toGF216)) · Sₖ`

This tracks the compound effect of `k` calls to `mult_xdiff_assign_trailing` on the trailing
sub-polynomial rooted at position `offset`.  After `k` iterations, the sub-polynomial at positions
`[offset − k, …, offset]` equals `expectedTrailingPoly p_coeffs pts offset iter_start k`.
-/
noncomputable def expectedTrailingPoly
    (p_coeffs : List GF16) (pts : List Pt)
    (offset iter_start : Nat) : Nat → GF216Poly
  | 0 => C (p_coeffs[offset]!.toGF216)
  | k + 1 =>
    C (p_coeffs[offset - (k + 1)]!.toGF216) +
    (X - C (pts[iter_start + k]!.x.toGF216)) *
      expectedTrailingPoly p_coeffs pts offset iter_start k

/--
Base case: the expected trailing polynomial after 0 iterations is just the constant
`C(p[offset]!.toGF216)`.
-/
@[simp]
lemma expectedTrailingPoly_zero (p_coeffs : List GF16) (pts : List Pt)
    (offset iter_start : Nat) :
    expectedTrailingPoly p_coeffs pts offset iter_start 0 =
      C (p_coeffs[offset]!.toGF216) := rfl

/-- Step case: one-step unfolding of `expectedTrailingPoly`. -/
lemma expectedTrailingPoly_succ (p_coeffs : List GF16) (pts : List Pt)
    (offset iter_start k : Nat) :
    expectedTrailingPoly p_coeffs pts offset iter_start (k + 1) =
      C (p_coeffs[offset - (k + 1)]!.toGF216) +
      (X - C (pts[iter_start + k]!.x.toGF216)) *
        expectedTrailingPoly p_coeffs pts offset iter_start k := rfl

/--
**Bridge lemma**: When the initial polynomial has `p[offset] = ONE` and `p[j] = ZERO` for `j <
offset`, the expected trailing polynomial collapses to `prodLinearFactors`.
-/
lemma expectedTrailingPoly_eq_prodLinearFactors
    (p_coeffs : List GF16) (pts : List Pt) (offset : Nat)
    (h_leading : p_coeffs[offset]!.toGF216 = 1)
    (h_zeros : ∀ j, j < offset → p_coeffs[j]!.toGF216 = 0)
    (h_pts : offset ≤ pts.length) :
    ∀ k, k ≤ offset →
      expectedTrailingPoly p_coeffs pts offset 0 k =
        prodLinearFactors pts 0 k := by
  intro k hk
  induction k with
  | zero =>
    rw [expectedTrailingPoly_zero, prodLinearFactors_base pts 0 0 (by omega),
        h_leading, map_one]
  | succ n ih =>
    rw [expectedTrailingPoly_succ]
    have hn_le : n ≤ offset := by omega
    rw [ih hn_le]
    have h_zero : p_coeffs[offset - (n + 1)]!.toGF216 = 0 := by
      apply h_zeros; omega
    rw [h_zero, map_zero, zero_add]
    have h_n_lt : n < pts.length := by omega
    rw [prodLinearFactors_snoc pts 0 n (by omega) h_n_lt]
    conv_lhs =>
      rw [show pts[0 + n]!.x.toGF216 = (pts.get ⟨n, h_n_lt⟩).x.toGF216 from by
        congr 1; congr 1; rw [Nat.zero_add]; exact getElem!_pos pts n h_n_lt]
    ring

/-- Coefficient 0 of `C a + (X - C b) * P` equals `a - b * P.coeff 0`. -/
private lemma coeff_zero_C_add_X_sub_C_mul {R : Type*} [CommRing R]
    (a b : R) (P : R[X]) :
    (C a + (X - C b) * P).coeff 0 = a - b * P.coeff 0 := by
  rw [sub_mul, coeff_add, coeff_sub, coeff_C_zero, coeff_X_mul_zero, coeff_C_mul]
  ring

/--
For any `n`, coefficient `n + 1` of `C a + (X - C b) * P` equals
    `P.coeff n - b * P.coeff (n + 1)`.
-/
private lemma coeff_succ_C_add_X_sub_C_mul {R : Type*} [CommRing R]
    (a b : R) (P : R[X]) (n : ℕ) :
    (C a + (X - C b) * P).coeff (n + 1) = P.coeff n - b * P.coeff (n + 1) := by
  rw [sub_mul, coeff_add, coeff_sub, coeff_X_mul, coeff_C_mul]
  have : (C a).coeff (n + 1) = 0 := by rw [coeff_C]; exact if_neg (by omega)
  rw [this]; ring

/-- Coefficients of `expectedTrailingPoly` beyond degree `k` are zero. -/
private lemma expectedTrailingPoly_coeff_eq_zero
    (p_coeffs : List GF16) (pts : List Pt)
    (offset iter_start k n : Nat) (hn : k < n) :
    (expectedTrailingPoly p_coeffs pts offset iter_start k).coeff n = 0 := by
  induction k generalizing n with
  | zero =>
    simp only [expectedTrailingPoly_zero, coeff_C]
    exact if_neg (by omega)
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n' =>
      rw [expectedTrailingPoly_succ, coeff_succ_C_add_X_sub_C_mul,
          ih n' (by omega), ih (n' + 1) (by omega)]
      ring

/--
**Closed-form postcondition for `encoding.polynomial.Poly.lagrange_interpolate_prepare_loop`**:

The full loop constructing `∏_{j=0}^{offset−1} (x − pts[j].x)`.  Starting from a range
`iter.start..iter.end`, a point slice `pts`, and a polynomial `p` with `p.coefficients.length =
offset + 1`, the loop processes indices `i = iter.start, iter.start + 1, …, iter.end − 1` — at each
step calling `mult_xdiff_assign_trailing(offset − i, pts[i].x)` — and returns a polynomial `result`
satisfying:

• **Length preserved**: `result.coefficients.length = p.coefficients.length`.
• **Leading coefficient unchanged**:
    `result.coefficients[offset]? = p.coefficients[offset]?`.
• **leading.toGF216 coefficient preserved**:
    `result.toGF216.coefficients[offset] =
       p.toGF216.coefficients[offset]`
  (the leading coefficient is unchanged under the map
   `GF16.toGF216 : GF16 → GF(2¹⁶)` from the implementation type
   to the mathematical field).
• **Frame for unmodified positions**:
    `result.coefficients[j]? = p.coefficients[j]?`
  for all positions `j` not in the modified range
  `{k | offset − iter.end ≤ k ∧ k < offset}`.
• **Trailing polynomial identity** (property 5):
    For each `m ≤ iter.end − iter.start` and valid position
    `offset − (iter.end − iter.start) + m`, the coefficient at
    that position matches the `m`-th coefficient of
    `expectedTrailingPoly p.coefficients pts offset iter.start
      (iter.end − iter.start)`.
    This characterises the modified positions by expressing the
    compound effect of all iterations as a single polynomial
    recurrence.

The loop invariant tracks which iterations have been processed: after iterating indices `iter.start,
…, k−1`, the sub-polynomial `result[offset−(k−iter.start)..]` represents `∏_{j=iter.start}^{k−1} (x
− pts[j].x)`, the leading coefficient at position `offset` remains unchanged (as
`mult_xdiff_assign_trailing` never writes past position `len − 2 = offset − 1`), the vector length
is unchanged, and all positions below `offset − k` retain their original values.

**Source**: spqr/src/encoding/polynomial.rs (lines 155:8-159:9)
-/
@[step]
theorem loop_spec
    (pts : Slice Pt)
    (offset : Usize)
    (iter : core.ops.range.Range Usize)
    (p : Poly)
    (h_end_le_pts : iter.«end».val ≤ pts.val.length)
    (h_end_le_offset : iter.«end».val ≤ offset.val)
    (h_len_eq : p.coefficients.val.length = offset.val + 1)
    (h_le : iter.start.val ≤ iter.«end».val)
    (h_start_zero : iter.start.val = 0) :
    lagrange_interpolate_prepare_loop
      iter pts p offset ⦃ (result : Poly) =>
      result.coefficients.val.length = p.coefficients.val.length ∧
      result.coefficients.val[offset.val]? =
        p.coefficients.val[offset.val]? ∧
      (∀ (hoff : offset.val < result.coefficients.val.length),
        (result.coefficients.val.get ⟨offset.val, hoff⟩).toGF216 =
          (p.coefficients.val[offset.val]!).toGF216) ∧
      (∀ (j : Nat),
        ¬(offset.val - iter.«end».val ≤ j ∧ j < offset.val) →
        result.coefficients.val[j]? = p.coefficients.val[j]?) ∧
      -- Property 5: trailing polynomial identity
      (∀ (m : Nat),
        m ≤ iter.«end».val - iter.start.val →
        ∀ (hpos : offset.val - (iter.«end».val - iter.start.val) + m <
                    result.coefficients.val.length),
          GF16.toGF216
            (result.coefficients.val.get
              ⟨offset.val - (iter.«end».val - iter.start.val) + m, hpos⟩) =
            (expectedTrailingPoly p.coefficients.val pts.val offset.val
              iter.start.val (iter.«end».val - iter.start.val)).coeff m) ⦄ := by
  unfold spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop
  apply loop.spec_decr_nat
    (measure := fun (st : core.ops.range.Range Std.Usize ×
                        encoding.polynomial.Poly) =>
                  st.1.«end».val - st.1.start.val)
    (inv := fun (st : core.ops.range.Range Std.Usize ×
                     encoding.polynomial.Poly) =>
        st.1.«end» = iter.«end» ∧
        iter.start.val ≤ st.1.start.val ∧
        st.1.start.val ≤ iter.«end».val ∧
        st.2.coefficients.val.length = p.coefficients.val.length ∧
        st.2.coefficients.val[offset.val]? =
          p.coefficients.val[offset.val]? ∧
        (∀ (hoff : offset.val < st.2.coefficients.val.length),
          (st.2.coefficients.val.get ⟨offset.val, hoff⟩).toGF216 =
            (p.coefficients.val[offset.val]!).toGF216) ∧
        (∀ (j : Nat),
          ¬(offset.val - st.1.start.val ≤ j ∧ j < offset.val) →
          st.2.coefficients.val[j]? = p.coefficients.val[j]?) ∧
        -- Invariant for trailing polynomial identity
        (∀ (m : Nat),
          m ≤ st.1.start.val - iter.start.val →
          ∀ (hpos : offset.val - (st.1.start.val - iter.start.val) + m <
                      st.2.coefficients.val.length),
            GF16.toGF216
              (st.2.coefficients.val.get
                ⟨offset.val - (st.1.start.val - iter.start.val) + m, hpos⟩) =
              (expectedTrailingPoly p.coefficients.val pts.val offset.val
                iter.start.val (st.1.start.val - iter.start.val)).coeff m))
  · rintro ⟨iter', p'⟩ ⟨h_end', h_ge', h_le', h_len', h_off', h_gf16_off', h_frame', h_trail'⟩
    simp only [] at h_end' h_ge' h_le' h_len' h_off' h_gf16_off' h_frame' h_trail' ⊢
    have h_end_le_pts' : iter'.«end».val ≤ pts.val.length := by grind
    have h_end_le_offset' : iter'.«end».val ≤ offset.val := by grind
    have h_offset_lt_len' : offset.val < p'.coefficients.val.length := by omega
    step*
    split
    · -- done: iterator exhausted, result = current polynomial
      rename_i r_post
      simp only [] at r_post
      obtain ⟨h_eq, h_nlt⟩ := r_post
      subst h_eq
      have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
      refine ⟨h_len', h_off', h_gf16_off', fun j hj => ?_, fun m hm hpos => ?_⟩
      · apply h_frame'
        intro ⟨h1, h2⟩
        exact hj ⟨by omega, h2⟩
      · have h_iters_eq : iter'.start.val - iter.start.val =
            iter.«end».val - iter.start.val := by omega
        rw [h_iters_eq] at h_trail'
        exact h_trail' m hm hpos
    · -- cont: one iteration processed
      rename_i r_post
      simp only [] at r_post
      obtain ⟨h_lt, h_start1, h_end1, h_v1len, h_modified, h_frame⟩ := r_post
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- end preserved
        rw [h_end1]; exact h_end'
      · -- start lower bound
        omega
      · -- start upper bound
        grind
      · -- length preserved
        omega
      · -- [offset]? preserved via body frame
        have h_off_frame := h_frame offset.val (by
          push_neg; intro _; omega)
        rw [h_off_frame, h_off']
      · -- leading.toGF216 coefficient preserved
        intro hoff
        have h_off_frame := h_frame offset.val (by
          push_neg; intro _; omega)
        have hoff_p' : offset.val < p'.coefficients.val.length := by omega
        have h_get_eq := list_get_of_getElem?_eq h_off_frame hoff hoff_p'
        simp only [List.get_eq_getElem] at h_get_eq ⊢
        rw [h_get_eq]
        exact h_gf16_off' hoff_p'
      · -- Frame: positions outside modified range unchanged
        intro j hj
        have h_body_fr : (Prod.snd r_post).coefficients.val[j]? =
            p'.coefficients.val[j]? := by
          apply h_frame
          intro ⟨ha, hb⟩
          exact hj ⟨by omega, by omega⟩
        have h_inv_fr : p'.coefficients.val[j]? =
            p.coefficients.val[j]? := by
          apply h_frame'
          intro ⟨ha, hb⟩
          exact hj ⟨by omega, hb⟩
        rw [h_body_fr, h_inv_fr]
      · -- Trailing polynomial identity maintenance
        intro m hm hpos
        set k := iter'.start.val - iter.start.val with hk_def
        -- k+1 = new number of iterations
        have hk1 : (Prod.fst r_post).start.val - iter.start.val = k + 1 := by omega
        have hpos' : offset.val - (k + 1) + m <
            (Prod.snd r_post).coefficients.val.length := by omega
        have hget_eq : (Prod.snd r_post).coefficients.val.get
            ⟨offset.val - ((Prod.fst r_post).start.val - iter.start.val) + m, hpos⟩ =
            (Prod.snd r_post).coefficients.val.get
            ⟨offset.val - (k + 1) + m, hpos'⟩ := by
          congr 1; exact Fin.ext (by grind)
        rw [hget_eq, hk1]
        rw [expectedTrailingPoly_succ]
        -- Position index: offset - (k+1) + m
        set pos := offset.val - (k + 1) + m with hpos_def
        by_cases hm0 : m = 0
        · -- m = 0: new position entering the trailing range
          subst hm0
          -- pos = offset.val - (k + 1) + 0; keep it as-is for now
          rw [coeff_zero_C_add_X_sub_C_mul]
          -- Body spec: result[pos] = p'[pos]! - p'[pos+1]! * pts[iter'.start]!.x
          have hmod := h_modified pos (by omega) (by omega) hpos'
          rw [hmod]
          -- Simplify: pos + 1 = offset.val - k
          have hidx : pos + 1 = offset.val - k := by omega
          rw [hidx]
          -- Frame: p'[pos] is unchanged from original p
          have hfr := h_frame' pos (by
            intro ⟨h1, _⟩
            have hiter_eq : iter'.start.val = k := by
              rw [h_start_zero] at hk_def; omega
            rw [hiter_eq] at h1; omega)
          have hfr_val : p'.coefficients.val[pos]! =
              p.coefficients.val[pos]! := by
            have hp' : pos < p'.coefficients.val.length := by omega
            have hp : pos < p.coefficients.val.length := by omega
            rw [getElem!_pos p'.coefficients.val pos hp',
                getElem!_pos p.coefficients.val pos hp]
            exact list_get_of_getElem?_eq hfr hp' hp
          rw [hfr_val]
          -- Trailing identity at m=0: p'[offset-k].toGF216 = S_k.coeff 0
          have htr := h_trail' 0 (by omega)
            (show offset.val - k + 0 < p'.coefficients.val.length by omega)
          simp only [Nat.add_zero] at htr
          have htr_val : (p'.coefficients.val[offset.val - k]!).toGF216 =
              (expectedTrailingPoly p.coefficients.val pts.val
                offset.val iter.start.val k).coeff 0 := by
            rw [getElem!_pos p'.coefficients.val (offset.val - k)
              (show offset.val - k < p'.coefficients.val.length by omega)]
            exact htr
          rw [htr_val]
          -- Align pts index: iter'.start.val = iter.start.val + k
          have hiter : iter'.start.val = iter.start.val + k := by omega
          rw [hiter]
          -- pos = offset - (k+1) + 0 needs to match offset - (k+1)
          have : pos = offset.val - (k + 1) := by omega
          rw [this]
          ring
        · -- m ≥ 1: existing positions in the trailing range
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          rw [coeff_succ_C_add_X_sub_C_mul]
          -- pos = offset - (k+1) + (m'+1) = offset - k + m'
          have hpos_simp : pos = offset.val - k + m' := by omega
          by_cases hm'k : m' + 1 ≤ k
          · -- m' + 1 ≤ k: position in body's modified range
            -- Body spec at j = offset - k + m'
            have hj_len : offset.val - k + m' <
                (Prod.snd r_post).coefficients.val.length := by omega
            have hmod := h_modified (offset.val - k + m')
              (by omega) (by omega) hj_len
            -- Convert get index from pos to offset - k + m'
            have hget_conv : (Prod.snd r_post).coefficients.val.get ⟨pos, hpos'⟩ =
                (Prod.snd r_post).coefficients.val.get
                  ⟨offset.val - k + m', hj_len⟩ := by
              congr 1; exact Fin.ext (by omega)
            rw [hget_conv, hmod]
            -- Trail at m': p'[offset - k + m'] = S_k.coeff m'
            have hlen_m' : offset.val - k + m' < p'.coefficients.val.length := by omega
            have htr_m' := h_trail' m' (by omega) hlen_m'
            have htr_m'_val : (p'.coefficients.val[offset.val - k + m']!).toGF216 =
                (expectedTrailingPoly p.coefficients.val pts.val
                  offset.val iter.start.val k).coeff m' := by
              rw [getElem!_pos p'.coefficients.val (offset.val - k + m') hlen_m']
              exact htr_m'
            -- Trail at m'+1: p'[offset - k + (m'+1)] = S_k.coeff (m'+1)
            have hlen_m1 : offset.val - k + (m' + 1) < p'.coefficients.val.length := by omega
            have htr_m1 := h_trail' (m' + 1) (by omega) hlen_m1
            have htr_m1_val : (p'.coefficients.val[offset.val - k + m' + 1]!).toGF216 =
                (expectedTrailingPoly p.coefficients.val pts.val
                  offset.val iter.start.val k).coeff (m' + 1) := by
              rw [getElem!_pos p'.coefficients.val (offset.val - k + m' + 1)
                (show offset.val - k + m' + 1 < p'.coefficients.val.length by omega)]
              have hconv : p'.coefficients.val.get
                  ⟨offset.val - k + m' + 1,
                   show offset.val - k + m' + 1 < p'.coefficients.val.length by omega⟩ =
                  p'.coefficients.val.get ⟨offset.val - k + (m' + 1), hlen_m1⟩ := by
                congr 1
              grind
            rw [htr_m'_val, htr_m1_val]
            -- Align pts index
            have hiter : iter'.start.val = iter.start.val + k := by omega
            rw [hiter]
            ring
          · -- m' = k: position is offset (not in body's modified range)
            have hm'_eq : m' = k := by omega
            subst hm'_eq
            -- pos = offset
            have hpos_off : pos = offset.val := by omega
            -- Body frame: result[offset]? = p'[offset]?
            have hfr := h_frame offset.val (by push_neg; intro _; omega)
            -- Convert get index from pos to offset
            have hoff_len : offset.val <
                (Prod.snd r_post).coefficients.val.length := by omega
            have hget_conv : (Prod.snd r_post).coefficients.val.get ⟨pos, hpos'⟩ =
                (Prod.snd r_post).coefficients.val.get
                  ⟨offset.val, hoff_len⟩ := by
              congr 1; exact Fin.ext (by omega)
            rw [hget_conv]
            -- result[offset] = p'[offset] via body frame
            have hoff_len_r : offset.val <
                (Prod.snd r_post).coefficients.val.length := by omega
            have hoff_len_p : offset.val < p'.coefficients.val.length := by omega
            have hoff_eq : (Prod.snd r_post).coefficients.val[offset.val]! =
                p'.coefficients.val[offset.val]! := by
              rw [getElem!_pos (Prod.snd r_post).coefficients.val offset.val hoff_len_r,
                  getElem!_pos p'.coefficients.val offset.val hoff_len_p]
              exact list_get_of_getElem?_eq hfr hoff_len_r hoff_len_p
            have hget_to_bang : ((Prod.snd r_post).coefficients.val.get
                ⟨offset.val, hoff_len⟩).toGF216 =
                ((Prod.snd r_post).coefficients.val[offset.val]!).toGF216 := by
              congr 1
              exact (getElem!_pos (Prod.snd r_post).coefficients.val offset.val hoff_len).symm
            rw [hget_to_bang, hoff_eq]
            -- Trail at k: p'[offset] = S_k.coeff k
            have htr_k := h_trail' k (by omega)
              (show offset.val - k + k < p'.coefficients.val.length by omega)
            have htr_k_val : (p'.coefficients.val[offset.val]!).toGF216 =
                (expectedTrailingPoly p.coefficients.val pts.val
                  offset.val iter.start.val k).coeff k := by
              rw [getElem!_pos p'.coefficients.val offset.val hoff_len_p]
              have hconv : p'.coefficients.val.get ⟨offset.val, hoff_len_p⟩ =
                  p'.coefficients.val.get
                    ⟨offset.val - k + k,
                     show offset.val - k + k < p'.coefficients.val.length by omega⟩ := by
                congr 1; exact Fin.ext (by grind)
              grind
            rw [htr_k_val]
            -- S_k.coeff (k + 1) = 0 since degree ≤ k
            rw [expectedTrailingPoly_coeff_eq_zero _ _ _ _ _ _ (by omega : k < k + 1)]
            ring
      · -- measure decreases
        grind
  · refine ⟨rfl, le_refl _, h_le, rfl, rfl, ?_, ?_, ?_⟩
    · intro hoff
      congr 1
      exact (getElem!_pos p.coefficients.val offset.val hoff).symm
    · intro _ _; rfl
    · -- Initial trailing polynomial: k = 0, only m = 0
      intro m hm hpos
      have hm0 : m = 0 := by grind
      subst hm0
      simp only [Nat.sub_self,  expectedTrailingPoly_zero,
                 coeff_C_zero]
      congr 1
      exact (getElem!_pos p.coefficients.val offset.val (by omega)).symm

end spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop

/-!
# Spec theorem for
`spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::lagrange_interpolate_prepare`

Given a slice of evaluation points `pts`, the function `Poly::lagrange_interpolate_prepare`
constructs the product polynomial
  `∏_{j=0}^{offset−1} (x − pts[j].x)`
where `offset = pts.len()`, returning a `Poly` of degree `offset` with `offset + 1` coefficients.

Concretely the function proceeds as follows:

1. **Allocate**: `p = Poly::zero(pts.len() + 1)` creates an empty coefficient vector with the given
   capacity hint.
2. **Resize**: `p.coefficients.resize(pts.len() + 1, GF16::ZERO)` fills the vector with `offset + 1`
   zero entries.
3. **Set leading coefficient**: `p.coefficients[offset] = GF16::ONE` places the leading `1` at
   position `offset` (the highest degree), representing the monic polynomial `x^0 = 1` in the
   trailing sub-polynomial view.
4. **Loop** (`for i in 0..offset`): at each step calls `p.mult_xdiff_assign_trailing(offset − i,
   pts[i].x)` to multiply the trailing sub-polynomial by `(x − pts[i].x)`, propagating one carry
   coefficient downward.
5. **Assert**: `debug_assert_eq!(p.coefficients[pts.len()], GF16::ONE)` — the loop preserves the
   leading coefficient at position `offset`.

Since GF(2¹⁶) has characteristic 2, subtraction coincides with addition:
  `(x − pts[i].x) = (x + pts[i].x) = (x ⊕ pts[i].x)`

The key postconditions of the function are:

• **Length**: `result.coefficients.length = pts.length + 1`.
• **Leading coefficient**: `result.coefficients[pts.length] = GF16::ONE`.
• **Polynomial identity**:
    `result.toGF216Poly = prodLinearFactors pts.val 0 pts.val.length`
  i.e. the result represents `∏_{j=0}^{pts.length−1} (X − C(pts[j].x.toGF216))`.
• **Root property**: The result polynomial evaluates to zero at each `pts[j].x`.

The leading-coefficient invariant is maintained by the loop (as proved in
`LagrangeInterpolatePrepareLoop0.loop_spec`): the loop body calls `mult_xdiff_assign_trailing` which
never modifies position `offset` (the last position in the vector), so the `ONE` placed there before
the loop is still present after the loop, and the `debug_assert_eq!` always passes.

The on-target Rust implementation may dispatch to hardware carry-less multiplication instructions
(`PCLMULQDQ` / `PMULL`) on x86/x86_64 and aarch64 when the corresponding CPU feature is detected;
the extracted Lean version contains only the unaccelerated fallback.

**Source**: spqr/src/encoding/polynomial.rs (lines 144:4-163:5)
-/

namespace spqr.encoding.polynomial.Poly

open encoding.gf.GF16
open lagrange_interpolate_prepare_loop (prodLinearFactors expectedTrailingPoly
  prodLinearFactors_eval_root expectedTrailingPoly_eq_prodLinearFactors
  prodLinearFactors_base prodLinearFactors_step
  expectedTrailingPoly_coeff_eq_zero)

open Polynomial in
/--
Coefficients of `prodLinearFactors` beyond degree `stop − start` are zero.  This is the degree bound
for the product of linear factors, proved by induction on the number of factors.
-/
private lemma prodLinearFactors_coeff_eq_zero_high
    (pts : List Pt) (start stop m : Nat) (hm : stop - start < m) :
    (prodLinearFactors pts start stop).coeff m = 0 := by
  suffices h : ∀ d start stop m, stop - start = d → d < m →
      (prodLinearFactors pts start stop).coeff m = 0 from
    h (stop - start) start stop m rfl hm
  intro d
  induction d with
  | zero =>
    intro start stop m hd hm'
    have : ¬(start < stop ∧ start < pts.length) := by omega
    rw [prodLinearFactors_base _ _ _ this, coeff_one]
    exact if_neg (by omega)
  | succ n ih =>
    intro start stop m hd hm'
    by_cases h : start < stop ∧ start < pts.length
    · rw [prodLinearFactors_step _ _ _ h.1 h.2]
      cases m with
      | zero => omega
      | succ m' =>
        rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul,
            ih (start + 1) stop (m' + 1) (by omega) (by omega),
            ih (start + 1) stop m' (by omega) (by omega)]
        ring
    · rw [prodLinearFactors_base _ _ _ h, coeff_one]
      exact if_neg (by omega)

/--
**Indexed read after `List.set` at the same index** (using `[·]!`). If `n < l.length`, then `(l.set
n x)[n]! = x`.  This is a local replacement for `List.getElem!_set_self` (which we do not use).
-/
private lemma list_getElem_bang_set_self {α : Type*} [Inhabited α]
    (l : List α) (n : Nat) (x : α) (hn : n < l.length) :
    (l.set n x)[n]! = x := by
  have h : n < (l.set n x).length := by rw [List.length_set]; exact hn
  rw [getElem!_pos (l.set n x) n h, List.getElem_set_self]

/--
If all coefficients of a list, interpreted via `GF16.toGF216`, match those of a polynomial `q` at
in-range positions, and `q` has zero coefficients beyond the list length, then `listToGF216Poly cs =
q`.
-/
private lemma listToGF216Poly_eq_of_coeffs
    (cs : List GF16) (q : GF216Poly)
    (h_in : ∀ (m : Nat) (hm : m < cs.length),
      (cs.get ⟨m, hm⟩).toGF216 = q.coeff m)
    (h_out : ∀ m, cs.length ≤ m → q.coeff m = 0) :
    listToGF216Poly cs = q := by
  ext m
  rw [listToGF216Poly_coeff]
  split
  · rename_i hm; exact h_in m hm
  · rename_i hm; push_neg at hm; exact (h_out m hm).symm

/--
**Spec theorem for
`spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::lagrange_interpolate_prepare`**:

• The function always succeeds (no panic) for any point slice `pts` satisfying the precondition
  `pts.length + 1 ≤ Usize.max`, since all arithmetic operations stay within bounds, `Vec.resize` is
  total, and the loop driver `lagrange_interpolate_prepare_loop` is total on bounded indices.
• The resulting coefficient vector has length `pts.length + 1`:
    `result.coefficients.length = pts.length + 1`.
• The leading coefficient at position `pts.length` is `GF16::ONE`:
    `result.coefficients[pts.length]? = some GF16.ONE`.
  This is the `debug_assert_eq!` that the Rust source checks at
  line 161.
• The leading coefficient maps to the multiplicative identity
  in `GF216 = GF(2¹⁶)` under `GF16.toGF216`:
    `result.toGF216.coefficients[pts.length] = 1`.
  This follows from the loop preserving the leading coefficient
  (proved in `loop_spec`) and the fact that `ONE.toGF216 = 1`
  (proved in `Spqr.Specs.Encoding.Gf.GF16.ONE`).
• For each position `m ≤ pts.length`, the coefficient at position `m` in the result matches the
  `m`-th coefficient of `prodLinearFactors pts.val 0 pts.val.length` under `GF16.toGF216`. This is
  the coefficient-level polynomial identity, derived from the loop's trailing polynomial identity
  (property 5 of `loop_spec`) and the bridge lemma `expectedTrailingPoly_eq_prodLinearFactors`.
• The mathematical interpretation of the result polynomial equals
  the product of linear factors:
    `result.toGF216Poly = prodLinearFactors pts.val 0 pts.val.length`
  i.e. the result represents
  `∏_{j=0}^{pts.length−1} (X − C(pts[j].x.toGF216))`.
  This follows from the coefficient-level identity at all positions
  within the vector, combined with the degree bound showing that
  `prodLinearFactors` has no coefficients beyond degree
  `pts.length`.

**Source**: spqr/src/encoding/polynomial.rs (lines 144:4-163:5)
-/
@[step]
theorem lagrange_interpolate_prepare_spec
    (pts : Slice Pt)
    (h_len : pts.val.length + 1 ≤ Std.Usize.max) :
    lagrange_interpolate_prepare pts
      ⦃ (result : Poly) =>
      result.coefficients.val.length = pts.val.length + 1 ∧
      result.coefficients.val[pts.val.length]? =
        some ONE ∧
      (∀ (hoff : pts.val.length < result.coefficients.val.length),
        (result.coefficients.val.get ⟨pts.val.length, hoff⟩).toGF216 = 1) ∧
      -- Property 4: coefficient-level polynomial identity
      (∀ (m : Nat),
        m ≤ pts.val.length →
        ∀ (hpos : m < result.coefficients.val.length),
          (result.coefficients.val.get ⟨m, hpos⟩).toGF216 =
            (prodLinearFactors pts.val 0 pts.val.length).coeff m) ∧
      -- Property 5: mathematical polynomial identity
      result.toGF216Poly = prodLinearFactors pts.val 0 pts.val.length ⦄ := by
  unfold lagrange_interpolate_prepare
  step*
  · simp_all [encoding.gf.GF16.Insts.CoreCloneClone.clone]
  -- Bridge: connect expectedTrailingPoly to prodLinearFactors
  · simp_all
  · simp_all
  · simp_all
  · simp_all only [Order.add_one_le_iff, Usize.ofNatCore_val_eq, List.resize_length,
    lt_add_iff_pos_right, zero_lt_one, getElem!_pos, alloc.vec.Vec.set_val_eq, List.length_set,
    getElem?_pos, List.getElem_set_self, Option.some.injEq, List.get_eq_getElem, ONE_toGF216,
    imp_self, tsub_self, zero_le, true_and, not_lt, tsub_zero, zero_add, Order.lt_add_one_iff,
    forall_true_left, ONE_value, iff_true, forall_const]
    have h_bridge : expectedTrailingPoly
        ((p.coefficients.val.resize (pts.val.length + 1) ZERO).set pts.val.length ONE)
        pts.val pts.val.length 0 pts.val.length =
      prodLinearFactors pts.val 0 pts.val.length := by
      apply expectedTrailingPoly_eq_prodLinearFactors
      · have hlen : pts.val.length <
          (p.coefficients.val.resize (pts.val.length + 1) ZERO).length := by
          unfold List.resize
          simp
          grind
        rw [list_getElem_bang_set_self _ _ _ hlen, ONE_toGF216]
      · intro j hj
        have hj_lt : j < (p.coefficients.val.resize (pts.val.length + 1) ZERO).length := by
          unfold List.resize; simp; omega
        have h_p_coeff_zero : ∀ k (hk : k < p.coefficients.val.length),
            (p.coefficients.val.get ⟨k, hk⟩).toGF216 = 0 := by
          intro k hk
          have h0 : (p.toGF216Poly).coeff k = 0 := by rw [p_post]; simp
          simp only [Poly.toGF216Poly, listToGF216Poly_coeff, hk, ↓reduceDIte] at h0
          exact h0
        unfold List.resize at hj_lt ⊢
        simp only [Nat.zero_le, ge_iff_le, ↓reduceIte] at hj_lt ⊢
        by_cases hk : j < p.coefficients.val.length
        · -- j within original: in the take part
          have hj_take : j < (p.coefficients.val.take (pts.val.length + 1)).length := by
            simp; omega
          grind
        · -- j in padded range: in the replicate part
          push_neg at hk
          have htake_len_le : (p.coefficients.val.take (pts.val.length + 1)).length ≤ j := by
            rw [List.length_take]; omega
          have hrepl_bnd : j - (p.coefficients.val.take (pts.val.length + 1)).length <
              pts.val.length + 1 - p.coefficients.val.length := by
            rw [List.length_take]; omega
          have hj_ne : Nat.not_eq pts.val.length j := by
            simp [Nat.not_eq]; omega
          rw [List.getElem!_set_ne _ pts.val.length j ONE hj_ne,
              List.getElem!_append_right
                (p.coefficients.val.take (pts.val.length + 1))
                (List.replicate (pts.val.length + 1 - p.coefficients.val.length) ZERO)
                j htake_len_le,
              List.getElem!_replicate ZERO hrepl_bnd, ZERO_toGF216]
      · exact le_refl _
      · exact le_refl _
    constructor
    · intro m hm
      rw [h_bridge]
    · change listToGF216Poly p1.coefficients.val =
        prodLinearFactors pts.val 0 pts.val.length
      apply listToGF216Poly_eq_of_coeffs
      · intro m hm
        simp only [List.get_eq_getElem]
        have hm_le : m ≤ pts.val.length := by omega
        rw [p1_post5 m hm_le, h_bridge]
      · intro m hm
        exact prodLinearFactors_coeff_eq_zero_high _ _ _ _ (by omega)

end spqr.encoding.polynomial.Poly
