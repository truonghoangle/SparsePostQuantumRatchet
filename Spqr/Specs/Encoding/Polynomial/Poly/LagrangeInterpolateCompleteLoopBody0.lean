/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Gf.GF16.Eq
import Spqr.Specs.Encoding.Gf.GF16.Sub
import Spqr.Specs.Encoding.Gf.GF16.MulAssign
/-! # Spec Theorem for `lagrange_interpolate_complete`: loop body 0

Specification and proof for
`spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0.body`,
which implements one iteration step of the denominator accumulation
in Lagrange interpolation over GF(2¹⁶).

Given a distinguished point `pi = pts[i]` and a running accumulator
`denominator`, the full loop 0 computes the product
  `denominator_final = ∏_{j : pts[j].x ≠ pi.x} (pi.x - pts[j].x)`
by iterating over all points `pj` in `pts`.  This denominator is
then used to form the Lagrange scaling factor
  `scale = pi.y / denominator_final`
which ensures that the interpolating polynomial `f` satisfies
`f(pi.x) = pi.y` for the distinguished point and `f(pj.x) = 0`
for all other points.

Each step of the loop body:

1. Retrieves the next point `pj` from the slice iterator.
2. If the iterator is exhausted (`none`), returns `done` with
   the current `(pi, denominator)` pair — the accumulation is
   complete.
3. If `pi.x = pj.x`, returns `cont` with the denominator
   unchanged — this is the `i = j` case where the point is
   skipped.
4. If `pi.x ≠ pj.x`, computes `g = pi.x - pj.x` and updates
   `denominator ← denominator * g`, then returns `cont` with
   the updated denominator.

In GF(2¹⁶) (characteristic 2), subtraction coincides with
addition:
  `pi.x - pj.x = pi.x + pj.x = pi.x ⊕ pj.x`

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.polynomial

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0

/-
natural language description:

• Takes a distinguished point `pi : Pt` (the Lagrange interpolation
  target), a slice iterator `iter` over the full point set, and the
  current `denominator : GF16` accumulator (initialized to
  `GF16::ONE` before the first call).
• Calls `iter.next()` to retrieve the next point `pj`.
• If the iterator is exhausted (`none`), returns
  `done (pi, denominator)` — the loop terminates with the final
  accumulated denominator.
• If a point `pj` is obtained (`some pj`):
  – If `pi.x == pj.x` (same x-coordinate), returns
    `cont (iter', denominator)` — skips this point since it is
    the interpolation target itself (the `i = j` case).
  – If `pi.x ≠ pj.x`, computes `g = pi.x - pj.x` and updates
    `denominator' = denominator * g`, then returns
    `cont (iter', denominator')`.

natural language specs:

• The function always succeeds (no panic) for any valid inputs,
  since `PartialEq<GF16>`, `Sub<GF16>`, and `MulAssign<GF16>`
  are total operations on bounded integers.
• In the `done` case, the point `pi` and the denominator are
  returned unchanged — the loop exits with the final accumulator.
• In the `cont` case, the denominator is either unchanged
  (when `pi.x = pj.x`, i.e. the self-point skip) or has been
  multiplied by `(pi.x - pj.x)` in GF(2¹⁶).
• The loop body preserves the invariant that `denominator`
  equals the running product
    `∏_{k ∈ visited, pts[k].x ≠ pi.x} (pi.x - pts[k].x)`
  over all points visited so far.
-/

/-! ## Spec for `core.slice.iter.IteratorSliceIter.next`

The slice iterator `next` method is a concrete (non-axiomatic)
definition in the Aeneas standard library.  It advances the internal
index `i` by one and returns the element at that position, or `none`
if the iterator is exhausted.

The postcondition captures both branches:
- If `iter.i ≥ iter.slice.len` (exhausted), returns `(none, iter)`
  with the iterator unchanged.
- If `iter.i < iter.slice.len` (has element), returns
  `(some x, iter')` where `x` is the element at position `iter.i`
  and `iter'.i = iter.i + 1`, `iter'.slice = iter.slice`.

This function is always total — it never panics.
-/

/-- **Spec and proof concerning
`core.slice.iter.IteratorSliceIter.next`**:

The `next` method of the `Iterator` instance for `Iter<'a, T>`,
specified at the WP / postcondition level: on an `iter : Iter T`,
`next` returns `(opt, iter')` where:

* if `iter.i ≥ iter.slice.len` (the iterator is exhausted), then
  `opt = none` and `iter' = iter` (the iterator is unchanged);
* if `iter.i < iter.slice.len` (the iterator still has an element),
  then `opt = some x` for some element `x`, `iter'.i = iter.i + 1`,
  and `iter'.slice = iter.slice` (the slice is preserved).
-/
@[step]
theorem IteratorSliceIter_next_spec {T : Type}
    (iter : core.slice.iter.Iter T) :
    core.slice.iter.IteratorSliceIter.next iter
      ⦃ (opt, iter') =>
        (¬ iter.i < iter.slice.len →
            opt = none ∧ iter' = iter) ∧
        (iter.i < iter.slice.len →
            ∃ x, opt = some x ∧
            iter'.slice = iter.slice ∧
            iter'.i = iter.i + 1) ⦄ := by
  suffices h : ∃ opt iter',
      core.slice.iter.IteratorSliceIter.next iter
        = ok (opt, iter') ∧
      (¬ iter.i < iter.slice.len → opt = none ∧ iter' = iter) ∧
      (iter.i < iter.slice.len →
          ∃ x, opt = some x ∧
          iter'.slice = iter.slice ∧
          iter'.i = iter.i + 1) by
    obtain ⟨opt, iter', heq, h1, h2⟩ := h
    rw [heq]; simp only [WP.spec_ok]
    exact ⟨h1, h2⟩
  simp only [core.slice.iter.IteratorSliceIter.next]
  by_cases hlt : iter.i < iter.slice.len
  · rw [dif_pos hlt]
    exact ⟨some (iter.slice[iter.i]),
           { iter with i := iter.i + 1 }, rfl,
           fun h => absurd hlt h,
           fun _ => ⟨_, rfl, rfl, rfl⟩⟩
  · rw [dif_neg hlt]
    exact ⟨none, iter, rfl,
           fun _ => ⟨rfl, rfl⟩,
           fun h => absurd h hlt⟩

/-- `core.slice.iter.IteratorSliceIter.next` always succeeds:
returns `ok (o, iter')` for some option `o` and iterator `iter'`.
This is used in the body proof to extract the result and case-split
on the option (following the pattern from `DivImpl.lean`). -/
private lemma IteratorSliceIter_next_ok {T : Type}
    (iter : core.slice.iter.Iter T) :
    ∃ o iter1,
      core.slice.iter.IteratorSliceIter.next iter = ok (o, iter1) := by
  unfold core.slice.iter.IteratorSliceIter.next
  split <;> exact ⟨_, _, rfl⟩

/-! ## Spec for by-value `Sub<GF16>`

The body uses the by-value `CoreOpsArithSubGF16GF16.sub` rather than
the by-reference `CoreOpsArithSubShared0GF16GF16.sub`.  Both delegate
to the same `sub_assign` (which itself delegates to `add_assign`),
but `step*` needs an explicit `@[step]` theorem for the by-value
variant.
-/

/-- **Spec for by-value `Sub<GF16> for GF16`**:

The by-value `Sub<GF16>::sub` computes GF(2¹⁶) subtraction, which
coincides with addition (XOR) in characteristic 2.  The result
satisfies the same GF(2¹⁶)-level postcondition as the by-reference
variant:

  `result.value.val.toGF216 = self.value.val.toGF216 - other.value.val.toGF216`

The proof unfolds the by-value `sub` and the underlying `sub_assign`
to expose `add_assign`, then discharges via `step*` using the
already-registered `add_assign_spec`.
-/
@[step]
theorem SubGF16GF16_sub_spec (self other : spqr.encoding.gf.GF16) :
    spqr.encoding.gf.GF16.Insts.CoreOpsArithSubGF16GF16.sub self other
    ⦃ (result : spqr.encoding.gf.GF16) =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 - other.value.val.toGF216 ⦄ := by
  unfold spqr.encoding.gf.GF16.Insts.CoreOpsArithSubGF16GF16.sub
         spqr.encoding.gf.GF16.Insts.CoreOpsArithSubAssignShared0GF16.sub_assign
  step*

/-- **Spec and proof concerning
`encoding.polynomial.Poly.lagrange_interpolate_complete_loop0.body`**:

One step of the denominator accumulation for Lagrange interpolation.
Given a distinguished point `pi`, an iterator over the point set,
and the current denominator accumulator, the body processes the next
point from the iterator:

• If the iterator is exhausted, returns `done` with the unchanged
  `(pi, denominator)` pair.
• If the next point `pj` has `pi.x = pj.x` (self-point), returns
  `cont` with the denominator unchanged.
• If `pi.x ≠ pj.x`, returns `cont` with the denominator updated to
  `denominator * (pi.x - pj.x)` in GF(2¹⁶).

The postcondition captures the mathematical invariant:

  In the **`done`** branch:
    `GF16toGF216 denom' = GF16toGF216 denominator ∧ pi' = pi`

  In the **`cont`** branch (disjunction over skip / accumulate):
    `GF16toGF216 denom' = GF16toGF216 denominator`
    ∨ `∃ pj_x : GF216, GF16toGF216 denom' =
        GF16toGF216 denominator * (GF16toGF216 pi.x - pj_x)`

The proof unfolds `body`, extracts the `IteratorSliceIter.next`
result using `IteratorSliceIter_next_ok`, case-splits on the
returned `Option`, and then delegates to `step*` which applies the
registered specs for `GF16.eq`, `GF16.sub` (by-value), and
`GF16.mul_assign`.

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/
@[step]
theorem body_spec (pi : spqr.encoding.polynomial.Pt)
    (iter : core.slice.iter.Iter spqr.encoding.polynomial.Pt)
    (denominator : spqr.encoding.gf.GF16) :
    body pi iter denominator ⦃ result =>
      match result with
      | ControlFlow.done (pi', denom') =>
          GF16toGF216 denom' = GF16toGF216 denominator ∧ pi' = pi
      | ControlFlow.cont (_, denom') =>
          GF16toGF216 denom' = GF16toGF216 denominator ∨
          ∃ (pj_x : GF216),
            GF16toGF216 denom' =
              GF16toGF216 denominator *
                (GF16toGF216 pi.x - pj_x)
      ⦄ := by
  unfold body
  obtain ⟨o, iter1, hnext⟩ := IteratorSliceIter_next_ok iter
  rw [hnext]; simp only [bind_tc_ok]
  cases o with
  | none =>
    simp only [WP.spec_ok]
    simp
  | some pj =>
    step*
    -- step* handles b = true automatically; only b = false remains
    right
    exact ⟨GF16toGF216 pj.x, by simp only [GF16toGF216]; rw [denominator1_post, g_post]⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0
