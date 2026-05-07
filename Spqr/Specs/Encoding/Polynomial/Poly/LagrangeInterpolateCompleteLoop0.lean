/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateCompleteLoopBody0
/-! # Spec Theorem for `lagrange_interpolate_complete`: loop 0

Specification and proof for
`spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0`,
which implements the full denominator accumulation loop in Lagrange
interpolation over GF(2¹⁶).

Given a distinguished point `pi = pts[i]`, an iterator over the full
point set, and an initial `denominator` (typically `GF16::ONE`), the
loop computes the product
  `denominator_final = denominator_init *
      ∏_{j ∈ remaining, pts[j].x ≠ pi.x} (pi.x - pts[j].x)`
by repeatedly invoking
`lagrange_interpolate_complete_loop0.body`, which processes one
point per iteration.  This denominator is then used to form the
Lagrange scaling factor
  `scale = pi.y / denominator_final`
which ensures that the interpolating polynomial `f` satisfies
`f(pi.x) = pi.y` for the distinguished point and `f(pj.x) = 0`
for all other points.

The loop is an Aeneas-extracted `loop` fixed-point: it calls the
body function `body pi iter₁ denominator₁` at each step, threading
the `(iter, denominator)` state through the `cont` control-flow arm
until the iterator is exhausted (`done`).

Each iteration (handled by the body spec in
`LagrangeInterpolateCompleteLoopBody0.lean`):

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

/-! ## Mathematical helper: Lagrange denominator product

The mathematical specification of the loop requires a function that
computes the partial product of `(pi.x - pts[j].x)` over all
remaining points in the slice (from position `start` onwards) where
`pts[j].x ≠ pi.x`.  This is the "Lagrange denominator product",
which captures what the loop accumulates.
-/

/-- **Lagrange denominator product over a suffix of the point list.**

Given a distinguished x-coordinate `pi_x : GF16`, a list of points
`pts`, and a starting index `start`, compute the product

  `∏_{j = start}^{pts.length - 1}
      (if pi_x.value = pts[j].x.value then 1
       else GF16toGF216 pi_x - GF16toGF216 pts[j].x)`

over the remaining points in the list.  The product is `1` when
`start ≥ pts.length` (no remaining points).

This function is used only in specifications and proofs — it is
`noncomputable` because `GF216` arithmetic is noncomputable. -/
noncomputable def lagrangeDenomProd (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat) : GF216 :=
  if h : start < pts.length then
    if pi_x.value = (pts.get ⟨start, h⟩).x.value
    then lagrangeDenomProd pi_x pts (start + 1)
    else (GF16toGF216 pi_x - GF16toGF216 (pts.get ⟨start, h⟩).x) *
         lagrangeDenomProd pi_x pts (start + 1)
  else 1
termination_by pts.length - start

/-! ### Basic properties of `lagrangeDenomProd` -/

/-- When `start ≥ pts.length`, the product is `1` (empty product). -/
@[simp]
lemma lagrangeDenomProd_ge (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : pts.length ≤ start) :
    lagrangeDenomProd pi_x pts start = 1 := by
  unfold lagrangeDenomProd
  simp [show ¬(start < pts.length) from by omega]

/-- One-step unfolding when the current point matches `pi_x`. -/
lemma lagrangeDenomProd_skip (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : start < pts.length)
    (heq : pi_x.value = (pts.get ⟨start, h⟩).x.value) :
    lagrangeDenomProd pi_x pts start =
      lagrangeDenomProd pi_x pts (start + 1) := by
  conv_lhs => unfold lagrangeDenomProd
  rw [dif_pos h, if_pos heq]

/-- One-step unfolding when the current point differs from `pi_x`. -/
lemma lagrangeDenomProd_accum (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : start < pts.length)
    (hne : pi_x.value ≠ (pts.get ⟨start, h⟩).x.value) :
    lagrangeDenomProd pi_x pts start =
      (GF16toGF216 pi_x - GF16toGF216 (pts.get ⟨start, h⟩).x) *
        lagrangeDenomProd pi_x pts (start + 1) := by
  conv_lhs => unfold lagrangeDenomProd
  rw [dif_pos h, if_neg hne]

/-! ### Helper lemma for element access across equal slices -/

/-- Elements at the same index in equal slices are equal.
This avoids dependent-type issues with `rw`/`rwa` when rewriting
the slice in a `List.get` term whose bound proof depends on the
slice. -/
private lemma slice_get_eq_of_eq {T : Type} {s₁ s₂ : Slice T} (h : s₁ = s₂)
    (i : Nat) (h₁ : i < s₁.val.length) (h₂ : i < s₂.val.length) :
    s₁.val.get ⟨i, h₁⟩ = s₂.val.get ⟨i, h₂⟩ := by
  subst h; rfl

/-
natural language description:

• Takes an iterator `iter` over the full point set (with current
  position `iter.i` and underlying slice `iter.slice`), a
  distinguished point `pi : Pt` (the Lagrange interpolation
  target), and the current `denominator : GF16` accumulator
  (initialized to `GF16::ONE` before the first call).
• Drives the Aeneas `loop` combinator with the body function
  `lagrange_interpolate_complete_loop0.body pi`, threading the
  `(iter, denominator)` pair through successive iterations.
• Each iteration calls `body pi iter₁ denominator₁`, which
  processes the next point from the iterator:
  – If the iterator is exhausted (`none`), the body returns
    `done (pi, denominator₁)` and the loop terminates.
  – If a point `pj` is obtained (`some pj`):
    • If `pi.x == pj.x`, the body returns
      `cont (iter', denominator₁)` — the denominator is
      unchanged (self-point skip).
    • If `pi.x ≠ pj.x`, the body computes `g = pi.x - pj.x`
      and returns `cont (iter', denominator₁ * g)`.
• On termination, the loop returns `(pi, denominator_final)`.

natural language specs:

• The function always succeeds (no panic) for any valid inputs,
  since the underlying operations (`PartialEq<GF16>`,
  `Sub<GF16>`, `MulAssign<GF16>`, and iterator `next`) are all
  total on bounded integers.
• The returned point is unchanged: `pi' = pi`.
• The returned denominator satisfies the GF(2¹⁶)-level identity:
    `GF16toGF216 denominator' =
        GF16toGF216 denominator *
          lagrangeDenomProd pi.x
            iter.slice.val iter.i`
  i.e. the final denominator is the initial denominator multiplied
  by the product of `(pi.x - pj.x)` for all remaining points
  `pj` in the iterator where `pj.x ≠ pi.x`.
• When the loop is called at the top level with `iter.i = 0` and
  `denominator = GF16::ONE`, the result specialises to:
    `GF16toGF216 denominator' =
        lagrangeDenomProd pi.x
          iter.slice.val 0`
  which is the full Lagrange denominator product over all points.
-/

/-- **Spec and proof concerning
`encoding.polynomial.Poly.lagrange_interpolate_complete_loop0`**:

The full denominator accumulation loop for Lagrange interpolation
over GF(2¹⁶).  Given a distinguished point `pi`, an iterator over
the point set, and an initial denominator accumulator, the loop
processes every remaining point in the iterator and accumulates the
product of `(pi.x - pj.x)` for all points where `pj.x ≠ pi.x`.

The result `(pi', denom')` satisfies:

  **`pi'` is unchanged**:  `pi' = pi`

  **Denominator is the full partial product**:
    `GF16toGF216 denom' =
        GF16toGF216 denominator *
          lagrangeDenomProd pi.x
            iter.slice.val iter.i`

where `lagrangeDenomProd pi_x pts start` is the mathematical
product `∏_{j ≥ start, pts[j].x.value ≠ pi_x.value}
(GF16toGF216 pi_x - GF16toGF216 pts[j].x)`,
with the convention that an empty product equals `1`.

The proof applies `loop.spec_decr_nat` with:
- **measure**: `iter.slice.len - iter.i` (remaining elements),
- **invariant**: the iterator's underlying slice is preserved, the
  index is within bounds, and the current `denominator` satisfies
  the partial-product identity up to the current iterator position,

and discharges each step by unfolding the body and applying the
registered specs for `GF16.eq`, `GF16.sub`, and `GF16.mul_assign`.

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/
@[step]
theorem loop0_spec
    (iter : core.slice.iter.Iter spqr.encoding.polynomial.Pt)
    (pi : spqr.encoding.polynomial.Pt)
    (denominator : spqr.encoding.gf.GF16) :
    lagrange_interpolate_complete_loop0 iter pi denominator
      ⦃ (result : spqr.encoding.polynomial.Pt ×
                   spqr.encoding.gf.GF16) =>
        result.1 = pi ∧
        GF16toGF216 result.2 =
          GF16toGF216 denominator *
            lagrangeDenomProd pi.x
              iter.slice.val iter.i ⦄ := by
  unfold lagrange_interpolate_complete_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter spqr.encoding.polynomial.Pt ×
                        spqr.encoding.gf.GF16) =>
      p.1.slice.len - p.1.i)
    (inv := fun (p : core.slice.iter.Iter spqr.encoding.polynomial.Pt ×
                      spqr.encoding.gf.GF16) =>
      p.1.slice = iter.slice ∧
      iter.i ≤ p.1.i ∧
      GF16toGF216 p.2 * lagrangeDenomProd pi.x
          iter.slice.val p.1.i =
        GF16toGF216 denominator *
          lagrangeDenomProd pi.x
            iter.slice.val iter.i)
  · -- Step case: the body preserves the invariant and decreases the measure
    rintro ⟨iter', denom'⟩ ⟨hslice, hge, hinv⟩
    -- Normalize pair projections so hslice : iter'.slice = iter.slice, etc.
    simp only [] at hslice hge hinv ⊢
    -- Unfold the body and the iterator next
    unfold body
    simp only [core.slice.iter.IteratorSliceIter.next]
    split
    · -- Case: iter'.i < iter'.slice.len (iterator has an element)
      rename_i hlt
      simp only [bind_tc_ok]
      -- Process the equality check and arithmetic via step*
      step*
      -- After step*, we have two branches from `if b then ... else ...`
      -- Branch 1: b = true (pi.x.value = pj.x.value → skip)
      · -- cont with unchanged denominator
        have hlt_list : iter'.i < iter.slice.val.length := by
          simp only [Slice.len_val, hslice] at hlt; exact hlt
        have hval_eq : pi.x.value = (iter.slice.val.get ⟨iter'.i, hlt_list⟩).x.value := by
          have h1 := b_post.mp ‹b = true›
          simp only [hslice] at h1
          exact h1
        -- Build the full invariant + measure decrease as a 4-tuple
        refine ⟨hslice, by omega, ?_, by (simp only [Slice.len_val]; grind)⟩
        rw [← lagrangeDenomProd_skip pi.x iter.slice.val iter'.i hlt_list hval_eq]
        exact hinv
      -- Branch 2: b = false (pi.x.value ≠ pj.x.value → accumulate)
      · -- cont with updated denominator
        have hlt_list : iter'.i < iter.slice.val.length := by
          simp only [Slice.len_val, hslice] at hlt; exact hlt
        have hval_ne : pi.x.value ≠ (iter.slice.val.get ⟨iter'.i, hlt_list⟩).x.value := by
          have h1 := mt b_post.mpr ‹¬b = true›
          simp only [hslice] at h1
          exact h1
        -- Build the full invariant + measure decrease as a 4-tuple
        refine ⟨hslice, by omega, ?_, by (simp only [Slice.len_val]; grind)⟩
        -- Need: GF16toGF216 denominator1 * lagrangeDenomProd ... (iter'.i + 1) = RHS
        rw [lagrangeDenomProd_accum pi.x iter.slice.val iter'.i hlt_list hval_ne] at hinv
        -- Unfold GF16toGF216 so rw can match denominator1_post/g_post
        simp only [GF16toGF216] at hinv ⊢
        -- Normalize iter'.slice to iter.slice in g_post
        simp only [hslice] at g_post
        simp only [List.get_eq_getElem] at hinv
        rw [denominator1_post, g_post]
        ring_nf
        ring_nf at hinv
        exact hinv
    · -- Case: ¬ iter'.i < iter'.slice.len (iterator exhausted)
      rename_i hnlt
      simp only [bind_tc_ok, WP.spec_ok]
      -- Returns done (pi, denom') — loop terminates
      have hge' : iter.slice.val.length ≤ iter'.i := by
        simp only [Slice.len_val, hslice] at hnlt; grind
      rw [lagrangeDenomProd_ge pi.x iter.slice.val iter'.i hge', mul_one] at hinv
      exact ⟨trivial, hinv⟩
  · -- Initial invariant holds
    exact ⟨rfl, le_refl _, by ring⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0
