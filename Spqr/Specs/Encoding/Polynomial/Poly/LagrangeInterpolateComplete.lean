/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Gf.GF16.Sub
import Spqr.Specs.Encoding.Gf.GF16.MulAssign
import Spqr.Specs.Encoding.Gf.GF16.Div
import Spqr.Specs.Encoding.Gf.GF16.Eq
import Spqr.Specs.Encoding.Gf.GF16.ZERO
import Spqr.Specs.Encoding.Gf.GF16.ONE
import Mathlib.RingTheory.DedekindDomain.Basic
/-!
# Spec Theorem for `lagrange_interpolate_complete`: loop body 0

Given a distinguished point `pi = pts[i]` and a running accumulator `denominator`, the full loop 0
computes the product
  `denominator_final = ∏_{j : pts[j].x ≠ pi.x} (pi.x - pts[j].x)`
by iterating over all points `pj` in `pts`.  This denominator is then used to form the Lagrange
scaling factor
  `scale = pi.y / denominator_final`
which ensures that the interpolating polynomial `f` satisfies `f(pi.x) = pi.y` for the distinguished
point and `f(pj.x) = 0` for all other points.

Each step of the loop body:

1. Retrieves the next point `pj` from the slice iterator.
2. If the iterator is exhausted (`none`), returns `done` with the current `(pi, denominator)` pair —
   the accumulation is complete.
3. If `pi.x = pj.x`, returns `cont` with the denominator unchanged — this is the `i = j` case where
   the point is skipped.
4. If `pi.x ≠ pj.x`, computes `g = pi.x - pj.x` and updates `denominator ← denominator * g`, then
   returns `cont` with the updated denominator.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition:
  `pi.x - pj.x = pi.x + pj.x = pi.x ⊕ pj.x`

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0

/--
**Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_complete_loop0.body`**:

• The function always succeeds (no panic) for any valid inputs, since `PartialEq<GF16>`,
  `Sub<GF16>`, and `MulAssign<GF16>` are total operations on bounded integers.
• In the `done` case, the point `pi` and the denominator are returned unchanged — the loop exits
  with the final accumulator.
• In the `cont` case, the denominator is either unchanged (when `pi.x = pj.x`, i.e. the self-point
  skip) or has been multiplied by `(pi.x - pj.x)` in GF(2¹⁶).
• The loop body preserves the invariant that `denominator`
  equals the running product
    `∏_{k ∈ visited, pts[k].x ≠ pi.x} (pi.x - pts[k].x)`
  over all points visited so far.

## Spec for `core.slice.iter.IteratorSliceIter.next`

The slice iterator `next` method is a concrete (non-axiomatic) definition in the Aeneas standard
library.  It advances the internal index `i` by one and returns the element at that position, or
`none` if the iterator is exhausted.

The postcondition captures both branches:
- If `iter.i ≥ iter.slice.len` (exhausted), returns `(none, iter)` with the iterator unchanged.
- If `iter.i < iter.slice.len` (has element), returns `(some x, iter')` where `x` is the element at
  position `iter.i` and `iter'.i = iter.i + 1`, `iter'.slice = iter.slice`.

This function is always total — it never panics.
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

/--
`core.slice.iter.IteratorSliceIter.next` always succeeds: returns `ok (o, iter')` for some option
`o` and iterator `iter'`. This is used in the body proof to extract the result and case-split on the
option (following the pattern from `DivImpl.lean`).
-/
private lemma IteratorSliceIter_next_ok {T : Type}
    (iter : core.slice.iter.Iter T) :
    ∃ o iter1,
      core.slice.iter.IteratorSliceIter.next iter = ok (o, iter1) := by
  unfold core.slice.iter.IteratorSliceIter.next
  split <;> exact ⟨_, _, rfl⟩


/--
**Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_complete_loop0.body`**:

One step of the denominator accumulation for Lagrange interpolation. Given a distinguished point
`pi`, an iterator over the point set, and the current denominator accumulator, the body processes
the next point from the iterator:

• If the iterator is exhausted, returns `done` with the unchanged `(pi, denominator)` pair.
• If the next point `pj` has `pi.x = pj.x` (self-point), returns `cont` with the denominator
  unchanged.
• If `pi.x ≠ pj.x`, returns `cont` with the denominator updated to `denominator * (pi.x - pj.x)` in
  GF(2¹⁶).

The postcondition captures the mathematical invariant:

  In the **`done`** branch:
    `denom'.toGF216 = denominator.toGF216 ∧ pi' = pi`

  In the **`cont`** branch (disjunction over skip / accumulate):
    `denom'.toGF216 = denominator.toGF216`
    ∨ `∃ pj_x : GF216, denom'.toGF216 =
        denominator.toGF216 * (pi.x.toGF216 - pj_x)`

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/
@[step]
theorem body_spec (pi : Pt)
    (iter : core.slice.iter.Iter Pt)
    (denominator : GF16) :
    body pi iter denominator ⦃ result =>
      match result with
      | ControlFlow.done (pi', denom') =>
          denom'.toGF216 = denominator.toGF216 ∧ pi' = pi
      | ControlFlow.cont (_, denom') =>
          denom'.toGF216 = denominator.toGF216 ∨
          ∃ (pj_x : GF216),
            denom'.toGF216 =
              denominator.toGF216 *
                (pi.x.toGF216 - pj_x)
      ⦄ := by
  unfold body
  obtain ⟨o, iter1, hnext⟩ := IteratorSliceIter_next_ok iter
  rw [hnext]
  simp only [bind_tc_ok]
  cases o with
  | none =>
    simp [WP.spec_ok]
  | some pj =>
    simp only [encoding.gf.GF16.Insts.CoreCmpPartialEqGF16.eq, bind_tc_ok]
    split
    · simp only [WP.spec_ok]
      grind
    · step
      step
      right
      exact ⟨pj.x.toGF216, by rw [denominator1_post, g_post]⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0

/-!
# Spec Theorem for `lagrange_interpolate_complete`: loop 0

Given a distinguished point `pi = pts[i]`, an iterator over the full point set, and an initial
`denominator` (typically `GF16::ONE`), the loop computes the product
  `denominator_final = denominator_init *
      ∏_{j ∈ remaining, pts[j].x ≠ pi.x} (pi.x - pts[j].x)`
by repeatedly invoking `lagrange_interpolate_complete_loop0.body`, which processes one point per
iteration.  This denominator is then used to form the Lagrange scaling factor
  `scale = pi.y / denominator_final`
which ensures that the interpolating polynomial `f` satisfies `f(pi.x) = pi.y` for the distinguished
point and `f(pj.x) = 0` for all other points.

The loop is an Aeneas-extracted `loop` fixed-point: it calls the body function `body pi iter₁
denominator₁` at each step, threading the `(iter, denominator)` state through the `cont`
control-flow arm until the iterator is exhausted (`done`).

Each iteration (handled by the body spec in `LagrangeInterpolateCompleteLoopBody0.lean`):

1. Retrieves the next point `pj` from the slice iterator.
2. If the iterator is exhausted (`none`), returns `done` with the current `(pi, denominator)` pair —
   the accumulation is complete.
3. If `pi.x = pj.x`, returns `cont` with the denominator unchanged — this is the `i = j` case where
   the point is skipped.
4. If `pi.x ≠ pj.x`, computes `g = pi.x - pj.x` and updates `denominator ← denominator * g`, then
   returns `cont` with the updated denominator.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition:
  `pi.x - pj.x = pi.x + pj.x = pi.x ⊕ pj.x`

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0

open spqr.encoding.polynomial (lagrangeDenomProd lagrangeDenomProd_ge
  lagrangeDenomProd_skip lagrangeDenomProd_accum)

/-! ### Helper lemma for element access across equal slices -/

private lemma slice_get_eq_of_eq {T : Type} {s₁ s₂ : Slice T} (h : s₁ = s₂)
    (i : Nat) (h₁ : i < s₁.val.length) (h₂ : i < s₂.val.length) :
    s₁.val.get ⟨i, h₁⟩ = s₂.val.get ⟨i, h₂⟩ := by
  subst h; rfl

/--
**Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_complete_loop0`**:

• The function always succeeds (no panic) for any valid inputs, since the underlying operations
  (`PartialEq<GF16>`, `Sub<GF16>`, `MulAssign<GF16>`, and iterator `next`) are all total on bounded
  integers.
• The returned point is unchanged: `pi' = pi`.
• The returned denominator satisfies the GF(2¹⁶)-level identity:
    `denominator'.toGF216 =
        denominator.toGF216 *
          lagrangeDenomProd pi.x
            iter.slice.val iter.i`
  i.e. the final denominator is the initial denominator multiplied
  by the product of `(pi.x - pj.x)` for all remaining points
  `pj` in the iterator where `pj.x ≠ pi.x`.
• When the loop is called at the top level with `iter.i = 0` and
  `denominator = GF16::ONE`, the result specialises to:
    `denominator'.toGF216 =
        lagrangeDenomProd pi.x
          iter.slice.val 0`
  which is the full Lagrange denominator product over all points.

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/
@[step]
theorem loop0_spec
    (iter : core.slice.iter.Iter Pt)
    (pi : Pt)
    (denominator : GF16) :
    lagrange_interpolate_complete_loop0 iter pi denominator ⦃ (result : Pt × GF16) =>
        result.1 = pi ∧
        result.2.toGF216 =
          denominator.toGF216 *
            lagrangeDenomProd pi.x
              iter.slice.val iter.i ⦄ := by
  unfold lagrange_interpolate_complete_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter Pt × GF16) =>
      p.1.slice.len - p.1.i)
    (inv := fun (p : core.slice.iter.Iter Pt × GF16) =>
      p.1.slice = iter.slice ∧
      iter.i ≤ p.1.i ∧
      p.2.toGF216 * lagrangeDenomProd pi.x
          iter.slice.val p.1.i =
        denominator.toGF216 *
          lagrangeDenomProd pi.x
            iter.slice.val iter.i)
  · rintro ⟨iter', denom'⟩ ⟨hslice, hge, hinv⟩
    simp only [] at hslice hge hinv ⊢
    unfold body
    simp only [core.slice.iter.IteratorSliceIter.next]
    split
    · rename_i hlt
      simp only [bind_tc_ok]
      step*
      · have hlt_list : iter'.i < iter.slice.val.length := by
          simp only [Slice.len_val, hslice] at hlt; exact hlt
        have hval_eq : pi.x.value = (iter.slice.val.get ⟨iter'.i, hlt_list⟩).x.value := by
          have h1 := b_post.mp ‹b = true›
          simp only [hslice] at h1
          exact h1
        refine ⟨hslice, by omega, ?_, by (simp only [Slice.len_val]; grind)⟩
        rw [← lagrangeDenomProd_skip pi.x iter.slice.val iter'.i hlt_list hval_eq]
        exact hinv
      · have hlt_list : iter'.i < iter.slice.val.length := by
          simp only [Slice.len_val, hslice] at hlt; exact hlt
        have hval_ne : pi.x.value ≠ (iter.slice.val.get ⟨iter'.i, hlt_list⟩).x.value := by
          have h1 := mt b_post.mpr ‹¬b = true›
          simp only [hslice] at h1
          exact h1
        refine ⟨hslice, by omega, ?_, by (simp only [Slice.len_val]; grind)⟩
        rw [lagrangeDenomProd_accum pi.x iter.slice.val iter'.i hlt_list hval_ne] at hinv
        simp only [hslice] at g_post
        simp only [List.get_eq_getElem] at hinv
        rw [denominator1_post, g_post]
        ring_nf
        ring_nf at hinv
        exact hinv
    · rename_i hnlt
      simp only [bind_tc_ok, WP.spec_ok]
      have hge' : iter.slice.val.length ≤ iter'.i := by
        simp only [Slice.len_val, hslice] at hnlt; grind
      rw [lagrangeDenomProd_ge pi.x iter.slice.val iter'.i hge', mul_one] at hinv
      exact ⟨trivial, hinv⟩
  · exact ⟨rfl, le_refl _, by ring⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0


/-! # Spec Theorem for `lagrange_interpolate_complete`: loop 1 -/

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop1

open spqr.encoding.polynomial (hornerAccum hornerAccum_ge hornerAccum_unfold)

private lemma list_get_of_getElem?_eq {T : Type} {xs ys : List T}
    {k : Nat}
    (h : xs[k]? = ys[k]?) (hx : k < xs.length) (hy : k < ys.length) :
    xs.get ⟨k, hx⟩ = ys.get ⟨k, hy⟩ := by
  have h1 : xs[k]? = some (xs.get ⟨k, hx⟩) := List.getElem?_eq_getElem hx
  have h2 : ys[k]? = some (ys.get ⟨k, hy⟩) := List.getElem?_eq_getElem hy
  rw [h1, h2] at h
  exact Option.some_injective _ h

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

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

private lemma list_double_set_getElem_fst {T : Type} {xs : List T} {i j : Nat} {a b : T}
    (hij : j ≠ i) {h : i < ((xs.set i a).set j b).length} :
    ((xs.set i a).set j b)[i]'h = a := by
  simp [hij]

private lemma list_getElem?_getD_eq_getElem {T : Type} [Inhabited T] {xs : List T} {n : Nat}
    (h : n < xs.length) : xs[n]?.getD default = xs[n] := by
  simp [List.getElem?_eq_getElem h]

@[step]
theorem body_spec
    (g scale : spqr.encoding.gf.GF16)
    (iter' : core.ops.range.Range Std.Usize)
    (v' : alloc.vec.Vec spqr.encoding.gf.GF16)
    (h_start_ge : 1 ≤ iter'.start.val)
    (h_end_eq : iter'.«end».val = v'.val.length) :
    body g scale iter' v' ⦃ cf =>
      match cf with
      | ControlFlow.done r =>
          r = v' ∧ ¬ (iter'.start.val < iter'.«end».val)
      | ControlFlow.cont (iter1, v2) =>
          iter'.start.val < iter'.«end».val ∧
          iter1.start.val = iter'.start.val + 1 ∧
          iter1.«end» = iter'.«end» ∧
          v2.val.length = v'.val.length ∧
          (∀ (h_idx : v'.val.length - iter'.start.val < v2.val.length),
            (v2.val.get ⟨v'.val.length - iter'.start.val, h_idx⟩).toGF216 =
              (v'.val[v'.val.length - iter'.start.val]!).toGF216 *
                scale.toGF216) ∧
          (∀ (h_idx : v'.val.length - iter'.start.val - 1 < v2.val.length),
            (v2.val.get ⟨v'.val.length - iter'.start.val - 1, h_idx⟩).toGF216 =
              (v'.val[v'.val.length - iter'.start.val - 1]!).toGF216 +
              (v'.val[v'.val.length - iter'.start.val]!).toGF216 *
                g.toGF216) ∧
          (∀ (j : Nat),
            j ≠ v'.val.length - iter'.start.val →
            j ≠ v'.val.length - iter'.start.val - 1 →
            v2.val[j]? = v'.val[j]?) ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext, h_none, h_some⟩ := IteratorRange_next_Usize_post iter'
  rw [hnext]; simp only [bind_tc_ok]
  by_cases h_lt : iter'.start.val < iter'.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]; simp only
    have h_start_lt_len : iter'.start.val < v'.val.length := by omega
    have h_start_le_len : iter'.start.val ≤ v'.val.length := by omega
    have h_cursor_lt_len : v'.val.length - iter'.start.val < v'.val.length := by omega
    have h_cursor_ge1 : 1 ≤ v'.val.length - iter'.start.val := by omega
    step*
    all_goals simp_all
    · grind
    ·   rw [list_double_set_getElem_fst (show v'.val.length - iter'.start.val - 1 ≠
            v'.val.length - iter'.start.val from by omega)]
        simp only [GF16.toGF216]
        exact g3_post
  · obtain ⟨h_opt_eq, h_range_eq⟩ := h_none (by omega)
    rw [h_opt_eq]; simp only [WP.spec_ok]
    exact ⟨trivial, by omega⟩

private lemma hornerAccum_eq_of_idx_eq
    {g_x : spqr.encoding.gf.GF16} {v_list xs : List spqr.encoding.gf.GF16}
    {a b : Nat} {ha : a < xs.length} {hb : b < xs.length}
    (h_eq : a = b)
    (hsuff : (xs.get ⟨b, hb⟩).toGF216 = hornerAccum g_x v_list b) :
    (xs.get ⟨a, ha⟩).toGF216 = hornerAccum g_x v_list a := by
  subst h_eq; exact hsuff

@[step]
theorem loop1_spec
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (g : spqr.encoding.gf.GF16)
    (scale : spqr.encoding.gf.GF16)
    (h_start : iter.start.val = 1)
    (h_end : iter.«end».val = v.val.length) :
    lagrange_interpolate_complete_loop1 iter v g scale
      ⦃ (result : alloc.vec.Vec spqr.encoding.gf.GF16) =>
        result.val.length = v.val.length ∧
        (∀ k (hk : k < result.val.length),
          0 < k →
            (result.val.get ⟨k, hk⟩).toGF216 =
              scale.toGF216 * hornerAccum g v.val k) ∧
        (∀ (h0 : 0 < result.val.length),
            (result.val.get ⟨0, h0⟩).toGF216 =
              hornerAccum g v.val 0) ⦄ := by
  unfold lagrange_interpolate_complete_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                        alloc.vec.Vec spqr.encoding.gf.GF16) =>
      p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                      alloc.vec.Vec spqr.encoding.gf.GF16) =>
      p.2.val.length = v.val.length ∧
      p.1.«end».val = v.val.length ∧
      1 ≤ p.1.start.val ∧
      (∀ k (hk : k < p.2.val.length),
        v.val.length - p.1.start.val < k →
          (p.2.val.get ⟨k, hk⟩).toGF216 =
            scale.toGF216 * hornerAccum g v.val k) ∧
      (∀ (hcur : v.val.length - p.1.start.val < p.2.val.length),
          (p.2.val.get ⟨v.val.length - p.1.start.val,
            hcur⟩).toGF216 =
            hornerAccum g v.val (v.val.length - p.1.start.val)) ∧
      (∀ k, k < v.val.length - p.1.start.val →
        p.2.val[k]? = v.val[k]?))
  · rintro ⟨iter', v'⟩ ⟨hlen, hend, hstart_ge, hscaled, hcursor, hunchanged⟩
    simp only [] at hlen hend hstart_ge hscaled hcursor hunchanged ⊢
    have h_end_eq : iter'.«end».val = v'.val.length := by omega
    step*
    split
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_eq, h_nlt⟩ := r_post
      constructor
      · simp_all
      constructor
      · intro k hk hk_pos
        subst h_eq
        exact hscaled k hk (by omega)
      · intro h0
        simp_all only [List.get_eq_getElem, tsub_lt_self_iff, and_self,
        forall_and_index, not_lt, Nat.sub_eq_zero_of_le,
        not_lt_zero, IsEmpty.forall_iff, implies_true]
        have hcz : v.val.length - iter'.start.val = 0 := by omega
        have hc := hcursor (by grind)
        convert hc using 2
        simp_all
        grind
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_lt, h_start1, h_end1, h_v2len, h_scaled_pos, h_carry_pos, h_frame⟩ := r_post
      set cursor := v.val.length - iter'.start.val with hcursor_def
      have hcge1 : cursor ≥ 1 := by omega
      have hcur_v' : cursor < v'.val.length := by omega
      have h_new_start_eq : v.val.length - (iter'.start.val + 1) = cursor - 1 := by omega
      have h_new_cursor_eq : v.val.length - (Prod.fst r_post).start.val = cursor - 1 := by
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · have : (Prod.fst r_post).«end».val = iter'.«end».val := by
          rw [h_end1]
        omega
      · omega
      · intro k hk hk_gt
        rw [h_new_cursor_eq] at hk_gt
        by_cases hk_eq : k = cursor
        · subst hk_eq
          rw [hlen] at h_scaled_pos
          have h_idx : cursor < (Prod.snd r_post).val.length := by omega
          specialize h_scaled_pos h_idx
          simp only [GF16.toGF216] at h_scaled_pos hcursor ⊢
          rw [h_scaled_pos]
          have hbang : v'.val[cursor]! = v'.val.get ⟨cursor, hcur_v'⟩ :=
            getElem!_pos v'.val cursor hcur_v'
          rw [hbang]
          specialize hcursor hcur_v'
          rw [hcursor]; ring
        · have hk_gt' : cursor < k := by omega
          have hk_v' : k < v'.val.length := by omega
          have h_inv := hscaled k hk_v' (by omega)
          have h_fr := h_frame k (by omega) (by omega)
          simp only [GF16.toGF216] at h_inv ⊢
          have h_get := list_get_of_getElem?_eq h_fr (by omega) hk_v'
          simp only [List.get_eq_getElem] at h_get
          grind
      · intro hcur
        rw [h_new_cursor_eq] at hcur
        have hcm1_v' : cursor - 1 < v'.val.length := by omega
        have hcm1_v : cursor - 1 < v.val.length := by omega
        rw [hlen] at h_carry_pos
        have h_idx : cursor - 1 < (Prod.snd r_post).val.length := by omega
        specialize h_carry_pos h_idx
        have h_idx_eq : v.val.length - (Prod.fst r_post).start.val = cursor - 1 :=
          h_new_cursor_eq
        suffices hsuff :
            ((Prod.snd r_post).val.get ⟨cursor - 1, h_idx⟩).toGF216 =
              hornerAccum g v.val (cursor - 1) by
          exact hornerAccum_eq_of_idx_eq h_idx_eq hsuff
        rw [h_carry_pos]
        rw [hornerAccum_unfold g v.val (cursor - 1) hcm1_v]
        have h_succ : cursor - 1 + 1 = cursor := by omega
        rw [h_succ]
        have hbang_cm1 : v'.val[cursor - 1]! = v'.val.get ⟨cursor - 1, hcm1_v'⟩ :=
          getElem!_pos v'.val (cursor - 1) hcm1_v'
        have hbang_c : v'.val[cursor]! = v'.val.get ⟨cursor, hcur_v'⟩ :=
          getElem!_pos v'.val cursor hcur_v'
        rw [hbang_cm1, hbang_c]
        have h_unch := hunchanged (cursor - 1) (by omega)
        have h_get_cm1 := list_get_of_getElem?_eq h_unch hcm1_v' hcm1_v
        rw [h_get_cm1]
        specialize hcursor hcur_v'
        rw [hcursor]
        ring
      · intro k hk_lt
        rw [h_new_cursor_eq] at hk_lt
        have h_fr := h_frame k (by omega) (by omega)
        have h_unch := hunchanged k (by omega)
        rw [h_fr, h_unch]
      · have : (Prod.fst r_post).«end».val = iter'.«end».val := by
          rw [h_end1]
        omega
  · dsimp only [Prod.fst, Prod.snd]
    simp only [h_start]
    refine ⟨trivial, h_end, le_refl 1, ?_, ?_, ?_⟩
    · intro k hk hgt; omega
    · intro hcur
      rw [hornerAccum_unfold g v.val (v.val.length - 1) hcur]
      have hlen_eq : v.val.length - 1 + 1 = v.val.length := by omega
      rw [hlen_eq, hornerAccum_ge g v.val v.val.length (le_refl _)]
      simp [mul_zero, add_zero]
    · intro _ _; trivial

end spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop1


/-! # Spec theorem for `spqr.encoding.polynomial.Poly.lagrange_interpolate_complete` -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.gf.GF16.Insts.CoreOpsArithDivShared0GF16GF16

namespace spqr.encoding.polynomial.Poly

open spqr.encoding.polynomial (lagrangeScaleGF216 lagrangeDenomProd)

@[step]
theorem into_iter_spec (pts : Slice Pt) :
    SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
      pts
      ⦃ (iter : core.slice.iter.Iter Pt) =>
        iter.slice = pts ∧ iter.i = 0 ⦄ := by
  unfold SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
  simp [WP.spec_ok]

private lemma GF216_add_self_eq_zero (x : GF216) : x + x = 0 := by
  have h2 : (2 : GF216) = 0 := GF216.two_eq_zero
  have : x + x = 2 * x := by ring
  rw [this, h2, zero_mul]

private lemma hornerAccum_cancel (g : spqr.encoding.gf.GF16)
    (coeffs : List spqr.encoding.gf.GF16) (k : Nat)
    (hk : k < coeffs.length) :
    hornerAccum g coeffs k +
      g.toGF216 *
        hornerAccum
          g coeffs (k + 1) =
      (coeffs.get ⟨k, hk⟩).toGF216 := by
  conv_lhs =>
    rw [hornerAccum_unfold
      g coeffs k hk]
  set c := (coeffs.get ⟨k, hk⟩).toGF216
  set t := g.toGF216 *
    hornerAccum
      g coeffs (k + 1)
  rw [show (c + t) + t = c + (t + t) from by ring]
  rw [GF216_add_self_eq_zero t, add_zero]

private lemma GF216_eq_of_add_eq_zero
    {a b : GF216} (h : a + b = 0) : a = b := by
  have : b + b = 0 := GF216_add_self_eq_zero b
  have hab : a = a + 0 := by ring
  rw [hab, ← this, ← add_assoc, h, zero_add]

private lemma poly_identity_from_loop1
    (coeffs v : List spqr.encoding.gf.GF16)
    (g : spqr.encoding.gf.GF16) (s : GF216)
    (hlen : v.length = coeffs.length)
    (hpos : 0 < coeffs.length)
    (hv0_zero : ∀ (h0 : 0 < v.length),
        (v.get ⟨0, h0⟩).toGF216 = 0)
    (hH0 : hornerAccum
      g coeffs 0 = 0)
    (hvk : ∀ k (hk : k < v.length), 0 < k →
        (v.get ⟨k, hk⟩).toGF216 =
          s * hornerAccum
            g coeffs k) :
    listToGF216Poly v * (X - C (g.toGF216)) =
      X * C s * listToGF216Poly coeffs := by
  rw [GF216Poly.sub_eq_add, mul_add, mul_comm (listToGF216Poly v) (C (g.toGF216)),
      show X * C s * listToGF216Poly coeffs =
        C s * (X * listToGF216Poly coeffs) from by ring]
  ext m
  simp only [coeff_add, coeff_C_mul]
  set α := g.toGF216
  by_cases hm0 : m = 0
  · subst hm0
    rw [coeff_mul_X_zero, coeff_X_mul_zero, zero_add, mul_zero]
    simp only [listToGF216Poly_coeff]
    split
    · rename_i h0v
      rw [hv0_zero h0v, mul_zero]
    · rename_i h0v; push_neg at h0v; omega
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    have hcoeff_v_X : (listToGF216Poly v * X).coeff m =
        (listToGF216Poly v).coeff (m - 1) := by
      conv_lhs => rw [show m = m - 1 + 1 from by omega]
      rw [coeff_mul_X]
    have hcoeff_X_c : (X * listToGF216Poly coeffs).coeff m =
        (listToGF216Poly coeffs).coeff (m - 1) := by
      conv_lhs => rw [show m = m - 1 + 1 from by omega]
      rw [coeff_X_mul]
    rw [hcoeff_v_X, hcoeff_X_c]
    simp only [listToGF216Poly_coeff]
    by_cases hm_lt : m < coeffs.length
    · have hm1_lt_c : m - 1 < coeffs.length := by omega
      have hm1_lt_v : m - 1 < v.length := by omega
      have hm_lt_v : m < v.length := by omega
      rw [dif_pos hm1_lt_v, dif_pos hm_lt_v, dif_pos hm1_lt_c]
      by_cases hm1_zero : m - 1 = 0
      · have hm_eq_1 : m = 1 := by omega
        subst hm_eq_1; simp only [Nat.sub_self]
        rw [hv0_zero (by omega),
            hvk 1 (by omega) (by omega), zero_add]
        have hH0_unf :=
          hornerAccum_unfold
            g coeffs 0 (by omega)
        rw [hH0] at hH0_unf
        have hcoeff0 :
            (coeffs.get ⟨0, by omega⟩).toGF216 =
              α * hornerAccum
                g coeffs 1 :=
          GF216_eq_of_add_eq_zero hH0_unf.symm
        rw [hcoeff0]; ring
      · have hm1_pos : 0 < m - 1 := by omega
        rw [hvk (m - 1) hm1_lt_v hm1_pos,
            hvk m hm_lt_v hm_pos]
        rw [show s * hornerAccum
                g coeffs (m - 1) +
              α * (s * hornerAccum
                g coeffs m) =
            s * (hornerAccum
                g coeffs (m - 1) +
              α * hornerAccum
                g coeffs m) from by ring]
        congr 1
        have hm_succ : m - 1 + 1 = m := by omega
        have := hornerAccum_cancel g coeffs (m - 1) hm1_lt_c
        rw [hm_succ] at this
        exact this
    · push_neg at hm_lt
      by_cases hm_eq : m = coeffs.length
      · subst hm_eq
        have hm1_lt_c : coeffs.length - 1 < coeffs.length :=
          by omega
        have hm1_lt_v : coeffs.length - 1 < v.length := by omega
        rw [dif_pos hm1_lt_v,
            dif_neg (show ¬(coeffs.length < v.length) from
              by omega),
            dif_pos hm1_lt_c]
        rw [mul_zero, add_zero]
        have hH_last :=
          hornerAccum_unfold
            g coeffs (coeffs.length - 1) hm1_lt_c
        have hsucc : coeffs.length - 1 + 1 = coeffs.length :=
          by omega
        rw [hsucc] at hH_last
        rw [hornerAccum_ge
          g coeffs coeffs.length (le_refl _)] at hH_last
        simp [mul_zero, add_zero] at hH_last
        have hH_last_get : (coeffs.get ⟨coeffs.length - 1, hm1_lt_c⟩).toGF216 =
            hornerAccum g coeffs (coeffs.length - 1) := by
          simp only [List.get_eq_getElem]; exact hH_last.symm
        rw [hH_last_get]
        by_cases h_pos : 0 < coeffs.length - 1
        · exact hvk (coeffs.length - 1) hm1_lt_v h_pos
        · have h0 : coeffs.length - 1 = 0 := by omega
          have hv_eq : v.get ⟨coeffs.length - 1, hm1_lt_v⟩ =
              v.get ⟨0, by omega⟩ := by
            congr 1; exact Fin.ext h0
          rw [show (v.get ⟨coeffs.length - 1, hm1_lt_v⟩).toGF216 =
              (v.get ⟨0, by omega⟩).toGF216 from by rw [hv_eq]]
          rw [hv0_zero (by omega), h0, hH0, mul_zero]
      · have hm_gt : coeffs.length < m := by omega
        rw [dif_neg (show ¬(m - 1 < v.length) from by omega),
            dif_neg (show ¬(m < v.length) from by omega),
            dif_neg (show ¬(m - 1 < coeffs.length) from by omega)]
        ring

/-! ## Bridge: hornerAccum at position 0 equals polynomial evaluation -/

/--
Shifting lemma: evaluating `hornerAccum` on `c :: cs` at position
    `pos + 1` is the same as evaluating on `cs` at position `pos`.
-/
private lemma hornerAccum_cons
    (g c : GF16)
    (cs : List GF16)
    (pos : Nat) :
    hornerAccum g (c :: cs) (pos + 1) =
      hornerAccum g cs pos := by
  by_cases hlt : pos < cs.length
  · rw [hornerAccum_unfold g (c :: cs) (pos + 1)
          (by simp; omega),
        hornerAccum_unfold g cs pos hlt]
    have hget : (c :: cs).get ⟨pos + 1, by simp; omega⟩ = cs.get ⟨pos, hlt⟩ := by
      simp [List.get_eq_getElem]
    rw [hget]; congr 1; congr 1
    exact hornerAccum_cons g c cs (pos + 1)
  · rw [hornerAccum_ge g (c :: cs) (pos + 1)
          (by simp; omega),
        hornerAccum_ge g cs pos (by omega)]
termination_by cs.length - pos
decreasing_by omega

/-- Decomposition: `listToGF216Poly (c :: cs) = C(c.toGF216) + X · listToGF216Poly cs`. -/
private lemma listToGF216Poly_cons
    (c : GF16)
    (cs : List GF16) :
    listToGF216Poly (c :: cs) =
      C (c.toGF216) + X * listToGF216Poly cs := by
  ext m
  cases m with
  | zero =>
    simp only [coeff_add, listToGF216Poly_coeff,
               dif_pos (show 0 < (c :: cs).length from by simp)]
    simp only [List.get_eq_getElem, List.getElem_cons_zero,
               coeff_C_zero, coeff_X_mul_zero, add_zero]
  | succ n =>
    simp only [coeff_add, coeff_C_succ, zero_add, coeff_X_mul,
               listToGF216Poly_coeff]
    by_cases hlt : n + 1 < (c :: cs).length
    · rw [dif_pos hlt, dif_pos (show n < cs.length from by simp at hlt; omega)]
      congr 1
    · rw [dif_neg hlt, dif_neg (show ¬(n < cs.length) from by simp at hlt ⊢; omega)]

/--
**`hornerAccum` at position 0 equals polynomial evaluation.**
    This connects the Horner-scheme computation `hornerAccum g coeffs 0`
    to the Mathlib `Polynomial.eval` of `listToGF216Poly coeffs`.
-/
private lemma hornerAccum_zero_eq_eval
    (g : GF16)
    (coeffs : List GF16) :
    hornerAccum g coeffs 0 =
      (listToGF216Poly coeffs).eval (g.toGF216) := by
  induction coeffs with
  | nil =>
    rw [hornerAccum_ge g [] 0 (by simp)]
    simp
  | cons c cs ih =>
    rw [hornerAccum_unfold g (c :: cs) 0 (by simp)]
    simp only [List.get_eq_getElem, List.getElem_cons_zero]
    rw [hornerAccum_cons g c cs 0, ih, listToGF216Poly_cons]
    simp [eval_add, eval_mul, eval_C, eval_X]

/-! ## injectivity.toGF216 at zero -/

/- If `n.toGF216 = 0` and `n < 2^16`, then `n = 0`.
    Uses the kernel characterization of the ring homomorphism
    `BinaryPoly.toGF216`: since `polyGF2` is irreducible in the PID
    `BinaryPoly`, the ideal `(polyGF2)` is maximal, and
    `ker BinaryPoly.toGF216 = (polyGF2)`.  Any element of
    `ker BinaryPoly.toGF216` with degree `< 16` must therefore be
    zero. -/
open spqr.encoding.gf.unaccelerated in
private lemma Nat_toGF216_eq_zero
    {n : Nat} (hn : n < 2 ^ 16) (h : n.toGF216 = 0) : n = 0 := by
  unfold Nat.toGF216 at h
  by_contra hn0
  have hne : natToBinaryPoly n ≠ 0 := fun h0 =>
    hn0 (natToBinaryPoly_inj
      (by rw [h0, natToBinaryPoly_zero] : natToBinaryPoly n = natToBinaryPoly 0))
  have hcoeff_zero : ∀ m, 16 ≤ m → (natToBinaryPoly n).coeff m = 0 := by
    intro m hm
    rw [natToBinaryPoly_coeff]
    simp [Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num : 0 < 2) hm))]
  have hnd : (natToBinaryPoly n).natDegree < 16 := by
    by_contra h_not
    push_neg at h_not
    have h_lc : (natToBinaryPoly n).coeff (natToBinaryPoly n).natDegree ≠ 0 := by
      intro h0; exact hne (Polynomial.leadingCoeff_eq_zero.mp h0)
    exact h_lc (hcoeff_zero _ h_not)
  have hprime : Prime polyGF2 :=
    (UniqueFactorizationMonoid.irreducible_iff_prime).mp polyGF2_irreducible
  have hprime_ideal : (Ideal.span {polyGF2}).IsPrime :=
    (Ideal.span_singleton_prime polyGF2_monic.ne_zero).mpr hprime
  have hne_bot : Ideal.span ({polyGF2} : Set BinaryPoly) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact polyGF2_monic.ne_zero
  have hmax : (Ideal.span {polyGF2}).IsMaximal :=
    Ideal.IsPrime.isMaximal hprime_ideal hne_bot
  have hle : Ideal.span {polyGF2} ≤ RingHom.ker BinaryPoly.toGF216 :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (RingHom.mem_ker.mpr BinaryPoly.toGF216_polyGF2))
  have hker_eq : RingHom.ker BinaryPoly.toGF216 = Ideal.span {polyGF2} := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact heq.symm
    · exact absurd (hmax.out.2 _ hlt) (RingHom.ker_ne_top BinaryPoly.toGF216)
  have hmem : polyGF2 ∣ natToBinaryPoly n := by
    rwa [← Ideal.mem_span_singleton, ← hker_eq, RingHom.mem_ker]
  have := Polynomial.natDegree_le_of_dvd hmem hne
  rw [polyGF2_natDegree] at this
  omega

/--
If `g.toGF216 = 0`, then `g.value.val = 0`.
    This is the reverse direction of `GF16.toGF216_zero_val`.
-/
private lemma GF16.toGF216_eq_zero_imp
    (g : GF16) (h : g.toGF216 = 0) :
    g.value.val = 0 := by
  unfold GF16.toGF216 at h
  exact Nat_toGF216_eq_zero (by have := g.value.hBounds; scalar_tac) h

/-! ## Spec for core.fmt.Arguments.from_str -/

/--
The `from_str` function always succeeds (returns `ok`).  This is the
    Lean model for `core::fmt::Arguments::from_str` which builds a format
    argument from a string literal.  `step*` unfolds `from_str` directly
    and can discharge the `fail panic` branch automatically.
-/
lemma core_fmt_Arguments_from_str_spec (s : Str) :
    core.fmt.Arguments.from_str s
      ⦃ (_ : core.fmt.Arguments) => True ⦄ := by
  unfold core.fmt.Arguments.from_str
  simp [WP.spec_ok]

/-!
## Spec theorem for `spqr.encoding.polynomial.Poly.lagrange_interpolate_complete`

The theorem `lagrange_interpolate_complete_spec` is the top-level correctness specification for the
Rust function `Poly::lagrange_interpolate_complete` (`src/encoding/polynomial.rs`, lines 197–223).

**What the Rust function does:**

Given a polynomial `self` (whose coefficients represent the product `∏ⱼ (X − pⱼ.x)` over all
points), a point slice `pts`, and an index `i`, the function:

1. **Loop 0 (denominator accumulation):** Iterates over `pts` to compute `denominator = ∏_{j ≠ i}
   (pᵢ.x − pⱼ.x)`, the Lagrange basis denominator for the i-th point.

2. **Scaling:** Computes `scale = pᵢ.y / denominator`. In GF(2¹⁶), division by `d` is multiplication
   by `d^(2¹⁶ − 2)` (Fermat's little theorem), so `scale = pᵢ.y · denominator^(2¹⁶ − 2)`.

3. **Loop 1 (polynomial long division + scaling):** Divides out the factor `(X − pᵢ.x)` from `self`
   using synthetic/Horner-style long division (processing coefficients from high to low degree), and
   simultaneously scales each coefficient by `scale`. Due to the little-endian coefficient
   representation, the result is implicitly multiplied by `X` (the leading zero coefficient is left
   in place).

4. **Debug assertion:** Asserts `self.coefficients[0] == GF16::ZERO`, confirming the division was
   exact (i.e., `pᵢ.x` was indeed a root).

The net effect is to produce a new polynomial `result` such that:
  `result(X) · (X − pᵢ.x) = X · scale · self(X)`

**Parameters:**
- `self : Poly` — The input polynomial, stored as a `Vec<GF16>` of coefficients in ascending degree
  order. Typically this is the product polynomial `∏ⱼ (X − pⱼ.x)` over all interpolation points.
- `pts : Slice Pt` — A slice of `Pt` values, where each `Pt` has fields `x : GF16` (evaluation
  point) and `y : GF16` (desired value).
- `i : Std.Usize` — Index of the distinguished point `pᵢ = pts[i]` for which we are building the
  Lagrange basis polynomial.

```
    (hi : i.val < pts.val.length)
```

**Precondition 1 — Index in bounds:** `i` is a valid index into the points slice. This mirrors the
Rust `#[hax_lib::requires(i < pts.len())]` annotation.

```
    (hlen : 0 < self.coefficients.val.length)
```

**Precondition 2 — Non-empty polynomial:** The polynomial has at least one coefficient. This ensures
that the long-division loop (loop 1, which iterates `1..coefficients.len()`) and the debug assertion
(`coefficients[0]`) are well-defined.

```
    (heval : self.evalAt (pts.val.get ⟨i.val, hi⟩).x = 0)
```

**Precondition 3 — Root condition:** The polynomial `self` evaluates to zero at `pᵢ.x`.
Mathematically, `self.toGF216Poly.eval(GF16.toGF216(pᵢ.x)) = 0`, meaning `(X − pᵢ.x)` divides `self`
in `GF(2¹⁶)[X]`. This is the crucial algebraic precondition that guarantees the long division in
loop 1 is exact (no remainder), which is what the `debug_assert_eq!` checks at runtime.

Without this precondition, the division would leave a non-zero remainder in `coefficients[0]`, and
the polynomial identity in the postcondition would not hold.


**Postcondition — a weakest-precondition (WP) spec:** The function succeeds (no panic) and produces
a `result : Poly` satisfying two properties:

```
        result.coefficients.val.length =
          self.coefficients.val.length ∧
```

**Postcondition Part 1 — Length preservation:** The output polynomial has the same number of
coefficients as the input. This is because the function modifies coefficients in-place (synthetic
division + scaling) without adding or removing entries. The `X`-scaling artifact means `result` has
an extra leading zero at position 0, but the vector length is unchanged.

```
        result.toGF216Poly *
          (X - C (GF16.toGF216
            (pts.val.get ⟨i.val, hi⟩).x)) =
          X * C (lagrangeScaleGF216
            (pts.val.get ⟨i.val, hi⟩) pts.val) *
            self.toGF216Poly ⦄
```

**Postcondition Part 2 — Polynomial identity:** The core mathematical content. In `GF(2¹⁶)[X]`:

  `result(X) · (X − pᵢ.x) = X · lagrangeScale(pᵢ, pts) · self(X)`

where:
- `result.toGF216Poly` is the mathematical polynomial corresponding to the output coefficient
  vector.
- `(X − C(GF16.toGF216(pᵢ.x)))` is the linear factor that was divided out by the long-division loop.
- `lagrangeScaleGF216(pᵢ, pts)` is the Lagrange scaling factor defined as:
  ```
  lagrangeScaleGF216(pᵢ, pts) =
    GF16.toGF216(pᵢ.y) · (∏_{j, pⱼ.x ≠ pᵢ.x} (pᵢ.x − pⱼ.x))^(2¹⁶ − 2)
  ```
  This equals `pᵢ.y / ∏_{j≠i}(pᵢ.x − pⱼ.x)` using Fermat inversion in
  GF(2¹⁶).
- `X · C(scale) · self.toGF216Poly` captures the `X`-scaling artifact: the result is the quotient
  `self / (X − pᵢ.x)` scaled by `lagrangeScale`, but shifted up by one degree (multiplied by `X`).

**Why the `X` factor?**  The Rust code processes coefficients in-place starting from the high end,
and the quotient naturally lands one position higher than expected in the little-endian vector.
Rather than shifting all coefficients down (which would be O(n) extra work), the function leaves the
zero at `coefficients[0]` and lets the caller remove it via `coefficients.remove(0)` (see
`lagrange_interpolate_pt`).

**Algebraic meaning:**  If we define `Q(X) = self(X) / (X − pᵢ.x)` (the exact polynomial quotient,
which exists by the root precondition), then the identity says:
  `result(X) = X · lagrangeScale(pᵢ, pts) · Q(X)`
After the caller strips the leading zero (divides by `X`), the final polynomial is
`lagrangeScale(pᵢ, pts) · Q(X)`, which is exactly the i-th Lagrange basis polynomial scaled to
produce `pᵢ.y` at `pᵢ.x`.
-/

@[step]
theorem lagrange_interpolate_complete_spec
    (self : Poly) (pts : Slice Pt) (i : Usize)
    (hi : i.val < pts.val.length)
    (hlen : 0 < self.coefficients.val.length)
    (heval : self.evalAt (pts.val.get ⟨i.val, hi⟩).x = 0) :
    lagrange_interpolate_complete self pts i
      ⦃ (result : Poly) =>
        result.coefficients.val.length =
          self.coefficients.val.length ∧
        result.toGF216Poly *
          (X - C (GF16.toGF216
            (pts.val.get ⟨i.val, hi⟩).x)) =
          X * C (lagrangeScaleGF216
            (pts.val.get ⟨i.val, hi⟩) pts.val) *
            self.toGF216Poly ⦄ := by
  unfold lagrange_interpolate_complete
  step*
  case h2 =>
    simp only [core.fmt.Arguments.from_str, bind_tc_ok,
    List.get_eq_getElem, X_mul_C, WP.spec_fail]
    rename_i _ _ _ _ loop0_fst_eq _ _ _ _ h_not_b
    have hpi_eq : pi = pts.val.get ⟨i.val, hi⟩ := by
      rw [List.get_eq_getElem, List.Inhabited_getElem_eq_getElem!]
      exact pi_post
    have hH0 : hornerAccum
        (pts.val.get ⟨i.val, hi⟩).x self.coefficients.val 0 = 0 := by
      rw [hornerAccum_zero_eq_eval]
      unfold Poly.evalAt Poly.toGF216Poly at heval
      exact heval
    have h0_len : 0 < v.val.length := by omega
    have hv0_zero : (v.val.get ⟨0, h0_len⟩).toGF216 = 0 := by
      rw [v_post3 h0_len, loop0_fst_eq, hpi_eq]; exact hH0
    have hlv_get : left_val = v.val.get ⟨0, h0_len⟩ := by
      rw [List.get_eq_getElem, List.Inhabited_getElem_eq_getElem!]
      exact left_val_post
    have hlv_val_zero : left_val.value.val = 0 :=
      GF16.toGF216_eq_zero_imp left_val (by rw [hlv_get]; exact hv0_zero)
    have hlv_eq_zero : left_val.value = spqr.encoding.gf.GF16.ZERO.value :=
      UScalar.eq_of_val_eq (by simp only [spqr.encoding.gf.GF16.ZERO]; exact hlv_val_zero)
    have :=h_not_b (b_post.mpr hlv_eq_zero)
    simp[this]
  case h1 =>
    rename_i _ _ loop0_res _ loop0_fst_eq loop0_snd_eq _ _ _ hb
    have hpi_eq : pi = pts.val.get ⟨i.val, hi⟩ := by
      rw [List.get_eq_getElem, List.Inhabited_getElem_eq_getElem!]
      exact pi_post
    have hlv_zero := b_post.mp hb
    have hH0 : hornerAccum
        loop0_res.1.x self.coefficients.val 0 = 0 := by
      have h0 : 0 < v.val.length := by omega
      rw [← v_post3 h0]
      have hlv_get : left_val = v.val.get ⟨0, h0⟩ := by
        rw [List.get_eq_getElem, List.Inhabited_getElem_eq_getElem!]
        exact left_val_post
      rw [← hlv_get]
      have hval_zero : left_val.value.val = 0 := by
        have := congr_arg UScalar.val hlv_zero
        simp only [gf.GF16.ZERO, UScalar.ofNatCore_val_eq] at this
        exact this
      exact GF16.toGF216_zero_val left_val hval_zero
    have hscale_eq : scale.toGF216 =
        lagrangeScaleGF216 (pts.val.get ⟨i.val, hi⟩)
          pts.val := by
      unfold lagrangeScaleGF216
      rw [loop0_fst_eq] at scale_post
      rw [scale_post]
      rw [iter_post1, iter_post2] at loop0_snd_eq
      simp only [spqr.encoding.gf.GF16.ONE_toGF216,
        one_mul] at loop0_snd_eq
      rw [loop0_snd_eq, hpi_eq]
    rw [loop0_fst_eq] at v_post2 v_post3 hH0
    rw [hpi_eq] at v_post2 v_post3 hH0
    constructor
    · exact v_post1
    · unfold Poly.toGF216Poly
      apply poly_identity_from_loop1
        self.coefficients.val v.val
        (pts.val.get ⟨i.val, hi⟩).x
        (lagrangeScaleGF216
          (pts.val.get ⟨i.val, hi⟩) pts.val)
      · exact v_post1
      · exact hlen
      · intro h0; rw [v_post3 h0, hH0]
      · exact hH0
      · intro k hk hk_pos
        rw [v_post2 k hk hk_pos, hscale_eq]

end spqr.encoding.polynomial.Poly
