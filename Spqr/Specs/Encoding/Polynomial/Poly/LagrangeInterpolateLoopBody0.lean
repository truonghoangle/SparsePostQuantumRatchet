/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateComplete
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateLoop1

/-!
# Spec theorem for `lagrange_interpolate`: loop body 0

The outer Rust function `Poly::lagrange_interpolate` (in `src/encoding/polynomial.rs`, lines
106:4-137:5) computes the unique polynomial of degree `< pts.len()` that interpolates a set of
points `pts : &[Pt]` with distinct x-coordinates.  After preparing the "product" polynomial
  `template = ∏_j (X − pts[j].x)`
and unrolling the first iteration, the function maintains two parallel coefficient vectors:

  * `out : Poly` — the running interpolant of degree `< pts.len()`,
    whose coefficient vector `v` has length `pts.len() − 1`;
  * `working : Poly` — a scratch polynomial whose coefficient vector
    has length `pts.len()` and is *re-loaded from `template` at the
    start of every iteration* via `copy_from_slice`.

The body of the outer loop processes the `i`-th point (lines 122:8-135:9):

  1. **Reset `working` from `template`**:
     `working.coefficients.copy_from_slice(&template.coefficients)`
     — restores `working = template = ∏_j (X − pts[j].x)`.
  2. **Compute the `i`-th Lagrange contribution in place**:
     `working.lagrange_interpolate_complete(pts, i)`.  By the spec
     of `lagrange_interpolate_complete`, the new polynomial
     `working₁` satisfies the polynomial identity
     ```
       working₁ · (X − pts[i].x) =
         X · C(lagrangeScale(pts[i], pts)) · template
     ```
     i.e. `working₁ = X · pᵢ.y · ∏_{j ≠ i} (X − pts[j].x) /
     ∏_{j ≠ i} (pts[i].x − pts[j].x)` (the `X` factor is the
     "shifted-up by one position" artifact described in
     `LagrangeInterpolateComplete`).
  3. **Add the contribution to `out`, simultaneously dividing by `X`**:
     the inner `for j in 0..out.coefficients.len()` loop executes
       `out.coefficients[j] += working.coefficients[j + 1]`
     for every `j` in `0..out.coefficients.len()`.  Reading from
     `working.coefficients[j + 1]` rather than `j` is exactly the
     "divide by `X`" trick: it shifts `working₁` down by one position
     without performing a `memmove`.  This inner loop is specified by
     `lagrange_interpolate_loop0_loop0.loop_spec`.

Concretely, the extracted Lean body `encoding.polynomial.Poly.lagrange_interpolate_loop0.body`
performs one step of this outer loop.  Given the slice `pts`, the fixed `template`, the range
iterator `iter : 1..pts.len()`, the current coefficient vector `v` of `out`, and the scratch
polynomial `working`, it:

  1. Retrieves the next index `i` from the range iterator.
  2. If the iterator is exhausted (`none`), returns `done v` — the
     outer loop is complete and the unchanged vector `v` is propagated
     out.
  3. Otherwise, deref's `working.coefficients` to a mutable slice `s`,
     deref's `template.coefficients` to the (immutable) slice `s1`,
     copies `s1` into `s` via `core.slice.Slice.copy_from_slice`,
     writes the result back to produce a fresh `Vec` `v1`, calls
     `Poly.lagrange_interpolate_complete { coefficients := v1 } pts i`
     to obtain `working₁`, reads `i1 = v.len`, calls
     `Poly.lagrange_interpolate_loop0_loop0 (0..i1) v working₁` to
     obtain the updated coefficient vector `v₂` and the (unchanged)
     polynomial `working₂ = working₁`, and finally returns
     `cont (iter1, v₂, working₂)` with the iterator advanced.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the 16-bit
encodings:
  `a + b = a − b = a ⊕ b`,
so the `+=` performed by the inner loop is the same as the in-place addition used by the Rust
`AddAssign` instance for `GF16`.

**Source**: spqr/src/encoding/polynomial.rs (lines 122:8-135:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

/--
The range iterator `next` always returns `ok` and either provides the current `start` value (when
`start < end`) or `none` (when `start ≥ end`).  This is the concrete specification for the
`core.ops.range.Range<usize>` iterator used in the Rust `for i in 1..pts.len()` loop.
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
**Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_loop0.body`**:

One step of the outer Lagrange-interpolation loop.  Given the slice `pts`, a fixed `template`
polynomial (the product `∏_j (X − pts[j].x)` precomputed by `lagrange_interpolate_prepare`), a
range iterator over the unprocessed indices, the current coefficient vector `v` of the running
interpolant, and the scratch polynomial `working`, the body processes the next index from the
iterator:

• The function always succeeds (no panic) provided the preconditions hold, since
  `Vec.deref_mut`, `Vec.deref`, `Slice.copy_from_slice` (with matching lengths), the
  `lagrange_interpolate_complete` call (with the root precondition), and the inner
  `lagrange_interpolate_loop0_loop0` (with the length preconditions) are total under those
  assumptions.
• In the `done` case (iterator exhausted):
    the coefficient vector `v` is returned unchanged, and the iterator
    condition is negated: `¬ (iter.start.val < iter.«end».val)`.
• In the `cont` case (index `i = iter.start.val` processed):
    - The iterator has advanced by exactly one position:
        `iter1.start = iter.start + 1`,
        `iter1.«end» = iter.«end»`.
    - The coefficient-vector length is preserved:
        `v₂.val.length = v.val.length`.
    - The new scratch polynomial `working₂` has the same coefficient
      vector length as `template`:
        `working₂.coefficients.val.length =
            template.coefficients.val.length`.
    - **`working₂` is the `i`-th Lagrange contribution** of `template`,
      shifted up by one position; equivalently the polynomial identity
        `working₂.toGF216Poly · (X − C(pts[i].x.toGF216)) =
            X · C(lagrangeScaleGF216 pts[i] pts) ·
              template.toGF216Poly`
      holds in `GF216[X]`.
    - **Inner-loop update** on the running interpolant: for every
      coefficient position `j ∈ [0, v.length)`,
        `v₂.val[j].toGF216 =
            v.val[j].toGF216 +
            working₂.coefficients.val[j + 1].toGF216`
      where the `+` on the right-hand side is addition in
      `GF216 = GaloisField 2 16` (which, in characteristic 2,
      coincides with subtraction and is bitwise XOR of the 16-bit
      encodings).  Reading at position `j + 1` is the "divide by `X`"
      trick that strips the leading-zero coefficient artifact of
      `working₂` without an explicit shift.

The preconditions are exactly the loop invariants maintained by the surrounding outer Rust loop
(`out.coefficients.len() == _w_l - 1` and `working.coefficients.len() == _w_l`) together with the
algebraic root condition required by `lagrange_interpolate_complete`:

* `iter.«end».val ≤ pts.val.length` — every iterator index is a
  valid point index.
* `0 < template.coefficients.val.length` — the prepared product
  polynomial is non-empty (true for `pts.len() ≥ 1`).
* `v.val.length < template.coefficients.val.length` — the running
  interpolant has one fewer coefficient than the scratch polynomial,
  so the inner-loop read at position `j + 1` is always in range.
* `template.coefficients.val.length =
    working.coefficients.val.length` — the `copy_from_slice` call
  requires matching slice lengths.
* For the current index `i = iter.start.val`,
  `template.evalAt pts[i].x = 0` — this is the algebraic root
  precondition required by `lagrange_interpolate_complete`, and it
  holds because `template = ∏_j (X − pts[j].x)` vanishes at every
  `pts[j].x` (see `LagrangeInterpolatePrepare`).

**Source**: spqr/src/encoding/polynomial.rs (lines 122:8-135:9)
-/
@[step]
theorem body_spec
    (pts : Slice spqr.encoding.polynomial.Pt)
    (template : Poly)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (working : Poly)
    (h_end_le_pts : iter.«end».val ≤ pts.val.length)
    (h_template_pos : 0 < template.coefficients.val.length)
    (h_v_lt : v.val.length < template.coefficients.val.length)
    (h_wt : template.coefficients.val.length = working.coefficients.val.length)
    (h_eval : iter.start.val < iter.«end».val →
        ∀ (hi : iter.start.val < pts.val.length),
          template.evalAt (pts.val.get ⟨iter.start.val, hi⟩).x = 0) :
    body pts template iter v working ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬ (iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, v₂, working₂) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          v₂.val.length = v.val.length ∧
          working₂.coefficients.val.length =
            template.coefficients.val.length ∧
          (∀ (hi : iter.start.val < pts.val.length),
            working₂.toGF216Poly *
              (X - C (GF16.toGF216
                (pts.val.get ⟨iter.start.val, hi⟩).x)) =
              X * C (lagrangeScaleGF216
                (pts.val.get ⟨iter.start.val, hi⟩) pts.val) *
                template.toGF216Poly) ∧
          (∀ (j : Nat) (hj : j < v₂.val.length),
            (v₂.val.get ⟨j, hj⟩).toGF216 =
              (v.val[j]!).toGF216 +
              (working₂.coefficients.val[j + 1]!).toGF216) ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := IteratorRange_next_Usize_post iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    simp only
    have hi_pts : iter.start.val < pts.val.length := by omega
    have h_eval_t : template.evalAt (pts.val.get ⟨iter.start.val, hi_pts⟩).x = 0 :=
      h_eval h_lt hi_pts
    have h_match_len :
        (alloc.vec.Vec.deref_mut working.coefficients).1.length =
        (alloc.vec.Vec.deref template.coefficients).length := by
      simp only [alloc.vec.Vec.deref_mut, alloc.vec.Vec.deref, Slice.length]
      exact h_wt.symm
    have hv1_val :
        ((alloc.vec.Vec.deref_mut working.coefficients).2
          (alloc.vec.Vec.deref template.coefficients)).val = template.coefficients.val := by
      simp only [alloc.vec.Vec.deref_mut, alloc.vec.Vec.deref]
    have h_toGF_eq :
      ({coefficients := (alloc.vec.Vec.deref_mut working.coefficients).2
                          (alloc.vec.Vec.deref template.coefficients)}
        : encoding.polynomial.Poly).toGF216Poly = template.toGF216Poly := by
      unfold Poly.toGF216Poly
      rw [hv1_val]
    have h_poly_eval :
      ({coefficients := (alloc.vec.Vec.deref_mut working.coefficients).2
                          (alloc.vec.Vec.deref template.coefficients)}
        : encoding.polynomial.Poly).evalAt
          (pts.val.get ⟨iter.start.val, hi_pts⟩).x = 0 := by
      unfold Poly.evalAt
      rw [h_toGF_eq]
      exact h_eval_t
    have h_v1_len :
        0 < ({coefficients := (alloc.vec.Vec.deref_mut working.coefficients).2
                                (alloc.vec.Vec.deref template.coefficients)}
              : encoding.polynomial.Poly).coefficients.val.length := by
      change 0 < ((alloc.vec.Vec.deref_mut working.coefficients).2
                  (alloc.vec.Vec.deref template.coefficients)).val.length
      rw [hv1_val]
      exact h_template_pos
    simp only [lift, bind_tc_ok]
    have h_copy :=
      core.slice.Slice.copy_from_slice.step_spec
        encoding.gf.GF16.Insts.CoreMarkerCopy
        (alloc.vec.Vec.deref_mut working.coefficients).1
        (alloc.vec.Vec.deref template.coefficients)
        h_match_len
    have h_complete :=
      lagrange_interpolate_complete_spec
        { coefficients := (alloc.vec.Vec.deref_mut working.coefficients).2
                            (alloc.vec.Vec.deref template.coefficients) }
        pts iter.start hi_pts h_v1_len h_poly_eval
    have h_v_len_val : (alloc.vec.Vec.len v).val = v.val.length := by
      simp [alloc.vec.Vec.len]
    step*
  · obtain ⟨h_opt_eq, h_range_eq⟩ := h_none (by omega)
    rw [h_opt_eq]
    simp only [WP.spec_ok]
    exact ⟨trivial, h_lt⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0
