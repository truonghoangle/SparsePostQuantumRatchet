/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.GF16.AddAssign

/-!
# Spec theorem for `lagrange_interpolate`: loop body 1

The outer Rust function `Poly::lagrange_interpolate` (in `src/encoding/polynomial.rs`, lines
106:4-137:5) computes the unique polynomial of degree `< pts.len()` that interpolates a set of
points `pts : &[Pt]` with distinct x-coordinates.  After preparing the "product" polynomial
  `template = ∏_j (x − pts[j].x)`
and unrolling the first iteration, the function maintains two parallel coefficient vectors:

  * `out : Poly` — the running interpolant of degree `< pts.len()`,
    whose coefficient vector has length `pts.len() − 1 + 1 = pts.len()`;
  * `working : Poly` — the per-iteration contribution
    `pi.y · ∏_{j ≠ i} (x − pts[j].x) / ∏_{j ≠ i} (pi.x − pts[j].x)`
    *shifted up by one position* (i.e. `working` represents
    `x · <the polynomial we need>`), so its coefficient vector has
    length `pts.len() + 1`.

To add the `i`-th contribution to `out` *and* divide by `x` simultaneously, the inner `for j in
0..out.coefficients.len()` loop (lines 131:12-134:13) executes

  `out.coefficients[j] += working.coefficients[j + 1]`

for each `j` in `0..out.coefficients.len()`.  Reading from index `j + 1` rather than `j` is exactly
the "divide by x" trick that the source-level comment describes: it shifts `working` down by one
position without performing a `memmove`.

Concretely, the extracted Lean body `encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0.body`
performs one step of this inner loop.  Given the (fixed) polynomial `working`, the range iterator
`iter : 0..out.coefficients.len()`, and the current coefficient vector `v` of `out`, it:

  1. Retrieves the next index `j` from the range iterator.
  2. If the iterator is exhausted (`none`), returns `done (v, working)`
     — the inner loop is complete and the unchanged pair
     `(v, working)` is propagated to the outer loop.
  3. Otherwise, calls `Vec::index_mut(v, j)` to obtain a mutable
     reference `g = v[j]` together with the write-back closure
     `index_mut_back`, computes `i = j + 1`, reads
     `g1 = working.coefficients[i]`, performs the GF(2¹⁶) sum
     `g2 = g + g1` via
     `encoding.gf.GF16.Insts.CoreOpsArithAddAssignGF16.add_assign`,
     writes back `v[j] := g2`, and returns `cont (iter1, v1)` with
     the iterator advanced and the updated vector.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the 16-bit
encodings:
  `a + b = a − b = a ⊕ b`
so `add_assign` is the same as the in-place addition used by the Rust `+=` operator on `GF16`.

**Source**: spqr/src/encoding/polynomial.rs (lines 131:12-134:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

/--
The range iterator `next` always returns `ok` and either provides the current `start` value (when
`start < end`) or `none` (when `start ≥ end`).  This is the concrete specification for the
`core.ops.range.Range<usize>` iterator used in the Rust `for j in 0..out.coefficients.len()` loop.
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
**Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0.body`**:

One step of the inner Lagrange-interpolation accumulation `out.coefficients[j] +=
working.coefficients[j + 1]`.  Given a fixed polynomial `working` (the shifted per-iteration
contribution), a range iterator over `0..out.coefficients.len()`, and the current coefficient vector
`v` of `out`, the body processes the next index from the iterator:

• The function always succeeds (no panic) for any valid inputs satisfying the preconditions, since
  `Vec.index_mut`, `Usize` addition (within bounds), `Vec.index`, and the by-value
  `AddAssign<GF16>::add_assign` are all total on bounded integers within range.
• In the `done` case (iterator exhausted):
    both the coefficient vector `v` and the polynomial `working` are
    returned unchanged, and the iterator condition is negated:
    `¬ (iter.start.val < iter.«end».val)`.
• In the `cont` case (index `j = iter.start.val` processed):
    - The iterator has advanced by exactly one position:
        `iter1.start = iter.start + 1`, `iter1.«end» = iter.«end»`.
    - The coefficient vector length is preserved:
        `v1.val.length = v.val.length`.
    - Position `j = iter.start.val` has been updated with the
      GF(2¹⁶) sum
        `v1[j].toGF216 =
            v[j].toGF216 +
            working.toGF216.coefficients[j + 1]`
      where the `+` on the right-hand side is addition in
      `GF216 = GaloisField 2 16` (which, in characteristic 2,
      coincides with subtraction and is bitwise XOR of the 16-bit
      encodings).
    - All other positions are unchanged:
        `v1.val[k]? = v.val[k]?`  for `k ≠ j`.

The two preconditions `iter.«end».val ≤ v.val.length` and `iter.«end».val <
working.coefficients.val.length` are exactly the invariants maintained by the surrounding outer
loop:

  `out.coefficients.len() == _w_l - 1`  and
  `working.coefficients.len() == _w_l`,

which together guarantee that for every `j < iter.«end».val ≤ out.coefficients.len()` both `v[j]`
and `working.coefficients[j + 1]` are valid reads.

**Source**: spqr/src/encoding/polynomial.rs (lines 131:12-134:13)
-/
@[step]
theorem body_spec
    (working : encoding.polynomial.Poly)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec encoding.gf.GF16)
    (h_end_le_v : iter.«end».val ≤ v.val.length)
    (h_end_lt_working : iter.«end».val < working.coefficients.val.length) :
    body working iter v ⦃ cf =>
      match cf with
      | ControlFlow.done (v', working') =>
          v' = v ∧ working' = working ∧ ¬ (iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, v1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          v1.val.length = v.val.length ∧
          (∀ (h_idx : iter.start.val < v1.val.length),
            (v1.val.get ⟨iter.start.val, h_idx⟩).toGF216 =
              (v.val[iter.start.val]!).toGF216 +
              (working.coefficients.val[iter.start.val + 1]!).toGF216) ∧
          (∀ (k : Nat),
            k ≠ iter.start.val →
            v1.val[k]? = v.val[k]?) ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext, h_none, h_some⟩ := IteratorRange_next_Usize_post iter
  rw [hnext]; simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]; simp only
    have h_j_lt_v : iter.start.val < v.val.length := by omega
    have h_jp1_lt_w : iter.start.val + 1 < working.coefficients.val.length := by
      omega
    step*
    rename_i _ hxset hxclo _ _
    rw [hxclo]
    refine ⟨h_lt, h_start1, h_end1, by
              simp [alloc.vec.Vec.set_val_eq], ?_, ?_⟩
    · intro h_idx
      simp only [alloc.vec.Vec.set_val_eq, List.get_eq_getElem,
                 List.getElem_set_self]
      rw [g2_post, hxset]
      simp [g1_post, i_post]
    · intro k hk
      simp [alloc.vec.Vec.set_val_eq, hk]
  · obtain ⟨h_opt_eq, h_range_eq⟩ := h_none (by omega)
    rw [h_opt_eq]; simp only [WP.spec_ok]
    exact ⟨trivial, trivial, by omega⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0
