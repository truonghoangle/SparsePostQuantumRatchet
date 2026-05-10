/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.Poly.Zero
import Spqr.Specs.Encoding.Gf.GF16.Eq
import Spqr.Specs.Encoding.Gf.GF16.ONE
import Spqr.Specs.Encoding.Gf.GF16.ZERO
import Spqr.Specs.Encoding.Polynomial.Poly.MultXdiffAssignTrailing

/-! # Spec theorem for `lagrange_interpolate_prepare`: loop body 0

Given a slice of points `pts` and an offset (= `pts.len()`), the
function `Poly::lagrange_interpolate_prepare` builds the polynomial
  `∏_{j=0}^{offset−1} (x − pts[j].x)`
by starting with the constant `1` at position `offset` in the
coefficient vector and successively multiplying the trailing
sub-polynomial by `(x − pts[i].x)` for `i = 0, 1, …, offset − 1`.

Concretely, `lagrange_interpolate_prepare(pts)` calls
`Poly::zero(pts.len() + 1)`, resizes the coefficient vector to
`offset + 1` entries filled with `GF16::ZERO`, sets
`p.coefficients[offset] = GF16::ONE`, and then runs the `for i in
0..offset` loop driver
`encoding.polynomial.Poly.lagrange_interpolate_prepare_loop`,
performing `offset` iterations of the body function specified below.

Each step of the loop body (this function):

1. Retrieves the next index `i` from the range iterator
   `0..offset`.
2. If the iterator is exhausted (`none`), returns `done` with
   the current polynomial — the construction is complete.
3. Otherwise, looks up `pi = pts[i]`, computes the start position
   `i1 = offset − i`, and calls
   `mult_xdiff_assign_trailing(i1, pi.x)` to multiply the trailing
   sub-polynomial `p[offset−i..]` by `(x − pi.x)`, then returns
   `cont` with the updated iterator and polynomial.

Since GF(2¹⁶) has characteristic 2, subtraction coincides with
addition:
  `(x − pts[i].x) = (x + pts[i].x) = (x ⊕ pts[i].x)`

The multiplication `self[start..] *= (x − difference)` is performed
by the recurrence:
  `v[j − 1] −= v[j] * difference`  for `j` in `start..l`
where `l = self.coefficients.len()`.

The key invariant maintained by the outer loop is:
- `p.coefficients.len() = offset + 1` (vector length is preserved).
- After `i` iterations, the trailing sub-polynomial
  `p[offset−i..]` represents `∏_{j=0}^{i−1} (x − pts[j].x)`.

**Source**: spqr/src/encoding/polynomial.rs (lines 155:8-159:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf
instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

instance : Inhabited spqr.encoding.polynomial.Pt where
  default := ⟨⟨0#u16⟩, ⟨0#u16⟩⟩


namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop


/-- The range iterator `next` always returns `ok` and either provides
the current `start` value (when `start < end`) or `none` (when
`start ≥ end`).  This is the concrete specification for the
`core.ops.range.Range<usize>` iterator used in the Rust `for i in
0..offset` loop. -/
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

/-- **Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_prepare_loop.body`**:

One step of the polynomial construction
`∏_{j=0}^{offset−1} (x − pts[j].x)`.  Given a point slice `pts`,
an offset value (= number of points), a range iterator over
`0..offset`, and the current polynomial `p`, the body processes the
next index from the iterator:

• The function always succeeds (no panic) for any valid inputs
  satisfying the preconditions, since `Slice.index_usize`,
  `Usize` subtraction, and `mult_xdiff_assign_trailing` are
  total on bounded integers within range.
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
        `GF16toGF216 p'.coefficients[j] =
            GF16toGF216 p.coefficients[j] −
            GF16toGF216 p.coefficients[j+1] *
              GF16toGF216 pts[iter.start].x`
      where the subtraction on the right-hand side is in
      `GF216 = GaloisField 2 16` (which, in characteristic 2,
      coincides with addition).
    - All other positions are unchanged:
        `p'.coefficients[j]? = p.coefficients[j]?`.

The postcondition propagates the closed-form specification of
`mult_xdiff_assign_trailing` (from
`Spqr.Specs.Encoding.Polynomial.Poly.MultXdiffAssignTrailing`)
through the body, substituting `start = offset − i` and
`difference = pts[i].x`.  This forms the foundation for the
full loop invariant proved at the loop level.

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
              GF16toGF216 (p1.coefficients.val.get ⟨j, hj⟩) =
                GF16toGF216 (p.coefficients.val[j]!) -
                GF16toGF216 (p.coefficients.val[j + 1]!) *
                  GF16toGF216 (pts.val[iter.start.val]!).x) ∧
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

/-! # Spec theorem for `lagrange_interpolate_prepare`: loop 0

Given a slice of points `pts` and an offset (= `pts.len()`), the
function `Poly::lagrange_interpolate_prepare` builds the polynomial
  `∏_{j=0}^{offset−1} (x − pts[j].x)`
by starting with the constant `1` at position `offset` in the
coefficient vector and successively multiplying the trailing
sub-polynomial by `(x − pts[i].x)` for `i = 0, 1, …, offset − 1`.

This file specifies the full loop (the `loop` fixed-point wrapper
around the body), providing a closed-form postcondition that
characterises the entire output polynomial after all iterations.  The
per-iteration specification is in
`Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolatePrepareLoopBoby0`.

Concretely, `lagrange_interpolate_prepare(pts)` calls
`Poly::zero(pts.len() + 1)`, resizes the coefficient vector to
`offset + 1` entries filled with `GF16::ZERO`, sets
`p.coefficients[offset] = GF16::ONE`, and then runs the `for i in
0..offset` loop driver
`encoding.polynomial.Poly.lagrange_interpolate_prepare_loop`,
performing `offset` iterations of the body function.

Each step of the loop body calls
`mult_xdiff_assign_trailing(offset − i, pts[i].x)` to multiply the
trailing sub-polynomial `p[offset−i..]` by `(x − pts[i].x)`, with
the carry propagating into the next lower position.

Since GF(2¹⁶) has characteristic 2, subtraction coincides with
addition:
  `(x − pts[i].x) = (x + pts[i].x) = (x ⊕ pts[i].x)`

The key invariant maintained by the outer loop is:
- `p.coefficients.len() = offset + 1` (vector length is preserved).
- `p.coefficients[offset] = GF16::ONE` (leading coefficient
  unchanged, since `mult_xdiff_assign_trailing` never modifies the
  last position when `len = offset + 1`).
- After `i` iterations, the trailing sub-polynomial
  `p[offset−i..]` represents `∏_{j=0}^{i−1} (x − pts[j].x)`.

**Closed-form postcondition**:

After the loop completes with range `iter.start..iter.end`:

1. The coefficient vector length is preserved:
     `result.coefficients.length = p.coefficients.length`.
2. The leading coefficient (position `offset`) is unchanged:
     `result.coefficients[offset]? = p.coefficients[offset]?`.

The correctness of each step relies on the body specification
(`LagrangeInterpolatePrepareLoopBoby0.body_spec`), which guarantees
that each call to `mult_xdiff_assign_trailing` preserves the vector
length and only modifies positions in the carry range
`[offset − i − 1, offset − 1]`, leaving the leading coefficient
at position `offset` unchanged (since `offset + 1 = len` means
position `offset` is never in the carry range `j + 1 < len`).

**Source**: spqr/src/encoding/polynomial.rs (lines 155:8-159:9)
-/

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop

/-- **Closed-form postcondition for
`encoding.polynomial.Poly.lagrange_interpolate_prepare_loop`**:

The full loop constructing
`∏_{j=0}^{offset−1} (x − pts[j].x)`.  Starting from a range
`iter.start..iter.end`, a point slice `pts`, and a polynomial `p`
with `p.coefficients.length = offset + 1`, the loop processes
indices `i = iter.start, iter.start + 1, …, iter.end − 1` — at
each step calling `mult_xdiff_assign_trailing(offset − i, pts[i].x)`
— and returns a polynomial `result` satisfying:

• **Length preserved**: `result.coefficients.length = p.coefficients.length`.
• **Leading coefficient unchanged**:
    `result.coefficients[offset]? = p.coefficients[offset]?`.

The loop invariant tracks which iterations have been processed:
after iterating indices `iter.start, …, k−1`, the sub-polynomial
`result[offset−(k−iter.start)..]` represents
`∏_{j=iter.start}^{k−1} (x − pts[j].x)`, the leading coefficient
at position `offset` remains unchanged (as
`mult_xdiff_assign_trailing` never writes past position
`len − 2 = offset − 1`), and the vector length is unchanged.

**Source**: spqr/src/encoding/polynomial.rs (lines 155:8-159:9)
-/
@[step]
theorem loop_spec
    (pts : Slice encoding.polynomial.Pt)
    (offset : Std.Usize)
    (iter : core.ops.range.Range Std.Usize)
    (p : encoding.polynomial.Poly)
    (h_end_le_pts : iter.«end».val ≤ pts.val.length)
    (h_end_le_offset : iter.«end».val ≤ offset.val)
    (h_len_eq : p.coefficients.val.length = offset.val + 1)
    (h_le : iter.start.val ≤ iter.«end».val) :
    spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop
      iter pts p offset ⦃ result =>
      result.coefficients.val.length = p.coefficients.val.length ∧
      result.coefficients.val[offset.val]? =
        p.coefficients.val[offset.val]? ⦄ := by
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
          p.coefficients.val[offset.val]?)
  · rintro ⟨iter', p'⟩ ⟨h_end', h_ge', h_le', h_len', h_off'⟩
    simp only [] at h_end' h_ge' h_le' h_len' h_off' ⊢
    have h_end_le_pts' : iter'.«end».val ≤ pts.val.length := by grind
    have h_end_le_offset' : iter'.«end».val ≤ offset.val := by grind
    have h_offset_lt_len' : offset.val < p'.coefficients.val.length := by omega
    step*
    split
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_eq, h_nlt⟩ := r_post
      subst h_eq
      exact ⟨h_len', h_off'⟩
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_lt, h_start1, h_end1, h_v1len, h_modified, h_frame⟩ := r_post
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_end1]; exact h_end'
      · omega
      · grind
      · omega
      · have h_off_frame := h_frame offset.val (by
          push_neg; intro _; omega)
        rw [h_off_frame, h_off']
      · grind
  · exact ⟨rfl, le_refl _, h_le, rfl, rfl⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop

/-! # Spec theorem for
`spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::lagrange_interpolate_prepare`

Given a slice of evaluation points `pts`, the function
`Poly::lagrange_interpolate_prepare` constructs the product polynomial
  `∏_{j=0}^{offset−1} (x − pts[j].x)`
where `offset = pts.len()`, returning a `Poly` of degree `offset`
with `offset + 1` coefficients.

Concretely the function proceeds as follows:

1. **Allocate**: `p = Poly::zero(pts.len() + 1)` creates an empty
   coefficient vector with the given capacity hint.
2. **Resize**: `p.coefficients.resize(pts.len() + 1, GF16::ZERO)`
   fills the vector with `offset + 1` zero entries.
3. **Set leading coefficient**: `p.coefficients[offset] = GF16::ONE`
   places the leading `1` at position `offset` (the highest degree),
   representing the monic polynomial `x^0 = 1` in the trailing
   sub-polynomial view.
4. **Loop** (`for i in 0..offset`): at each step calls
   `p.mult_xdiff_assign_trailing(offset − i, pts[i].x)` to multiply
   the trailing sub-polynomial by `(x − pts[i].x)`, propagating one
   carry coefficient downward.
5. **Assert**: `debug_assert_eq!(p.coefficients[pts.len()], GF16::ONE)`
   — the loop preserves the leading coefficient at position `offset`.

Since GF(2¹⁶) has characteristic 2, subtraction coincides with
addition:
  `(x − pts[i].x) = (x + pts[i].x) = (x ⊕ pts[i].x)`

The key postconditions of the function are:

• **Length**: `result.coefficients.length = pts.length + 1`.
• **Leading coefficient**: `result.coefficients[pts.length] = GF16::ONE`.

The leading-coefficient invariant is maintained by the loop (as proved
in `LagrangeInterpolatePrepareLoop0.loop_spec`): the loop body calls
`mult_xdiff_assign_trailing` which never modifies position `offset`
(the last position in the vector), so the `ONE` placed there before
the loop is still present after the loop, and the `debug_assert_eq!`
always passes.

The on-target Rust implementation may dispatch to hardware carry-less
multiplication instructions (`PCLMULQDQ` / `PMULL`) on x86/x86_64 and
aarch64 when the corresponding CPU feature is detected; the extracted
Lean version contains only the unaccelerated fallback.

**Source**: spqr/src/encoding/polynomial.rs (lines 144:4-163:5)
-/

namespace spqr.encoding.polynomial.Poly

/-- **Spec theorem for
`spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::lagrange_interpolate_prepare`**:

• The function always succeeds (no panic) for any point slice `pts`
  satisfying the precondition `pts.length + 1 ≤ Usize.max`, since
  all arithmetic operations stay within bounds, `Vec.resize` is
  total, and the loop driver
  `lagrange_interpolate_prepare_loop` is total on bounded indices.
• The resulting coefficient vector has length `pts.length + 1`:
    `result.coefficients.length = pts.length + 1`.
• The leading coefficient at position `pts.length` is `GF16::ONE`:
    `result.coefficients[pts.length]? = some GF16.ONE`.
  This is the `debug_assert_eq!` that the Rust source checks at
  line 161.

**Source**: spqr/src/encoding/polynomial.rs (lines 144:4-163:5)
-/
@[step]
theorem lagrange_interpolate_prepare_spec
    (pts : Slice encoding.polynomial.Pt)
    (h_len : pts.val.length + 1 ≤ Std.Usize.max) :
    encoding.polynomial.Poly.lagrange_interpolate_prepare pts
      ⦃ (result : encoding.polynomial.Poly) =>
      result.coefficients.val.length = pts.val.length + 1 ∧
      result.coefficients.val[pts.val.length]? =
        some encoding.gf.GF16.ONE ⦄ := by
  unfold encoding.polynomial.Poly.lagrange_interpolate_prepare
  step*
  all_goals simp_all [encoding.gf.GF16.Insts.CoreCloneClone.clone]

end spqr.encoding.polynomial.Poly
