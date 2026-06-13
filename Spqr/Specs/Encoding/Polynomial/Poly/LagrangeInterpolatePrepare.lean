/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
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
open Polynomial

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop


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
    (pts : Slice Pt)
    (offset : Usize)
    (iter : core.ops.range.Range Std.Usize)
    (p : Poly)
    (h_end_le_pts : iter.end ≤ pts.length)
    (h_end_le_offset : iter.end ≤ offset)
    (h_offset_lt_len : offset < p.coefficients.length) :
    body pts offset iter p ⦃ cf =>
      match cf with
      | ControlFlow.done r =>
          r = p ∧ ¬ (iter.start < iter.end)
      | ControlFlow.cont (iter1, p1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          p1.coefficients.length = p.coefficients.length ∧
          (∀ (j : Nat),
            offset - iter.start ≤ j + 1 →
            j + 1 < p.coefficients.length →
            ∀ (hj : j < p1.coefficients.val.length),
              (p1.coefficients.val.get ⟨j, hj⟩).toGF216 =
                (p.coefficients.val[j]!).toGF216 -
                (p.coefficients.val[j + 1]!).toGF216 *
                  (pts.val[iter.start.val]!).x.toGF216) ∧
          (∀ (j : Nat),
            ¬(offset - iter.start ≤ j + 1 ∧
              j + 1 < p.coefficients.length) →
            p1.coefficients.val[j]? = p.coefficients.val[j]?) ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]; simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    simp only [uncurry_apply_pair, not_lt, tsub_le_iff_right, List.get_eq_getElem,
      List.getElem!_eq_getElem?_getD, not_and]
    have h_i_lt_pts : iter.start < pts.length := by grind
    have h_i_lt_offset : iter.start < offset := by grind
    step*
    simp_all
    grind[degree]
  · obtain ⟨h_opt_eq, h_range_eq⟩ := h_none (by omega)
    rw [h_opt_eq]
    grind

end spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop

/-!
# Spec theorem for `lagrange_interpolate_prepare`: loop 0

Given a slice of points `pts` and an offset (= `pts.len()`), the function
`Poly::lagrange_interpolate_prepare` builds the polynomial
  `∏_{j=0}^{offset−1} (x − pts[j].x)`
by starting with the constant `1` at position `offset` in the coefficient vector and successively
multiplying the trailing sub-polynomial by `(x − pts[i].x)` for `i = 0, 1, …, offset − 1`.


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


**Source**: spqr/src/encoding/polynomial.rs (lines 155:8-159:9)
-/

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop

@[step]
theorem loop_spec
    (pts : Slice Pt)
    (offset : Usize)
    (iter : core.ops.range.Range Usize)
    (p : Poly)
    (h_end_le_pts : iter.end ≤ pts.length)
    (h_end_le_offset : iter.end ≤ offset)
    (h_len_eq : p.coefficients.val.length = offset + 1)
    (h_le : iter.start ≤ iter.end)
    (h_start_zero : iter.start.val = 0) :
    lagrange_interpolate_prepare_loop
      iter pts p offset ⦃ (result : Poly) =>
      result.coefficients.val.length = p.coefficients.val.length ∧
      result.coefficients.val[offset.val]? =
        p.coefficients.val[offset.val]? ∧
      (∀ (hoff : offset.val < result.coefficients.val.length),
        (result.coefficients.val[offset]).toGF216 =
          (p.coefficients.val[offset.val]!).toGF216) ∧
      (∀ (j : Nat),
        ¬(offset.val - iter.end ≤ j ∧ j < offset.val) →
        result.coefficients.val[j]? = p.coefficients.val[j]?) ∧
      -- Property 5: trailing polynomial identity
      (∀ (m : Nat),
        m ≤ iter.end - iter.start →
        ∀ (hpos : offset - (iter.end - iter.start) + m <
                    result.coefficients.length),
          GF16.toGF216
            (result.coefficients.val[offset.val - (iter.end.val - iter.start.val) + m]) =
            (expectedTrailingPoly p.coefficients pts offset
              iter.start (iter.end - iter.start)).coeff m) ⦄ := by
  unfold spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop
  apply loop.spec_decr_nat
    (measure := fun (st : core.ops.range.Range Std.Usize ×
                        encoding.polynomial.Poly) =>
                  st.1.end.val - st.1.start.val)
    (inv := fun (st : core.ops.range.Range Std.Usize ×
                     encoding.polynomial.Poly) =>
        st.1.end = iter.end ∧
        iter.start.val ≤ st.1.start.val ∧
        st.1.start.val ≤ iter.end.val ∧
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
    have h_end_le_pts' : iter'.end.val ≤ pts.val.length := by grind
    have h_end_le_offset' : iter'.end.val ≤ offset.val := by grind
    have h_offset_lt_len' : offset.val < p'.coefficients.val.length := by omega
    step*
    split
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_eq, h_nlt⟩ := r_post
      subst h_eq
      have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
      refine ⟨h_len', h_off', h_gf16_off', fun j hj => ?_, fun m hm hpos => ?_⟩
      · apply h_frame'
        intro ⟨h1, h2⟩
        exact hj ⟨by omega, h2⟩
      · have h_iters_eq : iter'.start.val - iter.start.val =
            iter.end.val - iter.start.val := by grind
        rw [h_iters_eq] at h_trail'
        exact h_trail' m hm hpos
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_lt, h_start1, h_end1, h_v1len, h_modified, h_frame⟩ := r_post
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_end1]; exact h_end'
      · omega
      · grind
      · grind
      · have h_off_frame := h_frame offset (by
          push Not; intro _; grind)
        rw [h_off_frame, h_off']
      · intro hoff
        have h_off_frame := h_frame offset.val (by
          push Not; intro _; grind)
        have hoff_p' : offset.val < p'.coefficients.val.length := by omega
        have h_get_eq := list_get_of_getElem?_eq h_off_frame hoff hoff_p'
        simp only [List.get_eq_getElem] at h_get_eq ⊢
        rw [h_get_eq]
        exact h_gf16_off' hoff_p'
      · intro j hj
        have h_body_fr : (Prod.snd r_post).coefficients.val[j]? =
            p'.coefficients.val[j]? := by
          apply h_frame
          intro ⟨ha, hb⟩
          exact hj ⟨by omega, by grind⟩
        have h_inv_fr : p'.coefficients.val[j]? =
            p.coefficients.val[j]? := by
          apply h_frame'
          intro ⟨ha, hb⟩
          exact hj ⟨by omega, hb⟩
        rw [h_body_fr, h_inv_fr]
      · intro m hm hpos
        set k := iter'.start.val - iter.start.val with hk_def
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
        set pos := offset.val - (k + 1) + m with hpos_def
        by_cases hm0 : m = 0
        · subst hm0
          rw [coeff_zero_C_add_X_sub_C_mul]
          have hmod := h_modified pos (by omega) (by grind) hpos'
          rw [hmod]
          have hidx : pos + 1 = offset.val - k := by grind
          rw [hidx]
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
          have hiter : iter'.start.val = iter.start.val + k := by omega
          rw [hiter]
          have : pos = offset.val - (k + 1) := by omega
          rw [this]
          grind
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          rw [coeff_succ_C_add_X_sub_C_mul]
          have hpos_simp : pos = offset.val - k + m' := by grind
          by_cases hm'k : m' + 1 ≤ k
          · have hj_len : offset.val - k + m' <
                (Prod.snd r_post).coefficients.val.length := by omega
            have hmod := h_modified (offset.val - k + m')
              (by omega) (by grind) hj_len
            have hget_conv : (Prod.snd r_post).coefficients.val.get ⟨pos, hpos'⟩ =
                (Prod.snd r_post).coefficients.val.get
                  ⟨offset.val - k + m', hj_len⟩ := by
              congr 1; exact Fin.ext (by omega)
            rw [hget_conv, hmod]
            have hlen_m' : offset.val - k + m' < p'.coefficients.val.length := by omega
            have htr_m' := h_trail' m' (by omega) hlen_m'
            have htr_m'_val : (p'.coefficients.val[offset.val - k + m']!).toGF216 =
                (expectedTrailingPoly p.coefficients.val pts.val
                  offset.val iter.start.val k).coeff m' := by
              rw [getElem!_pos p'.coefficients.val (offset.val - k + m') hlen_m']
              exact htr_m'
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
            have hiter : iter'.start.val = iter.start.val + k := by omega
            rw [hiter]
            grind
          · have hm'_eq : m' = k := by omega
            subst hm'_eq
            have hpos_off : pos = offset.val := by omega
            have hfr := h_frame offset.val (by push Not; intro _; grind)
            have hoff_len : offset.val <
                (Prod.snd r_post).coefficients.val.length := by omega
            have hget_conv : (Prod.snd r_post).coefficients.val.get ⟨pos, hpos'⟩ =
                (Prod.snd r_post).coefficients.val.get
                  ⟨offset.val, hoff_len⟩ := by
              congr 1; exact Fin.ext (by omega)
            rw [hget_conv]
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
            rw [expectedTrailingPoly_coeff_eq_zero_of_lt _ _ _ _ _ _ (by omega : k < k + 1)]
            ring
      · grind
  · refine ⟨rfl, le_refl _, h_le, rfl, rfl, ?_, ?_, ?_⟩
    · intro hoff
      congr 1
      exact (getElem!_pos p.coefficients.val offset.val hoff).symm
    · intro _ _; rfl
    · intro m hm hpos
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

**Source**: spqr/src/encoding/polynomial.rs (lines 144:4-163:5)
-/

namespace spqr.encoding.polynomial.Poly

open encoding.gf.GF16

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
    (h_len : pts.length + 1 ≤ Usize.max) :
    lagrange_interpolate_prepare pts
      ⦃ (result : Poly) =>
      result.degree = pts.length + 1 ∧
      result.coefficients.val[pts.length]! =
        some ONE ∧
      (∀ (hoff : pts.length < result.degree),
        (result.coefficients.val[pts.length]).toGF216 = 1) ∧
      (∀ (m : Nat),
        m ≤ pts.length →
        ∀ (hpos : m < result.degree),
          (result.coefficients.val[m]).toGF216 =
            (prodLinearFactors pts 0 pts.length).coeff m) ∧
      result.toGF216Poly = prodLinearFactors pts 0 pts.length ⦄ := by
  unfold lagrange_interpolate_prepare degree
  step*
  · simp_all [encoding.gf.GF16.Insts.CoreCloneClone.clone]
  · simp_all
  · simp_all
  · simp_all
  · simp_all only [Order.add_one_le_iff, Usize.ofNatCore_val_eq, List.resize_length,
    lt_add_iff_pos_right, zero_lt_one, getElem!_pos, alloc.vec.Vec.set_val_eq, List.length_set,
    getElem?_pos, List.getElem_set_self, Option.some.injEq, ONE_toGF216,
    imp_self, tsub_self, zero_le, true_and, not_lt, tsub_zero, zero_add, Order.lt_add_one_iff,
    forall_true_left, ONE_value,  forall_const]
    have h_bridge : expectedTrailingPoly
        ((p.coefficients.val.resize (pts.length + 1) ZERO).set pts.length ONE)
        pts pts.length 0 pts.length =
      prodLinearFactors pts 0 pts.length := by
      apply expectedTrailingPoly_eq_prodLinearFactors
      · have hlen : pts.length <
          (p.coefficients.val.resize (pts.length + 1) ZERO).length := by
          unfold List.resize
          simp
          grind
        grind [list_getElem_bang_set_self _ _ _ hlen, ONE_toGF216]
      · intro j hj
        have hj_lt : j < (p.coefficients.val.resize (pts.length + 1) ZERO).length := by
          unfold List.resize
          grind
        have h_p_coeff_zero : ∀ k (hk : k < p.coefficients.length),
            (p.coefficients.val[k]!).toGF216 = 0 := by
          intro k hk
          have h0 : (p.toGF216Poly).coeff k = 0 := by grind
          simp only [Poly.toGF216Poly, listToGF216Poly_coeff, hk, ↓reduceDIte] at h0
          grind
        unfold List.resize at hj_lt ⊢
        simp only [Nat.zero_le, ge_iff_le, ↓reduceIte] at hj_lt ⊢
        by_cases hk : j < p.coefficients.length
        · grind
        · push Not at hk
          have htake_len_le : (p.coefficients.val.take (pts.length + 1)).length ≤ j := by
            rw [List.length_take]; omega
          have hrepl_bnd : j - (p.coefficients.val.take (pts.length + 1)).length <
              pts.length + 1 - p.coefficients.length := by
            rw [List.length_take]
            grind
          have hj_ne : Nat.not_eq pts.length j := by
            simp [Nat.not_eq]
            grind
          simp_all
      · exact le_refl _
      · exact le_refl _
    constructor
    · intro m hm
      rw [h_bridge]
    · change listToGF216Poly p1.coefficients =
        prodLinearFactors pts 0 pts.length
      apply listToGF216Poly_eq_of_coeffs
      · intro m hm
        grind
      · intro m hm
        exact prodLinearFactors_coeff_eq_zero_high _ _ _ _ (by grind)

end spqr.encoding.polynomial.Poly
