/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeSum
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_1
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_3
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_5
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_30
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_34
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_36
/-!
# Spec theorem for `Poly::from_complete_points`: loop body 0
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly core.iter.adapters.enumerate core.slice.iter
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop


namespace spqr.encoding.polynomial.Poly.from_complete_points_loop

/-! ## Helper: checked addition for usize -/

private lemma usize_checked_add_one_val (x : Usize)
    (h : x.val + 1 ≤ Usize.max) :
    ∃ (y : Usize), (x + 1#usize : Result Usize) = ok y ∧ y.val = x.val + 1 := by
  have h_add : x.val + (1#usize : Usize).val ≤ Usize.max := by scalar_tac
  have h_spec := Usize.add_spec h_add
  revert h_spec
  generalize (x + 1#usize : Result Usize) = res
  intro h_spec
  match res with
  | .ok z => exact ⟨z, rfl, by simp_all [WP.spec_ok]⟩
  | .fail e => simp_all
  | .div => simp_all

/-! ## Helper lemma: Enumerate<SliceIter<Pt>>::next always succeeds -/

private lemma EnumerateSliceIter_next_Pt_post
    (iter : Enumerate (Iter Pt))
    (h_bound : iter.iter.i < iter.iter.slice.val.length → iter.count.val + 1 ≤ Usize.max) :
    ∃ (opt : Option (Usize × Pt))
      (iter' : Enumerate (Iter Pt)),
      IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Pt) iter =
          ok (opt, iter') := by
  simp only [IteratorEnumerate.next,
    IteratorSliceIter.next]
  split
  · have h_add_bound : iter.count.val + 1 ≤ Usize.max := h_bound (by scalar_tac)
    obtain ⟨count', h_add_eq, _⟩ := usize_checked_add_one_val iter.count h_add_bound
    rw [h_add_eq]
    exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-! ## Helper: extract facts when Enumerate.next returns some -/

private lemma EnumerateSliceIter_next_Pt_some
    (iter : Enumerate (Iter Pt))
    (h_lt : iter.iter.i < iter.iter.slice.val.length)
    (h_bound : iter.count.val + 1 ≤ Usize.max) :
    ∃ (iter1 : Enumerate (Iter Pt)),
      IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Pt) iter =
          ok (some (iter.count, iter.iter.slice.val[iter.iter.i]), iter1) ∧
      iter1.iter.i = iter.iter.i + 1 ∧
      iter1.iter.slice = iter.iter.slice ∧
      iter1.count.val = iter.count.val + 1 := by
  simp only [
    IteratorEnumerate.next,
    IteratorSliceIter.next]
  have h_lt' : iter.iter.i < (↑iter.iter.slice.len : Nat) := by scalar_tac
  rw [dif_pos h_lt']
  obtain ⟨count', h_add_eq, h_add_val⟩ := usize_checked_add_one_val iter.count h_bound
  rw [h_add_eq]
  exact ⟨_, rfl, rfl, rfl, h_add_val⟩

/-! ## Helper: extract facts when Enumerate.next returns none -/

private lemma EnumerateSliceIter_next_Pt_none
    (iter : Enumerate (Iter Pt))
    (iter' : Enumerate (Iter Pt))
    (hnext : IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Pt) iter =
          ok (none, iter')) :
    ¬ (iter.iter.i < iter.iter.slice.val.length) := by
  simp only [IteratorEnumerate.next,
    IteratorSliceIter.next] at hnext
  split at hnext
  case isTrue h_lt =>
    exfalso
    revert hnext
    generalize (iter.count + 1#usize : Result Usize) = add_res
    cases add_res <;> simp
  case isFalse h_neg => exact h_neg

/-! ## Helper: UScalar.cast .U16 preserves value when in range -/

private lemma usize_cast_u16_val (x : Usize) (h : x.val ≤ UScalar.max .U16) :
    (UScalar.cast UScalarTy.U16 x).val = x.val :=
  UScalar.cast_inBounds_spec UScalarTy.U16 x h

/-! ## Common postcondition abbreviation -/

/-- The postcondition shared by all body_spec helper lemmas. Using `abbrev` ensures it is
    definitionally transparent and `step*` can see through it.

    The `Ok` branch states that `p` is the Lagrange interpolation sum using the
    scaled Lagrange basis polynomials `scaledLagrangeBasis (Slice.len pts) j`
    for the complete-points array of size `pts.val.length`. -/
private abbrev bodyPost
    (pts : Slice Pt) (iter : Enumerate (Iter Pt)) :
    ControlFlow (Enumerate (Iter Pt)) (core.result.Result Poly Unit) → Prop :=
  fun cf =>
    match cf with
    | ControlFlow.done (core.result.Result.Ok p) =>
        ¬ (iter.iter.i < pts.val.length) ∧
        p.toGF216Poly = ∑ j ∈ Finset.range pts.val.length,
          C ((pts.val[j]!).y.toGF216) * scaledLagrangeBasis (Slice.len pts) j
    | ControlFlow.done (core.result.Result.Err ()) =>
        ∃ (h_i : iter.iter.i < pts.val.length),
          (pts.val.get ⟨iter.iter.i, h_i⟩).x.value.val ≠
            iter.count.val
    | ControlFlow.cont iter' =>
        ∃ (h_i : iter.iter.i < pts.val.length),
          (pts.val.get ⟨iter.iter.i, h_i⟩).x.value.val =
            iter.count.val ∧
          iter'.iter.i = iter.iter.i + 1 ∧
          iter'.iter.slice = pts ∧
          iter'.count.val = iter.count.val + 1

/-! ## Helper: contradict `some` when iterator is out of bounds -/

private lemma absurd_some_out_of_bounds
    (iter : Enumerate (Iter Pt))
    (idx : Usize) (pt : Pt) (iter1 : Enumerate (Iter Pt))
    (hnext : IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Pt) iter =
          ok (some (idx, pt), iter1))
    (h_out : ¬(iter.iter.i < iter.iter.slice.val.length)) :
    False := by
  simp only [IteratorEnumerate.next,
    IteratorSliceIter.next] at hnext
  split at hnext
  case isTrue h_lt => exact absurd h_lt h_out
  case isFalse => simp at hnext

/-! ## Spec helper: the `some` (validation) branch -/

private theorem body_spec_some_case
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_count : iter.count.val ≤ UScalar.max .U16)
    (h_slice_eq : iter.iter.slice = pts)
    (h_in_bounds : iter.iter.i < iter.iter.slice.val.length) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  have h_count_bound : iter.count.val + 1 ≤ Usize.max := by scalar_tac
  obtain ⟨iter1, hnext, h_iter1_i, h_iter1_slice, h_iter1_count⟩ :=
    EnumerateSliceIter_next_Pt_some iter h_in_bounds h_count_bound
  rw [hnext]
  simp only [bind_tc_ok]
  have h_lt_pts : iter.iter.i < pts.val.length := by
    rw [← h_slice_eq]; exact h_in_bounds
  have h_cast_val := usize_cast_u16_val iter.count h_count
  step*
  · simp_all
    grind
  · grind

/-! ## Spec helpers: the `none` (computation) branch by size -/


private theorem body_spec_none_0
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_slice_eq : iter.iter.slice = pts)
    (h_out_of_bounds : ¬(iter.iter.i < iter.iter.slice.val.length))
    (h0 : pts.val.length = 0) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext⟩ := EnumerateSliceIter_next_Pt_post iter
    (fun h_lt => absurd h_lt h_out_of_bounds)
  rw [hnext]
  simp only [bind_tc_ok]
  cases opt with
  | some p =>
    obtain ⟨idx, pt⟩ := p
    exact (absurd_some_out_of_bounds iter idx pt iter1 hnext h_out_of_bounds).elim
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      have := EnumerateSliceIter_next_Pt_none iter iter1 hnext
      rw [h_slice_eq] at this; exact this
    have h_len_0 : Slice.len pts = 0#usize := by
      ext
      simp [Slice.len]
      simp [h0]
      simp [Usize.ofNatCore]
    step as ⟨ s, hs⟩
    have : s = 0#uscalar := by
      simp only [hs, h_len_0]
      simp[UScalar.cast]
    simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]
    step
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD]
    constructor
    · grind
    · simp_all


/-- `scaledLagrangeBasis 1#usize 0 = 1`: for the single-point case (`N = 1`),
the only scaled Lagrange basis polynomial is the constant `1`. Both
`condProdLinearFactors` and `lagrangeDenomProd` skip index 0 (self-match)
and immediately hit the empty-product base case. -/
private lemma scaledLagrangeBasis_one_zero :
    scaledLagrangeBasis (1#usize) 0 = 1 := by
  simp only [global_simps]
  rw [condProdLinearFactors_skip _ _ 0 (by simp ),
      condProdLinearFactors_ge _ _ 1 (by simp ),
      lagrangeDenomProd_skip _ _ 0 (by simp ),
      lagrangeDenomProd_eq_one_of_le _ _ 1 (by simp )] <;>
  simp_all [ GF16.toGF216, one_pow, mul_one, map_one,
            List.length_finRange, List.get_eq_getElem, Nat.toGF216,
            spqr.math.gf.natToBinaryPoly_one]

private theorem body_spec_none_1
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_slice_eq : iter.iter.slice = pts)
    (h_out_of_bounds : ¬(iter.iter.i < iter.iter.slice.val.length))
    (h1 : pts.val.length = 1) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext⟩ := EnumerateSliceIter_next_Pt_post iter
    (fun h_lt => absurd h_lt h_out_of_bounds)
  rw [hnext]; simp only [bind_tc_ok]
  cases opt with
  | some p =>
    obtain ⟨idx, pt⟩ := p
    exact (absurd_some_out_of_bounds iter idx pt iter1 hnext h_out_of_bounds).elim
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      have := EnumerateSliceIter_next_Pt_none iter iter1 hnext
      rw [h_slice_eq] at this; exact this
    have h_len_1 : Slice.len pts = 1#usize := by
      simp [Slice.len, h1, Usize.ofNatCore]
    step as ⟨ s, hs⟩
    have : s = 1#uscalar := by
      simp [hs, h_len_1]
      simp [UScalar.cast]
      grind
    simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]
    step
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD, ne_eq,List.get_eq_getElem]
    step
    step
    · have : (polys.deref).val.length = (polys).val.length:= by
        simp [alloc.vec.Vec.deref]
      grind
    · intros i hi
      have : (polys.deref.val[i]!.coefficients).val.length =
        (polys.val[i]!.coefficients).val.length := by
        simp [alloc.vec.Vec.deref]
      grind [degree]
    · constructor
      · grind
      · rw [h_len_1]
        simp only [alloc.vec.Vec.deref] at *
        simp only [h1] at *
        rw [p_post]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_range] at hx
        simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
        congr 1
        have hx_lt_polys : x < (↑polys : List Poly).length := by grind
        simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
        have hx0 : x = 0 := by omega
        subst hx0
        apply (polys_post2 0 (by omega) (by omega) (by omega)).2.trans
        simp_all[scaledLagrangeBasis_one_zero.symm]

private theorem body_spec_none_3
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_slice_eq : iter.iter.slice = pts)
    (h_out_of_bounds : ¬(iter.iter.i < iter.iter.slice.val.length))
    (h3 : pts.val.length = 3) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext⟩ := EnumerateSliceIter_next_Pt_post iter
    (fun h_lt => absurd h_lt h_out_of_bounds)
  rw [hnext]; simp only [bind_tc_ok]
  cases opt with
  | some p =>
    obtain ⟨idx, pt⟩ := p
    exact (absurd_some_out_of_bounds iter idx pt iter1 hnext h_out_of_bounds).elim
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      have := EnumerateSliceIter_next_Pt_none iter iter1 hnext
      rw [h_slice_eq] at this; exact this
    have h_len_1 : Slice.len pts = 3#usize := by
      simp [Slice.len, h3, Usize.ofNatCore]
    step as ⟨ s, hs⟩
    have : s = 3#uscalar := by
      simp [hs, h_len_1]
      simp [UScalar.cast]
      grind
    simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]
    step
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD, ne_eq, List.get_eq_getElem]
    step
    step
    · have : (polys.deref).val.length = (polys).val.length:= by
        simp [alloc.vec.Vec.deref]
      grind
    · intros i hi
      have : (polys.deref.val[i]!.coefficients).val.length =
        (polys.val[i]!.coefficients).val.length := by
        simp [alloc.vec.Vec.deref]
      grind [degree]
    · constructor
      · grind
      · rw [h_len_1]
        simp only [alloc.vec.Vec.deref] at *
        simp only [h3] at *
        rw [p_post]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_range] at hx
        simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
        congr 1
        have hx_lt_polys : x < (↑polys : List Poly).length := by grind
        simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
        have := (polys_post2 x (by omega) (by omega) (by grind)).2
        have := a_post x (by grind)
        simp_all

private theorem body_spec_none_5
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_slice_eq : iter.iter.slice = pts)
    (h_out_of_bounds : ¬(iter.iter.i < iter.iter.slice.val.length))
    (h5 : pts.val.length = 5) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext⟩ := EnumerateSliceIter_next_Pt_post iter
    (fun h_lt => absurd h_lt h_out_of_bounds)
  rw [hnext]; simp only [bind_tc_ok]
  cases opt with
  | some p =>
    obtain ⟨idx, pt⟩ := p
    exact (absurd_some_out_of_bounds iter idx pt iter1 hnext h_out_of_bounds).elim
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      have := EnumerateSliceIter_next_Pt_none iter iter1 hnext
      rw [h_slice_eq] at this; exact this
    have h_len_1 : Slice.len pts = 5#usize := by
      simp [Slice.len, h5, Usize.ofNatCore]
    step as ⟨ s, hs⟩
    have : s = 5#uscalar := by
      simp [hs, h_len_1]
      simp [UScalar.cast]
      grind
    simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]
    step
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD, ne_eq, List.get_eq_getElem]
    step
    step
    · have : (polys.deref).val.length = (polys).val.length:= by
        simp [alloc.vec.Vec.deref]
      grind
    · intros i hi
      have : (polys.deref.val[i]!.coefficients).val.length =
        (polys.val[i]!.coefficients).val.length := by
        simp [alloc.vec.Vec.deref]
      grind [degree]
    · constructor
      · grind
      · rw [h_len_1]
        simp only [alloc.vec.Vec.deref] at *
        simp only [h5] at *
        rw [p_post]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_range] at hx
        simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
        congr 1
        have hx_lt_polys : x < (↑polys : List Poly).length := by grind
        simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
        have := (polys_post2 x (by omega) (by omega) (by grind)).2
        have := a_post x (by grind)
        simp_all

private theorem body_spec_none_30
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_slice_eq : iter.iter.slice = pts)
    (h_out_of_bounds : ¬(iter.iter.i < iter.iter.slice.val.length))
    (h30 : pts.val.length = 30) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext⟩ := EnumerateSliceIter_next_Pt_post iter
    (fun h_lt => absurd h_lt h_out_of_bounds)
  rw [hnext]; simp only [bind_tc_ok]
  cases opt with
  | some p =>
    obtain ⟨idx, pt⟩ := p
    exact (absurd_some_out_of_bounds iter idx pt iter1 hnext h_out_of_bounds).elim
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      have := EnumerateSliceIter_next_Pt_none iter iter1 hnext
      rw [h_slice_eq] at this; exact this
    have h_len_1 : Slice.len pts = 30#usize := by
      simp [Slice.len, h30, Usize.ofNatCore]
    step as ⟨ s, hs⟩
    have : s = 30#uscalar := by
      simp [hs, h_len_1]
      simp [UScalar.cast]
      grind
    simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]
    step
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD, ne_eq, List.get_eq_getElem]
    step
    step
    · have : (polys.deref).val.length = (polys).val.length:= by
        simp [alloc.vec.Vec.deref]
      grind
    · intros i hi
      have : (polys.deref.val[i]!.coefficients).val.length =
        (polys.val[i]!.coefficients).val.length := by
        simp [alloc.vec.Vec.deref]
      grind [degree]
    · constructor
      · grind
      · rw [h_len_1]
        simp only [alloc.vec.Vec.deref] at *
        simp only [h30] at *
        rw [p_post]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_range] at hx
        simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
        congr 1
        have hx_lt_polys : x < (↑polys : List Poly).length := by grind
        simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
        have := (polys_post2 x (by omega) (by omega) (by grind)).2
        have := a_post x (by grind)
        simp_all

private theorem body_spec_none_34
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_slice_eq : iter.iter.slice = pts)
    (h_out_of_bounds : ¬(iter.iter.i < iter.iter.slice.val.length))
    (h34 : pts.val.length = 34) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext⟩ := EnumerateSliceIter_next_Pt_post iter
    (fun h_lt => absurd h_lt h_out_of_bounds)
  rw [hnext]; simp only [bind_tc_ok]
  cases opt with
  | some p =>
    obtain ⟨idx, pt⟩ := p
    exact (absurd_some_out_of_bounds iter idx pt iter1 hnext h_out_of_bounds).elim
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      have := EnumerateSliceIter_next_Pt_none iter iter1 hnext
      rw [h_slice_eq] at this; exact this
    have h_len_1 : Slice.len pts = 34#usize := by
      simp [Slice.len, h34, Usize.ofNatCore]
    step as ⟨ s, hs⟩
    have : s = 34#uscalar := by
      simp [hs, h_len_1]
      simp [UScalar.cast]
      grind
    simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]
    step
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD,  ne_eq, List.get_eq_getElem]
    step
    step
    · have : (polys.deref).val.length = (polys).val.length:= by
        simp [alloc.vec.Vec.deref]
      grind
    · intros i hi
      have : (polys.deref.val[i]!.coefficients).val.length =
        (polys.val[i]!.coefficients).val.length := by
        simp [alloc.vec.Vec.deref]
      grind [degree]
    · constructor
      · grind
      · rw [h_len_1]
        simp only [alloc.vec.Vec.deref] at *
        simp only [h34] at *
        rw [p_post]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_range] at hx
        simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
        congr 1
        have hx_lt_polys : x < (↑polys : List Poly).length := by grind
        simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
        have := (polys_post2 x (by omega) (by omega) (by grind)).2
        have := a_post x (by grind)
        simp_all

private theorem body_spec_none_36
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_slice_eq : iter.iter.slice = pts)
    (h_out_of_bounds : ¬(iter.iter.i < iter.iter.slice.val.length))
    (h36 : pts.val.length = 36) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext⟩ := EnumerateSliceIter_next_Pt_post iter
    (fun h_lt => absurd h_lt h_out_of_bounds)
  rw [hnext]; simp only [bind_tc_ok]
  cases opt with
  | some p =>
    obtain ⟨idx, pt⟩ := p
    exact (absurd_some_out_of_bounds iter idx pt iter1 hnext h_out_of_bounds).elim
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      have := EnumerateSliceIter_next_Pt_none iter iter1 hnext
      rw [h_slice_eq] at this; exact this
    have h_len_1 : Slice.len pts = 36#usize := by
      simp [Slice.len, h36, Usize.ofNatCore]
    step as ⟨ s, hs⟩
    have : s = 36#uscalar := by
      simp [hs, h_len_1]
      simp [UScalar.cast]
      grind
    simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]
    step
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD, ne_eq, List.get_eq_getElem]
    step
    step
    · have : (polys.deref).val.length = (polys).val.length:= by
        simp [alloc.vec.Vec.deref]
      grind
    · intros i hi
      have : (polys.deref.val[i]!.coefficients).val.length =
        (polys.val[i]!.coefficients).val.length := by
        simp [alloc.vec.Vec.deref]
      grind [degree]
    · constructor
      · grind
      · rw [h_len_1]
        simp only [alloc.vec.Vec.deref] at *
        simp only [h36] at *
        rw [p_post]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_range] at hx
        simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
        congr 1
        have hx_lt_polys : x < (↑polys : List Poly).length := by grind
        simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
        have := (polys_post2 x (by omega) (by omega) (by grind)).2
        have := a_post x (by grind)
        simp_all



/-! ## Spec theorem: in-bounds body (no size restriction) -/

/--
Body spec when the iterator is in-bounds. Does NOT require admissible size.
Used for the non-admissible-size theorem where the loop invariant guarantees
we never reach the exhausted-iterator (none) branch.
-/
theorem body_spec_inbounds
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_count : iter.count.val ≤ UScalar.max .U16)
    (h_slice_eq : iter.iter.slice = pts)
    (h_in_bounds : iter.iter.i < pts.val.length) :
    body pts iter ⦃ cf =>
      match cf with
      | ControlFlow.done (core.result.Result.Err ()) =>
          (pts.val.get ⟨iter.iter.i, h_in_bounds⟩).x.value.val ≠
            iter.count.val
      | ControlFlow.cont iter' =>
          (pts.val.get ⟨iter.iter.i, h_in_bounds⟩).x.value.val =
            iter.count.val ∧
          iter'.iter.i = iter.iter.i + 1 ∧
          iter'.iter.slice = pts ∧
          iter'.count.val = iter.count.val + 1
      | ControlFlow.done (core.result.Result.Ok _) =>
          False
    ⦄ := by
  have h_in_bounds' : iter.iter.i < iter.iter.slice.val.length := by
    rw [h_slice_eq]; exact h_in_bounds
  unfold body
  have h_count_bound : iter.count.val + 1 ≤ Usize.max := by scalar_tac
  obtain ⟨iter1, hnext, h_iter1_i, h_iter1_slice, h_iter1_count⟩ :=
    EnumerateSliceIter_next_Pt_some iter h_in_bounds' h_count_bound
  rw [hnext]
  simp only [bind_tc_ok]
  have h_lt_pts : iter.iter.i < pts.val.length := h_in_bounds
  have h_cast_val := usize_cast_u16_val iter.count h_count
  step*
  · simp_all only [UScalar.max_UScalarTy_U16_eq, Order.add_one_le_iff, bne_iff_ne, ne_eq,
    UScalar.neq_to_neq_val, List.get_eq_getElem, not_false_eq_true]
  grind

/-! ## Spec theorem for the loop body -/

/-- **Spec theorem for `encoding.polynomial.Poly.from_complete_points_loop.body`**:

The postcondition uses `scaledLagrangeBasis (Slice.len pts) j` — the `j`-th scaled
Lagrange basis polynomial for the complete-points array of size `pts.val.length` — to
express the Lagrange sum directly, without existentially quantifying the intermediate
`polys` slice.

• **`Ok p`** (iterator exhausted, computation done):
    `p.toGF216Poly = ∑ j ∈ Finset.range pts.val.length,
       C ((pts.val[j]!).y.toGF216) * scaledLagrangeBasis (Slice.len pts) j`

• **`Err ()`** (validation failure):
    `(pts.val[iter.iter.i]).x.value.val ≠ iter.count.val`

• **`cont iter'`** (validation passes, continue):
    `(pts.val[iter.iter.i]).x.value.val = iter.count.val` and the iterator advances. -/
@[step]
theorem body_spec
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_count : iter.count.val ≤ UScalar.max .U16)
    (h_slice_eq : iter.iter.slice = pts)
    (h_len_ok : pts.val.length = 0 ∨ pts.val.length = 1 ∨ pts.val.length = 3 ∨
                pts.val.length = 5 ∨ pts.val.length = 30 ∨ pts.val.length = 34 ∨
                pts.val.length = 36) :
    body pts iter ⦃ cf =>
      match cf with
      | ControlFlow.done (core.result.Result.Ok p) =>
          ¬ (iter.iter.i < pts.val.length) ∧
          p.toGF216Poly = ∑ j ∈ Finset.range pts.val.length,
            C ((pts.val[j]!).y.toGF216) * scaledLagrangeBasis (Slice.len pts) j
      | ControlFlow.done (core.result.Result.Err ()) =>
          ∃ (h_i : iter.iter.i < pts.val.length),
            (pts.val.get ⟨iter.iter.i, h_i⟩).x.value.val ≠
              iter.count.val
      | ControlFlow.cont iter' =>
          ∃ (h_i : iter.iter.i < pts.val.length),
            (pts.val.get ⟨iter.iter.i, h_i⟩).x.value.val =
              iter.count.val ∧
            iter'.iter.i = iter.iter.i + 1 ∧
            iter'.iter.slice = pts ∧
            iter'.count.val = iter.count.val + 1
    ⦄ := by
  by_cases h_in : iter.iter.i < iter.iter.slice.val.length
  · exact body_spec_some_case pts iter h_count h_slice_eq h_in
  · rcases h_len_ok with h | h | h | h | h | h | h
    · exact body_spec_none_0 pts iter h_slice_eq h_in h
    · exact body_spec_none_1 pts iter h_slice_eq h_in h
    · exact body_spec_none_3 pts iter h_slice_eq h_in h
    · exact body_spec_none_5 pts iter h_slice_eq h_in h
    · exact body_spec_none_30 pts iter h_slice_eq h_in h
    · exact body_spec_none_34 pts iter h_slice_eq h_in h
    · exact body_spec_none_36 pts iter h_slice_eq h_in h


end spqr.encoding.polynomial.Poly.from_complete_points_loop
