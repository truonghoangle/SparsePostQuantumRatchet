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

/-! ## Helper: the nonzero-size none case -/

private lemma none_nonzero_postcondition
    (pts : Slice Pt)
    (N : Usize)
    (h_N_eq : N.val = pts.val.length)
    (h_N_pos : pts.val.length ≠ 0)
    (polys : Slice Poly)
    (p : Poly)
    (h_polys_len : polys.val.length = N.val)
    (ones1 : Array Pt N)
    (h_ones1_pts : ∀ (j : Nat), j < N.val →
      (ones1[j]!).x.value.val = j ∧
      (ones1[j]!).y = GF16.ONE)
    (h_polys_lagrange : ∀ (j : Nat), j < N.val →
      ∀ (hj : j < polys.length)
        (hjo : j < ones1.length),
        (polys.val[j]).toGF216Poly =
          C ((ones1.val[j]!).y.toGF216 *
              (lagrangeDenomProd (ones1[j]!).x
                (ones1.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
            condProdLinearFactors (ones1[j]!).x
              (ones1.val.take N.val) 0)
    (h_sum : p.toGF216Poly = ∑ j ∈ Finset.range pts.val.length,
      C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly) :
    ∃ (polys' : Slice Poly),
      pts.length ≤ polys'.length ∧
      (p.toGF216Poly = ∑ j ∈ Finset.range pts.val.length,
        C ((pts.val[j]!).y.toGF216) * (polys'.val[j]!).toGF216Poly) ∧
      (pts.val.length = 0 →
        polys'.val.length = 0 ∧ p.toGF216Poly = 0) ∧
      (pts.val.length ≠ 0 →
        polys'.val.length = pts.val.length ∧
        ∃ (N' : Usize) (ones1' : Array Pt N'),
          N'.val = pts.val.length ∧
          (∀ (j : Nat), j < N'.val →
            (ones1'[j]!).x.value.val = j ∧
            (ones1'[j]!).y = GF16.ONE) ∧
          (∀ (j : Nat), j < N'.val →
            ∀ (hj : j < polys'.val.length)
              (hjo : j < ones1'.length),
              (polys'.val.get ⟨j, hj⟩).toGF216Poly =
                C ((ones1'.val[j]!).y.toGF216 *
                    (lagrangeDenomProd (ones1'[j]!).x
                      (ones1'.val.take N'.val) 0) ^ (2 ^ 16 - 2)) *
                  condProdLinearFactors (ones1'[j]!).x
                    (ones1'.val.take N'.val) 0)) :=
  ⟨polys,
    by grind,
    h_sum,
    fun h => absurd h h_N_pos,
    fun _ => ⟨by omega, N, ones1, h_N_eq, h_ones1_pts, h_polys_lagrange⟩⟩

/-! ## Common postcondition abbreviation -/

/-- The postcondition shared by all body_spec helper lemmas. Using `abbrev` ensures it is
    definitionally transparent and `step*` can see through it. -/
private abbrev bodyPost
    (pts : Slice Pt) (iter : Enumerate (Iter Pt)) :
    ControlFlow (Enumerate (Iter Pt)) (core.result.Result Poly Unit) → Prop :=
  fun cf =>
    match cf with
    | ControlFlow.done (core.result.Result.Ok p) =>
        ¬ (iter.iter.i < pts.val.length) ∧
        ∃ (polys : Slice Poly),
          pts.val.length ≤ polys.val.length ∧
          (p.toGF216Poly = ∑ j ∈ Finset.range pts.val.length,
            C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly) ∧
          (pts.length = 0 →
            polys.length = 0 ∧ p.toGF216Poly = 0) ∧
          (pts.length ≠ 0 →
            polys.length = pts.length ∧
            ∃ (N : Usize) (ones1 : Array Pt N),
              N = pts.length ∧
              (∀ (j : Nat), j < N →
                (ones1[j]!).x.value.val = j ∧
                (ones1[j]!).y = GF16.ONE) ∧
              (∀ (j : Nat), j < N.val →
                ∀ (hj : j < polys.length)
                  (hjo : j < ones1.length),
                  (polys.val[j]).toGF216Poly =
                    C ((ones1.val[j]!).y.toGF216 *
                        (lagrangeDenomProd (ones1[j]!).x
                          (ones1.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
                      condProdLinearFactors (ones1[j]!).x
                        (ones1.val.take N.val) 0))
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
    simp only [not_lt, List.getElem!_eq_getElem?_getD, List.length_eq_zero_iff, ne_eq,
      List.Vector.length_val,  Nat.reducePow, Nat.reduceSub, map_mul, map_pow,
      exists_and_left]
    constructor
    · grind
    · use (alloc.vec.Vec.new Poly)
      constructor
      · simp
        grind
      · simp_all




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
    rename_i ones1
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD, List.length_eq_zero_iff, ne_eq,
      List.Vector.length_val, List.get_eq_getElem, Nat.reducePow, Nat.reduceSub, map_mul, map_pow,
      exists_and_left]
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
      · use (polys.deref)
        constructor
        · have : (polys.deref).val.length = (polys).val.length:= by
            simp [alloc.vec.Vec.deref]
          grind
        · simp_all only [Order.lt_one_iff, not_false_eq_true, BitVec.ofNat_eq_ofNat,
          UScalarTy.U64_numBits_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
           forall_true_left, Nat.reducePow, Nat.reduceSub,
          Finset.range_one,  Finset.sum_singleton,
          getElem?_pos, Option.getD_some, mul_eq_zero, map_eq_zero]
          constructor
          · grind
          · constructor
            · have : (polys.deref).val.length = (polys).val.length:= by
                simp [alloc.vec.Vec.deref]
              grind
            · intro h
              constructor
              · have : (polys.deref).val.length = (polys).val.length:= by
                  simp [alloc.vec.Vec.deref]
                grind
              · use 1#usize
                simp only [UScalar.ofNatCore_val_eq, Order.lt_one_iff, true_and]
                use a
                have : (polys.deref).val = (polys).val:= by
                  simp [alloc.vec.Vec.deref]
                simp_all












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
    rename_i ones1
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD, List.length_eq_zero_iff, ne_eq,
      List.Vector.length_val, List.get_eq_getElem, Nat.reducePow, Nat.reduceSub, map_mul, map_pow,
      exists_and_left]
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
      · use (polys.deref)
        constructor
        · have : (polys.deref).val.length = (polys).val.length:= by
            simp [alloc.vec.Vec.deref]
          grind
        · simp_all only [not_false_eq_true, BitVec.ofNat_eq_ofNat,
          UScalarTy.U64_numBits_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
           forall_true_left, Nat.reducePow, Nat.reduceSub]
          constructor
          · grind
          · constructor
            · have : (polys.deref).val.length = (polys).val.length:= by
                simp [alloc.vec.Vec.deref]
              grind
            · intro h
              constructor
              · have : (polys.deref).val.length = (polys).val.length:= by
                  simp [alloc.vec.Vec.deref]
                grind
              · use 3#usize
                simp only [UScalar.ofNatCore_val_eq, true_and]
                use a
                have : (polys.deref).val = (polys).val:= by
                  simp [alloc.vec.Vec.deref]
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
    rename_i ones1
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD, List.length_eq_zero_iff, ne_eq,
      List.Vector.length_val, List.get_eq_getElem, Nat.reducePow, Nat.reduceSub, map_mul, map_pow,
      exists_and_left]
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
      · use (polys.deref)
        constructor
        · have : (polys.deref).val.length = (polys).val.length:= by
            simp [alloc.vec.Vec.deref]
          grind
        · simp_all only [not_false_eq_true, BitVec.ofNat_eq_ofNat,
          UScalarTy.U64_numBits_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
          forall_true_left, Nat.reducePow, Nat.reduceSub]
          constructor
          · grind
          · constructor
            · have : (polys.deref).val.length = (polys).val.length:= by
                simp [alloc.vec.Vec.deref]
              grind
            · intro h
              constructor
              · have : (polys.deref).val.length = (polys).val.length:= by
                  simp [alloc.vec.Vec.deref]
                grind
              · use 5#usize
                simp only [UScalar.ofNatCore_val_eq, true_and]
                use a
                have : (polys.deref).val = (polys).val:= by
                  simp [alloc.vec.Vec.deref]
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
    rename_i ones1
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD, List.length_eq_zero_iff, ne_eq,
      List.Vector.length_val, List.get_eq_getElem, Nat.reducePow, Nat.reduceSub, map_mul, map_pow,
      exists_and_left]
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
      · use (polys.deref)
        constructor
        · have : (polys.deref).val.length = (polys).val.length:= by
            simp [alloc.vec.Vec.deref]
          grind
        · simp_all only [ not_false_eq_true, BitVec.ofNat_eq_ofNat,
          UScalarTy.U64_numBits_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
          forall_true_left,  Nat.reducePow, Nat.reduceSub]
          constructor
          · grind
          · constructor
            · have : (polys.deref).val.length = (polys).val.length:= by
                simp [alloc.vec.Vec.deref]
              grind
            · intro h
              constructor
              · have : (polys.deref).val.length = (polys).val.length:= by
                  simp [alloc.vec.Vec.deref]
                grind
              · use 30#usize
                simp only [UScalar.ofNatCore_val_eq, true_and]
                use a
                have : (polys.deref).val = (polys).val:= by
                  simp [alloc.vec.Vec.deref]
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
    rename_i ones1
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD, List.length_eq_zero_iff, ne_eq,
      List.Vector.length_val, List.get_eq_getElem, Nat.reducePow, Nat.reduceSub, map_mul, map_pow,
      exists_and_left]
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
      · use (polys.deref)
        constructor
        · have : (polys.deref).val.length = (polys).val.length:= by
            simp [alloc.vec.Vec.deref]
          grind
        · simp_all only [ not_false_eq_true, BitVec.ofNat_eq_ofNat,
          UScalarTy.U64_numBits_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
          forall_true_left, Nat.reducePow, Nat.reduceSub]
          constructor
          · grind
          · constructor
            · have : (polys.deref).val.length = (polys).val.length:= by
                simp [alloc.vec.Vec.deref]
              grind
            · intro h
              constructor
              · have : (polys.deref).val.length = (polys).val.length:= by
                  simp [alloc.vec.Vec.deref]
                grind
              · use 34#usize
                simp only [UScalar.ofNatCore_val_eq, true_and]
                use a
                have : (polys.deref).val = (polys).val:= by
                  simp [alloc.vec.Vec.deref]
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
    rename_i ones1
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD, List.length_eq_zero_iff, ne_eq,
      List.Vector.length_val, List.get_eq_getElem, Nat.reducePow, Nat.reduceSub, map_mul, map_pow,
      exists_and_left]
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
      · use (polys.deref)
        constructor
        · have : (polys.deref).val.length = (polys).val.length:= by
            simp [alloc.vec.Vec.deref]
          grind
        · simp_all only [not_false_eq_true, BitVec.ofNat_eq_ofNat,
          UScalarTy.U64_numBits_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
          forall_true_left, Nat.reducePow, Nat.reduceSub]
          constructor
          · grind
          · constructor
            · have : (polys.deref).val.length = (polys).val.length:= by
                simp [alloc.vec.Vec.deref]
              grind
            · intro h
              constructor
              · have : (polys.deref).val.length = (polys).val.length:= by
                  simp [alloc.vec.Vec.deref]
                grind
              · use 36#usize
                simp only [UScalar.ofNatCore_val_eq,  true_and]
                use a
                have : (polys.deref).val = (polys).val:= by
                  simp [alloc.vec.Vec.deref]
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
          ∃ (polys : Slice Poly),
            pts.val.length ≤ polys.val.length ∧
            (p.toGF216Poly = ∑ j ∈ Finset.range pts.val.length,
              C ((pts.val[j]!).y.toGF216) * (polys.val[j]!).toGF216Poly) ∧
            (pts.val.length = 0 →
              polys.val.length = 0 ∧ p.toGF216Poly = 0) ∧
            (pts.val.length ≠ 0 →
              polys.val.length = pts.val.length ∧
              ∃ (N : Usize) (ones1 : Array Pt N),
                N.val = pts.val.length ∧
                (∀ (j : Nat), j < N.val →
                  (ones1[j]!).x.value.val = j ∧
                  (ones1[j]!).y = GF16.ONE) ∧
                (∀ (j : Nat), j < N.val →
                  ∀ (hj : j < polys.val.length)
                    (hjo : j < ones1.length),
                    (polys.val[j]).toGF216Poly =
                      C ((ones1.val[j]!).y.toGF216 *
                          (lagrangeDenomProd (ones1[j]!).x
                            (ones1.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
                        condProdLinearFactors (ones1[j]!).x
                          (ones1.val.take N.val) 0))
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
