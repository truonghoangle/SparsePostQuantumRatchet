/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Coeff.ListOps
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Math.Poly.Eval
import Spqr.Math.Poly.Lagrange.InterpolantSum
import Spqr.Math.Poly.Horner.Eval
import Spqr.Math.Poly.ExpectedTrailing.Basic
import Spqr.Math.Poly.Identities.Basic
import Spqr.Specs.Encoding.Gf.GF16.AddAssign

/-!
# Spec theorem for `Poly::add_assign`: loop body 0

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the 16-bit
encodings:
  `a + b = a − b = a ⊕ b`,
so the `+=` performed in the in-range case is the same as the in-place XOR used by the Rust
`AddAssign` instance for `GF16`.

**Polynomial interpretation**: each step of the loop adds the `i`-th monomial `v · X^i` of `other`
to the running polynomial `self`.  After all iterations complete,
  `self.toGF216Poly = self_old.toGF216Poly + other.toGF216Poly`
in `GF216[X] = (GaloisField 2 16)[X]`.

**Source**: spqr/src/encoding/polynomial.rs (lines 240:8-246:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly core.iter.adapters.enumerate core.slice.iter

namespace spqr.encoding.polynomial.Poly.add_assign_loop

private lemma EnumerateSliceIter_next_post
    (iter : Enumerate
      (Iter GF16)) :
    ∃ (opt : Option (Usize × GF16))
      (iter' : Enumerate
        (Iter GF16)),
      Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (core.iter.traits.iterator.IteratorSliceIter GF16) iter =
          ok (opt, iter') := by
  simp only [Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    IteratorSliceIter.next]
  split <;> exact ⟨_, _, rfl⟩


private lemma in_range_update_post
    {coeffs : List GF16}
    {i : Nat} {v g1 : GF16}
    (h_lt : i < coeffs.length)
    (g1_post : g1.toGF216 = coeffs[i].toGF216 + v.toGF216) :
    let v1 := coeffs.set i g1
    (i < coeffs.length →
      v1.length = coeffs.length ∧
      (∀ (h : i < v1.length),
        (v1.get ⟨i, h⟩).toGF216 = coeffs[i]!.toGF216 + v.toGF216) ∧
      (∀ (k : Nat), k ≠ i → v1[k]? = coeffs[k]?)) ∧
    (¬ i < coeffs.length → v1 = coeffs ++ [v]) := by
  constructor
  · intro _
    refine ⟨by simp, fun h => ?_, fun k hk => ?_⟩
    · simp only [List.get_eq_getElem, List.getElem_set]
      simp only [ ↓reduceIte]
      rw [g1_post, getElem!_pos coeffs i h_lt]
    · grind
  · intro h; exact absurd h_lt h


/--
**Spec theorem for `encoding.polynomial.Poly.add_assign_loop.body`**:

One step of the `Poly::add_assign` iteration.  Given an enumerate iterator over the coefficients of
`other` and the current polynomial `self`, the body retrieves the next `(i, v)` pair from the
iterator and either terminates or processes the coefficient:

• The function always succeeds (no panic) provided the precondition holds, since `Vec::index_mut`,
  `Vec::push`, and the by-value `AddAssign<GF16>::add_assign` are all total on bounded integers
  within range.

• In the **done** case (iterator exhausted):
    the polynomial `self` is returned unchanged.

• In the **cont** case (received `(i, v)` from iterator), there exist `i : Usize` and
  `v : GF16` such that the result `self'` satisfies one of two sub-cases:

  - **In-range update** (`i.val < self.coefficients.val.length`):
    - The coefficient vector length is preserved:
        `self'.coefficients.val.length = self.coefficients.val.length`.
    - Position `i` has been updated with the GF(2¹⁶) sum:
        `self'.coefficients[i].toGF216 =
            self.coefficients[i].toGF216 + v.toGF216`
      where the `+` on the right-hand side is addition in
      `GF216 = GaloisField 2 16` (which, in characteristic 2,
      coincides with subtraction and is bitwise XOR of the 16-bit
      encodings).
    - All other positions are unchanged:
        `self'.coefficients.val[k]? = self.coefficients.val[k]?`
      for `k ≠ i.val`.

  - **Extension** (`¬ i.val < self.coefficients.val.length`):
    - The coefficient vector is extended by exactly one element:
        `self'.coefficients.val = self.coefficients.val ++ [v]`.

The precondition `self.coefficients.val.length < Usize.max` ensures that `Vec::len` does
not overflow and that `Vec::push` can accommodate the new element.

**Source**: spqr/src/encoding/polynomial.rs (lines 240:8-246:9)
-/
@[step]
theorem body_spec
    (iter : Enumerate
      (Iter GF16))
    (self : encoding.polynomial.Poly)
    (h_self_len : self.coefficients.val.length < Usize.max) :
    body iter self ⦃ cf =>
      match cf with
      | ControlFlow.done self' =>
          self' = self
      | ControlFlow.cont (_, self') =>
          ∃ (i : Usize) (v : GF16),
            (i.val < self.coefficients.val.length →
              self'.coefficients.val.length = self.coefficients.val.length ∧
              (∀ (h : i.val < self'.coefficients.val.length),
                (self'.coefficients.val.get ⟨i.val, h⟩).toGF216 =
                  (self.coefficients.val[i.val]!).toGF216 + v.toGF216) ∧
              (∀ (k : Nat),
                k ≠ i.val →
                self'.coefficients.val[k]? = self.coefficients.val[k]?)) ∧
            (¬ i.val < self.coefficients.val.length →
              self'.coefficients.val = self.coefficients.val ++ [v]) ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext⟩ := EnumerateSliceIter_next_post iter
  rw [hnext]
  simp only [bind_tc_ok]
  cases opt with
  | none =>
    simp [WP.spec_ok]
  | some p =>
    obtain ⟨i, v⟩ := p
    simp only [alloc.vec.Vec.len, UScalar.lt_equiv, Usize.ofNatCore_val_eq,
      alloc.vec.Vec.index_mut_slice_index, uncurry_apply_pair, List.get_eq_getElem,
      List.getElem!_eq_getElem?_getD, ne_eq, not_lt]
    have h_i_lt_len : i.val < self.coefficients.val.length →
        i.val < self.coefficients.val.length := id
    step*
    simp_all only [implies_true, getElem!_pos, alloc.vec.Vec.set_val_eq, List.length_set,
      forall_true_left, true_and]
    use i
    use v
    grind

/-!
# Spec theorem for `Poly::add_assign`: loop 0

After all iterations, the coefficient vector of the result represents the polynomial sum
`self + other` in `GF216[X]`.  Out-of-range coefficients (those beyond a polynomial's degree)
contribute `0 : GF216` to the sum, so the result polynomial is indeed the pointwise GF(2¹⁶)
addition of the coefficient vectors, padded with zeros to equal length:

  `result.toGF216Poly = self.toGF216Poly + listToGF216Poly other_coeffs`

where `listToGF216Poly` is the canonical map from `List GF16` to the Mathlib polynomial ring
`GF216[X] = (GaloisField 2 16)[X]`, and `other_coeffs` is the list of coefficients remaining in the
enumerate iterator.

**Loop invariant**: after processing `k` coefficients from the iterator (i.e., pairs
`(0, other_coeffs[0]), …, (k−1, other_coeffs[k−1])`), the running polynomial equals
`self₀.toGF216Poly + listToGF216Poly (other_coeffs.take k)`, where `self₀` is the initial
polynomial.  When the iterator is exhausted (`k = other_coeffs.length`), the take prefix becomes the
full list and the postcondition follows.

The preconditions are:
* `h_iter_data`: the remaining elements in the iterator equal `other_coeffs` — this connects the
  abstract enumerate-slice-iterator state to the ghost coefficient list.
* `h_count_eq`: the enumerate counter equals the slice iterator index — this ensures that the
  index `i` yielded by `enumerate` at each step matches the physical position in the slice, which
  is needed for the in-range/extension branch to correspond to the correct coefficient position.
* `h_start`: the slice iterator starts at position 0 — this ensures that the enumerate index
  equals the position in the coefficient list, which is required for the polynomial algebra to
  work out (the monomial `v · X^i` matches position `i` in the coefficient vector).
* `h_len`: `self.coefficients.val.length + other_coeffs.length ≤ Usize.max` — ensures that
  `Vec::len` does not overflow and `Vec::push` can accommodate new elements throughout all
  iterations.

**Source**: spqr/src/encoding/polynomial.rs (lines 240:8-246:9)
-/


private lemma poly_update_in_range
    (self self' : Poly)
    (i : Std.Usize) (v : GF16)
    (h_lt : i.val < self.coefficients.val.length)
    (h_len_eq : self'.coefficients.val.length = self.coefficients.val.length)
    (h_upd : ∀ (h : i.val < self'.coefficients.val.length),
      (self'.coefficients.val.get ⟨i.val, h⟩).toGF216 =
        (self.coefficients.val[i.val]!).toGF216 + v.toGF216)
    (h_other : ∀ (k : Nat), k ≠ i.val →
      self'.coefficients.val[k]? = self.coefficients.val[k]?) :
    self'.toGF216Poly = self.toGF216Poly + C (v.toGF216) * X ^ i.val := by
  unfold Poly.toGF216Poly
  ext m
  simp only [listToGF216Poly_coeff, coeff_add, coeff_C_mul, coeff_X_pow]
  by_cases hm_lt : m < self.coefficients.val.length
  · have hm_lt' : m < self'.coefficients.val.length := by omega
    rw [dif_pos hm_lt', dif_pos hm_lt]
    by_cases hm_eq : m = i.val
    · subst hm_eq
      rw [if_pos rfl, mul_one]
      have := h_upd hm_lt'
      rw [List.get_eq_getElem] at this
      simp [this]
      grind
    · rw [if_neg hm_eq, mul_zero, add_zero]
      have h_eq := h_other m hm_eq
      have : self'.coefficients.val[m]? = some (self'.coefficients.val.get ⟨m, hm_lt'⟩) := by
        simp [List.get_eq_getElem]
      have : self.coefficients.val[m]? = some (self.coefficients.val.get ⟨m, hm_lt⟩) := by
        simp [ List.get_eq_getElem]
      rw [List.get_eq_getElem, List.get_eq_getElem]
      have h1 : self'.coefficients.val[m]? = some (self'.coefficients.val[m]'hm_lt') := by
        simp
      have h2 : self.coefficients.val[m]? = some (self.coefficients.val[m]'hm_lt) := by
        simp
      rw [h1, h2] at h_eq
      simp at h_eq
      congr 1
  · push Not at hm_lt
    have hm_lt' : ¬(m < self'.coefficients.val.length) := by omega
    rw [dif_neg hm_lt']
    have hm_ne : m ≠ i.val := by omega
    simp [hm_ne]
    grind

private lemma poly_update_extension
    (self self' : Poly)
    (v : GF16)
    (h_ext : self'.coefficients.val = self.coefficients.val ++ [v]) :
    self'.toGF216Poly = self.toGF216Poly + C (v.toGF216) * X ^ self.coefficients.val.length := by
  unfold Poly.toGF216Poly
  rw [h_ext]
  exact listToGF216Poly_append_singleton self.coefficients.val v

private lemma step_invariant_preservation
    (orig_poly : GF216Poly)
    (self self' : Poly)
    (other_coeffs : List GF16)
    (k : Nat) (v : GF16)
    (hk : k < other_coeffs.length)
    (hv : other_coeffs.get ⟨k, hk⟩ = v)
    (h_prev : self.toGF216Poly = orig_poly + listToGF216Poly (other_coeffs.take k))
    (h_step : self'.toGF216Poly = self.toGF216Poly + C (v.toGF216) * X ^ k) :
    self'.toGF216Poly = orig_poly + listToGF216Poly (other_coeffs.take (k + 1)) := by
  rw [h_step, h_prev]
  have h_take_succ :
    other_coeffs.take (k + 1) = other_coeffs.take k ++ [other_coeffs.get ⟨k, hk⟩] := by simp
  rw [h_take_succ, listToGF216Poly_append_singleton]
  have h_take_len : (other_coeffs.take k).length = k := by
    rw [List.length_take]; omega
  rw [h_take_len, hv]
  ring

private lemma usize_wrapping_add_one_val (x : Std.Usize)
    (h : x.val + 1 ≤ Std.Usize.max) :
    (UScalar.wrapping_add x 1#usize).val = x.val + 1 := by
  simp only [UScalar.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
  have h1 : (1#usize : Usize).val = 1 := by simp
  rw [h1]
  apply Nat.mod_eq_of_lt
  scalar_tac

private lemma enumerate_sliceiter_next_some
    (iter : Enumerate
      (Iter GF16))
    (h_lt : iter.iter.i < iter.iter.slice.val.length)
    (h_count : iter.count.val = iter.iter.i)
    (h_bound : iter.iter.slice.val.length ≤ Std.Usize.max) :
    ∃ (iter1 : Enumerate
        (Iter GF16)),
      Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (core.iter.traits.iterator.IteratorSliceIter GF16) iter =
          ok (some (iter.count, iter.iter.slice.val[iter.iter.i]), iter1) ∧
      iter1.iter.slice = iter.iter.slice ∧
      iter1.iter.i = iter.iter.i + 1 ∧
      iter1.count.val = iter.iter.i + 1 := by
  simp only [
    Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    IteratorSliceIter.next]
  have h_wrapping : (UScalar.wrapping_add iter.count 1#usize).val = iter.iter.i + 1 := by
    have := usize_wrapping_add_one_val iter.count (by omega)
    rw [this, h_count]
  split
  · exact ⟨_, rfl, rfl, rfl, h_wrapping⟩
  · exact absurd h_lt ‹_›

private theorem body_cont_spec
    (iter' : Enumerate
      (Iter GF16))
    (self' : Poly)
    (h_self_len : self'.coefficients.val.length < Std.Usize.max)
    (h_count' : iter'.count.val = iter'.iter.i)
    (h_lt : iter'.iter.i < iter'.iter.slice.val.length)
    (h_bound' : iter'.iter.slice.val.length ≤ Std.Usize.max) :
    body iter' self' ⦃ cf =>
      match cf with
      | ControlFlow.done _ => False
      | ControlFlow.cont (iter'', self'') =>
          iter''.iter.slice = iter'.iter.slice ∧
          iter''.iter.i = iter'.iter.i + 1 ∧
          iter''.count.val = iter'.iter.i + 1 ∧
          (∃ (_ : iter'.iter.i < iter'.iter.slice.val.length)
           (i : Std.Usize) (v : GF16),
            i.val = iter'.iter.i ∧
            v = iter'.iter.slice.val[iter'.iter.i] ∧
            ((i.val < self'.coefficients.val.length →
              self''.coefficients.val.length = self'.coefficients.val.length ∧
              (∀ (h : i.val < self''.coefficients.val.length),
                (self''.coefficients.val.get ⟨i.val, h⟩).toGF216 =
                  (self'.coefficients.val[i.val]!).toGF216 + v.toGF216) ∧
              (∀ (k : Nat), k ≠ i.val →
                self''.coefficients.val[k]? = self'.coefficients.val[k]?)) ∧
            (¬ i.val < self'.coefficients.val.length →
              self''.coefficients.val = self'.coefficients.val ++ [v]))) ⦄ := by
  obtain ⟨iter1, h_next, h_iter1_slice, h_iter1_i, h_iter1_count⟩ :=
    enumerate_sliceiter_next_some iter' h_lt h_count' h_bound'
  unfold body
  rw [h_next]
  simp only [bind_tc_ok]
  have h_i_lt_len : iter'.count.val < self'.coefficients.val.length →
      iter'.count.val < self'.coefficients.val.length := id
  step*
  simp_all only [implies_true, alloc.vec.Vec.len, UScalar.lt_equiv, Usize.ofNatCore_val_eq,
    getElem!_pos, alloc.vec.Vec.set_val_eq, List.length_set, List.get_eq_getElem,
    forall_true_left, ne_eq, true_and, not_lt]
  grind

private theorem body_done_spec
    (iter' : Enumerate (Iter GF16)) (self' : Poly)
    (h_not_lt : ¬(iter'.iter.i < iter'.iter.slice.val.length)) :
    body iter' self' ⦃ cf =>
      match cf with
      | ControlFlow.done result => result = self'
      | ControlFlow.cont _ => False ⦄ := by
  unfold body
  simp only [
    Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    IteratorSliceIter.next]
  split
  · rename_i h_lt; exact absurd h_lt h_not_lt
  · simp [WP.spec_ok]


/--
**Spec theorem for `encoding.polynomial.Poly.add_assign_loop`**:

The full `Poly::add_assign` iteration loop.  Given an enumerate iterator over the coefficients of
another polynomial (represented as `other_coeffs : List GF16`) and the current polynomial `self`,
the loop processes all `(i, v)` pairs from the iterator and returns the updated polynomial `result`
satisfying:

• The function always succeeds (no panic) provided the preconditions hold, since the loop body
  (`add_assign_loop.body`) is total when the coefficient vector length stays within `Usize.max`.

• **Polynomial addition postcondition**:
    `result.toGF216Poly = self.toGF216Poly + listToGF216Poly other_coeffs`
  where `listToGF216Poly` interprets the coefficient list as a polynomial in
  `GF216[X] = (GaloisField 2 16)[X]`, and the `+` on the right-hand side is polynomial addition in
  `GF216[X]`.

When called from `encoding.polynomial.Poly.add_assign` with an iterator freshly created via
`Slice.iter` and `enumerate` over `other.coefficients`, the preconditions are trivially satisfied
(the iterator starts at position 0, the count is 0, and the remaining elements are exactly
`other.coefficients.val`), giving:
    `result.toGF216Poly = self.toGF216Poly + other.toGF216Poly`
which is the expected semantics of `self += other` in `GF216[X]`.

**Source**: spqr/src/encoding/polynomial.rs (lines 240:8-246:9)
-/
@[step]
theorem loop_spec
    (iter : Enumerate
      (Iter GF16))
    (self : Poly)
    (other_coeffs : List GF16)
    (h_iter_data : iter.iter.slice.val.drop iter.iter.i = other_coeffs)
    (h_count_eq : iter.count.val = iter.iter.i)
    (h_start : iter.iter.i = 0)
    (h_len : max self.coefficients.val.length other_coeffs.length < Std.Usize.max) :
    add_assign_loop iter self ⦃ (result : Poly) =>
        result.coefficients.val.length =
          max self.coefficients.val.length other_coeffs.length ∧
        result.toGF216Poly =
          self.toGF216Poly + listToGF216Poly other_coeffs ⦄ := by
  unfold Poly.add_assign_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Enumerate
                        (Iter GF16) ×
                      Poly) =>
                  p.1.iter.slice.val.length - p.1.iter.i)
    (inv := fun (p : Enumerate
                      (Iter GF16) ×
                    Poly) =>
        p.1.iter.slice = iter.iter.slice ∧
        iter.iter.i ≤ p.1.iter.i ∧
        p.1.iter.i ≤ p.1.iter.slice.val.length ∧
        p.1.count.val = p.1.iter.i ∧
        max p.2.coefficients.val.length
          (p.1.iter.slice.val.length - p.1.iter.i) ≤ Std.Usize.max ∧
        p.2.coefficients.val.length = max self.coefficients.val.length p.1.iter.i ∧
        p.2.toGF216Poly =
          self.toGF216Poly +
            listToGF216Poly (other_coeffs.take (p.1.iter.i - iter.iter.i)))
  · rintro ⟨iter', self'⟩
      ⟨h_slice', h_ge', h_le_slice', h_count', h_len', h_coeff_len', h_poly'⟩
    simp only [] at h_slice' h_ge' h_le_slice' h_count' h_len' h_coeff_len' h_poly' ⊢
    by_cases h_more : iter'.iter.i < iter'.iter.slice.val.length
    · have h_self_len : self'.coefficients.val.length < Std.Usize.max := by grind
      have h_bound' : iter'.iter.slice.val.length ≤ Std.Usize.max := by
        rw [h_slice']; grind
      have h_body := body_cont_spec iter' self' h_self_len h_count' h_more h_bound'
      apply WP.spec_mono h_body
      intro cf h_cf
      match cf with
      | ControlFlow.done result =>
        exact h_cf.elim
      | ControlFlow.cont (iter'', self'') =>
        simp only [] at h_cf ⊢
        obtain ⟨h_slice'', h_i_adv, h_count'', h_lt_slice, i, v, h_i_val, h_v_val,
          h_in_range, h_extension⟩ := h_cf
        have h_k : iter'.iter.i - iter.iter.i < other_coeffs.length := by
          have : other_coeffs.length = iter.iter.slice.val.length - iter.iter.i := by
            rw [← h_iter_data]; simp [List.length_drop]
          rw [h_slice'] at h_lt_slice
          omega
        have h_v_eq : other_coeffs.get ⟨iter'.iter.i - iter.iter.i, h_k⟩ = v := by
          have h_oc : other_coeffs = iter.iter.slice.val := by
            rw [← h_iter_data, h_start, List.drop_zero]
          simp only [h_oc, h_start, Nat.sub_zero, List.get_eq_getElem, h_v_val, h_slice']
        have h_k_eq : iter'.iter.i - iter.iter.i = iter'.iter.i := by omega
        have h_poly_step :
          self''.toGF216Poly = self'.toGF216Poly + C (v.toGF216) * X ^ iter'.iter.i := by
          rw [h_i_val] at h_in_range h_extension
          by_cases h_lt_coeff : iter'.iter.i < self'.coefficients.val.length
          · obtain ⟨h_len_eq, h_upd, h_other_k⟩ := h_in_range h_lt_coeff
            exact poly_update_in_range self' self'' ⟨⟨iter'.iter.i, by scalar_tac⟩⟩ v
              (by exact h_lt_coeff) (by exact h_len_eq)
              (by exact h_upd) (by exact h_other_k)
          · have h_ext := h_extension h_lt_coeff
            have h_len_eq_k : self'.coefficients.val.length = iter'.iter.i := by
              rw [h_coeff_len']; omega
            have h_poly := poly_update_extension self' self'' v h_ext
            rw [h_len_eq_k] at h_poly
            exact h_poly
        constructor
        · rw [h_i_val] at h_in_range h_extension
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [h_slice'', h_slice']
          · rw [h_i_adv]; omega
          · rw [h_i_adv, h_slice'', h_slice']; grind
          · rw [h_i_adv, h_count'']
          · have h_slice_len : iter''.iter.slice.val.length = iter'.iter.slice.val.length := by
              rw [h_slice'']
            by_cases h_lt_coeff : iter'.iter.i < self'.coefficients.val.length
            · obtain ⟨h_len_eq, _, _⟩ := h_in_range h_lt_coeff
              rw [h_i_adv, h_slice_len, h_len_eq]; omega
            · have h_ext := h_extension h_lt_coeff
              have : self''.coefficients.val.length = self'.coefficients.val.length + 1 := by
                rw [h_ext]; simp
              rw [h_i_adv, h_slice_len]; omega
          · by_cases h_lt_coeff : iter'.iter.i < self'.coefficients.val.length
            · obtain ⟨h_len_eq, _, _⟩ := h_in_range h_lt_coeff
              rw [h_i_adv, h_len_eq, h_coeff_len']; omega
            · have h_ext := h_extension h_lt_coeff
              have : self''.coefficients.val.length = self'.coefficients.val.length + 1 := by
                rw [h_ext]; simp
              rw [h_i_adv]; omega
          · rw [h_i_adv]
            have h_new_k :
              iter'.iter.i + 1 - iter.iter.i = (iter'.iter.i - iter.iter.i) + 1 := by omega
            rw [h_new_k]
            exact step_invariant_preservation
              self.toGF216Poly self' self'' other_coeffs
              (iter'.iter.i - iter.iter.i) v h_k h_v_eq h_poly'
              (by rw [h_k_eq]; exact h_poly_step)
        · rw [h_i_adv]
          have h_slice_eq : iter''.iter.slice.val.length = iter'.iter.slice.val.length := by
            rw [h_slice'', h_slice']
          rw [h_slice_eq]
          omega
    · have h_body := body_done_spec iter' self' h_more
      apply WP.spec_mono h_body
      intro cf h_cf
      match cf with
      | ControlFlow.done result =>
        simp only [] at h_cf ⊢
        subst h_cf
        rw [h_poly']
        have h_exhausted : iter'.iter.i ≥ iter'.iter.slice.val.length := by
          push Not at h_more; exact h_more
        have h_oc_len : other_coeffs.length = iter.iter.slice.val.length - iter.iter.i := by
          rw [← h_iter_data]; simp [List.length_drop]
        have h_all_taken : other_coeffs.take (iter'.iter.i - iter.iter.i) = other_coeffs := by
          apply List.take_of_length_le
          rw [h_slice'] at h_exhausted
          omega
        refine ⟨?_, ?_⟩
        · rw [h_coeff_len']
          rw [h_slice'] at h_exhausted
          have h_i_eq : iter'.iter.i = other_coeffs.length := by grind
          rw [h_i_eq]
        · rw [h_all_taken]
      | ControlFlow.cont _ =>
        exact h_cf.elim
  · refine ⟨rfl, le_refl _, ?_, h_count_eq, ?_, ?_, ?_⟩
    · change iter.iter.i ≤ iter.iter.slice.val.length
      omega
    · grind
    · rw [h_start]; simp
    · simp [List.take_zero]

end spqr.encoding.polynomial.Poly.add_assign_loop


/-!
# Spec theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::add_assign`

After all iterations, the result polynomial represents the sum `self + other` in
`GF216[X] = (GaloisField 2 16)[X]`.

The Aeneas-extracted Lean function `encoding.polynomial.Poly.add_assign` is a direct delegation:
  1. `alloc.vec.Vec.deref other.coefficients` — obtains the coefficient slice.
  2. `core.slice.Slice.iter` — creates a slice iterator (starting at index 0).
  3. `core.slice.iter.IteratorSliceIter.enumerate` — wraps with an enumerate adapter (count 0).
  4. `encoding.polynomial.Poly.add_assign_loop iter self` — the verified loop driver.

**Source**: spqr/src/encoding/polynomial.rs (lines 239:4-247:5)
-/

namespace spqr.encoding.polynomial.Poly

/--
**Spec theorem for `encoding.polynomial.Poly.add_assign`**:

• The function always succeeds (no panic) provided the combined coefficient vector length is within
  `Usize.max`, since the underlying iterator creation (`Slice.iter`, `enumerate`) and the loop
  driver (`add_assign_loop`) are all total on bounded vectors.

• **Polynomial addition postcondition**:
    `result.toGF216Poly = self.toGF216Poly + other.toGF216Poly`
  where `toGF216Poly : Poly → GF216Poly` interprets the coefficient vector as a polynomial in
  `GF216[X] = (GaloisField 2 16)[X]`, and the `+` on the right-hand side is polynomial addition in
  `GF216[X]`.

  In GF(2¹⁶) (characteristic 2), polynomial addition is coefficient-wise XOR, so this is
  equivalent to `self ⊕ other` on the coefficient vectors (padded with zeros to equal length).

**Source**: spqr/src/encoding/polynomial.rs (lines 239:4-247:5)
-/
@[step]
theorem add_assign_spec
    (self other : Poly)
    (h_len : max self.coefficients.val.length other.coefficients.val.length < Usize.max) :
    add_assign self other ⦃ (result : Poly) =>
      result.coefficients.val.length =
        max self.coefficients.val.length other.coefficients.val.length ∧
      result.toGF216Poly = self.toGF216Poly + other.toGF216Poly ⦄ := by
  unfold add_assign
  simp only [alloc.vec.Vec.deref, core.slice.Slice.iter,
             core.slice.iter.IteratorSliceIter.enumerate, bind_tc_ok]
  apply WP.spec_mono (add_assign_loop.loop_spec _ self other.coefficients.val
    (by simp) (by simp) rfl h_len)
  intro result h
  exact h

end spqr.encoding.polynomial.Poly
