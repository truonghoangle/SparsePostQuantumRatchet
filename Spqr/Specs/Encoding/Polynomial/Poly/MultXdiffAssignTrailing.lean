/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Gf.GF16.Mul
import Spqr.Specs.Encoding.Gf.GF16.SubAssign
/-!
# Spec theorem for `mult_xdiff_assign_trailing`: loop body 0

Given a polynomial represented as a vector of GF(2¹⁶) coefficients `v = [c₀, c₁, …, cₙ₋₁]` in
ascending degree order and a field element `difference : GF16`, the function
`Poly.mult_xdiff_assign_trailing(start, difference)` computes in place the product `self[start..] *=
(x − difference)` of the trailing sub-polynomial (from index `start` to the end) by the linear
factor `(x − difference)`.

Since GF(2¹⁶) has characteristic 2, subtraction coincides with addition, so `(x − difference) = (x +
difference)`.  The multiplication is performed by the recurrence:

  `v[i − 1] −= v[i] * difference`    for `i` in `start..l`

where `l = self.coefficients.len()`.  Distributing `(x − d)` over the polynomial `p(x) = ∑ᵢ cᵢ xⁱ`
gives:
  `x · p(x) − d · p(x)`
The `x · p(x)` part shifts every coefficient up by one position (implicit in the indexing), while
the `−d · p(x)` part subtracts `cᵢ · d` from position `i − 1`.  The loop traverses from `start` to
`l − 1`, performing this carry propagation in place.

Each step of the loop body (this function):

1. Retrieves the next index `i` from the range iterator `start..l`.
2. If the iterator is exhausted (`none`), returns `done` with the current coefficient vector — the
   multiplication is complete.
3. Otherwise, reads `v[i]`, computes `delta = v[i] * difference` in GF(2¹⁶), then updates `v[i − 1]
   −= delta`, and returns `cont` with the updated vector and the advanced iterator.

**Source**: spqr/src/encoding/polynomial.rs (lines 176:8-180:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.Poly.mult_xdiff_assign_trailing_loop

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

/--
The range iterator `next` always returns `ok` and either provides the current `start` value (when
`start < end`) or `none` (when `start ≥ end`).  This is the concrete specification for the
`core.ops.range.Range<usize>` iterator used in the Rust `for i in start..l` loop.
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
**Spec theorem for `encoding.polynomial.Poly.mult_xdiff_assign_trailing_loop.body`**:

One step of the in-place multiplication `self[start..] *= (x − difference)`.  Given a GF(2¹⁶) field
element `difference`, a range iterator over `start..l`, and the current coefficient vector `v`, the
body processes the next index from the iterator:

• The function always succeeds (no panic) for any valid inputs satisfying the preconditions, since
  `Mul<GF16>`, `SubAssign<GF16>`, and vector indexing are total on bounded integers within range.
• In the `done` case (iterator exhausted):
    `result = v` (vector unchanged).
• In the `cont` case (index `i` processed):
    - The iterator has advanced by one: `iter'.start = iter.start + 1`.
    - The vector length is preserved: `v'.length = v.length`.
    - Position `i − 1` has been updated:
        `v'[i−1].toGF216 =
            v[i−1].toGF216 −
            v[i].toGF216 * difference.toGF216`
      where the subtraction on the right-hand side is in
      `GF216 = GaloisField 2 16` (which, in characteristic 2,
      coincides with addition).
    - All other positions are unchanged:
        `v'[j] = v[j]`  for `j ≠ i − 1`.

**Source**: spqr/src/encoding/polynomial.rs (lines 176:8-180:9)
-/
@[step]
theorem body_spec
    (difference : spqr.encoding.gf.GF16)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (h_start_ge : 1 ≤ iter.start.val)
    (h_end_eq : iter.«end».val = v.val.length) :
    body difference iter v ⦃ cf =>
      match cf with
      | ControlFlow.done r =>
          r = v ∧ ¬ (iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, v1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          v1.val.length = v.val.length ∧
          (∀ (h_idx : iter.start.val - 1 < v1.val.length),
            (v1.val.get ⟨iter.start.val - 1, h_idx⟩).toGF216 =
              (v.val[iter.start.val - 1]!).toGF216 -
              (v.val[iter.start.val]!).toGF216 *
                difference.toGF216) ∧
          (∀ (j : Nat),
            j ≠ iter.start.val - 1 →
            v1.val[j]? = v.val[j]?) ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext, h_none, h_some⟩ := IteratorRange_next_Usize_post iter
  rw [hnext]; simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]; simp only
    have h_i_lt_len : iter.start.val < v.val.length := by omega
    have h_im1_lt_len : iter.start.val - 1 < v.val.length := by omega
    step*
    all_goals simp_all
  · obtain ⟨h_opt_eq, h_range_eq⟩ := h_none (by omega)
    rw [h_opt_eq]; simp only [WP.spec_ok]
    exact ⟨trivial, by omega⟩

end spqr.encoding.polynomial.Poly.mult_xdiff_assign_trailing_loop

/-!
# Spec theorem for `mult_xdiff_assign_trailing`: loop 0

Given a polynomial represented as a vector of GF(2¹⁶) coefficients `v = [c₀, c₁, …, cₙ₋₁]` in
ascending degree order and a field element `difference : GF16`, the loop
`Poly.mult_xdiff_assign_trailing_loop` iterates over the range `start..l` (where `l = v.length`) and
computes in place the product `self[start..] *= (x − difference)` of the trailing sub-polynomial
(from index `start` to the end) by the linear factor `(x − difference)`.

Since GF(2¹⁶) has characteristic 2, subtraction coincides with addition, so `(x − difference) = (x +
difference)`.  The multiplication is performed by the recurrence:

  `v[i − 1] −= v[i] * difference`    for `i` in `start..l`

where `l = self.coefficients.len()`.  Distributing `(x − d)` over the polynomial `p(x) = ∑ᵢ cᵢ xⁱ`
gives:
  `x · p(x) − d · p(x)`
The `x · p(x)` part shifts every coefficient up by one position (implicit in the indexing), while
the `−d · p(x)` part subtracts `cᵢ · d` from position `i − 1`.  The loop traverses from `start` to
`l − 1`, performing this carry propagation in place.

This file specifies the full loop (the `loop` fixed-point wrapper around the body), providing a
closed-form postcondition that characterises the entire output vector after all iterations.  The
per-iteration specification is in
`Spqr.Specs.Encoding.Polynomial.Poly.MultXdiffAssignTrailingLoopBody0`.

**Closed-form postcondition**:

After the loop completes with range `start..l`:

1. The vector length is preserved: `result.length = v.length`.
2. For each position `j` with `start ≤ j + 1` and `j + 1 < l`
   (the "carry-propagated" positions):
     `result[j].toGF216 =
         v[j].toGF216 −
         v[j + 1].toGF216 * difference.toGF216`
   where the subtraction on the right-hand side is in
   `GF216 = GaloisField 2 16` (which, in characteristic 2,
   coincides with addition).
3. All other positions are unchanged:
     `result[j]? = v[j]?`  for `j` outside the carry range.

The correctness of each step relies on the fact that when processing index `i`, positions `i, i+1,
…, l−1` in the current vector still hold their original values (only positions `start−1, …, i−2`
have been modified so far), so reading `v_current[i]` yields the original `v[i]`.

**Source**: spqr/src/encoding/polynomial.rs (lines 176:8-180:9)
-/

namespace spqr.encoding.polynomial.Poly.mult_xdiff_assign_trailing_loop

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

private lemma list_get_of_getElem?_eq {T : Type} {xs ys : List T}
    {k : Nat}
    (h : xs[k]? = ys[k]?) (hx : k < xs.length) (hy : k < ys.length) :
    xs.get ⟨k, hx⟩ = ys.get ⟨k, hy⟩ := by
  have h1 : xs[k]? = some (xs.get ⟨k, hx⟩) := List.getElem?_eq_getElem hx
  have h2 : ys[k]? = some (ys.get ⟨k, hy⟩) := List.getElem?_eq_getElem hy
  rw [h1, h2] at h
  exact Option.some_injective _ h

private lemma getElem_bang_eq {T : Type} [Inhabited T] {xs ys : List T} {k : Nat}
    (h : xs[k]? = ys[k]?)
    (hx : k < xs.length) (hy : k < ys.length) :
    xs[k]! = ys[k]! := by
  rw [getElem!_pos xs k hx, getElem!_pos ys k hy]
  exact list_get_of_getElem?_eq h hx hy

/--
**Closed-form postcondition for `encoding.polynomial.Poly.mult_xdiff_assign_trailing_loop`**:

The full in-place multiplication loop `self[start..] *= (x − difference)`.  Starting from a range
`start..l` and a coefficient vector `v` of length `l`, the loop processes indices `i = start,
start+1, …, l−1` and returns a vector `result` of the same length satisfying:

• **Length preserved**: `result.length = v.length`.
• **Carry-propagated positions** (`start ≤ j + 1 ∧ j + 1 < l`):
    `result[j].toGF216 =
        v[j].toGF216 −
        v[j+1].toGF216 * difference.toGF216`
  where the subtraction is in `GF216 = GaloisField 2 16`
  (equivalently, addition in characteristic 2).
• **Unchanged positions** (all other `j`):
    `result[j]? = v[j]?`.

The loop invariant tracks which positions have been processed: after iterating indices `start, …,
k−1`, positions `start−1, …, k−2` carry their final values and all other positions still hold their
original values.  The body spec (`MultXdiffAssignTrailingLoopBody0.body_spec`) guarantees that each
step modifies exactly one position (`i−1`) and leaves all others unchanged, and the key correctness
observation is that the read position (`i`) has not yet been modified when step `i` executes.

**Source**: spqr/src/encoding/polynomial.rs (lines 176:8-180:9)
-/
@[step]
theorem loop_spec
    (difference : spqr.encoding.gf.GF16)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (h_start_ge : 1 ≤ iter.start.val)
    (h_end_eq : iter.«end».val = v.val.length)
    (h_le : iter.start.val ≤ iter.«end».val) :
    spqr.encoding.polynomial.Poly.mult_xdiff_assign_trailing_loop
      iter v difference ⦃ result =>
      result.val.length = v.val.length ∧
      (∀ (j : Nat),
        iter.start.val ≤ j + 1 →
        j + 1 < iter.«end».val →
        ∀ (hj : j < result.val.length),
          (result.val.get ⟨j, hj⟩).toGF216 =
            (v.val[j]!).toGF216 -
            (v.val[j + 1]!).toGF216 *
              difference.toGF216) ∧
      (∀ (j : Nat),
        ¬(iter.start.val ≤ j + 1 ∧ j + 1 < iter.«end».val) →
        result.val[j]? = v.val[j]?) ⦄ := by
  unfold spqr.encoding.polynomial.Poly.mult_xdiff_assign_trailing_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                        alloc.vec.Vec spqr.encoding.gf.GF16) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                    alloc.vec.Vec spqr.encoding.gf.GF16) =>
        p.1.«end» = iter.«end» ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ iter.«end».val ∧
        p.2.val.length = v.val.length ∧
        (∀ (j : Nat),
          iter.start.val ≤ j + 1 →
          j + 1 < p.1.start.val →
          ∀ (hj : j < p.2.val.length),
            (p.2.val.get ⟨j, hj⟩).toGF216 =
              (v.val[j]!).toGF216 -
              (v.val[j + 1]!).toGF216 *
                difference.toGF216) ∧
        (∀ (j : Nat),
          ¬(iter.start.val ≤ j + 1 ∧ j + 1 < p.1.start.val) →
          p.2.val[j]? = v.val[j]?))
  · rintro ⟨iter', v'⟩ ⟨h_end', h_ge', h_le', h_len', h_processed, h_unchanged⟩
    simp only [] at h_end' h_ge' h_le' h_len' h_processed h_unchanged ⊢
    have h_start_ge' : 1 ≤ iter'.start.val := by omega
    have h_end_eq' : iter'.«end».val = v'.val.length := by grind
    step*
    split
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_eq, h_nlt⟩ := r_post
      subst h_eq
      refine ⟨h_len', ?_, ?_⟩
      · intro j hj1 hj2 hj
        exact h_processed j hj1 (by omega) hj
      · intro j hj
        apply h_unchanged
        push_neg at hj ⊢
        intro h1; have := hj h1; omega
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_lt, h_start1, h_end1, h_v1len, h_modified, h_frame⟩ := r_post
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_end1]; exact h_end'
      · omega
      · omega
      · omega
      · intro j hj1 hj2 hj
        by_cases hjk : j + 1 < iter'.start.val
        · have hj_ne : j ≠ iter'.start.val - 1 := by omega
          have hj_v' : j < v'.val.length := by omega
          have h_fr := h_frame j hj_ne
          have h_old := h_processed j hj1 hjk hj_v'
          have h_get_eq := list_get_of_getElem?_eq h_fr hj hj_v'
          simp only [List.get_eq_getElem] at h_get_eq h_old ⊢
          rw [h_get_eq, h_old]
        · have hj_eq : j = iter'.start.val - 1 := by omega
          subst hj_eq
          have h_mod := h_modified (by omega)
          have h_unch_m1 : v'.val[iter'.start.val - 1]? = v.val[iter'.start.val - 1]? :=
            h_unchanged (iter'.start.val - 1) (by push_neg; intro _; omega)
          have h_unch_s : v'.val[iter'.start.val]? = v.val[iter'.start.val]? :=
            h_unchanged iter'.start.val (by push_neg; intro _; omega)
          have h_bang_m1 := getElem_bang_eq h_unch_m1 (by omega) (by omega)
          have h_bang_s := getElem_bang_eq h_unch_s (by omega) (by omega)
          simp only [List.get_eq_getElem] at h_mod ⊢
          rw [h_mod, h_bang_m1, h_bang_s]
          grind
      · intro j hj
        push_neg at hj
        have hj_ne : j ≠ iter'.start.val - 1 := by
          intro heq; subst heq
          grind
        have h_fr := h_frame j hj_ne
        have h_old_unch : v'.val[j]? = v.val[j]? := by
          apply h_unchanged; push_neg; intro h1
          have := hj h1; omega
        rw [h_fr, h_old_unch]
      · grind
  · refine ⟨rfl, le_refl _, h_le, rfl, ?_, ?_⟩
    · intro j hj1 hj2
      grind
    · intro _ _; rfl

end spqr.encoding.polynomial.Poly.mult_xdiff_assign_trailing_loop

/-!
# Spec theorem for `mult_xdiff_assign_trailing`

Given a polynomial represented as a vector of GF(2¹⁶) coefficients `v = [c₀, c₁, …, cₙ₋₁]` in
ascending degree order and a field element `difference : GF16`, the function
`Poly.mult_xdiff_assign_trailing(start, difference)` computes in place the product `self[start..] *=
(x − difference)` of the trailing sub-polynomial (from index `start` to the end) by the linear
factor `(x − difference)`.

Since GF(2¹⁶) has characteristic 2, subtraction coincides with addition, so `(x − difference) = (x +
difference)`.  The multiplication is performed by the recurrence:

  `v[i − 1] −= v[i] * difference`    for `i` in `start..l`

where `l = self.coefficients.len()`.  Distributing `(x − d)` over the polynomial `p(x) = ∑ᵢ cᵢ xⁱ`
gives:
  `x · p(x) − d · p(x)`
The `x · p(x)` part shifts every coefficient up by one position (implicit in the indexing), while
the `−d · p(x)` part subtracts `cᵢ · d` from position `i − 1`.  The loop traverses from `start` to
`l − 1`, performing this carry propagation in place.

This file specifies the top-level wrapper `Poly.mult_xdiff_assign_trailing`, which:
  1. Reads `l := self.coefficients.len()`.
  2. Calls the loop `mult_xdiff_assign_trailing_loop` with the
     range `start..l` on the coefficient vector.
  3. Wraps the resulting vector back into a `Poly`.

The postcondition is inherited directly from the loop specification in
`Spqr.Specs.Encoding.Polynomial.Poly.MultXdiffAssignTrailingLoop0`:

1. The coefficient vector length is preserved:
     `result.coefficients.length = self.coefficients.length`.
2. For each carry-propagated position `j` with
   `start ≤ j + 1` and `j + 1 < l`:
     `result.toGF216.coefficients[j] =
         self.toGF216.coefficients[j] −
         self.toGF216.coefficients[j + 1] * difference.toGF216`
   where the subtraction is in `GF216 = GaloisField 2 16`
   (equivalently, addition in characteristic 2).
3. All other positions are unchanged:
     `result.coefficients[j]? = self.coefficients[j]?`.

**Source**: spqr/src/encoding/polynomial.rs (lines 174:4-181:5)
-/

namespace spqr.encoding.polynomial.Poly

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

open Polynomial

private lemma list_get_of_getElem?_eq' {T : Type} {xs ys : List T}
    {k : Nat}
    (h : xs[k]? = ys[k]?) (hx : k < xs.length) (hy : k < ys.length) :
    xs.get ⟨k, hx⟩ = ys.get ⟨k, hy⟩ := by
  have h1 : xs[k]? = some (xs.get ⟨k, hx⟩) := List.getElem?_eq_getElem hx
  have h2 : ys[k]? = some (ys.get ⟨k, hy⟩) := List.getElem?_eq_getElem hy
  rw [h1, h2] at h
  exact Option.some_injective _ h

/-- Drop indexing: `(l.drop n).get ⟨k, hk⟩ = l.get ⟨n + k, _⟩`. -/
private lemma list_get_drop_eq {α : Type*} (l : List α) (n k : Nat)
    (hk : k < (l.drop n).length) :
    (l.drop n).get ⟨k, hk⟩ =
      l.get ⟨n + k, by rw [List.length_drop] at hk; omega⟩ := by
  simp only [List.get_eq_getElem, List.getElem_drop]

/--
**Mathematical polynomial identity for `mult_xdiff_assign_trailing`.**

Given a coefficient list `cs`, a result list `rs` of the same length, a starting index `s ≥ 1` with
`s ≤ cs.length`, and a field element `d : GF16` such that:
• For carry-propagated positions (`s ≤ j + 1 ∧ j + 1 < cs.length`):
    `rs[j].toGF216 = cs[j].toGF216 − cs[j+1].toGF216 * d.toGF216`
• All other positions are unchanged (`rs[j]? = cs[j]?`),

then the polynomial interpretation of `rs` satisfies:

  `listToGF216Poly rs =
      listToGF216Poly cs −
      C(d.toGF216) · X^(s−1) · listToGF216Poly (cs.drop s)`

This identity captures the algebraic content of the in-place recurrence `v[i−1] −= v[i] * d` for
`i ∈ start..l`: the result polynomial is obtained from the original by subtracting the trailing
sub-polynomial (from position `s`) scaled by `d` and shifted down by one degree.  Since GF(2¹⁶) has
characteristic 2, subtraction coincides with addition.
-/
private lemma mult_xdiff_poly_identity
    (cs rs : List GF16) (s : Nat) (d : GF16)
    (h_s_pos : 1 ≤ s) (h_s_le : s ≤ cs.length)
    (h_len : rs.length = cs.length)
    (h_mod : ∀ j, s ≤ j + 1 → j + 1 < cs.length → ∀ hj : j < rs.length,
      (rs.get ⟨j, hj⟩).toGF216 = (cs[j]!).toGF216 - (cs[j + 1]!).toGF216 * d.toGF216)
    (h_same : ∀ j, ¬(s ≤ j + 1 ∧ j + 1 < cs.length) → rs[j]? = cs[j]?) :
    listToGF216Poly rs =
      listToGF216Poly cs -
      C d.toGF216 * X ^ (s - 1) * listToGF216Poly (cs.drop s) := by
  ext m
  rw [coeff_sub, listToGF216Poly_coeff, listToGF216Poly_coeff,
      show C d.toGF216 * X ^ (s - 1) * listToGF216Poly (cs.drop s) =
        C d.toGF216 * (listToGF216Poly (cs.drop s) * X ^ (s - 1)) by ring,
      coeff_C_mul, coeff_mul_X_pow']
  by_cases hm : m < cs.length
  · -- m < cs.length (= rs.length)
    rw [dif_pos (show m < rs.length by omega), dif_pos hm]
    by_cases hs : s - 1 ≤ m
    · -- s − 1 ≤ m: product term may be nonzero
      rw [if_pos hs, listToGF216Poly_coeff]
      by_cases hd : m - (s - 1) < (cs.drop s).length
      · -- m + 1 < cs.length: carry-propagated position
        rw [dif_pos hd]
        have h2 : m + 1 < cs.length := by rw [List.length_drop] at hd; omega
        have hmod := h_mod m (by omega) h2 (by omega)
        simp only [List.get_eq_getElem] at hmod ⊢
        rw [hmod, getElem!_pos cs m hm, getElem!_pos cs (m + 1) h2]
        have h_drop := list_get_drop_eq cs s (m - (s - 1)) hd
        simp only [List.get_eq_getElem] at h_drop
        rw [h_drop]; simp only [show s + (m - (s - 1)) = m + 1 from by omega]; ring
      · -- m ≥ cs.length − 1: product term has zero factor
        rw [dif_neg hd, mul_zero, sub_zero]
        have h_not : ¬(s ≤ m + 1 ∧ m + 1 < cs.length) := by
          rw [List.length_drop] at hd; push_neg at hd ⊢; intro h1; omega
        exact congr_arg GF16.toGF216
          (list_get_of_getElem?_eq' (h_same m h_not) (by omega) hm)
    · -- m < s − 1: product term is zero
      rw [if_neg hs, mul_zero, sub_zero]
      exact congr_arg GF16.toGF216
        (list_get_of_getElem?_eq' (h_same m (by push_neg; intro h1; omega)) (by omega) hm)
  · -- m ≥ cs.length: both sides are zero
    push_neg at hm
    rw [dif_neg (by omega), dif_neg (by omega)]
    by_cases hs : s - 1 ≤ m
    · rw [if_pos hs, listToGF216Poly_coeff,
          dif_neg (by rw [List.length_drop]; omega), mul_zero]; ring
    · rw [if_neg hs]; ring

/--
**Spec theorem for `encoding.polynomial.Poly.mult_xdiff_assign_trailing`**:

• The function always succeeds (no panic) for any `Poly`, `start`, and `difference` satisfying the
  preconditions `1 ≤ start` and `start ≤ self.coefficients.length`, since the underlying loop
  `mult_xdiff_assign_trailing_loop` is total on bounded indices within range, and the `Mul<GF16>`
  and `SubAssign<GF16>` field operations are total.
• The coefficient vector length is preserved:
    `result.coefficients.length = self.coefficients.length`.
• For carry-propagated positions (`start ≤ j + 1 ∧ j + 1 < l`):
    `result.toGF216.coefficients[j] =
        self.toGF216.coefficients[j] −
        self.toGF216.coefficients[j+1] * difference.toGF216`
  where the subtraction is in `GF216 = GaloisField 2 16`
  (equivalently, addition in characteristic 2).
• All other positions are unchanged:
    `result.coefficients[j]? = self.coefficients[j]?`.
• **Mathematical polynomial identity**:
    `result.toGF216Poly =
        self.toGF216Poly −
        C(difference.toGF216) · X^(start − 1) ·
          listToGF216Poly(self.coefficients.val.drop start)`
  This expresses the algebraic content of the in-place recurrence
  `v[i−1] −= v[i] * difference` for `i ∈ start..l`: the result
  polynomial is obtained from the original by subtracting the trailing
  sub-polynomial (from position `start`) scaled by `difference` and
  shifted down by one degree.  Since GF(2¹⁶) has characteristic 2,
  subtraction coincides with addition.

**Source**: spqr/src/encoding/polynomial.rs (lines 174:4-181:5)
-/
@[step]
theorem mult_xdiff_assign_trailing_spec
    (self : Poly)
    (start : Usize)
    (difference : GF16)
    (h_start_pos : 1 ≤ start.val)
    (h_start_le : start.val ≤ self.coefficients.val.length) :
    mult_xdiff_assign_trailing self start difference
      ⦃ (result : Poly) =>
      result.coefficients.val.length = self.coefficients.val.length ∧
      (∀ (j : Nat),
        start.val ≤ j + 1 →
        j + 1 < self.coefficients.val.length →
        ∀ (hj : j < result.coefficients.val.length),
          (result.coefficients.val.get ⟨j, hj⟩).toGF216 =
            (self.coefficients.val[j]!).toGF216 -
            (self.coefficients.val[j + 1]!).toGF216 *
              difference.toGF216) ∧
      (∀ (j : Nat),
        ¬(start.val ≤ j + 1 ∧ j + 1 < self.coefficients.val.length) →
        result.coefficients.val[j]? = self.coefficients.val[j]?) ∧
      result.toGF216Poly =
        self.toGF216Poly -
        C (difference.toGF216) * X ^ (start.val - 1) *
          listToGF216Poly (self.coefficients.val.drop start.val) ⦄ := by
  unfold encoding.polynomial.Poly.mult_xdiff_assign_trailing
  step*
  refine ⟨‹_›, ‹_›, ‹_›, ?_⟩
  simp only [Poly.toGF216Poly]
  exact mult_xdiff_poly_identity _ _ _ _
    h_start_pos h_start_le ‹_› ‹_› ‹_›

end spqr.encoding.polynomial.Poly
