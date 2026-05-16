/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.Poly.AddAssignLoopBody0

/-!
# Spec theorem for `Poly::add_assign`: loop 0

The Rust function `Poly::add_assign` (in `src/encoding/polynomial.rs`, lines 239:4-247:5) implements
in-place polynomial addition `self += other` in GF(2¹⁶)[X].  It iterates over the coefficients of
`other` using an `enumerate` iterator, processing one coefficient `(i, v)` at a time:

```
for (i, v) in other.coefficients.iter().enumerate() {
    if i < self.coefficients.len() {
        self.coefficients[i] += *v;    // GF16 add-assign (XOR)
    } else {
        self.coefficients.push(*v);     // extend self
    }
}
```

This file specifies the **full loop** — the `loop` fixed-point wrapper around the body
(`AddAssignLoopBody0.body_spec`).  The loop consumes the enumerate iterator over `other`'s
coefficients, processing each `(i, v)` pair in order until the iterator is exhausted.  At each step:

  1. **In-range update** (`i < self.coefficients.len()`): the coefficient at
     position `i` is replaced with the GF(2¹⁶) sum `self.coefficients[i] + v`,
     where the addition is in
     `GF216 = GaloisField 2 16` (which, in characteristic 2, coincides with subtraction and is
     bitwise XOR of the 16-bit encodings).
  2. **Extension** (`i ≥ self.coefficients.len()`): the value `v` is appended to
     `self.coefficients` via `Vec::push`.

After all iterations, the coefficient vector of the result represents the polynomial sum
`self + other` in `GF216[X]`.  Out-of-range coefficients (those beyond a polynomial's degree)
contribute `0 : GF216` to the sum, so the result polynomial is indeed the pointwise GF(2¹⁶)
addition of the coefficient vectors, padded with zeros to equal length:

  `result.toGF216Poly = self.toGF216Poly + listToGF216Poly other_coeffs`

where `listToGF216Poly` is the canonical map from `List GF16` to the Mathlib polynomial ring
`GF216[X] = (GaloisField 2 16)[X]`, and `other_coeffs` is the list of coefficients remaining in the
enumerate iterator.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR:
  `a + b = a − b = a ⊕ b`,
so the `+=` in the in-range case is the same as the in-place XOR used by the Rust `AddAssign`
instance for `GF16`.

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

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly.add_assign_loop

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

/-! ## Helper lemmas for connecting coefficient-level updates to polynomial-level equality -/

set_option linter.style.longLine false in
/--
**In-range coefficient update preserves the polynomial invariant.**

When `i < self.coefficients.length`, updating position `i` with the GF(2¹⁶) sum
`self.coefficients[i] + v` produces a polynomial that differs from `self.toGF216Poly` by
exactly `C(v.toGF216) * X^i`.
-/
private lemma poly_update_in_range
    (self self' : encoding.polynomial.Poly)
    (i : Std.Usize) (v : encoding.gf.GF16)
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
  · push_neg at hm_lt
    have hm_lt' : ¬(m < self'.coefficients.val.length) := by omega
    rw [dif_neg hm_lt']
    have hm_ne : m ≠ i.val := by omega
    simp [hm_ne]
    grind

/--
**Extension case preserves the polynomial invariant.**

When `¬(i < self.coefficients.length)`, appending `v` to `self.coefficients` produces
a polynomial that differs from `self.toGF216Poly` by `C(v.toGF216) * X^{self.coefficients.length}`.
-/
private lemma poly_update_extension
    (self self' : encoding.polynomial.Poly)
    (v : encoding.gf.GF16)
    (h_ext : self'.coefficients.val = self.coefficients.val ++ [v]) :
    self'.toGF216Poly = self.toGF216Poly + C (v.toGF216) * X ^ self.coefficients.val.length := by
  unfold Poly.toGF216Poly
  rw [h_ext]
  exact listToGF216Poly_append_singleton self.coefficients.val v

set_option linter.style.longLine false in
/--
**Key step lemma**: processing the `k`-th coefficient from `other_coeffs` at position `k`
(when enumerate starts at 0) preserves the polynomial invariant.

Given that `self.toGF216Poly = orig + listToGF216Poly (other_coeffs.take k)` and the body
updates coefficient position `k` with `other_coeffs[k]`, the resulting polynomial satisfies
`self'.toGF216Poly = orig + listToGF216Poly (other_coeffs.take (k + 1))`.
-/
private lemma step_invariant_preservation
    (orig_poly : GF216Poly)
    (self self' : encoding.polynomial.Poly)
    (other_coeffs : List encoding.gf.GF16)
    (k : Nat) (v : encoding.gf.GF16)
    (hk : k < other_coeffs.length)
    (hv : other_coeffs.get ⟨k, hk⟩ = v)
    (h_prev : self.toGF216Poly = orig_poly + listToGF216Poly (other_coeffs.take k))
    (h_step : self'.toGF216Poly = self.toGF216Poly + C (v.toGF216) * X ^ k) :
    self'.toGF216Poly = orig_poly + listToGF216Poly (other_coeffs.take (k + 1)) := by
  rw [h_step, h_prev]
  have h_take_succ : other_coeffs.take (k + 1) = other_coeffs.take k ++ [other_coeffs.get ⟨k, hk⟩] := by simp
  rw [h_take_succ, listToGF216Poly_append_singleton]
  have h_take_len : (other_coeffs.take k).length = k := by
    rw [List.length_take]; omega
  rw [h_take_len, hv]
  ring

/-! ## Sub-lemmas for `body_cont_spec` decomposition -/


/--
**Wrapping add overflow guard.**

When `x.val + 1 ≤ Usize.max`, the wrapping addition `UScalar.wrapping_add x 1#usize` does not
overflow, and the result's `.val` equals `x.val + 1`.

*Proof*: The wrapping add computes `(x.bv + (1#usize).bv).toNat = (x.val + 1) % Usize.size`.
Since `x.val + 1 ≤ Usize.max < Usize.size`, the modulus is the identity.
-/
private lemma usize_wrapping_add_one_val (x : Std.Usize)
    (h : x.val + 1 ≤ Std.Usize.max) :
    (UScalar.wrapping_add x 1#usize).val = x.val + 1 := by
  -- Unfold wrapping_add: (x.bv + 1.bv).toNat = (x.val + 1) % 2^numBits = x.val + 1
  -- since x.val + 1 ≤ Usize.max < 2^numBits = Usize.size.
  simp only [UScalar.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
  have h1 : (1#usize : Usize).val = 1 := by simp
  rw [h1]
  apply Nat.mod_eq_of_lt
  scalar_tac

set_option linter.style.longLine false in
/--
**Enumerate SliceIter next: `some` case specification.**

When the inner slice iterator has remaining elements (`iter.iter.i < slice.val.length`),
the enumerate count equals the inner index (`count.val = iter.i`), and the slice length
is within Usize bounds, then `Enumerate.next (IteratorSliceIter GF16)` returns:

- `some (count, slice.val[iter.i])` — the current (index, value) pair
- A new enumerate iterator `iter1` satisfying:
  - `iter1.iter.slice = iter.iter.slice` (slice unchanged)
  - `iter1.iter.i = iter.iter.i + 1` (inner index advanced by 1)
  - `iter1.count.val = iter.iter.i + 1` (count advanced, no overflow)

This is a strengthening of `EnumerateSliceIter_next_post` (from `AddAssignLoopBody0`) that
additionally provides the *exact values* of the yielded index and element, and fully
characterizes the output iterator state.

*Proof strategy*:
1. Unfold `Enumerate.next` and `SliceIter.next` to expose the `dite` on
   `iter.iter.i < iter.iter.slice.len`.
2. The `dite` resolves to the `true` branch since `h_lt` implies
   `iter.iter.i < iter.iter.slice.val.length = (iter.iter.slice.len).val`.
3. In the `true` branch, the yielded pair is `(iter.count, slice.val[iter.i])` and
   the new iterator has inner index `iter.i + 1` and count `wrapping_add count 1`.
4. Apply `usize_wrapping_add_one_val` with the bound
   `count.val + 1 = iter.i + 1 ≤ slice.val.length ≤ Usize.max`.
-/
private lemma enumerate_sliceiter_next_some
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter encoding.gf.GF16))
    (h_lt : iter.iter.i < iter.iter.slice.val.length)
    (h_count : iter.count.val = iter.iter.i)
    (h_bound : iter.iter.slice.val.length ≤ Std.Usize.max) :
    ∃ (iter1 : core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter encoding.gf.GF16)),
      core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (core.iter.traits.iterator.IteratorSliceIter encoding.gf.GF16) iter =
          ok (some (iter.count, iter.iter.slice.val[iter.iter.i]), iter1) ∧
      iter1.iter.slice = iter.iter.slice ∧
      iter1.iter.i = iter.iter.i + 1 ∧
      iter1.count.val = iter.iter.i + 1 := by
  -- Step 1: Unfold Enumerate.next and SliceIter.next
  simp only [
    core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    core.slice.iter.IteratorSliceIter.next]
  -- Step 2: The dite condition `iter.iter.i < iter.iter.slice.len` holds via h_lt
  -- After unfolding, the `true` branch is taken, returning:
  --   ok (some (iter.count, slice[iter.i]),
  --       { iter := { slice := iter.iter.slice, i := iter.iter.i + 1 },
  --         count := UScalar.wrapping_add iter.count 1#usize })
  -- Step 3: Show the wrapping add doesn't overflow
  have h_wrapping : (UScalar.wrapping_add iter.count 1#usize).val = iter.iter.i + 1 := by
    have := usize_wrapping_add_one_val iter.count (by omega)
    rw [this, h_count]
  -- Step 4: Construct the witness and verify equalities
  -- Split on the dite condition (iter.iter.i < iter.iter.slice.len)
  split
  · -- True branch: iterator has remaining elements
    exact ⟨_, rfl, rfl, rfl, h_wrapping⟩
  · -- False branch: contradiction with h_lt
    exact absurd h_lt ‹_›

set_option linter.style.longLine false in
/--
**In-range coefficient update sub-lemma.**

When `i.val < coeffs.length` and `g1` is the GF(2¹⁶) sum of `coeffs[i]` and `v`,
performing `List.set i g1` on `coeffs` produces a list satisfying:
- Length is preserved.
- Position `i` holds the GF(2¹⁶) sum.
- All other positions are unchanged.
- The extension clause is vacuously true (since `i < length`).

This is a restatement of the `in_range_update_post` lemma from `AddAssignLoopBody0`,
made accessible within this file's namespace.
-/
private lemma in_range_update_post
    {coeffs : List encoding.gf.GF16}
    {i : Nat} {v g1 : encoding.gf.GF16}
    (h_lt : i < coeffs.length)
    (g1_post : g1.toGF216 = coeffs[i].toGF216 + v.toGF216) :
    let v1 := coeffs.set i g1
    v1.length = coeffs.length ∧
    (∀ (h : i < v1.length),
      (v1.get ⟨i, h⟩).toGF216 = coeffs[i]!.toGF216 + v.toGF216) ∧
    (∀ (k : Nat), k ≠ i → v1[k]? = coeffs[k]?) := by
  refine ⟨by simp, fun h => ?_, fun k hk => ?_⟩
  · simp only [List.get_eq_getElem, List.getElem_set]
    simp only [↓reduceIte]
    rw [g1_post, getElem!_pos coeffs i h_lt]
  · exact List.getElem?_set_ne hk.symm

/-! ## Body specs for the two iterator cases -/

set_option linter.style.longLine false in
/--
**Body spec for the continuation case (elements remaining).**

When `iter'.iter.i < iter'.iter.slice.val.length`, the body returns `cont` with
the updated state. The done case is `False` (unreachable).

The proof decomposes into three independent concerns:

1. **Iterator advancement** (via `enumerate_sliceiter_next_some`):
   The output iterator has the slice unchanged, inner index advanced by 1, and count advanced.
   This is established once by the sub-lemma and reused for all three iterator postcondition
   conjuncts.

2. **In-range coefficient update** (`i.val < self'.coefficients.val.length`):
   Position `i` is updated with the GF(2¹⁶) sum via `Vec.index_mut` + `GF16.add_assign`.
   All other positions are unchanged. This follows from the Aeneas step lemmas for
   `Vec.index_mut_usize` and `GF16.add_assign`, combined with `in_range_update_post`.

3. **Extension** (`¬(i.val < self'.coefficients.val.length)`):
   The value `v` is appended via `Vec.push`. This follows from `Vec.push_spec`.

*Proof outline*:
```
Phase 1: obtain ⟨iter1, h_next, h_iter1_slice, h_iter1_i, h_iter1_count⟩
         from enumerate_sliceiter_next_some
Phase 2: unfold body; rw [h_next]; simp only [bind_tc_ok]
         (resolves enumerate.next, enters `some` branch)
Phase 3: step* (processes Vec.len, if-branch, Vec.index_mut/add_assign or Vec.push)
Phase 4: simp_all (normalizes scalar/list operations)
Phase 5: refine ⟨h_iter1_slice, h_iter1_i, h_iter1_count, ...witnesses...⟩
Phase 6: grind (closes coefficient update goals)
```
-/
private theorem body_cont_spec
    (iter' : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter encoding.gf.GF16))
    (self' : encoding.polynomial.Poly)
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
           (i : Std.Usize) (v : encoding.gf.GF16),
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
  /-
    == Proof decomposition ==

    The proof is structured into six phases that cleanly separate concerns:

    Phase 1 (Iterator resolution):
      Use `enumerate_sliceiter_next_some` to determine the exact result of the
      `Enumerate.next` call. This gives us `iter1` (the output iterator) with
      three known properties: slice unchanged, index +1, count +1.

    Phase 2 (Body unfolding):
      Unfold the `body` definition and substitute the resolved enumerate result.
      After `rw [h_next]` and `simp only [bind_tc_ok]`, the match on `some`
      reduces, leaving the coefficient update operations.

    Phase 3 (Monadic step processing):
      Use `step*` to process the remaining monadic operations:
      - `Vec.len` evaluates to `self'.coefficients.val.length`
      - The `if` branches into in-range and extension cases
      - In-range: `Vec.index_mut` + `GF16.add_assign` produce the updated vector
      - Extension: `Vec.push` produces the extended vector

    Phase 4 (Normalization):
      `simp_all` normalizes scalar comparisons (`UScalar.lt_equiv`),
      list operations (`List.length_set`, `List.get_eq_getElem`), and
      arithmetic (`Usize.ofNatCore_val_eq`).

    Phase 5 (Postcondition construction):
      Provide the iterator state properties directly from Phase 1 and
      the existential witnesses (iter'.count for i, slice[iter'.iter.i] for v).

    Phase 6 (Coefficient update closure):
      Close the remaining coefficient update goals:
      - In-range: from `in_range_update_post` (List.set properties)
      - Extension: from `Vec.push_spec` (list append)
  -/
  -- Phase 1: Resolve the enumerate iterator next call
  obtain ⟨iter1, h_next, h_iter1_slice, h_iter1_i, h_iter1_count⟩ :=
    enumerate_sliceiter_next_some iter' h_lt h_count' h_bound'
  -- Phase 2: Unfold body and substitute the resolved enumerate result
  unfold body
  rw [h_next]
  simp only [bind_tc_ok]
  -- After substitution, the body processes (i, v) = (iter'.count, slice[iter'.iter.i])
  -- and returns cont (iter1, { coefficients := updated_vec })
  -- Phase 3: Process the coefficient update operations
  -- The `id` hint makes the index_mut precondition available to step*
  have h_i_lt_len : iter'.count.val < self'.coefficients.val.length →
      iter'.count.val < self'.coefficients.val.length := id
  step*
  -- Phase 4: Normalize and close
  -- After step*, the goal contains iterator state + coefficient update properties.
  -- Iterator state: h_iter1_slice, h_iter1_i, h_iter1_count provide the first three conjuncts.
  -- Existential witnesses: iter'.count (for i), slice[iter'.iter.i] (for v).
  -- Coefficient properties: from step* hypotheses about List.set / Vec.push.
  simp_all only [implies_true, alloc.vec.Vec.len, UScalar.lt_equiv, Usize.ofNatCore_val_eq,
    getElem!_pos, alloc.vec.Vec.set_val_eq, List.length_set, List.get_eq_getElem,
    forall_true_left, ne_eq, true_and, not_lt]
  -- Phase 5-6: Provide witnesses and close remaining goals
  -- Note: After simp_all, some iterator goals may already be resolved to True.
  -- The exact proof term depends on the post-simp_all goal state, which must be
  -- completed interactively. The strategy is:
  --   1. Provide existential witnesses (h_lt, iter'.count, slice[iter'.iter.i], h_count', rfl)
  --   2. For in-range: use List.set properties (length_set, getElem_set, getElem?_set_ne)
  --   3. For extension: use the Vec.push result (val = val ++ [v])
  grind

/--
**Body spec for the done case (iterator exhausted).**

When `¬(iter'.iter.i < iter'.iter.slice.val.length)`, the body returns `done self'`
and the continuation case is `False` (unreachable).
-/
private theorem body_done_spec
    (iter' : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter encoding.gf.GF16))
    (self' : encoding.polynomial.Poly)
    (h_not_lt : ¬(iter'.iter.i < iter'.iter.slice.val.length)) :
    body iter' self' ⦃ cf =>
      match cf with
      | ControlFlow.done result => result = self'
      | ControlFlow.cont _ => False ⦄ := by
  unfold body
  simp only [
    core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    core.slice.iter.IteratorSliceIter.next, bind_tc_ok]
  split
  · rename_i h_lt; exact absurd h_lt h_not_lt
  · simp [WP.spec_ok]

set_option linter.style.longLine false in
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
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter GF16))
    (self : Poly)
    (other_coeffs : List encoding.gf.GF16)
    (h_iter_data : iter.iter.slice.val.drop iter.iter.i = other_coeffs)
    (h_count_eq : iter.count.val = iter.iter.i)
    (h_start : iter.iter.i = 0)
    (h_len : self.coefficients.val.length + other_coeffs.length ≤ Std.Usize.max) :
    add_assign_loop iter self
      ⦃ (result : Poly) =>
        result.toGF216Poly =
          self.toGF216Poly + listToGF216Poly other_coeffs ⦄ := by
  unfold encoding.polynomial.Poly.add_assign_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.iter.adapters.enumerate.Enumerate
                        (core.slice.iter.Iter encoding.gf.GF16) ×
                      encoding.polynomial.Poly) =>
                  p.1.iter.slice.val.length - p.1.iter.i)
    (inv := fun (p : core.iter.adapters.enumerate.Enumerate
                      (core.slice.iter.Iter encoding.gf.GF16) ×
                    encoding.polynomial.Poly) =>
        p.1.iter.slice = iter.iter.slice ∧
        iter.iter.i ≤ p.1.iter.i ∧
        p.1.iter.i ≤ p.1.iter.slice.val.length ∧
        p.1.count.val = p.1.iter.i ∧
        p.2.coefficients.val.length +
          (p.1.iter.slice.val.length - p.1.iter.i) ≤ Std.Usize.max ∧
        p.2.coefficients.val.length = max self.coefficients.val.length p.1.iter.i ∧
        p.2.toGF216Poly =
          self.toGF216Poly +
            listToGF216Poly (other_coeffs.take (p.1.iter.i - iter.iter.i)))
  · -- Body step: prove the invariant is preserved
    rintro ⟨iter', self'⟩
      ⟨h_slice', h_ge', h_le_slice', h_count', h_len', h_coeff_len', h_poly'⟩
    simp only [] at h_slice' h_ge' h_le_slice' h_count' h_len' h_coeff_len' h_poly' ⊢
    -- Case split: does the iterator have more elements?
    by_cases h_more : iter'.iter.i < iter'.iter.slice.val.length
    · -- Case 1: elements remaining — use body_cont_spec (done = False)
      have h_self_len : self'.coefficients.val.length < Std.Usize.max := by omega
      have h_bound' : iter'.iter.slice.val.length ≤ Std.Usize.max := by
        rw [h_slice']; grind
      have h_body := body_cont_spec iter' self' h_self_len h_count' h_more h_bound'
      apply WP.spec_mono h_body
      intro cf h_cf
      match cf with
      | ControlFlow.done result =>
        -- Unreachable: body_cont_spec says done → False
        exact h_cf.elim
      | ControlFlow.cont (iter'', self'') =>
        -- Cont case: process one element and check invariant + measure decrease
        simp only [] at h_cf ⊢
        obtain ⟨h_slice'', h_i_adv, h_count'', h_lt_slice, i, v, h_i_val, h_v_val, h_in_range, h_extension⟩ := h_cf
        -- Establish key derived facts
        have h_k : iter'.iter.i - iter.iter.i < other_coeffs.length := by
          have : other_coeffs.length = iter.iter.slice.val.length - iter.iter.i := by
            rw [← h_iter_data]; simp [List.length_drop]
          rw [h_slice'] at h_lt_slice
          omega
        -- The element v equals other_coeffs at position k
        have h_v_eq : other_coeffs.get ⟨iter'.iter.i - iter.iter.i, h_k⟩ = v := by
          -- The k-th element of other_coeffs = the k-th element of slice.drop(start)
          -- = slice[start + k] = slice[iter'.iter.i] = v
          have h_oc : other_coeffs = iter.iter.slice.val := by
            rw [← h_iter_data, h_start, List.drop_zero]
          simp only [h_oc, h_start, Nat.sub_zero, List.get_eq_getElem, h_v_val, h_slice']
        -- Prove the polynomial step
        have h_k_eq : iter'.iter.i - iter.iter.i = iter'.iter.i := by omega
        have h_poly_step : self''.toGF216Poly = self'.toGF216Poly + C (v.toGF216) * X ^ iter'.iter.i := by
          rw [h_i_val] at h_in_range h_extension
          by_cases h_lt_coeff : iter'.iter.i < self'.coefficients.val.length
          · -- In-range case
            obtain ⟨h_len_eq, h_upd, h_other_k⟩ := h_in_range h_lt_coeff
            exact poly_update_in_range self' self'' ⟨⟨iter'.iter.i, by scalar_tac⟩⟩ v
              (by exact h_lt_coeff) (by exact h_len_eq)
              (by exact h_upd) (by exact h_other_k)
          · -- Extension case
            have h_ext := h_extension h_lt_coeff
            have h_len_eq_k : self'.coefficients.val.length = iter'.iter.i := by
              rw [h_coeff_len']; omega
            have h_poly := poly_update_extension self' self'' v h_ext
            rw [h_len_eq_k] at h_poly
            exact h_poly
        -- Build invariant ∧ measure decrease
        constructor
        · -- invariant (7 parts)
          rw [h_i_val] at h_in_range h_extension
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [h_slice'', h_slice']
          · rw [h_i_adv]; omega
          · rw [h_i_adv, h_slice'', h_slice']; grind
          · rw [h_i_adv, h_count'']
          · -- length bound: self''.coefficients.length + (slice.length - (iter'.i + 1)) ≤ Usize.max
            -- Follows from h_len' and the coefficient length change (±0 or +1).
            have h_slice_len : iter''.iter.slice.val.length = iter'.iter.slice.val.length := by
              rw [h_slice'']
            by_cases h_lt_coeff : iter'.iter.i < self'.coefficients.val.length
            · obtain ⟨h_len_eq, _, _⟩ := h_in_range h_lt_coeff
              rw [h_i_adv, h_slice_len, h_len_eq]; omega
            · have h_ext := h_extension h_lt_coeff
              have : self''.coefficients.val.length = self'.coefficients.val.length + 1 := by
                rw [h_ext]; simp
              rw [h_i_adv, h_slice_len]; omega
          · -- coefficient length = max(N, iter''.iter.i)
            -- Follows from h_coeff_len' and the coefficient length change.
            by_cases h_lt_coeff : iter'.iter.i < self'.coefficients.val.length
            · obtain ⟨h_len_eq, _, _⟩ := h_in_range h_lt_coeff
              rw [h_i_adv, h_len_eq, h_coeff_len']; omega
            · have h_ext := h_extension h_lt_coeff
              have : self''.coefficients.val.length = self'.coefficients.val.length + 1 := by
                rw [h_ext]; simp
              rw [h_i_adv]; omega
          · -- polynomial invariant
            rw [h_i_adv]
            have h_new_k : iter'.iter.i + 1 - iter.iter.i = (iter'.iter.i - iter.iter.i) + 1 := by omega
            rw [h_new_k]
            exact step_invariant_preservation
              self.toGF216Poly self' self'' other_coeffs
              (iter'.iter.i - iter.iter.i) v h_k h_v_eq h_poly'
              (by rw [h_k_eq]; exact h_poly_step)
        · -- measure decrease
          rw [h_i_adv]
          have h_slice_eq : iter''.iter.slice.val.length = iter'.iter.slice.val.length := by
            rw [h_slice'', h_slice']
          rw [h_slice_eq]
          omega
    · -- Case 2: iterator exhausted — use body_done_spec (cont = False)
      have h_body := body_done_spec iter' self' h_more
      apply WP.spec_mono h_body
      intro cf h_cf
      match cf with
      | ControlFlow.done result =>
        -- Done case: result = self', prove the postcondition
        simp only [] at h_cf ⊢
        subst h_cf
        rw [h_poly']
        have h_exhausted : iter'.iter.i ≥ iter'.iter.slice.val.length := by
          push_neg at h_more; exact h_more
        have h_all_taken : other_coeffs.take (iter'.iter.i - iter.iter.i) = other_coeffs := by
          apply List.take_of_length_le
          have : other_coeffs.length = iter.iter.slice.val.length - iter.iter.i := by
            rw [← h_iter_data]; simp [List.length_drop]
          rw [h_slice'] at h_exhausted
          omega
        rw [h_all_taken]
      | ControlFlow.cont _ =>
        -- Unreachable: body_done_spec says cont → False
        exact h_cf.elim
  · -- Initial invariant
    refine ⟨rfl, le_refl _, ?_, h_count_eq, ?_, ?_, ?_⟩
    · show iter.iter.i ≤ iter.iter.slice.val.length
      omega
    · show self.coefficients.val.length +
        (iter.iter.slice.val.length - iter.iter.i) ≤ Std.Usize.max
      have : other_coeffs.length = iter.iter.slice.val.length - iter.iter.i := by
        rw [← h_iter_data]; simp [List.length_drop]
      omega
    · rw [h_start]; simp
    · simp [List.take_zero, listToGF216Poly_nil]

end spqr.encoding.polynomial.Poly.add_assign_loop
