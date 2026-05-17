/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.GF16.AddAssign

/-!
# Spec theorem for `Poly::add_assign`: loop body 0

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

This file specifies the **loop body** — a single step of the above iteration.  The extracted Lean
function `encoding.polynomial.Poly.add_assign_loop.body` performs one step: it calls `next` on the
`Enumerate<SliceIter<GF16>>` iterator and either:

  1. **Done** (`none`): the iterator is exhausted, and the polynomial `self` is returned unchanged.
  2. **Continue** (`some (i, v)`): processes the pair `(i, v)` where `i` is the coefficient index
     and `v` is the coefficient value from the `other` polynomial:
     - **In-range update** (`i < self.coefficients.len()`): calls `Vec::index_mut` to obtain a
       mutable reference to `self.coefficients[i]`, performs GF(2¹⁶) addition
       `self.coefficients[i] += v` via `GF16.Insts.CoreOpsArithAddAssignGF16.add_assign`, writes
       back the result, and returns `cont (iter', { coefficients := updated_vec })`.
     - **Extension** (`i ≥ self.coefficients.len()`): calls `Vec::push` to append `v` to
       `self.coefficients`, and returns `cont (iter', { coefficients := extended_vec })`.

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
open spqr.encoding.polynomial.Poly
open core.iter.adapters.enumerate core.slice.iter

namespace spqr.encoding.polynomial.Poly.add_assign_loop

-- The long identifier cannot be broken across lines; suppress
-- the line-length linter for the lemma statement and proof.
/--
The enumerate iterator `next` always succeeds and returns either
`none` (iterator exhausted) or `some (index, element)` together
with an advanced iterator.  This is the specification for
`Enumerate.next` applied to a `SliceIter GF16`.

The enumerate adapter wraps the underlying slice iterator and
pairs each yielded element with a zero-based index.  Since the
underlying `SliceIter.next` is a concrete definition that always
returns `ok`, and the enumerate count uses wrapping addition
(which never fails), the composed `Enumerate.next` also always
returns `ok`:

- When the underlying `SliceIter` has remaining elements, `next`
  returns `some (count, element)` and advances both the iterator
  and the counter.
- When the underlying `SliceIter` is exhausted, `next` returns
  `none`.
-/
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


/--
**Auxiliary lemma for the in-range update case of `body_spec`**.

When `i < self.coefficients.length`, performing `List.set` at index `i` with the
GF(2¹⁶) sum `g1` (where `g1.toGF216 = self.coefficients[i].toGF216 + v.toGF216`) yields
a list that satisfies the postcondition: position `i` holds the sum, all other positions
are unchanged, and the extension clause is vacuously true.
-/
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

end spqr.encoding.polynomial.Poly.add_assign_loop
