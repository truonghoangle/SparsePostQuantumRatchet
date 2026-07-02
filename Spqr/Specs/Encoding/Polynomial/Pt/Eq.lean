/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec Theorem for `Pt::eq` (PartialEq / Eq)

Specification and proof for `encoding.polynomial.Pt.Insts.CoreCmpPartialEqPt.eq`, which implements
`PartialEq<Pt> for Pt` via a custom implementation that compares only the x-coordinates.

Unlike a derived `PartialEq`, this implementation intentionally ignores the y-coordinate:
  `eq(a, b) = (a.x.value == b.x.value)`
Two points with the same x-coordinate but different y-coordinates are therefore considered equal
under this relation.  This is consistent with the `PartialOrd` and `Ord` implementations, which
also compare only x-coordinates.

**Source**: spqr/src/encoding/polynomial.rs (lines 60:0-64:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.Pt

/--
**Spec theorem for `encoding.polynomial.Pt.Insts.CoreCmpPartialEqPt.eq`**:

• The function always succeeds (no panic / no error) for any pair of `Pt` inputs.
• The result is `true` if and only if `self.x.value = other.x.value`:
    `eq(a, b) = ok (a.x.value = b.x.value)`
• Only the x-coordinate participates in the comparison; the y-coordinate is ignored.
• The relation is reflexive, symmetric, and transitive — i.e. it is a total equivalence relation
  on x-coordinates, consistent with the `Eq` trait.

**Source**: spqr/src/encoding/polynomial.rs (lines 61:4-63:5)
-/
@[step]
theorem eq_spec (self other : spqr.encoding.polynomial.Pt) :
    Insts.CoreCmpPartialEqPt.eq self other ⦃ (result : Bool) =>
      result = true ↔ (self.x.value = other.x.value) ⦄ := by
  simp [Insts.CoreCmpPartialEqPt.eq]

/--
Two `Pt` elements are equal (as structs) if and only if both their `x` and `y` fields are equal.
This connects propositional equality of the wrapper to propositional equality of the components.

Note that structural equality is strictly finer than the `PartialEq` relation, which only compares
x-coordinates.
-/
theorem pt_eq_iff (a b : spqr.encoding.polynomial.Pt) :
    a = b ↔ a.x = b.x ∧ a.y = b.y := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · intro ⟨hx, hy⟩
    cases a
    cases b
    simp only at hx hy
    subst hx
    subst hy
    rfl

end spqr.encoding.polynomial.Pt
