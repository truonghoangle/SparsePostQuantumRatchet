/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
/-! # Spec theorem for `spqr::encoding::gf::GF16::eq`

Specification and proof for `encoding.gf.GF16.Insts.CoreCmpPartialEqGF16.eq`,
which implements `PartialEq<GF16> for GF16` via the derived `#[derive(Eq, PartialEq)]`
attribute.

**Source**: spqr/src/encoding/gf.rs (line 9, `#[derive(Eq, PartialEq)]`)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.gf.GF16

/-- **Spec theorem for `encoding.gf.GF16.Insts.CoreCmpPartialEqGF16.eq`**:

• The function always succeeds (no panic / no error) for any pair of
  GF16 inputs.
• The result is `true` if and only if `self.value = other.value`:
    `eq(a, b) = ok (a.value = b.value)`
• The relation is reflexive, symmetric, and transitive — i.e. it is
  a total equivalence relation, consistent with the `Eq` trait.

**Source**: spqr/src/encoding/gf.rs (line 9, `#[derive(Eq, PartialEq)]`)
-/
@[step]
theorem eq_spec (self other : spqr.encoding.gf.GF16) :
    Insts.CoreCmpPartialEqGF16.eq self other ⦃ (result : Bool) =>
      result = true ↔ (self.value = other.value) ⦄ := by
  simp [Insts.CoreCmpPartialEqGF16.eq]

/-- Two `GF16` elements are equal (as structs) if and only if their
`value` fields are equal.  This connects propositional equality of the
wrapper to propositional equality of the representation. -/
theorem gf16_eq_iff (a b : spqr.encoding.gf.GF16) :
    a = b ↔ a.value = b.value := by
  constructor
  · intro h; rw [h]
  · intro h
    cases a
    cases b
    simp only at h
    subst h
    rfl

end spqr.encoding.gf.GF16
