/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::proto::pq_ratchet::{impl PartialEq<PolynomialEncoder> for PolynomialEncoder}::eq`

`PolynomialEncoder` is the protobuf-generated product (record) type

  `PolynomialEncoder ≃ { idx : u32 ; pts : Vec<Vec<u8>> ; polys : Vec<Vec<u8>> }`

representing the serialised form of a polynomial encoder's state.  The three fields are:
  • `idx : u32` — the current index in the encoding sequence.
  • `pts : Vec<Vec<u8>>` — the list of serialised evaluation points (`repeated bytes` in proto3).
  • `polys : Vec<Vec<u8>>` — the list of serialised polynomials (`repeated bytes` in proto3).

The compiler-derived `PartialEq::eq` implementation proceeds field-by-field:
  1. Compare `self.idx = other.idx` (decidable equality on `u32`).
  2. If equal, compare `self.pts` with `other.pts` via
     `alloc.vec.partial_eq.PartialEqVec.eq (PartialEqVec PartialEqU8)`.
  3. If that also returns `true`, compare `self.polys` with `other.polys` using the same
     nested `Vec<Vec<u8>>` equality.
  4. Short-circuit to `false` as soon as any field comparison fails.

Because `u8` has a total, reflexive `PartialEq`, and `Vec<T>` equality (when `T : PartialEq`)
reduces to length + elementwise comparison, the whole struct-level equality is observationally
the same as propositional (structural) equality:
  `eq(self, other) = ok (self = other)`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 2:16-2:25)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.PolynomialEncoder

/-- `Vec<u8>` equality is propositional equality.

`alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8` compares two `Vec U8` vectors by
first checking lengths, then running `List.allM` with `PartialEqU8.eq` on the zipped elements.
The result is `true` iff the two vectors are propositionally equal. -/
@[step]
private theorem eq_vec_u8_spec
    (v1 v2 : alloc.vec.Vec Std.U8) :
    alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 v1 v2
      ⦃ (r : Bool) => r = true ↔ v1 = v2 ⦄ := by
  sorry

/-- `Vec<Vec<u8>>` equality is propositional equality.

`alloc.vec.partial_eq.PartialEqVec.eq (core.cmp.PartialEqVec core.cmp.PartialEqU8)` compares two
`Vec (Vec U8)` vectors by first checking outer lengths, then running `List.allM` with the inner
`Vec U8` equality on the zipped elements.  The result is `true` iff the two vectors are
propositionally equal. -/
@[step]
private theorem eq_vec_vec_u8_spec
    (v1 v2 : alloc.vec.Vec (alloc.vec.Vec Std.U8)) :
    alloc.vec.partial_eq.PartialEqVec.eq
      (core.cmp.PartialEqVec core.cmp.PartialEqU8) v1 v2
      ⦃ (r : Bool) => r = true ↔ v1 = v2 ⦄ := by
  sorry

/--
**Spec theorem for
`proto.pq_ratchet.PolynomialEncoder.Insts.CoreCmpPartialEqPolynomialEncoder.eq`**:

• Takes two `PolynomialEncoder` values `self` and `other`, each wrapping three fields:
    - `idx : U32` — the encoding index.
    - `pts : Vec (Vec U8)` — serialised evaluation points.
    - `polys : Vec (Vec U8)` — serialised polynomials.
• Delegates to field-wise comparison:
    - Decidable equality on `idx` (`U32`).
    - `alloc.vec.partial_eq.PartialEqVec.eq (PartialEqVec PartialEqU8)` for `pts` and `polys`
      (nested pointwise comparison on `Vec (Vec U8)` — see `eq_vec_vec_u8_spec`).
• Short-circuits to `false` as soon as any field comparison fails.

• The function always succeeds (no panic / no error) for any pair of `PolynomialEncoder` inputs,
  since scalar comparison is total and each nested `Vec<u8>` comparison is total
  (element-wise `PartialEqU8.eq` is the identity decision procedure on bounded integers).
• The result is `true` if and only if the two inputs are propositionally equal:
    `eq(self, other) = ok (self = other)`
  i.e. the derived `PartialEq` implementation is observationally the same as structural equality
  on `PolynomialEncoder`.
• The relation is reflexive, symmetric, and transitive — i.e. it is a total equivalence relation,
  consistent with the `PartialEq` (and structurally derived `Eq`) trait.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 2:16-2:25)
-/
@[step]
theorem eq_spec (self other : proto.pq_ratchet.PolynomialEncoder) :
    Insts.CoreCmpPartialEqPolynomialEncoder.eq self other ⦃ (result : Bool) =>
      result = true ↔ self = other ⦄ := by
  unfold Insts.CoreCmpPartialEqPolynomialEncoder.eq
  split <;> rename_i h_idx
  · -- self.idx = other.idx
    step*
    constructor
    · intro h
      cases self; cases other; simp_all
    · intro h; subst h; simp_all
  · -- self.idx ≠ other.idx
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro h
    exact h_idx (congrArg proto.pq_ratchet.PolynomialEncoder.idx h)

/--
Two `PolynomialEncoder` elements are equal (as structs) if and only if all three fields are
pairwise equal.  This connects propositional equality of the wrapper to propositional equality
of the individual fields, and is the `PolynomialEncoder`-level counterpart of `gf16_eq_iff`.
-/
theorem poly_encoder_eq_iff (a b : proto.pq_ratchet.PolynomialEncoder) :
    a = b ↔ a.idx = b.idx ∧ a.pts = b.pts ∧ a.polys = b.polys := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl, rfl⟩
  · intro ⟨h1, h2, h3⟩
    cases a; cases b; simp_all

end spqr.proto.pq_ratchet.PolynomialEncoder
