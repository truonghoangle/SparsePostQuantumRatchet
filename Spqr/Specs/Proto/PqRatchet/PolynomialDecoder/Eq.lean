/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::proto::pq_ratchet::{impl PartialEq<PolynomialDecoder> for PolynomialDecoder}::eq`

`PolynomialDecoder` is the protobuf-generated product (record) type

  `PolynomialDecoder ≃ { pts_needed : u32 ; polys : u32 ; pts : Vec<Vec<u8>> ; is_complete : bool }`

representing the serialised form of a polynomial decoder's state.  The four fields are:
  • `pts_needed : u32` — the number of evaluation points still needed before decoding can complete.
  • `polys : u32` — the number of polynomials accumulated so far.
  • `pts : Vec<Vec<u8>>` — the list of serialised evaluation points (`repeated bytes` in proto3).
  • `is_complete : bool` — whether enough points have been received for decoding.

The protobuf schema (src/proto/pq_ratchet.proto, lines 18–23):
  ```proto
  message PolynomialDecoder {
    uint32 pts_needed = 1;
    uint32 polys = 2;
    repeated bytes pts = 3;
    bool is_complete = 4;
  }
  ```

The prost-generated Rust struct carries a `#[derive(PartialEq)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(PartialEq)]
  impl PartialEq for PolynomialDecoder {
      fn eq(&self, other: &Self) -> bool {
          self.pts_needed == other.pts_needed
              && self.polys == other.polys
              && self.is_complete == other.is_complete
              && self.pts == other.pts
      }
  }
  ```

The compiler-derived `PartialEq::eq` implementation proceeds field-by-field:
  1. Compare `self.pts_needed = other.pts_needed` (decidable equality on `u32`).
  2. If equal, compare `self.polys = other.polys` (decidable equality on `u32`).
  3. If equal, compare `self.is_complete = other.is_complete` (decidable equality on `bool`).
  4. If all three scalar fields match, compare `self.pts` with `other.pts` via
     `alloc.vec.partial_eq.PartialEqVec.eq (PartialEqVec PartialEqU8)`.
  5. Short-circuit to `false` as soon as any field comparison fails.

Because `u8` has a total, reflexive `PartialEq`, and `Vec<T>` equality (when `T : PartialEq`)
reduces to length + elementwise comparison, the whole struct-level equality is observationally
the same as propositional (structural) equality:
  `eq(self, other) = ok (self = other)`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 14:16-14:25)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.PolynomialDecoder

/-- Helper: `List.allM` with `PartialEqU8.eq` on zipped `U8` lists preserves
propositional equality.  Given equal-length lists `xs` and `ys`, the list-level
`allM` returns `ok b` with `b = true ↔ xs = ys`. -/
private lemma allM_zip_u8_post
    (xs ys : List Std.U8) (h_len : xs.length = ys.length) :
    ∃ b : Bool,
      List.allM (fun (p : Std.U8 × Std.U8) =>
        core.cmp.PartialEqU8.eq p.1 p.2) (List.zip xs ys) = ok b ∧
      (b = true ↔ xs = ys) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨true, rfl, by simp⟩
    | cons _ _ => simp at h_len
  | cons x xs ih =>
    cases ys with
    | nil => simp at h_len
    | cons y ys =>
      have h_len' : xs.length = ys.length := by
        simpa [List.length_cons] using h_len
      obtain ⟨b_tail, hb_tail_eq, hb_tail_iff⟩ := ih ys h_len'
      -- core.cmp.PartialEqU8.eq p.1 p.2 is definitionally ok (decide (p.1 = p.2))
      -- via @[reducible] PartialEqU8 + @[simp] liftFun2
      change ∃ b, List.allM _ ((x, y) :: List.zip xs ys) = ok b ∧ _
      simp only [List.allM, liftFun2, bind_tc_ok, core.cmp.impls.PartialEqU8.eq]
      by_cases hxy : x = y
      · -- Head pair equal
        subst hxy
        simp only
        exact ⟨b_tail, hb_tail_eq, by
          rw [hb_tail_iff]
          constructor
          · intro h; rw [h]
          · intro h; exact (List.cons.inj h).2⟩
      · -- Head pair differs
        simp only [decide_eq_false hxy]
        exact ⟨false, rfl, by
          simp only [Bool.false_eq_true, false_iff]
          intro h; exact hxy (List.cons.inj h).1⟩

/-- `Vec<u8>` equality is propositional equality.

`alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8` compares two `Vec U8` vectors by
first checking lengths, then running `List.allM` with `PartialEqU8.eq` on the zipped elements.
The result is `true` iff the two vectors are propositionally equal. -/
@[step]
private theorem eq_vec_u8_spec
    (v1 v2 : alloc.vec.Vec Std.U8) :
    alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 v1 v2
      ⦃ (r : Bool) => r = true ↔ v1 = v2 ⦄ := by
  simp only [alloc.vec.partial_eq.PartialEqVec.eq]
  split
  · -- v1.length = v2.length
    rename_i h_len
    obtain ⟨b, hb_eq, hb_iff⟩ := allM_zip_u8_post v1.val v2.val h_len
    apply WP.exists_imp_spec
    exact ⟨b, hb_eq, by
      rw [hb_iff]
      constructor
      · intro h; cases v1; cases v2; simp_all
      · intro h; subst h; rfl⟩
  · -- v1.length ≠ v2.length
    rename_i h_len
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro h; subst h; exact h_len rfl

/-- Helper: `List.allM` with a propositional inner equality on zipped lists preserves
propositional equality.  Given `eq_fn` that decides equality for elements of type `T`
(returning `ok b` with `b = true ↔ x = y`), the list-level `allM` over `zip xs ys`
returns `ok b` with `b = true ↔ xs = ys`, provided the lists have the same length. -/
private lemma allM_zip_vec_u8_post
    (eq_fn : alloc.vec.Vec Std.U8 → alloc.vec.Vec Std.U8 → Result Bool)
    (eq_fn_spec : ∀ x y, eq_fn x y ⦃ (r : Bool) => r = true ↔ x = y ⦄)
    (xs ys : List (alloc.vec.Vec Std.U8)) (h_len : xs.length = ys.length) :
    ∃ b : Bool,
      List.allM (fun (p : alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8) =>
        eq_fn p.1 p.2) (List.zip xs ys) = ok b ∧
      (b = true ↔ xs = ys) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨true, rfl, by simp⟩
    | cons _ _ => simp at h_len
  | cons x xs ih =>
    cases ys with
    | nil => simp at h_len
    | cons y ys =>
      have h_len' : xs.length = ys.length := by
        simpa [List.length_cons] using h_len
      obtain ⟨b_tail, hb_tail_eq, hb_tail_iff⟩ := ih ys h_len'
      obtain ⟨b_head, hb_head_eq, hb_head_iff⟩ :=
        WP.spec_imp_exists (eq_fn_spec x y)
      simp only [List.zip_cons_cons, List.allM, hb_head_eq, bind_tc_ok]
      by_cases hxy : x = y
      · -- Head pair equal: b_head = true, recurse on tails.
        subst hxy
        have hbt : b_head = true := hb_head_iff.mpr rfl
        subst hbt
        exact ⟨b_tail, hb_tail_eq, by
          rw [hb_tail_iff]
          constructor
          · intro h; rw [h]
          · intro h; exact (List.cons.inj h).2⟩
      · -- Head pair differs: b_head = false, short-circuit.
        have hbf : b_head = false := by
          cases b_head with
          | false => rfl
          | true => exact absurd (hb_head_iff.mp rfl) hxy
        subst hbf
        exact ⟨false, rfl, by
          simp only [Bool.false_eq_true, false_iff]
          intro h; exact hxy (List.cons.inj h).1⟩

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
  simp only [alloc.vec.partial_eq.PartialEqVec.eq]
  split
  · -- v1.length = v2.length
    rename_i h_len
    obtain ⟨b, hb_eq, hb_iff⟩ := allM_zip_vec_u8_post
      ((core.cmp.PartialEqVec core.cmp.PartialEqU8).eq)
      eq_vec_u8_spec v1.val v2.val h_len
    apply WP.exists_imp_spec
    exact ⟨b, hb_eq, by
      rw [hb_iff]
      constructor
      · intro h; cases v1; cases v2; simp_all
      · intro h; subst h; rfl⟩
  · -- v1.length ≠ v2.length
    rename_i h_len
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro h; subst h; exact h_len rfl

/--
**Spec theorem for
`proto.pq_ratchet.PolynomialDecoder.Insts.CoreCmpPartialEqPolynomialDecoder.eq`**:

• Takes two `PolynomialDecoder` values `self` and `other`, each wrapping four fields:
    - `pts_needed : U32` — the number of evaluation points still needed.
    - `polys : U32` — the number of accumulated polynomials.
    - `pts : Vec (Vec U8)` — serialised evaluation points.
    - `is_complete : Bool` — whether decoding is complete.
• Delegates to field-wise comparison:
    - Decidable equality on `pts_needed` (`U32`).
    - Decidable equality on `polys` (`U32`).
    - Decidable equality on `is_complete` (`Bool`).
    - `alloc.vec.partial_eq.PartialEqVec.eq (PartialEqVec PartialEqU8)` for `pts`
      (nested pointwise comparison on `Vec (Vec U8)` — see `eq_vec_vec_u8_spec`).
• Short-circuits to `false` as soon as any field comparison fails.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 356–375):
  ```lean
  def proto.pq_ratchet.PolynomialDecoder.Insts.CoreCmpPartialEqPolynomialDecoder.eq
    (self : proto.pq_ratchet.PolynomialDecoder)
    (other : proto.pq_ratchet.PolynomialDecoder) :
    Result Bool
    := do
    if self.pts_needed = other.pts_needed
    then
      if self.polys = other.polys
      then
        if self.is_complete = other.is_complete
        then
          alloc.vec.partial_eq.PartialEqVec.eq (core.cmp.PartialEqVec
            core.cmp.PartialEqU8) self.pts other.pts
        else ok false
      else ok false
    else ok false
  ```

• The function always succeeds (no panic / no error) for any pair of `PolynomialDecoder` inputs,
  since scalar comparison is total and each nested `Vec<u8>` comparison is total
  (element-wise `PartialEqU8.eq` is the identity decision procedure on bounded integers).
• The result is `true` if and only if the two inputs are propositionally equal:
    `eq(self, other) = ok (self = other)`
  i.e. the derived `PartialEq` implementation is observationally the same as structural equality
  on `PolynomialDecoder`.
• The relation is reflexive, symmetric, and transitive — i.e. it is a total equivalence relation,
  consistent with the `PartialEq` (and structurally derived `Eq`) trait.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 14:16-14:25)
-/
@[step]
theorem eq_spec (self other : proto.pq_ratchet.PolynomialDecoder) :
    Insts.CoreCmpPartialEqPolynomialDecoder.eq self other ⦃ (result : Bool) =>
      result = true ↔ self = other ⦄ := by
  unfold Insts.CoreCmpPartialEqPolynomialDecoder.eq
  split <;> rename_i h_pts_needed
  · -- self.pts_needed = other.pts_needed
    split <;> rename_i h_polys
    · -- self.polys = other.polys
      split <;> rename_i h_is_complete
      · -- self.is_complete = other.is_complete
        step*
        constructor
        · intro h
          cases self; cases other; simp_all
        · intro h; subst h; simp_all
      · -- self.is_complete ≠ other.is_complete
        simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
        intro h
        exact h_is_complete (congrArg proto.pq_ratchet.PolynomialDecoder.is_complete h)
    · -- self.polys ≠ other.polys
      simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
      intro h
      exact h_polys (congrArg proto.pq_ratchet.PolynomialDecoder.polys h)
  · -- self.pts_needed ≠ other.pts_needed
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro h
    exact h_pts_needed (congrArg proto.pq_ratchet.PolynomialDecoder.pts_needed h)

/--
Two `PolynomialDecoder` elements are equal (as structs) if and only if all four fields are
pairwise equal.  This connects propositional equality of the wrapper to propositional equality
of the individual fields, and is the `PolynomialDecoder`-level counterpart of
`poly_encoder_eq_iff`.
-/
theorem poly_decoder_eq_iff (a b : proto.pq_ratchet.PolynomialDecoder) :
    a = b ↔ a.pts_needed = b.pts_needed ∧ a.polys = b.polys
            ∧ a.pts = b.pts ∧ a.is_complete = b.is_complete := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl, rfl, rfl⟩
  · intro ⟨h1, h2, h3, h4⟩
    cases a; cases b; simp_all

end spqr.proto.pq_ratchet.PolynomialDecoder
