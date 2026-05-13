/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Specs.Encoding.Gf.GF16.Eq

/-!
# Spec theorem for `spqr::encoding::polynomial::Poly::eq`

After extraction, `eq self other` evaluates to

  `if self.coefficients.length = other.coefficients.length
   then List.allM (fun (a, b) => GF16.eq a b)
                  (List.zip self.coefficients.val other.coefficients.val)
   else ok false`,

so it returns `true` iff the two coefficient vectors have the same length and every pair of
coefficients at corresponding positions is equal in `GF16` (which itself reduces to equality of
the underlying `u16` `value` fields by `encoding.gf.GF16.Insts.CoreCmpPartialEqGF16.eq`).  The
function is total: it never panics and always succeeds.

**Source**: spqr/src/encoding/polynomial.rs (line 77, `#[derive(Clone, PartialEq)]`)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.Poly

private lemma allM_zip_GF16_post
    (xs ys : List spqr.encoding.gf.GF16) (h_len : xs.length = ys.length) :
    ∃ b : Bool,
      List.allM
          (fun (p : spqr.encoding.gf.GF16 × spqr.encoding.gf.GF16) =>
            spqr.encoding.gf.GF16.Insts.CoreCmpPartialEqGF16.eq p.1 p.2)
          (List.zip xs ys) = ok b ∧
      (b = true ↔ xs = ys) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      refine ⟨true, ?_, ?_⟩
      · rfl
      · simp
    | cons y ys =>
      simp at h_len
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp at h_len
    | cons y ys =>
      have h_len' : xs.length = ys.length := by
        simpa [List.length_cons] using h_len
      obtain ⟨b, hb_eq, hb_iff⟩ := ih ys h_len'
      simp only [spqr.encoding.gf.GF16.Insts.CoreCmpPartialEqGF16.eq] at hb_eq
      simp only [List.zip_cons_cons, List.allM,
        spqr.encoding.gf.GF16.Insts.CoreCmpPartialEqGF16.eq, bind_tc_ok]
      by_cases hxy : x.value = y.value
      · -- The head pair is equal; recurse with the IH on the tails.
        simp only [hxy, decide_true, hb_eq]
        refine ⟨b, rfl, ?_⟩
        rw [hb_iff]
        constructor
        · intro h_tails
          have hxe : x = y := (spqr.encoding.gf.GF16.gf16_eq_iff x y).mpr hxy
          rw [hxe, h_tails]
        · intro h_cons
          exact (List.cons.inj h_cons).2
      · -- The head pair differs; the whole result is `false`.
        simp only [decide_eq_false hxy]
        refine ⟨false, rfl, ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        intro h_cons
        have hx_eq : x = y := (List.cons.inj h_cons).1
        exact hxy ((spqr.encoding.gf.GF16.gf16_eq_iff x y).mp hx_eq)

/--
**Spec theorem for `encoding.polynomial.Poly.Insts.CoreCmpPartialEqPoly.eq`**:

• The function always succeeds (no panic / no error) for any pair of `Poly` inputs, because the
  underlying `alloc.vec.partial_eq.PartialEqVec.eq` either short-circuits to `ok false` (when the
  coefficient vectors differ in length) or runs `List.allM` over a list of `GF16` pairs, and each
  elementwise `GF16.eq` is itself total (`ok (a.value = b.value)`).
• The result is `true` if and only if the two coefficient vectors are pointwise equal as lists:
    `eq(a, b) = ok (a.coefficients.val = b.coefficients.val)`.
  Combined with `poly_eq_iff` below, this is equivalent to propositional equality of the wrapping
  `Poly` structs.
• The relation is reflexive, symmetric, and transitive — i.e. it is a total equivalence relation,
  consistent with the `PartialEq` (and structurally derived `Eq`) trait.

**Source**: spqr/src/encoding/polynomial.rs (line 77, `#[derive(Clone, PartialEq)]`)
-/
@[step]
theorem eq_spec (self other : spqr.encoding.polynomial.Poly) :
    Insts.CoreCmpPartialEqPoly.eq self other ⦃ (result : Bool) =>
      result = true ↔ self.coefficients.val = other.coefficients.val ⦄ := by
  simp only [Insts.CoreCmpPartialEqPoly.eq, alloc.vec.partial_eq.PartialEqVec.eq]
  split
  · rename_i h_len
    -- Vec.length is `val.length`, so the length precondition transfers to lists directly.
    have h_len' : self.coefficients.val.length = other.coefficients.val.length := h_len
    obtain ⟨b, hb_eq, hb_iff⟩ :=
      allM_zip_GF16_post self.coefficients.val other.coefficients.val h_len'
    rw [hb_eq]
    simp only [WP.spec_ok]
    exact hb_iff
  · rename_i h_len
    simp only [WP.spec_ok]
    have h_len' : ¬ self.coefficients.val.length = other.coefficients.val.length := h_len
    constructor
    · intro h_eq; cases h_eq
    · intro h_eq
      exact absurd (congrArg List.length h_eq) h_len'

/--
Two `Poly` elements are equal (as structs) if and only if their `coefficients` fields are equal as
`Vec`s, which in turn holds if and only if their underlying `val` lists are equal.  This connects
propositional equality of the wrapper to propositional equality of the coefficient list, and is
the `Poly`-level counterpart of `gf16_eq_iff` for the elementwise field type.
-/
theorem poly_eq_iff (a b : spqr.encoding.polynomial.Poly) :
    a = b ↔ a.coefficients.val = b.coefficients.val := by
  constructor
  · intro h; rw [h]
  · intro h
    cases a
    cases b
    rename_i ca cb
    have : ca = cb := by
      cases ca; cases cb; simp_all
    subst this
    rfl

end spqr.encoding.polynomial.Poly
