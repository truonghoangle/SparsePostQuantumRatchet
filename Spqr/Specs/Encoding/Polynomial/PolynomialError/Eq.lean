/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::polynomial::{impl PartialEq<PolynomialError> for PolynomialError}::eq`

`PolynomialError` is the three-constructor unit enumeration

  `PolynomialError ≃ {MessageLengthEven}  ⊕  {MessageLengthTooLong}  ⊕  {SerializationInvalid}`

In Rust, `PolynomialError` is annotated with `#[derive(Debug, thiserror::Error, Copy, Clone,
PartialEq)]`.  Because every variant is a *unit* constructor (no payload), the compiler-derived
`PartialEq::eq` implementation collapses to a single comparison of discriminants: two values are
equal iff they are built from the same constructor.  The extracted Lean body reflects this
exactly — it reads the `isize` discriminants of `self` and `other` via `read_discriminant` and
returns `ok (self1 = other1)`.

The function is total, pure, and never panics; it is the canonical decision procedure for
propositional equality on `PolynomialError`, realised at the level of `Result Bool`.

**Source**: spqr/src/encoding/polynomial.rs (lines 12:47-12:56)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.PolynomialError.Insts.CoreCmpPartialEqPolynomialError

/-- **Spec theorem for `encoding.polynomial.PolynomialError.Insts.CoreCmpPartialEqPolynomialError.eq`**:

Structurally faithful equality on `PolynomialError`: the function is the canonical decision
procedure for propositional equality on the three-constructor unit enumeration, and it satisfies
the value-level specification

  `result = true ↔ self = other`.

The proof is a *pure discriminant comparison*: `read_discriminant : PolynomialError → Isize` is
injective on the three unit constructors (it maps `MessageLengthEven`, `MessageLengthTooLong`,
`SerializationInvalid` to three distinct `isize` values), so equality of the discriminants is
equivalent to equality of `self` and `other`.  Since all variants are nullary, no payload
comparison is required — the entire decision procedure reduces to discriminant equality.

The relation is reflexive, symmetric, and transitive — i.e. it is a total equivalence relation,
consistent with the `PartialEq` (and structurally derived `Eq`) trait.

This establishes that `eq` realises — at the level of `Result Bool` — the canonical structural
equality

  `(·=·) : PolynomialError → PolynomialError → Prop`

on the unit enumeration `PolynomialError`, in agreement with the universal property of
`#[derive(PartialEq)]` on a Rust enum whose variants carry no payload.

**Source**: spqr/src/encoding/polynomial.rs (lines 12:47-12:56)
-/
@[step]
theorem eq_spec (self other : encoding.polynomial.PolynomialError) :
    eq self other ⦃ (result : Bool) =>
      result = true ↔ self = other ⦄ := by
  simp only [eq, encoding.polynomial.PolynomialError.read_discriminant, WP.spec_ok]
  cases self <;> cases other <;> grind

end spqr.encoding.polynomial.PolynomialError.Insts.CoreCmpPartialEqPolynomialError
