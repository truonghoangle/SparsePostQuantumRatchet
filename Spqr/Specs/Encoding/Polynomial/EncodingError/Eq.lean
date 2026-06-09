/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolynomialError.Eq

/-!
# Spec theorem for `spqr::encoding::{impl PartialEq<EncodingError> for EncodingError}::eq`

`EncodingError` is the algebraic sum type

  `EncodingError ≃ PolynomialError  ⊕  {ChunkIndexDecodingError}  ⊕  {ChunkDataDecodingError}`

In Rust, `EncodingError` is annotated with `#[derive(Debug, thiserror::Error, Copy, Clone,
PartialEq)]`.  The compiler-derived `PartialEq::eq` implementation realises the *structural*
equality of this sum: two values are equal iff they are built from the same constructor and,
when that constructor carries a payload, the payloads themselves are equal under the inner
`PartialEq` instance.  Since the only payload-carrying variant is `PolynomialError`, whose
payload is itself a finite enumeration `PolynomialError` whose derived `PartialEq` reduces to
discriminant equality, the entire decision procedure is *uniformly* a comparison of (possibly
nested) discriminants.

The function proceeds in two stages:
  1. *Discriminant prefilter* — read the `isize` discriminants of `self` and `other` via
     `read_discriminant`; if they differ, short-circuit to `ok false`.
  2. *Payload comparison* — if the discriminants agree, dispatch on `self`:
       * `PolynomialError p` is matched against `other`'s `PolynomialError q` branch and the
         result is `encoding.polynomial.PolynomialError.Insts.CoreCmpPartialEqPolynomialError.eq
         p q`, which itself reduces to `ok (read_discriminant p = read_discriminant q)` because
         `PolynomialError` has only unit variants.
       * `ChunkIndexDecodingError` and `ChunkDataDecodingError` are unit constructors, so
         agreement of the outer discriminants is sufficient and the result is `ok true`.

The function is total, pure, and never panics; it is the canonical decision procedure for
propositional equality on `EncodingError`, realised at the level of `Result Bool`.

**Source**: spqr/src/encoding.rs (lines 8:47-8:56)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.EncodingError.Insts.CoreCmpPartialEqEncodingError

/-- **Spec theorem for `encoding.EncodingError.Insts.CoreCmpPartialEqEncodingError.eq`**:

Structurally faithful equality on `EncodingError`: the function is the canonical decision
procedure for propositional equality on the three-constructor algebraic sum, and it satisfies
the value-level specification

  `result = true ↔ self = other`.

The proof composes:
  1. *Discriminant prefilter* — `read_discriminant : EncodingError → Isize` is injective on the
     constructors (it maps `PolynomialError`, `ChunkIndexDecodingError`, `ChunkDataDecodingError`
     to three distinct `isize` values), so disagreement of the discriminants is equivalent to
     disagreement of `self` and `other`.
  2. *Payload reduction* on the `PolynomialError` branch — the inner call to
     `encoding.polynomial.PolynomialError.Insts.CoreCmpPartialEqPolynomialError.eq` itself
     reduces to `ok (read_discriminant p = read_discriminant q)` (cf. the extracted body), and
     `read_discriminant` is injective on the three unit constructors of `PolynomialError`, so the
     inner result is `true` iff `p = q` iff `PolynomialError p = PolynomialError q`.

The relation is reflexive, symmetric, and transitive — i.e. it is a total equivalence relation,
consistent with the `PartialEq` (and structurally derived `Eq`) trait.

This establishes that `eq` realises — at the level of `Result Bool` — the canonical structural
equality

  `(·=·) : EncodingError → EncodingError → Prop`

on the algebraic sum `EncodingError`, in agreement with the universal property of
`#[derive(PartialEq)]` on a Rust enum whose payload (when present) is itself `PartialEq`.

**Source**: spqr/src/encoding.rs (lines 8:47-8:56)
-/

@[step]
theorem eq_spec (self other : encoding.EncodingError) :
    eq self other ⦃ (result : Bool) =>
      result = true ↔ self = other ⦄ := by
  rcases self with p | _ | _ <;> rcases other with q | _ | _ <;>
    simp only [eq, read_discriminant,
      polynomial.PolynomialError.Insts.CoreCmpPartialEqPolynomialError.eq,
      polynomial.PolynomialError.read_discriminant, PolynomialError.injEq, ] <;>
    (first | cases p | grind)


end spqr.encoding.EncodingError.Insts.CoreCmpPartialEqEncodingError
