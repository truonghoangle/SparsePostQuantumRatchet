/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::{impl core::clone::Clone for EncodingError}::clone`

`EncodingError` is the algebraic sum type

  `EncodingError ≃ PolynomialError  ⊕  {ChunkIndexDecodingError}  ⊕  {ChunkDataDecodingError}`

In Rust, `EncodingError` is annotated with `#[derive(Debug, thiserror::Error, Copy, Clone,
PartialEq)]`.  Because the type is declared `Copy`, the compiler-derived `Clone::clone`
implementation is the *trivial* (bit-for-bit) identity: cloning a value of a `Copy` type is
equivalent to returning the value itself, with no recursive descent into the payload of the
`PolynomialError` constructor.

The function proceeds in a single, constructor-agnostic stage:
  1. `ok self` — return the input verbatim, lifted into the `Result` monad of the Aeneas
     extraction.  No case-analysis on the three constructors of `EncodingError` is performed;
     the `Copy` semantics is realised at the meta-level by direct propagation of the argument.

**Source**: spqr/src/encoding.rs (lines 8:40-8:45)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.EncodingError.Insts.CoreCloneClone

/-- **Spec theorem for `encoding.EncodingError.Insts.CoreCloneClone.clone`**:

The derived `Clone` implementation on `EncodingError` is observationally the identity: for every
`self : EncodingError`, the call `clone self` succeeds and returns `self` unchanged.

The result satisfies the value-level specification:
  `clone self = ok self`

This follows immediately from the body of the extracted definition, which is literally `ok self`
(no constructor dispatch, no payload traversal) — a direct consequence of the `#[derive(Copy,
Clone)]` attribute on `EncodingError`, under which the compiler emits the trivial clone whose
denotation is the categorical identity on the underlying type.

This establishes that `clone` realises — at the level of `Result EncodingError` — the identity
endomorphism

  `id : EncodingError → EncodingError`

on the algebraic sum `EncodingError`, in agreement with the universal property of `Copy` types in
Rust's trait system: cloning is a no-op, indistinguishable from the original value.

**Source**: spqr/src/encoding.rs (lines 8:40-8:45)
-/
@[step]
theorem clone_spec (self : encoding.EncodingError) :
    clone self ⦃ (result : encoding.EncodingError) =>
      result = self ⦄ := by
  unfold clone
  step*

end spqr.encoding.EncodingError.Insts.CoreCloneClone
