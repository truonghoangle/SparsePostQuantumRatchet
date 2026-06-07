/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::{impl core::clone::Clone for spqr::encoding::Chunk}::clone`

`Chunk` is the product (record) type

  `Chunk ≃ { index : u16 ; data : [u8; 32] }`

In Rust, `Chunk` is annotated with `#[derive(Debug, Clone, Copy)]`.  Because the type is declared
`Copy`, the compiler-derived `Clone::clone` implementation is the *trivial* (bit-for-bit)
identity: cloning a value of a `Copy` type is equivalent to returning the value itself, with no
recursive descent into either of the two fields `index : u16` and `data : [u8; 32]`.

The function proceeds in a single, field-agnostic stage:
  1. `ok self` — return the input verbatim, lifted into the `Result` monad of the Aeneas
     extraction.  No projection of the two fields of `Chunk` is performed; the `Copy` semantics
     is realised at the meta-level by direct propagation of the argument.

**Source**: spqr/src/encoding.rs (lines 24:16-24:21)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.Chunk.Insts.CoreCloneClone

/-- **Spec theorem for `encoding.Chunk.Insts.CoreCloneClone.clone`**:

The derived `Clone` implementation on `Chunk` is observationally the identity: for every
`self : Chunk`, the call `clone self` succeeds and returns `self` unchanged.

The result satisfies the value-level specification:
  `clone self = ok self`

This follows immediately from the body of the extracted definition, which is literally `ok self`
(no field projection, no recursive cloning of `index` or `data`) — a direct consequence of the
`#[derive(Copy, Clone)]` attribute on `Chunk`, under which the compiler emits the trivial clone
whose denotation is the categorical identity on the underlying type.

This establishes that `clone` realises — at the level of `Result Chunk` — the identity
endomorphism

  `id : Chunk → Chunk`

on the product `Chunk`, in agreement with the universal property of `Copy` types in Rust's
trait system: cloning is a no-op, indistinguishable from the original value.

**Source**: spqr/src/encoding.rs (lines 24:16-24:21)
-/
@[step]
theorem clone_spec (self : encoding.Chunk) :
    clone self ⦃ (result : encoding.Chunk) =>
      result = self ⦄ := by
  unfold clone
  step*

end spqr.encoding.Chunk.Insts.CoreCloneClone
