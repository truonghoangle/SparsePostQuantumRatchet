/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::{impl core::fmt::Debug for spqr::encoding::Chunk}::fmt`

`Chunk` is the product (record) type

  `Chunk ≃ { index : u16 ; data : [u8; 32] }`

whose `Debug` instance — derived in Rust via `#[derive(Debug, …)]` — is the *structural*
debug formatter: it forwards both fields, tagged by their names, to the standard `core::fmt`
primitive that pretty-prints a two-field record.

The function proceeds in three straight-line steps:
  1. Wrap the `index : u16` field in a `Dyn` carrying its `core::fmt::Debug` witness
     (`Dyn.mk _ core.fmt.DebugU16 self.index`), which is the Rust phrase
     `&self.index as &dyn Debug`.
  2. Wrap the `data : [u8; 32]` field in a `Dyn` carrying its `core::fmt::Debug` witness for
     a 32-byte array (`Dyn.mk _ (core.fmt.DebugShared (Array.Insts.CoreFmtDebug 32#usize
     core.fmt.DebugU8)) self.data`), which is the Rust phrase `&self.data as &dyn Debug`.
  3. Forward the two `Dyn` payloads, together with the constructor name `"Chunk"` and the field
     names `"index"` and `"data"`, to `core.fmt.Formatter.debug_struct_field2_finish`.
     This realises Rust's `f.debug_struct("Chunk").field("index", &self.index)
     .field("data", &self.data).finish()`.

The function performs no nontrivial computation on either field: the two payloads are
forwarded verbatim through `Dyn.mk` into a single opaque call into the `core::fmt` formatter
machinery.

**Source**: spqr/src/encoding.rs (lines 24:9-24:14)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.Chunk.Insts.CoreFmtDebug

/-- **Spec theorem for `encoding.Chunk.Insts.CoreFmtDebug.fmt`**:

Structurally faithful debug formatter for `Chunk`: the function is the canonical
two-field-record projection that wraps each field in a `Dyn` carrying the corresponding
`core::fmt::Debug` witness and forwards them, tagged by the field names, to the
`core::fmt::Formatter` two-field record primitive.

The result satisfies the field-level specification:

  * The `index : u16` field is sent through `Dyn.mk _ core.fmt.DebugU16` (the `core::fmt::Debug`
    instance for `u16`).
  * The `data : [u8; 32]` field is sent through
    `Dyn.mk _ (core.fmt.DebugShared (Array.Insts.CoreFmtDebug 32#usize core.fmt.DebugU8))`
    (the `core::fmt::Debug` instance for `[u8; 32]`, derived elementwise from the `u8`
    instance).
  * Both `Dyn` payloads, together with the constructor name `"Chunk"` and the field names
    `"index"` and `"data"`, are forwarded to
    `core.fmt.Formatter.debug_struct_field2_finish`, which is the `core::fmt` realisation of
    Rust's `debug_struct("Chunk").field("index", &self.index).field("data", &self.data).finish()`.

Concretely, the spec is the definitional equality:

  `fmt self f =
     core.fmt.Formatter.debug_struct_field2_finish f "Chunk"
       "index" ⟨self.index⟩  "data" ⟨self.data⟩`

This establishes that `fmt` realises — at the level of
`Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)` — the canonical
*structural* debug projection

  `δ : Chunk → FormatterAction`

induced by the derived `#[derive(Debug)]` instance on the product `Chunk`: the record is
mapped to the formatter action that prints its constructor name and recursively delegates
each labelled field to its own `Debug` instance.

**Source**: spqr/src/encoding.rs (lines 24:9-24:14)
-/
theorem fmt_spec
    (self : encoding.Chunk) (f : core.fmt.Formatter) :
    encoding.Chunk.Insts.CoreFmtDebug.fmt self f =
      core.fmt.Formatter.debug_struct_field2_finish f (toStr "Chunk")
        (toStr "index") (Dyn.mk _ core.fmt.DebugU16 self.index)
        (toStr "data")
        (Dyn.mk _
          (core.fmt.DebugShared
            (Array.Insts.CoreFmtDebug 32#usize core.fmt.DebugU8))
          self.data) := by
  unfold encoding.Chunk.Insts.CoreFmtDebug.fmt
  rfl

end spqr.encoding.Chunk.Insts.CoreFmtDebug
