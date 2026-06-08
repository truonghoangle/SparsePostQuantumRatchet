/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::encoding::{impl core::fmt::Debug for EncodingError}::fmt`

`EncodingError` is the algebraic sum type

  `EncodingError ≃ PolynomialError  ⊕  {ChunkIndexDecodingError}  ⊕  {ChunkDataDecodingError}`

whose `Debug` instance — derived in Rust via `#[derive(Debug, …)]` — is the *structural*
debug formatter: it dispatches on the constructor and delegates to the standard `core::fmt`
primitives that pretty-print each branch.

The function proceeds in three exhaustive cases, one per constructor of `EncodingError`:
  1. `PolynomialError p` — wrap the payload `p : PolynomialError` in a `Dyn` carrying its own
     `core.fmt.DebugShared` witness, and forward to `core.fmt.Formatter.debug_tuple_field1_finish`
     with the constructor name `"PolynomialError"`.  This realises Rust's
     `f.debug_tuple("PolynomialError").field(p).finish()`.
  2. `ChunkIndexDecodingError` — emit the verbatim constructor name via
     `core.fmt.Formatter.write_str f "ChunkIndexDecodingError"`.
  3. `ChunkDataDecodingError` — emit the verbatim constructor name via
     `core.fmt.Formatter.write_str f "ChunkDataDecodingError"`.

Each branch is a single opaque call into the `core::fmt` formatter machinery; no nontrivial
computation is performed on the payload (it is forwarded verbatim through `Dyn.mk`).

**Source**: spqr/src/encoding.rs (lines 8:9-8:14)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.EncodingError.Insts.CoreFmtDebug

/-- **Spec theorem for `encoding.EncodingError.Insts.CoreFmtDebug.fmt`**:

Structurally faithful debug formatter for `EncodingError`: the function is the canonical
case-analysis over the three constructors of `EncodingError`, dispatching each branch to the
appropriate `core::fmt::Formatter` primitive.

The result satisfies the constructor-level specification (one branch per variant):
  * `PolynomialError p` is sent to
      `core.fmt.Formatter.debug_tuple_field1_finish f "PolynomialError"
        (Dyn.mk _ (core.fmt.DebugShared PolynomialError.Insts.CoreFmtDebug) p)`,
    which is the `core::fmt` realisation of Rust's `debug_tuple("PolynomialError").field(p).finish()`.
  * `ChunkIndexDecodingError` is sent to `core.fmt.Formatter.write_str f "ChunkIndexDecodingError"`.
  * `ChunkDataDecodingError` is sent to `core.fmt.Formatter.write_str f "ChunkDataDecodingError"`.

Concretely, the spec is the definitional equality:

  `fmt self f = match self with
                | PolynomialError p => debug_tuple_field1_finish f "PolynomialError" ⟨p⟩
                | ChunkIndexDecodingError => write_str f "ChunkIndexDecodingError"
                | ChunkDataDecodingError => write_str f "ChunkDataDecodingError"`

This establishes that `fmt` realises — at the level of
`Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)` — the canonical
*structural* debug projection

  `δ : EncodingError → FormatterAction`

induced by the derived `#[derive(Debug)]` instance on the algebraic sum `EncodingError`: each
constructor is mapped to the formatter action that prints its name (and, in the payload-carrying
`PolynomialError` branch, recursively delegates to the inner `PolynomialError` debug instance).

**Source**: spqr/src/encoding.rs (lines 8:9-8:14)
-/
theorem fmt_spec
    (self : encoding.EncodingError) (f : core.fmt.Formatter) :
    encoding.EncodingError.Insts.CoreFmtDebug.fmt self f =
      (match self with
       | encoding.EncodingError.PolynomialError p =>
         core.fmt.Formatter.debug_tuple_field1_finish f (toStr "PolynomialError")
           (Dyn.mk _ (core.fmt.DebugShared
             encoding.polynomial.PolynomialError.Insts.CoreFmtDebug) p)
       | encoding.EncodingError.ChunkIndexDecodingError =>
         core.fmt.Formatter.write_str f (toStr "ChunkIndexDecodingError")
       | encoding.EncodingError.ChunkDataDecodingError =>
         core.fmt.Formatter.write_str f (toStr "ChunkDataDecodingError")) := by
  unfold encoding.EncodingError.Insts.CoreFmtDebug.fmt
  cases self <;> rfl

end spqr.encoding.EncodingError.Insts.CoreFmtDebug

/-!
# Spec theorem for `spqr::encoding::{impl core::fmt::Display for EncodingError}::fmt`

`EncodingError` is the algebraic sum type

  `EncodingError ≃ PolynomialError  ⊕  {ChunkIndexDecodingError}  ⊕  {ChunkDataDecodingError}`

whose `Display` instance — derived in Rust via `#[derive(thiserror::Error)]` together with the
per-variant `#[error("…")]` attributes — is the *user-facing* formatter: it dispatches on the
constructor and, for each branch, renders the message string that was attached to it.

The function proceeds in three exhaustive cases, one per constructor of `EncodingError`:
  1. `PolynomialError p` — interpolate the payload `p : PolynomialError` into the literal template
     `"Polynomial error: {0}"`.  Concretely the extracted code
       (a) lifts `p` through `thiserror`'s `as_display` shim
             (`Shared0T.Insts.ThiserrorDisplayAsDisplayASharedAT.as_display
                 PolynomialError.Insts.CoreFmtDisplay p`),
       (b) wraps the result as a `core.fmt.rt.Argument.new_display` argument,
       (c) packages it together with the constant template (21 raw bytes encoding the literal
           prefix `"Polynomial error: "` followed by the format-arg placeholder) via
           `core.fmt.Arguments.new`, and
       (d) forwards the resulting `Arguments` value to `core.fmt.Formatter.write_fmt`.
     This realises Rust's `write!(f, "Polynomial error: {}", p)`.
  2. `ChunkIndexDecodingError` — emit the verbatim message via
     `core.fmt.Formatter.write_str f "Index decoding error"`.
  3. `ChunkDataDecodingError` — emit the verbatim message via
     `core.fmt.Formatter.write_str f "Data decoding error"`.

Unlike the `Debug` instance (which prints constructor names), the `Display` branches print the
user-facing strings declared by the `#[error(...)]` attributes in `src/encoding.rs`.

**Source**: spqr/src/encoding.rs (lines 8:16-8:32)
-/

namespace spqr.encoding.EncodingError.Insts.CoreFmtDisplay

/-- **Spec theorem for `encoding.EncodingError.Insts.CoreFmtDisplay.fmt`**:

Structurally faithful display formatter for `EncodingError`: the function is the canonical
case-analysis over the three constructors of `EncodingError`, dispatching each branch to the
appropriate `core::fmt::Formatter` primitive with the user-facing message string declared by
the corresponding `#[error("…")]` attribute.

The result satisfies the constructor-level specification (one branch per variant):
  * `PolynomialError p` is sent through the `thiserror`/`core.fmt.rt` argument-packing pipeline
    and finally forwarded to
      `core.fmt.Formatter.write_fmt __formatter args`
    where `args` is the `core.fmt.Arguments` value carrying the literal template
    `"Polynomial error: {0}"` (encoded as the 21-byte sequence
    `[18, 80,111,108,121,110,111,109,105,97,108, 32, 101,114,114,111,114, 58, 32, 192, 0]`)
    together with the single display-argument obtained from `p` via
    `Shared0T.Insts.ThiserrorDisplayAsDisplayASharedAT.as_display` and
    `core.fmt.rt.Argument.new_display`.
  * `ChunkIndexDecodingError` is sent to `core.fmt.Formatter.write_str f "Index decoding error"`.
  * `ChunkDataDecodingError` is sent to `core.fmt.Formatter.write_str f "Data decoding error"`.

Concretely, the spec is the definitional equality:

  `fmt self f = match self with
                | PolynomialError p =>
                    do
                      let d ← Shared0T.Insts.ThiserrorDisplayAsDisplayASharedAT.as_display
                                PolynomialError.Insts.CoreFmtDisplay p
                      let a ← core.fmt.rt.Argument.new_display
                                (Shared0T.Insts.CoreFmtDisplay
                                  PolynomialError.Insts.CoreFmtDisplay) d
                      let args ← core.fmt.Arguments.new
                                   (Array.make 21#usize
                                     [18#u8, 80#u8, 111#u8, 108#u8, 121#u8, 110#u8, 111#u8,
                                      109#u8, 105#u8,  97#u8, 108#u8,  32#u8, 101#u8, 114#u8,
                                      114#u8, 111#u8, 114#u8,  58#u8,  32#u8, 192#u8,   0#u8])
                                   (Array.make 1#usize [a])
                      core.fmt.Formatter.write_fmt f args
                | ChunkIndexDecodingError => write_str f "Index decoding error"
                | ChunkDataDecodingError  => write_str f "Data decoding error"`

This establishes that `fmt` realises — at the level of
`Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)` — the canonical
*user-facing* display projection

  `δ : EncodingError → FormatterAction`

induced by the `thiserror::Error` derivation on the algebraic sum `EncodingError`: each
constructor is mapped to the formatter action that prints the message string declared by its
`#[error(...)]` attribute (and, in the payload-carrying `PolynomialError` branch, recursively
interpolates the inner `PolynomialError` `Display` rendering).

**Source**: spqr/src/encoding.rs (lines 8:16-8:32)
-/
theorem fmt_spec
    (self : encoding.EncodingError) (__formatter : core.fmt.Formatter) :
    encoding.EncodingError.Insts.CoreFmtDisplay.fmt self __formatter =
      (match self with
       | encoding.EncodingError.PolynomialError _0 => do
         let __display0 ←
           Shared0T.Insts.ThiserrorDisplayAsDisplayASharedAT.as_display
             encoding.polynomial.PolynomialError.Insts.CoreFmtDisplay _0
         let a ←
           core.fmt.rt.Argument.new_display (Shared0T.Insts.CoreFmtDisplay
             encoding.polynomial.PolynomialError.Insts.CoreFmtDisplay) __display0
         let a1 ←
           core.fmt.Arguments.new
             (Array.make 21#usize [
               18#u8, 80#u8, 111#u8, 108#u8, 121#u8, 110#u8, 111#u8, 109#u8, 105#u8,
               97#u8, 108#u8, 32#u8, 101#u8, 114#u8, 114#u8, 111#u8, 114#u8, 58#u8,
               32#u8, 192#u8, 0#u8
               ]) (Array.make 1#usize [ a ])
         core.fmt.Formatter.write_fmt __formatter a1
       | encoding.EncodingError.ChunkIndexDecodingError =>
         core.fmt.Formatter.write_str __formatter (toStr "Index decoding error")
       | encoding.EncodingError.ChunkDataDecodingError =>
         core.fmt.Formatter.write_str __formatter (toStr "Data decoding error")) := by
  unfold encoding.EncodingError.Insts.CoreFmtDisplay.fmt
  cases self <;> rfl

end spqr.encoding.EncodingError.Insts.CoreFmtDisplay
