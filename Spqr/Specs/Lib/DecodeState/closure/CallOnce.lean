/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `decode_state::closure::call_once`

The `decode_state` function (in `src/lib.rs`, lines 472–482) deserializes a `SerializedState`
(`Vec<u8>`) into a `PqRatchetState` protobuf message.  When the input is non-empty, it delegates to
`PqRatchetState::decode(s.as_slice())` and maps any decode error via `.map_err(|_| Error::StateDecode)`
(line 480).

The closure `|_| Error::StateDecode` passed to `map_err` ignores its `DecodeError` argument and
unconditionally returns `Error::StateDecode`.  This is the standard error-mapping pattern used
throughout the codebase to convert library-specific errors into the unified `spqr::Error` type.

The closure captures no environment — Aeneas extracts the closure state type as
`decode_state.closure := Unit` — so the closure state is always `()`.

The closure is extracted by Aeneas as a `FnOnce` trait implementation
`decode_state.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorError`
whose `call_once` method takes:
  - a closure state `c : decode_state.closure` (i.e. `Unit`, since the closure captures nothing),
  - a `tupled_args : prost.error.DecodeError` argument (the decode error, which is ignored),

and returns `Result Error` — always `ok Error.StateDecode`.

Since the closure body is a single constant expression with no branching or fallible operations,
`call_once` always succeeds and the result is exactly `Error.StateDecode`.

**Source**: spqr/src/lib.rs (lines 480:72-480:94)
-/

open Aeneas Aeneas.Std Result

-- Long namespace names are unavoidable for Aeneas-extracted closures.
set_option linter.style.longLine false

namespace spqr.decode_state.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorError

/--
**Spec theorem for `decode_state.closure.call_once`**:

• Takes a closure state `c : decode_state.closure` (which is `Unit`, since the closure captures
  nothing) and a `tupled_args : prost.error.DecodeError` (the protobuf decode error, which is
  discarded).
• Ignores both arguments and unconditionally returns `ok Error.StateDecode`.

• The function always succeeds (no panic, no fallible operation) for any inputs.

The result satisfies the postcondition:

  `result = Error.StateDecode`

i.e. the closure is a constant function mapping every `DecodeError` to `Error.StateDecode`.

The proof unfolds `call_once` and discharges the resulting goal with `step*`.

**Source**: spqr/src/lib.rs (lines 480:72-480:94)
-/
@[step]
theorem call_once_spec
    (c : decode_state.closure)
    (tupled_args : prost.error.DecodeError) :
    call_once c tupled_args  ⦃ (result : Error) =>
      result = Error.StateDecode ⦄ := by
  unfold call_once
  step*

end spqr.decode_state.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorError
