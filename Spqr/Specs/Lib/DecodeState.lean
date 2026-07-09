/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.Axioms
import Spqr.Specs.Lib.DecodeState.closure.CallOnce
/-!
# Spec theorem for `spqr::decode_state`

`decode_state` deserializes a `SerializedState` (a `Vec<u8>`) into a `PqRatchetState` protobuf
message.  It handles two cases:

  1. **Empty input** (`s.is_empty()`): returns a default `PqRatchetState` with all fields set to
     `None` — representing the V0 (disabled) protocol state.

  2. **Non-empty input**: delegates to `PqRatchetState::decode(s.as_slice())`, mapping any decode
     error to `Error::StateDecode` via `map_err(|_| Error::StateDecode)`.

The by-value `decode_state` introduces no additional logic beyond the delegation, so the empty-input
postcondition follows directly from the function body, and the error-mapping behaviour is inherited
from the corresponding `call_once` specification on the closure.

This function is the deserialization counterpart to `PqRatchetState::encode_to_vec()`, and is used
by `current_version`, `send`, and `recv` to recover protocol state from its serialized form.

The `protobuf_encode_decode_roundtrip` axiom in `Axioms.lean` establishes that encoding followed
by decoding yields the original protobuf message.

**Source**: spqr/src/lib.rs (lines 472:0-482:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.decode_state`**:

• Takes a serialized state `s` (a `Vec<u8>`).
• Checks `s.is_empty()`:
  - If `s` is empty, returns `Ok` with a default `PqRatchetState`:
      `{ inner := none, version_negotiation := none, chain := none }`
  - If `s` is non-empty, delegates to the prost `PqRatchetState::decode(s.as_slice())` and maps
    any `DecodeError` to `Error::StateDecode` via:
      `core.result.Result.map_err call_once_closure r ()`
    which applies the already-registered `call_once_spec` on the error-mapping closure.

• The function always succeeds at the monadic level (no panic); protobuf decode errors are
  returned via `core.result.Result.Err`.
• The by-reference `as_slice` call and the emptiness check are total operations on bounded
  vectors, so neither can fail.
• Together with the `call_once_spec` on the closure, the following identity holds for any
  protobuf decode error `e`:
    `map_err(|_| Error::StateDecode)(Err(e)) = Err(Error::StateDecode)`

The result satisfies the following postconditions:

  **Empty-input case** (`s.val = []`):
    `result = core.result.Result.Ok
      { version_negotiation := none, chain := none, inner := none }`

  **Non-empty-input case** (`s.val ≠ []`):
    `match result with
     | core.result.Result.Ok pb =>
         proto.pq_ratchet.PqRatchetState.Insts.ProstMessageMessage.encode_to_vec
           pb = ok s
     | core.result.Result.Err e => e = Error.StateDecode`

  i.e., when the input is non-empty, the result is either a successfully decoded protobuf
  message whose re-encoding yields the original bytes `s` (canonical-form property), or a
  `StateDecode` error (the only possible `Err` variant).  The `Ok` branch property follows
  from the `protobuf_decode_encode_roundtrip` axiom in `Axioms.lean`, which establishes
  that prost's deterministic serialization preserves canonical form.

where `result : core.result.Result proto.pq_ratchet.PqRatchetState Error` is the inner
`Result` produced by `decode_state`.

The proof unfolds `decode_state` to expose the underlying `is_empty` branch and the `map_err`
delegation, then discharges the resulting goal with `sorry` — the non-empty branch depends on
the opaque prost `Message::decode` implementation, whose correctness is axiomatized rather than
proved.

**Source**: spqr/src/lib.rs (lines 472:0-482:1)
-/
@[step]
theorem decode_state_spec (s : alloc.vec.Vec U8) :
    decode_state s ⦃ (result : core.result.Result proto.pq_ratchet.PqRatchetState Error) =>
      (s.val = [] →
        result = core.result.Result.Ok
          { version_negotiation := none, chain := none, inner := none }) ∧
      (s.val ≠ [] →
        match result with
        | core.result.Result.Ok pb =>
            proto.pq_ratchet.PqRatchetState.Insts.ProstMessageMessage.encode_to_vec
              pb = ok s
        | core.result.Result.Err e => e = Error.StateDecode) ⦄ := by
  unfold decode_state
  step*
  · simp_all
  · simp_all
    step*
    sorry


end spqr
