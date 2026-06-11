/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::empty_state`

In the Sparse Post-Quantum Ratchet, a *serialized state* is a `Vec<u8>` — a heap-allocated byte
buffer carrying the wire-format representation of a ratchet state. The top-level helper
`empty_state` produces the canonical "no-state-yet" value: a freshly allocated, length-`0` byte
buffer.

The function proceeds in a single stage:
  1. `alloc.vec.Vec.new Std.U8` — allocate a new `Vec<u8>` whose backing list is `[]`,
     and lift it into the `Result` monad via `ok`.

There is no failure path, no input to validate, and no further computation: the function is pure,
total, and deterministic.

**Source**: spqr/src/lib.rs (lines 47:0-49:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-- **Spec theorem for `spqr::empty_state` at the list level**:

Construction of a fresh, empty `Vec<u8>` representing the initial serialized state. The Rust source
is the one-liner
```rust
pub fn empty_state() -> SerializedState {
    SerializedState::new()
}
```
with `SerializedState = Vec<u8>`, and after extraction this becomes
```
def empty_state : Result (alloc.vec.Vec Std.U8) := do
  ok (alloc.vec.Vec.new Std.U8)
```

The function never fails and its result is fully determined: the backing list of the returned
vector is the empty list. Formally,
  `(empty_state).result.val = []`.

This follows directly from unfolding the definition and reducing `alloc.vec.Vec.new` to its
empty-list representation. It is the strongest possible characterization of the output and is the
foundational fact from which all weaker, more "interface-level" properties (e.g. length-`0`,
emptiness predicate) follow.

**Source**: spqr/src/lib.rs (lines 47:0-49:1)
-/
theorem empty_state_spec_nat :
    empty_state ⦃ (result : alloc.vec.Vec Std.U8) =>
      result.val = [] ⦄ := by
  unfold empty_state
  step*

/--
For any "size measure" `List.length : List Std.U8 → ℕ` that vanishes on the empty list, the
result of `empty_state` corresponds — via `List.length ∘ alloc.vec.Vec.val` — to `0`.

Specializing the underlying-list characterization of `empty_state_spec_nat` to the length measure
recovers the standard "the returned buffer has size `0`" interpretation, which is the form most
commonly consumed by downstream callers (e.g. as the initial accumulator in state-serialization
loops, or as the witness that no bytes are yet pending).
-/
@[step]
theorem empty_state_spec :
    empty_state ⦃ (result : alloc.vec.Vec Std.U8) =>
      result.val.length = 0 ⦄ := by
  unfold empty_state
  step*

end spqr
