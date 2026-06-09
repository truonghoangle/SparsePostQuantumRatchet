/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::empty_state`

The function `empty_state` constructs a fresh, empty serialized state. In the Rust source it is
defined as:
```rust
pub fn empty_state() -> SerializedState {
    SerializedState::new()
}
```
where `SerializedState = Vec<u8>`. The extracted Lean definition is:
```
def empty_state : Result (alloc.vec.Vec Std.U8) := do
  ok (alloc.vec.Vec.new Std.U8)
```

The function is unconditional and pure — it takes no arguments, never fails, and always returns the
empty byte vector.

**Source**: spqr/src/lib.rs (lines 47:0-49:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-- **The underlying list of `empty_state` is `[]`**.

`empty_state` always succeeds and the result vector has an empty backing list. -/
@[simp]
theorem empty_state_eq :
    empty_state = ok (alloc.vec.Vec.new Std.U8) := by
  simp [empty_state]

/-- **The length of the vector returned by `empty_state` is `0`**. -/
@[simp]
theorem empty_state_val_length :
    ∀ v, empty_state = ok v → v.val.length = 0 := by
  intro v hv
  simp [empty_state] at hv
  subst hv
  rfl

/--
**Spec and proof concerning `spqr::empty_state`**:

`empty_state` constructs a new, empty `Vec<u8>` representing the initial serialized state. The
function always succeeds and returns a vector whose backing list is empty (length 0).

Concretely:
  `empty_state ⦃ (result : alloc.vec.Vec Std.U8) => result.val.length = 0 ⦄`

The proof unfolds the definition and reduces `alloc.vec.Vec.new` to its empty-list
representation.

**Source**: spqr/src/lib.rs (lines 47:0-49:1)
-/
@[step]
theorem empty_state_spec :
    empty_state ⦃ (result : alloc.vec.Vec Std.U8) =>
      result.val.length = 0 ⦄ := by
  unfold empty_state
  step*

end spqr
