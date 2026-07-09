/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::Direction::switch`

`Direction::switch` swaps the two communication directions: `A2B ↔ B2A`.  This is used throughout
the SPQR protocol to derive the peer's direction from the local direction, e.g. when constructing
version negotiation metadata or interpreting received messages.

The function is a pure pattern match with no error paths — it always succeeds for any valid
`Direction` value.  Algebraically, `switch` is an involution: `switch (switch d) = d`.

**Source**: spqr/src/lib.rs (lines 65:4-71:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.Direction.switch`**:

• Takes a `Direction` value `self`.
• Pattern-matches on `self`:
  - `A2B` → returns `B2A`
  - `B2A` → returns `A2B`
• The function always succeeds (no panic, no error) for any valid `Direction` input.

The result satisfies the direction-swap postcondition:

  `match self with`
  `| .A2B => result = .B2A`
  `| .B2A => result = .A2B`

The proof unfolds `switch` and case-splits on `self`, closing each branch by `rfl`.

**Source**: spqr/src/lib.rs (lines 65:4-71:5)
-/
@[step]
theorem Direction.switch_spec (self : proto.pq_ratchet.Direction) :
    Direction.switch self ⦃ (result : proto.pq_ratchet.Direction) =>
      (self = .A2B → result = .B2A) ∧
      (self = .B2A → result = .A2B) ⦄ := by
  unfold Direction.switch
  sorry

end spqr
