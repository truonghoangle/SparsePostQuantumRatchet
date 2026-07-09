/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::Version::DISABLED`

`Version::DISABLED` is a named constant alias for `Version::V0`, indicating that the SPQR
post-quantum ratchet protocol is disabled.  When a client initializes with `version = DISABLED`,
no inner V1 state is constructed and the protocol operates in pass-through mode (empty states,
empty messages, no key material).

The constant is declared `@[global_simps, irreducible]` in the Aeneas extraction, meaning it will
not unfold by default but is available as a simp lemma via `@[global_simps]`.

**Source**: spqr/src/lib.rs (line 239)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.Version.DISABLED`**:

• `Version.DISABLED` is defined as `proto.pq_ratchet.Version.V0`.
• This is a pure constant definition with no computation or error paths.
• It is the complement of `Version.MAX` (which equals `V1`).

The result satisfies the identity:

  `Version.DISABLED = proto.pq_ratchet.Version.V0`

The proof unfolds the `@[irreducible]` definition to expose the underlying `V0` value.

**Source**: spqr/src/lib.rs (line 239)
-/
@[simp]
theorem Version.DISABLED_spec :
    Version.DISABLED = proto.pq_ratchet.Version.V0 := by
  unfold Version.DISABLED; rfl

end spqr
