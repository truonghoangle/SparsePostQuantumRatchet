/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::Version::MAX`

`Version::MAX` is a named constant alias for `Version::V1`, representing the highest supported
SPQR protocol version.  When a client initializes with `version = MAX`, the full V1 post-quantum
ratchet state machine is activated, including ML-KEM768 key encapsulation, chunked encoding, and
HMAC-based authentication.

The constant is declared `@[global_simps, irreducible]` in the Aeneas extraction, meaning it will
not unfold by default but is available as a simp lemma via `@[global_simps]`.

**Source**: spqr/src/lib.rs (line 240)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.Version.MAX`**:

• `Version.MAX` is defined as `proto.pq_ratchet.Version.V1`.
• This is a pure constant definition with no computation or error paths.
• It is the complement of `Version.DISABLED` (which equals `V0`).

The result satisfies the identity:

  `Version.MAX = proto.pq_ratchet.Version.V1`

The proof unfolds the `@[irreducible]` definition to expose the underlying `V1` value.

**Source**: spqr/src/lib.rs (line 240)
-/
@[simp]
theorem Version.MAX_spec :
    Version.MAX = proto.pq_ratchet.Version.V1 := by
  unfold Version.MAX; rfl

end spqr
