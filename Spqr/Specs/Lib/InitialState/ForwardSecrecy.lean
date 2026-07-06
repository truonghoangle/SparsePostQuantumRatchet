/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.Axioms
import Spqr.Specs.Authenticator.Authenticator.New
/-!
# Forward Secrecy Foundation — Ratchet Invariant (§4.6, §8.4)

This file formalizes the **ratchet invariant** that underpins the forward secrecy
guarantees of the SPQR protocol, as described in §4.6 and §8.4 of
`doc/truong/discuss_initial_state.md`.

All definitions (`PROTOCOL_LABEL`, `ZERO_SALT`, `ratchet_ikm`, `ratchet_info`,
`ratchet_step_explicit`, `initial_ratchet_step`, `ratchet_chain_valid`, etc.)
are provided by `Spqr/Specs/Lib/RatchetDefs.lean` and re-exported via the
`Spqr.Specs.Authenticator.Authenticator.New` import.

## Contents

- `initial_state_ratchet_base_case`: base case theorem — `Authenticator.new`
  satisfies `initial_ratchet_step`

## References
- Cohn-Gordon et al. "On Post-Compromise Security" (IEEE S&P 2020)
- Signal Protocol — Double Ratchet Algorithm specification
- `proofs/proverif/spqr-cka.pv` lines 73–79 (`recvCT2` updates authenticator)
- `proofs/proverif/spqr-dr.pv` — Double Ratchet security model
- RFC 5869 — HKDF
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-! ### Base Case: Initial State -/

/--
**Base case of the ratchet invariant** (§4.6, §8.4).

The initial authenticator state, constructed by `Authenticator.new(root_key, ep)`,
is the base case of the ratchet chain.  It satisfies `initial_ratchet_step`, i.e.:

1. Both `root_key` and `mac_key` are exactly 32 bytes.
2. They are derived by a single explicit HKDF ratchet step from a zero-initialized
   authenticator with the `root_key` as shared secret:

```
ikm       = ZERO_SALT ++ root_key.val
info      = PROTOCOL_LABEL ++ ep.to_be_bytes()
kdf_out   = HKDF-SHA256(ZERO_SALT, ikm, info, 64)
auth.root_key = kdf_out[0..32]
auth.mac_key  = kdf_out[32..64]
```

The proof follows from `Authenticator.new_spec`, which establishes
`initial_ratchet_step` as its postcondition.
-/
theorem initial_state_ratchet_base_case
    (root_key : alloc.vec.Vec U8) (ep : U64)
    (h_key : root_key.length ≤ U32.max)
    (auth : authenticator.Authenticator)
    (h_new : authenticator.Authenticator.new root_key ep = ok auth) :
    initial_ratchet_step root_key.val ep auth := by
  have h := authenticator.Authenticator.new_spec root_key ep h_key
  rw [h_new] at h
  simp only [Aeneas.Std.WP.spec_ok] at h
  exact h

/-! ### Forward Secrecy: Computational Irreversibility

The computational irreversibility of the ratchet (i.e., forward secrecy) follows from
the PRF assumption on HMAC-SHA256. Specifically:

**Mathematical formulation**: The function
```
  f(root_key, k) = HKDF(ZERO_SALT, ratchet_ikm root_key k, ratchet_info ep_bytes, 64)[0..32]
```
is computationally one-way in `root_key` when `k` is erased.

This cannot be proved structurally in Lean — it is a reduction to the PRF security
of HMAC-SHA256. The ProVerif model (`proofs/proverif/spqr-cka.pv`) verifies this
property at the symbolic level.

The relevant axiom for domain separation is `hkdf_domain_separation` in
`Spqr/Specs/Lib/Axioms.lean`, which models the computational independence of HKDF
outputs under distinct info strings.

**References**:
- Cohn-Gordon et al. "On Post-Compromise Security" (IEEE S&P 2020)
- Signal Protocol — Double Ratchet Algorithm specification
- `proofs/proverif/spqr-cka.pv`, `proofs/proverif/spqr-dr.pv`
-/

end spqr
