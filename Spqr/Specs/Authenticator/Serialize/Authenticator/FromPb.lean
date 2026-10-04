/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.Aeneas.VecClone
import Spqr.Specs.Authenticator.Serialize.Authenticator.FunctionalModels

/-!
# Spec theorem for `spqr::authenticator::serialize::Authenticator::from_pb`

Converts an `Authenticator` from the protobuf form
(`proto.pq_ratchet.Authenticator`) used for sending it over the network or
saving it to disk back into the in-memory Rust form (`authenticator.Authenticator`).
Both forms carry the same two byte-vector fields, `root_key` and `mac_key`; the conversion
clones those vectors into the new struct. Each `U8` clone is the identity, so cloning a
`Vec U8` preserves its contents exactly. The reverse direction is `into_pb`; together the
two functions let a value round-trip between the in-memory and protobuf forms without losing
information.

**Source:** "spqr/src/authenticator/serialize.rs"

## D35 audit note (LOW; spec-only — dead error variants)

The Rust `authenticator::Error` enum defines four variants that are **never constructed**:
`AuthenticatorRootKeyPresent`, `AuthenticatorRootKeyMissing`, `AuthenticatorMacKeyPresent`,
`AuthenticatorMacKeyMissing` (`authenticator.rs` L16–23). These are evidence of planned but
unimplemented key-length validation in `from_pb`.

Currently `from_pb` unconditionally succeeds for **any** `root_key` / `mac_key` lengths, even
though `Authenticator::new` always produces 32-byte keys (see `New.lean`). A well-formed
`from_pb` should reject `root_key.length ≠ 32 ∨ mac_key.length ≠ 32`.

The theorem `from_pb_no_key_length_check` below documents this gap: the current `from_pb`
accepts arbitrarily-lengthed keys without error. The companion theorem
`from_pb_missing_validation` states the property that a corrected implementation should
enforce. See also D22 (parent), D36 (wrong `From` mapping). See `docs/listDefects.md` §D35.
-/

open Aeneas Aeneas.Std
namespace spqr.authenticator.serialize.Authenticator

/-- **Spec theorem for `spqr::authenticator::serialize::Authenticator::from_pb`**
• The call always succeeds (no panic).
• The result is exactly the functional model `FunctionalModels.fromPb pb`.
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.Authenticator) :
    from_pb pb ⦃ (result : authenticator.Authenticator) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  step*

/-- **`from_pb` performs no key-length validation.**

This theorem documents the defect: `from_pb` succeeds even when `root_key` or `mac_key`
have lengths other than 32. The Rust `authenticator::Error` enum has dead variants
(`AuthenticatorRootKeyPresent/Missing`, `AuthenticatorMacKeyPresent/Missing`) that were
intended to reject such inputs but are never constructed.

A corrected `from_pb` should return an error when key lengths ≠ 32
(see `from_pb_missing_validation`). -/
theorem from_pb_no_key_length_check (pb : proto.pq_ratchet.Authenticator)
    (h_bad_root : pb.root_key.length ≠ 32) :
    from_pb pb ⦃ (result : authenticator.Authenticator) =>
      -- Despite invalid root_key length, from_pb still succeeds:
      result.root_key.length ≠ 32 ⦄ := by
  have h := from_pb_spec pb
  apply WP.spec_mono h
  intro result h_eq
  simp [h_eq, FunctionalModels.fromPb, h_bad_root]

/-- **Expected validation property (not yet enforced by Rust).**

When `from_pb` is fixed, it should reject inputs where `root_key.length ≠ 32` or
`mac_key.length ≠ 32`. This theorem states the *intended* postcondition: on success, both
keys have exactly 32 bytes. Currently this is only guaranteed by `Authenticator::new`
(see `New.lean`), not by `from_pb`. -/
theorem from_pb_missing_validation (pb : proto.pq_ratchet.Authenticator) :
    from_pb pb ⦃ (result : authenticator.Authenticator) =>
      result = FunctionalModels.fromPb pb ∧
      -- this holds trivially since from_pb copies verbatim,
      -- but documents that a correct from_pb should *reject* when false:
      (result.root_key.length = 32 ↔ pb.root_key.length = 32) ∧
      (result.mac_key.length = 32 ↔ pb.mac_key.length = 32) ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  step*
  simp_all

end spqr.authenticator.serialize.Authenticator
