/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.KeysUnsampled.IntoPb
/-!
# Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::into_pb`

`KeysUnsampled.into_pb` converts a `KeysUnsampled` from the in-memory Rust form
(`v1.chunked.send_ek.KeysUnsampled`) into the protobuf form
(`proto.pq_ratchet.v1_state.chunked.KeysUnsampled`) used for network serialization or
persistent storage.

The chunked `KeysUnsampled` wraps an unchunked core
(`uc : v1.unchunked.send_ek.KeysUnsampled`) containing an epoch counter and an
authenticator.

The conversion performs the following step:

1. Delegates to the unchunked `KeysUnsampled.into_pb` to convert the `uc` field from
   `v1.unchunked.send_ek.KeysUnsampled` to
   `proto.pq_ratchet.v1_state.unchunked.KeysUnsampled`, wrapping the result in `some`.
   This in turn delegates to `Authenticator.into_pb` to convert the embedded `auth` field,
   while copying `epoch` directly.

The by-value `into_pb` introduces no additional logic beyond the delegation to the unchunked
`KeysUnsampled.into_pb`, so the postcondition is inherited from the corresponding
specification.  The reverse direction is `from_pb`; together the two functions let a value
round-trip between the in-memory and protobuf forms without losing information.

**Source**: spqr/src/v1/chunked/send_ek/serialize.rs (lines 10:4-14:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.send_ek.serialize.KeysUnsampled

/--
**Spec theorem for `v1.chunked.send_ek.serialize.KeysUnsampled.into_pb`**:

• Takes a `self : v1.chunked.send_ek.KeysUnsampled` containing:
  - `uc : v1.unchunked.send_ek.KeysUnsampled` — the unchunked core, which itself holds an
    epoch counter (`U64`) and an authenticator (`authenticator.Authenticator`).
• Delegates to `v1.unchunked.send_ek.serialize.KeysUnsampled.into_pb self.uc`, which
  converts the unchunked core into its protobuf representation, preserving `epoch` and
  converting the authenticator's `root_key` and `mac_key`.
• Returns a `proto.pq_ratchet.v1_state.chunked.KeysUnsampled` with:
  - `uc` set to `some ku` where `ku` is the converted unchunked core.

• The function always succeeds (no panic), since `KeysUnsampled.into_pb` (unchunked) is
  total.

The result satisfies the following postcondition:

  `match result.uc with
   | some ku =>
       ku.epoch = self.uc.epoch ∧
       match ku.auth with
       | some a => a.root_key = self.uc.auth.root_key ∧
                   a.mac_key  = self.uc.auth.mac_key
       | none   => False
   | none => False`

i.e. the unchunked core is faithfully converted via the unchunked `KeysUnsampled.into_pb`
(preserving the epoch and converting the authenticator).

The proof unfolds `into_pb` to expose the underlying delegation call and discharges the
resulting goal with `step*`, which applies the already-registered `into_pb_spec`.

**Source**: spqr/src/v1/chunked/send_ek/serialize.rs (lines 10:4-14:5)
-/
@[step]
theorem into_pb_spec (self : v1.chunked.send_ek.KeysUnsampled) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.chunked.KeysUnsampled) =>
      match result.uc with
      | some ku =>
        ku.epoch = self.uc.epoch ∧
        match ku.auth with
        | some a =>
          a.root_key = self.uc.auth.root_key ∧
          a.mac_key = self.uc.auth.mac_key
        | none => False
      | none => False ⦄ := by
  unfold into_pb
  step*
  grind

end spqr.v1.chunked.send_ek.serialize.KeysUnsampled
