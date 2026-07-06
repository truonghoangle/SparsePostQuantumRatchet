/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.IntoPb
/-!
# Spec theorem for `spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received::into_pb`

`EkSentCt1Received.into_pb` converts an `EkSentCt1Received` from the in-memory Rust form
(`v1.unchunked.send_ek.EkSentCt1Received`) into the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received`) used for network serialization or
persistent storage.

The conversion performs the following steps:

1. Delegates to `Authenticator.into_pb` to convert the embedded `auth` field from
   `authenticator.Authenticator` to `proto.pq_ratchet.Authenticator`, wrapping the result
   in `some`.
2. Copies the remaining fields (`epoch`, `dk`, `ct1`) directly into the protobuf struct.

The by-value `into_pb` introduces no additional logic beyond the delegation to
`Authenticator.into_pb`, so the authenticator postcondition is inherited from the
corresponding `Authenticator.into_pb` specification.  The reverse direction is `from_pb`;
together the two functions let a value round-trip between the in-memory and protobuf forms
without losing information.

**Source**: spqr/src/v1/unchunked/send_ek/serialize.rs (lines 72:4-79:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ek.serialize.EkSentCt1Received

/--
**Spec theorem for `v1.unchunked.send_ek.serialize.EkSentCt1Received.into_pb`**:

• Takes a `self : v1.unchunked.send_ek.EkSentCt1Received` containing an epoch counter (`U64`),
  an authenticator (`authenticator.Authenticator`), a decapsulation key (`dk : Vec U8`), and a
  first ciphertext (`ct1 : Vec U8`).
• Delegates to `authenticator.serialize.Authenticator.into_pb self.auth`, which converts the
  authenticator into its protobuf representation, preserving `root_key` and `mac_key`.
• Returns a `proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received` with:
  - `epoch` copied directly from `self.epoch`,
  - `auth` set to `some a` where `a` is the converted authenticator,
  - `dk` copied directly from `self.dk`,
  - `ct1` copied directly from `self.ct1`.

• The function always succeeds (no panic), since `Authenticator.into_pb` is total.

The result satisfies the following postconditions:

  `result.epoch = self.epoch`
  `result.dk    = self.dk`
  `result.ct1   = self.ct1`
  `match result.auth with
   | some a => a.root_key = self.auth.root_key ∧
               a.mac_key  = self.auth.mac_key
   | none   => False`

i.e. the scalar fields are preserved verbatim, and the embedded authenticator is converted
via `Authenticator.into_pb`, retaining its `root_key` and `mac_key` byte vectors.

The proof unfolds `into_pb` to expose the underlying `Authenticator.into_pb` call and discharges
the resulting goal with `step*`, which applies the already-registered `into_pb_spec`.

**Source**: spqr/src/v1/unchunked/send_ek/serialize.rs (lines 72:4-79:5)
-/
@[step]
theorem into_pb_spec (self : v1.unchunked.send_ek.EkSentCt1Received) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received) =>
      result.epoch = self.epoch ∧
      result.dk = self.dk ∧
      result.ct1 = self.ct1 ∧
      match result.auth with
      | some a =>
        a.root_key = self.auth.root_key ∧
        a.mac_key = self.auth.mac_key
      | none => False ⦄ := by
  unfold into_pb
  step*

end spqr.v1.unchunked.send_ek.serialize.EkSentCt1Received
