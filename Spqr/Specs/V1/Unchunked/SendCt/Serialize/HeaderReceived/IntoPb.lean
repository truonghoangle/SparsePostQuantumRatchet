/-
<<<<<<< HEAD
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.IntoPb
/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::serialize::HeaderReceived::into_pb`

`HeaderReceived.into_pb` converts a `HeaderReceived` from the in-memory Rust form
(`v1.unchunked.send_ct.HeaderReceived`) into the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.HeaderReceived`) used for network serialization or
persistent storage.

The conversion performs the following steps:

1. Delegates to `Authenticator.into_pb` to convert the embedded `auth` field from
   `authenticator.Authenticator` to `proto.pq_ratchet.Authenticator`, wrapping the result
   in `some`.
2. Copies the remaining fields (`epoch`, `hdr`) directly into the protobuf struct.

The by-value `into_pb` introduces no additional logic beyond the delegation to
`Authenticator.into_pb`, so the authenticator postcondition is inherited from the
corresponding `Authenticator.into_pb` specification.  The reverse direction is `from_pb`;
together the two functions let a value round-trip between the in-memory and protobuf forms
without losing information.

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs (lines 26:4-32:5)
=======
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec theorem for `spqr::v1::unchunked::send_ct::serialize::HeaderReceived::into_pb`

Converts a `HeaderReceived` state from the in-memory Rust form
(`v1.unchunked.send_ct.HeaderReceived`) into the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.HeaderReceived`) used for saving it
to disk. The `epoch` and `hdr` fields are copied over unchanged and the
`auth` field is converted with `Authenticator::into_pb` (a plain field
copy) and wrapped in `Some`. The reverse direction is `from_pb`.

**Source**: src/v1/unchunked/send_ct/serialize.rs (lines 26:4-32:5)
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ct.serialize.HeaderReceived

<<<<<<< HEAD
/--
**Spec theorem for `v1.unchunked.send_ct.serialize.HeaderReceived.into_pb`**:

• Takes a `self : v1.unchunked.send_ct.HeaderReceived` containing an epoch counter (`U64`),
  an authenticator (`authenticator.Authenticator`), and a header (`hdr : Vec U8`).
• Delegates to `authenticator.serialize.Authenticator.into_pb self.auth`, which converts the
  authenticator into its protobuf representation, preserving `root_key` and `mac_key`.
• Returns a `proto.pq_ratchet.v1_state.unchunked.HeaderReceived` with:
  - `epoch` copied directly from `self.epoch`,
  - `auth` set to `some a` where `a` is the converted authenticator,
  - `hdr` copied directly from `self.hdr`.

• The function always succeeds (no panic), since `Authenticator.into_pb` is total.

The result satisfies the following postconditions:

  `result.epoch = self.epoch`
  `result.hdr   = self.hdr`
  `match result.auth with
   | some a => a.root_key = self.auth.root_key ∧
               a.mac_key  = self.auth.mac_key
   | none   => False`

i.e. the scalar fields are preserved verbatim, and the embedded authenticator is converted
via `Authenticator.into_pb`, retaining its `root_key` and `mac_key` byte vectors.

The proof unfolds `into_pb` to expose the underlying `Authenticator.into_pb` call and discharges
the resulting goal with `step*`, which applies the already-registered `into_pb_spec`.

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs (lines 26:4-32:5)
-/
=======
/-- **Spec theorem for `v1.unchunked.send_ct.serialize.HeaderReceived.into_pb`**:

• The call always succeeds (no panic).
• The result's `epoch` and `hdr` equal the corresponding fields of `self`.
• The result's `auth` is `some` of the protobuf form of `self.auth`,
  carrying the same `root_key` and `mac_key`. -/
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
@[step]
theorem into_pb_spec (self : v1.unchunked.send_ct.HeaderReceived) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.HeaderReceived) =>
      result.epoch = self.epoch ∧
      result.hdr = self.hdr ∧
<<<<<<< HEAD
      match result.auth with
      | some a =>
        a.root_key = self.auth.root_key ∧
        a.mac_key = self.auth.mac_key
      | none => False ⦄ := by
  unfold into_pb
  step*
=======
      result.auth = some { root_key := self.auth.root_key,
                           mac_key := self.auth.mac_key } ⦄ := by
  simp [into_pb, authenticator.serialize.Authenticator.into_pb]
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5

end spqr.v1.unchunked.send_ct.serialize.HeaderReceived
