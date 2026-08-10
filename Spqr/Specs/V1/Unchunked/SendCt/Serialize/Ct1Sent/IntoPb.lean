/-
<<<<<<< HEAD
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.IntoPb
/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::serialize::Ct1Sent::into_pb`

`Ct1Sent.into_pb` converts a `Ct1Sent` from the in-memory Rust form
(`v1.unchunked.send_ct.Ct1Sent`) into the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.Ct1Sent`) used for network serialization or
persistent storage.

The conversion performs the following steps:

1. Delegates to `Authenticator.into_pb` to convert the embedded `auth` field from
   `authenticator.Authenticator` to `proto.pq_ratchet.Authenticator`, wrapping the result
   in `some`.
2. Calls `alloc.vec.Vec.deref` on `self.ct1` to obtain a slice, then
   `alloc.slice.Slice.to_vec` to clone it into a fresh `Vec U8`.
3. Copies the remaining fields (`epoch`, `hdr`, `es`) directly into the protobuf struct.

The by-value `into_pb` introduces no additional logic beyond the delegation to
`Authenticator.into_pb` and the `to_vec` clone, so the authenticator postcondition is
inherited from the corresponding `Authenticator.into_pb` specification.  The reverse
direction is `from_pb`; together the two functions let a value round-trip between the
in-memory and protobuf forms without losing information.

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs (lines 48:4-56:5)
=======
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.IntoPb

/-! # Spec theorem for `spqr::v1::unchunked::send_ct::serialize::Ct1Sent::into_pb`

Converts a `Ct1Sent` state from the in-memory Rust form
(`v1.unchunked.send_ct.Ct1Sent`) into the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.Ct1Sent`) used for saving it to
disk. The `epoch`, `hdr` and `es` fields are copied over unchanged, the
`auth` field is converted with `Authenticator::into_pb` (a plain field
copy) and wrapped in `Some`, and `ct1` is cloned into a fresh vector with
`to_vec` (byte cloning is the identity, so its contents are preserved
exactly). The reverse direction is `from_pb`.

**Source**: src/v1/unchunked/send_ct/serialize.rs (lines 48:4-56:5)
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ct.serialize.Ct1Sent

<<<<<<< HEAD
/--
**Spec theorem for `v1.unchunked.send_ct.serialize.Ct1Sent.into_pb`**:

• Takes a `self : v1.unchunked.send_ct.Ct1Sent` containing an epoch counter (`U64`),
  an authenticator (`authenticator.Authenticator`), a header (`hdr : Vec U8`), an
  encoded secret (`es : Vec U8`), and a first ciphertext (`ct1 : Vec U8`).
• Delegates to `authenticator.serialize.Authenticator.into_pb self.auth`, which converts the
  authenticator into its protobuf representation, preserving `root_key` and `mac_key`.
• Clones `self.ct1` via `alloc.vec.Vec.deref` followed by `alloc.slice.Slice.to_vec`,
  producing a `Vec U8` with the same content.
• Returns a `proto.pq_ratchet.v1_state.unchunked.Ct1Sent` with:
  - `epoch` copied directly from `self.epoch`,
  - `auth` set to `some a` where `a` is the converted authenticator,
  - `hdr` copied directly from `self.hdr`,
  - `es` copied directly from `self.es`,
  - `ct1` set to the cloned vector (equal to `self.ct1`).

• The function always succeeds (no panic), since `Authenticator.into_pb` is total and
  `to_vec` is total on any valid `Vec U8`.

The result satisfies the following postconditions:

  `result.epoch = self.epoch`
  `result.hdr   = self.hdr`
  `result.es    = self.es`
  `result.ct1   = self.ct1`
  `match result.auth with
   | some a => a.root_key = self.auth.root_key ∧
               a.mac_key  = self.auth.mac_key
   | none   => False`

i.e. the scalar fields are preserved verbatim, and the embedded authenticator is converted
via `Authenticator.into_pb`, retaining its `root_key` and `mac_key` byte vectors.

The proof unfolds `into_pb` to expose the underlying `Authenticator.into_pb` call and discharges
the resulting goal with `step*`, which applies the already-registered `into_pb_spec`.

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs (lines 48:4-56:5)
-/
=======
/-- **Spec theorem for `v1.unchunked.send_ct.serialize.Ct1Sent.into_pb`**:

• The call always succeeds (no panic).
• The result's `epoch`, `hdr`, `es` and `ct1` equal the corresponding
  fields of `self` (cloning the `ct1` byte vector preserves it exactly).
• The result's `auth` is `some` of the protobuf form of `self.auth`,
  carrying the same `root_key` and `mac_key`. -/
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
@[step]
theorem into_pb_spec (self : v1.unchunked.send_ct.Ct1Sent) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.Ct1Sent) =>
      result.epoch = self.epoch ∧
      result.hdr = self.hdr ∧
      result.es = self.es ∧
      result.ct1 = self.ct1 ∧
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
  unfold into_pb
  step*
  obtain ⟨root_key, mac_key⟩ := a
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
  simp_all [alloc.vec.Vec.deref]

end spqr.v1.unchunked.send_ct.serialize.Ct1Sent
