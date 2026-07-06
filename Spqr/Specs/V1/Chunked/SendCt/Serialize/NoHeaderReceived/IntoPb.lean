/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendCt.Serialize.NoHeaderReceived.IntoPb
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPb
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::serialize::NoHeaderReceived::into_pb`

`NoHeaderReceived.into_pb` converts a `NoHeaderReceived` from the in-memory Rust form
(`v1.chunked.send_ct.NoHeaderReceived`) into the protobuf form
(`proto.pq_ratchet.v1_state.chunked.NoHeaderReceived`) used for network serialization or
persistent storage.

The chunked `NoHeaderReceived` wraps an unchunked core
(`uc : v1.unchunked.send_ct.NoHeaderReceived`) together with a polynomial decoder
(`receiving_hdr : encoding.polynomial.PolyDecoder`) used for incremental reception of the
header.

The conversion performs the following steps:

1. Delegates to the unchunked `NoHeaderReceived.into_pb` to convert the `uc` field from
   `v1.unchunked.send_ct.NoHeaderReceived` to
   `proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived`, wrapping the result in `some`.
   This in turn delegates to `Authenticator.into_pb` to convert the embedded `auth` field,
   while copying `epoch` directly.
2. Delegates to `PolyDecoder.into_pb` to convert the `receiving_hdr` field from
   `encoding.polynomial.PolyDecoder` to `proto.pq_ratchet.PolynomialDecoder`, wrapping the
   result in `some`.

The by-value `into_pb` introduces no additional logic beyond the delegation to the unchunked
`NoHeaderReceived.into_pb` and `PolyDecoder.into_pb`, so the postconditions are inherited
from the corresponding specifications.  The reverse direction is `from_pb`; together the two
functions let a value round-trip between the in-memory and protobuf forms without losing
information.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs (lines 11:4-16:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.send_ct.serialize.NoHeaderReceived

/--
**Spec theorem for `v1.chunked.send_ct.serialize.NoHeaderReceived.into_pb`**:

• Takes a `self : v1.chunked.send_ct.NoHeaderReceived` containing:
  - `uc : v1.unchunked.send_ct.NoHeaderReceived` — the unchunked core, which itself holds an
    epoch counter (`U64`) and an authenticator (`authenticator.Authenticator`).
  - `receiving_hdr : encoding.polynomial.PolyDecoder` — the polynomial decoder tracking
    incremental reception of the header.
• Delegates to `v1.unchunked.send_ct.serialize.NoHeaderReceived.into_pb self.uc`, which
  converts the unchunked core into its protobuf representation, preserving `epoch` and
  converting the authenticator's `root_key` and `mac_key`.
• Delegates to `encoding.polynomial.PolyDecoder.into_pb self.receiving_hdr`, which serializes
  the polynomial decoder into `proto.pq_ratchet.PolynomialDecoder`, preserving `pts_needed`,
  `polys`, `is_complete`, and the length of `pts`.
• Returns a `proto.pq_ratchet.v1_state.chunked.NoHeaderReceived` with:
  - `uc` set to `some nhr` where `nhr` is the converted unchunked core,
  - `receiving_hdr` set to `some pd` where `pd` is the converted polynomial decoder.

• The function always succeeds (no panic), given that:
  - `self.receiving_hdr.pts_needed.val ≤ U32.max` (the `usize → u32` cast succeeds),
  - The `SortedSet → SortedVec` and `SortedVec → Vec<Pt>` deref operations succeed for each
    of the 16 polynomial slots (witnessed by `sv` and `inner`),
  - The serialized byte vectors do not overflow `Usize.max`.

The result satisfies the following postconditions:

  `match result.uc with
   | some nhr =>
       nhr.epoch = self.uc.epoch ∧
       match nhr.auth with
       | some a => a.root_key = self.uc.auth.root_key ∧
                   a.mac_key  = self.uc.auth.mac_key
       | none   => False
   | none => False`
  `match result.receiving_hdr with
   | some pd =>
       pd.pts_needed.val = self.receiving_hdr.pts_needed.val ∧
       pd.polys = 16#u32 ∧
       pd.is_complete = self.receiving_hdr.is_complete ∧
       pd.pts.val.length = self.receiving_hdr.pts.val.length
   | none => False`

i.e. the unchunked core is faithfully converted via the unchunked `NoHeaderReceived.into_pb`
(preserving the epoch and converting the authenticator), and the polynomial decoder is
converted via `PolyDecoder.into_pb` (preserving the high-level decoder metadata).

The proof unfolds `into_pb` to expose the underlying delegation calls and discharges the
resulting goal with `step*`, which applies the already-registered `into_pb_spec` lemmas.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs (lines 11:4-16:5)
-/
@[step]
theorem into_pb_spec (self : v1.chunked.send_ct.NoHeaderReceived)
    (h_pts_needed_fits : self.receiving_hdr.pts_needed.val ≤ U32.max)
    (sv : Nat → sorted_vec.SortedVec encoding.polynomial.Pt)
    (inner : Nat → alloc.vec.Vec encoding.polynomial.Pt)
    (h_sv : ∀ (k : Nat) (h : k < self.receiving_hdr.pts.val.length),
      sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
        encoding.polynomial.Pt.Insts.CoreCmpOrd
        (self.receiving_hdr.pts.val[k]'h) = ok (sv k))
    (h_inner : ∀ (k : Nat), k < self.receiving_hdr.pts.val.length →
      sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
        encoding.polynomial.Pt.Insts.CoreCmpOrd (sv k) = ok (inner k))
    (h_inner_overflow : ∀ (k : Nat), k < self.receiving_hdr.pts.val.length →
        4 * (inner k).val.length + 4 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.chunked.NoHeaderReceived) =>
      (match result.uc with
      | some nhr =>
        nhr.epoch = self.uc.epoch ∧
        match nhr.auth with
        | some a =>
          a.root_key = self.uc.auth.root_key ∧
          a.mac_key = self.uc.auth.mac_key
        | none => False
      | none => False) ∧
      match result.receiving_hdr with
      | some pd =>
        pd.pts_needed.val = self.receiving_hdr.pts_needed.val ∧
        pd.polys = 16#u32 ∧
        pd.is_complete = self.receiving_hdr.is_complete ∧
        pd.pts.val.length = self.receiving_hdr.pts.val.length
      | none => False ⦄ := by
  unfold into_pb
  step*
  grind


end spqr.v1.chunked.send_ct.serialize.NoHeaderReceived
