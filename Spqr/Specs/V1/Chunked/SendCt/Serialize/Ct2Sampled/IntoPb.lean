/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendCt.Serialize.Ct2Sent.IntoPb
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPb
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::serialize::Ct2Sampled::into_pb`

`Ct2Sampled.into_pb` converts a `Ct2Sampled` from the in-memory Rust form
(`v1.chunked.send_ct.Ct2Sampled`) into the protobuf form
(`proto.pq_ratchet.v1_state.chunked.Ct2Sampled`) used for network serialization or
persistent storage.

The chunked `Ct2Sampled` wraps an unchunked core
(`uc : v1.unchunked.send_ct.Ct2Sent`) together with a polynomial encoder
(`sending_ct2 : encoding.polynomial.PolyEncoder`) used for incremental transmission of the
second ciphertext.

The conversion performs the following steps:

1. Delegates to the unchunked `Ct2Sent.into_pb` to convert the `uc` field from
   `v1.unchunked.send_ct.Ct2Sent` to
   `proto.pq_ratchet.v1_state.unchunked.Ct2Sent`, wrapping the result in `some`.
   This in turn delegates to `Authenticator.into_pb` to convert the embedded `auth` field,
   while copying `epoch` directly.
2. Delegates to `PolyEncoder.into_pb` to convert the `sending_ct2` field from
   `encoding.polynomial.PolyEncoder` to `proto.pq_ratchet.PolynomialEncoder`, wrapping the
   result in `some`.

The by-value `into_pb` introduces no additional logic beyond the delegation to the unchunked
`Ct2Sent.into_pb` and `PolyEncoder.into_pb`, so the postconditions are inherited
from the corresponding specifications.  The reverse direction is `from_pb`; together the two
functions let a value round-trip between the in-memory and protobuf forms without losing
information.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs (lines 135:4-140:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.send_ct.serialize.Ct2Sampled

/--
**Spec theorem for `v1.chunked.send_ct.serialize.Ct2Sampled.into_pb`**:

• Takes a `self : v1.chunked.send_ct.Ct2Sampled` containing:
  - `uc : v1.unchunked.send_ct.Ct2Sent` — the unchunked core, which itself holds an
    epoch counter (`U64`) and an authenticator (`authenticator.Authenticator`).
  - `sending_ct2 : encoding.polynomial.PolyEncoder` — the polynomial encoder tracking
    incremental transmission of the second ciphertext.
• Delegates to `v1.unchunked.send_ct.serialize.Ct2Sent.into_pb self.uc`, which
  converts the unchunked core into its protobuf representation, preserving `epoch`
  and converting the authenticator's `root_key` and `mac_key`.
• Delegates to `encoding.polynomial.PolyEncoder.into_pb self.sending_ct2`, which serializes
  the polynomial encoder into `proto.pq_ratchet.PolynomialEncoder`, preserving the chunk
  index `idx` and serializing the encoder state (either points or polynomials over GF(2¹⁶))
  into byte vectors.
• Returns a `proto.pq_ratchet.v1_state.chunked.Ct2Sampled` with:
  - `uc` set to `some cs` where `cs` is the converted unchunked core,
  - `sending_ct2` set to `some pe` where `pe` is the converted polynomial encoder.

• The function always succeeds (no panic), given that:
  - For the `Points` case: `2 * points[j].value.length + 2 ≤ Usize.max` for each of the
    16 point slots (the `u16 → [u8; 2]` serialization does not overflow).
  - For the `Polys` case: `2 * polys[j].degree + 2 ≤ Usize.max` for each of the
    16 polynomial slots (the coefficient serialization does not overflow).

The result satisfies the following postconditions:

  `match result.uc with
   | some cs =>
       cs.epoch = self.uc.epoch ∧
       match cs.auth with
       | some a => a.root_key = self.uc.auth.root_key ∧
                   a.mac_key  = self.uc.auth.mac_key
       | none   => False
   | none => False`
  `match result.sending_ct2 with
   | some pe => pe.idx = self.sending_ct2.idx
   | none    => False`

i.e. the unchunked core is faithfully converted via the unchunked `Ct2Sent.into_pb`
(preserving scalar fields and converting the authenticator), and the polynomial encoder is
converted via `PolyEncoder.into_pb` (preserving the chunk index).

The proof unfolds `into_pb` to expose the underlying delegation calls and discharges the
resulting goal with `step*`, which applies the already-registered `into_pb_spec` lemmas.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs (lines 135:4-140:5)
-/
@[step]
theorem into_pb_spec (self : v1.chunked.send_ct.Ct2Sampled)
    (h_overflow_points : ∀ points,
      self.sending_ct2.s = .Points points →
        ∀ j < points.length,
          2 * (points[j]!).value.length + 2 ≤ Usize.max)
    (h_overflow_polys : ∀ polys,
      self.sending_ct2.s = .Polys polys →
        ∀ j < polys.length, 2 * (polys[j]!).degree + 2 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.chunked.Ct2Sampled) =>
      (match result.uc with
      | some cs =>
        cs.epoch = self.uc.epoch ∧
        match cs.auth with
        | some a =>
          a.root_key = self.uc.auth.root_key ∧
          a.mac_key = self.uc.auth.mac_key
        | none => False
      | none => False) ∧
      match result.sending_ct2 with
      | some pe => pe.idx = self.sending_ct2.idx
      | none => False ⦄ := by
  unfold into_pb
  step*
  grind

end spqr.v1.chunked.send_ct.serialize.Ct2Sampled
