/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendCt.Serialize.Ct1SentEkReceived.IntoPb
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPb
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::serialize::EkReceivedCt1Sampled::into_pb`

`EkReceivedCt1Sampled.into_pb` converts an `EkReceivedCt1Sampled` from the in-memory Rust form
(`v1.chunked.send_ct.EkReceivedCt1Sampled`) into the protobuf form
(`proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled`) used for network serialization or
persistent storage.

The chunked `EkReceivedCt1Sampled` wraps an unchunked core
(`uc : v1.unchunked.send_ct.Ct1SentEkReceived`) together with a polynomial encoder
(`sending_ct1 : encoding.polynomial.PolyEncoder`) used for incremental transmission of the
first ciphertext.

The conversion performs the following steps:

1. Delegates to the unchunked `Ct1SentEkReceived.into_pb` to convert the `uc` field from
   `v1.unchunked.send_ct.Ct1SentEkReceived` to
   `proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived`, wrapping the result in `some`.
   This in turn delegates to `Authenticator.into_pb` to convert the embedded `auth` field,
   while copying `epoch`, `es`, `ek`, and `ct1` directly.
2. Delegates to `PolyEncoder.into_pb` to convert the `sending_ct1` field from
   `encoding.polynomial.PolyEncoder` to `proto.pq_ratchet.PolynomialEncoder`, wrapping the
   result in `some`.

The by-value `into_pb` introduces no additional logic beyond the delegation to the unchunked
`Ct1SentEkReceived.into_pb` and `PolyEncoder.into_pb`, so the postconditions are inherited
from the corresponding specifications.  The reverse direction is `from_pb`; together the two
functions let a value round-trip between the in-memory and protobuf forms without losing
information.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs (lines 92:4-97:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.send_ct.serialize.EkReceivedCt1Sampled

/--
**Spec theorem for `v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.into_pb`**:

• Takes a `self : v1.chunked.send_ct.EkReceivedCt1Sampled` containing:
  - `uc : v1.unchunked.send_ct.Ct1SentEkReceived` — the unchunked core, which itself holds an
    epoch counter (`U64`), an authenticator (`authenticator.Authenticator`), an encoded secret
    (`es : Vec U8`), an encapsulation key (`ek : Vec U8`), and a first ciphertext
    (`ct1 : Vec U8`).
  - `sending_ct1 : encoding.polynomial.PolyEncoder` — the polynomial encoder tracking
    incremental transmission of the first ciphertext.
• Delegates to `v1.unchunked.send_ct.serialize.Ct1SentEkReceived.into_pb self.uc`, which
  converts the unchunked core into its protobuf representation, preserving `epoch`, `es`,
  `ek`, `ct1`, and converting the authenticator's `root_key` and `mac_key`.
• Delegates to `encoding.polynomial.PolyEncoder.into_pb self.sending_ct1`, which serializes
  the polynomial encoder into `proto.pq_ratchet.PolynomialEncoder`, preserving the chunk
  index `idx` and serializing the encoder state (either points or polynomials over GF(2¹⁶))
  into byte vectors.
• Returns a `proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled` with:
  - `uc` set to `some cser` where `cser` is the converted unchunked core,
  - `sending_ct1` set to `some pe` where `pe` is the converted polynomial encoder.

• The function always succeeds (no panic), given that:
  - For the `Points` case: `2 * points[j].value.length + 2 ≤ Usize.max` for each of the
    16 point slots (the `u16 → [u8; 2]` serialization does not overflow).
  - For the `Polys` case: `2 * polys[j].degree + 2 ≤ Usize.max` for each of the
    16 polynomial slots (the coefficient serialization does not overflow).

The result satisfies the following postconditions:

  `match result.uc with
   | some cser =>
       cser.epoch = self.uc.epoch ∧
       cser.es    = self.uc.es ∧
       cser.ek    = self.uc.ek ∧
       cser.ct1   = self.uc.ct1 ∧
       match cser.auth with
       | some a => a.root_key = self.uc.auth.root_key ∧
                   a.mac_key  = self.uc.auth.mac_key
       | none   => False
   | none => False`
  `match result.sending_ct1 with
   | some pe => pe.idx = self.sending_ct1.idx
   | none    => False`

i.e. the unchunked core is faithfully converted via the unchunked `Ct1SentEkReceived.into_pb`
(preserving scalar fields and converting the authenticator), and the polynomial encoder is
converted via `PolyEncoder.into_pb` (preserving the chunk index).

The proof unfolds `into_pb` to expose the underlying delegation calls and discharges the
resulting goal with `step*`, which applies the already-registered `into_pb_spec` lemmas.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs (lines 92:4-97:5)
-/
@[step]
theorem into_pb_spec (self : v1.chunked.send_ct.EkReceivedCt1Sampled)
    (h_overflow_points : ∀ points,
      self.sending_ct1.s = .Points points →
        ∀ j < points.length,
          2 * (points[j]!).value.length + 2 ≤ Usize.max)
    (h_overflow_polys : ∀ polys,
      self.sending_ct1.s = .Polys polys →
        ∀ j < polys.length, 2 * (polys[j]!).degree + 2 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled) =>
      (match result.uc with
      | some cser =>
        cser.epoch = self.uc.epoch ∧
        cser.es = self.uc.es ∧
        cser.ek = self.uc.ek ∧
        cser.ct1 = self.uc.ct1 ∧
        match cser.auth with
        | some a =>
          a.root_key = self.uc.auth.root_key ∧
          a.mac_key = self.uc.auth.mac_key
        | none => False
      | none => False) ∧
      match result.sending_ct1 with
      | some pe => pe.idx = self.sending_ct1.idx
      | none => False ⦄ := by
  unfold into_pb
  step*
  grind

end spqr.v1.chunked.send_ct.serialize.EkReceivedCt1Sampled
