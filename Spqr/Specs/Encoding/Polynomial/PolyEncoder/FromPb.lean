/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.ModByMonic
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.FromPbLoop0
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.FromPbLoop1
import Spqr.Specs.Encoding.Polynomial.NUM_POLYS
import Spqr.Specs.Encoding.Polynomial.Poly.Zero
/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::from_pb`

In GF(2¹⁶) — the Galois field with 65 536 elements — each field element is represented as a
polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned integer.
The big-endian two-byte encoding satisfies `value = hi * 256 + lo` where `hi` and `lo` are the
high and low bytes respectively.

The function `PolyEncoder::from_pb` reconstructs a `PolyEncoder` — which holds a
chunk index `idx : U32` and an `EncoderState` (either `Points` or `Polys`,
each wrapping a fixed-size array of 16 elements over GF(2¹⁶)) — from its
protobuf representation `proto::pq_ratchet::PolynomialEncoder`.  The input
structure carries three fields: the chunk index `idx`, a vector of serialized
point byte vectors `pts`, and a vector of serialized polynomial byte vectors
`polys`.

The function proceeds by branching on the contents of the protobuf message:
  1. `pts` is empty, `polys.len() == NUM_POLYS` — the polynomial-deserialization
     loop (`from_pb_loop0`) iterates over all 16 serialized byte vectors.  For
     each vector, `Poly::deserialize` reconstructs the polynomial from its
     big-endian byte encoding (each pair of bytes `[hi, lo]` yields a GF(2¹⁶)
     coefficient with value `hi * 256 + lo`).  The result populates
     `EncoderState::Polys(out)`.
  2. `polys` is empty, `pts.len() == NUM_POLYS` — the point-deserialization
     loop (`from_pb_loop1`) iterates over all 16 serialized byte vectors.
     For each vector, consecutive byte pairs are decoded from big-endian
     format into GF(2¹⁶) elements via `GF16::new(u16::from_be_bytes([hi, lo]))`.
     The result populates `EncoderState::Points(out)`.
  3. Otherwise (both non-empty, wrong length, or both empty) — the function
     returns `Err(PolynomialError::SerializationInvalid)`.

This is the inverse of `into_pb`: serialization via `into_pb` followed by
deserialization via `from_pb` recovers the original `PolyEncoder` (up to
structural equality of the coefficient data).

**Source**: spqr/src/encoding/polynomial.rs (lines 573:4-620:5)
-/

open Aeneas Aeneas.Std Result spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb`** (byte-level)

Deserialization of a `proto.pq_ratchet.PolynomialEncoder` into a `PolyEncoder`,
with the postcondition expressed at the raw byte level.

The result is a conjunction of two conditional guarantees corresponding to the
two valid input configurations:

  1. **Polys branch**: when `pb.pts` is empty and `pb.polys` has length 16
     (= `NUM_POLYS`), the result is `Ok { idx := pb.idx, s := Polys out }`
     where each polynomial in `out` satisfies the big-endian byte-decoding
     invariant: for coefficient index `k`, the GF(2¹⁶) value equals
       `pb.polys[j][2*k] * 256 + pb.polys[j][2*k+1]`

  2. **Points branch**: when `pb.polys` is empty and `pb.pts` has length 16,
     the result is `Ok { idx := pb.idx, s := Points out }` where each point
     in `out` satisfies the same big-endian byte-decoding invariant over the
     corresponding byte vector from `pb.pts`.

This follows from composing:
  1. `from_pb_loop0.loop_spec`:  the outer polynomial-deserialization loop faithfully
     reconstructs all `Poly` values from their serialized byte vectors.
  2. `from_pb_loop1.loop_spec`:  the outer point-deserialization loop faithfully
     reconstructs all `Point` values from their serialized byte vectors.

**Source**: spqr/src/encoding/polynomial.rs (lines 573:4-620:5)
-/
theorem from_pb_spec_bytes
    (pb : proto.pq_ratchet.PolynomialEncoder)
    (h_polys_nonempty : pb.pts.val = [] →
      ∀ (j : Nat), j < pb.polys.val.length →
        (pb.polys.val[j]!).val.length ≠ 0)
    (h_polys_even : pb.pts.val = [] →
      ∀ (j : Nat), j < pb.polys.val.length →
        (pb.polys.val[j]!).val.length % 2 = 0)
    (h_pts_even : pb.polys.val = [] →
      ∀ (j : Nat), j < pb.pts.val.length →
        (pb.pts.val[j]!).val.length % 2 = 0) :
    from_pb pb ⦃ (result : core.result.Result
        encoding.polynomial.PolyEncoder encoding.polynomial.PolynomialError) =>
      -- Polys branch: pts empty, polys.len = 16
      (pb.pts.val = [] → pb.polys.val.length = 16 →
        ∃ (out : Array encoding.polynomial.Poly 16#usize),
          result = core.result.Result.Ok
            { idx := pb.idx, s := encoding.polynomial.EncoderState.Polys out } ∧
          ∀ (j : Nat), j < 16 →
            ∃ (poly : encoding.polynomial.Poly),
              out.val[j]! = poly ∧
              poly.coefficients.val.length =
                (pb.polys.val[j]!).val.length / 2 ∧
              ∀ (k : Nat),
                k < (pb.polys.val[j]!).val.length / 2 →
                ∃ (g : encoding.gf.GF16),
                  poly.coefficients.val[k]? = some g ∧
                  g.value.val =
                    ((pb.polys.val[j]!).val[2 * k]!).val * 256 +
                    ((pb.polys.val[j]!).val[2 * k + 1]!).val) ∧
      -- Points branch: polys empty, pts.len = 16
      (pb.polys.val = [] → pb.pts.val.length = 16 →
        ∃ (out : Array encoding.polynomial.Point 16#usize),
          result = core.result.Result.Ok
            { idx := pb.idx, s := encoding.polynomial.EncoderState.Points out } ∧
          ∀ (j : Nat), j < 16 →
            ∃ (pt : encoding.polynomial.Point),
              out.val[j]! = pt ∧
              pt.value.val.length =
                (pb.pts.val[j]!).val.length / 2 ∧
              ∀ (k : Nat),
                k < (pb.pts.val[j]!).val.length / 2 →
                ∃ (g : encoding.gf.GF16),
                  pt.value.val[k]? = some g ∧
                  g.value.val =
                    ((pb.pts.val[j]!).val[2 * k]!).val * 256 +
                    ((pb.pts.val[j]!).val[2 * k + 1]!).val) ⦄ := by
  unfold from_pb
  step*
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind

/--
Lifts the byte-level specification (`from_pb_spec_bytes`) to a cascading
postcondition that includes the raw byte equality **and** the derived
GF(2¹⁶) and polynomial identities.  For each deserialized GF(2¹⁶) coefficient
with value `v = hi * 256 + lo`, the cascading postcondition additionally
asserts:
  • `v.toGF216 = v.toGF216`   — the `Nat.toGF216` image is preserved
  • `natToBinaryPoly v = natToBinaryPoly v`   — the binary polynomial image is preserved

Specializing `BinaryPoly.toGF216` to the canonical isomorphism (whose construction requires
irreducibility of `polyGF2` over `ZMod 2`, i.e. a finite-field development we omit here) recovers
the GF(2¹⁶) interpretation of each deserialized coefficient.
-/
@[step]
theorem from_pb_spec
    (pb : proto.pq_ratchet.PolynomialEncoder)
    (h_polys_nonempty : pb.pts.val = [] →
      ∀ (j : Nat), j < pb.polys.val.length →
        (pb.polys.val[j]!).val.length ≠ 0)
    (h_polys_even : pb.pts.val = [] →
      ∀ (j : Nat), j < pb.polys.val.length →
        (pb.polys.val[j]!).val.length % 2 = 0)
    (h_pts_even : pb.polys.val = [] →
      ∀ (j : Nat), j < pb.pts.val.length →
        (pb.pts.val[j]!).val.length % 2 = 0) :
    from_pb pb ⦃ (result : core.result.Result
        encoding.polynomial.PolyEncoder encoding.polynomial.PolynomialError) =>
      -- Polys branch: pts empty, polys.len = 16
      (pb.pts.val = [] → pb.polys.val.length = 16 →
        ∃ (out : Array encoding.polynomial.Poly 16#usize),
          result = core.result.Result.Ok
            { idx := pb.idx, s := encoding.polynomial.EncoderState.Polys out } ∧
          ∀ (j : Nat), j < 16 →
            ∃ (poly : encoding.polynomial.Poly),
              out.val[j]! = poly ∧
              poly.coefficients.val.length =
                (pb.polys.val[j]!).val.length / 2 ∧
              ∀ (k : Nat),
                k < (pb.polys.val[j]!).val.length / 2 →
                ∃ (g : encoding.gf.GF16),
                  poly.coefficients.val[k]? = some g ∧
                  g.value.val =
                    ((pb.polys.val[j]!).val[2 * k]!).val * 256 +
                    ((pb.polys.val[j]!).val[2 * k + 1]!).val ∧
                  (g.value.val).toGF216 =
                    (((pb.polys.val[j]!).val[2 * k]!).val * 256 +
                     ((pb.polys.val[j]!).val[2 * k + 1]!).val).toGF216 ∧
                  natToBinaryPoly g.value.val =
                    natToBinaryPoly
                      (((pb.polys.val[j]!).val[2 * k]!).val * 256 +
                       ((pb.polys.val[j]!).val[2 * k + 1]!).val)) ∧
      -- Points branch: polys empty, pts.len = 16
      (pb.polys.val = [] → pb.pts.val.length = 16 →
        ∃ (out : Array encoding.polynomial.Point 16#usize),
          result = core.result.Result.Ok
            { idx := pb.idx, s := encoding.polynomial.EncoderState.Points out } ∧
          ∀ (j : Nat), j < 16 →
            ∃ (pt : encoding.polynomial.Point),
              out.val[j]! = pt ∧
              pt.value.val.length =
                (pb.pts.val[j]!).val.length / 2 ∧
              ∀ (k : Nat),
                k < (pb.pts.val[j]!).val.length / 2 →
                ∃ (g : encoding.gf.GF16),
                  pt.value.val[k]? = some g ∧
                  g.value.val =
                    ((pb.pts.val[j]!).val[2 * k]!).val * 256 +
                    ((pb.pts.val[j]!).val[2 * k + 1]!).val ∧
                  (g.value.val).toGF216 =
                    (((pb.pts.val[j]!).val[2 * k]!).val * 256 +
                     ((pb.pts.val[j]!).val[2 * k + 1]!).val).toGF216 ∧
                  natToBinaryPoly g.value.val =
                    natToBinaryPoly
                      (((pb.pts.val[j]!).val[2 * k]!).val * 256 +
                       ((pb.pts.val[j]!).val[2 * k + 1]!).val)) ⦄ := by
  have h_raw := from_pb_spec_bytes pb h_polys_nonempty h_polys_even h_pts_even
  apply WP.spec_mono h_raw
  intro result h_post
  obtain ⟨h_polys, h_pts⟩ := h_post
  refine ⟨fun h_pts_empty h_polys_len => ?_, fun h_polys_empty h_pts_len => ?_⟩
  · -- Polys branch
    obtain ⟨out, h_ok, h_ser⟩ := h_polys h_pts_empty h_polys_len
    refine ⟨out, h_ok, fun j hj => ?_⟩
    obtain ⟨poly, h_some, h_slen, h_enc⟩ := h_ser j hj
    refine ⟨poly, h_some, h_slen, fun k hk => ?_⟩
    obtain ⟨g, hg, h_eq⟩ := h_enc k hk
    exact ⟨g, hg, h_eq,
      congr_arg Nat.toGF216 h_eq,
      congr_arg natToBinaryPoly h_eq⟩
  · -- Points branch
    obtain ⟨out, h_ok, h_ser⟩ := h_pts h_polys_empty h_pts_len
    refine ⟨out, h_ok, fun j hj => ?_⟩
    obtain ⟨pt, h_some, h_slen, h_enc⟩ := h_ser j hj
    refine ⟨pt, h_some, h_slen, fun k hk => ?_⟩
    obtain ⟨g, hg, h_eq⟩ := h_enc k hk
    exact ⟨g, hg, h_eq,
      congr_arg Nat.toGF216 h_eq,
      congr_arg natToBinaryPoly h_eq⟩

end spqr.encoding.polynomial.PolyEncoder
