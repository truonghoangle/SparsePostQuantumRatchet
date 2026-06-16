/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
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
with the postcondition expressed at the raw byte level via `match` on the result
(without `∃` or explicit `Result.Ok` equations).

The postcondition is a conjunction of two conditional guarantees corresponding to the
two valid input configurations:

  1. **Polys branch**: when `pb.pts` is empty and `pb.polys` has length 16
     (= `NUM_POLYS`), the result matches `Ok encoder` where `encoder.idx = pb.idx`
     and `encoder.s` matches `Polys out`, with each polynomial in `out` satisfying
     the big-endian byte-decoding invariant: for coefficient index `k`, the GF(2¹⁶)
     value equals `pb.polys[j][2*k] * 256 + pb.polys[j][2*k+1]`.

  2. **Points branch**: when `pb.polys` is empty and `pb.pts` has length 16,
     the result matches `Ok encoder` where `encoder.idx = pb.idx` and `encoder.s`
     matches `Points out`, with each point in `out` satisfying the same big-endian
     byte-decoding invariant over the corresponding byte vector from `pb.pts`.

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
      ∀ j < pb.polys.length, (pb.polys[j]!).length ≠ 0)
    (h_polys_even : pb.pts.val = [] →
      ∀ j < pb.polys.length, (pb.polys[j]!).length % 2 = 0)
    (h_pts_even : pb.polys.val = [] →
      ∀ j < pb.pts.length,
        (pb.pts[j]!).length % 2 = 0) :
    from_pb pb ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
      -- Polys branch: pts empty, polys.len = 16
      (pb.pts.val = [] → pb.polys.val.length = 16 →
        match result with
        | core.result.Result.Ok encoder =>
            encoder.idx = pb.idx ∧
            match encoder.s with
            | encoding.polynomial.EncoderState.Polys out =>
                ∀ j < 16,
                    (out[j]!).degree = (pb.polys[j]!).length / 2 ∧
                    ∀ k < (pb.polys[j]!).length / 2,
                        (out[j]!.coefficients[k]!).value.val =
                          256 * ((pb.polys[j]!)[2 * k]!).val + ((pb.polys[j]!)[2 * k + 1]!).val
            | _ => False
        | core.result.Result.Err _ => False) ∧
      -- Points branch: polys empty, pts.len = 16
      (pb.polys.val = [] → pb.pts.length = 16 →
        match result with
        | core.result.Result.Ok encoder =>
            encoder.idx = pb.idx ∧
            match encoder.s with
            | encoding.polynomial.EncoderState.Points out =>
                ∀ j < 16,
                    (out[j]!).value.length = (pb.pts[j]!).length / 2 ∧
                    ∀ k < (pb.pts[j]!).length / 2,
                        ((out[j]!).value[k]!).value.val =
                          256 * ((pb.pts[j]!)[2 * k]!).val +
                          ((pb.pts[j]!)[2 * k + 1]!).val
            | _ => False
        | core.result.Result.Err _ => False) ⦄ := by
  unfold from_pb
  step*
  · grind
  · grind
  · refine ⟨fun _ _ => ?_, fun h _ => ?_⟩
    · -- First conjunct: polys branch (Usize → Nat quantifier conversion)
      cases result with
      | Err _ => exact result_post
      | Ok enc =>
        obtain ⟨h_idx, h_enc⟩ := result_post
        refine ⟨h_idx, ?_⟩
        revert h_enc
        cases enc.s with
        | Points _ => exact id
        | Polys out =>
          intro h_enc
          exact fun j hj => h_enc ⟨j, by scalar_tac⟩ (by
            change j < ↑i1; rw [i1_post]; exact hj)
    · -- Second conjunct: vacuously true (polys is non-empty)
      simp_all
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
      ∀ j < pb.polys.length, (pb.polys[j]!).length ≠ 0)
    (h_polys_even : pb.pts.val = [] →
      ∀ j < pb.polys.length, (pb.polys[j]!).length % 2 = 0)
    (h_pts_even : pb.polys.val = [] →
      ∀ j < pb.pts.length,
        (pb.pts[j]!).length % 2 = 0) :
    from_pb pb ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
      -- Polys branch: pts empty, polys.len = 16
      (pb.pts.val = [] → pb.polys.val.length = 16 →
        match result with
        | core.result.Result.Ok encoder =>
            encoder.idx = pb.idx ∧
            match encoder.s with
            | encoding.polynomial.EncoderState.Polys out =>
                ∀ j < 16,
                    (out[j]!).degree = (pb.polys[j]!).length / 2 ∧
                    ∀ k < (pb.polys[j]!).length / 2,
                        (out[j]!.coefficients[k]!).value.val =
                          256 * ((pb.polys[j]!)[2 * k]!).val + ((pb.polys[j]!)[2 * k + 1]!).val ∧
                        ((out[j]!.coefficients[k]!).value.val).toGF216 =
                          (256 * ((pb.polys[j]!)[2 * k]!).val +
                           ((pb.polys[j]!)[2 * k + 1]!).val).toGF216 ∧
                        natToBinaryPoly (out[j]!.coefficients[k]!).value.val =
                          natToBinaryPoly
                            (256 * ((pb.polys[j]!)[2 * k]!).val +
                             ((pb.polys[j]!)[2 * k + 1]!).val)
            | _ => False
        | core.result.Result.Err _ => False) ∧
      -- Points branch: polys empty, pts.len = 16
      (pb.polys.val = [] → pb.pts.length = 16 →
        match result with
        | core.result.Result.Ok encoder =>
            encoder.idx = pb.idx ∧
            match encoder.s with
            | encoding.polynomial.EncoderState.Points out =>
                ∀ j < 16,
                    (out[j]!).value.length = (pb.pts[j]!).length / 2 ∧
                    ∀ k < (pb.pts[j]!).length / 2,
                        ((out[j]!).value[k]!).value.val =
                          256 * ((pb.pts[j]!)[2 * k]!).val +
                          ((pb.pts[j]!)[2 * k + 1]!).val ∧
                        (((out[j]!).value[k]!).value.val).toGF216 =
                          (256 * ((pb.pts[j]!)[2 * k]!).val +
                           ((pb.pts[j]!)[2 * k + 1]!).val).toGF216 ∧
                        natToBinaryPoly ((out[j]!).value[k]!).value.val =
                          natToBinaryPoly
                            (256 * ((pb.pts[j]!)[2 * k]!).val +
                             ((pb.pts[j]!)[2 * k + 1]!).val)
            | _ => False
        | core.result.Result.Err _ => False) ⦄ := by
  have h_raw := from_pb_spec_bytes pb h_polys_nonempty h_polys_even h_pts_even
  apply WP.spec_mono h_raw
  intro result ⟨h_polys, h_pts⟩
  constructor
  · intro h1 h2
    have h := h_polys h1 h2
    revert h
    match result with
    | .Err _ => exact id
    | .Ok encoder =>
      intro ⟨h_idx, h_enc⟩
      exact ⟨h_idx, by
        revert h_enc
        match encoder.s with
        | .Points _ => exact id
        | .Polys out =>
          intro h_enc j hj
          obtain ⟨h_deg, h_coeff⟩ := h_enc j hj
          exact ⟨h_deg, fun k hk => by
            have hv := h_coeff k hk
            exact ⟨hv, congr_arg Nat.toGF216 hv, congr_arg natToBinaryPoly hv⟩⟩⟩
  · intro h1 h2
    have h := h_pts h1 h2
    revert h
    match result with
    | .Err _ => exact id
    | .Ok encoder =>
      intro ⟨h_idx, h_enc⟩
      exact ⟨h_idx, by
        revert h_enc
        match encoder.s with
        | .Polys _ => exact id
        | .Points out =>
          intro h_enc j hj
          obtain ⟨h_len, h_coeff⟩ := h_enc j hj
          exact ⟨h_len, fun k hk => by
            have hv := h_coeff k hk
            exact ⟨hv, congr_arg Nat.toGF216 hv, congr_arg natToBinaryPoly hv⟩⟩⟩

end spqr.encoding.polynomial.PolyEncoder
