/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.ModByMonic
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPbLoop0
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPbLoop2

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::into_pb`

The function `PolyEncoder::into_pb` converts a `PolyEncoder` — which holds a
chunk index `idx : U32` and an `EncoderState` (either `Points` or `Polys`,
each wrapping a fixed-size array of 16 elements over GF(2¹⁶)) — into its
protobuf representation `proto::pq_ratchet::PolynomialEncoder`.  The output
structure carries three fields: the chunk index `idx`, a vector of serialized
point byte vectors `pts`, and a vector of serialized polynomial byte vectors
`polys`.

The function proceeds in two stages depending on the `EncoderState`:
  1. `EncoderState::Points(points)` — the outer point-serialization loop
     (`into_pb_loop0`) iterates over all 16 `Point` values.  For each point,
     its GF(2¹⁶) coefficient vector is serialized into a big-endian byte
     vector (each `u16` element encoded as two bytes `hi * 256 + lo = value`).
     The result populates `result.pts`; `result.polys` is left empty.
  2. `EncoderState::Polys(polys)` — the polynomial-serialization loop
     (`into_pb_loop1`) iterates over all 16 `Poly` values via a slice
     iterator.  Each polynomial's coefficient vector is serialized via
     `Poly::serialize` into a big-endian byte vector.  The result populates
     `result.polys`; `result.pts` is left empty.

**Source**: spqr/src/encoding/polynomial.rs (lines 541:4-571:5)
-/

open Aeneas Aeneas.Std Result spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb`** (byte-level)

Serialization of a `PolyEncoder` into its protobuf representation
`proto.pq_ratchet.PolynomialEncoder`, with the postcondition expressed at the
raw byte level.

**Source**: spqr/src/encoding/polynomial.rs (lines 541:4-571:5)
-/
theorem into_pb_spec_bytes
    (self : encoding.polynomial.PolyEncoder)
    (h_overflow_points : ∀ points,
      self.s = .Points points →
        ∀ j < points.length,
          2 * (points[j]!).value.length + 2 ≤ Usize.max)
    (h_overflow_polys : ∀ polys,
      self.s = .Polys polys →
        ∀ j < polys.length, 2 * (polys[j]!).degree + 2 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.PolynomialEncoder) =>
      result.idx = self.idx ∧
      match self.s with
      | .Points points =>
        result.polys.val = [] ∧
        result.pts.length = points.length ∧
        ∀ j < points.length,
          ∃ (serialized : alloc.vec.Vec Std.U8),
            result.pts.val[j]? = some serialized ∧
            (result.pts[j]!).length =
              2 * (points[j]!).value.length ∧
            ∀ k < (points[j]!).value.length,
                256 * (result.pts[j]!)[2 * k]! + (result.pts[j]!)[2 * k + 1]!  =
                  ((points.val[j]!).value[k]!).value.val
      | .Polys polys =>
        result.pts.val = [] ∧
        result.polys.length = polys.length ∧
        ∀  j < polys.length,
           result.polys[j]!.length =2 * (polys.val[j]!).degree ∧
            ∀ k < (polys.val[j]!).degree,
                256 * (result.polys[j]!)[2 * k ]! + (result.polys[j]!)[2 * k + 1]! =
                  ((polys[j]!).coefficients.val[k]!).value.val ⦄ := by
  unfold into_pb
  simp only [alloc.vec.Vec.with_capacity]
  cases h : self.s with
  | Points points =>
    have h_overflow := h_overflow_points points h
    step*
    all_goals first
      | assumption
      | grind
  | Polys polys =>
    have h_overflow := h_overflow_polys polys h
    step*
    -- step* stopped at Slice.iter; unfold it manually
    simp only [core.slice.Slice.iter, bind_tc_ok]
    -- Now the goal has into_pb_loop1 with concrete iter
    step with into_pb_loop1.loop_spec by
      first
        | assumption
        | scalar_tac
        | omega
        | (simp only [s_post])
    · intros j hj
      simp_all
    · constructor
      · grind
      · simp_all
        grind

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb`**
(cascading: byte-level + algebraic)

Lifts the byte-level specification (`into_pb_spec_bytes`) to a cascading
postcondition that includes the raw byte equality **and** the derived
GF(2¹⁶) and polynomial identities.  This is marginally tighter than stating
only the algebraic consequences, because clients that need the raw equality
can use it directly without having to re-derive it.

**Source**: spqr/src/encoding/polynomial.rs (lines 541:4-571:5)
-/
@[step]
theorem into_pb_spec
    (self : encoding.polynomial.PolyEncoder)
    (h_overflow_points : ∀ points,
      self.s = .Points points →
        ∀ j < points.length, 2 * (points[j]!).value.length + 2 ≤ Usize.max)
    (h_overflow_polys : ∀ polys, self.s = .Polys polys →
        ∀ j < polys.length, 2 * (polys[j]!).degree + 2 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.PolynomialEncoder) =>
      result.idx = self.idx ∧
      match self.s with
      | .Points points =>
        result.polys.val = [] ∧
        result.pts.length = points.length ∧
        ∀ j < points.length,
            result.pts[j]!.length = 2 * (points[j]!).value.length ∧
            ∀ k < (points[j]!).value.length,
                256 * (result.pts[j]!)[2 * k]! + (result.pts[j]!)[2 * k + 1]! =
                  ((points[j]!).value[k]!).value.val ∧
                (256 * (result.pts[j]!)[2 * k]! + (result.pts[j]!)[2 * k + 1]! : ℕ).toGF216 =
                  ((points[j]!).value[k]!).value.val.toGF216 ∧
                natToBinaryPoly (256 * (result.pts[j]!)[2 * k]! + (result.pts[j]!)[2 * k + 1]!) =
                  natToBinaryPoly (((points[j]!).value[k]!).value.val)
      | .Polys polys =>
        result.pts.val = [] ∧
        result.polys.length = polys.length ∧
        ∀ j < polys.length,
            (result.polys[j]!).length =
              2 * (polys[j]!).degree ∧
            ∀ k < (polys[j]!).degree,
                 256 * (result.polys[j]!)[2 * k]! + (result.polys[j]!)[2 * k + 1]! =
                  ((polys[j]!).coefficients[k]! ).value.val ∧
                (256 * (result.polys[j]!)[2 * k]! + (result.polys[j]!)[2 * k + 1]! :ℕ ).toGF216 =
                  ((polys[j]!).coefficients[k]!).value.val.toGF216 ∧
                natToBinaryPoly (
                  256 * (result.polys[j]!)[2 * k]! + (result.polys[j]!)[2 * k + 1]! ) =
                  natToBinaryPoly (((polys[j]!).coefficients[k]!).value.val) ⦄ := by
  have h_raw := into_pb_spec_bytes self h_overflow_points h_overflow_polys
  apply WP.spec_mono h_raw
  intro result h_post
  obtain ⟨h_idx, h_data⟩ := h_post
  refine ⟨h_idx, ?_⟩
  cases h : self.s with
  | Points points =>
    simp only [h] at h_data ⊢
    obtain ⟨h_polys, h_len, h_ser⟩ := h_data
    refine ⟨h_polys, h_len, fun j hj => ?_⟩
    obtain ⟨serialized, h_some, h_slen, h_enc⟩ := h_ser j hj
    simp_all
  | Polys polys =>
    simp only [h] at h_data ⊢
    obtain ⟨h_pts, h_len, h_ser⟩ := h_data
    refine ⟨h_pts, h_len, fun j hj => ?_⟩
    obtain ⟨h_slen, h_enc⟩ := h_ser j hj
    simp_all

end spqr.encoding.polynomial.PolyEncoder
