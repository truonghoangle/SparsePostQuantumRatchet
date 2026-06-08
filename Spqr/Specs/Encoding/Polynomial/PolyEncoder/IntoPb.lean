/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
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
        ∀ (j : Nat), j < points.val.length →
          2 * (points.val[j]!).value.val.length + 2 ≤ Usize.max)
    (h_overflow_polys : ∀ polys,
      self.s = .Polys polys →
        ∀ (j : Nat), j < polys.val.length →
          2 * (polys.val[j]!).coefficients.val.length +
            2 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.PolynomialEncoder) =>
      result.idx = self.idx ∧
      match self.s with
      | .Points points =>
        result.polys.val = [] ∧
        result.pts.val.length = points.val.length ∧
        ∀ (j : Nat), j < points.val.length →
          ∃ (serialized : alloc.vec.Vec Std.U8),
            result.pts.val[j]? = some serialized ∧
            serialized.val.length =
              2 * (points.val[j]!).value.val.length ∧
            ∀ (k : Nat),
              k < (points.val[j]!).value.val.length →
              ∃ (hi lo : Std.U8),
                serialized.val[2 * k]? = some hi ∧
                serialized.val[2 * k + 1]? = some lo ∧
                hi.val * 256 + lo.val =
                  ((points.val[j]!).value.val[k]!).value.val
      | .Polys polys =>
        result.pts.val = [] ∧
        result.polys.val.length = polys.val.length ∧
        ∀ (j : Nat), j < polys.val.length →
          ∃ (serialized : alloc.vec.Vec Std.U8),
            result.polys.val[j]? = some serialized ∧
            serialized.val.length =
              2 * (polys.val[j]!).coefficients.val.length ∧
            ∀ (k : Nat),
              k < (polys.val[j]!).coefficients.val.length →
              ∃ (hi lo : Std.U8),
                serialized.val[2 * k]? = some hi ∧
                serialized.val[2 * k + 1]? = some lo ∧
                hi.val * 256 + lo.val =
                  ((polys.val[j]!).coefficients.val[k]!
                    ).value.val ⦄ := by
  unfold into_pb
  simp only [alloc.vec.Vec.with_capacity]
  cases h : self.s with
  | Points points =>
    have h_overflow := h_overflow_points points h
    step*
    all_goals first
      | assumption
      | scalar_tac
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
        | (simp only [s_post, Array.val_to_slice]; exact h_overflow)
    constructor
    · simp_all
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
        ∀ (j : Nat), j < points.val.length →
          2 * (points.val[j]!).value.val.length + 2 ≤ Usize.max)
    (h_overflow_polys : ∀ polys,
      self.s = .Polys polys →
        ∀ (j : Nat), j < polys.val.length →
          2 * (polys.val[j]!).coefficients.val.length +
            2 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.PolynomialEncoder) =>
      result.idx = self.idx ∧
      match self.s with
      | .Points points =>
        result.polys.val = [] ∧
        result.pts.val.length = points.val.length ∧
        ∀ (j : Nat), j < points.val.length →
          ∃ (serialized : alloc.vec.Vec Std.U8),
            result.pts.val[j]? = some serialized ∧
            serialized.val.length =
              2 * (points.val[j]!).value.val.length ∧
            ∀ (k : Nat),
              k < (points.val[j]!).value.val.length →
              ∃ (hi lo : Std.U8),
                serialized.val[2 * k]? = some hi ∧
                serialized.val[2 * k + 1]? = some lo ∧
                hi.val * 256 + lo.val =
                  ((points.val[j]!).value.val[k]!).value.val ∧
                (hi.val * 256 + lo.val).toGF216 =
                  ((points.val[j]!).value.val[k]!
                    ).value.val.toGF216 ∧
                natToBinaryPoly (hi.val * 256 + lo.val) =
                  natToBinaryPoly
                    (((points.val[j]!).value.val[k]!
                      ).value.val)
      | .Polys polys =>
        result.pts.val = [] ∧
        result.polys.val.length = polys.val.length ∧
        ∀ (j : Nat), j < polys.val.length →
          ∃ (serialized : alloc.vec.Vec Std.U8),
            result.polys.val[j]? = some serialized ∧
            serialized.val.length =
              2 * (polys.val[j]!).coefficients.val.length ∧
            ∀ (k : Nat),
              k < (polys.val[j]!).coefficients.val.length →
              ∃ (hi lo : Std.U8),
                serialized.val[2 * k]? = some hi ∧
                serialized.val[2 * k + 1]? = some lo ∧
                hi.val * 256 + lo.val =
                  ((polys.val[j]!).coefficients.val[k]!
                    ).value.val ∧
                (hi.val * 256 + lo.val).toGF216 =
                  ((polys.val[j]!).coefficients.val[k]!
                    ).value.val.toGF216 ∧
                natToBinaryPoly (hi.val * 256 + lo.val) =
                  natToBinaryPoly
                    (((polys.val[j]!).coefficients.val[k]!
                      ).value.val) ⦄ := by
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
    refine ⟨serialized, h_some, h_slen, fun k hk => ?_⟩
    obtain ⟨hi, lo, hhi, hlo, h_eq⟩ := h_enc k hk
    exact ⟨hi, lo, hhi, hlo, h_eq,
      congr_arg Nat.toGF216 h_eq,
      congr_arg natToBinaryPoly h_eq⟩
  | Polys polys =>
    simp only [h] at h_data ⊢
    obtain ⟨h_pts, h_len, h_ser⟩ := h_data
    refine ⟨h_pts, h_len, fun j hj => ?_⟩
    obtain ⟨serialized, h_some, h_slen, h_enc⟩ := h_ser j hj
    refine ⟨serialized, h_some, h_slen, fun k hk => ?_⟩
    obtain ⟨hi, lo, hhi, hlo, h_eq⟩ := h_enc k hk
    exact ⟨hi, lo, hhi, hlo, h_eq,
      congr_arg Nat.toGF216 h_eq,
      congr_arg natToBinaryPoly h_eq⟩

end spqr.encoding.polynomial.PolyEncoder
