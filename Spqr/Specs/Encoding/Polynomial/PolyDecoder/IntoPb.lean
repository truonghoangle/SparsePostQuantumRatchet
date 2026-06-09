/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPbLoop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::into_pb`

The function `PolyDecoder::into_pb` converts a `PolyDecoder` — which holds a target point
count `pts_needed : Usize`, a fixed-size array `pts : [SortedSet<Pt>; 16]` of cartesian
evaluation points over GF(2¹⁶) × GF(2¹⁶), and an `is_complete : bool` flag — into its
protobuf representation `proto::pq_ratchet::PolynomialDecoder`.

The function proceeds in three stages:
  1. `UScalar.cast .U32 self.pts_needed` — checked narrowing of the `usize` point count to
     `u32` (succeeds whenever `self.pts_needed.val ≤ U32.max`).
  2. The serialization loop `into_pb_loop0` iterates over each of the 16 `SortedSet<Pt>` slots
     via a slice iterator.  For each slot, both deref operations
     (`SortedSet → SortedVec → Vec<Pt>`) are unfolded to expose the underlying point vector
     `inner`, and each `pt : Pt = ⟨x, y⟩ ∈ inner` is serialized as four big-endian bytes
     satisfying `b0·256 + b1 = x.value` and `b2·256 + b3 = y.value`.
  3. Packages the result as `{ pts_needed := (pts_needed as u32), polys := 16, pts := serialized,
     is_complete }`.

In GF(2¹⁶) (characteristic 2), each field element is stored as a `u16`, and a `Pt` packs two
such elements `(x, y)`.  The 4-byte serialization satisfies, in the canonical isomorphism
GF(2¹⁶) ≅ GF(2)[X]/(polyGF2):

  `(b0·256 + b1).toGF216 = x.value.toGF216`   and
  `(b2·256 + b3).toGF216 = y.value.toGF216`.

**Source**: spqr/src/encoding/polynomial.rs (lines 793:4-811:5)
-/

open Aeneas Aeneas.Std Result spqr.math.gf spqr.encoding.polynomial

namespace spqr.encoding.polynomial.PolyDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb`** (byte-level):

Serialization of a `PolyDecoder` into its protobuf representation
`proto.pq_ratchet.PolynomialDecoder`, with the postcondition expressed at the raw byte level.

The result satisfies:
  * `result.pts_needed.val = self.pts_needed.val` — the `U32`-cast of the point count equals
    the original `Usize` value (succeeds by `h_pts_needed_fits`).
  * `result.polys = 16#u32` — the fixed `u32` constant declaring 16 polynomial slots.
  * `result.is_complete = self.is_complete` — completion flag preserved.
  * `result.pts.val.length = 16` — exactly one serialized byte vector per `SortedSet<Pt>` slot.
  * For every slot `j < 16`, the `j`-th serialized vector encodes the underlying point vector
    `inner j` of the `j`-th `SortedSet`:
      `∃ serialized, result.pts.val[j]? = some serialized ∧
        serialized.val.length = 4 * (inner j).val.length ∧
        ∀ k < (inner j).val.length, ∃ b0 b1 b2 b3,
          serialized.val[4*k]?   = some b0 ∧
          serialized.val[4*k+1]? = some b1 ∧
          serialized.val[4*k+2]? = some b2 ∧
          serialized.val[4*k+3]? = some b3 ∧
          b0.val·256 + b1.val = ((inner j).val[k]!).x.value.val ∧
          b2.val·256 + b3.val = ((inner j).val[k]!).y.value.val`.

Because both `SortedSet → SortedVec` and `SortedVec → Vec<Pt>` deref operations are extracted
as opaque axioms, we parameterise the spec by their hypothetical witnesses `sv` and `inner`,
together with the `h_sv` and `h_inner` hypotheses asserting that they are indeed the deref
results at each index.

This follows from composing:
  1. `UScalar.cast` — succeeds because `self.pts_needed.val ≤ U32.max`.
  2. `Array.to_slice` — produces a slice with the same backing list (length 16).
  3. `into_pb_loop0.loop_spec`: the loop drives the body to completion, producing a vector of
     length 16 where each entry is the big-endian 4-byte serialization of the corresponding
     `inner j`.

**Source**: spqr/src/encoding/polynomial.rs (lines 793:4-811:5)
-/
theorem into_pb_spec_nat
    (self : encoding.polynomial.PolyDecoder)
    (h_pts_needed_fits : self.pts_needed.val ≤ U32.max)
    (sv : Nat → sorted_vec.SortedVec Pt)
    (inner : Nat → alloc.vec.Vec Pt)
    (h_sv : ∀ (k : Nat) (h : k < self.pts.val.length),
      sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
        Pt.Insts.CoreCmpOrd (self.pts.val[k]'h) = ok (sv k))
    (h_inner : ∀ (k : Nat), k < self.pts.val.length →
      sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
        Pt.Insts.CoreCmpOrd (sv k) = ok (inner k))
    (h_inner_overflow : ∀ (k : Nat), k < self.pts.val.length →
        4 * (inner k).val.length + 4 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.PolynomialDecoder) =>
      result.pts_needed.val = self.pts_needed.val ∧
      result.polys = 16#u32 ∧
      result.is_complete = self.is_complete ∧
      result.pts.val.length = self.pts.val.length ∧
      ∀ (j : Nat), j < self.pts.val.length →
        ∃ (serialized : alloc.vec.Vec Std.U8),
          result.pts.val[j]? = some serialized ∧
          serialized.val.length = 4 * (inner j).val.length ∧
          ∀ (k : Nat), k < (inner j).val.length →
            ∃ (b0 b1 b2 b3 : Std.U8),
              serialized.val[4 * k]?     = some b0 ∧
              serialized.val[4 * k + 1]? = some b1 ∧
              serialized.val[4 * k + 2]? = some b2 ∧
              serialized.val[4 * k + 3]? = some b3 ∧
              b0.val * 256 + b1.val = ((inner j).val[k]!).x.value.val ∧
              b2.val * 256 + b3.val = ((inner j).val[k]!).y.value.val ⦄ := by
  unfold into_pb
  simp only [alloc.vec.Vec.with_capacity]
  step*
  -- step* stops at Slice.iter; unfold it manually so the concrete iter is exposed
  simp only [core.slice.Slice.iter, bind_tc_ok]
  step with into_pb_loop0.loop_spec
    (sv := sv) (inner := inner) by
    first
      | assumption
      | scalar_tac
      | omega
      | (simp only [s1_post, Array.val_to_slice]; exact h_sv)
      | (simp only [s1_post, Array.val_to_slice]; exact h_inner)
      | (simp only [s1_post, Array.val_to_slice]; exact h_inner_overflow)
  -- Postcondition: combine the loop's output with the U32-cast of pts_needed.
  -- After `step*`, the framework auto-discharges the `pts_needed.val`, `polys`,
  -- `is_complete`, and `length` components from the constructor of `result`,
  -- leaving the cast bound and the per-slot byte witnesses.
  refine ⟨?_, ?_, ?_⟩
  · -- U32 cast of `pts_needed` preserves the underlying value
    simp_all [UScalar.cast_val_eq]; scalar_tac
  · -- Length is propagated from the loop output
    simp_all [Array.val_to_slice]
  · -- Per-slot byte witnesses are exactly the loop's `v1_post2`
    intro j hj
    have h_j : j < (s1.val).length := by simp_all [Array.val_to_slice]
    exact v1_post2 j h_j

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb`** (cascading: byte-level +
algebraic):

Lifts the byte-level specification (`into_pb_spec_nat`) to a cascading postcondition that
includes the raw byte equality **and** the derived GF(2¹⁶) and polynomial identities for each
encoded coordinate of every cartesian point.  Specializing the canonical ring-homomorphism
`BinaryPoly.toGF216 : BinaryPoly →+* GF216` (which vanishes on `polyGF2`) recovers the
GF(2¹⁶)-level interpretation of the serialized bytes via `Nat.toGF216`.
-/
@[step]
theorem into_pb_spec
    (self : encoding.polynomial.PolyDecoder)
    (h_pts_needed_fits : self.pts_needed.val ≤ U32.max)
    (sv : Nat → sorted_vec.SortedVec Pt)
    (inner : Nat → alloc.vec.Vec Pt)
    (h_sv : ∀ (k : Nat) (h : k < self.pts.val.length),
      sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
        Pt.Insts.CoreCmpOrd (self.pts.val[k]'h) = ok (sv k))
    (h_inner : ∀ (k : Nat), k < self.pts.val.length →
      sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
        Pt.Insts.CoreCmpOrd (sv k) = ok (inner k))
    (h_inner_overflow : ∀ (k : Nat), k < self.pts.val.length →
        4 * (inner k).val.length + 4 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.PolynomialDecoder) =>
      result.pts_needed.val = self.pts_needed.val ∧
      result.polys = 16#u32 ∧
      result.is_complete = self.is_complete ∧
      result.pts.val.length = self.pts.val.length ∧
      ∀ (j : Nat), j < self.pts.val.length →
        ∃ (serialized : alloc.vec.Vec Std.U8),
          result.pts.val[j]? = some serialized ∧
          serialized.val.length = 4 * (inner j).val.length ∧
          ∀ (k : Nat), k < (inner j).val.length →
            ∃ (b0 b1 b2 b3 : Std.U8),
              serialized.val[4 * k]?     = some b0 ∧
              serialized.val[4 * k + 1]? = some b1 ∧
              serialized.val[4 * k + 2]? = some b2 ∧
              serialized.val[4 * k + 3]? = some b3 ∧
              b0.val * 256 + b1.val = ((inner j).val[k]!).x.value.val ∧
              b2.val * 256 + b3.val = ((inner j).val[k]!).y.value.val ∧
              (b0.val * 256 + b1.val).toGF216 =
                ((inner j).val[k]!).x.value.val.toGF216 ∧
              (b2.val * 256 + b3.val).toGF216 =
                ((inner j).val[k]!).y.value.val.toGF216 ∧
              natToBinaryPoly (b0.val * 256 + b1.val) =
                natToBinaryPoly (((inner j).val[k]!).x.value.val) ∧
              natToBinaryPoly (b2.val * 256 + b3.val) =
                natToBinaryPoly (((inner j).val[k]!).y.value.val) ⦄ := by
  have h_raw :=
    into_pb_spec_nat self h_pts_needed_fits sv inner h_sv h_inner h_inner_overflow
  apply WP.spec_mono h_raw
  intro result h_post
  obtain ⟨h_idx, h_polys, h_done, h_len, h_ser⟩ := h_post
  refine ⟨h_idx, h_polys, h_done, h_len, fun j hj => ?_⟩
  obtain ⟨serialized, h_some, h_slen, h_enc⟩ := h_ser j hj
  refine ⟨serialized, h_some, h_slen, fun k hk => ?_⟩
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, h_x, h_y⟩ := h_enc k hk
  exact ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, h_x, h_y,
    congr_arg Nat.toGF216 h_x,
    congr_arg Nat.toGF216 h_y,
    congr_arg natToBinaryPoly h_x,
    congr_arg natToBinaryPoly h_y⟩

end spqr.encoding.polynomial.PolyDecoder
