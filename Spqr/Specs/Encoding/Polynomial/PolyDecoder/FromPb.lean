/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.ModByMonic
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FromPbLoop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::from_pb`

The function `PolyDecoder::from_pb` reconstructs a `PolyDecoder` — which holds a target point
count `pts_needed : Usize`, a fixed-size array `pts : [SortedSet<Pt>; 16]` of cartesian
evaluation points over GF(2¹⁶) × GF(2¹⁶), and an `is_complete : bool` flag — from its
protobuf representation `proto::pq_ratchet::PolynomialDecoder`.

The function proceeds in three stages:
  1. **Length validation.**  If `pb.pts.len() != 16` then
     `Err(PolynomialError::SerializationInvalid)` is returned.  Otherwise each of the 16
     serialized byte vectors `pb.pts[i]` is checked for `len() % 4 == 0`; if *any* slot fails
     this check the function short-circuits with the same `SerializationInvalid` error.
  2. **Per-slot deserialization.**  After validation, a fresh `[SortedSet<Pt>; 16]` is
     allocated (16 copies of `SortedSet::new()`).  The outer loop `from_pb_loop0` then
     iterates over slot indices `0..16`.  For each slot, `SortedSet::with_capacity(pts.len()/4)`
     allocates a fresh sorted set, and the inner 4-byte-chunk loop populates it with
     cartesian points decoded from `pb.pts[i]` in big-endian form
     (`p.x.value = pb.pts[i][4·k]·256 + pb.pts[i][4·k+1]`,
      `p.y.value = pb.pts[i][4·k+2]·256 + pb.pts[i][4·k+3]`).
  3. **Result assembly.**  Casts `pb.pts_needed : u32` to `usize` (always succeeds since
     `U32.max ≤ Usize.max`) and packages the result as
     `Ok { pts_needed := (pb.pts_needed as usize), pts := out_pts, is_complete := pb.is_complete }`.

In GF(2¹⁶) (characteristic 2), each field element is stored as a `u16`, and a `Pt` packs two
such elements `(x, y)`.  The 4-byte big-endian decoding satisfies, in the canonical isomorphism
GF(2¹⁶) ≅ GF(2)[X]/(polyGF2):

  `p.x.value.toGF216 = (b0·256 + b1).toGF216`   and
  `p.y.value.toGF216 = (b2·256 + b3).toGF216`,

so `from_pb` is the byte-level left inverse of `into_pb` for valid inputs.

**Source**: spqr/src/encoding/polynomial.rs (lines 815:4-854:5)
-/

open Aeneas Aeneas.Std Result spqr.math.gf spqr.encoding.polynomial

namespace spqr.encoding.polynomial.PolyDecoder

set_option maxHeartbeats 4000000 in
/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb`** (byte-level):

Deserialization of a `proto.pq_ratchet.PolynomialDecoder` into a `PolyDecoder`, with the
postcondition expressed at the raw byte level.

The result is a conjunction of three branches mirroring the structure of the Rust function:

  * **Bad length branch**: when `pb.pts.val.length ≠ 16`, the result is
    `Err(SerializationInvalid)`.
  * **Bad chunking branch**: when `pb.pts.val.length = 16` but some slot fails
    `len() % 4 = 0`, the result is `Err(SerializationInvalid)`.
  * **Valid branch**: when `pb.pts.val.length = 16` and every slot satisfies
    `(pb.pts[j]).len() % 4 = 0`, the result is `Ok decoder` with:
      - `decoder.pts_needed.val = pb.pts_needed.val` — the `Usize`-cast of the protobuf
        `u32` point count succeeds and preserves the value.
      - `decoder.is_complete = pb.is_complete` — completion flag preserved.
      - `decoder.pts.val.length = 16` — exactly 16 `SortedSet<Pt>` slots.
      - For every slot `j < 16`, there exist a final sorted set `v_final`, an iteration
        count `n : Nat`, and a chain `vs : Nat → SortedSet Pt` such that
          `decoder.pts.val[j]! = v_final`, `vs n = v_final`,
          `4 · n ≤ (pb.pts[j]).len() < 4 · (n + 1)`,
          and for every `k < n` there exist a cartesian point `p : Pt`
          (over GF(2¹⁶) × GF(2¹⁶)) and `SortedSet.push`-outputs `(m, o)` with
            `p.x.value.val = pb.pts[j][4·k]·256   + pb.pts[j][4·k+1]`,
            `p.y.value.val = pb.pts[j][4·k+2]·256 + pb.pts[j][4·k+3]`,
            `SortedSet.push (vs k) p = ok ((m, o), vs (k+1))`.

Because both `sorted_vec.SortedSet.with_capacity` and `sorted_vec.SortedSet.push` are extracted
as opaque axioms, we parameterise the spec by an index-dependent witness
`v_init : Std.Usize → SortedSet Pt` for the `with_capacity` axiom, and the postcondition only
asserts the existence of a chain of intermediate sorted-set states linked by valid push
equations.

This follows from composing:
  1. The 16 modulo guards — discharged by the `% 4 = 0` hypothesis in the valid branch.
  2. `sorted_vec.SortedSet.new_spec` — initialises the 16-slot output array with `default`.
  3. `from_pb_loop0.loop_spec`: drives the outer deserialization loop, producing for every
     slot the chain of `SortedSet.push` operations corresponding to the big-endian 4-byte
     decoded cartesian points.
  4. `UScalar.cast` — succeeds because `U32.max ≤ Usize.max`.

**Source**: spqr/src/encoding/polynomial.rs (lines 815:4-854:5)
-/
theorem from_pb_spec_nat
    (pb : proto.pq_ratchet.PolynomialDecoder)
    (v_init : Std.Usize → sorted_vec.SortedSet Pt)
    (h_init : ∀ (n : Std.Usize),
        sorted_vec.SortedSet.with_capacity Pt.Insts.CoreCmpOrd n
          = ok (v_init n))
    (h_pts_overflow : ∀ (j : Nat), j < pb.pts.val.length →
        (pb.pts.val[j]!).val.length + 4 ≤ Usize.max) :
    from_pb pb ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder
        encoding.polynomial.PolynomialError) =>
      -- Bad length: returns Err
      (pb.pts.val.length ≠ 16 →
        result = core.result.Result.Err
          encoding.polynomial.PolynomialError.SerializationInvalid) ∧
      -- Bad chunking: some slot has length not a multiple of 4
      (pb.pts.val.length = 16 →
        (∃ (j : Nat), j < 16 ∧ (pb.pts.val[j]!).val.length % 4 ≠ 0) →
        result = core.result.Result.Err
          encoding.polynomial.PolynomialError.SerializationInvalid) ∧
      -- Valid: every slot has length a multiple of 4, result is Ok with chain witnesses
      (pb.pts.val.length = 16 →
        (∀ (j : Nat), j < 16 → (pb.pts.val[j]!).val.length % 4 = 0) →
        ∃ (decoder : encoding.polynomial.PolyDecoder),
          result = core.result.Result.Ok decoder ∧
          decoder.pts_needed.val = pb.pts_needed.val ∧
          decoder.is_complete = pb.is_complete ∧
          decoder.pts.val.length = 16 ∧
          ∀ (j : Nat), j < 16 →
            ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
              (vs : Nat → sorted_vec.SortedSet Pt),
              decoder.pts.val[j]! = v_final ∧
              vs n = v_final ∧
              4 * n ≤ (pb.pts.val[j]!).val.length ∧
              (pb.pts.val[j]!).val.length < 4 * (n + 1) ∧
              ∀ (k : Nat), k < n →
                ∃ (p : Pt) (m : Std.Usize) (o : Option Pt),
                  p.x.value.val =
                    ((pb.pts.val[j]!).val[4 * k]!).val * 256 +
                    ((pb.pts.val[j]!).val[4 * k + 1]!).val ∧
                  p.y.value.val =
                    ((pb.pts.val[j]!).val[4 * k + 2]!).val * 256 +
                    ((pb.pts.val[j]!).val[4 * k + 3]!).val ∧
                  sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd (vs k) p =
                    ok ((m, o), vs (k + 1))) ⦄ := by
  -- This spec packages a 16-modulo-guard cascade plus a 16-slot deserialization
  -- loop into a single tri-branch postcondition.  The proof is by symbolic
  -- execution of `from_pb`, dispatching each `if ... != 0` branch to the
  -- appropriate clause of the disjunction; the valid branch is discharged by
  -- `from_pb_loop0.loop_spec` (registered as `@[step]`).
  unfold from_pb
  simp [sorted_vec.SortedSet.new]
  step*
  -- All goals (16 Err-branches + 1 Ok-branch) are now closed structural
  -- post-conditions over a triple-conjunction.  The Err-branches each carry a
  -- hypothesis `(i != 0#usize) = true` for some intermediate modulo, which
  -- contradicts the third-conjunct `% 4 = 0` premise (and trivially satisfies
  -- the first/second Err conjuncts).  The Ok-branch packages the loop's
  -- output through `out_pts_post`.
  · simp_all
    intro x hx
    interval_cases x <;> assumption
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind




/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb`** (cascading: byte-level +
algebraic):

Lifts the byte-level specification (`from_pb_spec_nat`) to a cascading postcondition that
includes the raw byte equality **and** the derived GF(2¹⁶) and polynomial identities for each
decoded coordinate of every cartesian point.  Specializing the canonical ring-homomorphism
`BinaryPoly.toGF216 : BinaryPoly →+* GF216` (which vanishes on `polyGF2`) recovers the
GF(2¹⁶)-level interpretation of the decoded bytes via `Nat.toGF216`.
-/
@[step]
theorem from_pb_spec
    (pb : proto.pq_ratchet.PolynomialDecoder)
    (v_init : Std.Usize → sorted_vec.SortedSet Pt)
    (h_init : ∀ (n : Std.Usize),
        sorted_vec.SortedSet.with_capacity Pt.Insts.CoreCmpOrd n
          = ok (v_init n))
    (h_pts_overflow : ∀ (j : Nat), j < pb.pts.val.length →
        (pb.pts.val[j]!).val.length + 4 ≤ Usize.max) :
    from_pb pb ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder
        encoding.polynomial.PolynomialError) =>
      -- Bad length: returns Err
      (pb.pts.val.length ≠ 16 →
        result = core.result.Result.Err
          encoding.polynomial.PolynomialError.SerializationInvalid) ∧
      -- Bad chunking: some slot has length not a multiple of 4
      (pb.pts.val.length = 16 →
        (∃ (j : Nat), j < 16 ∧ (pb.pts.val[j]!).val.length % 4 ≠ 0) →
        result = core.result.Result.Err
          encoding.polynomial.PolynomialError.SerializationInvalid) ∧
      -- Valid: every slot has length a multiple of 4, result is Ok with chain witnesses
      (pb.pts.val.length = 16 →
        (∀ (j : Nat), j < 16 → (pb.pts.val[j]!).val.length % 4 = 0) →
        ∃ (decoder : encoding.polynomial.PolyDecoder),
          result = core.result.Result.Ok decoder ∧
          decoder.pts_needed.val = pb.pts_needed.val ∧
          decoder.is_complete = pb.is_complete ∧
          decoder.pts.val.length = 16 ∧
          ∀ (j : Nat), j < 16 →
            ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
              (vs : Nat → sorted_vec.SortedSet Pt),
              decoder.pts.val[j]! = v_final ∧
              vs n = v_final ∧
              4 * n ≤ (pb.pts.val[j]!).val.length ∧
              (pb.pts.val[j]!).val.length < 4 * (n + 1) ∧
              ∀ (k : Nat), k < n →
                ∃ (p : Pt) (m : Std.Usize) (o : Option Pt),
                  p.x.value.val =
                    ((pb.pts.val[j]!).val[4 * k]!).val * 256 +
                    ((pb.pts.val[j]!).val[4 * k + 1]!).val ∧
                  p.y.value.val =
                    ((pb.pts.val[j]!).val[4 * k + 2]!).val * 256 +
                    ((pb.pts.val[j]!).val[4 * k + 3]!).val ∧
                  sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd (vs k) p =
                    ok ((m, o), vs (k + 1)) ∧
                  (p.x.value.val).toGF216 =
                    (((pb.pts.val[j]!).val[4 * k]!).val * 256 +
                     ((pb.pts.val[j]!).val[4 * k + 1]!).val).toGF216 ∧
                  (p.y.value.val).toGF216 =
                    (((pb.pts.val[j]!).val[4 * k + 2]!).val * 256 +
                     ((pb.pts.val[j]!).val[4 * k + 3]!).val).toGF216 ∧
                  natToBinaryPoly p.x.value.val =
                    natToBinaryPoly
                      (((pb.pts.val[j]!).val[4 * k]!).val * 256 +
                       ((pb.pts.val[j]!).val[4 * k + 1]!).val) ∧
                  natToBinaryPoly p.y.value.val =
                    natToBinaryPoly
                      (((pb.pts.val[j]!).val[4 * k + 2]!).val * 256 +
                       ((pb.pts.val[j]!).val[4 * k + 3]!).val)) ⦄ := by
  have h_raw := from_pb_spec_nat pb v_init h_init h_pts_overflow
  apply WP.spec_mono h_raw
  intro result h_post
  obtain ⟨h_bad_len, h_bad_chunk, h_valid⟩ := h_post
  refine ⟨h_bad_len, h_bad_chunk, fun h_len h_mod => ?_⟩
  obtain ⟨decoder, h_ok, h_idx, h_done, h_dlen, h_slots⟩ :=
    h_valid h_len h_mod
  refine ⟨decoder, h_ok, h_idx, h_done, h_dlen, fun j hj => ?_⟩
  obtain ⟨v_final, n, vs, h_slot, h_vs_n, h_n_lo, h_n_hi, h_chain⟩ :=
    h_slots j hj
  refine ⟨v_final, n, vs, h_slot, h_vs_n, h_n_lo, h_n_hi, fun k hk => ?_⟩
  obtain ⟨p, m, o, h_px, h_py, h_push⟩ := h_chain k hk
  exact ⟨p, m, o, h_px, h_py, h_push,
    congr_arg Nat.toGF216 h_px,
    congr_arg Nat.toGF216 h_py,
    congr_arg natToBinaryPoly h_px,
    congr_arg natToBinaryPoly h_py⟩

end spqr.encoding.polynomial.PolyDecoder
