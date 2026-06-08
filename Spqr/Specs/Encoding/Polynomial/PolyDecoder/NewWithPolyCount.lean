/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.CallMut
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.CallOnce
import Spqr.Specs.Encoding.Polynomial.PolynomialError.From
/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::new_with_poly_count`

A `PolyDecoder` wraps three fields:
  • `pts_needed : usize` — the total number of evaluation points still needed for decoding.
  • `pts : [SortedSet<Pt>; 16]` — a fixed-size array of 16 sorted sets of evaluation points,
     one per polynomial.
  • `is_complete : bool` — whether the decoder has collected enough points to decode.

The constructor `new_with_poly_count` builds a fresh `PolyDecoder` from a target message length
`len_bytes` (in bytes) and a polynomial-count parameter `_polys` (which is ignored — the array
length is hard-coded to `NUM_POLYS = 16`).  The function proceeds in two stages:

  1. **Input validation** — the message length must be even (`len_bytes % 2 == 0`).
     Otherwise the function returns `Err(PolynomialError::MessageLengthEven)`,
     lifted into `EncodingError` via the `From<PolynomialError>` instance.

  2. **Decoder construction** — if `len_bytes` is even, the function returns
     `Ok(PolyDecoder { pts_needed := len_bytes / 2, pts := [SortedSet::new(); 16],
                       is_complete := false })`.
     The array of 16 empty sorted sets is materialised by
     `core::array::from_fn(|_| SortedSet::new())`,
     whose per-element closure is the unit-state `FnMut` extracted as
     `new_with_poly_count.closure.Insts.CoreOpsFunctionFnMutTupleUsizeSortedSetPt`
     (specified in `CallMut.lean` / `CallOnce.lean`).

Since `len_bytes` is encoded as 16 bits of GF(2¹⁶) data per evaluation point, dividing by 2 yields
the total number of evaluation points required to reconstruct the encoded message via Lagrange
interpolation over GF(2¹⁶) ≅ GF(2)[X] / (x¹⁶ + x¹² + x³ + x + 1).

**Source**: spqr/src/encoding/polynomial.rs (lines 782:4-791:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

namespace spqr.encoding.polynomial.PolyDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.new_with_poly_count`** (nat-level):

`new_with_poly_count` is the validating constructor for `PolyDecoder`.  Given a byte-length
`len_bytes` and an (ignored) polynomial-count parameter `_polys`, the function:

• Returns `Err(EncodingError.PolynomialError MessageLengthEven)` when `len_bytes.val % 2 ≠ 0`.

• Otherwise returns `Ok(PolyDecoder { pts_needed, pts, is_complete })` where
    - `pts_needed.val = len_bytes.val / 2`,
    - `pts.val = List.replicate 16 default` — an array of 16 default (empty) `SortedSet Pt`
      values, materialised by `core::array::from_fn(|_| SortedSet::new())`,
    - `is_complete = false`.

The arithmetic steps (`len_bytes % 2`, `len_bytes / 2`) never fail since the divisor `2` is
nonzero.  Array construction never fails because `core.array.from_fn` is modelled as the
constant function returning `default` (see `Spqr/Code/FunsExternal.lean`).

**Source**: spqr/src/encoding/polynomial.rs (lines 782:4-791:5)
-/
theorem new_with_poly_count_spec_nat (len_bytes _polys : Std.Usize) :
    new_with_poly_count len_bytes _polys ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder encoding.EncodingError) =>
      if len_bytes.val % 2 = 0 then
        ∃ (pts : Array (sorted_vec.SortedSet Pt) 16#usize),
          pts.val = List.replicate 16 default ∧
          result = core.result.Result.Ok
            { pts_needed := ⟨len_bytes.val / 2, by
                have : len_bytes.val / 2 ≤ len_bytes.val := Nat.div_le_self _ _
                exact Nat.lt_of_le_of_lt this len_bytes.hBounds⟩,
              pts := pts,
              is_complete := false }
      else
        result = core.result.Result.Err
          (encoding.EncodingError.PolynomialError
            encoding.polynomial.PolynomialError.MessageLengthEven) ⦄ := by
  unfold new_with_poly_count
  step*
  · split
    · grind
    · grind
  · split
    · simp_all only [bne_iff_ne, ne_eq, UScalar.neq_to_neq_val, UScalar.ofNatCore_val_eq,
      not_true_eq_false, not_false_eq_true, List.reduceReplicate, UScalarTy.Usize_numBits_eq,
      core.result.Result.Ok.injEq, mk.injEq, and_true, exists_eq_right_right', true_and]
      apply UScalar.val_eq_imp
      simp_all
      rfl
    · grind

/--
`new_with_poly_count` is the public constructor used by the `Decoder` trait to initialise a
`PolyDecoder` from a target message length.  This re-statement of `new_with_poly_count_spec_nat`
exposes the same postcondition through the `step` attribute so downstream proofs can dispatch
the call automatically.

The decoder starts with:
  • `pts_needed = len_bytes / 2` — the total number of `(x, y)` evaluation points required to
    decode the message via Lagrange interpolation (one point per 2 bytes, since each GF(2¹⁶)
    element fits in 2 bytes).
  • `pts = [∅; 16]` — 16 empty sorted sets, one slot per polynomial (`NUM_POLYS = 16`).
  • `is_complete = false` — no points have been received yet.

Validation enforces the invariant `len_bytes % 2 = 0` required by `MessageLengthEven` — the
companion check on the encoding side (`PolyEncoder::encode_bytes`).

**Source**: spqr/src/encoding/polynomial.rs (lines 782:4-791:5)
-/
@[step]
theorem new_with_poly_count_spec (len_bytes _polys : Std.Usize) :
    new_with_poly_count len_bytes _polys ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder encoding.EncodingError) =>
      if len_bytes.val % 2 = 0 then
        ∃ (pts : Array (sorted_vec.SortedSet Pt) 16#usize),
          pts.val = List.replicate 16 default ∧
          result = core.result.Result.Ok
            { pts_needed := ⟨len_bytes.val / 2, by
                have : len_bytes.val / 2 ≤ len_bytes.val := Nat.div_le_self _ _
                exact Nat.lt_of_le_of_lt this len_bytes.hBounds⟩,
              pts := pts,
              is_complete := false }
      else
        result = core.result.Result.Err
          (encoding.EncodingError.PolynomialError
            encoding.polynomial.PolynomialError.MessageLengthEven) ⦄ :=
  new_with_poly_count_spec_nat len_bytes _polys

end spqr.encoding.polynomial.PolyDecoder
