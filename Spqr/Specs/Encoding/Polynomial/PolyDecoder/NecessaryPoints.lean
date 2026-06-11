/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::necessary_points`

A `PolyDecoder` wraps three fields:
  • `pts_needed : usize` — the total number of evaluation points still needed for decoding.
  • `pts : [SortedSet<Pt>; 16]` — a fixed-size array of 16 sorted sets of evaluation points,
     one per polynomial.
  • `is_complete : bool` — whether the decoder has collected enough points to decode.

The function `necessary_points` computes how many evaluation points a given polynomial (indexed
by `poly`) requires. It distributes `pts_needed` total points across 16 polynomials using
Euclidean division:
  1. Each polynomial gets the base allocation `pts_needed / 16`.
  2. The first `pts_needed % 16` polynomials each receive one additional point.

This is the standard balanced-distribution ("round-robin") pattern:
  `necessary_points(self, poly) = pts_needed / 16 + (if poly < pts_needed % 16 then 1 else 0)`

The function always succeeds:
  • Division and modulo by 16 (nonzero) cannot fail.
  • The addition `pts_needed / 16 + 1` cannot overflow since
    `pts_needed / 16 + 1 ≤ Usize.max / 16 + 1 ≤ Usize.max`.

**Source**: spqr/src/encoding/polynomial.rs (lines 771:4-779:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.PolyDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.necessary_points`**:

`necessary_points` distributes `pts_needed` evaluation points across 16 polynomials using
Euclidean division:
  `result.val = self.pts_needed.val / 16 + if poly.val < self.pts_needed.val % 16 then 1 else 0`

• The function always succeeds (no panic / no error) for any `PolyDecoder` and `poly` input.
  Division and modulo by 16 are infallible, and the potential `+1` cannot overflow `usize`
  because `pts_needed / 16 + 1 ≤ (Scalar.max .Usize) / 16 + 1 ≤ Scalar.max .Usize`.
• The result distributes the total point budget evenly: the first `pts_needed % 16` polynomials
  receive `⌈pts_needed / 16⌉` points and the remaining polynomials receive `⌊pts_needed / 16⌋`.

**Source**: spqr/src/encoding/polynomial.rs (lines 771:4-779:5)
-/
@[step]
theorem necessary_points_spec (self : encoding.polynomial.PolyDecoder) (poly : Std.Usize) :
    necessary_points self poly ⦃ (result : Std.Usize) =>
      result.val = self.pts_needed.val / 16 +
        if poly.val < self.pts_needed.val % 16 then 1 else 0 ⦄ := by
  unfold necessary_points
  step*
  grind

end spqr.encoding.polynomial.PolyDecoder
