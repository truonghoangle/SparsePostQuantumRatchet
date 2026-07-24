/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::get_pts_needed`

A `PolyDecoder` wraps three fields:
  • `pts_needed : usize` — the total number of evaluation points still needed for decoding.
  • `pts : [SortedSet<Pt>; 16]` — a fixed-size array of 16 sorted sets of evaluation points,
     one per polynomial.
  • `is_complete : bool` — whether the decoder has collected enough points to decode.

The function `get_pts_needed` is a pure field accessor that returns `self.pts_needed` without
modification. In the Aeneas extraction the body is simply `ok self.pts_needed`, so the function
always succeeds and the result is propositionally equal to the `pts_needed` field of the input.

**Source**: spqr/src/encoding/polynomial.rs (lines 767:4-769:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.PolyDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.get_pts_needed`**:

`get_pts_needed` is a pure field projection:
  `get_pts_needed self = ok self.pts_needed`

• The function always succeeds (no panic / no error) for any `PolyDecoder` input, since it
  performs no arithmetic and no indexing — it simply returns the `pts_needed` field.
• The result is propositionally equal to `self.pts_needed`.

This accessor is used in `hax_lib` annotations to refer to the number of evaluation points
the decoder still requires before it can reconstruct the encoded message via Lagrange
interpolation over GF(2¹⁶).

**Source**: spqr/src/encoding/polynomial.rs (lines 767:4-769:5)
-/
@[step]
theorem get_pts_needed_spec (self : encoding.polynomial.PolyDecoder) :
    get_pts_needed self ⦃ (result : Std.Usize) =>
      result = self.pts_needed ⦄ := by
  unfold get_pts_needed
  simp [WP.spec_ok]

end spqr.encoding.polynomial.PolyDecoder
