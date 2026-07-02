/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.Pt.PartialCmp
/-!
# Spec theorem for `spqr::encoding::polynomial::{impl core::cmp::Ord for Pt}::cmp`

The `Ord` implementation for `Pt` — a Cartesian point `(x, y)` in GF(2¹⁶) × GF(2¹⁶) — provides a
total ordering by comparing the underlying `u16` values of the x-coordinates.  It delegates to
`partial_cmp`, which always returns `some _`, and then unwraps the result.

Because `partial_cmp` always produces `some _` (the comparison is total), the `unwrap` call never
panics.

Note that in this ordering, two points with the same x-coordinate but different y-coordinates
compare as equal:
  `cmp (Pt x y₁) (Pt x y₂) = Ordering.eq`
since only the x-coordinate participates in the comparison.

**Source**: spqr/src/encoding/polynomial.rs (lines 47:4-49:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.Pt.Insts.CoreCmpOrd

/--
**Spec theorem for `spqr.encoding.polynomial.Pt.Insts.CoreCmpOrd.cmp`**:

• Takes two `Pt` values `self` and `other`, each containing an x-coordinate and y-coordinate
  as `GF16` field elements wrapping `u16` values.
• Delegates immediately to `partial_cmp`:
    `CoreCmpPartialOrdPt.partial_cmp self other`
  which computes `some (compare self.x.value.val other.x.value.val)`.
• Unwraps the `Option Ordering` via `core.option.Option.unwrap`, which is safe because the
  value is always `some _`.
• Returns the resulting `Ordering`.

• The function always succeeds (no panic) for any pair of `Pt` inputs.
• The y-coordinate is not considered in the ordering — two points with the same x but different
  y compare as equal under `cmp`.
• Together with the `PartialOrd` trait implementation, the following
  identity holds:
    `cmp(a, b) = unwrap(partial_cmp(a, b))`

The result satisfies the postcondition:

  `result = compare self.x.value.val other.x.value.val`

where `compare` is the standard natural-number three-way comparison returning
`Ordering.lt`, `Ordering.eq`, or `Ordering.gt`.

The proof unfolds `cmp` to expose the underlying `partial_cmp` call and discharges the resulting goal
with `step*`, which applies the already-registered `partial_cmp_spec`.

**Source**: spqr/src/encoding/polynomial.rs (lines 47:4-49:5)
-/
@[step]
theorem cmp_spec (self other : Pt) :
    cmp self other ⦃ (result : Ordering) =>
      result = compare self.x.value.val other.x.value.val ⦄ := by
  unfold cmp
  step*

end spqr.encoding.polynomial.Pt.Insts.CoreCmpOrd
