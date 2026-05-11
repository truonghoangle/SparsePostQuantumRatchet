/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.GF16.MulAssign

/-! # Spec theorem for `spqr::encoding::gf::GF16::const_mul`

In GF(2¹⁶) — the Galois field with 65 536 elements — multiplication
is polynomial multiplication modulo the irreducible polynomial
POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b).  Each field element is
represented as a polynomial of degree < 16 with coefficients in
GF(2), stored as a 16-bit unsigned integer.

In the extracted Lean it reduces to a single call to
`mul_assign self other`, which in turn invokes
`unaccelerated.mul self.value other.value`, which:
  1. Performs `poly_mul` — carry-less (XOR-based) long multiplication
     of the two 16-bit inputs, producing a 32-bit unreduced product.
  2. Performs `poly_reduce` — reduction of the 32-bit product modulo
     POLY using a precomputed table (`REDUCE_BYTES`), yielding a
     16-bit canonical representative in GF(2¹⁶).


**Source**: spqr/src/encoding/gf.rs (lines 515:4-519:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithMulGF16GF16

/-- **Spec theorem for `spqr.encoding.gf.GF16.Insts.CoreOpsArithMulGF16GF16.mul`**:

• The function always succeeds (no panic) for any pair of `GF16`
  inputs, since the underlying `unaccelerated.mul` is total on
  `Std.U16 × Std.U16`.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the GF(2¹⁶) product of the
  similarly-lifted inputs:
    `(result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 * other.value.val.toGF216`
  where the `*` on the right-hand side is multiplication in
  `GF216 = GaloisField 2 16`.
-/
@[step]
theorem mul_spec (self other : spqr.encoding.gf.GF16) :
    mul self other ⦃ result =>
      (GF16toGF216 result : GF216) =
        GF16toGF216 self * GF16toGF216 other ⦄ := by
  unfold mul
  step*

end spqr.encoding.gf.GF16.Insts.CoreOpsArithMulGF16GF16

/-! # Spec theorem for `spqr::encoding::gf::GF16::const_sub`

• Takes two `GF16` field elements `self` and `other`, each wrapping
  a `u16` value representing an element of GF(2¹⁶).
  In the original Rust source `other` is passed by reference
  (`&GF16`); after Aeneas extraction the reference is erased and
  both arguments are plain `GF16` values.
• Delegates immediately to the by-reference `mul_assign`:
    `CoreOpsArithMulAssignShared0GF16.mul_assign self other`
  which itself calls
    `encoding.gf.unaccelerated.mul self.value other.value`
  performing carry-less polynomial multiplication followed by
  reduction modulo POLY = 0x1100b.
• Returns the resulting `GF16` whose `value` field is the GF(2¹⁶)
  product of the two inputs.

**Source**: spqr/src/encoding/gf.rs (lines 525:4-529:5)
-/

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithMulShared0GF16GF16

/-- **Spec theorem for `spqr.encoding.gf.GF16.Insts.CoreOpsArithMulShared0GF16GF16.mul`**:

• The function always succeeds (no panic) for any pair of `GF16`
  inputs, since the underlying `unaccelerated.mul` is total on
  `Std.U16 × Std.U16`.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the GF(2¹⁶) product of the
  similarly-lifted inputs:
    `(GF16toGF216 result : GF216) =
        GF16toGF216 self * GF16toGF216 other`
  where the `*` on the right-hand side is multiplication in
  `GF216 = GaloisField 2 16`.

**Source**: spqr/src/encoding/gf.rs (lines 525:4-529:5)
-/
@[step]
theorem mul_spec (self other : spqr.encoding.gf.GF16) :
    mul self other ⦃ (result : spqr.encoding.gf.GF16) =>
      (GF16toGF216 result : GF216) =
        GF16toGF216 self* GF16toGF216 other ⦄ := by
  unfold mul
  step*

end spqr.encoding.gf.GF16.Insts.CoreOpsArithMulShared0GF16GF16
