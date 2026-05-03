/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.Unaccelerated.Mul

/-! # Spec Theorem for `GF16::mul_assign` (by-reference)

Specification and proof for
`encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul_assign`,
which implements `MulAssign<&GF16> for GF16` by delegating to the
software (unaccelerated) carry-less multiplication
`encoding.gf.unaccelerated.mul` on the underlying `u16` values, and
wrapping the result back into a `GF16`.

In GF(2¹⁶) — the Galois field with 65 536 elements — multiplication
is polynomial multiplication modulo the irreducible polynomial
POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b).  Each field element is
represented as a polynomial of degree < 16 with coefficients in
GF(2), stored as a 16-bit unsigned integer.

Concretely, `mul_assign self other` calls
`unaccelerated.mul self.value other.value`, which:
  1. Performs `poly_mul` — carry-less (XOR-based) long multiplication
     of the two 16-bit inputs, producing a 32-bit unreduced product.
  2. Performs `poly_reduce` — reduction of the 32-bit product modulo
     POLY using a precomputed table (`REDUCE_BYTES`), yielding a
     16-bit canonical representative in GF(2¹⁶).

The on-target Rust implementation may dispatch to hardware carry-less
multiplication instructions (`PCLMULQDQ` / `PMULL`) on x86/x86_64 and
aarch64 when the corresponding CPU feature is detected; the extracted
Lean version contains only the unaccelerated fallback.

The by-reference `MulAssign` introduces no additional logic beyond the
delegation, so its postcondition is inherited from the underlying
`unaccelerated.mul` specification: lifting the `u16` of the result
into `GF216 = GaloisField 2 16` via `Nat.toGF216` yields the GF(2¹⁶)
product of the lifts of `self.value` and `other.value`.

**Source**: spqr/src/encoding/gf.rs (lines 492:4-502:5)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16

/-
natural language description:

• Takes two `GF16` field elements `self` and `other`, each wrapping
  a `u16` value representing an element of GF(2¹⁶).
• Delegates to the unaccelerated software multiplication:
    `encoding.gf.unaccelerated.mul self.value other.value`
  which performs carry-less polynomial multiplication followed by
  reduction modulo POLY = 0x1100b.
• Returns the updated `self` with `self.value` replaced by the
  GF(2¹⁶) product.

natural language specs:

• The function always succeeds (no panic) for any pair of `GF16`
  inputs, since `unaccelerated.mul` is total on `Std.U16 × Std.U16`.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the GF(2¹⁶) product of the
  similarly-lifted inputs:
    `(result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 * other.value.val.toGF216`
  where the `*` on the right-hand side is multiplication in
  `GF216 = GaloisField 2 16`.
-/

@[step]
theorem mul_assign_spec (self other : spqr.encoding.gf.GF16) :
    mul_assign self other ⦃ result =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 * other.value.val.toGF216 ⦄ := by
  unfold mul_assign
  step*

end spqr.encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16
