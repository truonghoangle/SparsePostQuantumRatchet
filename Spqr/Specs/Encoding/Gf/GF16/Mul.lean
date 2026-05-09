/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.GF16.MulAssign

/-! # Spec Theorem for `GF16::mul` (by-value)

Specification and proof for
`encoding.gf.GF16.Insts.CoreOpsArithMulGF16GF16.mul`,
which implements `Mul<GF16> for GF16` by delegating to the by-reference
`MulAssign<&GF16> for GF16`
(`encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul_assign`),
which itself delegates to the software (unaccelerated) carry-less
multiplication `encoding.gf.unaccelerated.mul` on the underlying `u16`
values, wrapping the result back into a `GF16`.

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

The on-target Rust implementation may dispatch to hardware carry-less
multiplication instructions (`PCLMULQDQ` / `PMULL`) on x86/x86_64 and
aarch64 when the corresponding CPU feature is detected; the extracted
Lean version contains only the unaccelerated fallback.

The by-value `Mul` introduces no additional logic beyond the
delegation, so its postcondition is inherited from the underlying
`mul_assign` (and ultimately `unaccelerated.mul`) specification:
lifting the `u16` of the result into `GF216 = GaloisField 2 16` via
`Nat.toGF216` yields the GF(2¹⁶) product of the lifts of `self.value`
and `other.value`.

**Source**: spqr/src/encoding/gf.rs (lines 515:4-519:5)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithMulGF16GF16

/-
natural language description:

• Takes two `GF16` field elements `self` and `other` by value, each
  wrapping a `u16` value representing an element of GF(2¹⁶).
• Delegates to the by-reference `MulAssign<&GF16> for GF16`:
    `encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul_assign
       self other`
  which itself calls
    `encoding.gf.unaccelerated.mul self.value other.value`
  performing carry-less polynomial multiplication followed by
  reduction modulo POLY = 0x1100b.
• Returns a fresh `GF16` whose `value` is the GF(2¹⁶) product.

natural language specs:

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

/-! ## By-reference `Mul<&GF16> for GF16`

The by-reference `Mul<&GF16, Output = GF16> for GF16` takes `other`
by reference in the original Rust source.  In the Aeneas extraction
the reference is erased, so the Lean signature is identical to the
by-value variant.  The implementation delegates directly to the
by-reference `MulAssign<&GF16> for GF16` (i.e.
`CoreOpsArithMulAssignShared0GF16.mul_assign`), which itself calls
`encoding.gf.unaccelerated.mul` on the underlying `u16` values,
performing carry-less polynomial multiplication followed by reduction
modulo POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b).

Since the by-reference `Mul` introduces no additional logic beyond
the delegation, its postcondition is inherited from the corresponding
`MulAssign` specification.

**Source**: spqr/src/encoding/gf.rs (lines 525:4-529:5)
-/

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithMulShared0GF16GF16

/-
natural language description:

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

natural language specs:

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

/-- **Spec and proof concerning `spqr.encoding.gf.GF16.Insts.CoreOpsArithMulShared0GF16GF16.mul`**:

The by-reference `Mul<&GF16> for GF16` computes GF(2¹⁶)
multiplication by delegating to the by-reference
`MulAssign<&GF16> for GF16`
(`CoreOpsArithMulAssignShared0GF16.mul_assign`), which itself
delegates to `unaccelerated.mul`, performing carry-less polynomial
multiplication (`poly_mul`) followed by reduction modulo
POLY = 0x1100b (`poly_reduce`).

The result satisfies the GF(2¹⁶)-level postcondition:

  `(result.value.val.toGF216 : GF216) =
       self.value.val.toGF216 * other.value.val.toGF216`

where `Nat.toGF216 n = φ (natToGF2Poly n)` interprets a natural
number as an element of `GF216 = GaloisField 2 16` via the chosen
ring homomorphism `φ : GF2Poly →+* GF216` that vanishes on
`POLY_GF2`.

The proof unfolds `mul` to expose the underlying `mul_assign` call
and discharges the resulting goal with `step*`, which applies the
already-registered `mul_assign_spec`.

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
