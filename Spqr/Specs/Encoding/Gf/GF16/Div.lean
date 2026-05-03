/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.GF16.DivImpl

/-! # Spec Theorem for `GF16::div` (by-reference second operand)

Specification and proof for
`encoding.gf.GF16.Insts.CoreOpsArithDivShared0GF16GF16.div`,
which implements `Div<&GF16> for GF16` by delegating to
`encoding.gf.GF16.div_impl`, the Fermat-style iterated-squaring
GF(2¹⁶) division routine.

In GF(2¹⁶) — the Galois field with 65 536 elements — every non-zero
element `b` satisfies `b^(2¹⁶ − 1) = 1`, so the multiplicative
inverse is `b⁻¹ = b^(2¹⁶ − 2)` and `a / b = a · b^(2¹⁶ − 2)`.  Field
multiplication is polynomial multiplication modulo the irreducible
polynomial POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b); each field
element is represented as a polynomial of degree < 16 with
coefficients in GF(2), stored as a 16-bit unsigned integer, and the
`GF16` Rust type is the `u16` wrapper providing the field
operations.

In the extracted Lean it reduces to a single call to
`encoding.gf.GF16.div_impl self other`, which:
  1. Initialises `square := other · other` via the by-value
     `Mul<GF16> for GF16` instance, ultimately delegating to the
     software (unaccelerated) carry-less multiplication
     `encoding.gf.unaccelerated.mul`.
  2. Runs the `for _i in 1..16` loop driver
     `encoding.gf.GF16.div_impl_loop`, performing 15 iterations of
     `out := out · square; square := square²` to obtain
     `out = self · (other²)^(2¹⁵ − 1) = self · other^(2¹⁶ − 2)`.

The on-target Rust implementation may dispatch to hardware carry-less
multiplication instructions (`PCLMULQDQ` / `PMULL`) on x86/x86_64 and
aarch64 when the corresponding CPU feature is detected; the extracted
Lean version contains only the unaccelerated fallback.

The by-reference `Div<&GF16>` introduces no additional logic beyond
the delegation, so its postcondition is inherited from the underlying
`div_impl` specification: lifting the `u16` of the result into
`GF216 = GaloisField 2 16` via `Nat.toGF216` yields the GF(2¹⁶)
Fermat-style quotient `self · other^(2¹⁶ − 2)` of the lifts of
`self.value` and `other.value`.

**Source**: spqr/src/encoding/gf.rs (lines 558:4-560:5)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.GF16

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithDivShared0GF16GF16

/-
natural language description:

• Takes two `GF16` field elements `self` (by value) and `other` (by
  reference), each wrapping a `u16` value representing an element of
  GF(2¹⁶), and computes the GF(2¹⁶) quotient `self / other` by
  Fermat-style iterated squaring.
• Delegates to
    `encoding.gf.GF16.div_impl self other`,
  which initialises `square := other · other` via the by-value
  `Mul<GF16> for GF16` instance (itself defering to the software
  carry-less multiplication `encoding.gf.unaccelerated.mul`) and then
  runs the `for _i in 1..16` loop driver
  `encoding.gf.GF16.div_impl_loop` for 15 iterations of
  `out := out · square; square := square²`.
• Returns a fresh `GF16` whose `value` is the GF(2¹⁶) quotient
  `self · other^(2¹⁶ − 2)`.

natural language specs:

• The function always succeeds (no panic) for any pair of `GF16`
  inputs, since the underlying `unaccelerated.mul` and the loop
  driver are total on `GF16 × GF16`.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the GF(2¹⁶) Fermat-style
  quotient of the similarly-lifted inputs:
    `(result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 *
        other.value.val.toGF216 ^ (2 ^ 16 − 2)`
  where the operations on the right-hand side are performed in
  `GF216 = GaloisField 2 16`.  When `other ≠ 0` Fermat's little
  theorem in GF(2¹⁶) gives `other^(2¹⁶ − 1) = 1`, so
  `other^(2¹⁶ − 2) = other⁻¹` and the right-hand side is genuinely
  the field quotient `self / other`.
-/

@[step]
theorem div_spec (self other : spqr.encoding.gf.GF16) :
    div self other ⦃ result =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 *
          other.value.val.toGF216 ^ (2 ^ 16 - 2) ⦄ := by
  unfold div
  step*

end spqr.encoding.gf.GF16.Insts.CoreOpsArithDivShared0GF16GF16
