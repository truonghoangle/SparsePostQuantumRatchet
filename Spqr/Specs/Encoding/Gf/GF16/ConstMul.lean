/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.Unaccelerated.Mul

/-! # Spec Theorem for `GF16::const_mul`

Specification and proof for `encoding.gf.GF16.const_mul`,
which implements GF(2¹⁶) multiplication on the `GF16` wrapper by
delegating to the underlying carry-less multiplication on `u16`,
`encoding.gf.unaccelerated.mul`, and re-wrapping the result back
into a `GF16`.

In GF(2¹⁶) — the Galois field with 65 536 elements — multiplication
is polynomial multiplication modulo the irreducible polynomial
POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b).  Each `GF16` element is
represented as a `u16` polynomial of degree < 16 with coefficients
in GF(2).

Concretely, `const_mul self other` simply computes
  `unaccelerated::mul(self.value, other.value)`
and stores the resulting `u16` in a fresh `GF16` wrapper.  The
`const_mul` method introduces no additional logic beyond this
delegation, so its postcondition is inherited from the corresponding
`unaccelerated::mul` specification: lifting the underlying `u16` of
the result into `GF216 = GaloisField 2 16` via `Nat.toGF216` yields
the GF(2¹⁶) product of the lifts of `self.value` and `other.value`.

**Source**: spqr/src/encoding/gf.rs (lines 560:4-564:5)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16

/-
natural language description:

• Takes two `GF16` field elements `self` and `other`, each wrapping
  a `u16` value representing an element of GF(2¹⁶).
• Delegates immediately to the unaccelerated carry-less multiplier:
    `encoding.gf.unaccelerated.mul self.value other.value`
  which performs carry-less polynomial multiplication of the two
  16-bit inputs into a 32-bit intermediate, followed by reduction
  modulo the irreducible polynomial POLY = 0x1100b.
• Wraps the resulting `u16` back into a `GF16`, returning the
  GF(2¹⁶) product of the two inputs.

natural language specs:

• The function always succeeds (no panic) for any pair of `GF16`
  inputs, since `unaccelerated::mul` is total on `u16`.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the GF(2¹⁶) product of
  the similarly-lifted inputs:
    `(result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 * other.value.val.toGF216`
  where the `*` on the right-hand side is multiplication in
  `GF216 = GaloisField 2 16`.
-/

@[step]
theorem const_mul_spec (self other : spqr.encoding.gf.GF16) :
    const_mul self other ⦃ result =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 * other.value.val.toGF216 ⦄ := by
  unfold const_mul
  step*

end spqr.encoding.gf.GF16
