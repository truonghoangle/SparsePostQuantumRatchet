/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Mathlib.Data.Nat.Bitwise
import Spqr.Math.Gf16.Field
/-!
# Spec theorem for `spqr::encoding::gf::{impl ops::AddAssign<&GF16> for GF16}::add_assign`

In GF(2¹⁶) — the Galois field with 65 536 elements — addition is
simply bitwise XOR of the two 16-bit underlying values.  This follows
from the fact that GF(2¹⁶) has characteristic 2, so addition of
polynomial coefficients is addition in GF(2), which is XOR.

The by-reference `AddAssign<&GF16> for GF16` performs the actual
computation: `self.value ^= other.value` (bitwise XOR).  The
by-value `AddAssign<GF16> for GF16` wrapper delegates directly to
this by-reference variant, introducing no additional logic — the
two are observationally identical:
  `add_assign_val(a, b) = add_assign_ref(a, b)`

Note that in GF(2¹⁶), addition and subtraction coincide:
  `a + b = a - b = a ⊕ b`
since every element is its own additive inverse (`a + a = 0`).

**Source**: spqr/src/encoding/gf.rs (lines 28:4-31:5)
-/

open Aeneas Aeneas.Std Result spqr.math.gf spqr.encoding.gf

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithAddAssignShared0GF16

/-- **Spec theorem for `spqr.encoding.gf.GF16.Insts.CoreOpsArithAddAssignShared0GF16.add_assign`**:

• Takes two `GF16` field elements `self` and `other`, each wrapping
  a `u16` value representing an element of GF(2¹⁶).
• Computes `self.value ^= other.value` (bitwise XOR) directly,
  which is GF(2¹⁶) addition of the two polynomial encodings.
• Returns the updated `self` with `self.value` replaced by the
  GF(2¹⁶) sum.

• The function always succeeds (no panic) for any valid pair of
  GF16 inputs, since XOR is a total operation on bounded integers.
• The by-value `AddAssign<GF16>::add_assign` delegates to this
  by-reference variant and is observationally identical.
• Together with the `Add` trait implementation, the following
  identity holds:
    `(a + b).value = add_assign(a, b).value`

The result satisfies the GF(2¹⁶)-level postcondition:

  `result.value.val.toGF216 =
       self.value.val.toGF216 + other.value.val.toGF216`

where `Nat.toGF216 n = BinaryPoly.toGF216 (natToBinaryPoly n)` interprets a natural
number as an element of `GF216 = GaloisField 2 16` via the chosen
ring homomorphism `BinaryPoly.toGF216 : BinaryPoly →+* GF216` that vanishes on
`polyGF2`.

The proof reduces `result.value` to `self.value ^^^ other.value`,
applies `UScalar.val_xor` to push `.val` through `^^^`, and then
uses `natToBinaryPoly_xor` together with the additivity of the ring
homomorphism `BinaryPoly.toGF216` (`map_add`).

**Source**: spqr/src/encoding/gf.rs (lines 28:4-31:5)
-/
@[step]
theorem add_assign_spec (self other : GF16) :
    add_assign self other ⦃ (result : GF16) =>
      GF16toGF216 result = GF16toGF216 self + GF16toGF216 other ⦄ := by
  unfold add_assign
  step*
  simp_all only [UScalar.val_xor, GF16toGF216, Nat.toGF216, natToBinaryPoly_xor, map_add]

end spqr.encoding.gf.GF16.Insts.CoreOpsArithAddAssignShared0GF16

/-! # Spec theorem for `spqr::encoding::gf::{impl ops::AddAssign for GF16}::add_assign`

In GF(2¹⁶) — the Galois field with 65 536 elements — addition is
simply bitwise XOR of the two 16-bit underlying values.  This follows
from the fact that GF(2¹⁶) has characteristic 2, so addition of
polynomial coefficients is addition in GF(2), which is XOR.

Note that in GF(2¹⁶), addition and subtraction coincide:
  `a + b = a - b = a ⊕ b`
since every element is its own additive inverse (`a + a = 0`).

**Source**: spqr/src/encoding/gf.rs (lines 40:4-43:5)
-/

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithAddAssignGF16

/-- **Spec theorem for `spqr.encoding.gf.GF16.Insts.CoreOpsArithAddAssignGF16.add_assign`**:

• Takes two `GF16` field elements `self` and `other`, each wrapping
  a `u16` value representing an element of GF(2¹⁶).
  In the original Rust source `other` is passed by value
  (`GF16`); after Aeneas extraction the reference is erased and
  both arguments are plain `GF16` values.
• Delegates immediately to the by-reference `add_assign`:
    `CoreOpsArithAddAssignShared0GF16.add_assign self other`
  which computes `self.value ^^^ other.value` (bitwise XOR).
• Returns the resulting `GF16` whose `value` field is the GF(2¹⁶)
  sum of the two inputs.

• The function always succeeds (no panic) for any pair of `GF16`
  inputs, since XOR is a total operation on bounded integers.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = BinaryPoly.toGF216 ∘ natToBinaryPoly` yields the GF(2¹⁶) sum of the
  similarly-lifted inputs:
    `(result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 + other.value.val.toGF216`
  where the `+` on the right-hand side is addition in
  `GF216 = GaloisField 2 16`.

The result satisfies the GF(2¹⁶)-level postcondition:

  `(result.value.val.toGF216 : GF216) =
       self.value.val.toGF216 + other.value.val.toGF216`

where `Nat.toGF216 n = BinaryPoly.toGF216 (natToBinaryPoly n)` interprets a natural
number as an element of `GF216 = GaloisField 2 16` via the chosen
ring homomorphism `BinaryPoly.toGF216 : BinaryPoly →+* GF216` that vanishes on
`polyGF2`.

The proof unfolds `add_assign` (by-value) to expose the underlying
by-reference `add_assign` call and discharges the resulting goal
with `step*`, which applies the already-registered
`add_assign_spec`.

**Source**: spqr/src/encoding/gf.rs (lines 40:4-43:5)
-/
@[step]
theorem add_assign_spec (self other : GF16) :
    add_assign self other ⦃ (result : GF16) =>
      GF16toGF216 result = GF16toGF216 self + GF16toGF216 other ⦄ := by
  unfold add_assign
  step*

end spqr.encoding.gf.GF16.Insts.CoreOpsArithAddAssignGF16
