/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `core::num::U16::to_be_bytes`

In Rust's standard library, `u16::to_be_bytes(self)` converts a `u16` value into its 2-byte
big-endian representation: `[high_byte, low_byte]` where `high_byte = value / 256` and
`low_byte = value % 256`.

The Aeneas-extracted Lean function `core.num.U16.to_be_bytes` mirrors this behavior.

This is used in `Pt::serialize` and `Poly::serialize` to encode GF(2¹⁶) field elements.

**Source**: core/src/num/uint_macros.rs (u16::to_be_bytes)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.num.U16

/--
**Spec theorem for `core.num.U16.to_be_bytes`**:

The two-byte big-endian encoding of a `u16` value `x` satisfies
  `result[0].val * 256 + result[1].val = x.val`.

**Source**: core/src/num/uint_macros.rs (u16::to_be_bytes)
-/
@[step]
theorem to_be_bytes_spec (x : U16) :
    lift (core.num.U16.to_be_bytes x) ⦃ result =>
      (result[0]!).val * 256 + (result[1]!).val = x.val ⦄ := by
  simp  [lift, core.num.U16.to_be_bytes]
  simp only  [Std.UScalar.val]
  simp [BitVec.toBEBytes, BitVec.toLEBytes, Nat.shiftRight_eq_div_pow]
  grind

end Aeneas.Std.core.num.U16
