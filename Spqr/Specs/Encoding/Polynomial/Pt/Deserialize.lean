/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Specs.Aeneas.U16FromBeBytes
import Spqr.Specs.Aeneas.TryFromSliceToArray


/-!
# Spec Theorem for `Pt::deserialize`

Specification and proof for `encoding.polynomial.Pt.deserialize`, which deserializes a 4-byte
big-endian array into a GF(2¹⁶) cartesian point `Pt { x, y }`.

The function reads a `[u8; 4]` input array and reconstructs a point:
  - `result.x.value ← u16::from_be_bytes(s[0..2])`
    where `result.x.value = s[0] · 256 + s[1]`
  - `result.y.value ← u16::from_be_bytes(s[2..4])`
    where `result.y.value = s[2] · 256 + s[3]`

The two-byte big-endian identity
  `result.x.value.val = s[0].val · 256 + s[1].val`
  `result.y.value.val = s[2].val · 256 + s[3].val`
ensures that the deserialized point faithfully represents the original bytes, and together with
`Pt::serialize` forms a round-trip:
  `Pt::deserialize(pt.serialize()) = pt`

**Source**: spqr/src/encoding/polynomial.rs (lines 38:4-43:5)
-/


open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.Pt

/-
natural language description:

• Takes a `[u8; 4]` array `s`.
• Extracts the first two bytes `s[0..2]`, converts them from a big-endian byte pair into a `u16`
  via `u16::from_be_bytes`:
    - `x_val = (s[0] as u16) << 8 | (s[1] as u16)`
    i.e. `x_val = s[0] · 256 + s[1]`
• Wraps the resulting `u16` as a `GF16` field element → `x`.
• Extracts the last two bytes `s[2..4]`, converts them from a big-endian byte pair into a `u16`
  via `u16::from_be_bytes`:
    - `y_val = (s[2] as u16) << 8 | (s[3] as u16)`
    i.e. `y_val = s[2] · 256 + s[3]`
• Wraps the resulting `u16` as a `GF16` field element → `y`.
• Returns `ok { x, y }`.

natural language specs:

• The function always succeeds (no panic) for any valid `[u8; 4]` input.
• The x-coordinate is reconstructed from the first two bytes in big-endian:
    `result.x.value.val = s[0].val * 256 + s[1].val`
• The y-coordinate is reconstructed from the last two bytes in big-endian:
    `result.y.value.val = s[2].val * 256 + s[3].val`
• Together with `Pt::serialize`, the decoding is invertible:
    `Pt::deserialize(pt.serialize()) = ok pt`
-/

/--
**Spec and proof concerning `encoding.polynomial.Pt.deserialize`**:
• The function always succeeds (no panic) for any valid `[u8; 4]` input.
• The x-coordinate of the result is reconstructed from the first two bytes in big-endian:
  `result.x.value.val = s[0].val * 256 + s[1].val`
• The y-coordinate of the result is reconstructed from the last two bytes in big-endian:
  `result.y.value.val = s[2].val * 256 + s[3].val`
-/
@[step]
theorem deserialize_spec (s : Array Std.U8 4#usize) :
    deserialize s ⦃ result =>
      result.x.value.val = (s[0]!).val * 256 + (s[1]!).val ∧
      result.y.value.val = (s[2]!).val * 256 + (s[3]!).val ⦄ := by
  unfold deserialize encoding.gf.GF16.new core.result.Result.unwrap
  step*
  simp_all only
  step*
  simp_all only
  step*
  simp_all

end spqr.encoding.polynomial.Pt
