/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.Poly.SerializeLoop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{Poly}::serialize`

The Rust function `Poly::serialize` (in `src/encoding/polynomial.rs`, lines 329:4-340:5)
serializes a polynomial's GF(2¹⁶) coefficient vector into a byte vector by encoding each
coefficient's `u16` value as two big-endian bytes.

The function proceeds in two stages:
  1. **Allocation**: `Vec::with_capacity(self.coefficients.len() * 2)` — pre-allocates an output
     byte vector with capacity for `2 * n` bytes, where `n` is the number of coefficients.
  2. **Serialization loop**: `for i in 0..self.coefficients.len()` — iterates over each coefficient
     index, converting `self.coefficients[i].value : u16` to its 2-byte big-endian representation
     via `u16::to_be_bytes`, and appending those bytes to the output vector via
     `Vec::extend_from_slice`.

The result is a byte vector of length `2 * n` satisfying the big-endian encoding invariant:
for every coefficient index `j`, the bytes `result[2*j]` and `result[2*j+1]` encode
`self.coefficients[j].value` as `hi * 256 + lo`.

In GF(2¹⁶) (characteristic 2), each field element is stored as a `u16`, and the big-endian
encoding satisfies `hi * 256 + lo = value` where `hi` and `lo` are the high and low bytes
respectively.

**Source**: spqr/src/encoding/polynomial.rs (lines 329:4-340:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.Poly

/-- **Spec theorem for `encoding.polynomial.Poly.serialize`**:

Serialization of a `Poly`'s GF(2¹⁶) coefficient vector into a big-endian byte vector.

The function allocates an output byte vector via `Vec::with_capacity` and then drives the
serialization loop (`serialize_loop`) to completion.  The loop iterates over
`0..self.coefficients.len()`, appending the big-endian 2-byte encoding of each coefficient's
`u16` value to the output vector.

The result satisfies:
  * `result.val.length = 2 * self.coefficients.val.length` — exactly two bytes per coefficient.
  * For every `j < self.coefficients.val.length`:
      `∃ hi lo, result.val[2*j]? = some hi ∧ result.val[2*j+1]? = some lo ∧
        hi.val * 256 + lo.val = (self.coefficients.val[j]!).value.val`

This follows from composing:
  1. `Vec.with_capacity` — produces an empty vector (`val = []`).
  2. `serialize_loop.loop_spec` — the loop spec, which maintains the byte-encoding invariant
     across iterations and establishes the complete encoding at termination.

The precondition `2 * self.coefficients.val.length + 2 ≤ Usize.max` ensures that:
  * The `len * 2` capacity computation does not overflow `Usize`.
  * The loop body's `extend_from_slice` never overflows when appending 2 bytes.

This corresponds to the Rust function:
```rust
pub fn serialize(&self) -> Vec<u8> {
    let mut out = Vec::<u8>::with_capacity(self.coefficients.len() * 2);
    for i in 0..self.coefficients.len() {
        let c = self.coefficients[i];
        out.extend_from_slice(&c.value.to_be_bytes()[..]);
    }
    out
}
```

**Source**: spqr/src/encoding/polynomial.rs (lines 329:4-340:5)
-/
@[step]
theorem serialize_spec
    (self : encoding.polynomial.Poly)
    (h_overflow : 2 * self.coefficients.val.length + 2 ≤ Usize.max) :
    serialize self ⦃ (result : alloc.vec.Vec Std.U8) =>
      result.val.length = 2 * self.coefficients.val.length ∧
      ∀ (j : Nat), j < self.coefficients.val.length →
        ∃ (hi lo : Std.U8),
          result.val[2 * j]? = some hi ∧
          result.val[2 * j + 1]? = some lo ∧
          hi.val * 256 + lo.val = (self.coefficients.val[j]!).value.val ⦄ := by
  unfold serialize
  step*
  simp [alloc.vec.Vec.with_capacity]

end spqr.encoding.polynomial.Poly
