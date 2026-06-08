/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Poly.DeserializeLoop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{Poly}::deserialize`

The Rust function `Poly::deserialize` (in `src/encoding/polynomial.rs`, lines 342:4-353:5)
deserializes a byte slice into a polynomial over GF(2¹⁶) by decoding consecutive pairs of
bytes as big-endian `u16` values, each wrapped as a `GF16` element.

The function proceeds in three stages:
  1. **Validation**: rejects the input if the byte slice is empty or has odd length,
     returning `Err(PolynomialError::SerializationInvalid)`.
  2. **Allocation**: `Vec::with_capacity(serialized.len() / 2)` — pre-allocates a coefficient
     vector with capacity for `serialized.len() / 2` GF(2¹⁶) elements.
  3. **Deserialization loop**: `for i in 0..(serialized.len() / 2)` — iterates over each
     byte-pair index, converting `serialized[2*i]` and `serialized[2*i+1]` from big-endian
     to a `u16` via `u16::from_be_bytes`, wrapping as `GF16::new`, and pushing onto the
     coefficient vector.

When the input is valid (non-empty with even length), the result is
`Ok(Poly { coefficients })` where `coefficients` has length `serialized.len() / 2` and
satisfies the big-endian decoding invariant: for every coefficient index `j`, the
coefficient's `u16` value equals `serialized[2*j] * 256 + serialized[2*j+1]`.

This is the inverse of `Poly::serialize`, which encodes each GF(2¹⁶) coefficient as two
big-endian bytes.

**Source**: spqr/src/encoding/polynomial.rs (lines 342:4-353:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.Poly

/-- **Spec theorem for `encoding.polynomial.Poly.deserialize`**:

Deserialization of a byte slice into a `Poly` over GF(2¹⁶).

The function first validates the input: if the byte slice is empty or has odd length, it
returns `Err(SerializationInvalid)`.  Otherwise, it allocates a coefficient vector via
`Vec::with_capacity` and drives the deserialization loop (`deserialize_loop`) to completion.
The loop iterates over `0..(serialized.len() / 2)`, decoding each pair of consecutive bytes
as a big-endian `u16` and wrapping it as a `GF16` coefficient.

The result satisfies:
  * `result = core.result.Result.Ok poly` — deserialization succeeds.
  * `poly.coefficients.val.length = serialized.val.length / 2` — exactly one coefficient
    per byte pair.
  * For every `j < serialized.val.length / 2`:
      `∃ g, poly.coefficients.val[j]? = some g ∧
        g.value.val = (serialized.val[2*j]!).val * 256 + (serialized.val[2*j+1]!).val`

This follows from composing:
  1. `Slice.is_empty` and the modular-arithmetic check — guard against invalid inputs.
  2. `Vec.with_capacity` — produces an empty coefficient vector (`val = []`).
  3. `deserialize_loop.loop_spec` — the loop spec, which maintains the byte-decoding invariant
     across iterations and establishes the complete decoding at termination.

The preconditions ensure that:
  * The input is non-empty and has even length (so the validation checks pass).
  * The loop index and vector operations do not overflow `Usize`.

This corresponds to the Rust function:
```rust
pub fn deserialize(serialized: &[u8]) -> Result<Self, PolynomialError> {
    if serialized.is_empty() || serialized.len() % 2 == 1 {
        return Err(PolynomialError::SerializationInvalid);
    }
    let mut coefficients = Vec::<GF16>::with_capacity(serialized.len() / 2);
    for i in 0..(serialized.len() / 2) {
        let j = i * 2;
        coefficients.push(GF16::new(u16::from_be_bytes([serialized[j], serialized[j + 1]])));
    }
    Ok(Self { coefficients })
}
```

**Source**: spqr/src/encoding/polynomial.rs (lines 342:4-353:5)
-/
@[step]
theorem deserialize_spec
    (serialized : Slice Std.U8)
    (h_nonempty : serialized.val.length ≠ 0)
    (h_even : serialized.val.length % 2 = 0)
    (h_overflow : serialized.val.length / 2 + 1 ≤ Usize.max) :
    deserialize serialized ⦃ (result : core.result.Result encoding.polynomial.Poly
        encoding.polynomial.PolynomialError) =>
      ∃ (poly : encoding.polynomial.Poly),
        result = core.result.Result.Ok poly ∧
        poly.coefficients.val.length = serialized.val.length / 2 ∧
        ∀ (j : Nat), j < serialized.val.length / 2 →
          ∃ (g : encoding.gf.GF16),
            poly.coefficients.val[j]? = some g ∧
            g.value.val =
              (serialized.val[2 * j]!).val * 256 +
              (serialized.val[2 * j + 1]!).val ⦄ := by
  unfold Poly.deserialize
  step*
  simp [alloc.vec.Vec.with_capacity]

end spqr.encoding.polynomial.Poly
