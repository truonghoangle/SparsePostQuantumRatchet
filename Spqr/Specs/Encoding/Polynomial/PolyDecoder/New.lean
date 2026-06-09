/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NewWithPolyCount

/-!
# Spec theorem for `spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::new`

A `PolyDecoder` reconstructs a byte message from a stream of GF(2¹⁶) evaluation points via
Lagrange interpolation over GF(2¹⁶) ≅ GF(2)[X] / (x¹⁶ + x¹² + x³ + x + 1).  Its trait-level
constructor `<PolyDecoder as Decoder>::new` simply delegates to the inherent constructor
`PolyDecoder::new_with_poly_count` with the polynomial-count parameter fixed to
`NUM_POLYS = 16`:

```rust
fn new(len_bytes: usize) -> Result<Self, super::EncodingError> {
    Self::new_with_poly_count(len_bytes, 16)
}
```

The function proceeds in two stages:
  1. `new_with_poly_count(len_bytes, 16)` — validating constructor that checks
     `len_bytes % 2 == 0` and returns either `Err(PolynomialError::MessageLengthEven)`
     (lifted into `EncodingError`) or `Ok(PolyDecoder { pts_needed := len_bytes / 2,
     pts := [SortedSet::new(); 16], is_complete := false })`.
  2. The result of that call is returned verbatim.

**Source**: spqr/src/encoding/polynomial.rs (lines 874:4-876:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.new`**
(nat-level):

Trait-level constructor of `PolyDecoder` from a target message length `len_bytes` (in bytes).
The function composes (trivially) the inherent validating constructor `new_with_poly_count`
with the constant polynomial-count argument `16#usize`.

The result satisfies the function-level postcondition documented in the Rust source at
line 873 (`hax_lib::ensures`):
  `len_bytes % 2 == 0 → res.is_ok() ∧ res.unwrap().pts_needed == len_bytes / 2`,
together with the matching error case `len_bytes % 2 ≠ 0 → res = Err MessageLengthEven`.

This follows from composing:
  1. `new_with_poly_count_spec`: validating construction
     - returns `Ok { pts_needed := len_bytes / 2, pts := [∅; 16], is_complete := false }`
       when `len_bytes % 2 = 0`,
     - returns `Err (EncodingError.PolynomialError MessageLengthEven)` otherwise.

This establishes that the trait-level `Decoder::new` is a thin wrapper that delegates the
entire constructor contract to `new_with_poly_count`, with the polynomial count hard-coded
to `NUM_POLYS = 16`.

**Source**: spqr/src/encoding/polynomial.rs (lines 874:4-876:5)
-/
theorem new_spec_nat (len_bytes : Std.Usize) :
    new len_bytes ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder encoding.EncodingError) =>
      if len_bytes.val % 2 = 0 then
        ∃ (pts : Array (sorted_vec.SortedSet Pt) 16#usize),
          pts.val = List.replicate 16 default ∧
          result = core.result.Result.Ok
            { pts_needed := ⟨len_bytes.val / 2, by
                have : len_bytes.val / 2 ≤ len_bytes.val := Nat.div_le_self _ _
                exact Nat.lt_of_le_of_lt this len_bytes.hBounds⟩,
              pts := pts,
              is_complete := false }
      else
        result = core.result.Result.Err
          (encoding.EncodingError.PolynomialError
            encoding.polynomial.PolynomialError.MessageLengthEven) ⦄ := by
  unfold new
  step*
  assumption

/--
The trait-level `Decoder::new` for `PolyDecoder` is the public entry point exposed by the
`Decoder` trait implementation.  This re-statement of `new_spec_nat` exposes the same
postcondition through the `step` attribute so downstream proofs (e.g. those over the
chunked/unchunked state machines that initialise a `PolyDecoder`) can dispatch the call
automatically.

The decoder produced on success has:
  • `pts_needed = len_bytes / 2` — total number of `(x, y)` evaluation points required to
    decode the message (one point per 2 bytes of GF(2¹⁶) data),
  • `pts = [∅; 16]` — 16 empty sorted point sets, one per polynomial (`NUM_POLYS = 16`),
  • `is_complete = false` — no points absorbed yet.

The error case `len_bytes % 2 ≠ 0` returns `EncodingError.PolynomialError MessageLengthEven`,
matching the companion check on the encoding side (`PolyEncoder::encode_bytes`).
-/
@[step]
theorem new_spec (len_bytes : Std.Usize) :
    new len_bytes ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder encoding.EncodingError) =>
      if len_bytes.val % 2 = 0 then
        ∃ (pts : Array (sorted_vec.SortedSet Pt) 16#usize),
          pts.val = List.replicate 16 default ∧
          result = core.result.Result.Ok
            { pts_needed := ⟨len_bytes.val / 2, by
                have : len_bytes.val / 2 ≤ len_bytes.val := Nat.div_le_self _ _
                exact Nat.lt_of_le_of_lt this len_bytes.hBounds⟩,
              pts := pts,
              is_complete := false }
      else
        result = core.result.Result.Err
          (encoding.EncodingError.PolynomialError
            encoding.polynomial.PolynomialError.MessageLengthEven) ⦄ :=
  new_spec_nat len_bytes

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
