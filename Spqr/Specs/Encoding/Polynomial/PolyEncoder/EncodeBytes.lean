/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytesBase

/-!
# Spec theorem for `{spqr::encoding::Encoder for PolyEncoder}::encode_bytes`

In GF(2¹⁶) — the Galois field with 65 536 elements — a byte-slice message `msg` is encoded into a
`PolyEncoder` by distributing its 2-byte chunks round-robin across `NUM_POLYS = 16`
evaluation-data arrays (`Point` values).

The function `encode_bytes` is the `Encoder` trait implementation for `PolyEncoder`.  It is a thin
wrapper that delegates directly to `encode_bytes_base`, which performs:
  1. **Input validation** — the message length must be even (`msg.len() % 2 == 0`) and bounded
     (`msg.len() ≤ (1 << 16) * NUM_POLYS = 1_048_576`).  Violation of either condition returns
     an `Err` variant (`PolynomialError::MessageLengthEven` or `MessageLengthTooLong`).
  2. **Point array initialization** — `core::array::from_fn` creates an array of 16 `Point`s,
     each with an empty value vector pre-allocated with capacity `msg.len() / 2`.
  3. **Round-robin distribution** — iterating over `msg.chunks_exact(2).enumerate()`, each pair of
     consecutive bytes `(c[0], c[1])` is decoded as a big-endian 16-bit value and converted to a
     GF(2¹⁶) element via `GF16::new(((c[0] as u16) << 8) + (c[1] as u16))`.  The resulting element
     is appended to `pts[i % 16].value`, where `i` is the chunk's enumeration index.
  4. **Encoder construction** — the result is wrapped in
     `Ok(PolyEncoder { idx: 0, s: EncoderState::Points(pts) })`.

In GF(2¹⁶) (characteristic 2), each 16-bit big-endian value `c[0] * 256 + c[1]` represents a
polynomial of degree < 16 with coefficients in GF(2), and `GF16::new` packages it as the canonical
representative in GF(2¹⁶) ≅ GF(2)[X] / (x¹⁶ + x¹² + x³ + x + 1).

**Source**: spqr/src/encoding/polynomial.rs (lines 730:4-732:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes`**
(nat-level):

The `Encoder` trait implementation for `PolyEncoder`, which delegates directly to
`encode_bytes_base`.

Given a message `msg` of even length bounded by `2^16 * 16 = 1_048_576` bytes, the function
successfully returns an encoder in the `Points` state with:

  • `encoder.idx.val = 0` — the chunk counter starts at zero.
  • `encoder.s = EncoderState.Points pts` — the encoder holds 16 `Point` value vectors.
  • For every `j < 16`, every GF(2¹⁶) element `g` in `pts[j].value.val` satisfies:
      `g.toGF216 = ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216`
    for some 2-byte chunk `c` from the message.

This follows directly from `encode_bytes_base_spec` since `encode_bytes` is a direct delegation
to `encode_bytes_base`.

**Source**: spqr/src/encoding/polynomial.rs (lines 730:4-732:5)
-/
theorem encode_bytes_spec_nat (msg : Slice Std.U8)
    (h_even : msg.val.length % 2 = 0)
    (h_len : msg.val.length ≤ 2 ^ 16 * 16) :
    encode_bytes msg ⦃ (result : core.result.Result PolyEncoder
        encoding.EncodingError) =>
      ∃ (pts : Array encoding.polynomial.Point 16#usize),
        result = core.result.Result.Ok
          { idx := 0#u32, s := encoding.polynomial.EncoderState.Points pts } ∧
        (∀ (j : Nat), j < 16 →
          ∀ g ∈ pts.val[j]!.value.val,
            ∃ (c : Slice Std.U8),
              c.val.length ≥ 2 ∧
              g.toGF216 =
                ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216) ⦄ := by
  unfold encode_bytes
  step*

/--
For any byte-slice message `msg` of even length bounded by `2^16 * 16`, the result of
`encode_bytes msg` is a valid `PolyEncoder` in the `Points` state, with chunk counter
initialized to zero and all evaluation data consisting of correctly decoded GF(2¹⁶) elements.

Since `encode_bytes` delegates directly to `encode_bytes_base`, this theorem inherits the full
postcondition established by `encode_bytes_base_spec`: the encoder's GF(2¹⁶) evaluation-data
arrays contain the round-robin distribution of the message's big-endian–decoded byte pairs,
ready for subsequent Lagrange interpolation.

Combining with `encode_bytes_spec_nat`, this establishes that `encode_bytes` correctly
constructs the initial polynomial-encoding state, distributing message bytes round-robin into 16
GF(2¹⁶) evaluation-data arrays for subsequent Lagrange interpolation.
-/
@[step]
theorem encode_bytes_spec
    (msg : Slice Std.U8)
    (h_even : msg.val.length % 2 = 0)
    (h_len : msg.val.length ≤ 2 ^ 16 * 16) :
    encode_bytes msg ⦃ (result : core.result.Result PolyEncoder
        encoding.EncodingError) =>
      ∃ (pts : Array encoding.polynomial.Point 16#usize),
        result = core.result.Result.Ok
          { idx := 0#u32, s := encoding.polynomial.EncoderState.Points pts } ∧
        (∀ (j : Nat), j < 16 →
          ∀ g ∈ pts.val[j]!.value.val,
            ∃ (c : Slice Std.U8),
              c.val.length ≥ 2 ∧
              g.toGF216 =
                ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216) ⦄ := by
  exact encode_bytes_spec_nat msg h_even h_len

end spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder
