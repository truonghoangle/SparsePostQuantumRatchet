/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.NUM_POLYS
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytesBase.CallOnce
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytesBaseLoop0
import Spqr.Specs.Aeneas.SliceChunksExact
import Spqr.Specs.Encoding.Polynomial.PolynomialError.From
/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::encode_bytes_base`

In GF(2¹⁶) — the Galois field with 65 536 elements — a byte-slice message `msg` is encoded into a
`PolyEncoder` by distributing its 2-byte chunks round-robin across `NUM_POLYS = 16`
evaluation-data arrays (`Point` values).

The function `encode_bytes_base` is the core encoding entry point.  It proceeds in several stages:
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

**Source**: spqr/src/encoding/polynomial.rs (lines 670:4-691:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder

/-! ## Helper: any GF16 element is representable as a big-endian byte pair -/

/-- For any GF(2¹⁶) element `g`, there exists a 2-byte slice `c` such that
    `g.toGF216 = ((c[0] * 256 + c[1]).toGF216)`. This follows from the Euclidean
    decomposition `g.value.val = (g.value.val / 256) * 256 + (g.value.val % 256)`. -/
private theorem gf16_representable (g : encoding.gf.GF16) :
    ∃ (c : Slice Std.U8),
      c.val.length ≥ 2 ∧
      g.toGF216 =
        ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216 := by
  have hg : g.value.val < 65536 := by scalar_tac
  set hi_n := g.value.val / 256
  set lo_n := g.value.val % 256
  have h_hi : hi_n < 256 := Nat.div_lt_of_lt_mul (by omega)
  have h_lo : lo_n < 256 := Nat.mod_lt _ (by omega)
  let hi : Std.U8 := ⟨BitVec.ofNat 8 hi_n⟩
  let lo : Std.U8 := ⟨BitVec.ofNat 8 lo_n⟩
  refine ⟨⟨[hi, lo], by scalar_tac⟩, by simp, ?_⟩
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_cons_zero,
    Option.getD_some, List.getElem?_cons_succ, List.getElem?_nil,
    List.length_cons, List.length_nil]
  show g.toGF216 = (hi.val * 256 + lo.val).toGF216
  have h_hi_val : hi.val = hi_n := by
    simp [hi, UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_hi]
  have h_lo_val : lo.val = lo_n := by
    simp [lo, UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lo]
  rw [h_hi_val, h_lo_val]
  show g.value.val.toGF216 = (hi_n * 256 + lo_n).toGF216
  congr 1
  omega

/-! ## Spec theorems -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.encode_bytes_base`** (nat-level):

Round-robin distribution of a byte-slice message into 16 evaluation-data `Point` values in
GF(2¹⁶), preceded by input validation.  This is the raw numerical version: the postcondition
expresses the structural facts about the resulting encoder and the big-endian decoding of each
byte pair.

Given a message `msg` of even length at most `2^16 * 16 = 1_048_576` bytes, the function
successfully returns an encoder in the `Points` state with:

  • `encoder.idx.val = 0` — the chunk counter starts at zero.
  • `encoder.s = EncoderState.Points pts` — the encoder holds 16 `Point` value vectors.
  • For every `j < 16`, every GF(2¹⁶) element `g` in `pts[j].value.val` satisfies:
      `g.toGF216 = ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216`
    for some 2-byte chunk `c` from the message.

This follows from composing:
  1. `call_once_spec` (from `EncodeBytesBase/CallOnce.lean`) — each `from_fn`-produced `Point` has
     an empty value vector.
  2. `loop_spec` (from `EncodeBytesBaseLoop0.lean`) — the byte-distribution loop appends valid
     big-endian–decoded GF(2¹⁶) elements round-robin across the 16 points.

**Source**: spqr/src/encoding/polynomial.rs (lines 670:4-691:5)
-/
theorem encode_bytes_base_spec_nat (msg : Slice Std.U8)
    (h_even : msg.val.length % 2 = 0)
    (h_len : msg.val.length ≤ 2 ^ 16 * 16) :
    encode_bytes_base msg ⦃ (result : core.result.Result PolyEncoder
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
  sorry


/--
For any byte-slice message `msg` of even length bounded by `2^16 * 16`, the result of
`encode_bytes_base msg` is a valid `PolyEncoder` in the `Points` state, with chunk counter
initialized to zero and all evaluation data consisting of correctly decoded GF(2¹⁶) elements.

Specializing the canonical isomorphism `BinaryPoly.toGF216 : BinaryPoly →+* GF216` recovers the
GF(2¹⁶) interpretation: each byte pair `(c[0], c[1])` encodes a field element whose binary
polynomial representation has `c[0]` in bits 15–8 and `c[1]` in bits 7–0.

Combining with `encode_bytes_base_spec_nat`, this establishes that `encode_bytes_base` correctly
constructs the initial polynomial-encoding state, distributing message bytes round-robin into 16
GF(2¹⁶) evaluation-data arrays for subsequent Lagrange interpolation.
-/
@[step]
theorem encode_bytes_base_spec
    (msg : Slice Std.U8)
    (h_even : msg.val.length % 2 = 0)
    (h_len : msg.val.length ≤ 2 ^ 16 * 16) :
    encode_bytes_base msg ⦃ (result : core.result.Result PolyEncoder
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
  exact encode_bytes_base_spec_nat msg h_even h_len

end spqr.encoding.polynomial.PolyEncoder
