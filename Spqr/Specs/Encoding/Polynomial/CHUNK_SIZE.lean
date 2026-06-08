/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
/-!
# Spec theorem for `spqr::encoding::polynomial::CHUNK_SIZE`

Specification and proof for `encoding.polynomial.CHUNK_SIZE`, the module-level constant defining
the size of a data chunk in bytes for the polynomial encoding layer of the Sparse Post-Quantum
Ratchet.

In Protocol V1, plaintext data is split into fixed-size chunks of 32 bytes before being encoded via
erasure coding over GF(2¹⁶). Each 2-byte pair within a chunk corresponds to a single GF(2¹⁶)
element, so a 32-byte chunk yields `CHUNK_SIZE / 2 = 16` field elements (see `NUM_POLYS`).

This constant records that chunk size:
  `CHUNK_SIZE = 32#usize`

The constant is unconditional and pure — its evaluation never fails and never depends on any input.

**Source**: spqr/src/encoding/polynomial.rs (lines 508:0-508:29)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial

/-
natural language description:

• `CHUNK_SIZE` is a module-level constant of type `usize`.
• It is defined as the literal `32`, recording the size of a data
  chunk in bytes used by the polynomial encoding layer.
• Each chunk is split into 2-byte pairs, each pair representing a
  single element of GF(2¹⁶). Thus a 32-byte chunk encodes
  `32 / 2 = 16` field elements, which equals `NUM_POLYS`.
• The constant is unconditional and pure — its evaluation never
  fails and never depends on any input.

natural language specs:

• The underlying `usize` value of `CHUNK_SIZE` is `32`:
    `CHUNK_SIZE = 32#usize`
  and equivalently as a natural number:
    `CHUNK_SIZE.val = 32`.
• Dividing `CHUNK_SIZE` by 2 yields `NUM_POLYS = 16`, the number
  of GF(2¹⁶) elements (and hence polynomials) tracked per chunk.
-/

/-- **The `usize` value of `CHUNK_SIZE` is `32#usize`**. -/
@[simp]
theorem CHUNK_SIZE_eq :
    CHUNK_SIZE = 32#usize := by
  simp [CHUNK_SIZE]

/--
**The underlying natural-number value of `CHUNK_SIZE` is `32`**.
-/
@[simp]
theorem CHUNK_SIZE_val :
    CHUNK_SIZE.val = 32 := by
  simp

/--
**Spec and proof concerning `encoding.polynomial.CHUNK_SIZE`**:

`CHUNK_SIZE` is the constant `32 : usize`, recording the size of a data chunk in bytes for the
polynomial encoding layer. Each 32-byte chunk is partitioned into 16 two-byte GF(2¹⁶) elements,
matching the value of `NUM_POLYS`.

Concretely:

  `CHUNK_SIZE.val = 32`

The proof unfolds the definition and reduces the `usize` literal `32#usize` to its natural-number
value.

**Source**: spqr/src/encoding/polynomial.rs (lines 508:0-508:29)
-/
@[step]
theorem CHUNK_SIZE_spec :
    ok CHUNK_SIZE ⦃ (result : Std.Usize) =>
      result.val = 32 ⦄ := by
  simp

end spqr.encoding.polynomial
