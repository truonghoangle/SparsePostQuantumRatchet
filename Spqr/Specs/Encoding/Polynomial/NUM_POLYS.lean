/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Specs.Encoding.Polynomial.CHUNK_SIZE

/-!
# Spec theorem for `spqr::encoding::polynomial::NUM_POLYS`

Specification and proof for `encoding.polynomial.NUM_POLYS`, the module-level constant defining
the number of polynomials (equivalently, GF(2¹⁶) field elements) tracked per data chunk in the
polynomial encoding layer of the Sparse Post-Quantum Ratchet.

In Protocol V1, each 32-byte chunk (`CHUNK_SIZE`) is split into 2-byte pairs, with each pair
representing a single element of GF(2¹⁶). Therefore:
  `NUM_POLYS = CHUNK_SIZE / 2 = 32 / 2 = 16`

This constant records the number of polynomials per chunk:
  `NUM_POLYS = ok 16#usize`

The constant depends only on `CHUNK_SIZE` and the literal `2`; its evaluation never fails and
never depends on any external input.

**Source**: spqr/src/encoding/polynomial.rs (lines 510:0-510:44)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial

/--
**Spec and proof concerning `encoding.polynomial.NUM_POLYS`**:

`NUM_POLYS` is computed as `CHUNK_SIZE / 2`, yielding the constant `16 : usize`. It records the
number of GF(2¹⁶) field elements (equivalently, polynomials) tracked per 32-byte data chunk in the
polynomial encoding layer. Each 2-byte pair within a chunk corresponds to a single GF(2¹⁶) element,
so a 32-byte chunk yields `32 / 2 = 16` field elements.

Concretely:

  `NUM_POLYS ⦃ (result : Usize) => result.val = 16 ⦄`

The proof unfolds the definitions of `NUM_POLYS` and `CHUNK_SIZE`, reduces the `usize` division
`32#usize / 2#usize` to `16#usize`, and extracts the natural-number value.

**Source**: spqr/src/encoding/polynomial.rs (lines 510:0-510:44)
-/
@[step]
theorem NUM_POLYS_spec :
    NUM_POLYS ⦃ (result : Std.Usize) =>
      result.val = 16 ⦄ := by
  unfold NUM_POLYS CHUNK_SIZE
  step
  grind

end spqr.encoding.polynomial
