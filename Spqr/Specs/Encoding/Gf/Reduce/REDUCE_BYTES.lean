/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.Reduce.ReduceBytes
/-!
# Spec theorem for `spqr::encoding::gf::reduce::REDUCE_BYTES`

`REDUCE_BYTES` is a `const` associated item on the `reduce` module, defined as:
  `const REDUCE_BYTES: [u16; 256] = reduce_bytes();`

That is, `REDUCE_BYTES` is simply the result of evaluating `reduce_bytes` at compile time.  Each
entry `REDUCE_BYTES[k]` (for `0 ≤ k < 256`) stores the 16-bit XOR mask obtained by reducing the
polynomial `k · x¹⁶` modulo POLY:

  `REDUCE_BYTES[k] = (k · X¹⁶) mod polyGF2`

Concretely, `REDUCE_BYTES[k]` is the canonical 16-bit representative of the remainder of the
degree-< 24 polynomial `k · X¹⁶` when divided by polyGF2 = X¹⁶ + X¹² + X³ + X + 1 (a monic
polynomial of degree 16).  The table is used by `poly_reduce` to fold the high bytes of a 32-bit
carry-less product back into the low 16 bits, implementing GF(2¹⁶) reduction in two byte-level
passes.

The constant is unconditional and pure — its evaluation never fails and never depends on any input.

**Source**: spqr/src/encoding/gf.rs (lines 435:4-435:52)
-/

open Aeneas Aeneas.Std Result Polynomial spqr.encoding.gf.unaccelerated spqr.math.gf

namespace spqr.encoding.gf.reduce

/--
**Spec theorem for `encoding.gf.reduce.REDUCE_BYTES`**:
• `REDUCE_BYTES` is definitionally equal to `reduce_bytes`:
    `REDUCE_BYTES = reduce_bytes`
• For every index `j` with `j.val < 256`, the table entry satisfies:
    `∃ v : Std.U16, result[j] = ok v ∧ v.val = reduceByteTable j.val`
  where `reduceByteTable k` is the spec-level function computing the
  low 16 bits of the high-to-low reduction loop for byte `k`.
• Lifting each table entry into `GF(2)[X]` via `natToBinaryPoly`, the
  polynomial correctness property holds:
    `natToBinaryPoly v.val = (natToBinaryPoly j.val * X ^ 16) %ₘ polyGF2`
  confirming that each entry is the canonical remainder of `k · X¹⁶`
  modulo the irreducible polynomial polyGF2.

**`REDUCE_BYTES` is definitionally `reduce_bytes`**.
-/
@[simp]
theorem REDUCE_BYTES_eq : REDUCE_BYTES = reduce_bytes := by
  simp [REDUCE_BYTES]

/--
**Spec theorem for `encoding.gf.reduce.REDUCE_BYTES`**:

`REDUCE_BYTES` is the precomputed 256-entry reduction lookup table: for every index `j < 256`, the
entry `result[j]` is a `u16` whose natural-number value equals `reduceByteTable j.val` — the
spec-level function that computes `reduce_from_byte(j) as u16` (the low 16 bits of the XOR-reduction
loop applied to byte `j`).

Concretely:

  `∀ j, j.val < 256 → ∃ v, result[j] = ok v ∧ v.val = reduceByteTable j.val`

The proof unfolds `REDUCE_BYTES` to `reduce_bytes` and delegates to `reduce_bytes_spec`, which
establishes the invariant for all 256 entries via the loop specification.

**Source**: spqr/src/encoding/gf.rs (lines 435:4-435:52)
-/
@[step]
theorem REDUCE_BYTES_spec :
    REDUCE_BYTES ⦃ result =>
      ∀ j : Std.Usize, j.val < 256 →
        ∃ v : Std.U16,
          Array.index_usize result j = ok v ∧
            v.val = reduceByteTable j.val ⦄ := by
  simp only [REDUCE_BYTES]
  exact reduce_bytes_spec

/--
**Polynomial-level spec for `encoding.gf.reduce.REDUCE_BYTES`**:

GF(2)[X] polynomial correctness: for every index `j < 256`, the table entry satisfies

  `natToBinaryPoly result[j].val = (natToBinaryPoly j.val * X ^ 16) %ₘ polyGF2`

confirming that each entry is the canonical remainder of the polynomial `j · X¹⁶` modulo the
irreducible polynomial polyGF2 = X¹⁶ + X¹² + X³ + X + 1.

The proof unfolds `REDUCE_BYTES` to `reduce_bytes` and delegates to `reduce_byte_poly_spec`, which
combines the loop specification with `reduceByteTable_eq_poly_full`.

**Source**: spqr/src/encoding/gf.rs (lines 435:4-435:52)
-/
@[step]
theorem REDUCE_BYTES_poly_spec :
    REDUCE_BYTES ⦃ result =>
      ∀ j : Std.Usize, j.val < 256 →
        ∃ v : Std.U16,
          Array.index_usize result j = ok v ∧
            natToBinaryPoly v.val =
              (natToBinaryPoly j.val * X ^ 16) %ₘ polyGF2 ⦄ := by
  simp only [REDUCE_BYTES]
  exact reduce_byte_poly_spec

end spqr.encoding.gf.reduce
