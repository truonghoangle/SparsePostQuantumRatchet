# Verify GF(2¹⁶) core arithmetic and reduction functions in `gf.rs`

This PR verify the core GF(2¹⁶) arithmetic primitives and reduction infrastructure in `src/encoding/gf.rs`. It provide Lean 4 specifications and proofs for eleven functions spanning the unaccelerated multiplication kernel, the table-driven polynomial reduction pipeline, and the `GF16` wrapper's constructor, constants, and const-evaluable arithmetic methods. Each function is verified against the algebraic model of GF(2¹⁶) ≅ GF(2)[X] / (X¹⁶ + X¹² + X³ + X + 1) defined in `Spqr.Math.Gf`, with postconditions expressed both at the polynomial level (`natToGF2Poly … %ₘ POLY_GF2`) and at the abstract field level (`Nat.toGF216 = φ ∘ natToGF2Poly` into `GF216 = GaloisField 2 16`).

The verified functions are:

- `spqr::encoding::gf::unaccelerated::mul2` — double GF(2¹⁶) multiplication sharing a common left operand, verified as two independent applications of `mul`. Spec file: `Spqr/Specs/Encoding/Gf/Unaccelerated/Mul2.lean`.

- `spqr::encoding::gf::unaccelerated::mul` — carry-less polynomial multiplication of two `u16` values followed by reduction modulo POLY, composing `poly_mul` and `poly_reduce`. Spec file: `Spqr/Specs/Encoding/Gf/Unaccelerated/Mul.lean`.

- `spqr::encoding::gf::reduce::poly_reduce` — table-driven two-pass byte-by-byte reduction of a 32-bit carry-less product modulo POLY using the precomputed `REDUCE_BYTES` table, yielding a 16-bit canonical GF(2¹⁶) representative. The proof establish correctness via `polyReduceSpec_correct`, bridging the XOR/shift implementation to polynomial algebra over GF(2). Spec file: `Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean`.

- `spqr::encoding::gf::reduce::reduce_from_byte` — per-byte reduction loop that compute the 32-bit XOR mask for reducing byte `a` against POLY by iterating over bits 7 down to 0, with carry feedback into `a`. The loop body and full loop are verified separately, establishing that the low 16 bits of the result equal `reduceByteTable a.val`. Spec file: `Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean`.

- `spqr::encoding::gf::reduce::reduce_bytes` — construction of the 256-entry `REDUCE_BYTES` lookup table, verified to satisfy `result[j].val = reduceByteTable j` for all `j < 256`, with a polynomial-level corollary `natToGF2Poly result[j].val = (natToGF2Poly j * X^16) %ₘ POLY_GF2`. Spec file: `Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean`.

- `spqr::encoding::gf::GF16::new` — the trivial constructor wrapping a raw `u16` into a `GF16`, verified as the identity lift under `Nat.toGF216`. Spec file: `Spqr/Specs/Encoding/Gf/GF16/New.lean`.

- `spqr::encoding::gf::GF16::const_mul` — const-evaluable GF(2¹⁶) multiplication on the `GF16` wrapper, delegating to `unaccelerated::mul` and inheriting its postcondition. Spec file: `Spqr/Specs/Encoding/Gf/GF16/ConstMul.lean`.

- `spqr::encoding::gf::GF16::const_sub` — GF(2¹⁶) subtraction (= addition in characteristic 2) implemented as bitwise XOR of the underlying `u16` values. Spec file: `Spqr/Specs/Encoding/Gf/GF16/ConstSub.lean`.

- `spqr::encoding::gf::GF16::const_div` — GF(2¹⁶) division via Fermat-style iterated squaring (`a / b = a · b^(2¹⁶ − 2)`), verified through a closed-form loop invariant over 15 squaring rounds. Spec file: `Spqr/Specs/Encoding/Gf/GF16/ConstDiv.lean`.

- `spqr::encoding::gf::GF16::ZERO` — the additive identity constant `GF16 { value: 0 }`, verified to lift to `0 : GF216` via `natToGF2Poly_zero` and `map_zero`. Spec file: `Spqr/Specs/Encoding/Gf/GF16/ZERO.lean`.

- `spqr::encoding::gf::GF16::ONE` — the multiplicative identity constant `GF16 { value: 1 }`, verified to lift to `1 : GF216` via `natToGF2Poly_one` and `map_one`. Spec file: `Spqr/Specs/Encoding/Gf/GF16/ONE.lean`.

No breaking changes.

Closes #TODO
