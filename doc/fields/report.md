# Specification Report: GF(2¹⁶) and Polynomial Verification

**Date**: 2026-05-14
**Author**: Generated report
**Base reference**: `469d5b3` (upstream/main — `Verify : spqr::encoding::gf::reduce::reduce_from_byte`)
**Head reference**: `8b5daf6` (HEAD — `updated`)

---

## Overview

This report documents the changes made to — and the corresponding mathematical representations of — the formal specifications in five Lean 4 files covering GF(2¹⁶) field arithmetic and Lagrange interpolation over GF(2¹⁶). The work spans two functional areas:

1. **GF(2¹⁶) arithmetic** (`Gf/` directory): multiplication, polynomial reduction, and parallel multiplication.
2. **Polynomial interpolation** (`Polynomial/Poly/` directory): Lagrange interpolation and its preparation phase.

All five files live under `Spqr/Specs/Encoding/` and verify Rust functions extracted via Aeneas from `src/encoding/gf.rs` and `src/encoding/polynomial.rs`.

---

## 1. `Spqr/Specs/Encoding/Gf/Unaccelerated/Mul.lean`

### Rust Source
`spqr/src/encoding/gf.rs`, lines 444–446.

### Status
**Previously stubbed (`sorry`), now fully proved.**

### Changes from Base

| Aspect | Before (469d5b3) | After (HEAD) |
|--------|-------------------|--------------|
| Lines | 87 | 97 |
| Imports | 4 imports | 5 imports (added `Spqr.Math.Poly.ModByMonic`) |
| `mul_spec'` proof | `sorry` | Completed via `unfold mul; step*` |
| `mul_spec` proof | `sorry` | Completed with explicit algebraic chain |
| Type annotations | `Std.U16` | `U16` (alias) |
| Documentation | Included hardware-dispatch note | Removed hardware-dispatch and import notes (streamlined) |

### Mathematical Representation

The file contains two theorems specifying `encoding.gf.unaccelerated.mul`:

#### `mul_spec'` — Polynomial-level postcondition

```
theorem mul_spec' (a b : U16) :
    mul a b ⦃ result =>
      natToBinaryPoly result.val =
        (natToBinaryPoly a.val * natToBinaryPoly b.val) %ₘ polyGF2 ⦄
```

This states that the Rust function `mul(a, b)` — which composes `poly_mul` (carry-less long multiplication) with `poly_reduce` (table-based reduction) — produces a result whose binary polynomial representation equals the product of the input polynomials reduced modulo `polyGF2 = X¹⁶ + X¹² + X³ + X + 1`. The proof proceeds by unfolding `mul` and applying the `step*` tactic, which automatically chains the `@[step]`-tagged subspecifications `poly_mul_spec` and `poly_reduce_spec`.

#### `mul_spec` — GF(2¹⁶)-level postcondition

```
theorem mul_spec (a b : U16) :
    mul a b ⦃ (result : U16) =>
      result.val.toGF216 = a.val.toGF216 * b.val.toGF216 ⦄
```

This lifts the polynomial-level result to the abstract field `GF216 = GaloisField 2 16` via the ring homomorphism `BinaryPoly.toGF216 : BinaryPoly →+* GF216`. The proof:
1. Obtains the polynomial-level identity from `mul_spec'`.
2. Applies `ringHom_modByMonic` to show that the ring homomorphism commutes with `%ₘ polyGF2` (since `BinaryPoly.toGF216` vanishes on `polyGF2`).
3. Uses `map_mul` to distribute the homomorphism over multiplication.

---

## 2. `Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean`

### Rust Source
`spqr/src/encoding/gf.rs`, lines 489–498.

### Status
**Completely rewritten: old bit-by-bit approach replaced with table-based two-pass specification, fully proved.**

### Changes from Base

| Aspect | Before (469d5b3) | After (HEAD) |
|--------|-------------------|--------------|
| Lines | 216 | 329 |
| Approach | Bit-by-bit recursive `polyMod` | Table-based two-pass `polyReduceSpec` |
| Import | `Spqr.Code.Funs` | `Spqr.Specs.Encoding.Gf.Reduce.ReduceBytes` |
| Key definition | `polyMod` (recursive bit clearing) | `polyReduceSpec` (two byte-level table lookups) |
| Algebraic bridge | `polyMod_poly` (GF(2)[X] formulation) | `xor_table_shift_dvd` + `polyReduceSpec_correct` |
| Main theorem | `poly_reduce_poly_mul_spec` (`sorry`) | `poly_reduce_spec` (fully proved) |
| Namespace | `spqr.encoding.gf.reduce` | `spqr.encoding.gf.reduce` (unchanged) |

### Mathematical Representation

#### `polyReduceSpec` — Spec-level definition

```
def polyReduceSpec (v : Nat) : Nat :=
  let t1 := reduceByteTable (v >>> 24)
  let v1 := v ^^^ (t1 <<< 8)
  let t2 := reduceByteTable ((v1 >>> 16) &&& 255)
  (v1 ^^^ t2) % 2 ^ 16
```

This mirrors the Rust two-pass reduction exactly: extract the high byte, look up its reduction in `REDUCE_BYTES`, XOR-shift it in; then extract the next byte, look up, XOR in; return the low 16 bits.

#### `polyReduceSpec_correct` — Algebraic correctness

```
theorem polyReduceSpec_correct (v : Nat) (hv : v < 2 ^ 32)
    (htable : ∀ k, k < 256 → natToBinaryPoly (reduceByteTable k) =
      (natToBinaryPoly k * X ^ 16) %ₘ polyGF2) :
    natToBinaryPoly (polyReduceSpec v) = (natToBinaryPoly v) %ₘ polyGF2
```

This proves that the two-pass table reduction computes the correct polynomial remainder. The proof strategy:
1. Decomposes `v` into byte lanes (bits 24–31, 16–23, 0–15).
2. Uses `xor_table_shift_dvd` to show each XOR step preserves congruence modulo `polyGF2`.
3. Shows the final 16-bit result has degree < 16 and hence equals its own `%ₘ polyGF2`.

#### `poly_reduce_spec` — Full Aeneas-level spec

```
theorem poly_reduce_spec (v : Std.U32) :
    poly_reduce v ⦃ result =>
      natToBinaryPoly result.val = (natToBinaryPoly v.val) %ₘ polyGF2 ⦄
```

This connects the extracted Lean function `poly_reduce` to the mathematical specification. The proof unfolds the function, steps through the Aeneas-generated code, establishes value-level equalities for each intermediate variable (`i`, `i1`, `i2`, `i3`, `i4`, `v1`, `i5`, `shifted_v`, `i21`, `i6`, `i7`, `v2`), bridges to `polyReduceSpec`, and invokes `polyReduceSpec_correct`.

### Key Differences from Old Approach
- **Old**: Used a recursive bit-by-bit `polyMod` definition that cleared one bit at a time from position 16 upward; required an intermediate `polyMod_poly` GF(2)[X] formulation and a congruence-preservation lemma. The final theorem was `sorry`-ed.
- **New**: Uses the actual table-based two-pass algorithm matching the Rust implementation; proves correctness via divisibility of XOR-shift contributions by `polyGF2`; the final theorem is fully proved.

---

## 3. `Spqr/Specs/Encoding/Gf/ParallelMult.lean`

### Rust Source
`spqr/src/encoding/gf.rs`, lines 566–579.

### Status
**Newly created (did not exist at base). Fully proved.**

### Mathematical Representation

The file specifies `encoding.gf.parallel_mult`, which multiplies every element of a `Slice GF16` by a shared multiplier `a` in GF(2¹⁶). The implementation processes elements in pairs via `mul2_u16` (shared-left-operand double-product), with a trailing single-element fix-up if the slice has odd length.

#### `parallel_mult_loop_body_spec'` — Polynomial-level loop body

```
theorem parallel_mult_loop_body_spec'
    (a : encoding.gf.GF16) (into : Slice encoding.gf.GF16) (i : Std.Usize)
    (hi : i.val + 2 ≤ Std.Usize.max) :
    parallel_mult_loop.body a into i ⦃ cf =>
      match cf with
      | ControlFlow.done (a', into', i') =>
          a' = a ∧ into' = into ∧ i' = i ∧ into.length < i.val + 2
      | ControlFlow.cont (s, i') =>
          i.val + 2 ≤ into.length ∧
          i'.val = i.val + 2 ∧
          s.length = into.length ∧
          natToBinaryPoly (s.val[i.val]!).value.val =
            (natToBinaryPoly a.value.val *
             natToBinaryPoly (into.val[i.val]!).value.val) %ₘ polyGF2 ∧
          natToBinaryPoly (s.val[i.val + 1]!).value.val =
            (natToBinaryPoly a.value.val *
             natToBinaryPoly (into.val[i.val + 1]!).value.val) %ₘ polyGF2 ⦄
```

#### `parallel_mult_loop_body_spec` — GF(2¹⁶)-level loop body with frame

Lifts to `GF216` and adds a **frame condition**: all slice elements outside `{i, i+1}` are unchanged.

#### `parallel_mult_loop_spec` — Full loop specification

```
theorem parallel_mult_loop_spec
    (a : encoding.gf.GF16) (into : Slice encoding.gf.GF16) (i : Std.Usize)
    (hlen : into.length + 2 ≤ Std.Usize.max) (hi : i.val ≤ into.length) :
    parallel_mult_loop a into i ⦃ (a', into', i') =>
      a' = a ∧
      into'.length = into.length ∧
      into.length < i'.val + 2 ∧
      i.val ≤ i'.val ∧
      i'.val ≤ into'.length ∧
      (∀ j, i.val ≤ j → j < i'.val →
        (into'.val[j]!).toGF216 = a.toGF216 * (into.val[j]!).toGF216) ∧
      (∀ j, i'.val ≤ j → j < into'.length →
        (into'.val[j]!) = (into.val[j]!)) ∧
      (∀ j, j < i.val →
        (into'.val[j]!) = (into.val[j]!)) ⦄
```

The proof uses `loop.spec_decr_nat` with the natural-number measure `into.length − i.val` and a loop invariant tracking processed/unprocessed/before-range elements.

#### `parallel_mult_spec` — Top-level function specification

```
theorem parallel_mult_spec
    (a : encoding.gf.GF16) (into : Slice encoding.gf.GF16)
    (hlen : into.length + 2 ≤ Std.Usize.max) :
    parallel_mult a into ⦃ (result : Slice encoding.gf.GF16) =>
      result.length = into.length ∧
      (∀ j, j < result.length →
        (result.val[j]!).toGF216 = a.toGF216 * (into.val[j]!).toGF216) ⦄
```

Postconditions: length preserved; every element is the GF(2¹⁶) product of `a` with the original.

---

## 4. `Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolate.lean`

### Rust Source
`spqr/src/encoding/polynomial.rs`, lines 106–137.

### Status
**Newly created (did not exist at base). Fully proved.**

### Mathematical Representation

The file specifies `Poly.lagrange_interpolate`, which computes the unique polynomial of degree `< pts.len()` interpolating a set of evaluation points over GF(2¹⁶).

#### `lagrange_interpolate_formula` — Structural specification

```
theorem lagrange_interpolate_formula
    (pts : Slice Pt) (h_len : pts.val.length + 1 ≤ Std.Usize.max) :
    lagrange_interpolate pts ⦃ (result : Poly) =>
      result.coefficients.val.length = pts.val.length ∧
      (pts.val.length = 0 → result.toGF216Poly = 0) ∧
      (0 < pts.val.length →
        ∃ ws : List Poly,
          ws.length = pts.val.length ∧
          (∀ i, ws[i].toGF216Poly * (X - C(pts[i].x.toGF216)) =
              X * C(lagrangeScaleGF216 pts[i] pts.val) *
                prodLinearFactors pts.val 0 pts.val.length) ∧
          (∀ j, result.coefficients[j].toGF216 =
              (ws.map (fun w => w.coefficients[j+1].toGF216)).sum)) ⦄
```

This establishes:
- **Length**: result has `pts.len()` coefficients.
- **Empty case**: zero polynomial for empty input.
- **Witness polynomials**: a list `ws` of per-iteration scratch polynomials satisfying both the algebraic identity (each `ws[i]` times `(X − pts[i].x)` equals the scaled template) and the cumulative XOR-accumulation property (characteristic-2 summation of shifted coefficients).

#### `lagrange_interpolate_spec` — Classical formula

```
theorem lagrange_interpolate_spec
    (pts : Slice Pt) (h_len : pts.val.length + 1 ≤ Std.Usize.max) :
    lagrange_interpolate pts ⦃ (result : Poly) =>
      result.toGF216Poly = lagrangeInterpolantSum pts.val pts.val.length ⦄
```

This shows the result equals the classical Lagrange interpolant:

```
lagrangeInterpolantSum pts n =
  ∑_{i=0}^{n−1} C(lagrangeScaleGF216 pts[i] pts) * lagrangeBasisPoly pts i
```

where `lagrangeBasisPoly pts i = ∏_{j ≠ i} (X − pts[j].x)`.

#### Supporting Definitions

- **`lagrangeBasisPoly`**: `∏_{j ≠ i} (X − pts[j].x.toGF216)` — the Lagrange basis polynomial excluding point `i`.
- **`lagrangeInterpolantSum`**: Recursive partial sum of `C(lagrangeScaleGF216 pts[i] pts) * lagrangeBasisPoly pts i`.
- **Helper lemmas**: `prodLinearFactors_split_at`, `prodLinearFactors_eq_factor_mul_basis`, `getElem_bang_toGF216_eq_coeff`, degree bounds for `prodLinearFactors` and `lagrangeBasisPoly`, and `list_map_sum_eq_finset_sum` (converting `List.map/sum` to `Finset.sum`).

The proof of `lagrange_interpolate_spec` applies `lagrange_interpolate_formula`, then for each witness polynomial cancels `(X − pts[i].x)` from both sides (valid in the integral domain `GF216[X]`), identifies each `ws[i]` as `X * C(scale) * lagrangeBasisPoly`, and uses the "divide by X" trick (reading coefficients at position `j+1`) to recover the classical formula.

---

## 5. `Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolatePrepare.lean`

### Rust Source
`spqr/src/encoding/polynomial.rs`, lines 144–163.

### Status
**Newly created (did not exist at base). Fully proved.**

### Mathematical Representation

The file specifies `Poly.lagrange_interpolate_prepare`, which builds the product polynomial `∏_{j=0}^{n−1} (X − pts[j].x)` used as the "template" in Lagrange interpolation.

#### Loop Body — `body_spec`

```
theorem body_spec
    (pts : Slice Pt) (offset : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (p : Poly)
    (...preconditions...) :
    body pts offset iter p ⦃ cf =>
      match cf with
      | ControlFlow.done r => r = p ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, p1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start + 1 ∧
          iter1.end = iter.end ∧
          p1.coefficients.length = p.coefficients.length ∧
          (∀ j, offset − iter.start ≤ j+1 → j+1 < p.coefficients.length →
            p1[j].toGF216 = p[j].toGF216 − p[j+1].toGF216 * pts[iter.start].x.toGF216) ∧
          (frame condition for unmodified positions) ⦄
```

Each iteration retrieves the next index, looks up `pts[i].x`, and calls `mult_xdiff_assign_trailing(offset − i, pts[i].x)` to multiply the trailing sub-polynomial by `(X − pts[i].x)`.

#### Loop — `loop_spec`

The loop specification uses `loop.spec_decr_nat` with measure `iter.end − iter.start` and tracks:
1. **Length preservation**: coefficient vector length unchanged.
2. **Leading coefficient**: position `offset` is never modified.
3. **Frame**: positions outside `[offset − iter.end, offset)` are unchanged.
4. **Trailing polynomial identity**: the modified positions match `expectedTrailingPoly`, a recurrence defined as:
   ```
   S₀ = C(p[offset].toGF216)
   S_{k+1} = C(p[offset−(k+1)].toGF216) + (X − C(pts[start+k].x.toGF216)) · Sₖ
   ```
   which is shown to equal `prodLinearFactors` via `expectedTrailingPoly_eq_prodLinearFactors`.

#### Top-level — `lagrange_interpolate_prepare_spec`

```
theorem lagrange_interpolate_prepare_spec
    (pts : Slice Pt) (h_len : pts.val.length + 1 ≤ Std.Usize.max) :
    lagrange_interpolate_prepare pts ⦃ (result : Poly) =>
      result.coefficients.val.length = pts.val.length + 1 ∧
      result.coefficients.val[pts.val.length]? = some ONE ∧
      (leading coefficient maps to 1 in GF216) ∧
      (∀ m ≤ pts.val.length, result[m].toGF216 =
        (prodLinearFactors pts.val 0 pts.val.length).coeff m) ∧
      result.toGF216Poly = prodLinearFactors pts.val 0 pts.val.length ⦄
```

Postconditions:
- **Length**: `pts.len() + 1` coefficients.
- **Leading coefficient**: `GF16::ONE` at position `pts.len()`, matching the Rust `debug_assert_eq!`.
- **Coefficient-level identity**: each coefficient matches `prodLinearFactors`.
- **Polynomial identity**: `result.toGF216Poly = ∏_{j=0}^{n−1} (X − C(pts[j].x.toGF216))`.

The proof unfolds the function, steps through `Poly::zero`, `Vec::resize`, the `ONE` assignment, and the loop, then bridges the loop's `expectedTrailingPoly` output to `prodLinearFactors` via the bridge lemma `expectedTrailingPoly_eq_prodLinearFactors`. It also handles the initial coefficient vector construction, including the `resize` with `ZERO` fill and the `set` for the leading `ONE`.

---

## Summary of Changes

| File | Base State | Current State | Key Change |
|------|-----------|---------------|------------|
| `Gf/Unaccelerated/Mul.lean` | 87 lines, 2 `sorry` | 97 lines, fully proved | Proofs completed; `ModByMonic` import added; documentation streamlined |
| `Gf/Reduce/PolyReduce.lean` | 216 lines, 1 `sorry` | 329 lines, fully proved | Complete rewrite: bit-by-bit → table-based two-pass; `ReduceBytes` import; new `polyReduceSpec` + `polyReduceSpec_correct` + full Aeneas bridge |
| `Gf/ParallelMult.lean` | Did not exist | 384 lines, fully proved | New file: loop body (poly + GF216 levels with frame), loop (invariant-based), and top-level `parallel_mult` spec |
| `Polynomial/Poly/LagrangeInterpolate.lean` | Did not exist | 642 lines, fully proved | New file: structural formula with witness polynomials + classical Lagrange interpolant sum; helper definitions and degree-bound lemmas |
| `Polynomial/Poly/LagrangeInterpolatePrepare.lean` | Did not exist | 814 lines, fully proved | New file: loop body, loop with trailing-polynomial invariant, and top-level spec proving `result.toGF216Poly = ∏(X − pts[j].x)` |

**Total net change**: +2,143 lines added, −190 lines removed (across 4 files with diffs; 1 file unchanged path but with content changes).

All five specifications are now **fully proved** (no `sorry` remains) and establish a verified chain from the Aeneas-extracted Lean functions to their mathematical specifications in GF(2¹⁶) and GF(2¹⁶)[X].
