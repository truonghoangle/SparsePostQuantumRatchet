# Specification Report: GF(2¹⁶) and Polynomial Verification


---

## 1. `Spqr/Specs/Encoding/Gf/Unaccelerated/Mul.lean`

### Rust Source
`spqr/src/encoding/gf.rs`, lines 444–446.


### Mathematical Representation

The file contains two theorems specifying `encoding.gf.unaccelerated.mul`:

#### `mul_spec'` — Polynomial-level postcondition

```
theorem mul_spec' (a b : U16) :
    mul a b ⦃ result =>
      natToBinaryPoly result.val =
        (natToBinaryPoly a.val * natToBinaryPoly b.val) %ₘ polyGF2 ⦄
```

**In words:** Given two 16-bit unsigned integers `a` and `b`, the Rust function `mul(a, b)` returns a result whose binary polynomial representation equals the product of the input polynomials, reduced modulo the irreducible polynomial polyGF2 = X¹⁶ + X¹² + X³ + X + 1. That is, interpreting all values as polynomials over GF(2), the output is the remainder of `a(X) · b(X)` divided by polyGF2.

The proof proceeds by unfolding `mul` and applying the `step*` tactic, which automatically chains the `@[step]`-tagged subspecifications `poly_mul_spec` and `poly_reduce_spec`.

#### `mul_spec` — GF(2¹⁶)-level postcondition

```
theorem mul_spec (a b : U16) :
    mul a b ⦃ (result : U16) =>
      result.val.toGF216 = a.val.toGF216 * b.val.toGF216 ⦄
```

**In words:** The Rust function `mul(a, b)` computes the product of `a` and `b` as elements of the finite field GF(2¹⁶). When each 16-bit integer is mapped to its corresponding field element via the canonical embedding `toGF216`, the result of `mul` maps to the field-theoretic product of the images of `a` and `b`.

This lifts the polynomial-level result to the abstract field `GF216 = GaloisField 2 16` via the ring homomorphism `BinaryPoly.toGF216 : BinaryPoly →+* GF216`. The proof:
1. Obtains the polynomial-level identity from `mul_spec'`.
2. Applies `ringHom_modByMonic` to show that the ring homomorphism commutes with `%ₘ polyGF2` (since `BinaryPoly.toGF216` vanishes on `polyGF2`).
3. Uses `map_mul` to distribute the homomorphism over multiplication.



---

## 2. `Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean`

### Rust Source
`spqr/src/encoding/gf.rs`, lines 489–498.


### Mathematical Representation

#### `polyReduceSpec` — Spec-level definition

```
def polyReduceSpec (v : Nat) : Nat :=
  let t1 := reduceByteTable (v >>> 24)
  let v1 := v ^^^ (t1 <<< 8)
  let t2 := reduceByteTable ((v1 >>> 16) &&& 255)
  (v1 ^^^ t2) % 2 ^ 16
```

**In words:** This is a pure specification-level function that mirrors the Rust two-pass reduction exactly: extract the high byte (bits 24–31), look up its reduction in `REDUCE_BYTES`, XOR-shift the result into the value; then extract the next byte (bits 16–23), look up its reduction, XOR it in; finally return the low 16 bits as the fully reduced GF(2¹⁶) representative.

#### `polyReduceSpec_correct` — Algebraic correctness

```
theorem polyReduceSpec_correct (v : Nat) (hv : v < 2 ^ 32)
    (htable : ∀ k, k < 256 → natToBinaryPoly (reduceByteTable k) =
      (natToBinaryPoly k * X ^ 16) %ₘ polyGF2) :
    natToBinaryPoly (polyReduceSpec v) = (natToBinaryPoly v) %ₘ polyGF2
```

**In words:** For any 32-bit value `v`, assuming the reduction table is correct (i.e., each entry `reduceByteTable[k]` represents the polynomial remainder of `k · X¹⁶` modulo polyGF2), the spec-level two-pass reduction `polyReduceSpec(v)` — when interpreted as a GF(2) polynomial — equals the polynomial remainder of `v` modulo polyGF2 = X¹⁶ + X¹² + X³ + X + 1.

The proof strategy:
1. Decomposes `v` into byte lanes (bits 24–31, 16–23, 0–15).
2. Uses `xor_table_shift_dvd` to show each XOR step preserves congruence modulo `polyGF2`.
3. Shows the final 16-bit result has degree < 16 and hence equals its own `%ₘ polyGF2`.

#### `poly_reduce_spec` — Full Aeneas-level spec

```
theorem poly_reduce_spec (v : Std.U32) :
    poly_reduce v ⦃ result =>
      natToBinaryPoly result.val = (natToBinaryPoly v.val) %ₘ polyGF2 ⦄
```

**In words:** The Rust function `poly_reduce`, given a 32-bit unsigned integer `v` representing an unreduced carry-less product, returns a 16-bit result whose GF(2) polynomial representation is the remainder of `v(X)` modulo polyGF2 = X¹⁶ + X¹² + X³ + X + 1. This is the canonical degree-< 16 representative of `v` in the quotient ring GF(2)[X]/(polyGF2).

This connects the extracted Lean function `poly_reduce` to the mathematical specification. The proof unfolds the function, steps through the Aeneas-generated code, establishes value-level equalities for each intermediate variable (`i`, `i1`, `i2`, `i3`, `i4`, `v1`, `i5`, `shifted_v`, `i21`, `i6`, `i7`, `v2`), bridges to `polyReduceSpec`, and invokes `polyReduceSpec_correct`.

### Key Differences from Old Approach

The previous version (base commit `01eefaa`) took a fundamentally different approach to specifying and proving `poly_reduce`. Below is a detailed comparison.

#### Old Approach (216 lines, 3 `sorry`)

1. **Spec-level definition — `polyMod`**: A recursive bit-by-bit reduction operating on natural numbers. It iterated from bit position 16 up to bit `n + 15`, testing each high-order bit and XOR-ing with the shifted irreducible polynomial `0x1100b <<< k` to clear it:

    ```
    def polyMod (v : Nat) : (n : Nat) → Nat
      | 0     => v
      | n + 1 =>
        let v' := polyMod v n
        if v'.testBit (n + 16)
        then v' ^^^ (0x1100b <<< n)
        else v'
    ```

    This definition is mathematically natural (it mirrors textbook polynomial long division over GF(2)) but does **not** match the Rust implementation, which uses precomputed byte-level table lookups rather than bit-by-bit clearing.

2. **Algebraic bridge — `polyMod_poly`**: A `noncomputable` GF(2)[X] formulation that re-expressed `polyMod` in terms of polynomial arithmetic — replacing XOR with polynomial addition, bit-shifts with multiplication by `X^n`, and `testBit` with coefficient checks:

    ```
    noncomputable def polyMod_poly (p : (ZMod 2)[X]) : (n : Nat) → (ZMod 2)[X]
      | 0     => p
      | n + 1 =>
        let p' := polyMod_poly p n
        if p'.coeff (n + 16) ≠ 0
        then p' + POLY_GF2 * X ^ n
        else p'
    ```

3. **Correspondence lemma — `polyMod_eq_polyMod_poly`** (`sorry`-ed): Stated that interpreting the natural-number input as a GF(2) polynomial via `natToGF2Poly`, the Nat-level `polyMod` and the algebraic `polyMod_poly` agree:

    ```
    theorem polyMod_eq_polyMod_poly (v n : Nat) :
        natToGF2Poly (polyMod v n) = polyMod_poly (natToGF2Poly v) n := by sorry
    ```

    **In words:** The bitwise XOR/shift operation `polyMod` on natural numbers is faithfully represented by the polynomial operation `polyMod_poly` on GF(2)[X]: converting the input to a polynomial, applying `polyMod_poly`, gives the same result as applying `polyMod` to the natural number and then converting.

    This required proving that XOR on naturals corresponds to polynomial addition, and that `testBit` corresponds to coefficient extraction — a tedious bitwise-to-polynomial correspondence argument.

4. **Congruence lemma — `polyMod_poly_eq_modByMonic`** (`sorry`-ed): Stated that the recursive `polyMod_poly` computes the true polynomial remainder:

    ```
    theorem polyMod_poly_eq_modByMonic (p : (ZMod 2)[X]) (n : Nat)
        (hp : p.natDegree < n + 16) (hirr : POLY_GF2.Monic) :
        polyMod_poly p n = p %ₘ POLY_GF2 := by sorry
    ```

    **In words:** For any GF(2) polynomial `p` whose degree is less than `n + 16`, applying `n` steps of the recursive `polyMod_poly` reduction yields the same result as computing the true polynomial remainder `p mod POLY_GF2`. In particular, for a degree-≤ 30 product of two 16-bit polynomials, 16 steps suffice.

    Proving this would require an induction on `n` with a degree-drop argument at each step — showing that each XOR step preserves the congruence class modulo `POLY_GF2` and strictly reduces the degree.

5. **Final spec — `poly_reduce_spec`** (`sorry`-ed): The postcondition was stated at the **Nat level** (`result.val = polyMod v.val 16`) rather than at the polynomial level, and was `sorry`-ed because the table-based Rust implementation could not be directly connected to the bit-by-bit `polyMod` without first proving the table correctness:

    ```
    theorem poly_reduce_spec (v : Std.U32) :
        poly_reduce v ⦃ result => result.val = polyMod v.val 16 ⦄ := by sorry
    ```

    **In words:** The Rust function `poly_reduce(v)` returns a value equal to 16 steps of the recursive bit-by-bit polynomial modular reduction `polyMod` applied to `v`. This was `sorry`-ed because the Rust code uses table lookups, not bit-by-bit clearing, and the equivalence was not proved.

6. **Structural issues**: The approach required a three-step proof chain (`poly_reduce` → `polyMod` → `polyMod_poly` → `%ₘ polyGF2`) with two `sorry`-ed bridge lemmas. The `polyMod` definition also did not match the Rust code's byte-level table-lookup strategy, creating an additional gap between implementation and specification. A separate `reduceFromByte` definition was present but unused in the main proof path.

#### New Approach (329 lines, 0 `sorry`)

1. **Spec-level definition — `polyReduceSpec`**: Directly mirrors the Rust two-pass table-based algorithm — extract the high byte, look up `reduceByteTable`, XOR-shift, extract the next byte, look up, XOR, return low 16 bits:

    ```
    def polyReduceSpec (v : Nat) : Nat :=
      let t1 := reduceByteTable (v >>> 24)
      let v1 := v ^^^ (t1 <<< 8)
      let t2 := reduceByteTable ((v1 >>> 16) &&& 255)
      (v1 ^^^ t2) % 2 ^ 16
    ```

2. **Divisibility lemma — `xor_table_shift_dvd`**: Shows that each XOR-shift step preserves the congruence class modulo `polyGF2` by proving `polyGF2 ∣ (natToBinaryPoly k * X^(n+16) + natToBinaryPoly (reduceByteTable k) * X^n)`. This uses the table correctness hypothesis and `modByMonic_add_div`.

3. **Algebraic correctness — `polyReduceSpec_correct`**: Proves `natToBinaryPoly (polyReduceSpec v) = (natToBinaryPoly v) %ₘ polyGF2` in a single direct argument:
   - Decomposes `v` into byte lanes via bitwise analysis.
   - Applies `xor_table_shift_dvd` twice (once per pass) to show the accumulated XOR difference is divisible by `polyGF2`.
   - Shows the final 16-bit result has degree < 16 and hence equals its own `%ₘ polyGF2` via `modByMonic_eq_self_iff`.

4. **Full Aeneas bridge — `poly_reduce_spec`**: Steps through all 12+ intermediate variables in the Aeneas-generated code, establishing value-level equalities for each, then bridges to `polyReduceSpec` and invokes `polyReduceSpec_correct`. The postcondition is stated directly at the **polynomial level** (`natToBinaryPoly result.val = (natToBinaryPoly v.val) %ₘ polyGF2`), eliminating the need for any intermediate Nat-level spec.

#### Summary of Improvements

| Aspect | Old | New |
|--------|-----|-----|
| Spec definition | `polyMod`: bit-by-bit recursive clearing | `polyReduceSpec`: two-pass table lookup (matches Rust) |
| Proof chain length | 3 hops: `poly_reduce` → `polyMod` → `polyMod_poly` → `%ₘ` | 2 hops: `poly_reduce` → `polyReduceSpec` → `%ₘ` |
| Bridge lemmas | 2 (`sorry`-ed): Nat↔poly correspondence + recursive congruence | 1 (proved): `xor_table_shift_dvd` divisibility |
| Postcondition level | Nat-level (`result.val = polyMod v.val 16`) | Polynomial-level (`natToBinaryPoly result.val = ... %ₘ polyGF2`) |
| `sorry` count | 3 | 0 |
| Implementation fidelity | Does not match Rust (bit-by-bit vs. table) | Directly mirrors Rust's byte-level table algorithm |

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

**In words:** One iteration of the `parallel_mult` loop body processes a pair of consecutive slice elements at positions `i` and `i+1`. If fewer than 2 elements remain (the loop is done), the state is unchanged. Otherwise (the loop continues), the index advances by 2, the slice length is preserved, and both `into[i]` and `into[i+1]` are replaced by their GF(2¹⁶) products with `a` — expressed here at the polynomial level as carry-less multiplication reduced modulo polyGF2.

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

**In words:** After the loop completes starting from index `i`, the multiplier `a` is unchanged, the slice length is preserved, and the slice is partitioned into three regions: (1) elements before `i` are untouched, (2) elements from `i` up to the final index `i'` have each been multiplied by `a` in GF(2¹⁶), and (3) elements from `i'` onward (at most one trailing element) are untouched. The loop terminates when fewer than 2 elements remain to process.

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

**In words:** The Rust function `parallel_mult(a, into)` returns a slice of the same length as `into`, where every element has been replaced by its GF(2¹⁶) product with `a`. That is, for each index `j` in the result, `result[j]` equals `a * into[j]` as elements of the finite field GF(2¹⁶).

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

**In words:** The Rust function `lagrange_interpolate(pts)` returns a polynomial with exactly `pts.len()` coefficients. If the input is empty, the result is the zero polynomial. Otherwise, there exist "witness" polynomials `ws[0], …, ws[n−1]` — one per evaluation point — such that: (1) each witness `ws[i]`, when multiplied by the linear factor `(X − pts[i].x)`, equals a scaled copy of the full product-of-linear-factors template; and (2) each coefficient of the result is the characteristic-2 sum (XOR) of the corresponding shifted coefficients of all witnesses. This structural specification captures exactly how the Rust loop accumulates partial results via XOR.

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

**In words:** The Rust function `lagrange_interpolate(pts)` computes the classical Lagrange interpolating polynomial over GF(2¹⁶). Specifically, the result — interpreted as a polynomial in GF(2¹⁶)[X] — equals the sum `∑ᵢ cᵢ · Lᵢ(X)`, where `cᵢ` is the scaled y-value for point `i` and `Lᵢ(X) = ∏_{j≠i} (X − xⱼ)` is the Lagrange basis polynomial that is zero at all evaluation points except `xᵢ`.

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

**In words:** One iteration of the loop body either terminates (if the iterator range is exhausted, returning the polynomial unchanged) or continues by: advancing the iterator by one, preserving the coefficient vector length, and updating each coefficient in the trailing range via the recurrence `p1[j] = p[j] − p[j+1] · pts[i].x` (which is the in-place multiplication of the trailing sub-polynomial by the linear factor `(X − pts[i].x)`). Coefficients outside the affected range are unchanged.

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

**In words:** The Rust function `lagrange_interpolate_prepare(pts)` returns a monic polynomial of degree `pts.len()` (i.e., with `pts.len() + 1` coefficients and leading coefficient 1) that equals the product of all linear factors `∏_{j=0}^{n−1} (X − pts[j].x)` over GF(2¹⁶). Each coefficient of the result matches the corresponding coefficient of this product polynomial, and the leading coefficient is `GF16::ONE`.

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
| `Gf/Reduce/PolyReduce.lean` | 216 lines, 3 `sorry` | 329 lines, fully proved | Complete rewrite: bit-by-bit → table-based two-pass; `ReduceBytes` import; new `polyReduceSpec` + `polyReduceSpec_correct` + full Aeneas bridge |
| `Gf/ParallelMult.lean` | Did not exist | 384 lines, fully proved | New file: loop body (poly + GF216 levels with frame), loop (invariant-based), and top-level `parallel_mult` spec |
| `Polynomial/Poly/LagrangeInterpolate.lean` | Did not exist | 642 lines, fully proved | New file: structural formula with witness polynomials + classical Lagrange interpolant sum; helper definitions and degree-bound lemmas |
| `Polynomial/Poly/LagrangeInterpolatePrepare.lean` | Did not exist | 814 lines, fully proved | New file: loop body, loop with trailing-polynomial invariant, and top-level spec proving `result.toGF216Poly = ∏(X − pts[j].x)` |

**Total net change**: +2,143 lines added, −190 lines removed (across 4 files with diffs; 1 file unchanged path but with content changes).

All five specifications are now **fully proved** (no `sorry` remains) and establish a verified chain from the Aeneas-extracted Lean functions to their mathematical specifications in GF(2¹⁶) and GF(2¹⁶)[X].
