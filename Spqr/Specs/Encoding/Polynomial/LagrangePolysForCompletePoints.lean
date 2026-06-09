/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyConstN.LagrangeInterpolatePt
import Spqr.Specs.Encoding.Gf.GF16.New
/-!
# Spec theorem for `lagrange_polys_for_complete_points`: loop body 0

The Rust function `lagrange_polys_for_complete_points` (in `src/encoding/polynomial.rs`, lines
469:0-496:1) precomputes the array of Lagrange basis polynomials for the "complete points" —
evaluation points `0, 1, …, N−1` in GF(2¹⁶) with `y`-coordinate `GF16::ONE`.  The function begins
by constructing an array `ones` of `N` copies of `Pt { x: GF16::ZERO, y: GF16::ONE }`, then runs a
`while i < N` loop (lines 477:8-482:9) that sets `ones[i].x.value = i as u16` for each index `i`.

This file specifies **loop body 0** — one iteration of that initialisation loop.  The extracted
Lean function `encoding.polynomial.lagrange_polys_for_complete_points_loop0.body` performs one step:

  1. **Done** (`i ≥ N`): the loop terminates and the array `ones` is returned unchanged.
  2. **Continue** (`i < N`):
     a. Reads `ones[i]` and updates `ones[i].x.value := i` (cast from `usize` to `u16`).
     b. The `y` field of `ones[i]` is set to `GF16::ONE`.
     c. All other entries `ones[j]` for `j ≠ i` are left unchanged.
     d. Advances the loop counter: `i1 = i + 1`.

At the end of the full loop (after `N` iterations starting from `i = 0`), every entry satisfies:
  - `ones[j].x.value.val = j` — the raw `u16` bit pattern is the loop index.
  - `ones[j].y = GF16::ONE` — the `y`-coordinate is the multiplicative identity.

Semantically, `ones[j].x.toGF216 = Nat.toGF216 j` — the `j`-th distinct element of GF(2¹⁶) under
the canonical embedding `Nat.toGF216 = BinaryPoly.toGF216 ∘ natToBinaryPoly`.  These evaluation
points are subsequently used as the "complete points" for Lagrange interpolation in the second loop
of `lagrange_polys_for_complete_points`.

In GF(2¹⁶), the elements `0, 1, …, N−1` (for `N ≤ 2¹⁶`) are pairwise distinct because the
canonical map `Nat → GF(2¹⁶)` is injective on `{0, …, 2¹⁶ − 1}` (each natural number below `2¹⁶`
has a unique binary polynomial representative of degree < 16).

**Source**: spqr/src/encoding/polynomial.rs (lines 477:8-482:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop0

/--
**Spec theorem for `encoding.polynomial.lagrange_polys_for_complete_points_loop0.body`**:

One step of the initialisation loop in `lagrange_polys_for_complete_points`, which sets the
`x`-coordinate of `ones[i]` to the GF(2¹⁶) element with raw value `i`.  Given the point array
`ones` of size `N` and the loop counter `i`, the body processes one index:

• The function always succeeds (no panic) provided the preconditions hold, since:
    1. The array access `ones[i]` is bounded by `i < N`.
    2. The `usize`-to-`u16` cast is safe for `i.val < N.val ≤ 65536`.
    3. The array update `ones[i] := …` is in bounds.
    4. The increment `i + 1` does not overflow `usize`.

• In the **done** case (`i ≥ N`):
    `ones' = ones` — the array is returned unchanged and the loop terminates.

• In the **cont** case (`i < N`):
    - The loop counter has advanced: `i1.val = i.val + 1`.
    - The updated array `ones1` satisfies at position `i`:
        - `ones1[i].x.value.val = i.val` — the `x`-coordinate raw `u16` value equals the
          loop index.
        - `ones1[i].y = GF16.ONE` — the `y`-coordinate is set to the multiplicative identity.
    - All other positions are unchanged:
        `ones1.val[j]? = ones.val[j]?` for `j ≠ i.val`.
    - Equivalently, lifting the `x`-coordinate into `GF216`:
        `ones1[i].x.toGF216 = Nat.toGF216 i.val`
      where the right-hand side is the GF(2¹⁶) element represented by the natural number
      `i.val` under the canonical map `Nat.toGF216 = BinaryPoly.toGF216 ∘ natToBinaryPoly`.

**Source**: spqr/src/encoding/polynomial.rs (lines 477:8-482:9)
-/
@[step]
theorem body_spec
    {N : Usize}
    (ones : Array Pt N)
    (i : Usize)
    (h_N_bound : N.val ≤ 65536) :
    body ones i ⦃ cf =>
      match cf with
      | ControlFlow.done ones' =>
          ones' = ones ∧ ¬ (i.val < N.val)
      | ControlFlow.cont (ones1, i1) =>
          i.val < N.val ∧
          i1.val = i.val + 1 ∧
          (∀ (h_idx : i.val < ones1.val.length),
            (ones1.val.get ⟨i.val, h_idx⟩).x.value.val = i.val ∧
            (ones1.val.get ⟨i.val, h_idx⟩).y = GF16.ONE) ∧
          (∀ (j : Nat), j ≠ i.val → ones1.val[j]? = ones.val[j]?) ⦄ := by
  unfold body
  by_cases h_lt : i.val < N.val
  · -- Continue case: i < N
    simp only [UScalar.lt_equiv, h_lt, ↓reduceIte, not_true_eq_false, and_false,
      List.Vector.length_val, List.get_eq_getElem, forall_true_left, ne_eq,
      true_and]
    step*
    all_goals simp_all [UScalar.cast_val_eq]
    all_goals omega
  · -- Done case: i ≥ N
    step*

end spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop0


/-!
# Spec theorem for `lagrange_polys_for_complete_points`: loop 0

The Rust function `lagrange_polys_for_complete_points` (in `src/encoding/polynomial.rs`, lines
469:0-496:1) precomputes the array of Lagrange basis polynomials for the "complete points" —
evaluation points `0, 1, …, N−1` in GF(2¹⁶) with `y`-coordinate `GF16::ONE`.  The function begins
by constructing an array `ones` of `N` copies of `Pt { x: GF16::ZERO, y: GF16::ONE }`, then runs a
`while i < N` loop (lines 477:8-482:9) that sets `ones[i].x.value = i as u16` for each index `i`.

This file specifies **loop 0** — the `loop` fixed-point wrapper around the body
(`LagrangePolysForCompletePointsLoopBody0.body_spec`), which iterates over indices `i = 0, 1, …,
N−1` and sets the `x`-coordinate of each point to the corresponding GF(2¹⁶) element.

At each step, the body processes index `i`:
  1. **Done** (`i ≥ N`): the loop terminates and `ones` is returned unchanged.
  2. **Continue** (`i < N`):
     a. Updates `ones[i].x.value := i` (cast from `usize` to `u16`).
     b. The `y` field of `ones[i]` is set to `GF16::ONE`.
     c. All other entries `ones[j]` for `j ≠ i` are left unchanged.
     d. Advances the loop counter: `i1 = i + 1`.

**Closed-form postcondition** (after all iterations from `i` to `N−1`):

  - **Processed positions** (`i ≤ j < N`): the `x`-coordinate has been set:
      `result[j].x.value.val = j` and `result[j].y = GF16.ONE`
    Equivalently, lifting the `x`-coordinate into `GF216`:
      `result[j].x.toGF216 = Nat.toGF216 j`.

  - **Unprocessed positions** (`j < i`): the array is unchanged from the input:
      `result[j]? = ones[j]?`

At the call site in `lagrange_polys_for_complete_points`, the loop starts with `i = 0`, so all
positions are processed and every entry satisfies `ones[j].x.value.val = j` and
`ones[j].y = GF16.ONE`.

In GF(2¹⁶), the elements `0, 1, …, N−1` (for `N ≤ 2¹⁶`) are pairwise distinct because the
canonical map `Nat → GF(2¹⁶)` is injective on `{0, …, 2¹⁶ − 1}` (each natural number below `2¹⁶`
has a unique binary polynomial representative of degree < 16).

**Source**: spqr/src/encoding/polynomial.rs (lines 477:8-482:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop0

/--
**Spec theorem for `encoding.polynomial.lagrange_polys_for_complete_points_loop0`**:

The full `while i < N` initialisation loop in `lagrange_polys_for_complete_points`, which sets the
`x`-coordinate of each point `ones[j]` to the GF(2¹⁶) element with raw value `j`.  Given the
point array `ones` of size `N`, and the starting index `i`, the loop processes all indices from
`i` to `N−1` and returns the completed array `result` satisfying:

• The function always succeeds (no panic) provided the preconditions hold, since all array
  accesses and updates are bounded by `N`, and the loop counter `i < N` is checked before any
  operation.

• **Initialisation postcondition** (every position `j ∈ [i, N)` has been set):
    `∀ j, i.val ≤ j → j < N.val →
      result[j].x.value.val = j ∧ result[j].y = GF16.ONE`
  Equivalently, lifting the `x`-coordinate into `GF216`:
    `result[j].x.toGF216 = Nat.toGF216 j`.

• **Unchanged positions** (positions `j < i` are untouched):
    `∀ j, j < i.val → result[j]? = ones[j]?`

**Source**: spqr/src/encoding/polynomial.rs (lines 477:8-482:9)
-/
@[step]
theorem loop_spec
    {N : Usize}
    (ones : Array Pt N)
    (i : Usize)
    (h_N_bound : N.val ≤ 65536)
    (h_i_le_N : i.val ≤ N.val) :
    lagrange_polys_for_complete_points_loop0 ones i
      ⦃ result =>
        (∀ (j : Nat), i.val ≤ j → j < N.val →
          ∀ (hj : j < result.val.length),
            (result.val.get ⟨j, hj⟩).x.value.val = j ∧
            (result.val.get ⟨j, hj⟩).y = GF16.ONE) ∧
        (∀ (j : Nat), j < i.val →
          result.val[j]? = ones.val[j]?) ⦄ := by
  unfold lagrange_polys_for_complete_points_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : (Array Pt N) × Usize) =>
                  N.val - p.2.val)
    (inv := fun (p : (Array Pt N) × Usize) =>
        let ones' := p.1
        let i' := p.2
        i.val ≤ i'.val ∧
        i'.val ≤ N.val ∧
        -- processed positions: x set, y = ONE
        (∀ (j : Nat), i.val ≤ j → j < i'.val →
          ∀ (hj : j < ones'.val.length),
            (ones'.val.get ⟨j, hj⟩).x.value.val = j ∧
            (ones'.val.get ⟨j, hj⟩).y = GF16.ONE) ∧
        -- non-processed positions: unchanged from input ones
        (∀ (j : Nat), ¬(i.val ≤ j ∧ j < i'.val) →
          ones'.val[j]? = ones.val[j]?))
  · -- Body step: prove invariant is preserved and measure decreases
    rintro ⟨ones', i'⟩
      ⟨h_i_le_i', h_i'_le_N, h_proc, h_rest⟩
    simp only [] at h_i_le_i' h_i'_le_N h_proc h_rest ⊢
    have h_body := body_spec ones' i' h_N_bound
    apply WP.spec_mono h_body
    grind
  · -- Initial invariant: no positions processed yet, all unchanged
    grind

end spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop0


/-!
# Spec theorem for `lagrange_polys_for_complete_points`: loop body 1

The Rust function `lagrange_polys_for_complete_points` (in `src/encoding/polynomial.rs`, lines
469:0-496:1) precomputes the array of Lagrange basis polynomials for the "complete points" —
evaluation points `0, 1, …, N−1` in GF(2¹⁶) with `y`-coordinate `GF16::ONE`.  After the first loop
(loop 0, lines 477:8-482:9) initialises the point array `ones` so that `ones[j].x.value = j` and
`ones[j].y = GF16::ONE`, the second loop (loop 1, lines 488:8-493:9) fills the output array `out`
with the Lagrange basis polynomials:

```
while i < N {
    out[i] = PolyConst::<N>::lagrange_interpolate_pt(&ones, i);
    i += 1;
}
```

This file specifies **loop body 1** — one iteration of the Lagrange basis polynomial computation
loop.  The extracted Lean function
`encoding.polynomial.lagrange_polys_for_complete_points_loop1.body` performs one step:

  1. **Done** (`i ≥ N`): the loop terminates and the array `out` is returned unchanged.
  2. **Continue** (`i < N`):
     a. Converts `ones` to a slice `s` via `Array.to_slice`.
     b. Calls `PolyConst.lagrange_interpolate_pt N s i` to compute the `i`-th scaled Lagrange
        basis polynomial for the evaluation points in `ones`.
     c. Updates `out[i] := pc` with the computed polynomial.
     d. Advances the loop counter: `i1 = i + 1`.

At the end of the full loop (after `N` iterations starting from `i = 0`), every entry satisfies:
  - `out[j]` contains the `j`-th scaled Lagrange basis polynomial, i.e.,
      `listToGF216Poly out[j].coefficients.val =
         C (ones[j].y.toGF216 *
             (lagrangeDenomProd ones[j].x (ones.take N) 0) ^ (2¹⁶ − 2)) *
           condProdLinearFactors ones[j].x (ones.take N) 0`

Semantically, each `out[j]` is the `j`-th term of the Lagrange interpolation formula for
the points `ones[0], …, ones[N−1]`.  When the `x`-coordinates are pairwise distinct (which
they are for the "complete points" `0, 1, …, N−1` in GF(2¹⁶)), the denominator is nonzero
and the Fermat-style exponentiation `(lagrangeDenomProd …) ^ (2¹⁶ − 2)` yields the
multiplicative inverse, so the scaling factor reduces to
`ones[j].y / ∏_{k ≠ j} (ones[j].x − ones[k].x)`.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition (`a − b = a + b = a ⊕ b`),
so the linear factors `(X − ones[k].x)` and the differences `ones[j].x − ones[k].x` are
equivalently `(X + ones[k].x)` and `ones[j].x + ones[k].x`.

**Source**: spqr/src/encoding/polynomial.rs (lines 488:8-493:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop


namespace spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop1

/--
**Spec theorem for `encoding.polynomial.lagrange_polys_for_complete_points_loop1.body`**:

One step of the Lagrange basis polynomial computation loop in
`lagrange_polys_for_complete_points`, which computes `out[i] :=
PolyConst::lagrange_interpolate_pt(&ones, i)`.  Given the point array `ones` of size `N`, the
output array `out` of size `N`, and the loop counter `i`, the body processes one index:

• The function always succeeds (no panic) provided the preconditions hold, since:
    1. `Array.to_slice ones` always succeeds for any `Array`.
    2. `lagrange_interpolate_pt N s i` succeeds when `0 < N` and `i < N ≤ s.length`.
    3. `Array.update out i pc` is bounded by `i < N`.
    4. The increment `i + 1` does not overflow `usize` (since `i < N ≤ Usize.max`).

• In the **done** case (`i ≥ N`):
    `out' = out` — the array is returned unchanged and the loop terminates.

• In the **cont** case (`i < N`):
    - The loop counter has advanced: `i1.val = i.val + 1`.
    - The updated array `out1` satisfies at position `i`:
        `listToGF216Poly (out1[i].coefficients.val) =
           C ((ones[i].y.toGF216) *
               (lagrangeDenomProd (ones[i].x) (ones.val.take N) 0) ^ (2¹⁶ − 2)) *
             condProdLinearFactors (ones[i].x) (ones.val.take N) 0`
      This is precisely the `i`-th scaled Lagrange basis polynomial for the evaluation points
      given by `ones`, as specified by `lagrange_interpolate_pt_spec`.
    - All other positions are unchanged:
        `out1.val[j]? = out.val[j]?` for `j ≠ i.val`.

**Source**: spqr/src/encoding/polynomial.rs (lines 488:8-493:9)
-/
@[step]
theorem body_spec
    {N : Usize}
    (ones : Array Pt N)
    (out : Array (PolyConst N) N)
    (i : Usize)
    (h_N_pos : 0 < N.val) :
    body ones out i ⦃ cf =>
      match cf with
      | ControlFlow.done out' => out' = out ∧ ¬ (i.val < N.val)
      | ControlFlow.cont (out1, i1) =>
          i.val < N.val ∧
          i1.val = i.val + 1 ∧
          (∀ (h_idx : i.val < out1.val.length) (hi : i.val < ones.val.length),
            listToGF216Poly (out1.val.get ⟨i.val, h_idx⟩).coefficients.val =
              C ((ones.val.get ⟨i.val, hi⟩).y.toGF216 *
                  (lagrangeDenomProd (ones.val.get ⟨i.val, hi⟩).x
                    (ones.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
                condProdLinearFactors (ones.val.get ⟨i.val, hi⟩).x
                  (ones.val.take N.val) 0) ∧
          (∀ j < out.length, (_: j ≠ i.val) →  out1.val[j]? = out.val[j]?) ⦄ := by
  sorry
/-  unfold body
  split
  · -- Continue case: i < N
    simp
    step*
    grind
  · -- Done case: i ≥ N
    step*
-/
end spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop1

/-!
# Spec theorem for `lagrange_polys_for_complete_points`: loop 1

The Rust function `lagrange_polys_for_complete_points` (in `src/encoding/polynomial.rs`, lines
469:0-496:1) precomputes the array of Lagrange basis polynomials for the "complete points" —
evaluation points `0, 1, …, N−1` in GF(2¹⁶) with `y`-coordinate `GF16::ONE`.  After the first loop
(loop 0, lines 477:8-482:9) initialises the point array `ones` so that `ones[j].x.value = j` and
`ones[j].y = GF16::ONE`, the second loop (loop 1, lines 488:8-493:9) fills the output array `out`
with the Lagrange basis polynomials:

```
while i < N {
    out[i] = PolyConst::<N>::lagrange_interpolate_pt(&ones, i);
    i += 1;
}
```

This file specifies **loop 1** — the `loop` fixed-point wrapper around the body
(`LagrangePolysForCompletePointsLoopBody1.body_spec`), which iterates over indices `i = 0, 1, …,
N−1` and fills each slot of `out` with the corresponding scaled Lagrange basis polynomial.

At each step, the body processes index `i`:
  1. **Done** (`i ≥ N`): the loop terminates and `out` is returned unchanged.
  2. **Continue** (`i < N`):
     a. Converts `ones` to a slice `s` via `Array.to_slice`.
     b. Calls `PolyConst.lagrange_interpolate_pt N s i` to compute the `i`-th scaled Lagrange
        basis polynomial for the evaluation points in `ones`.
     c. Updates `out[i] := pc` with the computed polynomial.
     d. Advances the loop counter: `i1 = i + 1`.

**Closed-form postcondition** (after all iterations from `i` to `N−1`):

  - **Processed positions** (`i ≤ j < N`): the `j`-th Lagrange basis polynomial has been stored:
      `listToGF216Poly (result[j].coefficients.val) =
         C (ones[j].y.toGF216 *
             (lagrangeDenomProd ones[j].x (ones.take N) 0) ^ (2¹⁶ − 2)) *
           condProdLinearFactors ones[j].x (ones.take N) 0`
    Semantically, each `result[j]` is the `j`-th term of the Lagrange interpolation formula for
    the points `ones[0], …, ones[N−1]`.

  - **Unprocessed positions** (`j < i`): the array is unchanged from the input:
      `result[j]? = out[j]?`

At the call site in `lagrange_polys_for_complete_points`, the loop starts with `i = 0`, so all
positions are processed and every entry contains the corresponding Lagrange basis polynomial.

When the `x`-coordinates are pairwise distinct (which they are for the "complete points"
`0, 1, …, N−1` in GF(2¹⁶)), the denominator `lagrangeDenomProd` is nonzero and the Fermat-style
exponentiation `(lagrangeDenomProd …) ^ (2¹⁶ − 2)` yields the multiplicative inverse, so the
scaling factor reduces to `ones[j].y / ∏_{k ≠ j} (ones[j].x − ones[k].x)`.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition (`a − b = a + b = a ⊕ b`),
so the linear factors `(X − ones[k].x)` and the differences `ones[j].x − ones[k].x` are
equivalently `(X + ones[k].x)` and `ones[j].x + ones[k].x`.

**Source**: spqr/src/encoding/polynomial.rs (lines 488:8-493:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop1

/--
**Spec theorem for `encoding.polynomial.lagrange_polys_for_complete_points_loop1`**:

The full `while i < N` Lagrange basis polynomial computation loop in
`lagrange_polys_for_complete_points`, which fills `out[j]` with the `j`-th scaled Lagrange
basis polynomial for each index `j` from `i` to `N−1`.  Given the point array `ones` of size
`N`, the output array `out` of size `N`, and the starting index `i`, the loop processes all
indices from `i` to `N−1` and returns the completed array `result` satisfying:

• The function always succeeds (no panic) provided the preconditions hold, since all array
  accesses and updates are bounded by `N`, the `Array.to_slice` and
  `lagrange_interpolate_pt` calls succeed under the given constraints, and the loop counter
  `i < N` is checked before any operation.

• **Lagrange postcondition** (every position `j ∈ [i, N)` has been filled):
    `∀ j, i.val ≤ j → j < N.val →
      listToGF216Poly (result[j].coefficients.val) =
        C (ones[j].y.toGF216 *
            (lagrangeDenomProd ones[j].x (ones.take N) 0) ^ (2¹⁶ − 2)) *
          condProdLinearFactors ones[j].x (ones.take N) 0`
  Each `result[j]` is the `j`-th term of the standard Lagrange interpolation formula
  for the points `ones[0], …, ones[N−1]`.

• **Unchanged positions** (positions `j < i` are untouched):
    `∀ j, j < i.val → result[j]? = out[j]?`

**Source**: spqr/src/encoding/polynomial.rs (lines 488:8-493:9)
-/
@[step]
theorem loop_spec
    {N : Usize}
    (ones : Array Pt N)
    (out : Array (PolyConst N) N)
    (i : Usize)
    (h_N_pos : 0 < N.val)
    (h_i_le_N : i.val ≤ N.val) :
    lagrange_polys_for_complete_points_loop1 ones out i
      ⦃ result =>
        (∀ (j : Nat), i.val ≤ j → j < N.val →
          ∀ (hj : j < result.val.length) (hjo : j < ones.val.length),
            listToGF216Poly (result.val.get ⟨j, hj⟩).coefficients.val =
              C ((ones.val.get ⟨j, hjo⟩).y.toGF216 *
                  (lagrangeDenomProd (ones.val.get ⟨j, hjo⟩).x
                    (ones.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
                condProdLinearFactors (ones.val.get ⟨j, hjo⟩).x
                  (ones.val.take N.val) 0) ∧
        (∀ (j : Nat), j < i.val →
          result.val[j]? = out.val[j]?) ⦄ := by
  sorry
/-  unfold lagrange_polys_for_complete_points_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : (Array (PolyConst N) N) × Usize) =>
                  N.val - p.2.val)
    (inv := fun (p : (Array (PolyConst N) N) × Usize) =>
        let out' := p.1
        let i' := p.2
        i.val ≤ i'.val ∧
        i'.val ≤ N.val ∧
        -- processed positions: Lagrange basis polynomials stored
        (∀ (j : Nat), i.val ≤ j → j < i'.val →
          ∀ (hj : j < out'.val.length) (hjo : j < ones.val.length),
            listToGF216Poly (out'.val.get ⟨j, hj⟩).coefficients.val =
              C ((ones.val.get ⟨j, hjo⟩).y.toGF216 *
                  (lagrangeDenomProd (ones.val.get ⟨j, hjo⟩).x
                    (ones.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
                condProdLinearFactors (ones.val.get ⟨j, hjo⟩).x
                  (ones.val.take N.val) 0) ∧
        -- non-processed positions: unchanged from input out
        (∀ (j : Nat), ¬(i.val ≤ j ∧ j < i'.val) →
          out'.val[j]? = out.val[j]?))
  · -- Body step: prove invariant is preserved and measure decreases
    rintro ⟨out', i'⟩
      ⟨h_i_le_i', h_i'_le_N, h_proc, h_rest⟩
    simp only [] at h_i_le_i' h_i'_le_N h_proc h_rest ⊢
    have h_body := body_spec ones out' i' h_N_pos
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done out_r =>
      -- Done case: loop terminates, array unchanged
      simp only [] at h_cf ⊢
      obtain ⟨h_eq, h_not_lt⟩ := h_cf
      subst h_eq
      push Not at h_not_lt
      -- i' ≥ N (from ¬(i' < N)), combined with i' ≤ N gives i' = N
      refine ⟨?_, ?_⟩
      · -- All positions i ≤ j < N were processed
        intro j hj hj_lt hj' hjo
        exact h_proc j hj (by omega) hj' hjo
      · -- Positions j < i unchanged
        intro j hj
        exact h_rest j (by intro ⟨h1, _⟩; omega)
    | ControlFlow.cont (out1, i1) =>
      -- Cont case: one more iteration processed
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_i1, h_upd, h_frame⟩ := h_cf
      constructor
      · -- Invariant preserved (4 conjuncts)
        refine ⟨by omega, by omega, ?_, ?_⟩
        · -- Processed positions extended by one
          intro j hj hj_lt_i1 hj' hjo
          by_cases hjk : j < i'.val
          · -- j was already processed: chain frame + old invariant
            have h_ne : j ≠ i'.val := by omega
            have hj_old : j < out'.val.length := by
              simp only [List.Vector.length_val]; omega
            have h_fr := h_frame j h_ne hj_old
            have h_get := list_get_of_getElem?_eq h_fr hj' hj_old
            simp only [List.get_eq_getElem] at h_get h_proc ⊢
            rw [h_get]; exact h_proc j hj hjk hj_old hjo
          · -- j = i': newly processed by body
            have hj_eq : j = i'.val := by omega
            subst hj_eq
            exact h_upd hj' hjo
        · -- Non-processed positions still unchanged
          intro j hj
          have h_ne : j ≠ i'.val := by
            intro heq; apply hj; subst heq; exact ⟨h_i_le_i', by omega⟩
          by_cases hjb : j < out'.val.length
          · rw [h_frame j h_ne hjb,
                h_rest j (by intro ⟨h1, h2⟩; exact hj ⟨h1, by omega⟩)]
          · -- j is out of bounds for all arrays (all have length N.val)
            have h_ge_out1 : out1.val.length ≤ j := by
              simp only [List.Vector.length_val] at hjb ⊢; omega
            have h_ge_out : out.val.length ≤ j := by
              simp only [List.Vector.length_val] at hjb ⊢; omega
            simp [List.getElem?_eq_none h_ge_out1, List.getElem?_eq_none h_ge_out]
      · -- Measure decreases
        omega
  · -- Initial invariant: no positions processed yet, all unchanged
    refine ⟨le_refl _, h_i_le_N, fun _ h1 h2 => absurd h2 (by grind), fun _ _ => rfl⟩
-/
end spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop1


/-!
# Spec theorem for `spqr::encoding::polynomial::lagrange_polys_for_complete_points`

The Rust function `lagrange_polys_for_complete_points` (in `src/encoding/polynomial.rs`, lines
469:0-496:1) precomputes the array of Lagrange basis polynomials for the "complete points" —
evaluation points `0, 1, …, N−1` in GF(2¹⁶) with `y`-coordinate `GF16::ONE`.

Concretely, `lagrange_polys_for_complete_points N`:
  1. Constructs an array `ones` of `N` copies of `Pt { x: GF16::ZERO, y: GF16::ONE }`.
  2. Runs loop 0 (`lagrange_polys_for_complete_points_loop0`), which iterates `i = 0, …, N−1`
     and sets `ones[i].x.value = i as u16`, producing the "complete points" array `ones1` where
     `ones1[j].x.value.val = j` and `ones1[j].y = GF16::ONE` for all `j < N`.
  3. Constructs an output array `out` of `N` copies of `PolyConst::ZEROS`.
  4. Runs loop 1 (`lagrange_polys_for_complete_points_loop1`), which iterates `i = 0, …, N−1`
     and sets `out[i] = PolyConst::<N>::lagrange_interpolate_pt(&ones1, i)`, producing the
     final result array where each slot contains the corresponding scaled Lagrange basis
     polynomial.

**Postcondition**: there exists an intermediate point array `ones1` such that:
  - **Complete points**: for each `j < N`, `ones1[j].x.value.val = j` and
    `ones1[j].y = GF16::ONE`.  Equivalently, `ones1[j].x.toGF216 = Nat.toGF216 j`.
  - **Lagrange basis polynomials**: for each `j < N`,
      `listToGF216Poly (result[j].coefficients.val) =
         C (ones1[j].y.toGF216 *
             (lagrangeDenomProd ones1[j].x (ones1.take N) 0) ^ (2¹⁶ − 2)) *
           condProdLinearFactors ones1[j].x (ones1.take N) 0`
    which is the `j`-th term of the standard Lagrange interpolation formula for the
    points `ones1[0], …, ones1[N−1]`.

When the `x`-coordinates are pairwise distinct (which they are for the "complete points"
`0, 1, …, N−1` in GF(2¹⁶) provided `N ≤ 2¹⁶`), the denominator `lagrangeDenomProd` is nonzero
and the Fermat-style exponentiation `(lagrangeDenomProd …) ^ (2¹⁶ − 2)` yields the multiplicative
inverse, so the scaling factor reduces to `ones1[j].y / ∏_{k ≠ j} (ones1[j].x − ones1[k].x)`.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition (`a − b = a + b = a ⊕ b`),
so the linear factors `(X − ones1[k].x)` and the differences `ones1[j].x − ones1[k].x` are
equivalently `(X + ones1[k].x)` and `ones1[j].x + ones1[k].x`.

**Source**: spqr/src/encoding/polynomial.rs (lines 469:0-496:1)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial

/--
**Spec theorem for `encoding.polynomial.lagrange_polys_for_complete_points`**:

• The function always succeeds (no panic) for any `N` satisfying `0 < N` and `N ≤ 65536`,
  since all intermediate operations — array construction via `Array.repeat`, loop 0 (point
  initialisation via `lagrange_polys_for_complete_points_loop0`), and loop 1 (Lagrange basis
  polynomial computation via `lagrange_polys_for_complete_points_loop1`) — are total under
  these constraints.

• There exists an intermediate point array `ones1` of size `N` such that:

  - **Complete points** (every position `j < N` has been initialised):
      `ones1[j].x.value.val = j` and `ones1[j].y = GF16.ONE`
    Equivalently, lifting the `x`-coordinate into `GF216`:
      `ones1[j].x.toGF216 = Nat.toGF216 j`.

  - **Lagrange basis polynomials** (every position `j < N` has been filled):
      `listToGF216Poly (result[j].coefficients.val) =
         C (ones1[j].y.toGF216 *
             (lagrangeDenomProd ones1[j].x (ones1.val.take N) 0) ^ (2¹⁶ − 2)) *
           condProdLinearFactors ones1[j].x (ones1.val.take N) 0`
    Each `result[j]` is the `j`-th term of the standard Lagrange interpolation formula
    for the points `ones1[0], …, ones1[N−1]`.

**Source**: spqr/src/encoding/polynomial.rs (lines 469:0-496:1)
-/
@[step]
theorem lagrange_polys_for_complete_points_spec
    (N : Usize)
    (h_N_pos : 0 < N.val)
    (h_N_bound : N.val ≤ 65536) :
    lagrange_polys_for_complete_points N
      ⦃ result =>
        ∃ (ones1 : Array Pt N),
          (∀ (j : Nat), j < N.val →
            ∀ (hj : j < ones1.val.length),
              (ones1.val.get ⟨j, hj⟩).x.value.val = j ∧
              (ones1.val.get ⟨j, hj⟩).y = GF16.ONE) ∧
          (∀ (j : Nat), j < N.val →
            ∀ (hj : j < result.val.length) (hjo : j < ones1.val.length),
              listToGF216Poly (result.val.get ⟨j, hj⟩).coefficients.val =
                C ((ones1.val.get ⟨j, hjo⟩).y.toGF216 *
                    (lagrangeDenomProd (ones1.val.get ⟨j, hjo⟩).x
                      (ones1.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
                  condProdLinearFactors (ones1.val.get ⟨j, hjo⟩).x
                    (ones1.val.take N.val) 0) ⦄ := by
  sorry
  /-
  unfold lagrange_polys_for_complete_points
  -- Pre-instantiate the loop specs with the concrete starting index (0) and preconditions
  -- discharged, following the pattern from DivImpl.lean
  have h_loop1 := fun (ones1 : Array Pt N) (out : Array (PolyConst N) N) =>
    lagrange_polys_for_complete_points_loop1.loop_spec
      ones1 out (0#usize : Usize) h_N_pos (by scalar_tac)
  step*
  -- After step*, ones1 and its properties (from loop0_spec) are in context:
  --   ones1_post1 : complete points property (with 0 ≤ j precondition from loop0)
  --   result_post1 : Lagrange polynomial property (with 0 ≤ j precondition from loop1)
  -- We witness the existential with ones1, stripping the trivial 0 ≤ j condition.
  exact ⟨ones1, fun j hj hj' => ones1_post1 j (by omega) hj hj',
         fun j hj hj' hjo => result_post1 j (by omega) hj hj' hjo⟩
-/
end spqr.encoding.polynomial
