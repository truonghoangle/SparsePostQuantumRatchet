/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyConst.LagrangeInterpolatePt
import Spqr.Specs.Encoding.Gf.GF16.New
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

The result satisfies the GF(2¹⁶)-level postcondition:

  `out1[i]` stores the `i`-th scaled Lagrange basis polynomial for the evaluation points
  `ones[0], …, ones[N−1]`, and all other entries are unchanged.

The proof unfolds `body` to expose the underlying `to_slice`, `lagrange_interpolate_pt`, and
`Array.update` calls and discharges the resulting goal with `step*`, which applies the
already-registered `lagrange_interpolate_pt_spec`.

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
      | ControlFlow.done out' => out' = out ∧ ¬ (i < N)
      | ControlFlow.cont (out1, i1) =>
          i < N ∧
          i1 = i.val + 1 ∧
          (∀ (h_idx : i < out1.length) (hi : i < ones.length),
            listToGF216Poly (out1[i].coefficients) =
              C ((ones[i]).y.toGF216 *
                  (lagrangeDenomProd (ones[i]!).x
                    (ones.val.take N.val) 0) ^ (2 ^ 16 - 2)) *
                condProdLinearFactors (ones[i]!).x
                  (ones.val.take N.val) 0) ∧
          (∀ j < out.length, (_: j ≠ i.val) →  out1[j]? = out[j]?) ⦄ := by
  unfold body
  by_cases h_lt : i.val < N.val
  · simp only [UScalar.lt_equiv, h_lt, ↓reduceIte, true_and]
    step*
    subst s_post a_post
    simp_all [Array.to_slice]
  · step*

end spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop1
