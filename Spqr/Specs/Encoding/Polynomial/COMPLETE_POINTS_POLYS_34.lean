/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.LagrangePolysForCompletePoints

/-!
# Spec theorem for `spqr::encoding::polynomial::COMPLETE_POINTS_POLYS_34`

The Rust constant `COMPLETE_POINTS_POLYS_34` (in `src/encoding/polynomial.rs`, line 504) is defined
as

```
const COMPLETE_POINTS_POLYS_34: [PolyConst<34>; 34] = lagrange_polys_for_complete_points::<34>();
```

It precomputes the 34-element array of Lagrange basis polynomials for the "complete points" —
evaluation points `0, 1, …, 33` in GF(2¹⁶) with `y`-coordinate `GF16::ONE`.  The extracted Lean
definition `encoding.polynomial.COMPLETE_POINTS_POLYS_34` is simply a specialisation of the generic
`lagrange_polys_for_complete_points` to `N = 34`:

```
encoding.polynomial.lagrange_polys_for_complete_points 34#usize
```

The postcondition is therefore inherited directly from `lagrange_polys_for_complete_points_spec`:
there exists an intermediate point array `ones1` of size 34 such that:

  - **Complete points**: for each `j < 34`, `ones1[j].x.value.val = j` and
    `ones1[j].y = GF16::ONE`.  Equivalently, `ones1[j].x.toGF216 = Nat.toGF216 j`.

  - **Lagrange basis polynomials**: for each `j < 34`,
      `listToGF216Poly (result[j].coefficients.val) =
         C (ones1[j].y.toGF216 *
             (lagrangeDenomProd ones1[j].x (ones1.take 34) 0) ^ (2¹⁶ − 2)) *
           condProdLinearFactors ones1[j].x (ones1.take 34) 0`
    which is the `j`-th term of the standard Lagrange interpolation formula for the
    points `ones1[0], …, ones1[33]`.

When the `x`-coordinates are pairwise distinct (which they are for the "complete points"
`0, 1, …, 33` in GF(2¹⁶)), the denominator `lagrangeDenomProd` is nonzero and the Fermat-style
exponentiation `(lagrangeDenomProd …) ^ (2¹⁶ − 2)` yields the multiplicative inverse, so the
scaling factor reduces to `ones1[j].y / ∏_{k ≠ j} (ones1[j].x − ones1[k].x)`.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition (`a − b = a + b = a ⊕ b`),
so the linear factors `(X − ones1[k].x)` and the differences `ones1[j].x − ones1[k].x` are
equivalently `(X + ones1[k].x)` and `ones1[j].x + ones1[k].x`.

**Source**: spqr/src/encoding/polynomial.rs (line 504)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial

/--
**Spec theorem for `encoding.polynomial.COMPLETE_POINTS_POLYS_34`**:

• The constant always evaluates successfully (no panic), since it is a specialisation of
  `lagrange_polys_for_complete_points` at `N = 34`, which succeeds for any `N` satisfying
  `0 < N` and `N ≤ 65536`.

• There exists an intermediate point array `ones1` of size 34 such that:

  - **Complete points** (every position `j < 34` has been initialised):
      `ones1[j].x.value.val = j` and `ones1[j].y = GF16.ONE`
    Equivalently, lifting the `x`-coordinate into `GF216`:
      `ones1[j].x.toGF216 = Nat.toGF216 j`.

  - **Lagrange basis polynomials** (every position `j < 34` has been filled):
      `listToGF216Poly (result[j].coefficients.val) =
         C (ones1[j].y.toGF216 *
             (lagrangeDenomProd ones1[j].x (ones1.val.take 34) 0) ^ (2¹⁶ − 2)) *
           condProdLinearFactors ones1[j].x (ones1.val.take 34) 0`
    Each `result[j]` is the `j`-th term of the standard Lagrange interpolation formula
    for the points `ones1[0], …, ones1[33]`.

**Source**: spqr/src/encoding/polynomial.rs (line 504)
-/
@[step]
theorem COMPLETE_POINTS_POLYS_34_spec :
    COMPLETE_POINTS_POLYS_34
      ⦃ result =>
      ∃ (ones1 : Array Pt 34#usize),
        (∀ (j : Nat), j < (34#usize).val →
          (ones1[j]!).x.value.val = j ∧
          (ones1[j]!).y = GF16.ONE) ∧
        (∀ (j : Nat), j < (34#usize).val →
          ∀ (hj : j < result.length) (hjo : j < ones1.length),
            listToGF216Poly (result.val[j]).coefficients.val =
              C ((ones1.val[j]!).y.toGF216 *
                  (lagrangeDenomProd (ones1[j]!).x
                    (ones1.val.take (34#usize).val) 0) ^ (2 ^ 16 - 2)) *
                condProdLinearFactors (ones1[j]!).x
                  (ones1.val.take (34#usize).val) 0) ⦄ := by
  unfold COMPLETE_POINTS_POLYS_34
  step*
  exact ⟨result, fun j hj => result_post1 j hj,
         fun j hj hj' hjo => result_post2 j hj hj' hjo⟩

end spqr.encoding.polynomial
