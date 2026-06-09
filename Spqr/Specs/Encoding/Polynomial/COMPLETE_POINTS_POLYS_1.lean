/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.LagrangePolysForCompletePoints

/-!
# Spec theorem for `spqr::encoding::polynomial::COMPLETE_POINTS_POLYS_1`

The Rust constant `COMPLETE_POINTS_POLYS_1` (in `src/encoding/polynomial.rs`, line 500) is defined
as

```
const COMPLETE_POINTS_POLYS_1: [PolyConst<1>; 1] = lagrange_polys_for_complete_points::<1>();
```

It precomputes the 1-element array of Lagrange basis polynomials for the "complete points" —
evaluation point `0` in GF(2¹⁶) with `y`-coordinate `GF16::ONE`.  The extracted Lean
definition `encoding.polynomial.COMPLETE_POINTS_POLYS_1` is simply a specialisation of the generic
`lagrange_polys_for_complete_points` to `N = 1`:

```
encoding.polynomial.lagrange_polys_for_complete_points 1#usize
```

The postcondition is therefore inherited directly from `lagrange_polys_for_complete_points_spec`:
there exists an intermediate point array `ones1` of size 1 such that:

  - **Complete points**: for `j < 1` (i.e. `j = 0`), `ones1[j].x.value.val = j` and
    `ones1[j].y = GF16::ONE`.  Equivalently, `ones1[j].x.toGF216 = Nat.toGF216 j`.

  - **Lagrange basis polynomials**: for `j < 1` (i.e. `j = 0`),
      `listToGF216Poly (result[j].coefficients.val) =
         C (ones1[j].y.toGF216 *
             (lagrangeDenomProd ones1[j].x (ones1.take 1) 0) ^ (2¹⁶ − 2)) *
           condProdLinearFactors ones1[j].x (ones1.take 1) 0`
    which is the `j`-th term of the standard Lagrange interpolation formula for the
    point `ones1[0]`.

When there is only a single evaluation point (`N = 1`), the Lagrange basis polynomial is
trivially the constant polynomial `ones1[0].y` (since there are no other points to form
denominator or linear factor products over), and `condProdLinearFactors` with a single point
reduces to `1`.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition (`a − b = a + b = a ⊕ b`),
so the linear factors `(X − ones1[k].x)` and the differences `ones1[j].x − ones1[k].x` are
equivalently `(X + ones1[k].x)` and `ones1[j].x + ones1[k].x`.

**Source**: spqr/src/encoding/polynomial.rs (line 500)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial

/--
**Spec theorem for `encoding.polynomial.COMPLETE_POINTS_POLYS_1`**:

• The constant always evaluates successfully (no panic), since it is a specialisation of
  `lagrange_polys_for_complete_points` at `N = 1`, which succeeds for any `N` satisfying
  `0 < N` and `N ≤ 65536`.

• There exists an intermediate point array `ones1` of size 1 such that:

  - **Complete points** (every position `j < 1` has been initialised):
      `ones1[j].x.value.val = j` and `ones1[j].y = GF16.ONE`
    Equivalently, lifting the `x`-coordinate into `GF216`:
      `ones1[j].x.toGF216 = Nat.toGF216 j`.

  - **Lagrange basis polynomials** (every position `j < 1` has been filled):
      `listToGF216Poly (result[j].coefficients.val) =
         C (ones1[j].y.toGF216 *
             (lagrangeDenomProd ones1[j].x (ones1.val.take 1) 0) ^ (2¹⁶ − 2)) *
           condProdLinearFactors ones1[j].x (ones1.val.take 1) 0`
    Each `result[j]` is the `j`-th term of the standard Lagrange interpolation formula
    for the point `ones1[0]`.

**Source**: spqr/src/encoding/polynomial.rs (line 500)
-/
@[step]
theorem COMPLETE_POINTS_POLYS_1_spec :
    COMPLETE_POINTS_POLYS_1
      ⦃ result =>
        ∃ (ones1 : Array Pt 1#usize),
          (∀ (j : Nat), j < (1#usize).val →
            ∀ (hj : j < ones1.val.length),
              (ones1.val.get ⟨j, hj⟩).x.value.val = j ∧
              (ones1.val.get ⟨j, hj⟩).y = GF16.ONE) ∧
          (∀ (j : Nat), j < (1#usize).val →
            ∀ (hj : j < result.val.length) (hjo : j < ones1.val.length),
              listToGF216Poly (result.val.get ⟨j, hj⟩).coefficients.val =
                C ((ones1.val.get ⟨j, hjo⟩).y.toGF216 *
                    (lagrangeDenomProd (ones1.val.get ⟨j, hjo⟩).x
                      (ones1.val.take (1#usize).val) 0) ^ (2 ^ 16 - 2)) *
                  condProdLinearFactors (ones1.val.get ⟨j, hjo⟩).x
                    (ones1.val.take (1#usize).val) 0) ⦄ := by
  unfold COMPLETE_POINTS_POLYS_1
  step*
  exact ⟨result, fun j hj hj' => result_post1 j hj hj',
         fun j hj hj' hjo => result_post2 j hj hj' hjo⟩

end spqr.encoding.polynomial
