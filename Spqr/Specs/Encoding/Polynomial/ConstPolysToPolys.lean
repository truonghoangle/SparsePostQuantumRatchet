/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.Basic.Defs
import Spqr.Math.Poly.Basic.Zero
import Spqr.Math.Poly.Coeff.Basic
import Spqr.Math.Poly.Coeff.ListOps
import Spqr.Math.Poly.CharTwo.Basic
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Math.Poly.Eval
import Spqr.Math.Poly.LinearFactors.Basic
import Spqr.Math.Poly.LinearFactors.Degree
import Spqr.Math.Poly.Lagrange.DenomProd
import Spqr.Math.Poly.Lagrange.BasisPoly
import Spqr.Math.Poly.Lagrange.InterpolantSum
import Spqr.Math.Poly.Horner.Defs
import Spqr.Math.Poly.Horner.Eval
import Spqr.Math.Poly.ExpectedTrailing.Defs
import Spqr.Math.Poly.ExpectedTrailing.Basic
import Spqr.Math.Poly.Identities.Basic
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.CallMut
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.CallOne
import Spqr.Specs.Aeneas.SliceIter
import Spqr.Specs.Aeneas.SliceIterMap
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.SliceIterMapCollect

/-!
# Spec theorem for `spqr::encoding::polynomial::const_polys_to_polys`

The Rust function `const_polys_to_polys` (in `src/encoding/polynomial.rs`,
lines 465:0-467:1) converts a fixed-size array `[PolyConst<N>; N]` of constant
polynomials into a heap-allocated `Vec<Poly>` by mapping each element through
`PolyConst::to_poly`:

```
fn const_polys_to_polys<const N: usize>(
    cps: &[PolyConst<N>; N],
) -> Vec<Poly> {
    cps.iter().map(|x| x.to_poly()).collect::<Vec<_>>()
}
```

The Aeneas-extracted Lean function `encoding.polynomial.const_polys_to_polys`
performs:

  1. `Array.to_slice cps` — obtains a slice referencing the fixed-size input
     array.
  2. `core.slice.Slice.iter s` — creates a slice iterator over the elements.
  3. `Iter.map (FnMut closure) i ()` — wraps the iterator with the closure
     `|x| x.to_poly()`, producing a `Map` adapter.
  4. `Map.collect (FromIteratorVec Poly) m` — drives the `Map` iterator to
     completion, collecting each `Poly` into a fresh `Vec<Poly>`.

The net effect is a pure element-wise map: for each index `j ∈ [0, N)`, the
`j`-th output element is obtained by calling `PolyConst.to_poly` on the `j`-th
input element.  Since `to_poly` is a coefficient copy (as specified in
`Spqr.Specs.Encoding.Polynomial.PolyConstN.ToPoly`), the coefficients are
preserved verbatim and the `GF216[X]` polynomial interpretation is identical.

This function is the bridge used in `from_complete_points` to convert the
precomputed `COMPLETE_POINTS_POLYS_N` arrays (of type `Array (PolyConst N) N`)
into the `Vec<Poly>` representation expected by `Poly.lagrange_sum`.

**Postcondition**:
  - **Length preservation**: `result.val.length = N.val`
  - **Coefficient preservation**: for each `j < N`,
      `result[j].coefficients.val = cps[j].coefficients.val`
  - **Polynomial identity in `GF216[X]`**: for each `j < N`,
      `result[j].toGF216Poly =
         listToGF216Poly cps[j].coefficients.val`

**Source**: spqr/src/encoding/polynomial.rs (lines 465:0-467:1)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial

/--
**Spec theorem for `encoding.polynomial.const_polys_to_polys`**:

• The function always succeeds (no panic) for any `Array (PolyConst N) N`
  input, since:
    1. `Array.to_slice` is total on `Array T N`.
    2. `Slice.iter` is total on `Slice T`.
    3. The `map` adapter with the `|x| x.to_poly()` closure (which is total
       by `call_mut_spec`) is total.
    4. `collect` into `Vec<Poly>` is total for a finite iterator.

• **Length preservation**: the output vector has the same length as the input
  array:
    `result.val.length = N.val`

• **Coefficient preservation**: for each index `j < N`, the underlying
  coefficient list is copied verbatim from the corresponding input element:
    `result[j].coefficients.val = cps[j].coefficients.val`

• **Polynomial identity in `GF216[X]`**: for each index `j < N`, lifting
  through `listToGF216Poly` preserves the polynomial interpretation:
    `result[j].toGF216Poly =
       listToGF216Poly cps[j].coefficients.val`
  where `Poly.toGF216Poly p = listToGF216Poly p.coefficients.val` is the
  canonical bridge from the Aeneas-extracted `Poly` type to the mathematical
  polynomial ring `GF216[X] = (GaloisField 2 16)[X]`.

**Source**: spqr/src/encoding/polynomial.rs (lines 465:0-467:1)
-/
@[step]
theorem const_polys_to_polys_spec
    {N : Usize}
    (cps : Array (PolyConst N) N) :
    const_polys_to_polys cps ⦃ result =>
      result.val.length = N.val ∧
      (∀ (j : Nat), j < N.val →
        ∀ (hj : j < result.val.length)
          (hjc : j < cps.val.length),
          (result.val.get ⟨j, hj⟩).coefficients.val =
            (cps.val.get ⟨j, hjc⟩).coefficients.val ∧
          (result.val.get ⟨j, hj⟩).toGF216Poly =
            listToGF216Poly
              (cps.val.get ⟨j, hjc⟩).coefficients.val)
      ⦄ := by
  unfold const_polys_to_polys
  step*
  simp_all

end spqr.encoding.polynomial
