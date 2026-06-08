/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
import Spqr.Specs.Encoding.Polynomial.PolyConstN.ToPoly

/-!
# Spec theorem for `spqr::encoding::polynomial::const_polys_to_polys::{FnMut}::call_mut`

The Rust function `const_polys_to_polys` (in `src/encoding/polynomial.rs`, lines 465:0-467:1)
converts a fixed-size array `[PolyConst<N>; N]` of constant polynomials into a heap-allocated
`Vec<Poly>` by mapping each element through `PolyConst::to_poly`:

```
fn const_polys_to_polys<const N: usize>(cps: &[PolyConst<N>; N]) -> Vec<Poly> {
    cps.iter().map(|x| x.to_poly()).collect::<Vec<_>>()
}
```

The closure `|x| x.to_poly()` (at line 466:19-466:34) is extracted by Aeneas as the `FnMut` trait
implementation
`encoding.polynomial.const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly`
whose `call_mut` method takes:
  - a closure state `c : const_polys_to_polys.closure N` (which is simply `Unit`, since the closure
    captures no environment),
  - a `PolyConst N` argument (the current element from the iterator),

and returns `(Poly, closure N)` — the converted polynomial paired with the unchanged closure state.

Concretely, the extracted `call_mut` performs a single step:
  1. Calls `encoding.polynomial.PolyConst.to_poly tupled_args` to convert the fixed-size
     `PolyConst N` into the heap-allocated `Poly` representation.
  2. Returns `(p, c)` — the resulting `Poly` paired with the unchanged closure.

Since `PolyConst.to_poly` is a pure coefficient copy (as specified in
`Spqr.Specs.Encoding.Polynomial.PolyConstN.ToPoly`), the `call_mut` closure introduces no
additional logic beyond the delegation.  Its postcondition is therefore inherited directly from
`to_poly_spec`:

  - **Coefficient preservation**: `result.coefficients.val = tupled_args.coefficients.val`
  - **Polynomial identity in `GF216[X]`**:
      `result.toGF216Poly = listToGF216Poly tupled_args.coefficients.val`
  - **Closure unchanged**: `c' = c`

This is the per-element mapping step used by `const_polys_to_polys` to transform each `PolyConst N`
in the input array into a `Poly` in the output `Vec<Poly>`.

**Source**: spqr/src/encoding/polynomial.rs (lines 466:19-466:34)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly

/--
**Spec theorem for `encoding.polynomial.const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut`**:

The closure `|x| x.to_poly()` inside `const_polys_to_polys`, extracted as `call_mut`.  Takes a
closure state `c` (which is `Unit`, since the closure captures nothing) and a `PolyConst N`
argument, and returns the pair `(result, c')` where:

• The function always succeeds (no panic) for any `PolyConst N` input, since the underlying
  `PolyConst.to_poly` is total (it merely copies the coefficient array into a `Vec`).

• **Coefficient preservation**: the underlying coefficient list is copied verbatim:
    `result.coefficients.val = tupled_args.coefficients.val`

• **Polynomial identity in `GF216[X]`**: lifting through `listToGF216Poly` preserves the
  polynomial interpretation:
    `result.toGF216Poly = listToGF216Poly tupled_args.coefficients.val`
  where `Poly.toGF216Poly p = listToGF216Poly p.coefficients.val` is the canonical bridge
  from the Aeneas-extracted `Poly` type to the mathematical polynomial ring
  `GF216[X] = (GaloisField 2 16)[X]`.

• **Closure unchanged**: the closure state is returned as-is:
    `c' = c`

**Source**: spqr/src/encoding/polynomial.rs (lines 466:19-466:34)
-/
@[step]
theorem call_mut_spec
    {N : Usize}
    (c : const_polys_to_polys.closure N)
    (tupled_args : PolyConst N) :
    call_mut c tupled_args ⦃ (result : Poly × const_polys_to_polys.closure N) =>
      result.1.coefficients.val = tupled_args.coefficients.val ∧
      result.1.toGF216Poly = listToGF216Poly tupled_args.coefficients.val ∧
      result.2 = c ⦄ := by
  unfold call_mut
  step*

end spqr.encoding.polynomial.const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly
