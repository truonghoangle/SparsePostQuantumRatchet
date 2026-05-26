/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.CallMut

/-!
# Spec theorem for `spqr::encoding::polynomial::const_polys_to_polys::{FnOnce}::call_once`

The Rust function `const_polys_to_polys` (in `src/encoding/polynomial.rs`, lines 465:0-467:1)
converts a fixed-size array `[PolyConst<N>; N]` of constant polynomials into a heap-allocated
`Vec<Poly>` by mapping each element through `PolyConst::to_poly`:

```
fn const_polys_to_polys<const N: usize>(cps: &[PolyConst<N>; N]) -> Vec<Poly> {
    cps.iter().map(|x| x.to_poly()).collect::<Vec<_>>()
}
```

The closure `|x| x.to_poly()` (at line 466:19-466:34) is extracted by Aeneas as both a `FnMut`
and a `FnOnce` trait implementation.  The `FnOnce` variant
`encoding.polynomial.const_polys_to_polys.closure.Insts.
CoreOpsFunctionFnOnceTupleSharedPolyConstPoly`
whose `call_once` method takes:
  - a closure state `c : const_polys_to_polys.closure N` (which is simply `Unit`, since the closure
    captures no environment),
  - a `PolyConst N` argument (the current element from the iterator),

and returns `Poly` — the converted polynomial (without the closure state, unlike `call_mut`).

Concretely, the extracted `call_once` delegates to `call_mut`:
  1. Calls `call_mut c pc` to obtain `(p, _)` — the converted `Poly` paired with the (discarded)
     closure state.
  2. Returns `p` — just the resulting `Poly`.

Since `call_once` introduces no additional logic beyond the delegation to `call_mut`, its
postcondition is inherited directly from `call_mut_spec` (minus the closure state preservation):

  - **Coefficient preservation**: `result.coefficients.val = pc.coefficients.val`
  - **Polynomial identity in `GF216[X]`**:
      `result.toGF216Poly = listToGF216Poly pc.coefficients.val`

This is the per-element mapping step used by `const_polys_to_polys` when the closure is consumed
(via `FnOnce`) rather than borrowed (via `FnMut`).

**Source**: spqr/src/encoding/polynomial.rs (lines 466:19-466:34)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.const_polys_to_polys.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPolyConstPoly

/--
**Spec theorem for `encoding.polynomial.const_polys_to_polys.closure.Insts.
CoreOpsFunctionFnOnceTupleSharedPolyConstPoly.call_once`**:

The closure `|x| x.to_poly()` inside `const_polys_to_polys`, extracted as `call_once`.
Takes a closure state `c` (which is `Unit`, since the closure captures nothing) and a
`PolyConst N` argument, and returns the converted `Poly` where:

• The function always succeeds (no panic) for any `PolyConst N` input, since the underlying
  `call_mut` (and hence `PolyConst.to_poly`) is total (it merely copies the coefficient array
  into a `Vec`).

• **Coefficient preservation**: the underlying coefficient list is copied verbatim:
    `result.coefficients.val = pc.coefficients.val`

• **Polynomial identity in `GF216[X]`**: lifting through `listToGF216Poly` preserves the
  polynomial interpretation:
    `result.toGF216Poly = listToGF216Poly pc.coefficients.val`
  where `Poly.toGF216Poly p = listToGF216Poly p.coefficients.val` is the canonical bridge
  from the Aeneas-extracted `Poly` type to the mathematical polynomial ring
  `GF216[X] = (GaloisField 2 16)[X]`.

**Source**: spqr/src/encoding/polynomial.rs (lines 466:19-466:34)
-/
@[step]
theorem call_once_spec
    {N : Usize}
    (c : const_polys_to_polys.closure N)
    (pc : PolyConst N) :
    call_once c pc ⦃ (result : Poly) =>
      result.coefficients.val = pc.coefficients.val ∧
      result.toGF216Poly = listToGF216Poly pc.coefficients.val ⦄ := by
  unfold call_once
  step*

end spqr.encoding.polynomial.const_polys_to_polys.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPolyConstPoly
