/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly

/-!
# Spec theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyConst<N>}::to_poly`

The Rust function `PolyConst::to_poly` (in `src/encoding/polynomial.rs`, lines 456:4-461:5)
converts a fixed-size polynomial `PolyConst<N>` — stored as an array of `N` coefficients of type
`GF16` — into the heap-allocated `Poly` representation (backed by `Vec<GF16>`).  The conversion is a
simple coefficient copy:

```
fn to_poly(&self) -> Poly {
    Poly {
        coefficients: self.coefficients.to_vec(),
    }
}
```

The Aeneas-extracted Lean function `encoding.polynomial.PolyConst.to_poly` performs:

  1. `Array.to_slice self.coefficients` — obtains a slice `s` referencing the fixed-size coefficient
     array.  Since `to_slice` on an `Array T N` always succeeds and produces a `Slice T` with
     `s.val = self.coefficients.val`, this step is total.
  2. `alloc.slice.Slice.to_vec GF16.Clone s` — clones the slice into a fresh `Vec GF16`.  The
     `to_vec` operation on a `Slice T` with a `Clone` instance always succeeds and yields a
     `Vec T` with `v.val = s.val`.
  3. Wraps the result as `{ coefficients := v } : Poly`.

The net effect is purely structural: the underlying coefficient list is preserved verbatim.
Consequently, the `GF216[X]` polynomial interpretation through `listToGF216Poly` is identical
for the input `PolyConst N` and the output `Poly`:

  `listToGF216Poly result.coefficients.val = listToGF216Poly self.coefficients.val`

or equivalently, using the canonical bridge `Poly.toGF216Poly`:

  `result.toGF216Poly = listToGF216Poly self.coefficients.val`

This is the identity lemma that allows downstream proofs (e.g., for `const_polys_to_polys` and
`lagrange_polys_for_complete_points`) to seamlessly transfer polynomial-level properties from
`PolyConst N` specifications to `Poly` specifications.

**Source**: spqr/src/encoding/polynomial.rs (lines 456:4-461:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyConst

/--
**Spec theorem for `encoding.polynomial.PolyConst.to_poly`**:

• The function always succeeds (no panic) for any `PolyConst N` input, since `Array.to_slice`
  is total on `Array T N` and `Slice.to_vec` with the `GF16` `Clone` instance is total on
  `Slice GF16`.

• **Coefficient preservation**: the underlying coefficient list is copied verbatim:
    `result.coefficients.val = self.coefficients.val`
  This is the strongest postcondition — it implies all polynomial-level identities.

• **Polynomial identity in `GF216[X]`**: lifting through `listToGF216Poly` preserves the
  polynomial interpretation:
    `result.toGF216Poly = listToGF216Poly self.coefficients.val`
  where `Poly.toGF216Poly p = listToGF216Poly p.coefficients.val` is the canonical bridge
  from the Aeneas-extracted `Poly` type to the mathematical polynomial ring
  `GF216[X] = (GaloisField 2 16)[X]`.

  This follows immediately from coefficient preservation, and is the key identity used
  by downstream specifications to transfer `PolyConst`-level Lagrange interpolation results
  to the `Poly` type.

**Source**: spqr/src/encoding/polynomial.rs (lines 456:4-461:5)
-/
@[step]
theorem to_poly_spec
    {N : Usize}
    (self : PolyConst N) :
    to_poly self ⦃ (result : Poly) =>
      result.coefficients.val = self.coefficients.val ∧
      result.toGF216Poly = listToGF216Poly self.coefficients.val ⦄ := by
  unfold to_poly
  step*
  · intro x _
    simp [encoding.gf.GF16.Insts.CoreCloneClone.clone]
  · simp_all [Poly.toGF216Poly]

end spqr.encoding.polynomial.PolyConst
