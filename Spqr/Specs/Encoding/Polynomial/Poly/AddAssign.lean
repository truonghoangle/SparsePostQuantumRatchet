/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.Poly.AddAssignLoop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::add_assign`

The Rust function `Poly::add_assign` (in `src/encoding/polynomial.rs`, lines 239:4-247:5) implements
in-place polynomial addition `self += other` in GF(2¹⁶)[X].  It iterates over the coefficients of
`other` using an `enumerate` iterator, processing one coefficient `(i, v)` at a time:

```
fn add_assign(&mut self, other: &Self) {
    for (i, v) in other.coefficients.iter().enumerate() {
        if i < self.coefficients.len() {
            self.coefficients[i] += *v;    // GF16 add-assign (XOR)
        } else {
            self.coefficients.push(*v);     // extend self
        }
    }
}
```

Concretely, `add_assign self other`:
  1. Creates a slice iterator over `other.coefficients` via `Vec::deref` + `Slice::iter`.
  2. Wraps it with `enumerate` to pair each coefficient with its index.
  3. Delegates to `encoding.polynomial.Poly.add_assign_loop`, which processes each `(i, v)` pair:
     - **In-range update** (`i < self.coefficients.len()`): replaces `self.coefficients[i]` with
       the GF(2¹⁶) sum `self.coefficients[i] + v` (which is bitwise XOR in characteristic 2).
     - **Extension** (`i ≥ self.coefficients.len()`): appends `v` to `self.coefficients` via
       `Vec::push`.

After all iterations, the result polynomial represents the sum `self + other` in
`GF216[X] = (GaloisField 2 16)[X]`.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR:
  `a + b = a − b = a ⊕ b`.

The Aeneas-extracted Lean function `encoding.polynomial.Poly.add_assign` is a direct delegation:
  1. `alloc.vec.Vec.deref other.coefficients` — obtains the coefficient slice.
  2. `core.slice.Slice.iter` — creates a slice iterator (starting at index 0).
  3. `core.slice.iter.IteratorSliceIter.enumerate` — wraps with an enumerate adapter (count 0).
  4. `encoding.polynomial.Poly.add_assign_loop iter self` — the verified loop driver.

Since the delegation introduces no additional logic beyond iterator setup, the postcondition is
inherited directly from the loop specification (`add_assign_loop.loop_spec`): the mathematical
polynomial interpretation of the result equals the sum of the interpretations of the inputs.

**Source**: spqr/src/encoding/polynomial.rs (lines 239:4-247:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly

/--
**Spec theorem for `encoding.polynomial.Poly.add_assign`**:

• The function always succeeds (no panic) provided the combined coefficient vector length is within
  `Usize.max`, since the underlying iterator creation (`Slice.iter`, `enumerate`) and the loop
  driver (`add_assign_loop`) are all total on bounded vectors.

• **Polynomial addition postcondition**:
    `result.toGF216Poly = self.toGF216Poly + other.toGF216Poly`
  where `toGF216Poly : Poly → GF216Poly` interprets the coefficient vector as a polynomial in
  `GF216[X] = (GaloisField 2 16)[X]`, and the `+` on the right-hand side is polynomial addition in
  `GF216[X]`.

  In GF(2¹⁶) (characteristic 2), polynomial addition is coefficient-wise XOR, so this is
  equivalent to `self ⊕ other` on the coefficient vectors (padded with zeros to equal length).

**Source**: spqr/src/encoding/polynomial.rs (lines 239:4-247:5)
-/
@[step]
theorem add_assign_spec
    (self other : Poly)
    (h_len : self.coefficients.val.length + other.coefficients.val.length ≤ Usize.max) :
    add_assign self other ⦃ (result : Poly) =>
      result.toGF216Poly = self.toGF216Poly + other.toGF216Poly ⦄ := by
  unfold add_assign
  simp only [alloc.vec.Vec.deref, core.slice.Slice.iter,
             core.slice.iter.IteratorSliceIter.enumerate, bind_tc_ok]
  apply WP.spec_mono (add_assign_loop.loop_spec _ self other.coefficients.val
    (by simp) (by simp) rfl h_len)
  intro result h
  exact h

end spqr.encoding.polynomial.Poly
