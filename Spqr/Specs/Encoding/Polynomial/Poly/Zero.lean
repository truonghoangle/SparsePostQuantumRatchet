/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Poly
/-!
# Spec Theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::zero`

Specification and proof for `spqr.encoding.polynomial.Poly.zero`, which constructs the zero
polynomial — a `Poly` whose coefficient list is empty.

A `Poly` represents a polynomial over GF(2¹⁶), where the list `coefficients` stores the coefficients
in ascending degree order:
  `coefficients = [a₀, a₁, …, aₙ]`
represents the polynomial `a₀ + a₁·x + … + aₙ·xⁿ`.  The zero polynomial is the unique polynomial
with no terms, i.e. it evaluates to `0 : GF(2¹⁶)` at every point.

Concretely, `zero capacity` calls `Vec::with_capacity(capacity)` to allocate a vector with the given
capacity hint and wraps it into a `Poly`.  The `capacity` parameter is a performance hint only — it
does not affect the mathematical content.  The resulting vector has length 0 (it is empty), so the
`Poly` represents the zero polynomial in GF(2¹⁶)[x].

The function always succeeds (no panic) for any `capacity` value, since `Vec::with_capacity` is a
total operation.

**Source**: spqr/src/encoding/polynomial.rs (lines 94:4-98:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.Poly

/-
natural language description:

• Takes a single `usize` argument `capacity`, which is a hint for
  the initial allocation size of the internal coefficient vector.
• Creates a new `Poly` by wrapping a freshly allocated empty
  `Vec<GF16>` (via `Vec::with_capacity(capacity)`) into the
  `coefficients` field.
• Returns the resulting `Poly` whose coefficient list is empty,
  representing the zero polynomial in GF(2¹⁶)[x].

natural language specs:

• The function always succeeds (no panic) for any `capacity : Usize`
  input, since `Vec::with_capacity` is a total operation on bounded
  integers.
• The resulting `Poly` mathematically represents the zero polynomial
  in GF(2¹⁶)[x]:
    `result.toGF216Poly = 0`
  i.e. the canonical bridge `Poly.toGF216Poly` maps the result to
  the additive identity `0 : GF216[X]` in the polynomial ring.
• The `capacity` parameter is purely a performance hint and does not
  influence the mathematical content of the result.
-/

/--
**Spec and proof concerning `spqr.encoding.polynomial.Poly.zero`**:

`zero capacity` constructs the zero polynomial over GF(2¹⁶) — a `Poly` whose coefficient vector is
empty (length 0).  The `capacity` parameter is a performance hint for the vector allocation and does
not affect the mathematical content.

The result satisfies the mathematical postcondition:

  `result.toGF216Poly = 0`

i.e. the canonical bridge `Poly.toGF216Poly` maps the result to the zero polynomial `0 : GF216[X]` —
the additive identity in the polynomial ring GF(2¹⁶)[x].

The proof unfolds `zero` to expose the underlying `Vec.with_capacity` call, which produces an empty
vector, then unfolds `Poly.toGF216Poly` to reduce to `listToGF216Poly []`, which simplifies to `0`
by `listToGF216Poly_empty`.

**Source**: spqr/src/encoding/polynomial.rs (lines 94:4-98:5)
-/
@[step]
theorem zero_spec (capacity : Std.Usize) :
    zero capacity ⦃ (result : spqr.encoding.polynomial.Poly) =>
      result.toGF216Poly = 0 ⦄ := by
  unfold zero
  simp [alloc.vec.Vec.with_capacity, Poly.toGF216Poly, spqr.encoding.polynomial.listToGF216Poly]

/--
**Stronger spec for `Poly.zero`**: in addition to the polynomial-level postcondition
`result.toGF216Poly = 0` provided by `zero_spec`, the underlying coefficient vector
also has length `0`.

This is what `Vec::with_capacity` actually produces, regardless of the `capacity`
hint, and is the form needed by callers (e.g. `lagrange_interpolate`, `lagrange_sum`)
that have to discharge a uniform length bound `out.coefficients.val.length ≤ M`
for the running accumulator before entering a loop.

**Source**: spqr/src/encoding/polynomial.rs (lines 94:4-98:5)
-/
theorem zero_spec' (capacity : Std.Usize) :
    zero capacity ⦃ (result : spqr.encoding.polynomial.Poly) =>
      result.coefficients.val.length = 0 ∧ result.toGF216Poly = 0 ⦄ := by
  unfold zero
  simp [alloc.vec.Vec.with_capacity, Poly.toGF216Poly,
    spqr.encoding.polynomial.listToGF216Poly]

end spqr.encoding.polynomial.Poly
