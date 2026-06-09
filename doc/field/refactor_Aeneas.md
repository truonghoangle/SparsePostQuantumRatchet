# Refactoring proposal for `Spqr/Math/Poly/Aeneas.lean`

## Motivation

`Spqr/Math/Poly/Aeneas.lean` is currently **347 lines** and mixes several
distinct topics under a single file:

* **Polynomial identity from loop 1** (`poly_identity_from_loop1`) — a
  100-line theorem connecting the Horner-scheme loop in
  `lagrange_interpolate_complete` to a polynomial factorisation identity.
* **Polynomial identity for `mult_xdiff_assign_trailing`**
  (`mult_xdiff_poly_identity`) — a 40-line theorem giving the
  closed-form for the in-place recurrence `v[i−1] −= v[i] * d`.
* **Power-vector invariant** (`div2_add_sum_eq`,
  `power_invariant_step`, `initial_power_invariant`) — arithmetic and
  inductive lemmas about maintaining `xs[j].toGF216 = x.toGF216 ^ j`.
* **Dot-product to evaluation bridge** (`dot_product_eq_eval`,
  `zero_toGF216_eq_empty_sum`) — connecting finite sums to
  `Polynomial.eval`.
* **Usize bound** (`max_two_succ_le_usize_max`) — a small arithmetic
  fact about `Nat.max 2 n`.

Keeping these in one file makes navigation harder, slows incremental
elaboration, and creates an overly wide import footprint (Aeneas.lean
imports *every* Poly sub-module). Following the pattern established by
the prior refactor of `Spqr/Math/Poly.lean` (see `doc/fields/refactor_poly.md`)
and the style reference `Spqr/Math/Gf2Poly/Basic.lean`, we propose
splitting `Aeneas.lean` into a directory of focused sub-files of
~200 lines each, each importing only what it actually needs.

The user-facing module `Spqr.Math.Poly.Aeneas` is preserved as a thin
re-export shim so that no downstream `import` has to change.

### Downstream consumers (unchanged)

The three files that currently import `Spqr.Math.Poly.Aeneas`:

| File | Theorems used |
|------|---------------|
| `Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolateComplete.lean` | `poly_identity_from_loop1` |
| `Spqr/Specs/Encoding/Polynomial/Poly/MultXdiffAssignTrailing.lean` | `mult_xdiff_poly_identity` |
| `Spqr/Specs/Encoding/Polynomial/Poly/ComputeAt.lean` | `dot_product_eq_eval`, `zero_toGF216_eq_empty_sum`, `power_invariant_step`, `initial_power_invariant`, `max_two_succ_le_usize_max` |

Because the re-export shim keeps the import path `Spqr.Math.Poly.Aeneas`
intact, **none of these files need editing**.

---

## Conventions: aligning with `Spqr/Math/Gf2Poly/Basic.lean`

Every new file follows the same formatting and namespace rules already
documented in `doc/fields/refactor_poly.md` §§1–12. The key points
are repeated here for self-containedness.

### 1. File header

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
```

### 2. Imports

Immediately after the header, no blank line between them and the
header. Only import what the file actually uses — in particular, the
new sub-files should import *specific* Poly sub-modules (e.g.
`Spqr.Math.Poly.Horner.Defs`) rather than the monolithic umbrella.

### 3. Module docstring

After the imports, every file gets a module docstring with the
`Gf2Poly/Basic.lean` shape:

```lean
/-!
# <Title>

<One-paragraph description.>

## Main statements

* `<theorem₁>` — …
-/
```

### 4. `open` directives

A narrow `open Polynomial` (as in `Gf2Poly/Basic.lean` line 52),
plus the project-specific opens only where needed:

```lean
open Aeneas Aeneas.Std Result Polynomial
open spqr.math.gf spqr.encoding.gf spqr.encoding.polynomial
```

### 5. Namespace

All declarations live inside `namespace spqr.encoding.polynomial`,
matching the current file. No extra sub-namespaces are introduced.

### 6. Declaration-level naming

Following Mathlib conventions and the existing project style:

* `theorem` for headline results listed in `## Main statements`.
* `lemma` for supporting facts.
* `snake_case` for propositions, `lowerCamelCase` for definitions.
* `@[simp]` only for lemmas whose RHS is a normal form.

### 7. Docstrings

Plain sentences without `**bold**` headers, mirroring
`Gf2Poly/Basic.lean`'s style. The current `Aeneas.lean` uses bold
headers like `**Mathematical polynomial identity…**`; these will be
unwrapped to plain prose.

### 8. Section headers

Use `/-! ## Section title -/` as in `Gf2Poly/Basic.lean`.

---

## Proposed file layout

Following Mathlib's directory hierarchy, where topic-related `.lean`
files live in folders named after the concept (e.g.
`Mathlib/Algebra/Polynomial/{Basic,Coeff,Eval,…}.lean`), and matching
the project's existing structure in `Spqr/Math/Poly/{Basic/,Coeff/,
CharTwo/,Horner/,Lagrange/,…}`, we create a new **sub-folder**
`Spqr/Math/Poly/Aeneas/` to hold the split files.

```
Spqr/Math/Poly/Aeneas.lean               (re-export shim, replaces current monolith)
Spqr/Math/Poly/Aeneas/
│
├── PolyIdentity.lean                     (~120 lines: poly_identity_from_loop1)
│
├── MultXdiff.lean                        (~70  lines: mult_xdiff_poly_identity)
│
├── PowerVector.lean                      (~90  lines: div2_add_sum_eq,
│                                          power_invariant_step,
│                                          initial_power_invariant)
│
└── DotProduct.lean                       (~70  lines: dot_product_eq_eval,
                                           zero_toGF216_eq_empty_sum,
                                           max_two_succ_le_usize_max)
```

### Why a folder, not flat files?

| Reason | Detail |
|--------|--------|
| **Topic locality** | All Aeneas-bridge results live one `cd` away under `Aeneas/`. |
| **Future extension** | New bridge theorems (e.g. for `lagrange_interpolate_prepare`) slot into `Aeneas/` without inflating the flat directory. |
| **Smaller files** | Each `.lean` is in the ~70–120 line range, well below 200 lines. |
| **Matches project style** | `Spqr/Math/Poly/{Basic/,Coeff/,CharTwo/,Horner/,Lagrange/,…}` already use the "folder plus topic-named files" pattern. |

### Mathlib analogues

| Mathlib pattern | Our analogue |
|-----------------|--------------|
| `Mathlib/Algebra/Polynomial/Coeff.lean` (single-topic leaf) | `Spqr/Math/Poly/Aeneas/MultXdiff.lean` |
| `Mathlib/Algebra/Polynomial/Eval.lean` | `Spqr/Math/Poly/Aeneas/DotProduct.lean` |
| `Mathlib/LinearAlgebra/Lagrange.lean` (larger topic) | `Spqr/Math/Poly/Aeneas/PolyIdentity.lean` |
| `Mathlib/Algebra/Polynomial/Basic.lean` (umbrella re-export) | `Spqr/Math/Poly/Aeneas.lean` (shim) |

### Acyclic dependency DAG

```
                Poly sub-modules
        (Basic, Coeff, CharTwo, Eval,
         Horner, Lagrange, LinearFactors,
         ExpectedTrailing, Identities,
         General, Mathlib)
                    │
        ┌───────────┼───────────┐
        ▼           ▼           ▼
  PolyIdentity  MultXdiff  PowerVector
                                │
                                ▼
                          DotProduct
```

Within the folder the files are mostly independent. `DotProduct.lean`
depends on `PowerVector.lean` only conceptually (both deal with the
power-vector structure used in `ComputeAt`), but the actual Lean
imports are to the upstream Poly sub-modules, not to each other.

---

## File-by-file content

### 1. `Spqr/Math/Poly/Aeneas.lean` — re-export shim (~25 lines)

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Aeneas.PolyIdentity
import Spqr.Math.Poly.Aeneas.MultXdiff
import Spqr.Math.Poly.Aeneas.PowerVector
import Spqr.Math.Poly.Aeneas.DotProduct

/-!
# Aeneas-related polynomial bridge results — umbrella module

This module is a thin re-export of the sub-files under
`Spqr/Math/Poly/Aeneas/`. It exists so that downstream files can keep
writing `import Spqr.Math.Poly.Aeneas` after the refactor.

Each topic lives in a dedicated file; see the individual files for
their `## Main statements`.
-/
```

### 2. `Spqr/Math/Poly/Aeneas/PolyIdentity.lean` (~120 lines)

**Content:** `poly_identity_from_loop1` (lines 57–178 of current file).

**Imports:** Only the sub-modules actually referenced in the proof:

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Basic.Defs
import Spqr.Math.Poly.Coeff.Basic
import Spqr.Math.Poly.CharTwo.Basic
import Spqr.Math.Poly.Horner.Defs
import Spqr.Math.Poly.Horner.Eval

/-!
# Polynomial identity from loop 1 (lagrange_interpolate_complete)

The polynomial identity `listToGF216Poly v * (X - C g) = X * C s *
listToGF216Poly coeffs` arising from the Horner-scheme loop in
`lagrange_interpolate_complete`.

## Main statements

* `poly_identity_from_loop1` — the Horner-scheme division + scaling identity.
-/

open Aeneas Aeneas.Std Result Polynomial
open spqr.math.gf spqr.encoding.gf spqr.encoding.polynomial

namespace spqr.encoding.polynomial

/-! ## Polynomial identity from loop 1 -/

/--
The mathematical polynomial identity from the Horner-scheme loop.

Given a coefficient list `coeffs`, a result list `v` of the same length,
a field element `g : GF16`, a scale `s : GF216`, and the conditions that
`v[0].toGF216 = 0`, `hornerAccum g coeffs 0 = 0`, and
`v[k].toGF216 = s * hornerAccum g coeffs k` for `k > 0`, then
`listToGF216Poly v * (X - C g.toGF216) = X * C s * listToGF216Poly coeffs`.
-/
theorem poly_identity_from_loop1
    (coeffs v : List GF16)
    (g : GF16) (s : GF216)
    (hlen : v.length = coeffs.length)
    (hpos : 0 < coeffs.length)
    (hv0_zero : ∀ (h0 : 0 < v.length),
        (v.get ⟨0, h0⟩).toGF216 = 0)
    (hH0 : hornerAccum g coeffs 0 = 0)
    (hvk : ∀ k (hk : k < v.length), 0 < k →
        (v.get ⟨k, hk⟩).toGF216 =
          s * hornerAccum g coeffs k) :
    listToGF216Poly v * (X - C (g.toGF216)) =
      X * C s * listToGF216Poly coeffs := by
  -- (proof body unchanged, ~90 lines)
  sorry

end spqr.encoding.polynomial
```

### 3. `Spqr/Math/Poly/Aeneas/MultXdiff.lean` (~70 lines)

**Content:** `mult_xdiff_poly_identity` (lines 179–236 of current file).

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Basic.Defs
import Spqr.Math.Poly.Coeff.Basic
import Spqr.Math.Poly.Coeff.ListOps
import Spqr.Math.List

/-!
# Polynomial identity for `mult_xdiff_assign_trailing`

Closed-form identity for the in-place recurrence `v[i−1] −= v[i] * d`
used by `mult_xdiff_assign_trailing`.

## Main statements

* `mult_xdiff_poly_identity` — `listToGF216Poly rs = listToGF216Poly cs −
  C(d.toGF216) · X^(s−1) · listToGF216Poly (cs.drop s)`.
-/

open Aeneas Aeneas.Std Result Polynomial
open spqr.math.gf spqr.encoding.gf spqr.encoding.polynomial

namespace spqr.encoding.polynomial

/-! ## Polynomial identity for mult_xdiff_assign_trailing -/

/--
The mathematical polynomial identity for `mult_xdiff_assign_trailing`.

Given a coefficient list `cs`, a result list `rs` of the same length,
a starting index `s ≥ 1` with `s ≤ cs.length`, and a field element
`d : GF16`, when carry-propagated positions satisfy
`rs[j].toGF216 = cs[j].toGF216 − cs[j+1].toGF216 * d.toGF216` and all
other positions are unchanged, then `listToGF216Poly rs =
listToGF216Poly cs − C(d.toGF216) · X^(s−1) · listToGF216Poly (cs.drop s)`.
-/
theorem mult_xdiff_poly_identity
    (cs rs : List GF16) (s : Nat) (d : GF16)
    (h_s_pos : 1 ≤ s) (h_s_le : s ≤ cs.length)
    (h_len : rs.length = cs.length)
    (h_mod : ∀ j, s ≤ j + 1 → j + 1 < cs.length → ∀ hj : j < rs.length,
      (rs.get ⟨j, hj⟩).toGF216 = (cs[j]!).toGF216 - (cs[j + 1]!).toGF216 * d.toGF216)
    (h_same : ∀ j, ¬(s ≤ j + 1 ∧ j + 1 < cs.length) → rs[j]? = cs[j]?) :
    listToGF216Poly rs =
      listToGF216Poly cs -
      C d.toGF216 * X ^ (s - 1) * listToGF216Poly (cs.drop s) := by
  -- (proof body unchanged, ~30 lines)
  sorry

end spqr.encoding.polynomial
```

### 4. `Spqr/Math/Poly/Aeneas/PowerVector.lean` (~90 lines)

**Content:** `div2_add_sum_eq`, `power_invariant_step`,
`initial_power_invariant` (lines 238–292 of current file).

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Basic.Defs
import Spqr.Math.Poly.CharTwo.ToGF216

/-!
# Power-vector invariant

Lemmas for maintaining the invariant `xs[j].toGF216 = x.toGF216 ^ j`
during the power-vector construction in `compute_at`.

## Main statements

* `div2_add_sum_eq` — `n / 2 + (n / 2 + n % 2) = n`.
* `power_invariant_step` — appending `g = xs[n/2] * xs[n/2 + n%2]` extends
  the power vector.
* `initial_power_invariant` — `[GF16::ONE, x]` satisfies the power-vector
  invariant.
-/

open Aeneas Aeneas.Std Result Polynomial
open spqr.math.gf spqr.encoding.gf spqr.encoding.polynomial

namespace spqr.encoding.polynomial

/-! ## Euclidean-division helper -/

/-- Euclidean-division identity: `n / 2 + (n / 2 + n % 2) = n`. -/
theorem div2_add_sum_eq (n : Nat) : n / 2 + (n / 2 + n % 2) = n := by
  have := Nat.div_add_mod n 2; omega

/-! ## Power-vector invariant -/

/--
Power-vector invariant preservation.

Appending `g = xs[n/2] * xs[n/2 + n%2]` to a power vector `xs` of length
`n ≥ 2` that satisfies `xs[j].toGF216 = x.toGF216 ^ j` for all `j < n`
produces a vector of length `n + 1` satisfying the same property for all
`j < n + 1`.
-/
theorem power_invariant_step
    (x : GF16) (xs : List GF16) (g : GF16)
    (h_ge2 : 2 ≤ xs.length)
    (h_pow : ∀ j, j < xs.length → (xs[j]!).toGF216 = x.toGF216 ^ j)
    (h_g : g.toGF216 =
      (xs[xs.length / 2]!).toGF216 *
      (xs[xs.length / 2 + xs.length % 2]!).toGF216) :
    ∀ j, j < (xs ++ [g]).length → ((xs ++ [g])[j]!).toGF216 = x.toGF216 ^ j := by
  -- (proof body unchanged, ~15 lines)
  sorry

/--
Initial power-vector invariant.

The two-element vector `[GF16::ONE, x]` satisfies the power-vector invariant:
`[ONE, x][j]!.toGF216 = x.toGF216 ^ j` for all `j < 2`.
-/
theorem initial_power_invariant (x : GF16) :
    ∀ j, j < [GF16.ONE, x].length →
      ([GF16.ONE, x][j]!).toGF216 = x.toGF216 ^ j := by
  -- (proof body unchanged, ~5 lines)
  sorry

end spqr.encoding.polynomial
```

### 5. `Spqr/Math/Poly/Aeneas/DotProduct.lean` (~70 lines)

**Content:** `dot_product_eq_eval`, `zero_toGF216_eq_empty_sum`,
`max_two_succ_le_usize_max` (lines 294–347 of current file).

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Basic.Defs
import Spqr.Math.Poly.Coeff.Basic
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Math.Poly.Eval

/-!
# Dot-product to evaluation bridge

Connecting the dot product of coefficient and power vectors to
polynomial evaluation, and related Aeneas-level utility lemmas.

## Main statements

* `dot_product_eq_eval` — dot product of coefficient and power vectors
  equals polynomial evaluation.
* `zero_toGF216_eq_empty_sum` — `GF16.ZERO.toGF216` equals an empty sum.
* `max_two_succ_le_usize_max` — `max 2 n + 1 ≤ Usize.max` when
  `n + 1 ≤ Usize.max`.
-/

open Aeneas Aeneas.Std Result Polynomial
open spqr.math.gf spqr.encoding.gf spqr.encoding.polynomial

namespace spqr.encoding.polynomial

/-! ## Dot-product to evaluation bridge -/

/--
Dot-product to polynomial evaluation bridge.

When the power vector `xs` satisfies `xs[j].toGF216 = x.toGF216 ^ j` for
all `j < xs.length`, and `n = v.length ≤ xs.length`, the dot product
`∑ j ∈ Finset.range n, v[j]!.toGF216 * xs[j]!.toGF216` equals the
polynomial evaluation `(listToGF216Poly v).eval (x.toGF216)`.
-/
theorem dot_product_eq_eval
    (x : GF16) (v : List GF16) (xs : List GF16)
    (h_pow : ∀ j, j < xs.length → (xs[j]!).toGF216 = x.toGF216 ^ j)
    (h_len : v.length ≤ xs.length) :
    (∑ j ∈ Finset.range v.length,
      (v[j]!).toGF216 * (xs[j]!).toGF216) =
    (listToGF216Poly v).eval (x.toGF216) := by
  -- (proof body unchanged, ~10 lines)
  sorry

/-! ## Zero accumulator -/

/--
Zero accumulator equals empty sum.
`GF16.ZERO.toGF216 = ∑ j ∈ Finset.range 0, f j` for any `f`.
-/
theorem zero_toGF216_eq_empty_sum
    (v xs : alloc.vec.Vec GF16) :
    GF16.ZERO.toGF216 = ∑ j ∈ Finset.range 0,
      (v.val[j]!).toGF216 * (xs.val[j]!).toGF216 := by
  -- (proof body unchanged, ~2 lines)
  sorry

/-! ## Usize bound utility -/

/--
Max-2 length bound.
If `n + 1 ≤ Usize.max`, then `max 2 n + 1 ≤ Usize.max`.
-/
theorem max_two_succ_le_usize_max (n : Nat) (h : n + 1 ≤ Usize.max) :
    Nat.max 2 n + 1 ≤ Usize.max := by
  -- (proof body unchanged, ~3 lines)
  sorry

end spqr.encoding.polynomial
```

---

## Naming convention changes (applied in this refactor)

All existing names are **preserved as-is**. No renaming is required
for this file since the current names already follow Mathlib
conventions:

| Name | Convention | Status |
|------|-----------|--------|
| `poly_identity_from_loop1` | `snake_case` proposition | ✓ |
| `mult_xdiff_poly_identity` | `snake_case` proposition | ✓ |
| `div2_add_sum_eq` | `snake_case` proposition | ✓ |
| `power_invariant_step` | `snake_case` proposition | ✓ |
| `initial_power_invariant` | `snake_case` proposition | ✓ |
| `dot_product_eq_eval` | `snake_case` proposition | ✓ |
| `zero_toGF216_eq_empty_sum` | `snake_case` proposition | ✓ |
| `max_two_succ_le_usize_max` | `snake_case` proposition | ✓ |

### Docstring reformatting (applied)

The current `Aeneas.lean` uses `**bold first-line**` docstring headers.
In the new files these are unwrapped to plain prose, matching both
Mathlib and `Gf2Poly/Basic.lean`:

| Before | After |
|--------|-------|
| `**Mathematical polynomial identity from the Horner-scheme loop.**` | `The mathematical polynomial identity from the Horner-scheme loop.` |
| `**Euclidean-division identity**` | `Euclidean-division identity:` |
| `**Power-vector invariant preservation.**` | `Power-vector invariant preservation.` |
| `**Dot-product to polynomial evaluation bridge.**` | `Dot-product to polynomial evaluation bridge.` |
| `**Zero accumulator equals empty sum.**` | `Zero accumulator equals empty sum.` |
| `**Max-2 length bound.**` | `Max-2 length bound.` |

---

## Namespace placement summary

| Declaration | Namespace |
|------------|-----------|
| `poly_identity_from_loop1` | `spqr.encoding.polynomial` |
| `mult_xdiff_poly_identity` | `spqr.encoding.polynomial` |
| `div2_add_sum_eq` | `spqr.encoding.polynomial` |
| `power_invariant_step` | `spqr.encoding.polynomial` |
| `initial_power_invariant` | `spqr.encoding.polynomial` |
| `dot_product_eq_eval` | `spqr.encoding.polynomial` |
| `zero_toGF216_eq_empty_sum` | `spqr.encoding.polynomial` |
| `max_two_succ_le_usize_max` | `spqr.encoding.polynomial` |

This is identical to the current placement. The namespace
`spqr.encoding.polynomial` mirrors how `Gf2Poly/Basic.lean` places
`natToBinaryPoly` inside `namespace spqr.math.gf`.

---

## Import refinement

The current `Aeneas.lean` imports **all 17** Poly sub-modules. After
the split, each sub-file imports only what it needs:

| New file | Imports |
|----------|---------|
| `PolyIdentity.lean` | `Basic.Defs`, `Coeff.Basic`, `CharTwo.Basic`, `Horner.Defs`, `Horner.Eval` |
| `MultXdiff.lean` | `Basic.Defs`, `Coeff.Basic`, `Coeff.ListOps`, `General` |
| `PowerVector.lean` | `Basic.Defs`, `CharTwo.ToGF216` |
| `DotProduct.lean` | `Basic.Defs`, `Coeff.Basic`, `CharTwo.ToGF216`, `Eval` |

This reduces the transitive import cost for consumers that only need
a specific theorem.

---

## Line-count summary

| File | Approx. lines |
|------|-------------:|
| `Spqr/Math/Poly/Aeneas.lean` (shim) | ~25 |
| `Spqr/Math/Poly/Aeneas/PolyIdentity.lean` | ~120 |
| `Spqr/Math/Poly/Aeneas/MultXdiff.lean` | ~70 |
| `Spqr/Math/Poly/Aeneas/PowerVector.lean` | ~90 |
| `Spqr/Math/Poly/Aeneas/DotProduct.lean` | ~70 |
| **Total** | **~375** |

The increase over the current 347 lines is per-file overhead (header,
imports, module docstring, `namespace` blocks, section markers, blank
lines).

---

## Migration steps

1. **Create** the directory `Spqr/Math/Poly/Aeneas/` and the four new
   files, copying the proof bodies verbatim from the current
   `Aeneas.lean`.

2. **Replace** `Spqr/Math/Poly/Aeneas.lean` with the re-export shim
   (4 imports + module docstring).

3. **Update** `Spqr.lean` to add the four new imports:
   ```
   import Spqr.Math.Poly.Aeneas.DotProduct
   import Spqr.Math.Poly.Aeneas.MultXdiff
   import Spqr.Math.Poly.Aeneas.PolyIdentity
   import Spqr.Math.Poly.Aeneas.PowerVector
   ```
   (The existing `import Spqr.Math.Poly.Aeneas` line can be kept or
   removed — Lean will pull in all four sub-files transitively through
   the shim.)

4. **Run** `lake build Spqr`. The public API is unchanged, so no
   downstream file should need editing.

5. **Verify** that the three downstream consumers still build
   without modification:
   ```
   lake build Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateComplete
   lake build Spqr.Specs.Encoding.Polynomial.Poly.MultXdiffAssignTrailing
   lake build Spqr.Specs.Encoding.Polynomial.Poly.ComputeAt
   ```

---

## Risks and non-goals

* **Non-goal.** We are *not* changing any definitions, lemma
  statements, or proof terms. This is a pure file-level
  reorganization aligned with the `Gf2Poly/Basic.lean` style.
* **Risk: import cycles.** The dependency DAG above is acyclic by
  construction — every new file depends only on upstream Poly
  sub-modules, never on sibling Aeneas sub-files.
* **Risk: namespace placement.** Every sub-file must open/close
  exactly `namespace spqr.encoding.polynomial` so that the existing
  fully-qualified names are preserved bit-for-bit.
* **Risk: `open` directives.** Each new file opens only what it
  needs (`open Polynomial` is always required; `open Aeneas
  Aeneas.Std Result` in all four files since they all reference
  Aeneas-extracted types like `GF16`, `Poly`, `Vec`).
