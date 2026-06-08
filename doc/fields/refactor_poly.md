# Refactoring proposal for `Spqr/Math/Poly.lean`

## Motivation

`Spqr/Math/Poly.lean` has grown to **982 lines** and now mixes several
loosely-related topics:

* the core bridge from the Aeneas-extracted `spqr.encoding.polynomial.Poly`
  to the Mathlib polynomial ring `GF216[X]`,
* generic algebraic facts about polynomials over a characteristic-2 field,
* Lagrange interpolation infrastructure (products of linear factors,
  denominator product, scaling factor, basis polynomial, partial sums),
* Horner-scheme evaluation,
* the `expectedTrailingPoly` recurrence used by
  `lagrange_interpolate_prepare`,
* a few miscellaneous polynomial identities and `Inhabited` instances.

A single file of this size makes the module slow to elaborate, painful to
navigate, and hard to extend without producing review noise. Following the
pattern already used in `Spqr/Math/Gf2Poly/Basic.lean` (and elsewhere in
the project), we propose splitting `Spqr/Math/Poly.lean` into a directory
of focused sub-files of ~200 lines each, each importing only what it
actually needs.

The user-facing module `Spqr.Math.Poly` is preserved as a thin re-export
file so that no downstream `import` has to change.

---

## Conventions: aligning with `Spqr/Math/Gf2Poly/Basic.lean`

The reference for naming, namespacing, and formatting is the existing
file `Spqr/Math/Gf2Poly/Basic.lean`. Every new file under
`Spqr/Math/Poly/` follows the same rules.

### 1. File header

Use the exact 4-line copyright/license block found at the top of
`Gf2Poly/Basic.lean` (no `(c)`, no extra blank lines):

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
```

### 2. Imports

Imports come immediately after the header, with no blank line between
them and the header. They use the **smallest Mathlib prefix that
suffices** (just as `Gf2Poly/Basic.lean` imports
`Mathlib.RingTheory.Polynomial.Basic` rather than a larger umbrella).

### 3. Module docstring

After the imports, every file gets a module docstring with the same
shape as `Gf2Poly/Basic.lean`:

```lean
/-!
# <Title>

<One-paragraph plain-English description.>

## Main definitions

* `<def₁>` — …

## Main statements

* `<lemma₁>` — …

## Conventions

* <Bullet describing any non-obvious naming/notation choice.>
-/
```

The four sections (title, intro paragraph, `Main definitions`,
`Main statements`, optional `Conventions`) match
`Gf2Poly/Basic.lean` 1-for-1.

### 4. `open` directives

A single, narrow `open Polynomial` (as in `Gf2Poly/Basic.lean` line 52),
plus the project-specific opens only where needed (e.g.
`open Aeneas Aeneas.Std Result` inside the files that actually touch
the Aeneas-extracted `Poly`/`Pt` types).

### 5. Type abbreviations live at the *root* namespace

`Gf2Poly/Basic.lean` declares

```lean
abbrev BinaryPoly := (ZMod 2)[X]
```

at the **root namespace**, before any `namespace` block. We mirror this:

```lean
abbrev GF216Poly := GF216[X]
```

lives at the root in `Spqr/Math/Poly/Basic.lean`.

### 6. Bridge functions live inside the project namespace

`Gf2Poly/Basic.lean` places its bridge function `natToBinaryPoly` (and
all its lemmas) inside

```lean
namespace spqr.math.gf
…
end spqr.math.gf
```

We mirror this for the `Poly ↔ GF216[X]` bridge: every declaration whose
short name is `listToGF216Poly`, `Poly.toGF216Poly`, `Poly.evalAt`,
`prodLinearFactors`, `lagrangeDenomProd`, `lagrangeBasisPoly`,
`lagrangeInterpolantSum`, `hornerAccum`, `expectedTrailingPoly`, …
lives inside

```lean
namespace spqr.encoding.polynomial
…
end spqr.encoding.polynomial
```

Inside that namespace we do **not** introduce extra sub-namespaces like
`namespace Poly` — `Gf2Poly/Basic.lean` does not, and the dot-notation
`Poly.toGF216Poly` works without one (the declaration is literally
named `Poly.toGF216Poly`, exactly as in the current file).

### 7. Characteristic-2 helpers live at the *root* under the type prefix

`Gf2Poly/Basic.lean` deliberately puts the two characteristic-2 lemmas
*outside* `namespace spqr.math.gf`, at the root, under the `BinaryPoly`
prefix:

```lean
/-!
## Characteristic-2 facts in `BinaryPoly`
…
-/

lemma BinaryPoly.neg_eq (a : BinaryPoly) : -a = a := CharTwo.neg_eq a
lemma BinaryPoly.sub_eq_add (a b : BinaryPoly) : a - b = a + b :=
  CharTwo.sub_eq_add a b
```

We mirror this exactly in `Spqr/Math/Poly/CharTwo.lean`:

```lean
/-!
## Characteristic-2 facts in `GF216` and `GF216Poly`
-/

lemma GF216.two_eq_zero : (2 : GF216) = 0 := …
lemma GF216.add_self_eq_zero (x : GF216) : x + x = 0 := …
lemma GF216Poly.neg_eq (a : GF216Poly) : -a = a := …
lemma GF216Poly.sub_eq_add (a b : GF216Poly) : a - b = a + b := …
```

— all at the root, each lemma under its type prefix
(`GF216.` or `GF216Poly.`) so that dot notation is available.

### 8. `GF16.toGF216_*` lemmas

Following the same logic, the `GF16.toGF216_zero_val` and
`GF16.toGF216_one_val` lemmas (which are about the
`spqr.encoding.gf.GF16` type) live inside

```lean
namespace spqr.encoding.gf
…
end spqr.encoding.gf
```

so that they can be written as `lemma GF16.toGF216_zero_val …`,
mirroring how `Gf2Poly/Basic.lean` writes `natToBinaryPoly_*` inside
`namespace spqr.math.gf`.

### 9. Section headers

Use `/-! ## Section title -/` exactly as in `Gf2Poly/Basic.lean`
(lines 59, 70, 82). No `--` style markers, no separate `section` /
`end section` blocks.

### 10. Declaration-level naming and formatting (Mathlib style)

This is the section that needs the most discipline during the
refactor. Every `def` / `lemma` / `theorem` / `instance` in the new
files must follow Mathlib's published
[Naming Convention](https://leanprover-community.github.io/contribute/naming.html)
and [Style Guide](https://leanprover-community.github.io/contribute/style.html).

#### 10.1 `def` vs `lemma` vs `theorem`

* `def` / `noncomputable def` — definitions that introduce new
  terms or types (`listToGF216Poly`, `Poly.toGF216Poly`, `Poly.evalAt`,
  `prodLinearFactors`, `lagrangeDenomProd`, `lagrangeScaleGF216`,
  `lagrangeBasisPoly`, `lagrangeInterpolantSum`, `hornerAccum`,
  `expectedTrailingPoly`).
* `theorem` — *headline* results stated for downstream consumption
  (e.g. `Poly.toGF216Poly_eq_zero`, `hornerAccum_zero_eq_eval`,
  `expectedTrailingPoly_eq_prodLinearFactors`,
  `natToBinaryPoly_split` in `Gf2Poly/Basic.lean`).
* `lemma` — everything else (auxiliary statements, structural
  unfolding, coefficient/degree bounds, characteristic-2 facts).

This matches Mathlib's usage: `theorem` is reserved for the
"named" results listed in `## Main statements`; supporting facts
are `lemma`.

#### 10.2 Identifier capitalization

| Kind                            | Convention                            |
|---------------------------------|---------------------------------------|
| Types, type classes, structures | `UpperCamelCase` (`GF216Poly`, `Pt`)  |
| Terms, `def`, `lemma`, `theorem`, `instance` | `lowerCamelCase` or snake_case per Mathlib's rule below |
| Namespaces (root project)       | `lower.dotted.case` (`spqr.encoding.polynomial`) |
| File names                      | `UpperCamelCase.lean`                 |

Mathlib's rule for term-level identifiers:

* If the name describes a **mathematical object** (a value or
  function), use `lowerCamelCase` —
  `listToGF216Poly`, `lagrangeBasisPoly`, `hornerAccum`,
  `expectedTrailingPoly`, `prodLinearFactors`.
* If the name describes a **proposition** (a fact about objects),
  use `snake_case` — `listToGF216Poly_coeff`,
  `prodLinearFactors_eval_root`, `hornerAccum_zero_eq_eval`,
  `expectedTrailingPoly_succ`.

All current names already obey this split, so no renaming is needed.

#### 10.3 Naming patterns for propositions

Mathlib's connector keywords, used as infix tokens inside
`snake_case`:

| Pattern        | Meaning                                | Example from project           |
|----------------|----------------------------------------|--------------------------------|
| `X_eq_Y`       | `X = Y` (or `X = …` headline equality) | `GF216Poly.sub_eq_add`         |
| `X_eq_zero`    | `X = 0`                                | `GF216.two_eq_zero`            |
| `X_eq_one`     | `X = 1`                                | (none currently)               |
| `X_of_Y`       | `Y → X` (introduction form)            | `coeff_zero_of_X_mul_identity` |
| `X_iff_Y`      | `X ↔ Y`                                | (would be `_iff_`)             |
| `X_le_Y` / `_lt_` | order facts                         | `natDegree_…_le`               |
| `X_ne_Y`       | `X ≠ Y`                                |                                |
| `X_pos` / `X_neg` | `0 < X` / `X < 0`                   |                                |

The verbal order matches the term order: write
`prodLinearFactors_eval_root`, **not** `eval_root_of_prodLinearFactors`.
This is exactly the convention used in `Gf2Poly/Basic.lean`
(`natToBinaryPoly_coeff`, `natToBinaryPoly_xor`,
`natToBinaryPoly_shiftLeft`, `natToBinaryPoly_split`,
`natToBinaryPoly_inj`).

#### 10.4 `@[simp]` discipline

Mark a lemma `@[simp]` **iff** its RHS is a normal form for `simp`
and the rewrite is confluent. Current `@[simp]` lemmas
(`listToGF216Poly_empty`, `prodLinearFactors_base`,
`lagrangeDenomProd_ge`, `hornerAccum_ge`,
`expectedTrailingPoly_zero`) all fit this pattern and stay
`@[simp]`. The attribute goes on the line **immediately above** the
declaration, mirroring `@[simp] lemma natToBinaryPoly_zero` in
`Gf2Poly/Basic.lean` line 110.

#### 10.5 `protected` / `private` discipline

* `private` is used for helpers that should not leak outside the
  file. We keep `prodLinearFactors_snoc_aux` as `private`
  (mirroring `private lemma mem_bitIndices_iff_testBit` in
  `Gf2Poly/Basic.lean`).
* `protected` is used when we want to *prevent* automatic
  short-name access after `open`. None of the current declarations
  needs `protected`, but if a downstream `open
  spqr.encoding.polynomial` would shadow a Mathlib name
  (e.g. `eval`), mark the declaration `protected`.

#### 10.6 Variables and `variable` blocks

Where the same arguments recur across many declarations, declare
them once via `variable`:

```lean
variable (cs : List GF16) (m : Nat)
```

so each lemma reads `lemma listToGF216Poly_coeff …` rather than
re-introducing `(cs : List GF16) (m : Nat)` every time.
`Gf2Poly/Basic.lean` does not use `variable` because each lemma
has different arguments; in `Coeff.lean` and
`LinearFactors.lean` we **will** benefit from `variable` blocks
because `(cs : List GF16)` and `(pts : List Pt)` recur in every
statement.

#### 10.7 Docstring formatting

Mathlib docstrings are plain sentences without `**bold**` headers
or section markers:

* **One short sentence** summarizing the statement, ending with a
  period.
* Optionally one or two follow-up sentences in the same `/-- … -/`
  block giving the mathematical context (no Markdown headings).
* No `**Bold first-line**` style. The current `Spqr/Math/Poly.lean`
  uses bold headers like `**Decomposition: …**` and
  `**GF(2¹⁶) has characteristic 2**`; these will be unwrapped to
  plain prose. This brings them in line with both Mathlib and
  `Gf2Poly/Basic.lean`, whose docstrings read:

  > "Interpret a natural number as a `BinaryPoly` by taking its
  > binary expansion as the sequence of coefficients."

  rather than `**Interpret …**`.

#### 10.8 Statement formatting

Mathlib's statement style, mirrored in `Gf2Poly/Basic.lean`:

* The `:` introducing the type goes on the **first line**.
* Subsequent argument and hypothesis lines are indented **4 spaces**
  past the start of the keyword.
* The body of the proof (`by …` or term-mode) is indented 2 spaces.
* Backticked code inside docstrings uses single backticks
  (`` `BinaryPoly` ``), not triple-backtick blocks.

Concrete example (from `Gf2Poly/Basic.lean`):

```lean
lemma natToBinaryPoly_xor (a b : ℕ) :
    natToBinaryPoly (a ^^^ b) = natToBinaryPoly a + natToBinaryPoly b := by
  …
```

Every long signature in the new files will be reformatted to match
this 4-space-indent pattern.

#### 10.9 Statement of `def` results

Following Mathlib:

* `noncomputable def` is used whenever the function pattern-matches
  on `Polynomial.coeff` or uses classical choice; this is already
  the case for every definition migrated.
* Use `where` to introduce structure fields and `:=` for direct
  bodies; do **not** mix the two styles in the same definition.
* `instance : Inhabited Pt where default := …` is preferred over the
  ⟨…⟩ form when the underlying record has named fields, mirroring
  `Gf2Poly/Basic.lean`'s lack of anonymous-constructor instances.

#### 10.10 Renaming opportunities (suggested, non-blocking)

A few existing names are slightly off-pattern for Mathlib. We list
them here for discussion; this refactor PR will keep names as-is
to keep the diff reviewable, and a follow-up PR can apply the
renames if desired:

| Current name                             | Suggested Mathlib-style name                  |
|------------------------------------------|-----------------------------------------------|
| `GF16.toGF216_zero_val`                  | `GF16.toGF216_eq_zero`                        |
| `GF16.toGF216_one_val`                   | `GF16.toGF216_eq_one`                         |
| `getElem_bang_toGF216_eq_coeff`          | `GF16.getElem!_toGF216_eq_coeff`              |
| `lagrangeDenomProd_ge`                   | `lagrangeDenomProd_eq_one_of_le` (closer to Mathlib's `…_of_…` pattern) |
| `prodLinearFactors_base`                 | `prodLinearFactors_eq_one_of_not_lt`          |
| `hornerAccum_ge`                         | `hornerAccum_eq_zero_of_le`                   |
| `expectedTrailingPoly_coeff_eq_zero`     | `expectedTrailingPoly_coeff_eq_zero_of_lt`    |
| `coeff_zero_of_X_mul_identity`           | `coeff_zero_eq_zero_of_X_mul_identity`        |
| `list_map_sum_eq_finset_sum`             | `List.map_sum_eq_Finset_sum`                  |
| `prodLinearFactors_eq_factor_mul_basis`  | `prodLinearFactors_eq_X_sub_C_mul`            |
| `listToGF216Poly_eq_X_mul_drop_one`      | `listToGF216Poly_eq_X_mul_listToGF216Poly_drop_one` |

#### 10.11 Mathlib-aligned renamings (applied in this refactor)

A few existing names are slightly off-pattern for Mathlib's
`_eq_zero_of_…` / `_of_…` connectives. To keep the new files
Mathlib-style end-to-end, the refactor applies the following
renames at the same time as the file split. Each old name is also
kept as a one-line `@[deprecated]` alias inside `Poly.lean` (the
shim) so that downstream code continues to compile.

| Current name                             | Mathlib-style name                            | New home file        |
|------------------------------------------|-----------------------------------------------|----------------------|
| `GF16.toGF216_zero_val`                  | `GF16.toGF216_eq_zero`                        | `CharTwo.lean`       |
| `GF16.toGF216_one_val`                   | `GF16.toGF216_eq_one`                         | `CharTwo.lean`       |
| `getElem_bang_toGF216_eq_coeff`          | `GF16.getElem!_toGF216_eq_coeff`              | `CharTwo.lean`       |
| `lagrangeDenomProd_ge`                   | `lagrangeDenomProd_eq_one_of_le`              | `Lagrange.lean`      |
| `prodLinearFactors_base`                 | `prodLinearFactors_eq_one_of_not_lt`          | `LinearFactors.lean` |
| `hornerAccum_ge`                         | `hornerAccum_eq_zero_of_le`                   | `Horner.lean`        |
| `expectedTrailingPoly_coeff_eq_zero`     | `expectedTrailingPoly_coeff_eq_zero_of_lt`    | `ExpectedTrailing.lean` |
| `coeff_zero_of_X_mul_identity`           | `coeff_zero_eq_zero_of_X_mul_identity`        | `Identities.lean`    |
| `list_map_sum_eq_finset_sum`             | `List.map_sum_eq_Finset_sum`                  | `Identities.lean`    |
| `prodLinearFactors_eq_factor_mul_basis`  | `prodLinearFactors_eq_X_sub_C_mul`            | `LinearFactors.lean` |
| `listToGF216Poly_eq_X_mul_drop_one`      | `listToGF216Poly_eq_X_mul_listToGF216Poly_drop_one` | `Coeff.lean`    |

Conventions applied:

* Result-direction first, hypothesis-direction last:
  `prodLinearFactors_eq_one_of_not_lt` reads as "the polynomial
  *equals* 1, *because* the index is not less than the bound".
* For `iff`-like statements use `…_iff_…`; for one-directional
  implications use `…_of_…`.
* `getElem!_` (not `getElem_bang_`) matches Mathlib's existing
  `List.getElem!_…` lemmas.
* `Finset` and `List` are capitalized inside identifiers when they
  refer to the corresponding namespace
  (`List.map_sum_eq_Finset_sum`).

For each renamed declaration we also emit a Mathlib-style
deprecation alias in the new home file:

```lean
@[deprecated (since := "2026-06-08")]
alias GF16.toGF216_zero_val := GF16.toGF216_eq_zero
```

so that downstream files importing the old name continue to compile
with only a deprecation warning, exactly as Mathlib does for its own
renames.

### 11. `private` helpers


Private auxiliary lemmas keep the `private` modifier
(cf. `private lemma mem_bitIndices_iff_testBit` in `Gf2Poly/Basic.lean`
line 73, and `private lemma prodLinearFactors_snoc_aux` in the current
`Poly.lean`).

### 12. Whitespace and attribute placement

* Attribute lines (`@[simp]`) immediately precede the declaration on
  their own line, as in `Gf2Poly/Basic.lean` line 110.
* One blank line between sibling declarations, two between sections.
* Lines wrap at ~100 columns (the current file already respects this).

---

## Proposed file layout

Mathlib's directory hierarchy bundles topic-related `.lean` files into
folders whose name matches the concept, with a `Basic.lean` (and
optionally `Defs.lean`) acting as the entry point — for example
`Mathlib/Algebra/Polynomial/{Basic,Coeff,Eval,Degree,…}.lean`,
`Mathlib/LinearAlgebra/Lagrange.lean` (a single-file leaf because the
topic is small), `Mathlib/Algebra/CharP/{Basic,Two}.lean`. Following
the same logic, every new sub-topic of `Spqr.Math.Poly` becomes its
own **sub-folder** under `Spqr/Math/Poly/`, holding a `Basic.lean`
plus, where useful, additional focused files. This is the same
pattern that the project already uses in `Spqr/Math/Gf16/` and
`Spqr/Math/Gf2Poly/`.

```
Spqr/Math/Poly.lean                       (re-export shim)
Spqr/Math/Poly/
│
├── Aeneas.lean                          (existing, untouched)
├── General.lean                         (existing, untouched)
├── Mathlib.lean                         (existing, untouched)
├── ModByMonic.lean                      (existing, untouched)
│
├── Basic/                               (NEW folder — bridge `Poly ↔ GF216[X]`)
│   ├── Defs.lean                        (~120 lines:  `GF216Poly`,
│   │                                     `listToGF216Poly`,
│   │                                     `Poly.toGF216Poly`,
│   │                                     `Inhabited` instances)
│   └── Zero.lean                        (~80  lines:  empty-list /
│                                         zero-polynomial characterization)
│
├── Coeff/                               (NEW folder — coefficient lemmas)
│   ├── Basic.lean                       (~120 lines:  `listToGF216Poly_coeff`,
│   │                                     `_coeff_eq_zero`,
│   │                                     `_singleton`, `_cons`)
│   └── ListOps.lean                     (~120 lines:  `_append_singleton`,
│                                         `_add`, `_eq_X_mul_drop_one`,
│                                         `_eq_of_coeffs`)
│
├── CharTwo/                             (NEW folder — characteristic-2 facts)
│   ├── Basic.lean                       (~70  lines:  `GF216.two_eq_zero`,
│   │                                     `GF216.add_self_eq_zero`,
│   │                                     `GF216Poly.neg_eq`,
│   │                                     `GF216Poly.sub_eq_add`)
│   └── ToGF216.lean                     (~80  lines:  `GF16.toGF216_eq_zero`,
│                                         `_eq_one`,
│                                         `GF16.getElem!_toGF216_eq_coeff`)
│
├── Eval.lean                            (NEW single file, ~80 lines:
│                                         `Poly.evalAt`,
│                                         `Poly.evalAt_zero_poly`,
│                                         `listToGF216Poly_eval`)
│                                        — kept as a single file because the
│                                          topic is small, mirroring
│                                          `Mathlib/LinearAlgebra/Lagrange.lean`
│
├── LinearFactors/                       (NEW folder — `∏ (X − pts[j].x)`)
│   ├── Basic.lean                       (~120 lines:  `prodLinearFactors`,
│   │                                     `_base`, `_step`,
│   │                                     `_snoc_aux` (private), `_snoc`)
│   └── Degree.lean                      (~120 lines:  `_eval_root`,
│                                         `_split_at`,
│                                         `_eq_X_sub_C_mul`,
│                                         `natDegree_…_le`,
│                                         `_coeff_eq_zero_high`)
│
├── Lagrange/                            (NEW folder — interpolation)
│   ├── DenomProd.lean                   (~90  lines:  `lagrangeDenomProd`,
│   │                                     `_eq_one_of_le`,
│   │                                     `_skip`, `_accum`)
│   ├── BasisPoly.lean                   (~70  lines:  `lagrangeScaleGF216`,
│   │                                     `lagrangeBasisPoly`,
│   │                                     `natDegree_lagrangeBasisPoly_le`)
│   └── InterpolantSum.lean              (~70  lines:  `lagrangeInterpolantSum`,
│                                         `_eq_finset_sum`,
│                                         `_coeff_high`)
│
├── Horner/                              (NEW folder — Horner evaluation)
│   ├── Defs.lean                        (~80  lines:  `hornerAccum`,
│   │                                     `_eq_zero_of_le`, `_unfold`,
│   │                                     `_cons`)
│   └── Eval.lean                        (~80  lines:  `_cancel`,
│                                         `hornerAccum_zero_eq_eval`)
│
├── ExpectedTrailing/                    (NEW folder — recurrence)
│   ├── Defs.lean                        (~60  lines:  `expectedTrailingPoly`,
│   │                                     `_zero`, `_succ`)
│   └── Basic.lean                       (~80  lines:  `_coeff_eq_zero_of_lt`,
│                                         `_eq_prodLinearFactors`)
│
└── Identities/                          (NEW folder — misc helpers)
    └── Basic.lean                       (~80  lines:
                                          `coeff_zero_eq_zero_of_X_mul_identity`,
                                          `List.map_sum_eq_Finset_sum`,
                                          `Inhabited Poly` instance)
```

### Why folders, not flat files?

Adopting **one folder per topic** mirrors Mathlib's own layout:

| Mathlib folder/file                            | Our analogue                                  |
|------------------------------------------------|-----------------------------------------------|
| `Mathlib/Algebra/Polynomial/Basic.lean`        | `Spqr/Math/Poly/Basic/Defs.lean`              |
| `Mathlib/Algebra/Polynomial/Coeff.lean`        | `Spqr/Math/Poly/Coeff/Basic.lean`             |
| `Mathlib/Algebra/Polynomial/Eval.lean`         | `Spqr/Math/Poly/Eval.lean`                    |
| `Mathlib/Algebra/Polynomial/Degree/Basic.lean` | `Spqr/Math/Poly/LinearFactors/Degree.lean`    |
| `Mathlib/Algebra/CharP/Basic.lean`             | `Spqr/Math/Poly/CharTwo/Basic.lean`           |
| `Mathlib/Algebra/CharP/Two.lean`               | `Spqr/Math/Poly/CharTwo/ToGF216.lean`         |
| `Mathlib/LinearAlgebra/Lagrange.lean`          | `Spqr/Math/Poly/Lagrange/{DenomProd,BasisPoly,InterpolantSum}.lean` |
| `Mathlib/Algebra/Polynomial/Smeval.lean`       | `Spqr/Math/Poly/Horner/{Defs,Eval}.lean`      |

Benefits:

1. **Topic locality** — every file related to "Lagrange interpolation"
   is one `cd` away under `Lagrange/`, just as everything related to
   "polynomial coefficient lemmas" lives under `Coeff/`.
2. **Future extension** — once the project gains, say, an
   `InterpolantValue.lean` (the value of `lagrangeInterpolantSum` at
   a point), it slots into `Lagrange/` without inflating the flat
   directory listing.
3. **Smaller files** — each `.lean` is now in the ~70–120 line range,
   well below the original 982 lines and below the 200-line target.
4. **Matches existing project style** —
   `Spqr/Math/Gf16/{Basic,Field,Irreducible}.lean` and
   `Spqr/Math/Gf2Poly/{Basic,NatRep}.lean` already use the "folder
   plus topic-named files" pattern; this extension is the natural
   next step.

### Acyclic dependency DAG (folder-level)

```
                 Basic
                 │   │
        ┌────────┘   └────────┐
        ▼                     ▼
     Coeff                 CharTwo
        │   │                 │
        │   └───────┬─────────┤
        ▼           ▼         ▼
   LinearFactors   Eval    Horner
        │           │
        └─────┬─────┘
              ▼
          Lagrange
              │
              ▼
      ExpectedTrailing
              │
              ▼
         Identities
```

(Within each folder the files depend on each other in the obvious
order: `Defs.lean` → `Basic.lean` → `…`. None of these intra-folder
dependencies creates a cycle.)


---

## File-by-file content

Each file below is rendered in the same "shape" as
`Gf2Poly/Basic.lean`: header → imports → module docstring → root-level
`abbrev` (if any) → `open Polynomial` → `namespace spqr.encoding.polynomial`
(if applicable) → `/-! ## Section -/` markers → declarations →
`end spqr.encoding.polynomial` → optional root-level characteristic-2
section.

### 1. `Spqr/Math/Poly.lean` — re-export shim

The shim imports each topic folder via its `Basic.lean` (or
`Defs.lean`), exactly as Mathlib's umbrella files do
(e.g. `Mathlib/Algebra/Polynomial.lean` imports the various
`Mathlib/Algebra/Polynomial/*.lean` files):

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
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


/-!
# `GF(2¹⁶)[X]` polynomial library — umbrella module

This module is a thin re-export of the sub-files under
`Spqr/Math/Poly/`. It exists so that downstream files can keep writing
`import Spqr.Math.Poly` after the refactor.

Each topic lives in a dedicated file; see the individual files for
their `## Main definitions` and `## Main statements`.
-/
```

### 2. `Spqr/Math/Poly/Basic.lean` (~190 lines)

**Skeleton (mirroring `Gf2Poly/Basic.lean`):**

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Bridge from the Aeneas-extracted `Poly` to `GF(2¹⁶)[X]`

…(intro paragraph + Implementation → Mathematical diagram, copied
from the current top-of-file docstring)…

## Main definitions

* `GF216Poly` — abbreviation for `GF(2¹⁶)[X]`.
* `listToGF216Poly` — interprets a `List GF16` as a polynomial in
  `GF216[X]`.
* `Poly.toGF216Poly` — canonical bridge from the Aeneas-extracted
  `Poly` to `GF216[X]`.

## Main statements

* `listToGF216Poly_nil`, `@[simp] listToGF216Poly_empty`
* `Poly.toGF216Poly_eq_zero`

## Conventions

* `GF216`  = `GaloisField 2 16`.
* `GF216Poly` = `GF216[X]`.
* `listToGF216Poly` reads coefficients in ascending degree order.
-/

open Aeneas Aeneas.Std Result
open Polynomial
open spqr.encoding.gf spqr.math.gf

abbrev GF216Poly := GF216[X]

namespace spqr.encoding.polynomial

/-! ## Inhabited instances -/

deriving instance Inhabited for spqr.encoding.gf.GF16

instance : Inhabited Pt where
  default := ⟨⟨0#u16⟩, ⟨0#u16⟩⟩

/-! ## Core definition -/

noncomputable def listToGF216Poly (cs : List GF16) : GF216Poly := …

noncomputable def Poly.toGF216Poly (p : Poly) : GF216Poly :=
  listToGF216Poly p.coefficients.val

/-! ## Zero polynomial characterization -/

lemma listToGF216Poly_nil : listToGF216Poly [] = 0 := …
theorem Poly.toGF216Poly_eq_zero (p : Poly)
    (h : p.coefficients.length = 0) : p.toGF216Poly = 0 := …

@[simp]
lemma listToGF216Poly_empty :
    listToGF216Poly ([] : List GF16) = 0 :=
  listToGF216Poly_nil

end spqr.encoding.polynomial
```

### 3. `Spqr/Math/Poly/Coeff.lean` (~190 lines)

**Skeleton:**

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Basic

/-!
# Coefficients of `listToGF216Poly` and list manipulations

## Main statements

* `listToGF216Poly_coeff`, `listToGF216Poly_coeff_eq_zero`
* `listToGF216Poly_singleton`, `listToGF216Poly_cons`
* `listToGF216Poly_append_singleton`, `listToGF216Poly_add`
* `listToGF216Poly_eq_X_mul_drop_one`
* `listToGF216Poly_eq_of_coeffs`

## Conventions

* `cs.get ⟨m, hm⟩` is the canonical way to read coefficient `m`.
* All "out of range ⇒ 0" statements use `cs.length ≤ m`.
-/

open Polynomial
open spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial

/-! ## Coefficient characterization -/

lemma listToGF216Poly_coeff (cs : List GF16) (m : Nat) : … := …
lemma listToGF216Poly_coeff_eq_zero
    (cs : List GF16) (m : Nat) (hm : cs.length ≤ m) : … := …

/-! ## Singleton and cons decomposition -/

lemma listToGF216Poly_singleton (a : GF16) : … := …
lemma listToGF216Poly_cons (c : GF16) (cs : List GF16) : … := …

/-! ## Linking lemmas: `listToGF216Poly` and list operations -/

lemma listToGF216Poly_append_singleton (cs : List GF16) (a : GF16) : … := …
lemma listToGF216Poly_add (cs ds : List GF16) … : … := …
lemma listToGF216Poly_eq_X_mul_drop_one
    (cs : List GF16) (h0 : (listToGF216Poly cs).coeff 0 = 0) : … := …
lemma listToGF216Poly_eq_of_coeffs (cs : List GF16) (q : GF216Poly) … : … := …

end spqr.encoding.polynomial
```

### 4. `Spqr/Math/Poly/CharTwo.lean` (~110 lines)

This file ends with a **root-level** characteristic-2 section, *exactly*
mirroring the tail of `Gf2Poly/Basic.lean`.

**Skeleton:**

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Basic

/-!
# Characteristic-2 facts in `GF216` and `GF216Poly`

## Main statements

* `GF16.toGF216_zero_val`, `GF16.toGF216_one_val`
* `getElem_bang_toGF216_eq_coeff`
* `GF216.two_eq_zero`, `GF216.add_self_eq_zero`
* `GF216Poly.neg_eq`, `GF216Poly.sub_eq_add`
-/

open Polynomial
open spqr.math.gf

namespace spqr.encoding.gf

/-! ## `GF16.toGF216` at 0 and 1 -/

lemma GF16.toGF216_zero_val (g : GF16) (h : g.value.val = 0) :
    g.toGF216 = 0 := …
lemma GF16.toGF216_one_val (g : GF16) (h : g.value.val = 1) :
    g.toGF216 = 1 := …

end spqr.encoding.gf

namespace spqr.encoding.polynomial

/-! ## Bridge between `getElem!` and coefficients -/

lemma getElem_bang_toGF216_eq_coeff (cs : List GF16) (j : Nat) :
    (cs[j]!).toGF216 = (listToGF216Poly cs).coeff j := …

end spqr.encoding.polynomial

/-!
## Characteristic-2 facts in `GF216` and `GF216Poly`

The lemmas below record that `GF216` has characteristic `2`, in the
forms `x + x = 0`, `-a = a`, and `a - b = a + b`. They live at the
root namespace under the `GF216` / `GF216Poly` prefix so that dot
notation is available, exactly as `BinaryPoly.neg_eq` does in
`Spqr/Math/Gf2Poly/Basic.lean`.
-/

lemma GF216.two_eq_zero : (2 : GF216) = 0 :=
  CharP.cast_eq_zero GF216 2

lemma GF216.add_self_eq_zero (x : GF216) : x + x = 0 := …

lemma GF216Poly.neg_eq (a : GF216Poly) : -a = a := …

lemma GF216Poly.sub_eq_add (a b : GF216Poly) : a - b = a + b := …
```

### 5. `Spqr/Math/Poly/Eval.lean` (~80 lines)

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Basic
import Spqr.Math.Poly.Coeff

/-!
# Polynomial evaluation bridge

## Main definitions
* `Poly.evalAt` — evaluate the mathematical interpretation of a
  `Poly` at a `GF16` point.

## Main statements
* `Poly.evalAt_zero_poly`
* `listToGF216Poly_eval`
-/

open Polynomial
open spqr.encoding.gf

namespace spqr.encoding.polynomial

noncomputable def Poly.evalAt (p : Poly) (x : GF16) : GF216 :=
  (p.toGF216Poly).eval (x.toGF216)

lemma Poly.evalAt_zero_poly (p : Poly) (x : GF16)
    (h : p.coefficients.length = 0) : p.evalAt x = 0 := …

lemma listToGF216Poly_eval (cs : List GF16) (a : GF216) :
    (listToGF216Poly cs).eval a =
      ∑ i : Fin cs.length, (cs.get i).toGF216 * a ^ i.val := …

end spqr.encoding.polynomial
```

### 6. `Spqr/Math/Poly/LinearFactors.lean` (~200 lines)

Same skeleton (header → imports → module docstring → `open Polynomial`
→ `namespace spqr.encoding.polynomial`) carrying the
`prodLinearFactors` definition, its `_base` / `_step` / `_snoc` /
`_eval_root` / `_split_at` / `_eq_factor_mul_basis` /
`natDegree_…_le` / `_coeff_eq_zero_high` lemmas, including the
`private lemma prodLinearFactors_snoc_aux` (the `private` modifier is
kept, matching `Gf2Poly/Basic.lean`'s use of `private`).

### 7. `Spqr/Math/Poly/Lagrange.lean` (~190 lines)

`namespace spqr.encoding.polynomial` containing `lagrangeDenomProd`,
`lagrangeScaleGF216`, `lagrangeBasisPoly`, `lagrangeInterpolantSum`,
and their lemmas.

### 8. `Spqr/Math/Poly/Horner.lean` (~140 lines)

`namespace spqr.encoding.polynomial` containing `hornerAccum` and its
lemmas.

### 9. `Spqr/Math/Poly/ExpectedTrailing.lean` (~110 lines)

`namespace spqr.encoding.polynomial` containing `expectedTrailingPoly`
and its three lemmas (`_zero`, `_succ`, `_coeff_eq_zero`,
`_eq_prodLinearFactors`).

### 10. `Spqr/Math/Poly/Identities.lean` (~80 lines)

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Coeff
import Spqr.Math.Poly.CharTwo

/-!
# Miscellaneous polynomial identities and `Inhabited` instances
-/

open Polynomial

namespace spqr.encoding.polynomial

/-! ## Advanced polynomial identity helpers -/

lemma coeff_zero_of_X_mul_identity
    (p : GF216Poly) (a s : GF216) (P : GF216Poly) … : … := …

/-! ## List/Finset sum bridge -/

lemma list_map_sum_eq_finset_sum {α β : Type} [AddCommMonoid β]
    (l : List α) (f : α → β) : … := …

/-! ## Remaining `Inhabited` instance -/

instance : Inhabited Poly :=
  ⟨{ coefficients := alloc.vec.Vec.new _ }⟩

end spqr.encoding.polynomial
```

> **Cleanup.** The current file has two `Inhabited Pt` instances
> (lines 96 and 974). We keep the first (`Basic.lean`) — which gives
> the explicit `⟨0#u16, 0#u16⟩` value — and drop the duplicate from
> `Identities.lean`.

---

## Summary of namespace placement

| Declaration kind                                  | Namespace                                      |
|---------------------------------------------------|------------------------------------------------|
| `abbrev GF216Poly`                                | root                                           |
| `listToGF216Poly`, `Poly.toGF216Poly`, `Poly.evalAt`, `prodLinearFactors`, `lagrange*`, `hornerAccum`, `expectedTrailingPoly`, `coeff_zero_of_X_mul_identity`, `list_map_sum_eq_finset_sum`, `instance Inhabited Pt`, `instance Inhabited Poly` | `spqr.encoding.polynomial` |
| `GF16.toGF216_zero_val`, `GF16.toGF216_one_val`   | `spqr.encoding.gf`                             |
| `GF216.two_eq_zero`, `GF216.add_self_eq_zero`     | root, under the `GF216` prefix                 |
| `GF216Poly.neg_eq`, `GF216Poly.sub_eq_add`        | root, under the `GF216Poly` prefix             |

This placement is a direct generalization of `Gf2Poly/Basic.lean`:
- bridge functions inside the project's `spqr.*` namespace,
- characteristic-2 lemmas at the root under the type prefix.

---

## Line-count summary

| File                                                  | Approx. lines |
|-------------------------------------------------------|--------------:|
| `Spqr/Math/Poly.lean` (shim)                          |        ~40    |
| `Spqr/Math/Poly/Basic/Defs.lean`                      |       ~120    |
| `Spqr/Math/Poly/Basic/Zero.lean`                      |        ~80    |
| `Spqr/Math/Poly/Coeff/Basic.lean`                     |       ~120    |
| `Spqr/Math/Poly/Coeff/ListOps.lean`                   |       ~120    |
| `Spqr/Math/Poly/CharTwo/Basic.lean`                   |        ~70    |
| `Spqr/Math/Poly/CharTwo/ToGF216.lean`                 |        ~80    |
| `Spqr/Math/Poly/Eval.lean`                            |        ~80    |
| `Spqr/Math/Poly/LinearFactors/Basic.lean`             |       ~120    |
| `Spqr/Math/Poly/LinearFactors/Degree.lean`            |       ~120    |
| `Spqr/Math/Poly/Lagrange/DenomProd.lean`              |        ~90    |
| `Spqr/Math/Poly/Lagrange/BasisPoly.lean`              |        ~70    |
| `Spqr/Math/Poly/Lagrange/InterpolantSum.lean`         |        ~70    |
| `Spqr/Math/Poly/Horner/Defs.lean`                     |        ~80    |
| `Spqr/Math/Poly/Horner/Eval.lean`                     |        ~80    |
| `Spqr/Math/Poly/ExpectedTrailing/Defs.lean`           |        ~60    |
| `Spqr/Math/Poly/ExpectedTrailing/Basic.lean`          |        ~80    |
| `Spqr/Math/Poly/Identities/Basic.lean`                |        ~80    |
| **Total**                                             |     **~1560** |


The increase over the current 982 lines is per-file overhead
(header, imports, module docstring, `namespace` blocks, section
markers, blank lines).

---

## Migration steps

1. Create the nine new files under `Spqr/Math/Poly/`. Each file
   uses the `Gf2Poly/Basic.lean`-style header, module docstring,
   minimal `open` block, and namespace placement described above.
2. Replace `Spqr/Math/Poly.lean` with the re-export shim.
3. Remove the duplicate `Inhabited Pt` instance.
4. Run `lake build Spqr`. The public API is unchanged, so no other
   file should need editing.
5. Optional: update `doc/fields/Plan_poly` /
   `Plan_poly_requirements.md` to reflect the new file layout.

---

## Risks and non-goals

* **Non-goal.** We are *not* changing any definitions, lemma
  statements, or proof terms. This is a pure file-level
  reorganization aligned with the `Gf2Poly/Basic.lean` style.
* **Risk: import cycles.** The dependency DAG above is acyclic by
  construction.
* **Risk: namespace placement.** Every sub-file must open/close
  exactly the namespaces listed in the "Summary of namespace
  placement" table so that the existing fully-qualified names
  (`spqr.encoding.polynomial.listToGF216Poly`, `GF216Poly.neg_eq`,
  …) are preserved bit-for-bit.
* **Risk: `open` directives.** Each new file should open only what
  it needs (`open Polynomial` is always required; `open Aeneas
  Aeneas.Std Result` only inside files that touch the
  Aeneas-extracted `Poly`/`Pt` types).
