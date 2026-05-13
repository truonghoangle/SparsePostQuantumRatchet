# Requirements for `doc/fields/Plan_gf`

This document consolidates all requirements for creating the
`doc/fields/Plan_gf` verification plan, as discussed and refined
during the review process.

---

## Governing Document

All work must follow the rules and requirements defined in:

- [`doc/WORKFLOW_AND_PR_GUIDE.md`](../WORKFLOW_AND_PR_GUIDE.md)

---

## Source of Truth for Functions and Constants

All statistics and analyses must be based **exclusively** on the
functions and constants listed in:

- [`doc/truong/gf_functions.txt`](../truong/gf_functions.txt)

Functions that do not appear in `gf_functions.txt` must **not** be
analysed or included in the plan (e.g. `GF16::eq`, `Clone`, `Debug`,
marker traits).

---

## Content Requirements

The file `doc/fields/Plan_gf` must be titled **TODO** and contain the
following sections:

### Section 0: Mathematical Foundations — Statistics and Analysis

Provide statistics and analysis of the basic mathematical knowledge
required for the verification, as defined in:

- [`Spqr/Math/Gf.lean`](../../Spqr/Math/Gf.lean)

This includes: core definitions, verified lemmas/theorems, any `sorry`
instances in the math foundations, dependency mapping from spec files
to math lemmas, and a summary statistics table.

### Section 1: Combined Function and Constant Inventory

List every function and constant from `gf_functions.txt`, showing how
each combines with the corresponding functions in:

- [`Spqr/Code/Funs.lean`](../../Spqr/Code/Funs.lean) — Lean 4 / Aeneas extraction
- [`src/encoding/gf.rs`](../../src/encoding/gf.rs) — Rust source

Each entry must include its Lean name, spec file location (if any),
and verification status.

### Section 2: Skipped Functions with Explanations

Identify which functions from `gf_functions.txt` will be **skipped**
(not verified) and provide a clear explanation for each, including:

- Trait instance delegation wrappers (no new logic)
- Hardware-accelerated functions (not extracted by Aeneas)
- Test functions (`#[cfg(test)]`, not extracted)
- Deferred functions (e.g. `parallel_mult`)

All unverified functions from `gf_functions.txt` must be included in
this section.

### Section 3: Function Descriptions

Provide natural-language descriptions of all functions and constants
from `gf_functions.txt`.

### Section 4: Dependency-Ordered Verification Table

Provide a table listing **all** functions and constants from
`gf_functions.txt` (both verified and unverified) in dependency order,
with the following rule:

> **If verifying function A requires first completing the verification
> of function B, then function B must appear before function A in the
> table.**

The table must include all unverified/skipped functions with their
skip status noted.

---

## Source Code Modification Links

All source code modifications must have links to:

- The functions to be verified in [`aeneas-config.yml`](../../aeneas-config.yml)
- Or proof of fraud (`sorry`) must be clearly stated and demonstrated

---

## Key Constraints

1. **Only `gf_functions.txt` functions**: Do not include functions
   outside this list (no `eq`, `clone`, `debug`, marker traits, etc.).

2. **`sorry` transparency**: Every `sorry` in the codebase that could
   affect the GF(2¹⁶) verification must be identified, located, and
   explained — both in `Spqr/Code/Funs.lean` and in
   `Spqr/Math/Gf.lean`.

3. **Axioms**: Any axioms used (e.g. for opaque iterator functions)
   must be documented with justification.

4. **Dependency ordering**: The table must enforce strict dependency
   ordering — no function may appear before its prerequisites.
