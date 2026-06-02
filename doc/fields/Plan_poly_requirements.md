# Requirements for `doc/fields/Plan_poly`

This document consolidates all requirements for creating the
`doc/fields/Plan_poly` verification plan, as discussed and refined
during the review process. It is the polynomial-layer counterpart of
[`Plan_gf_requirements.md`](./Plan_gf_requirements.md) and the
information below is grounded in the actual contents of the Lean
specification tree at
[`Spqr/Specs/Encoding/Polynomial/`](../../Spqr/Specs/Encoding/Polynomial/)
and the mathematical foundations at
[`Spqr/Math/Poly.lean`](../../Spqr/Math/Poly.lean) (with helpers in
[`Spqr/Math/Poly/`](../../Spqr/Math/Poly/)).

---

## Governing Document

All work must follow the rules and requirements defined in:

- [`doc/WORKFLOW_AND_PR_GUIDE.md`](../WORKFLOW_AND_PR_GUIDE.md)

---

## Source of Truth for Functions and Constants

All statistics and analyses must be based **exclusively** on the
functions and constants listed in:

- [`doc/truong/poly_functions.txt`](../truong/poly_functions.txt)

Functions that do not appear in `poly_functions.txt` must **not** be
analysed or included in the plan (e.g. `Clone`, `Debug`, marker
traits, auto-derived helpers).

Note: `poly_functions.txt` does list the trait impl methods
`{impl Ord for Pt}::cmp`, `{impl PartialOrd for Pt}::partial_cmp`, and
`{impl PartialEq for Pt}::eq`. These are kept in scope but must be
handled in Section 2 as trait-delegation wrappers (no new logic).

---

## Content Requirements

The file `doc/fields/Plan_poly` must be titled **TODO** and contain the
following sections:

### Section 0: Mathematical Foundations — Statistics and Analysis

Provide statistics and analysis of the basic mathematical knowledge
required for the verification, as defined in:

- [`Spqr/Math/Poly.lean`](../../Spqr/Math/Poly.lean) — top-level bridge
  module (`GF216Poly`, `listToGF216Poly`, `Poly.toGF216Poly`,
  `Poly.evalAt`, Lagrange interpolation support, Horner scheme,
  expected trailing polynomial, etc.)
- [`Spqr/Math/Poly/Aeneas.lean`](../../Spqr/Math/Poly/Aeneas.lean)
- [`Spqr/Math/Poly/General.lean`](../../Spqr/Math/Poly/General.lean)
- [`Spqr/Math/Poly/Mathlib.lean`](../../Spqr/Math/Poly/Mathlib.lean)
- [`Spqr/Math/Poly/ModByMonic.lean`](../../Spqr/Math/Poly/ModByMonic.lean)

This includes: core definitions (`GF216Poly`, `listToGF216Poly`,
`Poly.toGF216Poly`, `Poly.evalAt`, `prodLinearFactors`,
`lagrangeDenomProd`, `lagrangeScaleGF216`, `lagrangeBasisPoly`,
`lagrangeInterpolantSum`, `hornerAccum`, `expectedTrailingPoly`),
verified lemmas/theorems, any `sorry` instances in the math
foundations, dependency mapping from spec files (e.g.
`Poly/ComputeAt.lean` ↔ `hornerAccum_zero_eq_eval`,
`Poly/LagrangeInterpolatePrepare.lean` ↔
`expectedTrailingPoly_eq_prodLinearFactors`,
`Poly/MultXdiffAssignTrailing.lean` ↔ `prodLinearFactors_snoc` /
`coeff_zero_of_X_mul_identity`) to math lemmas, and a summary
statistics table.

### Section 1: Combined Function and Constant Inventory

List every function and constant from `poly_functions.txt`, showing how
each combines with the corresponding functions in:

- [`Spqr/Code/Funs.lean`](../../Spqr/Code/Funs.lean) — Lean 4 / Aeneas extraction
- [`src/encoding/polynomial.rs`](../../src/encoding/polynomial.rs) — Rust source
- [`Spqr/Specs/Encoding/Polynomial/`](../../Spqr/Specs/Encoding/Polynomial/) — Lean spec files

Each entry must include its Lean name, spec file location (if any),
and verification status. The current spec tree contains:

- Constants — `CHUNK_SIZE.lean`, `NUM_POLYS.lean`,
  `MAX_STORED_POLYNOMIAL_DEGREE_V1.lean`,
  `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1.lean`,
  `COMPLETE_POINTS_POLYS_{1,3,5,30,34,36}.lean`,
  `PolyConstN/ZEROS.lean`.
- Free functions — `ConstPolysToPolys.lean` (+ subdirectory
  `ConstPolysToPolys/{CallMut,CallOne,SliceIterMapCollect}.lean`),
  `LagrangePolysForCompletePoints.lean`.
- `Pt` — `Pt/Serialize.lean`, `Pt/Deserialize.lean`.
- `Point` — `Point/Clone.lean` (delegation wrapper; not in
  `poly_functions.txt`, listed only for completeness in Section 2).
- `Poly` — `Poly/{Zero, AddAssign, MultAssign, ComputeAt, LagrangeSum,
  LagrangeInterpolate, LagrangeInterpolatePrepare,
  LagrangeInterpolateComplete, LagrangeInterpolatePt,
  MultXdiffAssignTrailing, FromCompletePoints,
  FromCompletePointsLoop0, FromCompletePointsLoopBody0, Serialize,
  SerializeLoop0, SerializeLoopBody, Deserialize, DeserializeLoop0,
  DeserializeLoopBody0, Clone, Eq, VecDeref}.lean`.
- `PolyConst<N>` — `PolyConstN/{LagrangeInterpolatePt, Mult,
  MultLoop0, MultLoopBody0, MultXdiff, MultXdiffLoop0,
  MultXdiffLoop1, MultXdiffLoopBody0, MultXdiffLoopBody1,
  ToPoly}.lean`.
- `PolyEncoder` — `PolyEncoder/{GetEncoderState, IntoPb, IntoPbLoop0,
  IntoPbLoop1, IntoPbLoop2, IntoPbLoopBody0, IntoPbLoopBody1,
  IntoPbLoopBody2, FromPb, FromPbLoop0, FromPbLoop1, FromPbLoop2,
  FromPbLoopBody0, FromPbLoopBody1, FromPbLoopBody2,
  PointAtLoopBody0}.lean`, plus
  `PolyEncoder/PointAt/{CallMut, CallOne, SliceIterEnumMapCollect}.lean`.

### Section 2: Skipped Functions with Explanations

Identify which functions from `poly_functions.txt` will be **skipped**
(not verified) and provide a clear explanation for each, including:

- **Trait instance delegation wrappers (no new logic).** Examples
  observed in the current spec tree:
  `{impl Ord for Pt}::cmp`, `{impl PartialOrd for Pt}::partial_cmp`,
  `{impl PartialEq for Pt}::eq`, and Aeneas-side clone wrappers under
  `Point/Clone.lean`, `Poly/Clone.lean`, `Poly/Eq.lean`,
  `Poly/VecDeref.lean`.
- **Hardware-accelerated functions (not extracted by Aeneas).** Any
  `polynomial.rs` entries gated behind SIMD / unaccelerated cfgs.
- **Test functions (`#[cfg(test)]`, not extracted).** All entries
  under the `# Test functions (mod test)` header of
  `poly_functions.txt`, plus
  `PolyEncoder::{into_pb_test, from_pb_test}` and
  `PolyDecoder::{into_pb_test, from_pb_test}`.
- **Deferred functions** (no spec file currently exists). Examples
  observed by comparing `poly_functions.txt` against the spec tree:
  - `PolyEncoder::encode_bytes_base`
  - `PolyEncoder::chunk_at`
  - `{impl Encoder for PolyEncoder}::encode_bytes`
  - `{impl Encoder for PolyEncoder}::next_chunk`
  - All `PolyDecoder` inherent methods (`get_pts_needed`,
    `necessary_points`, `new_with_poly_count`, `into_pb`, `from_pb`)
  - All `{impl Decoder for PolyDecoder}` methods (`new`, `add_chunk`,
    `decoded_message`)

All unverified functions from `poly_functions.txt` must be included in
this section.

### Section 3: Function Descriptions

Provide natural-language descriptions of all functions and constants
from `poly_functions.txt`.

### Section 4: Dependency-Ordered Verification Table

Provide a table listing **all** functions and constants from
`poly_functions.txt` (both verified and unverified) in dependency order,
with the following rule:

> **If verifying function A requires first completing the verification
> of function B, then function B must appear before function A in the
> table.**

The table must include all unverified/skipped functions with their
skip status noted. Representative dependency chains visible in the
spec tree that must be respected:

- `Poly::compute_at`  ←  `hornerAccum`-family lemmas in
  `Spqr/Math/Poly.lean`.
- `Poly::lagrange_sum`  ←  `Poly::compute_at`.
- `Poly::mult_xdiff_assign_trailing`  ←  `prodLinearFactors_snoc`,
  `coeff_zero_of_X_mul_identity`.
- `Poly::lagrange_interpolate_prepare`  ←
  `Poly::mult_xdiff_assign_trailing`,
  `expectedTrailingPoly_eq_prodLinearFactors`.
- `Poly::lagrange_interpolate_pt`  ←
  `Poly::lagrange_interpolate_prepare`, `Poly::lagrange_sum`.
- `Poly::lagrange_interpolate_complete`  ←
  `Poly::lagrange_interpolate_pt`.
- `Poly::lagrange_interpolate`  ←
  `Poly::lagrange_interpolate_complete`.
- `Poly::from_complete_points`  ←  `Poly::lagrange_interpolate`,
  `lagrange_polys_for_complete_points`, `const_polys_to_polys`.
- `Poly::serialize` / `Poly::deserialize`  ←  `Pt::serialize` /
  `Pt::deserialize`.
- `PolyEncoder::point_at`  ←  `Poly::compute_at`.
- `PolyEncoder::into_pb` / `PolyEncoder::from_pb`  ←
  `PolyEncoder::get_encoder_state`, `Poly::serialize` /
  `Poly::deserialize`.

---

## Source Code Modification Links

All source code modifications must have links to:

- The functions to be verified in [`aeneas-config.yml`](../../aeneas-config.yml)
- Or proof of fraud (`sorry`) must be clearly stated and demonstrated

---

## Key Constraints

1. **Only `poly_functions.txt` functions**: Do not include functions
   outside this list (no `clone`, `debug`, marker traits, etc., apart
   from the `Pt` trait impls explicitly listed above).

2. **`sorry` transparency**: Every `sorry` in the codebase that could
   affect the polynomial-layer verification must be identified,
   located, and explained — both in `Spqr/Code/Funs.lean` (extracted
   Aeneas definitions) and in `Spqr/Math/Poly.lean` together with the
   files under `Spqr/Math/Poly/`
   (`Aeneas.lean`, `General.lean`, `Mathlib.lean`, `ModByMonic.lean`),
   as well as in every spec file under
   [`Spqr/Specs/Encoding/Polynomial/`](../../Spqr/Specs/Encoding/Polynomial/).

3. **Axioms**: Any axioms used (e.g. for opaque iterator functions
   such as those underlying `ConstPolysToPolys/SliceIterMapCollect.lean`
   or `PolyEncoder/PointAt/SliceIterEnumMapCollect.lean`) must be
   documented with justification.

4. **Dependency ordering**: The table must enforce strict dependency
   ordering — no function may appear before its prerequisites. In
   particular the chains listed in Section 4 above must be preserved.
