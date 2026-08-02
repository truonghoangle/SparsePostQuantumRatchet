# Requirements for `doc/fields/Plan_encoding`

This document consolidates all requirements for creating the
`doc/fields/Plan_encoding` verification plan, as discussed and refined
during the review process. It is the encoding-layer counterpart of
[`Plan_poly_requirements.md`](./Plan_poly_requirements.md) and the
information below is grounded in the actual contents of the Lean
specification tree at
[`Spqr/Specs/Encoding/Encoder/`](../../Spqr/Specs/Encoding/Encoder/)
and
[`Spqr/Specs/Encoding/EncodingError/`](../../Spqr/Specs/Encoding/EncodingError/).

---

## Governing Document

All work must follow the rules and requirements defined in:

- [`doc/WORKFLOW_AND_PR_GUIDE.md`](../WORKFLOW_AND_PR_GUIDE.md)

---

## Source of Truth for Functions and Constants

All statistics and analyses must be based **exclusively** on the
functions and constants listed in:

- [`doc/truong/encoding.txt`](../truong/encoding.txt)

Functions that do not appear in `encoding.txt` must **not** be
analysed or included in the plan (e.g. `Clone`, `Debug`, marker
traits, auto-derived helpers).

Note: `encoding.txt` lists the trait definitions `Encoder` and
`Decoder`, the trait method names, the `Option<T>` blanket
implementations of both traits, the `From<PolynomialError>` conversion,
and the types `EncodingError` and `Chunk`. Trait definitions and type
definitions are kept in scope but are handled in Section 2 as
structural items (no standalone verification target).

---

## Content Requirements

The file `doc/fields/Plan_encoding` must be titled **TODO** and
contain the following sections:

### Section 0: Structural Overview — Statistics and Analysis

Provide statistics and analysis of the encoding layer as defined in:

- [`src/encoding.rs`](../../src/encoding.rs) — the Rust source defining
  the `Encoder` and `Decoder` traits, the `EncodingError` enum, the
  `Chunk` struct, and the generic `Option<T>` blanket implementations.
- [`Spqr/Specs/Encoding/Encoder/NextChunk.lean`](../../Spqr/Specs/Encoding/Encoder/NextChunk.lean)
  — spec for `{impl Encoder for Option<T>}::next_chunk`.
- [`Spqr/Specs/Encoding/EncodingError/From.lean`](../../Spqr/Specs/Encoding/EncodingError/From.lean)
  — spec for `{impl From<PolynomialError> for EncodingError}::from`.

This includes: core definitions (`EncodingError`, `Chunk`, `Encoder`,
`Decoder`), the generic `Option<T>` lifting pattern used throughout
the blanket implementations (take / unwrap / delegate / re-wrap),
verified lemmas/theorems, any `sorry` instances, and a summary
statistics table.

The encoding layer is a **thin structural adapter**: it defines the
`Encoder` / `Decoder` trait interface, provides a blanket
`Option<T>` lifting for both traits (using the take/unwrap/delegate
pattern to work around hax limitations with mutable references), and
converts `PolynomialError` into `EncodingError`. No new mathematical
content is introduced at this layer; all substantive logic lives in
the polynomial and GF sub-modules.

### Section 1: Combined Function and Constant Inventory

List every function and constant from `encoding.txt`, showing how
each combines with the corresponding functions in:

- [`SrcTranslated/Funs.lean`](../../SrcTranslated/Funs.lean) — Lean 4 / Aeneas extraction
- [`src/encoding.rs`](../../src/encoding.rs) — Rust source
- [`Spqr/Specs/Encoding/Encoder/`](../../Spqr/Specs/Encoding/Encoder/) and
  [`Spqr/Specs/Encoding/EncodingError/`](../../Spqr/Specs/Encoding/EncodingError/) — Lean spec files

Each entry must include its Lean name, spec file location (if any),
and verification status. The current spec tree contains:

- **`EncodingError`** —
  `EncodingError/From.lean` (the `From<PolynomialError>` conversion).
- **`Encoder` blanket impl** —
  `Encoder/NextChunk.lean` (the `Option<T>` lifting of `next_chunk`).

The functions from `encoding.txt` are:

| # | Rust Qualified Name | Category |
|---|---------------------|----------|
| 1 | `{impl From<polynomial::PolynomialError> for EncodingError}::from` | Error conversion |
| 2 | `{impl Encoder for Option<T>}::encode_bytes` | Trait blanket impl |
| 3 | `{impl Encoder for Option<T>}::next_chunk` | Trait blanket impl |
| 4 | `{impl Decoder for Option<T>}::new` | Trait blanket impl |
| 5 | `{impl Decoder for Option<T>}::add_chunk` | Trait blanket impl |
| 6 | `{impl Decoder for Option<T>}::decoded_message` | Trait blanket impl |

### Section 2: Skipped Functions with Explanations

Identify which functions from `encoding.txt` will be **skipped**
(not verified) and provide a clear explanation for each, including:

- **Trait definitions (no executable body).** The `Encoder` and
  `Decoder` traits define an interface only; verification targets are
  their concrete implementations, not the trait declaration itself.
- **Type definitions (structural only).** `EncodingError` and `Chunk`
  are plain enum/struct definitions with no logic to verify.
- **Trait method declarations (signatures only).**
  `Encoder::encode_bytes`, `Encoder::next_chunk`, `Decoder::new`,
  `Decoder::add_chunk`, `Decoder::decoded_message` are abstract
  signatures; verification applies to the concrete blanket impls.
- **Deferred functions** (no spec file currently exists). Functions
  observed in `encoding.txt` but without a corresponding spec file:
  - `{impl Encoder for Option<T>}::encode_bytes`
  - `{impl Decoder for Option<T>}::new`
  - `{impl Decoder for Option<T>}::add_chunk`
  - `{impl Decoder for Option<T>}::decoded_message`

All unverified functions from `encoding.txt` must be included in
this section.

### Section 3: Function Descriptions

Provide natural-language descriptions of all functions and constants
from `encoding.txt`.

The key pattern shared by all `Option<T>` blanket implementations is
the **take / unwrap / delegate / re-wrap** idiom necessitated by hax's
inability to handle mutable references returned by `Option::take`:

1. `core.option.Option.take self` — pure decomposition.
2. `core.option.Option.unwrap` — partial projection (requires `isSome`).
3. Delegation to the inner `T`-level trait method.
4. Re-injection into `Some`.

### Section 4: Dependency-Ordered Verification Table

Provide a table listing **all** functions and constants from
`encoding.txt` (both verified and unverified) in dependency order,
with the following rule:

> **If verifying function A requires first completing the verification
> of function B, then function B must appear before function A in the
> table.**

The table must include all unverified/skipped functions with their
skip status noted. Representative dependency chains visible in the
spec tree that must be respected:

- `{impl From<PolynomialError> for EncodingError}::from` — standalone,
  no encoding-layer dependencies.
- `{impl Encoder for Option<T>}::encode_bytes` ←
  inner `T::encode_bytes` (defined at the polynomial layer).
- `{impl Encoder for Option<T>}::next_chunk` ←
  inner `T::next_chunk` (defined at the polynomial layer).
- `{impl Decoder for Option<T>}::new` ←
  inner `T::new` (defined at the polynomial layer).
- `{impl Decoder for Option<T>}::add_chunk` ←
  inner `T::add_chunk` (defined at the polynomial layer).
- `{impl Decoder for Option<T>}::decoded_message` ←
  inner `T::decoded_message` (defined at the polynomial layer).

All `Option<T>` blanket impl methods are structurally independent of
each other but each depends on its corresponding inner `T`-level
trait method from the polynomial layer.

---

## Source Code Modification Links

All source code modifications must have links to:

- The functions to be verified in [`aeneas-config.yml`](../../aeneas-config.yml)
- Or proof of fraud (`sorry`) must be clearly stated and demonstrated

---

## Key Constraints

1. **Only `encoding.txt` functions**: Do not include functions
   outside this list (no `clone`, `debug`, marker traits, etc.).

2. **`sorry` transparency**: Every `sorry` in the codebase that could
   affect the encoding-layer verification must be identified,
   located, and explained — both in `SrcTranslated/Funs.lean`
   (extracted Aeneas definitions) and in every spec file under
   [`Spqr/Specs/Encoding/Encoder/`](../../Spqr/Specs/Encoding/Encoder/)
   and
   [`Spqr/Specs/Encoding/EncodingError/`](../../Spqr/Specs/Encoding/EncodingError/).

3. **Axioms**: Any axioms used (e.g. for opaque hax assumptions such
   as the `hax_lib::fstar!` calls in the `Option<T>` blanket
   implementations that assume inner preconditions hold) must be
   documented with justification.

4. **Dependency ordering**: The table must enforce strict dependency
   ordering — no function may appear before its prerequisites. In
   particular the chains listed in Section 4 above must be preserved.
