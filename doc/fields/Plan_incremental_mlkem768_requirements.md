# Requirements for `doc/fields/Plan_incremental_mlkem768`

This document consolidates all requirements for creating the
`doc/fields/Plan_incremental_mlkem768` verification plan, as discussed
and refined during the review process. It is the
incremental-ML-KEM-768-layer counterpart of
[`Plan_poly_requirements.md`](./Plan_poly_requirements.md) and the
information below is grounded in the actual contents of the Lean
specification tree at
[`Spqr/Specs/IncrementalMlkem768/`](../../Spqr/Specs/IncrementalMlkem768/)
and the external-function models at
[`Spqr/Code/FunsExternal.lean`](../../Spqr/Code/FunsExternal.lean).

---

## Governing Document

All work must follow the rules and requirements defined in:

- [`doc/WORKFLOW_AND_PR_GUIDE.md`](../WORKFLOW_AND_PR_GUIDE.md)

---

## Source of Truth for Functions and Constants

All statistics and analyses must be based **exclusively** on the
functions and constants listed in:

- [`doc/truong/incremental_mlkem768_functions.txt`](../truong/incremental_mlkem768_functions.txt)

Functions that do not appear in `incremental_mlkem768_functions.txt`
must **not** be analysed or included in the plan (e.g. `Clone`,
`Debug`, marker traits, auto-derived helpers).

---

## Content Requirements

The file `doc/fields/Plan_incremental_mlkem768` must be titled **TODO**
and contain the following sections:

### Section 0: External (Opaque) Function Models — Statistics and Analysis

Provide statistics and analysis of the external (opaque) function
models from the upstream `libcrux_ml_kem` crate that underpin the
verification, as defined in:

- [`Spqr/Code/FunsExternal.lean`](../../Spqr/Code/FunsExternal.lean) —
  concrete models and axioms for the libcrux incremental ML-KEM-768 API

This includes: axiomatised types
(`libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes`),
axiomatised functions
(`libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1.len`,
`core.result.Result.is_ok`,
`incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`,
`core.option.Option.as_ref`), concrete models with spec theorems
(`Ciphertext2.len`, `pk1_len`, `pk2_len`, `encaps_state_len`,
`encapsulate1`, `encapsulate2`, `decapsulate_compressed_key`,
`validate_pk_bytes`, `KeyPairCompressedBytes.from_seed`,
`KeyPairCompressedBytes.pk1`, `KeyPairCompressedBytes.pk2`,
`KeyPairCompressedBytes.sk`), any `sorry` instances in the external
models, and a summary statistics table.

### Section 1: Combined Function and Constant Inventory

List every function and constant from
`incremental_mlkem768_functions.txt`, showing how each combines with
the corresponding functions in:

- [`Spqr/Code/Funs.lean`](../../Spqr/Code/Funs.lean) — Lean 4 / Aeneas extraction
- [`src/incremental_mlkem768.rs`](../../src/incremental_mlkem768.rs) — Rust source
- [`Spqr/Specs/IncrementalMlkem768/`](../../Spqr/Specs/IncrementalMlkem768/) — Lean spec files

Each entry must include its Lean name, spec file location (if any),
and verification status. The current spec tree contains:

- Constants — `CIPHERTEXT1_SIZE.lean`, `CIPHERTEXT2_SIZE.lean`,
  `HEADER_SIZE.lean`, `ENCAPSULATION_KEY_SIZE.lean`.
- Free functions (pub) — `EkMatchesHeader.lean`, `Generate.lean`,
  `Encaps1.lean`, `Encaps2.lean`, `Decaps.lean`.
- Free functions (private) —
  `FlipEndiannessOfEncapsulationState.lean` (+ subdirectory-style
  decomposition:
  `FlipEndiannessOfEncapsulationStateLoop0.lean`,
  `FlipEndiannessOfEncapsulationStateLoopBody0.lean`).

### Section 2: Skipped Functions with Explanations

Identify which functions from
`incremental_mlkem768_functions.txt` will be **skipped** (not
verified) and provide a clear explanation for each, including:

- **Opaque / `#[hax_lib::opaque]` functions (not extracted by
  Aeneas).** The function
  `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`
  is marked `#[hax_lib::opaque]` in Rust and is emitted as an axiom in
  the Aeneas extraction. It is *used* by `encaps2` (via a hypothesis
  `potentially_fix_state_ok`), but its internal logic (the
  endianness-checking match on `i16` chunks) is not itself verified.
  The companion function `flip_endianness_of_encapsulation_state` is
  also `#[hax_lib::opaque]` in Rust but *is* fully specified and proved
  in the spec tree (see
  `FlipEndiannessOfEncapsulationState.lean` and its loop specs).
- **Test functions (`#[cfg(test)]`, not extracted).** The entry
  `spqr::incremental_mlkem768::test::incremental_mlkem768_round_trip`
  under the `# Test functions (mod test)` header of
  `incremental_mlkem768_functions.txt`.

All unverified functions from `incremental_mlkem768_functions.txt`
must be included in this section.

### Section 3: Function Descriptions

Provide natural-language descriptions of all functions and constants
from `incremental_mlkem768_functions.txt`.

The descriptions must cover the following aspects for each entry:

- **Constants**: `CIPHERTEXT1_SIZE` (= 960, byte length of the first
  ciphertext `Ciphertext1`), `CIPHERTEXT2_SIZE` (= 128, byte length of
  the second ciphertext `Ciphertext2`), `HEADER_SIZE` (= 64, byte
  length of the header / `pk1`), `ENCAPSULATION_KEY_SIZE` (= 1152,
  byte length of the encapsulation key / `pk2`).

- **`ek_matches_header`**: validates that an encapsulation key is
  consistent with a header by calling
  `incremental::validate_pk_bytes(hdr, ek).is_ok()`. In the extracted
  model, validation always succeeds (returns `true`).

- **`generate`**: key generation — samples 64 bytes of randomness,
  derives a `KeyPairCompressedBytes` via `from_seed`, and extracts the
  three fixed-size byte arrays (`pk1`/`pk2`/`sk`) into a `Keys` record
  with byte lengths 64/1152/2400.

- **`encaps1`**: first half of incremental encapsulation — samples 32
  bytes of randomness, allocates work buffers (`state` of length 2080,
  `ss` of length 32), invokes `encapsulate1`, and returns the triple
  `(ct1, es, ss)` with byte lengths 960/2080/32.

- **`encaps2`**: second half of incremental encapsulation — applies the
  endianness workaround
  (`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`),
  converts inputs to fixed-size arrays, invokes `encapsulate2`, and
  returns `ct2` with byte length 128.

- **`decaps`**: decapsulation — converts the three input byte vectors
  (`dk`, `ct1`, `ct2`) to fixed-size arrays, invokes
  `decapsulate_compressed_key`, and returns the shared secret with byte
  length 32.

- **`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`**:
  opaque workaround for cryspen/libcrux#1275 — inspects the `error2`
  portion of the encapsulation state to detect endianness mismatch and
  returns `Some(fixed_es)` if byte-swapping was needed, or `None`
  otherwise. Axiomatised in the Aeneas extraction; its contract is
  captured as the proposition `potentially_fix_state_ok`.

- **`flip_endianness_of_encapsulation_state`**: byte-swaps each
  consecutive 16-bit word in the first `len − 32` positions of the
  encapsulation state byte vector, leaving the last 32 bytes (the
  shared-secret portion) untouched. Fully verified with a three-part
  postcondition (length preservation, byte-swap, frame/tail).

### Section 4: Dependency-Ordered Verification Table

Provide a table listing **all** functions and constants from
`incremental_mlkem768_functions.txt` (both verified and unverified) in
dependency order, with the following rule:

> **If verifying function A requires first completing the verification
> of function B, then function B must appear before function A in the
> table.**

The table must include all unverified/skipped functions with their
skip status noted. Representative dependency chains visible in the
spec tree that must be respected:

- `CIPHERTEXT1_SIZE`  ←  `Ciphertext1.len` axiom (in
  `Spqr/Code/FunsExternal.lean`).
- `CIPHERTEXT2_SIZE`  ←  `Ciphertext2.len` concrete model (in
  `Spqr/Code/FunsExternal.lean`).
- `HEADER_SIZE`  ←  `pk1_len` concrete model (in
  `Spqr/Code/FunsExternal.lean`).
- `ENCAPSULATION_KEY_SIZE`  ←  `pk2_len` concrete model (in
  `Spqr/Code/FunsExternal.lean`).
- `ek_matches_header`  ←  `validate_pk_bytes` concrete model,
  `Result.is_ok` axiom.
- `generate`  ←  `fill_bytes_ok` hypothesis,
  `KeyPairCompressedBytes.from_seed` / `.pk1` / `.pk2` / `.sk` concrete
  models.
- `flip_endianness_of_encapsulation_state`  ←
  `FlipEndiannessOfEncapsulationStateLoop0.lean`  ←
  `FlipEndiannessOfEncapsulationStateLoopBody0.lean`.
- `encaps1`  ←  `generate` (imports `Generate.lean` for
  `fill_bytes_ok`), `encapsulate1` concrete model,
  `alloc.vec.from_elem`, `Result.expect`.
- `encaps2`  ←  `potentially_fix_state_ok` hypothesis,
  `option_as_ref_id` hypothesis, `encapsulate2` concrete model,
  `Result.expect`.
- `decaps`  ←  `TryFromArrayCopySlice.try_from`,
  `TryFromSharedArraySlice.try_from`, `Result.expect`,
  `decapsulate_compressed_key` concrete model.

---

## Source Code Modification Links

All source code modifications must have links to:

- The functions to be verified in [`aeneas-config.yml`](../../aeneas-config.yml)
- Or proof of fraud (`sorry`) must be clearly stated and demonstrated

The single `aeneas-config.yml` entry relevant to this module is:

```yaml
- "spqr::incremental_mlkem768::potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275"
  # has log calls; kept opaque so encaps2 can call it
```

This entry causes the function to be emitted as an axiom in
`Spqr/Code/FunsExternal.lean` rather than being extracted into
`Spqr/Code/Funs.lean`. The companion function
`flip_endianness_of_encapsulation_state` is also
`#[hax_lib::opaque]` in the Rust source but is **not** listed in
`aeneas-config.yml`; instead it is extracted into `Funs.lean` and
fully verified.

---

## Key Constraints

1. **Only `incremental_mlkem768_functions.txt` functions**: Do not
   include functions outside this list (no `clone`, `debug`, marker
   traits, etc.).

2. **`sorry` transparency**: Every `sorry` in the codebase that could
   affect the incremental-ML-KEM-768-layer verification must be
   identified, located, and explained — both in
   `Spqr/Code/Funs.lean` (extracted Aeneas definitions), in
   `Spqr/Code/FunsExternal.lean` (external axioms and concrete
   models), and in every spec file under
   [`Spqr/Specs/IncrementalMlkem768/`](../../Spqr/Specs/IncrementalMlkem768/).
   Currently there are **zero** `sorry` instances across all spec files
   in the `IncrementalMlkem768/` tree.

3. **Axioms**: Any axioms used must be documented with justification.
   The following axioms are in scope:

   - `Ciphertext1_len_id` (in `CIPHERTEXT1_SIZE.lean`): postulates
     `Ciphertext1.len LEN = ok LEN` because the Aeneas extraction
     emits `Ciphertext1.len` as an external axiom (the upstream
     `const fn` returns the const-generic length `LEN`).
   - `Result_is_ok_Ok` (in `EkMatchesHeader.lean`): postulates
     `core.result.Result.is_ok (Ok v) = ok true` because `is_ok` is an
     external axiom in the Aeneas extraction (a generic standard-library
     method).
   - `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`
     (in `Spqr/Code/FunsExternal.lean`): the function itself is an
     axiom; its functional contract is captured as the definition
     `potentially_fix_state_ok` in `Encaps2.lean`.
   - `core.option.Option.as_ref` (in `Spqr/Code/FunsExternal.lean`):
     an axiom modelling Rust's `Option::as_ref(&self)` borrow
     conversion; its functional contract is captured as the definition
     `option_as_ref_id` in `Encaps2.lean`.
   - `KeyPairCompressedBytes.instInhabited` (in
     `Spqr/Code/FunsExternal.lean`): postulates inhabitedness for the
     opaque `KeyPairCompressedBytes` type.

4. **Dependency ordering**: The table must enforce strict dependency
   ordering — no function may appear before its prerequisites. In
   particular the chains listed in Section 4 above must be preserved.
