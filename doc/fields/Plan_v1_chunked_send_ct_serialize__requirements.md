# Requirements for `doc/fields/Plan_v1_chunked_send_ct_serialize`

This document consolidates all requirements for creating the
`doc/fields/Plan_v1_chunked_send_ct_serialize` verification plan, as
discussed and refined during the review process. It is the
chunked-send-CT serialization-layer counterpart of
[`Plan_poly_requirements.md`](./Plan_poly_requirements.md) and the
information below is grounded in the actual contents of the Lean
specification tree at
[`Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/`](../../Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/),
the Aeneas-extracted definitions at
[`SrcTranslated/Funs.lean`](../../SrcTranslated/Funs.lean), and the
Rust source at
[`src/v1/chunked/send_ct/serialize.rs`](../../src/v1/chunked/send_ct/serialize.rs).

---

## Governing Document

All work must follow the rules and requirements defined in:

- [`doc/WORKFLOW_AND_PR_GUIDE.md`](../WORKFLOW_AND_PR_GUIDE.md)

---

## Source of Truth for Functions and Constants

All statistics and analyses must be based **exclusively** on the
functions listed in:

- [`doc/truong/v1_chunked_send_ct_serialize_functions.txt`](../truong/v1_chunked_send_ct_serialize_functions.txt)

Functions that do not appear in
`v1_chunked_send_ct_serialize_functions.txt` must **not** be analysed
or included in the plan (e.g. `Clone`, `Debug`, `Default`, `Eq`,
marker traits, auto-derived helpers, prost `Message` impls).

Note: `v1_chunked_send_ct_serialize_functions.txt` lists exactly 12
functions — an `into_pb` / `from_pb` pair for each of the six
chunked send-CT state structs: `NoHeaderReceived`,
`HeaderReceived`, `Ct1Sampled`, `EkReceivedCt1Sampled`,
`Ct1Acknowledged`, and `Ct2Sampled`.

---

## Content Requirements

The file `doc/fields/Plan_v1_chunked_send_ct_serialize` must be titled
**TODO** and contain the following sections:

### Section 0: Mathematical Foundations — Statistics and Analysis

This module has **no mathematical foundations**. All functions are
pure protobuf serialization / deserialization wrappers that delegate to
sub-state `into_pb` / `from_pb` methods. There are no GF₂¹⁶
polynomials, no Lagrange interpolation, and no Horner-scheme
computations involved.

Provide a brief statement confirming this and note that the only
"foundations" required are:

- The proto-generated Lean structures at
  [`SrcTranslated/Types.lean`](../../SrcTranslated/Types.lean)
  (e.g. `proto.pq_ratchet.v1_state.chunked.NoHeaderReceived`,
  `proto.pq_ratchet.v1_state.chunked.HeaderReceived`, etc.).
- The unchunked send-CT state types at
  `v1.unchunked.send_ct.{NoHeaderReceived, HeaderReceived,
  Ct1Sent, Ct1SentEkReceived, Ct2Sent}`.
- The polynomial encoder / decoder types
  `encoding.polynomial.PolyEncoder` and
  `encoding.polynomial.PolyDecoder`.
- Any `sorry` instances in the proto-level Clone specs under
  [`Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/`](../../Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/)
  and in
  [`SrcTranslated/Funs.lean`](../../SrcTranslated/Funs.lean) that
  could affect the serialization-layer verification must be
  identified and reported.

### Section 1: Combined Function Inventory

List every function from
`v1_chunked_send_ct_serialize_functions.txt`, showing how each
combines with the corresponding definitions in:

- [`SrcTranslated/Funs.lean`](../../SrcTranslated/Funs.lean) — Lean 4 / Aeneas extraction
- [`src/v1/chunked/send_ct/serialize.rs`](../../src/v1/chunked/send_ct/serialize.rs) — Rust source
- [`Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/`](../../Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/) — Lean spec files (if any)

Each entry must include its Lean name, spec file location (if any),
and verification status. The current spec tree contains **only
Clone specs** for the six structs — no `into_pb` / `from_pb` spec
files exist yet. The 12 functions, grouped by struct, are:

- **`NoHeaderReceived`** —
  `v1.chunked.send_ct.serialize.NoHeaderReceived.into_pb`,
  `v1.chunked.send_ct.serialize.NoHeaderReceived.from_pb`.
  Rust source lines 11–35. Lean extraction in `SrcTranslated/Funs.lean`.
  Delegates to `unchunked::send_ct::NoHeaderReceived::{into_pb, from_pb}`
  and `polynomial::PolyDecoder::{into_pb, from_pb}`.

- **`HeaderReceived`** —
  `v1.chunked.send_ct.serialize.HeaderReceived.into_pb`,
  `v1.chunked.send_ct.serialize.HeaderReceived.from_pb`.
  Rust source lines 39–59. Lean extraction in `SrcTranslated/Funs.lean`.
  Delegates to `unchunked::send_ct::HeaderReceived::{into_pb, from_pb}`
  and `polynomial::PolyDecoder::{into_pb, from_pb}`.

- **`Ct1Sampled`** —
  `v1.chunked.send_ct.serialize.Ct1Sampled.into_pb`,
  `v1.chunked.send_ct.serialize.Ct1Sampled.from_pb`.
  Rust source lines 63–88. Lean extraction in `SrcTranslated/Funs.lean`.
  Delegates to `unchunked::send_ct::Ct1Sent::{into_pb, from_pb}`,
  `polynomial::PolyEncoder::{into_pb, from_pb}`, and
  `polynomial::PolyDecoder::{into_pb, from_pb}`.

- **`EkReceivedCt1Sampled`** —
  `v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.into_pb`,
  `v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.from_pb`.
  Rust source lines 92–107. Lean extraction in `SrcTranslated/Funs.lean`.
  Delegates to `unchunked::send_ct::Ct1SentEkReceived::{into_pb, from_pb}`
  and `polynomial::PolyEncoder::{into_pb, from_pb}`.

- **`Ct1Acknowledged`** —
  `v1.chunked.send_ct.serialize.Ct1Acknowledged.into_pb`,
  `v1.chunked.send_ct.serialize.Ct1Acknowledged.from_pb`.
  Rust source lines 111–131. Lean extraction in `SrcTranslated/Funs.lean`.
  Delegates to `unchunked::send_ct::Ct1Sent::{into_pb, from_pb}`
  and `polynomial::PolyDecoder::{into_pb, from_pb}`.

- **`Ct2Sampled`** —
  `v1.chunked.send_ct.serialize.Ct2Sampled.into_pb`,
  `v1.chunked.send_ct.serialize.Ct2Sampled.from_pb`.
  Rust source lines 135–150. Lean extraction in `SrcTranslated/Funs.lean`.
  Delegates to `unchunked::send_ct::Ct2Sent::{into_pb, from_pb}`
  and `polynomial::PolyEncoder::{into_pb, from_pb}`.

### Section 2: Skipped Functions with Explanations

Identify which functions from
`v1_chunked_send_ct_serialize_functions.txt` will be **skipped**
(not verified) and provide a clear explanation for each, including:

- **Deferred functions** (no spec file currently exists). All 12
  functions are currently deferred — no `into_pb` / `from_pb` spec
  files exist under
  `Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/`. Only Clone specs
  are present:
  - `NoHeaderReceived/Clone.lean`
  - `HeaderReceived/Clone.lean`
  - `Ct1Sampled/Clone.lean`
  - `EkReceivedCt1Sampled/Clone.lean`
  - `Ct1Acknowledged/Clone.lean`
  - `Ct2Sampled/Clone.lean`
  (listed only for completeness; these are not in
  `v1_chunked_send_ct_serialize_functions.txt`).

- **`from_pb` validation guards.** Several `from_pb` methods
  (`NoHeaderReceived`, `HeaderReceived`, `Ct1Sampled`,
  `Ct1Acknowledged`) contain `pts_needed` validation checks against
  protocol constants (`HEADER_SIZE`, `MACSIZE`,
  `ENCAPSULATION_KEY_SIZE`). These guards must be verified or
  explicitly flagged as requiring axioms over the protocol constants.

All unverified functions from
`v1_chunked_send_ct_serialize_functions.txt` must be included in this
section.

### Section 3: Function Descriptions

Provide natural-language descriptions of all functions from
`v1_chunked_send_ct_serialize_functions.txt`. Each `into_pb` /
`from_pb` pair serializes / deserializes a chunked send-CT state
struct to / from the corresponding protobuf-generated Lean structure.
The descriptions must cover:

- **`NoHeaderReceived::into_pb`** — Serializes the
  `NoHeaderReceived` state by converting the unchunked
  `NoHeaderReceived` sub-state and the `receiving_hdr`
  `PolyDecoder` into their protobuf representations.
- **`NoHeaderReceived::from_pb`** — Deserializes a
  `NoHeaderReceived` protobuf, validating that
  `receiving_hdr.pts_needed` matches
  `(HEADER_SIZE + MACSIZE) / 2`. Returns `Error::StateDecode` on
  missing fields, `Error::MsgDecode` on validation failure.
- **`HeaderReceived::into_pb`** — Serializes the `HeaderReceived`
  state by converting the unchunked `HeaderReceived` sub-state and
  the `receiving_ek` `PolyDecoder`.
- **`HeaderReceived::from_pb`** — Deserializes a `HeaderReceived`
  protobuf, validating that `receiving_ek.pts_needed` matches
  `ENCAPSULATION_KEY_SIZE / 2`. Returns `Error::StateDecode` or
  `Error::MsgDecode` on failure.
- **`Ct1Sampled::into_pb`** — Serializes the `Ct1Sampled` state by
  converting the unchunked `Ct1Sent` sub-state, the `sending_ct1`
  `PolyEncoder`, and the `receiving_ek` `PolyDecoder`.
- **`Ct1Sampled::from_pb`** — Deserializes a `Ct1Sampled` protobuf,
  validating `receiving_ek.pts_needed`. Delegates to
  `Ct1Sent::from_pb`, `PolyEncoder::from_pb`, and
  `PolyDecoder::from_pb`.
- **`EkReceivedCt1Sampled::into_pb`** — Serializes the
  `EkReceivedCt1Sampled` state by converting the unchunked
  `Ct1SentEkReceived` sub-state and the `sending_ct1`
  `PolyEncoder`.
- **`EkReceivedCt1Sampled::from_pb`** — Deserializes an
  `EkReceivedCt1Sampled` protobuf. Delegates to
  `Ct1SentEkReceived::from_pb` and `PolyEncoder::from_pb`. No
  `pts_needed` validation (no decoder field).
- **`Ct1Acknowledged::into_pb`** — Serializes the `Ct1Acknowledged`
  state by converting the unchunked `Ct1Sent` sub-state and the
  `receiving_ek` `PolyDecoder`.
- **`Ct1Acknowledged::from_pb`** — Deserializes a `Ct1Acknowledged`
  protobuf, validating `receiving_ek.pts_needed` matches
  `ENCAPSULATION_KEY_SIZE / 2`.
- **`Ct2Sampled::into_pb`** — Serializes the `Ct2Sampled` state by
  converting the unchunked `Ct2Sent` sub-state and the
  `sending_ct2` `PolyEncoder`.
- **`Ct2Sampled::from_pb`** — Deserializes a `Ct2Sampled` protobuf.
  Delegates to `Ct2Sent::from_pb` and `PolyEncoder::from_pb`. No
  `pts_needed` validation (no decoder field).

### Section 4: Dependency-Ordered Verification Table

Provide a table listing **all** functions from
`v1_chunked_send_ct_serialize_functions.txt` in dependency order,
with the following rule:

> **If verifying function A requires first completing the verification
> of function B, then function B must appear before function A in the
> table.**

The table must include all unverified/skipped functions with their
skip status noted. Representative dependency chains that must be
respected:

- `NoHeaderReceived::into_pb`  ←
  `unchunked::send_ct::NoHeaderReceived::into_pb`,
  `PolyDecoder::into_pb`.
- `NoHeaderReceived::from_pb`  ←
  `unchunked::send_ct::NoHeaderReceived::from_pb`,
  `PolyDecoder::from_pb`.
- `HeaderReceived::into_pb`  ←
  `unchunked::send_ct::HeaderReceived::into_pb`,
  `PolyDecoder::into_pb`.
- `HeaderReceived::from_pb`  ←
  `unchunked::send_ct::HeaderReceived::from_pb`,
  `PolyDecoder::from_pb`.
- `Ct1Sampled::into_pb`  ←
  `unchunked::send_ct::Ct1Sent::into_pb`,
  `PolyEncoder::into_pb`, `PolyDecoder::into_pb`.
- `Ct1Sampled::from_pb`  ←
  `unchunked::send_ct::Ct1Sent::from_pb`,
  `PolyEncoder::from_pb`, `PolyDecoder::from_pb`.
- `EkReceivedCt1Sampled::into_pb`  ←
  `unchunked::send_ct::Ct1SentEkReceived::into_pb`,
  `PolyEncoder::into_pb`.
- `EkReceivedCt1Sampled::from_pb`  ←
  `unchunked::send_ct::Ct1SentEkReceived::from_pb`,
  `PolyEncoder::from_pb`.
- `Ct1Acknowledged::into_pb`  ←
  `unchunked::send_ct::Ct1Sent::into_pb`,
  `PolyDecoder::into_pb`.
- `Ct1Acknowledged::from_pb`  ←
  `unchunked::send_ct::Ct1Sent::from_pb`,
  `PolyDecoder::from_pb`.
- `Ct2Sampled::into_pb`  ←
  `unchunked::send_ct::Ct2Sent::into_pb`,
  `PolyEncoder::into_pb`.
- `Ct2Sampled::from_pb`  ←
  `unchunked::send_ct::Ct2Sent::from_pb`,
  `PolyEncoder::from_pb`.

All `into_pb` functions are independent of each other (no cross-struct
dependencies). Likewise all `from_pb` functions are independent of
each other. The `into_pb` and `from_pb` of the same struct are
independent of each other. However, all functions depend on the
unchunked-layer and polynomial-layer `into_pb` / `from_pb` being
verified first.

A suggested verification order (grouping by external dependency
complexity):

1. **Two-field structs with PolyEncoder** (simplest — no `pts_needed`
   validation):
   `EkReceivedCt1Sampled::into_pb`, `EkReceivedCt1Sampled::from_pb`,
   `Ct2Sampled::into_pb`, `Ct2Sampled::from_pb`.
2. **Two-field structs with PolyDecoder** (adds `pts_needed`
   validation):
   `HeaderReceived::into_pb`, `HeaderReceived::from_pb`,
   `Ct1Acknowledged::into_pb`, `Ct1Acknowledged::from_pb`,
   `NoHeaderReceived::into_pb`, `NoHeaderReceived::from_pb`.
3. **Three-field struct** (both PolyEncoder and PolyDecoder):
   `Ct1Sampled::into_pb`, `Ct1Sampled::from_pb`.

---

## Source Code Modification Links

All source code modifications must have links to:

- The functions to be verified in [`aeneas-config.yml`](../../aeneas-config.yml)
- Or proof of fraud (`sorry`) must be clearly stated and demonstrated

Note: Currently `aeneas-config.yml` contains only a single reference
to `v1.chunked` (a local-variable shadowing fix for
`v1.chunked.states`). The 12 serialize functions are extracted into
`SrcTranslated/Funs.lean` under the `v1.chunked.send_ct.serialize.*`
namespace and are available for verification without additional
`aeneas-config.yml` entries.

---

## Key Constraints

1. **Only `v1_chunked_send_ct_serialize_functions.txt` functions**: Do
   not include functions outside this list (no `Clone`, `Debug`,
   `Default`, `Eq`, prost `Message` impls, or other auto-derived
   helpers).

2. **`sorry` transparency**: Every `sorry` in the codebase that could
   affect the chunked-send-CT serialization verification must be
   identified, located, and explained — both in
   `SrcTranslated/Funs.lean` (extracted Aeneas definitions) and in
   every spec file under
   [`Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/`](../../Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/),
   as well as any unchunked-layer specs under
   [`Spqr/Specs/Proto/PqRatchet/V1_state/Unchunked/`](../../Spqr/Specs/Proto/PqRatchet/V1_state/Unchunked/)
   and polynomial-layer specs under
   [`Spqr/Specs/Encoding/Polynomial/`](../../Spqr/Specs/Encoding/Polynomial/)
   that are transitive dependencies.

3. **Axioms**: Any axioms used (e.g. for opaque prost-generated
   protobuf codec functions such as `encode_raw`, `merge_field`,
   `encoded_len`, `clear`, `decode` declared in
   `SrcTranslated/FunsExternal.lean`) must be documented with
   justification.

4. **Dependency ordering**: The table must enforce strict dependency
   ordering — no function may appear before its prerequisites. In
   particular the chains listed in Section 4 above must be preserved.
   All unchunked-layer `into_pb` / `from_pb` and polynomial-layer
   `PolyEncoder::into_pb` / `PolyEncoder::from_pb` /
   `PolyDecoder::into_pb` / `PolyDecoder::from_pb` must be verified
   (or axiomatized) before the chunked-layer functions that depend on
   them.

5. **Validation guards**: The `pts_needed` checks in `from_pb`
   methods for `NoHeaderReceived`, `HeaderReceived`, `Ct1Sampled`,
   and `Ct1Acknowledged` compare against protocol constants
   (`incremental_mlkem768::HEADER_SIZE`,
   `authenticator::Authenticator::MACSIZE`,
   `incremental_mlkem768::ENCAPSULATION_KEY_SIZE`). These constants
   must either be verified or axiomatized, and the validation logic
   must be shown to correctly reject invalid protobuf state.
