# TODO: Verification Plan for Chunked Send-CT Serialization Functions

## Overview

This document describes the TODO plan for verifying the functions
listed in
[`doc/truong/v1_chunked_send_ct_serialize_functions.txt`](../truong/v1_chunked_send_ct_serialize_functions.txt),
which enumerates all fully qualified function names from
`src/v1/chunked/send_ct/serialize.rs` (Rust source). These are
extracted into `SrcTranslated/Funs.lean` (Lean 4 / Aeneas extraction)
under the `v1.chunked.send_ct.serialize.*` namespace.

All extractable functions are configured via
[`aeneas-config.yml`](../../aeneas-config.yml). The 12 serialize
functions are extracted into `SrcTranslated/Funs.lean` and are
available for verification without additional `aeneas-config.yml`
entries. The only `aeneas-config.yml` reference to `v1.chunked` is a
local-variable shadowing fix for `v1.chunked.states` (issue #101).

The current Lean specification tree for the chunked V1 layer lives at
[`Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/`](../../Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/).

---

## 0. Mathematical Foundations — Statistics and Analysis

This module has **no mathematical foundations**. All 12 functions are
pure protobuf serialization / deserialization wrappers that delegate to
sub-state `into_pb` / `from_pb` methods. There are no GF(2¹⁶)
polynomials, no Lagrange interpolation, and no Horner-scheme
computations involved.

The only "foundations" required are:

- The proto-generated Lean structures at
  [`SrcTranslated/Types.lean`](../../SrcTranslated/Types.lean)
  (e.g. `proto.pq_ratchet.v1_state.chunked.NoHeaderReceived`,
  `proto.pq_ratchet.v1_state.chunked.HeaderReceived`, etc.).
- The unchunked send-CT state types at
  `v1.unchunked.send_ct.{NoHeaderReceived, HeaderReceived,
  Ct1Sent, Ct1SentEkReceived, Ct2Sent}` and their
  `into_pb` / `from_pb` methods extracted in
  `SrcTranslated/Funs.lean`.
- The polynomial encoder / decoder types
  `encoding.polynomial.PolyEncoder` and
  `encoding.polynomial.PolyDecoder`, whose `into_pb` / `from_pb`
  methods are verified in
  [`Plan_poly`](Plan_poly) (F26–F27, F38–F39 — all ✅).

### 0a. `sorry` / Axiom Inventory Affecting This Layer

#### `sorry` instances in `SrcTranslated/Funs.lean`

The following `sorry` instances in `SrcTranslated/Funs.lean` are on
the transitive dependency path of the 12 chunked-send-CT serialize
functions:

| `sorry` | Location | Effect |
|---------|----------|--------|
| `proto.pq_ratchet.v1_state.chunked.NoHeaderReceived.Insts.ProstMessageMessage` | `Funs.lean` | Prost-derived `Message` instance body for the chunked `NoHeaderReceived` protobuf struct. Not on the `into_pb`/`from_pb` verification path (these functions *construct* proto structs, they do not call `encode`/`decode`). |
| `proto.pq_ratchet.v1_state.chunked.HeaderReceived.Insts.ProstMessageMessage` | `Funs.lean` | Same — prost `Message` instance for `HeaderReceived`. |
| `proto.pq_ratchet.v1_state.chunked.Ct1Sampled.Insts.ProstMessageMessage` | `Funs.lean` | Same — prost `Message` instance for `Ct1Sampled`. |
| `proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled.Insts.ProstMessageMessage` | `Funs.lean` | Same — prost `Message` instance for `EkReceivedCt1Sampled`. |
| `proto.pq_ratchet.v1_state.chunked.Ct1Acknowledged.Insts.ProstMessageMessage` | `Funs.lean` | Same — prost `Message` instance for `Ct1Acknowledged`. |
| `proto.pq_ratchet.v1_state.chunked.Ct2Sampled.Insts.ProstMessageMessage` | `Funs.lean` | Same — prost `Message` instance for `Ct2Sampled`. |
| `proto.pq_ratchet.PolynomialEncoder.Insts.ProstMessageMessage` | `Funs.lean` | Prost `Message` for `PolynomialEncoder`. Not on path. |
| `proto.pq_ratchet.PolynomialDecoder.Insts.ProstMessageMessage` | `Funs.lean` | Prost `Message` for `PolynomialDecoder`. Not on path. |

All of these are prost-derived `Message` trait instance bodies that
Aeneas emits as `sorry` because prost's proc-macro-generated code
(wire encoding, merging, length computation) is not extracted. They
are **not** on the verification path for the `into_pb` / `from_pb`
functions, which construct protobuf struct values directly rather
than invoking `Message::encode` / `Message::decode`.

#### `sorry` instances in spec files

| File | `sorry` count |
|------|---------------|
| `Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/NoHeaderReceived/Clone.lean` | **0** |
| `Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/HeaderReceived/Clone.lean` | **0** |
| `Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/Ct1Sampled/Clone.lean` | **0** |
| `Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/EkReceivedCt1Sampled/Clone.lean` | **0** |
| `Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/Ct1Acknowledged/Clone.lean` | **0** |

The existing Clone spec files contain **0 `sorry`** instances. No
`into_pb` / `from_pb` spec files exist yet in this directory.

#### `sorry` instances in unchunked-layer specs

| Directory | `sorry` count |
|-----------|---------------|
| `Spqr/Specs/Proto/PqRatchet/V1_state/Unchunked/` (all files) | **0** |

The unchunked-layer spec tree contains only Clone specs (no
`into_pb` / `from_pb` specs), and those Clone specs are
`sorry`-free.

#### Axioms in `SrcTranslated/FunsExternal.lean`

The following axioms declared in `FunsExternal.lean` are transitively
relevant to the chunked-send-CT serialization layer:

| Axiom family | Count | Justification |
|--------------|-------|---------------|
| `proto.pq_ratchet.v1_state.chunked.*.Insts.ProstMessageMessage.{encode_raw, merge_field, encoded_len, clear, decode}` | 30 (5 × 6 structs) | Opaque prost-generated protobuf codec functions for each of the six chunked send-CT state protobuf structs. These are not invoked by the `into_pb` / `from_pb` functions (which construct struct values directly) but are present as part of the `Message` trait instance. |
| `proto.pq_ratchet.v1_state.unchunked.*.Insts.ProstMessageMessage.{encode_raw, merge_field, encoded_len, clear, decode}` | 25 (5 × 5 unchunked structs) | Same — opaque prost codec for the five unchunked send-CT state protobuf structs (`NoHeaderReceived`, `HeaderReceived`, `Ct1Sent`, `Ct1SentEkReceived`, `Ct2Sent`). |
| `sorted_vec.SortedSet.Insts.CoreCloneClone.clone` | 1 | Clone for `SortedSet` — used transitively by `PolyDecoder`. Documented in [`Plan_poly`](Plan_poly) §2h. |

### 0b. Protocol Constants Used by Validation Guards

Four `from_pb` methods (`NoHeaderReceived`, `HeaderReceived`,
`Ct1Sampled`, `Ct1Acknowledged`) contain `pts_needed` validation
checks that compare against protocol constants:

| Constant | Lean Definition | Value |
|----------|----------------|-------|
| `incremental_mlkem768.HEADER_SIZE` | `libcrux_ml_kem.mlkem768.incremental.pk1_len` | `Result Usize` (external function) |
| `authenticator.Authenticator.MACSIZE` | `32#usize` | `32` (irreducible) |
| `incremental_mlkem768.ENCAPSULATION_KEY_SIZE` | `libcrux_ml_kem.mlkem768.incremental.pk2_len` | `Result Usize` (external function) |

`HEADER_SIZE` and `ENCAPSULATION_KEY_SIZE` are defined via external
`libcrux` functions (`pk1_len`, `pk2_len`) that are axiomatized in
`SrcTranslated/FunsExternal.lean`. Verification of the `from_pb`
validation logic will require either:

1. Proving the concrete values of `pk1_len` and `pk2_len` (which
   requires axioms over the `libcrux` API), or
2. Axiomatizing the expected values of `HEADER_SIZE` and
   `ENCAPSULATION_KEY_SIZE` directly.

`MACSIZE` is a concrete constant (`32#usize`) marked `@[irreducible]`
and poses no verification difficulty.

### 0c. Statistics Summary

| Metric | Count |
|--------|-------|
| Functions in `v1_chunked_send_ct_serialize_functions.txt` | 12 |
| State structs covered | 6 |
| `into_pb` functions | 6 |
| `from_pb` functions | 6 |
| `from_pb` functions with `pts_needed` validation guards | 4 |
| `from_pb` functions without validation (no decoder field) | 2 |
| Existing spec files for `into_pb` / `from_pb` | **0** |
| Existing Clone-only spec files (not in scope) | 5 |
| `sorry` instances in chunked/unchunked spec trees | **0** |
| `sorry` instances in `Funs.lean` on the serialize path | **0** (prost `Message` `sorry`s are off-path) |
| Math foundation files required | **0** |

---

## 1. Combined Function Inventory

The following table lists every function from
`v1_chunked_send_ct_serialize_functions.txt`, together with its Lean
name in `SrcTranslated/Funs.lean`, its current spec file under
`Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/` (if any), and
verification status.

Legend: ✅ = verified (spec file present, no `sorry`), ⚠️ = spec
exists but contains `sorry`, ❌ = not yet verified (no spec file),
⏭️ = skipped (see Section 2).

### Functions: NoHeaderReceived

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F1 | `NoHeaderReceived::into_pb` | `v1.chunked.send_ct.serialize.NoHeaderReceived.into_pb` | — | ❌ |
| F2 | `NoHeaderReceived::from_pb` | `v1.chunked.send_ct.serialize.NoHeaderReceived.from_pb` | — | ❌ |

### Functions: HeaderReceived

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F3 | `HeaderReceived::into_pb` | `v1.chunked.send_ct.serialize.HeaderReceived.into_pb` | — | ❌ |
| F4 | `HeaderReceived::from_pb` | `v1.chunked.send_ct.serialize.HeaderReceived.from_pb` | — | ❌ |

### Functions: Ct1Sampled

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F5 | `Ct1Sampled::into_pb` | `v1.chunked.send_ct.serialize.Ct1Sampled.into_pb` | — | ❌ |
| F6 | `Ct1Sampled::from_pb` | `v1.chunked.send_ct.serialize.Ct1Sampled.from_pb` | — | ❌ |

### Functions: EkReceivedCt1Sampled

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F7 | `EkReceivedCt1Sampled::into_pb` | `v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.into_pb` | — | ❌ |
| F8 | `EkReceivedCt1Sampled::from_pb` | `v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.from_pb` | — | ❌ |

### Functions: Ct1Acknowledged

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F9 | `Ct1Acknowledged::into_pb` | `v1.chunked.send_ct.serialize.Ct1Acknowledged.into_pb` | — | ❌ |
| F10 | `Ct1Acknowledged::from_pb` | `v1.chunked.send_ct.serialize.Ct1Acknowledged.from_pb` | — | ❌ |

### Functions: Ct2Sampled

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F11 | `Ct2Sampled::into_pb` | `v1.chunked.send_ct.serialize.Ct2Sampled.into_pb` | — | ❌ |
| F12 | `Ct2Sampled::from_pb` | `v1.chunked.send_ct.serialize.Ct2Sampled.from_pb` | — | ❌ |

---

## 2. Skipped Functions and Reasons

### 2a. Deferred Functions (no spec file currently exists)

All 12 functions from
`v1_chunked_send_ct_serialize_functions.txt` are currently deferred —
no `into_pb` / `from_pb` spec files exist under
`Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/`. The spec tree
contains only Clone specs:

- `NoHeaderReceived/Clone.lean`
- `HeaderReceived/Clone.lean`
- `Ct1Sampled/Clone.lean`
- `EkReceivedCt1Sampled/Clone.lean`
- `Ct1Acknowledged/Clone.lean`

These Clone specs are listed for completeness only; they are **not**
in `v1_chunked_send_ct_serialize_functions.txt` and no verification
work is owed by this plan.

Note: `Ct2Sampled` does not have a Clone spec file in the current
spec tree.

### 2b. Unchunked-Layer `into_pb` / `from_pb` Dependencies (not yet verified)

The 12 chunked-layer serialize functions delegate to the
corresponding unchunked-layer `into_pb` / `from_pb` methods. These
unchunked-layer functions are extracted in `SrcTranslated/Funs.lean`
but do **not** yet have spec files:

| Unchunked Function | Lean Name | Spec File | Status |
|--------------------|-----------|-----------|--------|
| `NoHeaderReceived::into_pb` | `v1.unchunked.send_ct.serialize.NoHeaderReceived.into_pb` | — | ❌ |
| `NoHeaderReceived::from_pb` | `v1.unchunked.send_ct.serialize.NoHeaderReceived.from_pb` | — | ❌ |
| `HeaderReceived::into_pb` | `v1.unchunked.send_ct.serialize.HeaderReceived.into_pb` | — | ❌ |
| `HeaderReceived::from_pb` | `v1.unchunked.send_ct.serialize.HeaderReceived.from_pb` | — | ❌ |
| `Ct1Sent::into_pb` | `v1.unchunked.send_ct.serialize.Ct1Sent.into_pb` | — | ❌ |
| `Ct1Sent::from_pb` | `v1.unchunked.send_ct.serialize.Ct1Sent.from_pb` | — | ❌ |
| `Ct1SentEkReceived::into_pb` | `v1.unchunked.send_ct.serialize.Ct1SentEkReceived.into_pb` | — | ❌ |
| `Ct1SentEkReceived::from_pb` | `v1.unchunked.send_ct.serialize.Ct1SentEkReceived.from_pb` | — | ❌ |
| `Ct2Sent::into_pb` | `v1.unchunked.send_ct.serialize.Ct2Sent.into_pb` | — | ❌ |
| `Ct2Sent::from_pb` | `v1.unchunked.send_ct.serialize.Ct2Sent.from_pb` | — | ❌ |

The unchunked-layer spec directory
(`Spqr/Specs/Proto/PqRatchet/V1_state/Unchunked/`) contains only
Clone specs (all `sorry`-free). These unchunked functions must be
verified (or axiomatized) before their chunked-layer dependents.

### 2c. Polynomial-Layer Dependencies (verified)

The polynomial-layer `PolyEncoder::into_pb` / `from_pb` and
`PolyDecoder::into_pb` / `from_pb` are verified as documented in
[`Plan_poly`](Plan_poly):

| Polynomial Function | Spec File | Status |
|----------------------|-----------|--------|
| `PolyEncoder::into_pb` (F26) | `PolyEncoder/IntoPb.lean` | ✅ |
| `PolyEncoder::from_pb` (F27) | `PolyEncoder/FromPb.lean` | ✅ |
| `PolyDecoder::into_pb` (F38) | `PolyDecoder/IntoPb.lean` | ✅ |
| `PolyDecoder::from_pb` (F39) | `PolyDecoder/FromPb.lean` | ✅ |

### 2d. `from_pb` Validation Guards

Four `from_pb` methods contain `pts_needed` validation checks
against protocol constants. These guards must be verified or
explicitly flagged as requiring axioms over the protocol constants.

| Function | Validation Check | Constants Used |
|----------|-----------------|----------------|
| `NoHeaderReceived::from_pb` (F2) | `rhdr.pts_needed != (HEADER_SIZE + MACSIZE) / 2` | `incremental_mlkem768.HEADER_SIZE`, `authenticator.Authenticator.MACSIZE` |
| `HeaderReceived::from_pb` (F4) | `d.pts_needed as usize != ENCAPSULATION_KEY_SIZE / 2` | `incremental_mlkem768.ENCAPSULATION_KEY_SIZE` |
| `Ct1Sampled::from_pb` (F6) | `d.pts_needed as usize != ENCAPSULATION_KEY_SIZE / 2` | `incremental_mlkem768.ENCAPSULATION_KEY_SIZE` |
| `Ct1Acknowledged::from_pb` (F10) | `d.pts_needed as usize != ENCAPSULATION_KEY_SIZE / 2` | `incremental_mlkem768.ENCAPSULATION_KEY_SIZE` |

`EkReceivedCt1Sampled::from_pb` (F8) and `Ct2Sampled::from_pb` (F12)
have no `pts_needed` validation because they contain no `PolyDecoder`
field.

### 2e. Aeneas-Side Auto-Derived Wrappers (not in `v1_chunked_send_ct_serialize_functions.txt`, listed for completeness)

The following Lean spec files document Aeneas-emitted instance methods
(`Clone`) that do **not** appear in
`v1_chunked_send_ct_serialize_functions.txt`. They are listed here
purely for completeness; no verification work is owed by this plan.

| Spec file | Why "skipped" w.r.t. this plan |
|-----------|--------------------------------|
| `NoHeaderReceived/Clone.lean` | Auto-derived `Clone`; trivial delegation. |
| `HeaderReceived/Clone.lean` | Auto-derived `Clone`; trivial delegation. |
| `Ct1Sampled/Clone.lean` | Auto-derived `Clone`; trivial delegation. |
| `EkReceivedCt1Sampled/Clone.lean` | Auto-derived `Clone`; trivial delegation. |
| `Ct1Acknowledged/Clone.lean` | Auto-derived `Clone`; trivial delegation. |

---

## 3. Function Descriptions

### NoHeaderReceived

- **`NoHeaderReceived::into_pb`** [F1] — Serializes the
  `NoHeaderReceived` state by converting the unchunked
  `NoHeaderReceived` sub-state (via
  `unchunked::send_ct::NoHeaderReceived::into_pb`) and the
  `receiving_hdr` `PolyDecoder` (via `PolyDecoder::into_pb`) into
  their protobuf representations. Produces a
  `proto.pq_ratchet.v1_state.chunked.NoHeaderReceived` with both
  fields wrapped in `Some`. Rust source lines 11–16.
- **`NoHeaderReceived::from_pb`** [F2] — Deserializes a
  `NoHeaderReceived` protobuf, validating that
  `receiving_hdr.pts_needed` matches
  `(HEADER_SIZE + MACSIZE) / 2`. Returns `Error::StateDecode` on
  missing fields (`uc` or `receiving_hdr` is `None`),
  `Error::MsgDecode` on validation failure. Delegates to
  `unchunked::send_ct::NoHeaderReceived::from_pb` and
  `polynomial::PolyDecoder::from_pb`. Rust source lines 18–35.

### HeaderReceived

- **`HeaderReceived::into_pb`** [F3] — Serializes the
  `HeaderReceived` state by converting the unchunked
  `HeaderReceived` sub-state and the `receiving_ek` `PolyDecoder`
  into their protobuf representations. Rust source lines 39–44.
- **`HeaderReceived::from_pb`** [F4] — Deserializes a
  `HeaderReceived` protobuf, validating that
  `receiving_ek.pts_needed` matches
  `ENCAPSULATION_KEY_SIZE / 2`. Returns `Error::StateDecode` or
  `Error::MsgDecode` on failure. Delegates to
  `unchunked::send_ct::HeaderReceived::from_pb` and
  `polynomial::PolyDecoder::from_pb`. Rust source lines 46–59.

### Ct1Sampled

- **`Ct1Sampled::into_pb`** [F5] — Serializes the `Ct1Sampled` state
  by converting the unchunked `Ct1Sent` sub-state (via
  `unchunked::send_ct::Ct1Sent::into_pb`), the `sending_ct1`
  `PolyEncoder` (via `PolyEncoder::into_pb`), and the `receiving_ek`
  `PolyDecoder` (via `PolyDecoder::into_pb`). This is the only
  three-field struct. Rust source lines 63–69.
- **`Ct1Sampled::from_pb`** [F6] — Deserializes a `Ct1Sampled`
  protobuf, validating `receiving_ek.pts_needed` matches
  `ENCAPSULATION_KEY_SIZE / 2`. Delegates to
  `unchunked::send_ct::Ct1Sent::from_pb`,
  `polynomial::PolyEncoder::from_pb`, and
  `polynomial::PolyDecoder::from_pb`. Rust source lines 71–88.

### EkReceivedCt1Sampled

- **`EkReceivedCt1Sampled::into_pb`** [F7] — Serializes the
  `EkReceivedCt1Sampled` state by converting the unchunked
  `Ct1SentEkReceived` sub-state and the `sending_ct1`
  `PolyEncoder`. Rust source lines 92–97.
- **`EkReceivedCt1Sampled::from_pb`** [F8] — Deserializes an
  `EkReceivedCt1Sampled` protobuf. Delegates to
  `unchunked::send_ct::Ct1SentEkReceived::from_pb` and
  `polynomial::PolyEncoder::from_pb`. No `pts_needed` validation
  (no decoder field). Rust source lines 99–107.

### Ct1Acknowledged

- **`Ct1Acknowledged::into_pb`** [F9] — Serializes the
  `Ct1Acknowledged` state by converting the unchunked `Ct1Sent`
  sub-state and the `receiving_ek` `PolyDecoder`. Rust source
  lines 111–116.
- **`Ct1Acknowledged::from_pb`** [F10] — Deserializes a
  `Ct1Acknowledged` protobuf, validating
  `receiving_ek.pts_needed` matches
  `ENCAPSULATION_KEY_SIZE / 2`. Delegates to
  `unchunked::send_ct::Ct1Sent::from_pb` and
  `polynomial::PolyDecoder::from_pb`. Rust source lines 118–131.

### Ct2Sampled

- **`Ct2Sampled::into_pb`** [F11] — Serializes the `Ct2Sampled` state
  by converting the unchunked `Ct2Sent` sub-state and the
  `sending_ct2` `PolyEncoder`. Rust source lines 135–140.
- **`Ct2Sampled::from_pb`** [F12] — Deserializes a `Ct2Sampled`
  protobuf. Delegates to `unchunked::send_ct::Ct2Sent::from_pb`
  and `polynomial::PolyEncoder::from_pb`. No `pts_needed`
  validation (no decoder field). Rust source lines 142–150.

---

## 4. Verification Order (Dependency Table)

The table below lists every function from
`v1_chunked_send_ct_serialize_functions.txt` in **dependency order**:
to verify A, every prerequisite B must already be verified.
Polynomial-layer dependencies from [`Plan_poly`](Plan_poly) are
listed as a single prerequisite block ("Poly") because they are fully
verified. Unchunked-layer dependencies are listed explicitly because
they are not yet verified.

Legend (right column): ✅ verified, ⚠️ has a residual `sorry`,
❌ not verified, ⏭️ skipped (Section 2).

| Order | # | Function | Spec File | Depends On | Status |
|-------|---|----------|-----------|------------|--------|
| — | Poly | `PolyEncoder::into_pb` (F26), `PolyEncoder::from_pb` (F27), `PolyDecoder::into_pb` (F38), `PolyDecoder::from_pb` (F39) | See [`Plan_poly`](Plan_poly) | — | ✅ |
| — | UC1 | `unchunked::send_ct::NoHeaderReceived::into_pb` | — | — | ❌ (prerequisite) |
| — | UC2 | `unchunked::send_ct::NoHeaderReceived::from_pb` | — | — | ❌ (prerequisite) |
| — | UC3 | `unchunked::send_ct::HeaderReceived::into_pb` | — | — | ❌ (prerequisite) |
| — | UC4 | `unchunked::send_ct::HeaderReceived::from_pb` | — | — | ❌ (prerequisite) |
| — | UC5 | `unchunked::send_ct::Ct1Sent::into_pb` | — | — | ❌ (prerequisite) |
| — | UC6 | `unchunked::send_ct::Ct1Sent::from_pb` | — | — | ❌ (prerequisite) |
| — | UC7 | `unchunked::send_ct::Ct1SentEkReceived::into_pb` | — | — | ❌ (prerequisite) |
| — | UC8 | `unchunked::send_ct::Ct1SentEkReceived::from_pb` | — | — | ❌ (prerequisite) |
| — | UC9 | `unchunked::send_ct::Ct2Sent::into_pb` | — | — | ❌ (prerequisite) |
| — | UC10 | `unchunked::send_ct::Ct2Sent::from_pb` | — | — | ❌ (prerequisite) |
| 1 | F7 | `EkReceivedCt1Sampled::into_pb` | — | UC7, Poly (`PolyEncoder::into_pb`) | ❌ |
| 2 | F8 | `EkReceivedCt1Sampled::from_pb` | — | UC8, Poly (`PolyEncoder::from_pb`) | ❌ |
| 3 | F11 | `Ct2Sampled::into_pb` | — | UC9, Poly (`PolyEncoder::into_pb`) | ❌ |
| 4 | F12 | `Ct2Sampled::from_pb` | — | UC10, Poly (`PolyEncoder::from_pb`) | ❌ |
| 5 | F3 | `HeaderReceived::into_pb` | — | UC3, Poly (`PolyDecoder::into_pb`) | ❌ |
| 6 | F4 | `HeaderReceived::from_pb` | — | UC4, Poly (`PolyDecoder::from_pb`), `ENCAPSULATION_KEY_SIZE` | ❌ |
| 7 | F9 | `Ct1Acknowledged::into_pb` | — | UC5, Poly (`PolyDecoder::into_pb`) | ❌ |
| 8 | F10 | `Ct1Acknowledged::from_pb` | — | UC6, Poly (`PolyDecoder::from_pb`), `ENCAPSULATION_KEY_SIZE` | ❌ |
| 9 | F1 | `NoHeaderReceived::into_pb` | — | UC1, Poly (`PolyDecoder::into_pb`) | ❌ |
| 10 | F2 | `NoHeaderReceived::from_pb` | — | UC2, Poly (`PolyDecoder::from_pb`), `HEADER_SIZE`, `MACSIZE` | ❌ |
| 11 | F5 | `Ct1Sampled::into_pb` | — | UC5, Poly (`PolyEncoder::into_pb`, `PolyDecoder::into_pb`) | ❌ |
| 12 | F6 | `Ct1Sampled::from_pb` | — | UC6, Poly (`PolyEncoder::from_pb`, `PolyDecoder::from_pb`), `ENCAPSULATION_KEY_SIZE` | ❌ |

### Suggested Verification Grouping

The functions are grouped below by external dependency complexity,
from simplest to most complex:

1. **Two-field structs with PolyEncoder only** (simplest — no
   `pts_needed` validation):
   `EkReceivedCt1Sampled::into_pb` (F7),
   `EkReceivedCt1Sampled::from_pb` (F8),
   `Ct2Sampled::into_pb` (F11),
   `Ct2Sampled::from_pb` (F12).

2. **Two-field structs with PolyDecoder** (adds `pts_needed`
   validation against protocol constants):
   `HeaderReceived::into_pb` (F3),
   `HeaderReceived::from_pb` (F4),
   `Ct1Acknowledged::into_pb` (F9),
   `Ct1Acknowledged::from_pb` (F10),
   `NoHeaderReceived::into_pb` (F1),
   `NoHeaderReceived::from_pb` (F2).

3. **Three-field struct** (both PolyEncoder and PolyDecoder):
   `Ct1Sampled::into_pb` (F5),
   `Ct1Sampled::from_pb` (F6).

### Dependency DAG (ASCII)

```
    Polynomial layer (Plan_poly — all ✅)
    ┌─────────────────────────────────────────────────────────┐
    │ PolyEncoder::into_pb (F26)   PolyEncoder::from_pb (F27)│
    │ PolyDecoder::into_pb (F38)   PolyDecoder::from_pb (F39)│
    └───────────┬───────────────────────┬─────────────────────┘
                │                       │
    Unchunked layer (all ❌ — prerequisites)
    ┌───────────┴───────────────────────┴─────────────────────┐
    │ NoHeaderReceived::{into_pb,from_pb}  (UC1,UC2)          │
    │ HeaderReceived::{into_pb,from_pb}    (UC3,UC4)          │
    │ Ct1Sent::{into_pb,from_pb}           (UC5,UC6)          │
    │ Ct1SentEkReceived::{into_pb,from_pb} (UC7,UC8)          │
    │ Ct2Sent::{into_pb,from_pb}           (UC9,UC10)         │
    └───┬────────┬────────┬────────┬────────┬─────────────────┘
        │        │        │        │        │
        ▼        ▼        ▼        ▼        ▼
    ┌────────────────────────────────────────────────────────────┐
    │         Chunked send-CT serialize layer (all ❌)           │
    │                                                            │
    │  Group 1 (PolyEncoder, no validation):                     │
    │    EkReceivedCt1Sampled::{into_pb,from_pb}  (F7,F8)       │
    │    Ct2Sampled::{into_pb,from_pb}             (F11,F12)     │
    │                                                            │
    │  Group 2 (PolyDecoder, with pts_needed validation):        │
    │    HeaderReceived::{into_pb,from_pb}         (F3,F4)       │
    │    Ct1Acknowledged::{into_pb,from_pb}        (F9,F10)      │
    │    NoHeaderReceived::{into_pb,from_pb}        (F1,F2)      │
    │                                                            │
    │  Group 3 (PolyEncoder + PolyDecoder):                      │
    │    Ct1Sampled::{into_pb,from_pb}             (F5,F6)       │
    └────────────────────────────────────────────────────────────┘

    Protocol constants (for validation guards):
      HEADER_SIZE ← pk1_len (axiom)
      MACSIZE = 32 (concrete)
      ENCAPSULATION_KEY_SIZE ← pk2_len (axiom)
```

---

## 5. Source Code Modification Links

All chunked send-CT serialization functions are extracted from
`src/v1/chunked/send_ct/serialize.rs` via the Aeneas toolchain. The
extraction configuration is in
[`aeneas-config.yml`](../../aeneas-config.yml).

### Serialization-relevant entries in `aeneas-config.yml`

| Section | Entry | Purpose |
|---------|-------|---------|
| `tweaks` | Local variable `v1` shadowing fix for `v1.chunked.states` in `recv` ([issue #101](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/101)) | Fixes a namespace collision where a local variable `v1` shadows the module namespace `v1.chunked.states`. Not specific to the serialize functions, but affects the broader `v1.chunked` module. |

No additional `aeneas-config.yml` entries are required for the 12
serialize functions — they are extracted cleanly into
`SrcTranslated/Funs.lean` under the
`v1.chunked.send_ct.serialize.*` namespace.

### Aeneas-emitted closure types

Each `from_pb` function that calls `PolyEncoder::from_pb` or
`PolyDecoder::from_pb` uses `.map_err(|_| Error::StateDecode)` in
Rust, which Aeneas extracts as a closure type with an
`FnOnce` instance:

| Closure | Used By |
|---------|---------|
| `v1.chunked.send_ct.serialize.NoHeaderReceived.from_pb.closure` | F2 |
| `v1.chunked.send_ct.serialize.HeaderReceived.from_pb.closure` | F4 |
| `v1.chunked.send_ct.serialize.Ct1Sampled.from_pb.closure` | F6 (PolyDecoder) |
| `v1.chunked.send_ct.serialize.Ct1Sampled.from_pb.closure_1` | F6 (PolyEncoder) |
| `v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.from_pb.closure` | F8 |
| `v1.chunked.send_ct.serialize.Ct1Acknowledged.from_pb.closure` | F10 |
| `v1.chunked.send_ct.serialize.Ct2Sampled.from_pb.closure` | F12 |

These closures simply map `PolynomialError → Error::StateDecode` and
are trivially verified once the parent `from_pb` spec is written.

### Residual `sorry` impact summary

| Where | What |
|-------|------|
| `SrcTranslated/Funs.lean` — prost `Message` instances for 6 chunked proto structs | `sorry` bodies for `ProstMessageMessage` trait instances. These are **not** on the `into_pb` / `from_pb` verification path. |
| `SrcTranslated/FunsExternal.lean` — prost codec axioms for 6 chunked + 5 unchunked proto structs | 55 axioms (`encode_raw`, `merge_field`, `encoded_len`, `clear`, `decode` × 11 structs). These are **not** invoked by the `into_pb` / `from_pb` functions. |
| `SrcTranslated/Funs.lean` — `incremental_mlkem768.HEADER_SIZE`, `incremental_mlkem768.ENCAPSULATION_KEY_SIZE` | Defined via external `libcrux` functions (`pk1_len`, `pk2_len`). Verification of `from_pb` validation guards for F2, F4, F6, F10 requires axioms over these values. |

Pre-extraction source diff:
[`src-modifications.diff`](../../src-modifications.diff).

---

## 6. Summary

Based on the 12 functions in
`src/v1/chunked/send_ct/serialize.rs`:

- **12 functions**:
  - **0 verified** ✅ — no `into_pb` / `from_pb` spec files exist
    yet in
    `Spqr/Specs/Proto/PqRatchet/V1_state/Chunked/`.
  - **0 with residual `sorry`** ⚠️.
  - **12 not yet verified** ❌
    (F1–F12: all `into_pb` / `from_pb` pairs for the six state
    structs).
  - **0 skipped** ⏭️ — all functions in
    `v1_chunked_send_ct_serialize_functions.txt` are verifiable
    targets.
- **Prerequisites**:
  - **Polynomial layer** (`PolyEncoder::into_pb` / `from_pb`,
    `PolyDecoder::into_pb` / `from_pb`): all ✅ (see
    [`Plan_poly`](Plan_poly)).
  - **Unchunked layer** (5 × `into_pb` / `from_pb` pairs for
    `NoHeaderReceived`, `HeaderReceived`, `Ct1Sent`,
    `Ct1SentEkReceived`, `Ct2Sent`): all ❌ — must be verified
    or axiomatized before the chunked-layer specs.
  - **Protocol constants** (`HEADER_SIZE`, `MACSIZE`,
    `ENCAPSULATION_KEY_SIZE`): `MACSIZE` is concrete (32);
    `HEADER_SIZE` and `ENCAPSULATION_KEY_SIZE` require axioms
    over external `libcrux` functions.
- **`sorry` instances affecting this layer**: **0** on the
  verification path. All `sorry` instances in
  `SrcTranslated/Funs.lean` are prost-derived `Message` trait
  bodies, which are not invoked by the serialize functions.
- **Axioms**: 55 prost codec axioms in `FunsExternal.lean` for the
  11 relevant proto structs (6 chunked + 5 unchunked), plus
  axiomatized `libcrux` functions for `HEADER_SIZE` and
  `ENCAPSULATION_KEY_SIZE`. None of these are on the direct
  `into_pb` / `from_pb` verification path, but the protocol
  constants are needed for verifying the four `from_pb` validation
  guards.
- **Math foundations**: **none required** — all functions are pure
  protobuf serialization wrappers with no algebraic content.
