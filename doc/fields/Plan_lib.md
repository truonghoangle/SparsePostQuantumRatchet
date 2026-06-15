# TODO: Verification Plan for Top-Level Library Functions

## Overview

This document describes the TODO plan for verifying the functions and constants
listed in [`doc/truong/lib_functions.txt`](../truong/lib_functions.txt), which
enumerates all fully qualified function and constant names from
`src/lib.rs` (Rust source). These are extracted into
`SrcTranslated/Funs.lean` (Lean 4 / Aeneas extraction).

All extractable functions are configured via
[`aeneas-config.yml`](../../aeneas-config.yml). Functions not appearing in
that configuration (e.g. `#[cfg(test)]` items) are not extracted and
therefore cannot be verified in the current framework. Additionally,
several trait implementations (`Debug`, `Display`, `Error`) are
explicitly excluded from Charon extraction due to Aeneas limitations
(see Section 2).

No Lean specification tree currently exists for the `lib.rs` layer.
Spec files would need to be created under a new directory (e.g.
`Spqr/Specs/Lib/` or `Spqr/Specs/TopLevel/`). The lib module sits at
the top of the dependency hierarchy and transitively depends on:

- **Encoding** — [`Spqr/Specs/Encoding/`](../../Spqr/Specs/Encoding/)
  (polynomial, GF(2¹⁶), round-robin; see [`Plan_poly`](Plan_poly)
  and [`Plan_gf`](Plan_gf))
- **Chain** — `src/chain.rs` (key ratchet chain management)
- **Authenticator** — `src/authenticator/` (HMAC-based authentication;
  see [`HMAC_authenticator.md`](HMAC_authenticator.md))
- **KDF** — `src/kdf.rs` (key derivation functions)
- **Serialization** — `src/serialize.rs` (protobuf serialization)
- **V1 States** — `src/v1/` (protocol V1 state machine)
- **Protobuf** — `src/proto/pq_ratchet.rs` (prost-generated types)

---

## 0. Protocol Foundations — Statistics and Analysis

The `lib.rs` module is the **top-level SPQR protocol API**. Unlike the
polynomial or GF(2¹⁶) modules, it does not require algebraic
foundations in the traditional sense. Instead, its verification concerns
are:

1. **Protocol state machine correctness** — `send` and `recv` implement
   a version-negotiated ratcheting protocol that transitions through
   `PqRatchetState` (protobuf-serialized) states; invariants include
   correct version convergence and chain key agreement.
2. **Version negotiation** — `recv` performs multi-step negotiation
   comparing local and remote protocol versions, downgrading when
   permitted by `min_version` and rejecting when not.
3. **Error type totality** — the `From` trait impls guarantee that every
   subsystem error (`EncodingError`, `authenticator::Error`) is
   losslessly injected into the top-level `Error` enum.
4. **Serialization round-trip** — `decode_state` (protobuf decode) is
   the inverse of `PqRatchetState::encode_to_vec` (protobuf encode);
   `initial_state` produces a correctly formed serialized state.

### 0a. Files

No mathematical foundation files exist for `lib.rs`. The module's
semantic properties rest on the composition of verified lower layers:

| Dependency Layer | Foundation Location | Status |
|------------------|---------------------|--------|
| GF(2¹⁶) field arithmetic | [`Spqr/Math/Gf16/`](../../Spqr/Math/Gf16/) | Fully proved (see [`Plan_gf`](Plan_gf)) |
| Polynomial algebra | [`Spqr/Math/Poly/`](../../Spqr/Math/Poly/) | Fully proved (see [`Plan_poly`](Plan_poly)) |
| HMAC authenticator | [`Spqr/Aux/LibcruxHmac/`](../../Spqr/Aux/LibcruxHmac/) | Partial (see [`HMAC_authenticator.md`](HMAC_authenticator.md)) |
| Protobuf `Message` instances | `SrcTranslated/Funs.lean` (prost-generated) | `sorry`'d by `aeneas-config.yml` tweaks |
| Chain management | `src/chain.rs` | Not yet verified |
| KDF (HKDF) | `src/kdf.rs` | `hkdf_to_slice` declared opaque |
| V1 state machine | `src/v1/` | Not yet verified |

### 0b. Extracted Definitions

All lib-layer functions are extracted into `SrcTranslated/Funs.lean`
under the `spqr` namespace. The key extracted definitions are:

| Definition | Lean Name | Source Lines |
|------------|-----------|--------------|
| `Direction.switch` | `Direction.switch` | 65–71 |
| `empty_state` | `empty_state` | 47–49 |
| `SecretOutput.send_secret` | `SecretOutput.send_secret` | 152–158 |
| `SecretOutput.recv_secret` | `SecretOutput.recv_secret` | 159–165 |
| `SecretOutput.secret` | `SecretOutput.secret` | 167–172 |
| `SecretOutput.has_secret` | `SecretOutput.has_secret` | 173–175 |
| `init_inner` | `init_inner` | 198–210 |
| `initial_state` | `initial_state` | 212–236 |
| `decode_state` | `decode_state` | 472–482 |
| `current_version` | `current_version` | 249–262 |
| `send` | `send` | 265–326 |
| `recv` | `recv` | 356–455 |
| `chain_from_version_negotiation` | `chain_from_version_negotiation` | 333–341 |
| `chain_from` | `chain_from` | 343–354 |
| `state_version` | `state_version` | 457–462 |
| `msg_version` | `msg_version` | 464–470 |
| `Version.DISABLED` | `Version.DISABLED` | 239 |
| `Version.MAX` | `Version.MAX` | 240 |

### 0c. Aeneas Extraction Notes

Three functions — `initial_state`, `send`, and `recv` — are **also**
declared as axioms in `SrcTranslated/FunsExternal.lean` in addition to
having extracted bodies in `SrcTranslated/Funs.lean`. The axioms
provide simplified type signatures suitable for downstream specification
work:

| Function | `FunsExternal.lean` Axiom Type |
|----------|-------------------------------|
| `initial_state` | `Params → Result (core.result.Result (alloc.vec.Vec Std.U8) spqr.Error)` |
| `send` | `∀ {R}, Rng R → CryptoRng R → Vec U8 → R → Result ((Result Send Error) × R)` |
| `recv` | `Vec U8 → Vec U8 → Result (Result Recv Error)` |

The `send` function carries the Rust annotation
`#[hax_lib::fstar::verification_status(lax)]`, indicating it is not yet
verified in the F\* extraction either.

### 0d. Variable Shadowing Fixes (`aeneas-config.yml`)

The extracted bodies for `send` and `recv` require post-extraction
tweaks to resolve variable shadowing between local bindings and module
namespaces:

| Tweak | Lines | Effect |
|-------|-------|--------|
| `chain` → `chain'` in `send` | 106–113 | Prevents local `chain` from shadowing `chain.Chain` module path. |
| `chain` → `chain'` in `recv` | 116–124 | Same shadowing fix for the `recv` function. |
| `v1` → `v1'` in `recv` | 127–129 | Prevents local `v1` from shadowing `v1.chunked.states` module path. |

### 0e. `sorry` / Axiom Inventory Affecting the Lib Layer

| Source | What | Impact |
|--------|------|--------|
| `aeneas-config.yml` (lines 80–81) | `BytesBufBuf_implBuf` — sorry'd | Self-referential struct; affects protobuf decode path. |
| `aeneas-config.yml` (lines 86–87) | All prost `Message` instance bodies — sorry'd | Affects `encode_to_vec` and `decode` used by `initial_state`, `send`, `recv`, `decode_state`. |
| `aeneas-config.yml` (lines 91–92) | `VecDeque IntoIter Iterator` — sorry'd | Affects chain iteration in `send`. |
| `aeneas-config.yml` (line 49) | `decoded_message` — opaque axiom | Not in `lib.rs` but transitively reachable. |
| `aeneas-config.yml` (line 47) | `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` — opaque | Not in `lib.rs` but transitively reachable via V1 states. |
| `aeneas-config.yml` (lines 45–46) | `hkdf_to_slice` — opaque | Transitively reachable via KDF → Chain. |

### 0f. Statistics Summary

| Metric | Count |
|--------|-------|
| Functions in `lib_functions.txt` (non-test) | 21 |
| Constants in `lib_functions.txt` | 2 |
| Test functions in `lib_functions.txt` | 12 |
| Functions extracted into `Funs.lean` (with bodies) | 20 |
| Functions excluded by Charon config | 1 (`From<serialize::Error> for Error`) |
| Functions with FunsExternal axiom alternatives | 3 (`initial_state`, `send`, `recv`) |
| Existing spec files for lib layer | **0** |
| `sorry` instances directly in lib extraction | **0** (but protobuf dependencies are sorry'd) |
| Axioms declared for lib functions | **0** (but 3 alternative axioms in FunsExternal) |
| Transitive opaque dependencies | 3 (`hkdf_to_slice`, `decoded_message`, `potentially_fix_state…`) |

---

## 1. Combined Function and Constant Inventory

The following tables list every function and constant from
`lib_functions.txt`, together with its Lean name in
`SrcTranslated/Funs.lean`, its current spec file (if any), and
verification status.

Legend: ✅ = verified (spec file present, no `sorry`), ⚠️ = spec
exists but contains `sorry`, ❌ = not yet verified (no spec file),
⏭️ = skipped (see Section 2).

### Constants

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| C1 | `Version::DISABLED` | `Version.DISABLED` | — | ❌ |
| C2 | `Version::MAX` | `Version.MAX` | — | ❌ |

### Functions: Direction

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F1 | `Direction::switch` | `Direction.switch` | — | ❌ |

### Functions: Error Trait Impls

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F2 | `{impl From<encoding::EncodingError> for Error}::from` | `Error.Insts.CoreConvertFromEncodingError.from` | — | ❌ |
| F3 | `{impl From<serialize::Error> for Error}::from` | — (excluded) | — | ⏭️ Excluded (name clash) |
| F4 | `{impl From<authenticator::Error> for Error}::from` | `Error.Insts.CoreConvertFromError.from` | — | ❌ |

### Functions: SecretOutput

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F5 | `SecretOutput::send_secret` | `SecretOutput.send_secret` | — | ❌ |
| F6 | `SecretOutput::recv_secret` | `SecretOutput.recv_secret` | — | ❌ |
| F7 | `SecretOutput::secret` | `SecretOutput.secret` | — | ❌ |
| F8 | `SecretOutput::has_secret` | `SecretOutput.has_secret` | — | ❌ |

### Functions: Version Trait Impls

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F9 | `{impl TryFrom<u8> for Version}::try_from` | `proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String.try_from` | — | ❌ |
| F10 | `{impl From<Version> for u8}::from` | `U8.Insts.CoreConvertFromVersion.from` | — | ❌ |

### Functions: Free Functions

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F11 | `empty_state` | `empty_state` | — | ❌ |
| F12 | `initial_state` | `initial_state` | — | ❌ |
| F13 | `send` | `send` | — | ❌ |
| F14 | `current_version` | `current_version` | — | ❌ |
| F15 | `recv` | `recv` | — | ❌ |
| F16 | `init_inner` | `init_inner` | — | ❌ |
| F17 | `chain_from_version_negotiation` | `chain_from_version_negotiation` | — | ❌ |
| F18 | `chain_from` | `chain_from` | — | ❌ |
| F19 | `state_version` | `state_version` | — | ❌ |
| F20 | `msg_version` | `msg_version` | — | ❌ |
| F21 | `decode_state` | `decode_state` | — | ❌ |

### Functions: Tests

| # | Rust Name | Lean Name | Spec File | Status |
|---|-----------|-----------|-----------|--------|
| F22 | `lib_test::ratchet` | — | — | ⏭️ `#[cfg(test)]` |
| F23 | `lib_test::ratchet_v0_empty_states` | — | — | ⏭️ `#[cfg(test)]` |
| F24 | `lib_test::empty_constructor_for_state` | — | — | ⏭️ `#[cfg(test)]` |
| F25 | `lib_test::empty_key_until_version_negotiation` | — | — | ⏭️ `#[cfg(test)]` |
| F26 | `lib_test::min_version_v1_always_creates_keys_a2b` | — | — | ⏭️ `#[cfg(test)]` |
| F27 | `lib_test::min_version_v1_always_creates_keys_b2a` | — | — | ⏭️ `#[cfg(test)]` |
| F28 | `lib_test::negotiate_to_v0_a2b` | — | — | ⏭️ `#[cfg(test)]` |
| F29 | `lib_test::negotiate_to_v0_b2a` | — | — | ⏭️ `#[cfg(test)]` |
| F30 | `lib_test::negotiation_refused_a2b` | — | — | ⏭️ `#[cfg(test)]` |
| F31 | `lib_test::negotiation_refused_b2a` | — | — | ⏭️ `#[cfg(test)]` |
| F32 | `lib_test::lockstep_run_with_logging` | — | — | ⏭️ `#[cfg(test)]` |
| F33 | `lib_test::regression_test_libcrux_issue_1275_from_generated_states` | — | — | ⏭️ `#[cfg(test)]` |

---

## 2. Skipped Functions and Reasons

### 2a. Excluded Trait Implementations (Charon Config)

The following trait implementations are excluded from Charon extraction
in [`aeneas-config.yml`](../../aeneas-config.yml) due to Aeneas
limitations or name clashes:

| # | Rust Name | Config Line | Why Excluded |
|---|-----------|-------------|--------------|
| F3 | `{impl From<serialize::Error> for Error}::from` | 43 | Name clash with `From<authenticator::Error>` — both map to `Error::from` in the extraction. |
| — | `{impl Debug for Error}` | 39 | Aeneas assertion failure on `thiserror`-derived Debug. |
| — | `{impl Display for Error}` | 40 | Aeneas assertion failure on `thiserror`-derived Display. |
| — | `{impl std::error::Error for Error}` | 41 | Aeneas assertion failure. |
| — | `{impl Debug for CurrentVersion}` | 42 | Cascading exclusion: `Debug for Version` (proto) is excluded. |

### 2b. Aeneas-Side Auto-Derived Wrappers (not in `lib_functions.txt`, listed for completeness)

The following Lean definitions are emitted by Aeneas for auto-derived
trait instances on `SecretOutput`. They do **not** appear in
`lib_functions.txt` and are listed here purely for completeness:

| Lean Definition | Why "skipped" w.r.t. this plan |
|-----------------|--------------------------------|
| `SecretOutput.Insts.CoreMarkerStructuralPartialEq` | Auto-derived `StructuralPartialEq`; trivial. |
| `SecretOutput.Insts.CoreCmpPartialEqSecretOutput` (+ `.eq`) | Auto-derived `PartialEq`; structural enum comparison. |
| `SecretOutput.Insts.CoreFmtDebug` (+ `.fmt`) | Auto-derived `Debug`; formatting, no semantic content. |
| `I32.Insts.CoreConvertFromVersion` (+ `.from`) | `From<Version> for i32`; used internally by protobuf encoding. |

### 2c. Test Functions (`#[cfg(test)]`, not extracted)

| # | Rust Name | Why Skipped |
|---|-----------|-------------|
| F22–F33 | `lib_test::*` | `#[cfg(test)]` — unit / integration tests, not part of the library API. |

### 2d. Protobuf-Related Opaque Dependencies

The lib module's `send`, `recv`, `initial_state`, and `decode_state`
functions all call `PqRatchetState::encode_to_vec` (serialization) or
`PqRatchetState::decode` (deserialization). These protobuf `Message`
trait methods are declared opaque in `aeneas-config.yml` (lines 50–52)
and their instance bodies are sorry'd (lines 86–87). This means:

- Full functional verification of `send`, `recv`, `initial_state` requires
  either proving the protobuf round-trip properties or accepting them
  as trusted axioms.
- The protobuf layer is generated by `prost` and is outside the scope of
  the hand-written Rust source being verified.

### 2e. Functions with FunsExternal Axiom Alternatives

Three functions have both extracted `def` bodies in `Funs.lean` and
`axiom` declarations in `FunsExternal.lean`. The axioms provide
simplified type signatures for downstream specification work:

| # | Rust Name | Why Axiom Exists |
|---|-----------|------------------|
| F12 | `initial_state` | Complex body involving protobuf `encode_to_vec`, V1 state initialization. |
| F13 | `send` | Uses `rand::Rng` (generic RNG), protobuf serialization, chain management. Marked `#[hax_lib::fstar::verification_status(lax)]`. |
| F15 | `recv` | Complex multi-branch version negotiation, protobuf decode, chain management. |

---

## 3. Function Descriptions

### Constants

- **`Version::DISABLED`** [C1] — Alias for `Version::V0`; indicates the
  SPQR protocol is disabled. Defined as `@[global_simps, irreducible]`
  in the extraction.
- **`Version::MAX`** [C2] — Alias for `Version::V1`; the highest
  supported protocol version. Defined as `@[global_simps, irreducible]`
  in the extraction.

### Direction (Enum Method)

- **`Direction::switch`** [F1] — Swaps `A2B ↔ B2A`. A pure
  pattern-match with no error paths; trivially correct.

### Error Trait Impls (Error Type Injection)

- **`{impl From<EncodingError> for Error}::from`** [F2] — Wraps an
  `encoding::EncodingError` in `Error::EncodingDecoding`. Injective
  constructor application.
- **`{impl From<serialize::Error> for Error}::from`** [F3] — Wraps a
  `serialize::Error` in `Error::Serialization`. **Excluded** from
  extraction due to name clash with F4.
- **`{impl From<authenticator::Error> for Error}::from`** [F4] — Maps
  any `authenticator::Error` to `Error::MacVerifyFailed` (discards the
  inner error value).

### SecretOutput (Accessor Methods)

- **`SecretOutput::send_secret`** [F5] — Returns `Some(&secret)` for
  `SecretOutput::Send(secret)`, `None` otherwise.
- **`SecretOutput::recv_secret`** [F6] — Returns `Some(&secret)` for
  `SecretOutput::Recv(secret)`, `None` otherwise.
- **`SecretOutput::secret`** [F7] — Returns `Some(&secret)` for either
  `Send(secret)` or `Recv(secret)`, `None` for `None`.
- **`SecretOutput::has_secret`** [F8] — Returns `true` unless
  `self` is `SecretOutput::None`.

### Version Trait Impls (Conversion)

- **`{impl TryFrom<u8>}::try_from`** [F9] — Maps `0 → V0`,
  `1 → V1`, otherwise `Err("Expected 0 or 1")`.
- **`{impl From<Version> for u8}::from`** [F10] — Maps `V0 → 0`,
  `V1 → 1`. Total and injective.

### Free Functions (Protocol Core)

- **`empty_state()`** [F11] — Returns an empty `Vec<u8>`, representing
  the V0 (disabled) protocol state.
- **`initial_state(params)`** [F12] — Constructs the initial serialized
  `PqRatchetState` from `Params { direction, version, min_version,
  auth_key, chain_params }`. For `V0` returns `empty_state()`;
  for `V1+` builds a protobuf state with version negotiation metadata
  and calls `init_inner` for the inner V1 state.
- **`send(state, rng)`** [F13] — Deserializes the state, produces a
  message via the V1 state machine (`States::from_pb → send`), manages
  the key chain (adding epoch secrets, requesting send keys),
  serializes updated state and message. Returns `Send { state, msg,
  key }`. The `key` field is `Some` when the chain produces a non-empty
  message key.
- **`current_version(state)`** [F14] — Deserializes the state and
  returns `CurrentVersion::StillNegotiating { version, min_version }`
  or `CurrentVersion::NegotiationComplete(version)` depending on
  whether `version_negotiation` metadata is present.
- **`recv(state, msg)`** [F15] — The most complex function: performs
  version negotiation (comparing `msg_version` with `state_version`,
  downgrading or rejecting as appropriate), then processes the message
  through the V1 state machine (`States::from_pb → recv`), manages
  the receive chain, and returns `Recv { state, key }`.
- **`init_inner(v, d, auth_key)`** [F16] — For `V1`, initializes
  the V1 state machine (`States::init_a` or `States::init_b`
  depending on direction) and serializes to protobuf. Returns `None`
  for `V0`.
- **`chain_from_version_negotiation(vn)`** [F17] — Constructs a new
  `Chain` from version negotiation metadata (auth key, direction,
  chain params).
- **`chain_from(pb, vn)`** [F18] — Deserializes a `Chain` from
  protobuf if present; otherwise creates one from version negotiation
  metadata. Returns `Err(ChainNotAvailable)` if neither is available.
- **`state_version(state)`** [F19] — Returns `V0` if `state.inner` is
  `None`, `V1` if it is `Some(Inner::V1(_))`. Pure pattern match.
- **`msg_version(msg)`** [F20] — Returns `Some(V0)` for empty
  messages, `msg[0].try_into().ok()` otherwise. Maps the first byte
  to a `Version` via `TryFrom<u8>`.
- **`decode_state(s)`** [F21] — If `s` is empty, returns a default
  `PqRatchetState { inner: None, version_negotiation: None, chain:
  None }`. Otherwise calls `PqRatchetState::decode(s)`, mapping
  decode errors to `Error::StateDecode`.

### Test Functions (not extracted)

- **F22–F33** — Unit and integration tests covering:
  - Basic ratcheting (`ratchet`)
  - V0 empty state handling (`ratchet_v0_empty_states`)
  - Empty state constructor (`empty_constructor_for_state`)
  - Key availability after version negotiation (`empty_key_until_version_negotiation`)
  - Minimum version enforcement (`min_version_v1_always_creates_keys_{a2b,b2a}`)
  - Version downgrade negotiation (`negotiate_to_v0_{a2b,b2a}`)
  - Negotiation refusal (`negotiation_refused_{a2b,b2a}`)
  - Lockstep execution (`lockstep_run_with_logging`)
  - Regression test (`regression_test_libcrux_issue_1275_from_generated_states`)

---

## 4. Verification Order (Dependency Table)

The table below lists every function and constant from
`lib_functions.txt` in **dependency order**: to verify A, every
prerequisite B must already be verified.

Legend (right column): ✅ verified, ⚠️ has a residual `sorry`,
❌ not verified, ⏭️ skipped (Section 2).

| Order | # | Function / Constant | Spec File | Depends On | Status |
|-------|---|---------------------|-----------|------------|--------|
|  1 | C1 | `Version::DISABLED` | — | (irreducible constant) | ❌ |
|  2 | C2 | `Version::MAX` | — | (irreducible constant) | ❌ |
|  3 | F1 | `Direction::switch` | — | (pure enum match) | ❌ |
|  4 | F2 | `{impl From<EncodingError> for Error}::from` | — | (constructor wrapper) | ❌ |
|  5 | F3 | `{impl From<serialize::Error> for Error}::from` | — | — | ⏭️ excluded |
|  6 | F4 | `{impl From<authenticator::Error> for Error}::from` | — | (constructor wrapper) | ❌ |
|  7 | F5 | `SecretOutput::send_secret` | — | (pure match) | ❌ |
|  8 | F6 | `SecretOutput::recv_secret` | — | (pure match) | ❌ |
|  9 | F7 | `SecretOutput::secret` | — | (pure match) | ❌ |
| 10 | F8 | `SecretOutput::has_secret` | — | (pure match) | ❌ |
| 11 | F9 | `{impl TryFrom<u8>}::try_from` | — | (integer match) | ❌ |
| 12 | F10 | `{impl From<Version> for u8}::from` | — | (enum → integer) | ❌ |
| 13 | F11 | `empty_state` | — | (Vec::new) | ❌ |
| 14 | F19 | `state_version` | — | (pure match) | ❌ |
| 15 | F20 | `msg_version` | — | F9 (`try_from`) | ❌ |
| 16 | F21 | `decode_state` | — | protobuf `Message::decode` (opaque) | ❌ |
| 17 | F16 | `init_inner` | — | V1 `States::init_a/b`, protobuf (opaque) | ❌ |
| 18 | F17 | `chain_from_version_negotiation` | — | `Chain::new` (chain.rs) | ❌ |
| 19 | F18 | `chain_from` | — | F17, `Chain::from_pb` (chain.rs) | ❌ |
| 20 | F14 | `current_version` | — | F21 (`decode_state`), F9 (`try_from`) | ❌ |
| 21 | F12 | `initial_state` | — | F11, F16, protobuf `encode_to_vec` (opaque) | ❌ |
| 22 | F13 | `send` | — | F21, F17, F18, F19, V1 `States`, `Chain`, protobuf (opaque) | ❌ |
| 23 | F15 | `recv` | — | F21, F16, F17, F18, F19, F20, V1 `States`, `Chain`, protobuf (opaque) | ❌ |
| 24 | F22–F33 | `lib_test::*` | — | — | ⏭️ `#[cfg(test)]` |

### Dependency DAG (ASCII)

```
    Version::DISABLED(C1)    Version::MAX(C2)
    Direction::switch(F1)

    Error From impls (F2, F4)                [F3 ⏭️ excluded]

    SecretOutput accessors (F5–F8)           (pure match, no deps)

    TryFrom<u8> for Version (F9) ──► msg_version(F20)
    From<Version> for u8 (F10)

    empty_state(F11)
         │
         ▼
    state_version(F19)        decode_state(F21) ◄── protobuf decode (opaque)
         │                          │
         │          ┌───────────────┤
         │          │               │
         │          ▼               ▼
         │   current_version(F14)   │
         │                          │
    init_inner(F16) ◄── V1 States   │
         │                          │
         ▼                          │
    initial_state(F12) ◄── protobuf encode (opaque)
                                    │
    chain_from_version_negotiation(F17) ◄── Chain::new
         │                          │
         ▼                          │
    chain_from(F18) ◄── Chain::from_pb
         │                          │
         ├──────────────────────────┤
         ▼                          ▼
    send(F13) ◄── V1 States, Chain, protobuf
         │
    recv(F15) ◄── F16, F17, F18, F19, F20, F21, V1 States, Chain, protobuf
```

---

## 5. Source Code Modification Links

All lib-layer functions are extracted from `src/lib.rs` via the Aeneas
toolchain. The extraction configuration is in
[`aeneas-config.yml`](../../aeneas-config.yml).

### Lib-relevant entries in `aeneas-config.yml`

| Section | Entry | Purpose |
|---------|-------|---------|
| `charon.exclude` (line 39) | `{impl Debug for Error}` | Aeneas assertion failure on `thiserror`-derived Debug. |
| `charon.exclude` (line 40) | `{impl Display for Error}` | Aeneas assertion failure on `thiserror`-derived Display. |
| `charon.exclude` (line 41) | `{impl std::error::Error for Error}` | Aeneas assertion failure. |
| `charon.exclude` (line 42) | `{impl Debug for CurrentVersion}` | Cascading exclusion: `Debug for Version` (proto) is excluded. |
| `charon.exclude` (line 43) | `{impl From<serialize::Error> for Error}` | Name clash with `From<authenticator::Error>`. |
| `tweaks` (lines 106–113) | `chain` → `chain'` in `send` | Fixes local variable shadowing `chain.Chain` module namespace. |
| `tweaks` (lines 116–124) | `chain` → `chain'` in `recv` | Same shadowing fix for `recv`. |
| `tweaks` (lines 127–129) | `v1` → `v1'` in `recv` | Fixes local variable shadowing `v1.chunked.states` namespace. |
| `tweaks` (lines 155–156) | `Option.ok_or` type annotation | Fixes `none` type inference; affects `decode_state` → `PolyDecoder::from_pb` path. |

Pre-extraction source diff: [`src-modifications.diff`](../../src-modifications.diff).

### ProVerif security model

Protocol-level security properties of the SPQR ratchet (including
forward secrecy and post-compromise security) are modelled and verified
symbolically using ProVerif:

| File | Purpose |
|------|---------|
| [`proofs/proverif/spqr-cka.pv`](../../proofs/proverif/spqr-cka.pv) | CKA (Continuous Key Agreement) security model. |
| [`proofs/proverif/spqr-dr.pv`](../../proofs/proverif/spqr-dr.pv) | Double Ratchet security model. |
| [`proofs/proverif/cryptolib.pvl`](../../proofs/proverif/cryptolib.pvl) | Shared cryptographic library definitions. |

These models verify security at the protocol level but do not establish
functional correctness of the Rust implementation.

### Residual `sorry` impact summary

| Where | What |
|-------|------|
| `aeneas-config.yml` (prost `Message` instances) | All protobuf `encode_to_vec` / `decode` bodies are sorry'd. Blocks full functional verification of F12, F13, F15, F21. |
| `aeneas-config.yml` (`BytesBufBuf`) | Protobuf buffer instance sorry'd. Transitively affects decode paths. |
| `aeneas-config.yml` (`VecDeque IntoIter`) | Iterator instance sorry'd. Affects chain iteration in F13 (`send`). |
| `FunsExternal.lean` axioms | `initial_state`, `send`, `recv` have axiom alternatives; if the extracted bodies are unusable, these axioms must be trusted. |

---

## 6. Summary

Based on the 21 functions + 2 constants + 12 tests in `src/lib.rs`:

- **2 constants**: 0 verified ❌ — `Version::DISABLED` and
  `Version::MAX` are trivial `@[irreducible]` definitions but lack
  spec files.
- **21 functions** (non-test):
  - **0 verified** ✅
  - **0 with residual `sorry`** ⚠️
  - **19 not yet verified** ❌
    (F1, F2, F4–F21 — all lack spec files).
  - **1 excluded** ⏭️
    (F3 `From<serialize::Error>` — Charon name clash).
  - **1 excluded by category** — F3 above.
- **12 test functions**: all ⏭️ (`#[cfg(test)]`, not extracted).
- **`sorry` instances affecting lib layer**: 0 directly, but all
  protobuf `Message` instance bodies are sorry'd by `aeneas-config.yml`
  tweaks, blocking full verification of `initial_state` (F12),
  `send` (F13), `recv` (F15), and `decode_state` (F21).
- **Axioms used by the lib layer**:
  - 3 alternative axioms in `FunsExternal.lean` (`initial_state`,
    `send`, `recv`) — provide simplified type signatures.
  - 0 local bridge axioms in spec files (no spec files exist).
- **Transitive opaque dependencies**: `hkdf_to_slice` (KDF),
  `decoded_message` (polynomial decoder),
  `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`
  (incremental ML-KEM).
- **Verification priority**: The lib module is the top-level
  orchestration layer. Its verification should proceed bottom-up:
  1. First verify the simpler leaf functions (F1, F5–F11, F19, F20,
     C1, C2) — these are pure pattern matches or trivial constructors.
  2. Then verify the error injection impls (F2, F4) and version
     conversions (F9, F10).
  3. Then verify state decoding (F21) — requires protobuf axioms.
  4. Then verify `init_inner` (F16), `chain_from*` (F17–F18),
     `current_version` (F14), `initial_state` (F12).
  5. Finally verify `send` (F13) and `recv` (F15) — the most complex
     functions, requiring chain management and V1 state machine
     verification as prerequisites.
