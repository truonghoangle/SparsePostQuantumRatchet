# Properties of `spqr::initial_state` — Analysis and Lean Feasibility

## 0. Function Overview

`initial_state` (source: `src/lib.rs`, lines 212–236) is the **public entry point** that
constructs a fresh serialized SPQR protocol state from a `Params` structure:

```rust
pub fn initial_state(params: Params) -> Result<SerializedState, Error> {
    match params.version {
        Version::V0 => Ok(empty_state()),
        _ => {
            let version_negotiation = Some(VersionNegotiation {
                auth_key: params.auth_key.to_vec(),
                direction: params.direction.into(),
                min_version: params.min_version.into(),
                chain_params: Some(params.chain_params.into_pb()),
            });
            Ok(PqRatchetState {
                inner: init_inner(params.version, params.direction, params.auth_key),
                chain: None,
                version_negotiation,
            }
            .encode_to_vec())
        }
    }
}
```

**Inputs**: `Params { direction, version, min_version, auth_key, chain_params }`

**Outputs**: `Result<SerializedState, Error>` — always `Ok(...)`, never `Err`.

**Lean spec files** (existing):
- `Spqr/Specs/Lib/InitialState.lean` — `initial_state_spec`
- `Spqr/Specs/Lib/InitInner.lean` — `init_inner_spec`, `init_inner_university_spec`

---

## 1. Decomposition of Sub-operations

`initial_state` is a thin orchestration layer. Its behavior decomposes into:

| Step | Sub-operation | Lean Spec Location |
|------|---------------|-------------------|
| 1 | Version match (`V0` vs `V1`) | `initial_state_spec` (case split) |
| 2 | `empty_state()` (V0 branch) | trivial — `Vec::new()` |
| 3 | `auth_key.to_vec()` (clone) | `alloc.slice.Slice.to_vec` |
| 4 | `init_inner(V1, direction, auth_key)` | `init_inner_spec` / `init_inner_university_spec` |
| 5 | `ChainParams.into_pb` | `chain.ChainParams.into_pb` |
| 6 | `PqRatchetState.encode_to_vec()` | protobuf (opaque / sorry'd) |

Steps 1–5 are fully decomposed in the existing Lean specs. Step 6 is opaque.

---

## 2. Mathematical Properties

### 2.1 Property: Total Function (No Panics)

**Statement**: For all valid `Params` inputs with `auth_key.length ≤ U32.max`,
`initial_state` returns `Ok(...)` — it never returns `Err(...)` or panics.

**Mathematical characterization**: `initial_state` is a **total function** on its domain:
```
∀ params, auth_key.length ≤ U32.max →
  ∃ v, initial_state params = ok (core.result.Result.Ok v)
```

**Current Lean status**: `initial_state_spec` proves this under explicit sub-operation
success hypotheses (`h_to_vec`, `h_dir`, `h_ver`, `h_cp`, `h_init`, `h_encode`). The
theorem itself does not discharge these hypotheses from first principles — it takes them
as preconditions.

**Feasibility in Lean**: ✅ **Achievable**. The sub-operation hypotheses can be discharged
by composing the downstream specs (`init_inner_university_spec`, etc.) with the
`auth_key.length ≤ U32.max` bound. The only blocker is the opaque `encode_to_vec`
(protobuf serialization), which must be axiomatized.

**References**:
- RFC 9180 §4 (HKDF construction guarantees output for valid inputs)
- FIPS 203 §7.1 (ML-KEM key generation is total for valid randomness)

---

### 2.2 Property: Determinism

**Statement**: `initial_state` is a **deterministic, pure function** — given the same
`Params`, it always produces the same `SerializedState`.

**Mathematical characterization**:
```
∀ params₁ params₂,
  params₁ = params₂ →
  initial_state params₁ = initial_state params₂
```

This is a consequence of the fact that `initial_state` does **not** use any randomness
(unlike `send`, which takes `rng: &mut R`). All sub-operations are deterministic:
- `auth_key.to_vec()` — deterministic clone
- `init_inner` → `Authenticator.new` → `HKDF-SHA256` — deterministic KDF
- `encode_to_vec` — deterministic protobuf serialization

**Current Lean status**: Follows from definitional equality — Lean's `initial_state` is
a pure function by construction. No separate theorem is needed.

**Feasibility in Lean**: ✅ **Trivially true** by Lean's type system (no monadic
randomness appears in the type signature).

**References**:
- RFC 5869 §2.2 (HKDF-Expand is deterministic for fixed inputs)

---

### 2.3 Property: V0 Produces Empty State

**Statement**: When `params.version = V0`, `initial_state` returns an empty byte vector.

**Mathematical characterization**:
```
params.version = V0 →
  initial_state params = ok (core.result.Result.Ok [])
```

**Current Lean status**: ✅ **Proved** in `initial_state_spec` (the V0 branch):
```lean
| .V0 =>
  ∃ es, empty_state = ok es ∧
    result = core.result.Result.Ok es
```

**Feasibility in Lean**: ✅ **Already done**.

---

## 3. Cryptographic Properties

### 3.1 Property: HKDF-SHA256 Key Derivation Correctness

**Statement**: In the V1 branch, the embedded `Authenticator` is constructed via
`Authenticator.new(auth_key.to_vec(), 1)`, which internally calls:

```
ikm  = [0; 32] ++ auth_key
info = b"Signal_PQCKA_V1_MLKEM768:Authenticator Update" ++ (1 as u64).to_be_bytes()
kdf_out = HKDF-SHA256(salt=[0;32], ikm, info, L=64)
root_key = kdf_out[0..32]
mac_key  = kdf_out[32..64]
```

The derived keys satisfy:
1. `root_key.length = 32`
2. `mac_key.length = 32`
3. Both are deterministically derived from `auth_key` and epoch `1`.

**Mathematical characterization**: This is an instance of the HKDF construction
(RFC 5869), which itself is based on HMAC (RFC 2104). The security guarantee is that
if the input key material has sufficient min-entropy, the output is computationally
indistinguishable from uniform random, under the assumption that HMAC-SHA256 is a PRF.

**Current Lean status**: ⚠️ **Partially proved**. The `init_inner_university_spec`
theorem establishes the key length invariants and deterministic derivation:
```lean
ku.uc.auth.root_key.length = 32 ∧
ku.uc.auth.mac_key.length = 32 ∧
∃ v, v.val = auth_key.val ∧
  authenticator.Authenticator.new v 1#u64 = ok ku.uc.auth
```
However, `Authenticator.new_spec` itself uses `sorry` — the proof that `update`
(which calls HKDF) produces 32-byte keys is not yet completed.

**Feasibility in Lean**: ⚠️ **Partially feasible**. The key length invariants are
achievable once the `sorry` in `Authenticator.new_spec` is resolved. However, proving
the cryptographic PRF property of HKDF-SHA256 is **out of scope** for Lean verification
— this is a computational security property that requires a reduction argument, not
a structural proof. The standard approach is to axiomatize HKDF's output length and
treat its security as a trusted assumption.

**References**:
- RFC 5869 — HMAC-based Extract-and-Expand Key Derivation Function (HKDF)
- RFC 2104 — HMAC: Keyed-Hashing for Message Authentication
- Krawczyk, H. "Cryptographic Extraction and Key Derivation: The HKDF Scheme" (2010)
- NIST SP 800-56C Rev. 2 — Recommendation for Key-Derivation Methods

---

### 3.2 Property: Domain Separation

**Statement**: The HKDF info string includes a fixed protocol label
`"Signal_PQCKA_V1_MLKEM768:Authenticator Update"` concatenated with the epoch counter
(big-endian `u64`). This provides **domain separation** — the same `auth_key` used in
different contexts (different epochs, different protocol labels) produces independent keys.

**Mathematical characterization**: For distinct `(label, epoch)` pairs, the HKDF outputs
are independent (under the PRF assumption):
```
∀ label₁ label₂ ep₁ ep₂,
  (label₁, ep₁) ≠ (label₂, ep₂) →
  HKDF(salt, ikm, label₁ ++ ep₁) ⊥ HKDF(salt, ikm, label₂ ++ ep₂)
```
where `⊥` denotes computational independence.

**Current Lean status**: ❌ **Not addressed**. The HKDF function is opaque in the
extraction (`hkdf_to_slice` is declared with `#[hax_lib::opaque]`). The protocol label
is embedded in the Rust source but not visible in the Lean extraction.

**Feasibility in Lean**: ⚠️ **Structurally feasible, cryptographically axiomatized**.
One can state as a Lean axiom that HKDF with distinct info strings produces distinct
outputs (modeling the PRF assumption). Proving this from SHA-256 internals is not
feasible in Lean. The ProVerif models (`proofs/proverif/spqr-cka.pv`) already verify
this property symbolically — the Lean verification would complement that by ensuring the
implementation correctly constructs the info strings.

**References**:
- Krawczyk, H. "Cryptographic Extraction and Key Derivation: The HKDF Scheme" §3.2
- Signal Protocol specification — domain separation conventions

---

### 3.3 Property: Epoch Initialization at 1

**Statement**: Both A-side and B-side initial states set `epoch = 1` (not 0).

**Mathematical characterization**:
```
-- A2B branch:
∃ ku, s = States.KeysUnsampled ku ∧ ku.uc.epoch = 1#u64

-- B2A branch:
∃ nhr, s = States.NoHeaderReceived nhr ∧ nhr.uc.epoch = 1#u64
```

Epoch 0 is reserved for the initial chain key derivation (see `Chain::new` in
`src/chain.rs`, which sets `current_epoch: 0`). Starting the protocol state at epoch 1
ensures the first protocol operation increments to a distinct epoch, preventing key reuse.

**Current Lean status**: ✅ **Proved** in `init_inner_university_spec`:
```lean
ku.uc.epoch = 1#u64      -- A2B branch
nhr.uc.epoch = 1#u64     -- B2A branch
```

**Feasibility in Lean**: ✅ **Already done**.

**References**:
- Signal PQXDH specification — epoch numbering convention

---

## 4. Security Properties

### 4.1 Property: No Secret Material in V0 State

**Statement**: When `version = V0`, the returned state is an empty byte vector `[]`.
No cryptographic keys, authenticator state, or other secret material is embedded.

**Security relevance**: This ensures that the V0 (disabled) mode does not inadvertently
leak key material or create an attack surface. An attacker observing a V0 state learns
nothing about the `auth_key`.

**Current Lean status**: ✅ **Proved** — the V0 branch returns `empty_state()` which is
`Vec::new()`, i.e., an empty list.

**Feasibility in Lean**: ✅ **Already done**.

---

### 4.2 Property: auth_key Confidentiality in V1 State

**Statement**: In the V1 branch, the raw `auth_key` is **not** directly stored in the
serialized state. Instead, the state contains:
1. A clone of `auth_key` in the `version_negotiation` sub-message (for future
   version re-negotiation on `recv`).
2. HKDF-derived keys (`root_key`, `mac_key`) in the `Authenticator`, which are
   one-way derived from `auth_key`.

**Security relevance**: The `version_negotiation.auth_key` field does store the raw
`auth_key` (for version negotiation purposes). This means the serialized state is
**sensitive** and must be protected. If the serialized state is compromised, the
`auth_key` is exposed.

**Mathematical characterization**:
```
∀ params, params.version = V1 →
  let state := initial_state params in
  -- The version_negotiation sub-message contains auth_key
  state.version_negotiation.auth_key = params.auth_key.to_vec()
  -- The inner authenticator contains one-way derived keys
  ∧ state.inner.auth.root_key = HKDF(auth_key, 1)[0..32]
  ∧ state.inner.auth.mac_key  = HKDF(auth_key, 1)[32..64]
```

**Current Lean status**: ⚠️ **Partially addressed**. The `initial_state_spec` constructs
the protobuf with `auth_key := v` where `v` is the cloned key. The `init_inner_university_spec`
establishes the HKDF derivation relationship. However, no theorem explicitly states that
`root_key` and `mac_key` are computationally one-way from `auth_key`.

**Feasibility in Lean**: ⚠️ **Structural part feasible, computational part axiomatized**.
The structural facts (what fields contain what values) are provable. The one-wayness of
HKDF is a computational assumption that must be axiomatized.

**References**:
- Signal Protocol — state storage security model
- RFC 5869 §3 — security analysis of HKDF

---

### 4.3 Property: chain = None at Initialization

**Statement**: The initial state has `chain: None` — no key chain is constructed until
the first `send` or `recv` operation.

**Security relevance**: This ensures no message keys are derivable from the initial state
alone. The chain is only created (via `chain_from_version_negotiation`) when the first
message is sent or received, and epoch secrets are only added as the protocol progresses.

**Mathematical characterization**:
```
∀ params, initial_state params = ok state →
  decode_state state = ok pb →
  pb.chain = none
```

**Current Lean status**: ✅ **Proved** — the `initial_state_spec` explicitly constructs
the protobuf with `chain := none`.

**Feasibility in Lean**: ✅ **Already done**.

---

### 4.4 Property: Version Negotiation Metadata Preservation

**Statement**: The initial V1 state preserves all `Params` fields in the
`version_negotiation` sub-message, enabling correct future negotiation.

**Mathematical characterization**:
```
state.version_negotiation = some {
  auth_key := params.auth_key.to_vec(),
  direction := params.direction.into(),
  min_version := params.min_version.into(),
  chain_params := some (params.chain_params.into_pb())
}
```

**Security relevance**: Correct version negotiation is critical — if `min_version` is
not faithfully stored, the protocol could be downgraded below the minimum acceptable
version, enabling downgrade attacks.

**Current Lean status**: ✅ **Proved** in `initial_state_spec` — the protobuf is
constructed with exactly these fields.

**Feasibility in Lean**: ✅ **Already done**.

---

### 4.5 Property: Direction-Dependent State Machine Initialization

**Statement**: The direction parameter determines the initial state machine variant:
- `A2B` → `States.KeysUnsampled` (ready to sample ML-KEM keys and send headers)
- `B2A` → `States.NoHeaderReceived` (waiting to receive headers)

**Security relevance**: Mismatched initial states between parties would prevent the
protocol from completing. Both parties must agree on who sends EK (A-side) and who sends
CT (B-side).

**Mathematical characterization**:
```
direction = A2B → inner = some (Inner.V1 { inner_state = some (KeysUnsampled ...) })
direction = B2A → inner = some (Inner.V1 { inner_state = some (NoHeaderReceived ...) })
```

**Current Lean status**: ✅ **Proved** in `init_inner_university_spec` (Universality
Properties 4–5):
```lean
-- A2B: ∃ pb_ku, vs.inner_state = some (.KeysUnsampled pb_ku)
-- B2A: ∃ pb_nhr, vs.inner_state = some (.NoHeaderReceived pb_nhr)
```

**Feasibility in Lean**: ✅ **Already done**.

---

### 4.6 Property: Forward Secrecy Foundation

**Statement**: The initial state establishes the **root** of the forward secrecy chain.
The `Authenticator.new(auth_key, 1)` call derives keys from `auth_key` via HKDF, and
subsequent `Authenticator.update(ep, k)` calls derive new keys from the current
`root_key` and a fresh shared secret `k`. The old `root_key` is overwritten, providing
forward secrecy: compromising the current state does not reveal past `root_key` values.

**Mathematical characterization** (ratchet invariant):
```
root_key[n] = HKDF(root_key[n-1] ++ k[n], info[n])[0..32]
mac_key[n]  = HKDF(root_key[n-1] ++ k[n], info[n])[32..64]
```
where `root_key[0] = [0; 32]` (initial zero key) and `k[1] = auth_key`.

Erasing `root_key[n-1]` after computing `root_key[n]` breaks the chain backwards,
because HKDF (under the PRF assumption) is computationally irreversible.

**Current Lean status**: ❌ **Not addressed at the `initial_state` level**. The
`init_inner_university_spec` establishes the initial key derivation, but the ratchet
invariant across multiple epochs is not yet formalized.

**Feasibility in Lean**: ⚠️ **Partially feasible**. The structural ratchet invariant
(each `update` replaces `root_key` with a fresh HKDF output) can be stated and proved
structurally. The security claim (computational irreversibility) is a cryptographic
assumption that must be axiomatized. The ProVerif model (`proofs/proverif/spqr-cka.pv`)
already verifies forward secrecy at the symbolic level.

**References**:
- Cohn-Gordon et al. "On Post-Compromise Security" (IEEE S&P 2020)
- Signal Protocol — Double Ratchet Algorithm specification
- `proofs/proverif/spqr-cka.pv` lines 73–79 (`recvCT2` updates authenticator)
- `proofs/proverif/spqr-dr.pv` — Double Ratchet security model

---

## 5. Serialization / Round-Trip Properties

### 5.1 Property: Encode-Decode Round-Trip

**Statement**: The state produced by `initial_state` can be correctly decoded by
`decode_state`:
```
∀ params, initial_state params = ok (Result.Ok bytes) →
  decode_state bytes = ok pb →
  pb.inner = init_inner(params.version, params.direction, params.auth_key) ∧
  pb.chain = none ∧
  pb.version_negotiation = <constructed from params>
```

**Current Lean status**: ❌ **Not proved**. The protobuf `encode_to_vec` and `decode`
are both opaque (sorry'd in `aeneas-config.yml`). This property requires either:
1. Proving protobuf round-trip correctness (infeasible — prost-generated code), or
2. Axiomatizing the round-trip property.

**Feasibility in Lean**: ⚠️ **Axiomatizable**. The standard approach is to declare:
```lean
axiom protobuf_round_trip :
  ∀ (pb : PqRatchetState),
    PqRatchetState.decode (pb.encode_to_vec) = ok pb
```
This is a reasonable trusted assumption for a well-tested protobuf library.

**References**:
- Protocol Buffers Language Guide v3 — deterministic serialization
- `aeneas-config.yml` lines 86–87 (prost `Message` bodies sorry'd)

---

### 5.2 Property: Structural Completeness of Serialized State

**Statement**: All `Option` fields in the serialized protobuf sub-state are `some`
(not `none`), ensuring the message is structurally complete for deserialization.

**Current Lean status**: ✅ **Proved** in `into_pb_spec` and `into_pb_university_spec`:
```lean
-- KeysUnsampled: ∃ uc_inner, pb_ku.uc = some uc_inner
-- NoHeaderReceived: (∃ uc_inner, pb_nhr.uc = some uc_inner) ∧ (∃ pd, pb_nhr.receiving_hdr = some pd)
```

**Feasibility in Lean**: ✅ **Already done**.

---

## 6. Properties Relating to the ProVerif Security Model

The ProVerif model in `proofs/proverif/spqr-cka.pv` provides a symbolic security
analysis. The following table maps ProVerif concepts to `initial_state` properties:

| ProVerif Concept | `initial_state` Correspondence | Lean Status |
|-----------------|-------------------------------|-------------|
| `NeedToSample(ep)` | `States.KeysUnsampled` (A2B, epoch=1) | ✅ Proved |
| `Waiting(ep)` | `States.NoHeaderReceived` (B2A, epoch=1) | ✅ Proved |
| `auth_update(auth, k)` | `Authenticator.new(auth_key, 1)` | ⚠️ `sorry` in `new_spec` |
| `mac(auth, ...)` | `mac_ct` / `mac_hdr` (not called at init) | N/A at init |
| `kem_keygen()` | Not called at init (deferred to `send`) | N/A at init |

The ProVerif model assumes the initial state is correctly constructed (honest parties
start with the correct initial state). The Lean verification of `initial_state` provides
the **implementation correctness** guarantee that complements the ProVerif **protocol
security** guarantee.

---

## 7. Summary of Properties and Lean Feasibility

| # | Property | Category | Lean Status | Feasibility |
|---|----------|----------|-------------|-------------|
| 2.1 | Totality (no panics) | Mathematical | ⚠️ Conditional | ✅ Achievable (needs `encode_to_vec` axiom) |
| 2.2 | Determinism | Mathematical | ✅ By construction | ✅ Trivial |
| 2.3 | V0 → empty state | Mathematical | ✅ Proved | ✅ Done |
| 3.1 | HKDF key derivation correctness | Cryptographic | ⚠️ `sorry` in `new_spec` | ⚠️ Structural part feasible |
| 3.2 | Domain separation | Cryptographic | ❌ Not addressed | ⚠️ Axiomatizable |
| 3.3 | Epoch = 1 | Cryptographic | ✅ Proved | ✅ Done |
| 4.1 | No secrets in V0 | Security | ✅ Proved | ✅ Done |
| 4.2 | auth_key confidentiality | Security | ⚠️ Partial | ⚠️ Structural feasible |
| 4.3 | chain = None at init | Security | ✅ Proved | ✅ Done |
| 4.4 | Version negotiation preservation | Security | ✅ Proved | ✅ Done |
| 4.5 | Direction-dependent initialization | Security | ✅ Proved | ✅ Done |
| 4.6 | Forward secrecy foundation | Security | ❌ Not addressed | ⚠️ Structural feasible |
| 5.1 | Encode-decode round-trip | Serialization | ❌ Not proved | ⚠️ Axiomatizable |
| 5.2 | Structural completeness | Serialization | ✅ Proved | ✅ Done |

---

## 8. Recommended Next Steps

### 8.1 Close the `sorry` in `Authenticator.new_spec`

The most impactful next step is resolving the `sorry` in
`Spqr/Specs/Authenticator/Authenticator/New.lean` (line 82). This blocks:
- Property 3.1 (HKDF key derivation correctness)
- Downstream composition of `init_inner_university_spec` without axioms

The proof likely requires:
1. Unfolding `new` to expose the `update` call.
2. Applying the `update_spec` (which itself may need `sorry` resolution).
3. The `update` function calls `hkdf_to_vec`, which is opaque — so the proof will
   bottom out at the HKDF output length axiom:
   ```lean
   axiom hkdf_output_length :
     ∀ salt ikm info len, (hkdf_to_vec salt ikm info len).length ≥ len
   ```

### 8.2 State the Protobuf Round-Trip Axiom

Declare a trusted axiom for protobuf encode-decode round-trip to unblock Property 5.1:
```lean
axiom protobuf_encode_decode_roundtrip :
  ∀ (pb : proto.pq_ratchet.PqRatchetState),
    proto.pq_ratchet.PqRatchetState.decode (pb.encode_to_vec) = ok pb
```

### 8.3 Strengthen `initial_state_spec` to a "University Spec"

Following the pattern of `init_inner_university_spec`, create an
`initial_state_university_spec` that composes all sub-operation specs and
propagates the universality properties (epoch = 1, key lengths = 32,
variant preservation, structural completeness) through the full
`initial_state` pipeline. This would give callers a single theorem to
invoke rather than needing to manually compose multiple specs.

### 8.4 Formalize the Ratchet Invariant

Define a Lean predicate capturing the ratchet chain structure:
```lean
def ratchet_invariant (states : List AuthenticatorState) : Prop :=
  ∀ i, i + 1 < states.length →
    states[i+1] = HKDF(states[i].root_key ++ k[i+1], info[i+1])
```
This would enable compositional proofs across multiple `send`/`recv` steps,
connecting the `initial_state` as the base case of the induction.

---

## 9. References

1. **RFC 5869** — HMAC-based Extract-and-Expand Key Derivation Function (HKDF).
   H. Krawczyk, P. Eronen. May 2010.
2. **RFC 2104** — HMAC: Keyed-Hashing for Message Authentication.
   H. Krawczyk, M. Bellare, R. Canetti. February 1997.
3. **NIST FIPS 203** — Module-Lattice-Based Key-Encapsulation Mechanism Standard
   (ML-KEM). August 2024.
4. **NIST SP 800-56C Rev. 2** — Recommendation for Key-Derivation Methods in
   Key-Establishment Schemes. August 2020.
5. **Signal Protocol** — The Double Ratchet Algorithm.
   T. Perrin, M. Marlinspike. November 2016.
6. **Cohn-Gordon et al.** — "On Post-Compromise Security." IEEE S&P 2020.
7. **Krawczyk, H.** — "Cryptographic Extraction and Key Derivation: The HKDF Scheme."
   Crypto 2010.
8. **ProVerif models** — `proofs/proverif/spqr-cka.pv` (CKA security),
   `proofs/proverif/spqr-dr.pv` (Double Ratchet security).
9. **Lean spec files** —
   - `Spqr/Specs/Lib/InitialState.lean`
   - `Spqr/Specs/Lib/InitInner.lean`
   - `Spqr/Specs/V1/Chunked/States/States/InitA.lean`
   - `Spqr/Specs/V1/Chunked/States/States/InitB.lean`
   - `Spqr/Specs/Authenticator/Authenticator/New.lean`
   - `Spqr/Specs/V1/Chunked/States/Serialize/States/IntoPb.lean`
