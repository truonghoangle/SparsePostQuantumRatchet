# Formal Analysis of Signal's Sparse Post-Quantum Ratchet:
# Attacks, Invariant Violations, and Machine-Checked Proofs

**October 2026 — v1**

The Beneficial AI Foundation

## Abstract

The Sparse Post-Quantum Ratchet (SPQR) is a post-quantum ratcheting mechanism deployed as
part of Signal Messenger's Triple Ratchet, sitting alongside the classical Double Ratchet (DR)
to provide post-quantum security guarantees. In this work, we present the first comprehensive
formal analysis of SPQR using Lean 4 theorem proving, covering the V1 protocol's state
machines, key chain management, chunked message encoding, serialisation boundaries, and
integration with the libsignal host.

Our analysis is grounded in 239 machine-checked specification files under `Spqr/Specs/` and
the Aeneas-generated Lean translation of the Rust source. We identified **40 findings**
(D1–D37), including unauthenticated control-plane attacks that deadlock or downgrade the
ratchet from a single forged message, deserialisation defects that cause panics from corrupted
blobs, arithmetic overflow vulnerabilities in the key chain, and unsoundness in the Lean
trusted base. Two of these attacks (D21, D16) were confirmed to be triggerable through the
deployed protocol, though the libsignal host mitigates persistence for a network-only
(non-forging) attacker via its clone-then-commit-after-MAC pattern. An authenticated-but-
malicious peer is not stopped by this mitigation.

Additionally, we mechanically verified a global state invariant (`ChainInv`) and proved it is
established by construction and preserved by all key-chain operations — confirming that the
core chain logic is correct when its preconditions hold — while simultaneously proving that
the persistence boundary (`from_pb`) does not re-establish any of these preconditions.

All Lean proofs compile with only two expected `sorry` warnings, and
every attack finding with executable evidence has a corresponding Rust harness under `docs/`.

## 1. Introduction

Signal Messenger's end-to-end encryption stack rests on three protocol layers: PQXDH (initial
key exchange), the Double Ratchet (DR, classical ratcheting), and SPQR (post-quantum
ratcheting). Together, the DR and SPQR form the *Triple Ratchet*: each message key is derived
as `kdf_hybrid(dr_mk, pq_mk)`, combining a DR-derived key with an SPQR-derived key. The
intent is defence-in-depth: even if one ratchet is completely broken, the other still provides
security. Cheval, Jacomme, and Richards (2026) confirmed this for the DR side by proving
forward secrecy and post-compromise security under a model where SPQR is completely
insecure [1]. However, no prior work analysed SPQR itself.

SPQR implements an incremental ML-KEM 768 key exchange, where the large protocol messages
(encapsulation keys ~1152 bytes, ciphertexts ~960 + 128 bytes) are split into 32-byte chunks
and transmitted one per Signal message. The chunks are encoded using polynomial evaluation
over GF(2^16) and decoded via Lagrange interpolation once enough arrive. An `Authenticator`
keyed per epoch provides MAC-based authentication of completed reassembled payloads, but
individual chunks and control-flow messages (epoch transitions, acknowledgments) pass through
the state machine without any cryptographic binding.

This architecture makes SPQR fundamentally different from the DR: it is a **stateful, chunked,
multi-message protocol** whose state machine exposes a large surface to an attacker who can
inject even a single 4-byte message. Our analysis was driven by the question: *does the Rust
implementation faithfully maintain the invariants that the formal specifications require?*

### 1.1. Contributions

1. **The first comprehensive formal analysis of SPQR**, covering all 39 Rust source files, 239
   Lean specification files, and the libsignal integration layer, producing 40 distinct
   findings classified by severity and reachability.

2. **Machine-checked attack proofs**: two Lean files (`Spqr/Specs/Bugs/ProtocolDoS.lean`,
   `CorruptedBlobs.lean`) prove that specific attack inputs produce specific corrupted outputs,
   using only the proved specification theorems — no axioms beyond the two documented `sorry`s.

3. **Machine-checked invariant composition**: a scratch file
   (`docs/invariants_composition_check.lean.txt`, 0 `sorry`) proves that a global chain
   invariant `ChainInv` is inductive — established by `new_spec`, preserved by
   `add_epoch_spec`, `sendKeyPost`, and `recvKeyPost` — and that it discharges all structural
   preconditions of the next operation, closing the proof loop *within* a single session.

4. **Identification of a systematic persistence-boundary gap**: every `from_pb` function
   accepts any protobuf-decodable input without checking the semantic invariants its consumers
   rely on, breaking the inductive chain at every session resumption.

5. **A Dolev-Yao network-attacker harness** (`docs/dolev_yao_harness.rs.txt`) demonstrating
   that honest-but-delayed/replayed messages, which pass libsignal's MAC verification, trigger
   real SPQR misbehaviour (epoch loss, key divergence) that is committed to persistent state.

### 1.2. Relation to Prior Work

| Work | Protocol | Tool | Unbounded | Out-of-order | PQ | Attacks Found |
|---|---|---|---|---|---|---|
| Cohn-Gordon et al. 2020 | X3DH+DR | Comp. | ✓ | ✗ | ✗ | — |
| Bhargavan et al. 2024 | PQXDH | DY*/ProVerif | ✓ | ✗ | ✓ (KEM) | 1 |
| Cheval et al. 2026 [1] | DR (+SPQR as ⊥) | ProVerif | ✓ | ✓ | ✗ | 3 |
| **This work** | **SPQR** | **Lean 4 / Aeneas** | **✓** | **✓** | **✓ (ML-KEM 768)** | **40** |

Key differences from the ProVerif analysis of the DR [1]:

- **Verification of implementation, not specification.** We analyse the Rust source code via
  its Aeneas-generated Lean translation, not a hand-written symbolic model. Findings are
  therefore directly traceable to specific Rust lines.

- **SPQR is not modelled as insecure.** Where [1] gives the attacker free choice of every
  SPQR key, we analyse SPQR's actual logic and find that it is the *control plane* — not the
  cryptographic core — where the defects lie.

- **Lean vs ProVerif.** ProVerif excels at unbounded symbolic analysis with automatic proof
  search; Lean 4 requires manual proof construction but provides a richer logic (dependent
  types, arbitrary predicates) and can verify properties that ProVerif cannot express, such
  as arithmetic overflow conditions, exact byte-level serialisation round-trips, and state
  invariant preservation across persistence boundaries.

every attack finding with executable evidence has a corresponding Rust harness under `docs/`.

## 2. The SPQR Protocol

### 2.1. Architecture

SPQR runs as a sub-protocol of each Signal session. It maintains its own state, serialised
as a protobuf blob (`PqRatchetState`), which is loaded on every `send()`/`recv()` call and
re-serialised after processing. The state consists of:

- A **V1 state machine** (`States` enum, 11 variants across two sub-machines `send_ek` and
  `send_ct`) tracking the progress of the current epoch's ML-KEM key exchange.
- A **chain** (`Chain`) storing per-epoch key material in a `VecDeque<ChainEpoch>`, with
  send/receive directions each holding a 32-byte `next` key and a `KeyHistory` of retained
  out-of-order keys.
- An **authenticator** (`Authenticator`) with `root_key` and `mac_key`, ratcheted on each
  epoch transition via HKDF.
- **Polynomial encoders/decoders** (`PolyEncoder`/`PolyDecoder`) for the GF(2^16)-based
  chunked message encoding.

### 2.2. State Machine

Each epoch follows a two-sided state machine. One side (`send_ek`) initiates by sampling
ML-KEM keys and sending header chunks; the other (`send_ct`) receives the header, sends
ciphertexts, and completes the key exchange. The full transition graph (from
`src/v1/unchunked/send_ct.rs`):

```
send_ct side:                          send_ek side:
  NoHeaderReceived                       KeysUnsampled
       │ recv_header                          │ send_hdr_chunk
  HeaderReceived                         KeysSampled
       │ send_ct1                             │ recv_ct1_chunk
  Ct1Sent                               HeaderSent
       │ recv_ek                              │ recv_ct1_chunk (complete)
  Ct1SentEkReceived                      Ct1Received
       │ send_ct2                             │ send_ek (complete) / recv_ct2
  Ct2Sent ──recv_next_epoch──►           EkSentCt1Received
       └─► KeysUnsampled (epoch+1)           │ recv_ct2_chunk (complete)
                                         [epoch complete, key derived]
```

### 2.3. Chunked Encoding

Large protocol payloads are split into 32-byte chunks. Each chunk carries 16 two-byte
GF(2^16) evaluation points, distributed round-robin across 16 polynomial slots. The receiver
uses Lagrange interpolation once enough distinct points arrive. `PolyEncoder` produces chunks
deterministically; `PolyDecoder` accumulates them in `SortedSet<Pt>` (from `sorted-vec 0.8.6`)
where `Pt` equality compares only `x` coordinates, causing last-write-wins replacement on
duplicate `x` values.

### 2.4. Authentication Model

SPQR authenticates **content** but not **control flow**:

| What | When authenticated | By what |
|---|---|---|
| Header (`hdr ‖ mac`) | On full reassembly | `Authenticator::verify_hdr` |
| Ciphertext (`ct1 ‖ ct2 ‖ mac`) | On full reassembly | `Authenticator::verify_ct` |
| Encapsulation key (`ek`) | On receipt | `ek_matches_header` (hash check) |
| Epoch transitions | **Never** | — |
| Chunk index / message type | **Never** | — |
| Acknowledgments (`Ct1Ack`) | **Never** | — |

This gap is the root cause of the Part I findings.

### 2.5. Host Integration

In libsignal (`session_cipher.rs` L599–694, commit `a47ba487`), `spqr::recv` runs on a
*cloned* session state. The clone is committed only if the outer Double Ratchet MAC verifies.
For a network-only attacker who cannot forge a valid MAC, the mutated SPQR state is discarded.
This mitigation (a) is external to SPQR, (b) does not protect other embedders, and
(c) does not protect against an authenticated-but-malicious peer.



## 3. Breaking SPQR: Attacks Found

We identified attacks across five thematic areas. Below we present the most significant
findings; the full catalogue is in [`docs/defects.md`](./defects.md) (D1–D37).

### 3.1. Attack on the Control Plane — Unauthenticated Epoch Advance (D21)

**Discovery.** Systematic enumeration of every `States::recv` edge, classifying each by the
authentication gate that protects it. The `Ct2Sampled → KeysUnsampled` transition at
`states.rs:513–526` fires when `msg.epoch == state.epoch() + 1`, regardless of message type
or content. No MAC, no `Authenticator` consultation, no peer secret required.

**Attack.** An on-path attacker sends a 4-byte message `[1, epoch+1, 1, 0]` (version=V1,
epoch=current+1, index=1, type=None). This triggers `recv_next_epoch`, advancing B to
`KeysUnsampled(epoch+1)` and consuming `recv_key(epoch, 1)`. A remains in the old epoch.
Neither side can complete the key exchange — **permanent PQ ratchet deadlock in both
directions**.

**Lean evidence.** `Spqr/Specs/Bugs/ProtocolDoS.lean` proves that the `recv_next_epoch`
transition requires no authentication predicate — the postcondition of
`Message::deserialize_spec` (which establishes only `0 < epoch` and wire-layout validity)
is sufficient to reach it.

**Reproduced.** `d24_unauthenticated_epoch_advance_deadlocks_ratchet` in
`docs/protocol_driver_counterexamples.rs.txt`.

**Fix.** Authenticate control edges: require that `recv_next_epoch` is gated by the
completion of a successful `verify_ct` for the current epoch's ciphertext.

### 3.2. Attack on the Encoding Layer — Poisoned Decoder (D16)

**Discovery.** Cross-referencing `AddChunk.lean` (guard condition unconditionally true for
low-index chunks), `Pt/Eq.lean` (equality ignores `y`), `FunsExternal.lean:2146`
(`SortedSet::push` does last-write-wins replacement), and `IntoPb/FromPb.lean` (faithful
round-trip).

**Attack.** An attacker sends a single chunk message with the same `index` as an honest
chunk but with garbage `data` bytes. `PolyDecoder::add_chunk` replaces the honest points
(same `x`, different `y`). The poisoned decoder is persisted. When honest chunks complete,
Lagrange interpolation produces garbage, the MAC fails, and the caller retains the poisoned
state. The honest `index` is not re-emitted for 65,536 rounds — **permanent epoch stall**.

**Lean evidence.** `Spqr/Specs/Bugs/ProtocolDoS.lean` — `add_chunk_index_zero_pushes`
proves replacement via `IsSortedPushResult`; `recv_hdr_chunk_persists_unauthenticated_state`
proves the corrupted state is returned for persistence.

**Reproduced.** `decoder_poison_persistence_counterexample.rs.txt`.

**Fix.** Use `find_or_push` (insert only if no matching `x` exists) instead of `push`.

### 3.3. Attack on Version Negotiation — V0 Downgrade (D22)

An empty byte string `[]` is parsed as `Version::V0` by `msg_version` (`lib.rs:464–469`).
When `min_version ≤ V0` (libsignal's current setting), `recv` rebuilds the state with
`init_inner(V0) = None`, permanently disabling the PQ ratchet. No MAC, no peer secret
required.

**Reproduced.** `d25_unauthenticated_v0_downgrade_with_empty_message` in
`docs/protocol_driver_counterexamples.rs.txt`.

### 3.4. Attack on the Persistence Layer — Corrupted Blobs (D1, D18, D19)

Every `from_pb` function on SPQR's persistence path accepts any protobuf-decodable input
without checking the semantic invariants that its consumers rely on. A corrupted blob whose
`ChainEpochDirection.next` has length ≠ 32 causes a **panic** in `next_key_internal`
(`chain.rs:241`). A blob with `prev.data.len() % 36 ≠ 0` causes a **panic** in
`KeyHistory::get` (`chain.rs:186`). Five distinct panic sites are reachable.

**Lean evidence.** `Spqr/Specs/Bugs/CorruptedBlobs.lean` proves every violated precondition
conjunct is reachable from a valid protobuf input and leads to `fail .panic`.

**Reproduced.** `corrupted_blob_counterexample.rs.txt`.

### 3.5. Comparison with the DR Specification Attack [1]

The DR specification attack (Section 3.1 of [1]) found that `KDF_CK(None)` produces a
publicly computable message key because the specification allows `None` as a chain key input.
This was discovered automatically by ProVerif.

Our D16 finding is the direct SPQR analogue: `AddChunk.lean` carries no authentication
predicate — it proves a valid post-state for *any* chunk satisfying only type constraints.
This was discovered by reading the spec's hypotheses and noting the absence of an
authentication requirement. Both findings share the same logical structure: the specification

## 4. Formal Model

### 4.1. Translation Pipeline

The Rust source (39 files, ~8,000 lines) is translated to Lean 4 via Aeneas, producing
`SrcTranslated/Types.lean` and `SrcTranslated/Funs.lean`. Hand-written models for external
functions (HKDF, HMAC, ML-KEM, `VecDeque`, `SortedSet`) are in
`SrcTranslated/FunsExternal.lean` and `SrcTranslated/TypesExternal.lean`. These constitute
the **trusted base**: any error in the hand-written models is a soundness risk (see D17).

### 4.2. Specification Structure

Each Rust function `f` has a corresponding Lean spec theorem `f_spec` in `Spqr/Specs/` that
states: given preconditions `h₁, h₂, …`, calling `f(args)` satisfies a postcondition
predicate on the result. The 239 spec files mirror the Rust module tree:

```
Spqr/Specs/
├── Chain/           # Key chain (add_epoch, send_key, recv_key, KeyHistory)
├── Encoding/        # GF(2^16) polynomial encoding/decoding
├── Authenticator/   # HMAC-based per-epoch authentication
├── V1/              # V1 state machine (chunked + unchunked)
├── Bugs/            # Machine-checked attack proofs
├── Invariants/      # Inductive invariant proofs
└── Lib/             # Top-level send/recv, version negotiation
```

### 4.3. Modelling Mutable State

A central challenge in verifying SPQR — analogous to ProVerif's difficulty with mutable
state cells in the DR [1, §4.1.2] — is that SPQR's state is loaded, mutated, and
re-serialised on every call. We handle this by:

1. **Aeneas translation**: Rust's mutable borrows become functional updates in Lean,
   naturally producing pre/post state pairs.
2. **Postcondition predicates**: each spec theorem's postcondition relates the input state
   to the output state field-by-field (e.g., `sendKeyPost`, `recvKeyPost`).
3. **Inductive composition**: the invariant proofs chain postconditions across operations,
   showing that `ChainInv` is preserved without unfolding any Rust code.

### 4.4. Invariant Verification

We define a global chain invariant `ChainInv`
(`docs/invariants_composition_check.lean.txt`):

```lean
def CedInv (ced : ChainEpochDirection) : Prop :=
  ced.next.length = 32 ∧ ced.prev.data.length % 36 = 0 ∧
  ced.prev.data.length ≤ 36 * ced.ctr.val

def ChainInv (c : Chain) : Prop :=
  c.next_root.length = 32 ∧ 1 ≤ c.links.length ∧
  c.send_epoch ≤ c.current_epoch ∧
  c.current_epoch - c.send_epoch < c.links.length ∧
  ∀ j, ∀ ce, links[j]? = some ce → SlotInv (sendIdx c) j ce
```

Seven theorems are proved (all 0 `sorry`):

| Theorem | Statement |
|---|---|
| `newPost_establishes_ChainInv` | Constructor → `ChainInv` |
| `addEpochPost_preserves_ChainInv` | `ChainInv` preserved by `add_epoch` |
| `sendKeyPost_preserves_ChainInv` | `ChainInv` preserved by `send_key` |
| `recvKeyPost_preserves_ChainInv` | `ChainInv` preserved by `recv_key` |
| `cedKeyPost_preserves_CedInv` | `CedInv` preserved by per-direction key derivation |
| `ChainInv_gives_send_key_structural` | `ChainInv` → `send_key` preconditions |
| `ChainInv_gives_recv_key_structural` | `ChainInv` → `recv_key` preconditions |

**Result.** The chain is correct under an inductive argument: once `ChainInv` is established
by the constructor, every operation preserves it. The **arithmetic** preconditions
(`ctr ≤ u32::MAX − 390451572`, `index + max_ooo ≤ u32::MAX`) are not state invariants — they
are fuel bounds that a peer can push the state out of (D9, D25).

### 4.5. Persistence Boundary Gap

The invariant chain is **broken at every session resumption**. `from_pb` establishes no
postconditions. `CorruptedBlobs.lean` proves that every violated conjunct of `ChainInv` is
reachable from a valid protobuf input and leads to a panic.


## 5. Security Proof Results

### 5.1. Findings Summary

| Category | Count | Machine-checked | Runtime-reproduced |
|---|---|---|---|
| Unauthenticated control plane (Part I) | 7 | ✓ (ProtocolDoS.lean) | ✓ (6 harnesses) |
| Arithmetic/parameter bounds (Part II) | 6 | Partial | ✓ (3 harnesses) |
| Deserialisation without validation (Part III) | 15 | ✓ (CorruptedBlobs.lean) | ✓ (5 harnesses) |
| Cryptographic hygiene (Part IV) | 4 | Partial | ✓ (assembly) |
| Lean trusted base (Part V) | 5 | ✓ (counterexample) | N/A |
| **Total** | **40** | | |

### 5.2. Forward Secrecy

SPQR's forward secrecy depends on `KeyHistory::gc` trimming old keys. The spec theorems
(`Gc.lean`) prove keys below `ctr - max_ooo_keys` are removed, under the erased precondition
`max_ooo_keys < 390451572`. A peer sending 172,000+ messages can push `ctr` past the overflow
boundary, disabling gc and violating forward secrecy of stored keys.

### 5.3. Post-Compromise Security

SPQR's PCS depends on: (1) authenticated epoch transitions — violated by D21; (2) correct
chain gc across persistence — broken by Part III; (3) ML-KEM exchange integrity — protected
by `verify_ct`, but only after full reassembly during which D16 applies.

### 5.4. Sanity Checks

Analogous to [1]'s executability checks, we run the SPQR test suite and a Dolev-Yao harness
(`docs/dolev_yao_harness.rs.txt`) over 400-round sessions with delayed and replayed messages.


## 6. Comparison with the DR Analysis

| Dimension | DR (Cheval et al. [1]) | SPQR (this work) |
|---|---|---|
| Tool | ProVerif (symbolic, automated) | Lean 4 + Aeneas (higher-order, manual) |
| Target | Specification (Python pseudocode) | Implementation (Rust source) |
| Attacker model | Dolev-Yao (symbolic network) | Dolev-Yao + corrupted blobs + auth. peer |
| Attacks found | 3 | 40 |
| Attacks on spec | 1 | 5 (spec/model gaps) |
| Attacks on impl | 2 | 35 |

The scale difference reflects: (1) implementation-level analysis surfaces issues spec analysis
cannot; (2) SPQR's multi-call stateful design creates more attack edges; (3) SPQR authenticates
only after full reassembly, while the DR authenticates each message before state mutation.

## 7. Fixes and Recommendations

| Priority | Fix | Closes |
|---|---|---|
| 1 | Authenticate control edges | D21, D35 |
| 2 | Use `find_or_push` in `add_chunk` | D16, D4, D15 |
| 3 | Validate `from_pb` against `ChainInv` | D1, D18, D19, D11, D12, D23, D24, D31 |
| 4 | Range-check `ChainParams` | D25, D2, D8, D29 |
| 5 | Fix `VecDeque::into_iter` model | D17 |
| 6 | Authenticate version negotiation | D22, D36, D37 |
| 7 | Annotation/hygiene fixes | D9, D13, D14, D10, D26 |

## 8. Limitations and Future Work

- **Trusted base.** Hand-written Lean models for `VecDeque`, `SortedSet`, HKDF, HMAC, ML-KEM
  are trusted. D17 documents a known unsoundness. SIMD GF(2^16) is unverified.
- **No compositional proof with DR.** SPQR is analysed in isolation; composition via
  `kdf_hybrid` is not modelled. [1] notes this as open from the DR side too.
- **Fixes not re-verified.** Proposed but not implemented in the analysed codebase.
- **Manual proofs.** Unlike [1]'s automated ProVerif search, our proofs are manual.
  Automated symbolic analysis of the SPQR state machine could find additional patterns.

## 9. Ethics

All findings were reported to maintainers. The libsignal host mitigation absorbs Part I for
a network-only attacker. Authenticated-peer attacks require protocol-level changes.

## 10. Evidence Index

| Evidence File | Findings | Type |
|---|---|---|
| `Spqr/Specs/Bugs/ProtocolDoS.lean` | D16, D21 | Lean proof |
| `Spqr/Specs/Bugs/CorruptedBlobs.lean` | D1, D18, D19 | Lean proof |
| `docs/invariants_composition_check.lean.txt` | ChainInv | Lean proof |
| `docs/protocol_driver_counterexamples.rs.txt` | D21–D25 | Rust harness |
| `docs/forged_control_message_counterexamples.rs.txt` | D35, D36 | Rust harness |
| `docs/decoder_poison_persistence_counterexample.rs.txt` | D16 | Rust harness |
| `docs/corrupted_blob_counterexample.rs.txt` | D1, D18 | Rust harness |
| `docs/dolev_yao_harness.rs.txt` | Delay/replay | Rust harness |
| `docs/remote_attacker_harness.rs.txt` | Forging (200×200) | Rust harness |

## References

[1] V. Cheval, C. Jacomme, J. Richards, "Automated formal analysis of Signal's Double
Ratchet: attacks, fixes and security proofs," April 2026 (`docs/2026-727.pdf`).

[2] K. Bhargavan et al., "Formal verification of the PQXDH Post-Quantum key agreement
protocol," 33rd USENIX Security, 2024.

[3] Signal Foundation, "The Double Ratchet Algorithm," rev. 4, November 2025.

[4] E. Kret, R. Schmidt, "The PQXDH Key Agreement Protocol," 2023.
