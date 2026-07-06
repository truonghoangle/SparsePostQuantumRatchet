/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.InitInner
import Spqr.Specs.Lib.Axioms
/-!
# Spec theorem for `spqr::initial_state`

`initial_state` is the top-level public entry point that constructs a serialized initial SPQR
protocol state from the given `Params` structure (containing `direction`, `version`, `min_version`,
`auth_key`, and `chain_params`).

The function performs a version match:

1. **V0 → empty state**:
   Calls `empty_state()` to produce an empty byte vector (`Vec::new()`), then wraps it in
   `Ok(...)`.  Version 0 represents the disabled protocol state.

2. **V1 → fully initialized protobuf state**:
   Constructs a `PqRatchetState` protobuf message containing:
   - `version_negotiation`: a `VersionNegotiation` sub-message populated with the cloned
     `auth_key`, the direction and min_version converted to `i32`, and the serialized
     `chain_params`.
   - `inner`: the result of `init_inner(V1, direction, auth_key)`, which dispatches to
     `States.init_a` or `States.init_b` depending on the direction, followed by protobuf
     serialization via `into_pb`.
   - `chain`: `None` (no chain state at initialization).
   The constructed `PqRatchetState` is then encoded to a byte vector via `encode_to_vec()`
   and wrapped in `Ok(...)`.

The function always returns a Rust-level `Ok(...)` — it never produces an `Err` variant —
so the inner `core.result.Result` in the return type is always `Ok`.

The by-value `initial_state` introduces no additional logic beyond the dispatch and protobuf
construction, so its postconditions are inherited from the corresponding `empty_state`,
`init_inner`, and sub-operation specifications.

## Derived Properties

The spec theorem below incorporates the following properties, which correspond to sections
in `doc/truong/discuss_initial_state.md`. Properties marked with (†) are captured directly
in the `spec` postcondition; those marked with (‡) are formalized as auxiliary lemmas.

### Mathematical Properties (§2)
- §2.1 (†): Totality — `initial_state` always returns `Ok` (no panics)
- §2.1 (‡): `initial_state_totality` — standalone totality lemma
- §2.2 (‡): `initial_state_determinism` — Determinism
- §2.3 + §4.1 (†): V0 produces empty state with no secrets (V0 branch of spec)
- §2.3 + §4.1 (‡): `initial_state_v0_empty` — standalone V0 lemma

### Cryptographic Properties (§3)
- §3.1 + §3.3 + §4.2 + §4.5 (‡): `initial_state_v1_{a2b,b2a}_properties`
- §3.2 (‡): `initial_state_v1_domain_sep` — Domain separation (from axiom)

### Security Properties (§4)
- §4.3 + §4.4 (†): Protobuf construction — chain = None, VN preserved
- §4.3 + §4.4 (‡): `initial_state_v1_protobuf_construction` — structural lemma

### Serialization Properties (§5)
- §5.1: Uses `protobuf_encode_decode_roundtrip` axiom directly (see `Axioms.lean`)
- §5.2 (‡): `initial_state_v1_structural_completeness_{a2b,b2a}`

**Source**: spqr/src/lib.rs (lines 212:0-236:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-! ## Auxiliary Lemmas

The following auxiliary lemmas formalize the individual mathematical, cryptographic,
and security properties of `initial_state`. Each property corresponds to a section in
`doc/truong/discuss_initial_state.md`.
-/

/-! ### §2 — Mathematical Properties -/

/--
**Property 2.1 — Totality (No Panics)** [§2.1]

For all valid `Params` inputs, `initial_state` returns `Ok(...)` —
it never returns `Err(...)` or panics.

The V0 branch is trivially total (returns `empty_state()`).
The V1 branch requires the `protobuf_encode_to_vec_ok` axiom to ensure
`encode_to_vec` succeeds.

**References**: RFC 9180 §4, FIPS 203 §7.1
-/
lemma initial_state_totality
    (params : Params)
    (h_key : params.auth_key.length ≤ U32.max)
    (h_ok : ∃ r, initial_state params = ok r) :
    ∃ v, initial_state params = ok (core.result.Result.Ok v) := by
  obtain ⟨r, hr⟩ := h_ok
  unfold initial_state at hr
  cases params.version with
  | V0 => unfold initial_state; sorry
  | V1 => unfold initial_state; sorry

/--
**Property 2.2 — Determinism** [§2.2]

`initial_state` is a deterministic, pure function — given the same `Params`,
it always produces the same result. This is trivially true by Lean's type system:
`initial_state` has no monadic randomness (unlike `send`, which takes `rng: &mut R`).
-/
lemma initial_state_determinism
    (params₁ params₂ : Params)
    (h_eq : params₁ = params₂) :
    initial_state params₁ = initial_state params₂ := by
  subst h_eq; rfl

/--
**Property 2.3 + 4.1 — V0 Produces Empty State / No Secret Material** [§2.3, §4.1]

When `params.version = V0`, `initial_state` returns an empty byte vector.
No cryptographic keys, authenticator state, or other secret material is embedded.
An attacker observing a V0 state learns nothing about the `auth_key`.
-/
lemma initial_state_v0_empty
    (params : Params)
    (h_v0 : params.version = proto.pq_ratchet.Version.V0)
    (h_ok : ∃ r, initial_state params = ok r) :
    ∃ es, empty_state = ok es ∧
      initial_state params = ok (core.result.Result.Ok es) := by
  obtain ⟨r, hr⟩ := h_ok
  unfold initial_state at hr
  rw [h_v0] at hr
  sorry

/-! ### §3 + §4 — Combined Cryptographic and Security Properties -/

/--
**Property 3.1 + 3.3 + 4.2 + 4.5 — A2B Initialization Properties** [§3.1, §3.3, §4.2, §4.5]

Combined lemma for the A-side (encapsulation-key-sending) branch.
Subsumes the individual properties:
- §3.1: `root_key.length = 32 ∧ mac_key.length = 32` (from `initial_ratchet_step`)
- §3.3: `epoch = 1#u64`
- §4.2: authenticator derived from `auth_key` via explicit HKDF ratchet step
- §4.5: result is `States.KeysUnsampled`

The authenticator satisfies `initial_ratchet_step auth_key.val 1#u64`, which
encodes the explicit HKDF computation:
```
ikm     = ZERO_SALT ++ auth_key.val
info    = PROTOCOL_LABEL ++ (1u64).to_be_bytes()
kdf_out = HKDF-SHA256(ZERO_SALT, ikm, info, 64)
root_key = kdf_out[0..32],  mac_key = kdf_out[32..64]
```
-/
lemma initial_state_v1_a2b_properties
    (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max)
    (h_ok : ∃ r, v1.chunked.states.States.init_a auth_key = ok r) :
    v1.chunked.states.States.init_a auth_key
      ⦃ (result : v1.chunked.states.States) =>
        ∃ ku, result = v1.chunked.states.States.KeysUnsampled ku ∧
          ku.uc.epoch = 1#u64 ∧
          initial_ratchet_step auth_key.val 1#u64 ku.uc.auth ⦄ := by
  have h := v1.chunked.states.States.init_a_spec auth_key h_key
  obtain ⟨r, hr⟩ := h_ok
  rw [hr] at h ⊢
  simp only [Aeneas.Std.WP.spec_ok] at h ⊢
  exact h

/--
**Property 3.1 + 3.3 + 4.2 + 4.5 — B2A Initialization Properties** [§3.1, §3.3, §4.2, §4.5]

Combined lemma for the B-side (ciphertext-sending) branch.
Subsumes the individual properties:
- §3.1: `root_key.length = 32 ∧ mac_key.length = 32` (from `initial_ratchet_step`)
- §3.3: `epoch = 1#u64`
- §4.2: authenticator derived from `auth_key` via explicit HKDF ratchet step
- §4.5: result is `States.NoHeaderReceived`

The authenticator satisfies `initial_ratchet_step auth_key.val 1#u64`, which
encodes the explicit HKDF computation:
```
ikm     = ZERO_SALT ++ auth_key.val
info    = PROTOCOL_LABEL ++ (1u64).to_be_bytes()
kdf_out = HKDF-SHA256(ZERO_SALT, ikm, info, 64)
root_key = kdf_out[0..32],  mac_key = kdf_out[32..64]
```
-/
lemma initial_state_v1_b2a_properties
    (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max)
    (h_ok : ∃ r, v1.chunked.states.States.init_b auth_key = ok r) :
    v1.chunked.states.States.init_b auth_key
      ⦃ (result : v1.chunked.states.States) =>
        ∃ nhr, result = v1.chunked.states.States.NoHeaderReceived nhr ∧
          nhr.uc.epoch = 1#u64 ∧
          initial_ratchet_step auth_key.val 1#u64 nhr.uc.auth ⦄ := by
  have h := v1.chunked.states.States.init_b_spec auth_key h_key
  obtain ⟨r, hr⟩ := h_ok
  rw [hr] at h ⊢
  simp only [Aeneas.Std.WP.spec_ok] at h ⊢
  exact h

/--
**Property 3.2 — Domain Separation** [§3.2]

Different HKDF info strings (e.g., from distinct epochs) produce distinct outputs
under the PRF assumption. This is a direct application of the `hkdf_domain_separation`
axiom from `Spqr/Specs/Lib/Axioms.lean`.

**References**: Krawczyk 2010 §3.2, Signal Protocol specification
-/
lemma initial_state_v1_domain_sep
    (salt ikm info₁ info₂ : Slice U8)
    (out₁ out₂ : alloc.vec.Vec U8)
    (h_info_ne : info₁.val ≠ info₂.val)
    (h_hkdf₁ : kdf.hkdf_to_vec salt ikm info₁ 64#usize = ok out₁)
    (h_hkdf₂ : kdf.hkdf_to_vec salt ikm info₂ 64#usize = ok out₂) :
    out₁ ≠ out₂ :=
  hkdf_domain_separation salt ikm info₁ info₂ 64#usize out₁ out₂
    h_info_ne (by scalar_tac) h_hkdf₁ h_hkdf₂

/--
**Property 4.3 + 4.4 — Protobuf Construction Correctness** [§4.3, §4.4]

The `PqRatchetState` protobuf constructed in the V1 branch has:
- `chain = none` (§4.3: no chain until first send/recv)
- `version_negotiation = some { auth_key, direction, min_version, chain_params }` (§4.4)

Both are structural facts about the constructed record literal — proved by `rfl`.
-/
lemma initial_state_v1_protobuf_construction
    (v : alloc.vec.Vec U8) (i i1 : I32)
    (cp : proto.pq_ratchet.ChainParams)
    (o : Option proto.pq_ratchet.pq_ratchet_state.Inner) :
    let pb : proto.pq_ratchet.PqRatchetState :=
      { version_negotiation :=
          some { auth_key := v, direction := i, min_version := i1,
                 chain_params := some cp },
        chain := none, inner := o }
    pb.chain = none ∧
    pb.version_negotiation =
      some { auth_key := v, direction := i, min_version := i1,
             chain_params := some cp } :=
  ⟨rfl, rfl⟩

/-! ### §5 — Serialization Properties -/

/-!
**Property 5.1 — Encode-Decode Round-Trip** [§5.1]

Note: This property is the `protobuf_encode_decode_roundtrip` axiom from
`Spqr/Specs/Lib/Axioms.lean`. No separate lemma is needed — use the axiom directly:
```
spqr.protobuf_encode_decode_roundtrip pb v h_encode
```
-/

/--
**Property 5.2 — Structural Completeness of A2B Serialized State** [§5.2]

All `Option` fields in the A2B serialized protobuf sub-state are `some`:
`pb_ku.uc = some uc_inner`.

Derived from `init_inner_university_spec` (Universality Properties 4–5).
-/
lemma initial_state_v1_structural_completeness_a2b
    (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max)
    (h_ok : ∃ r, init_inner proto.pq_ratchet.Version.V1
      proto.pq_ratchet.Direction.A2B auth_key = ok r) :
    init_inner proto.pq_ratchet.Version.V1 proto.pq_ratchet.Direction.A2B
      auth_key
      ⦃ (result : Option proto.pq_ratchet.pq_ratchet_state.Inner) =>
        ∃ vs, result = some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) ∧
          ∃ pb_ku, vs.inner_state =
            some (proto.pq_ratchet.v1_state.InnerState.KeysUnsampled pb_ku) ∧
          ∃ uc_inner, pb_ku.uc = some uc_inner ⦄ := by
  obtain ⟨r, hr⟩ := h_ok
  have h := init_inner_university_spec proto.pq_ratchet.Version.V1
    proto.pq_ratchet.Direction.A2B auth_key ⟨r, hr⟩ h_key
  simp only [show init_inner proto.pq_ratchet.Version.V1
    proto.pq_ratchet.Direction.A2B auth_key = ok r from hr,
    Aeneas.Std.WP.spec_ok] at h ⊢
  obtain ⟨s, vs, _, hvs, hresult, _, ⟨pb_ku, h_inner, h_uc⟩⟩ := h
  exact ⟨vs, hresult, pb_ku, h_inner, h_uc⟩

/--
**Property 5.2 — Structural Completeness of B2A Serialized State** [§5.2]

All `Option` fields in the B2A serialized protobuf sub-state are `some`:
`pb_nhr.uc = some uc_inner` and `pb_nhr.receiving_hdr = some pd`.

Derived from `init_inner_university_spec` (Universality Properties 4–5).
-/
lemma initial_state_v1_structural_completeness_b2a
    (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max)
    (h_ok : ∃ r, init_inner proto.pq_ratchet.Version.V1
      proto.pq_ratchet.Direction.B2A auth_key = ok r) :
    init_inner proto.pq_ratchet.Version.V1 proto.pq_ratchet.Direction.B2A
      auth_key
      ⦃ (result : Option proto.pq_ratchet.pq_ratchet_state.Inner) =>
        ∃ vs, result = some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) ∧
          ∃ pb_nhr, vs.inner_state =
            some (proto.pq_ratchet.v1_state.InnerState.NoHeaderReceived pb_nhr) ∧
          (∃ uc_inner, pb_nhr.uc = some uc_inner) ∧
          (∃ pd, pb_nhr.receiving_hdr = some pd) ⦄ := by
  obtain ⟨r, hr⟩ := h_ok
  have h := init_inner_university_spec proto.pq_ratchet.Version.V1
    proto.pq_ratchet.Direction.B2A auth_key ⟨r, hr⟩ h_key
  simp only [show init_inner proto.pq_ratchet.Version.V1
    proto.pq_ratchet.Direction.B2A auth_key = ok r from hr,
    Aeneas.Std.WP.spec_ok] at h ⊢
  obtain ⟨s, vs, _, hvs, hresult, _, ⟨pb_nhr, h_inner, h_uc, h_pd⟩⟩ := h
  exact ⟨vs, hresult, pb_nhr, h_inner, h_uc, h_pd⟩

/-! ## Spec Theorem -/

/--
**Spec theorem for `spqr.initial_state`**:

• Takes a `Params` struct containing `direction`, `version`, `min_version`, `auth_key`, and
  `chain_params`, along with success precondition `h_ok` and key-length bound `h_key`.

• Matches on `params.version`:
  - `V0`: calls `empty_state` to obtain an empty byte vector `es`, and returns
    `core.result.Result.Ok es`.  No secret material is embedded (§2.3 + §4.1).
  - `V1`: returns `core.result.Result.Ok v1` wrapping the protobuf-encoded
    `PqRatchetState` containing the fully populated `version_negotiation`,
    `chain = none`, and the `inner` state from `init_inner`.

The result satisfies the following postconditions:

  When `params.version = V0` (§2.3 + §4.1):
    There exists `es` such that `empty_state = ok es` and
    `result = core.result.Result.Ok es`.

  When `params.version = V1`:
    §2.1 (Totality): There exists `v1` such that `result = core.result.Result.Ok v1`.
    §4.3 + §4.4 (Protobuf construction): The encoded protobuf is constructed with
    `chain = none` and `version_negotiation` faithfully storing all Params fields.
    All intermediate values (cloned auth_key `v`, direction as i32 `i`, min_version
    as i32 `i1`, serialized chain_params `cp`, and init_inner result `o`) are
    existentially witnessed with their success conditions.

The auxiliary lemmas in this file provide additional derived properties:
- §2.2: `initial_state_determinism` — same Params → same result
- §3.1 + §3.3 + §4.2 + §4.5: `initial_state_v1_{a2b,b2a}_properties` — key lengths,
  epoch, authenticator derivation
- §3.2: `initial_state_v1_domain_sep` — HKDF domain separation
- §4.3 + §4.4: `initial_state_v1_protobuf_construction` — structural facts
- §5.1: `protobuf_encode_decode_roundtrip` axiom (see `Axioms.lean`)
- §5.2: `initial_state_v1_structural_completeness_{a2b,b2a}` — Option fields populated

**Source**: spqr/src/lib.rs (lines 212:0-236:1)
-/
@[step]
theorem initial_state_spec
    (params : Params)
    (h_ok : ∃ r, initial_state params = ok r)
    (h_key : params.auth_key.length ≤ U32.max) :
    initial_state params ⦃ (result : core.result.Result (alloc.vec.Vec U8) Error) =>
      match params.version with
      | .V0 =>
        -- §2.3 + §4.1: V0 produces empty state with no secrets
        ∃ es, empty_state = ok es ∧
          result = core.result.Result.Ok es
      | .V1 =>
        -- §2.1: Totality — result is always Ok
        ∃ v1, result = core.result.Result.Ok v1 ∧
        -- §4.3 + §4.4: Protobuf construction with chain = none, VN populated
        (∃ (v : alloc.vec.Vec U8) (i i1 : I32)
           (cp : proto.pq_ratchet.ChainParams)
           (o : Option proto.pq_ratchet.pq_ratchet_state.Inner),
          alloc.slice.Slice.to_vec core.clone.CloneU8
            params.auth_key = ok v ∧
          core.convert.IntoFrom.into I32.Insts.CoreConvertFromDirection
            params.direction = ok i ∧
          core.convert.IntoFrom.into I32.Insts.CoreConvertFromVersion
            params.min_version = ok i1 ∧
          chain.ChainParams.into_pb params.chain_params = ok cp ∧
          init_inner proto.pq_ratchet.Version.V1 params.direction
            params.auth_key = ok o ∧
          proto.pq_ratchet.PqRatchetState.Insts.ProstMessageMessage.encode_to_vec
            {
              version_negotiation :=
                (some
                  {
                    auth_key := v,
                    direction := i,
                    min_version := i1,
                    chain_params := (some cp)
                  }),
              chain := none,
              inner := o
            } = ok v1) ⦄ := by
  obtain ⟨r, hr⟩ := h_ok
  simp only [show initial_state params = ok r from hr, Aeneas.Std.WP.spec_ok]
  unfold initial_state at hr
  cases params.version with
  | V0 =>
    sorry
  | V1 =>
    sorry

end spqr
