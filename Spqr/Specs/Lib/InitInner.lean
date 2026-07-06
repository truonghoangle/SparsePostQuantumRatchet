/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Chunked.States.States.InitA
import Spqr.Specs.V1.Chunked.States.States.InitB
import Spqr.Specs.V1.Chunked.States.Serialize.States.IntoPb
import Spqr.Specs.Authenticator.Authenticator.New
/-!
# Spec theorem for `spqr::init_inner`

`init_inner` is the top-level dispatch function that constructs the initial V1 chunked SPQR protocol
state — serialized into its protobuf `Inner` representation — from a `Version`, a `Direction`, and
an authentication key byte-slice.

The function performs a two-level match:

1. **Version match**:
   - `V0` → returns `none` (version 0 does not produce an inner state).
   - `V1` → proceeds to the direction match.

2. **Direction match** (V1 only):
   - `A2B` → delegates to `States.init_a(auth_key)` to construct the initial A-side
     (encapsulation-key-sending) state at epoch 1, then calls `States.into_pb` to serialize
     it into the protobuf `V1State`, and wraps the result as
     `some (pq_ratchet_state.Inner.V1 vs)`.
   - `B2A` → delegates to `States.init_b(auth_key)` to construct the initial B-side
     (ciphertext-sending) state at epoch 1, then calls `States.into_pb` to serialize it,
     and wraps the result similarly.

In both V1 branches, `init_a`/`init_b` derive an `Authenticator` from `auth_key` via
HKDF-SHA256 with epoch `1` (producing 32-byte `root_key` and `mac_key`), and `into_pb`
converts the resulting `States` enum into the protobuf `V1State` format used for network
serialization or persistent storage.

The by-value `init_inner` introduces no additional logic beyond the dispatch and wrapping, so
its postconditions are inherited from the corresponding `init_a`, `init_b`, and `into_pb`
specifications.

**Source**: spqr/src/lib.rs (lines 198:0-210:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.init_inner`**:

• Takes a `Version` `v`, a `Direction` `d`, and an `auth_key : Slice U8` — the initial
  authentication root key for the protocol.
• Matches on the version:
  - `V0`: immediately returns `ok none` — version 0 has no inner state.
  - `V1`: matches on the direction:
    - `A2B`: calls `v1.chunked.states.States.init_a auth_key` to construct the initial
      A-side `KeysUnsampled` state (epoch = 1, authenticator from HKDF-SHA256), then
      serializes via `v1.chunked.states.serialize.States.into_pb` into a `V1State`, and
      returns `ok (some (Inner.V1 vs))`.
    - `B2A`: calls `v1.chunked.states.States.init_b auth_key` to construct the initial
      B-side `NoHeaderReceived` state (epoch = 1, authenticator from HKDF-SHA256), then
      serializes via `v1.chunked.states.serialize.States.into_pb`, and returns
      `ok (some (Inner.V1 vs))`.

• The function succeeds (no panic) when the overall call is known to succeed, as captured
  by the precondition `h_ok : ∃ r, init_inner v d auth_key = ok r`.

The result satisfies the following postconditions:

  When `v = V0`:
    `result = none`

  When `v = V1` and `d = A2B`:
    There exist intermediate values `s : States` and `vs : V1State` such that:
    - `v1.chunked.states.States.init_a auth_key = ok s` — the initial A-side state was
      successfully constructed from `auth_key`.
    - `v1.chunked.states.serialize.States.into_pb s = ok vs` — the state was successfully
      serialized into protobuf form.
    - `result = some (pq_ratchet_state.Inner.V1 vs)` — the result wraps the serialized state.

  When `v = V1` and `d = B2A`:
    There exist intermediate values `s : States` and `vs : V1State` such that:
    - `v1.chunked.states.States.init_b auth_key = ok s` — the initial B-side state was
      successfully constructed from `auth_key`.
    - `v1.chunked.states.serialize.States.into_pb s = ok vs` — the state was successfully
      serialized into protobuf form.
    - `result = some (pq_ratchet_state.Inner.V1 vs)` — the result wraps the serialized state.

  This decomposition exposes the two computational stages of `init_inner` in the V1 case
  (state construction via `init_a`/`init_b`, followed by serialization via `into_pb`),
  allowing downstream proofs to compose with `init_a_spec`, `init_b_spec`, and `into_pb_spec`
  to obtain detailed structural properties of the result (epoch = 1, authenticator key
  lengths = 32, variant preservation under serialization, etc.).

The proof unfolds `init_inner` in the success hypothesis, case-splits on the version and
direction, and in each V1 branch decomposes the two `bind` calls (`init_a`/`init_b` followed
by `into_pb`) to extract the intermediate `States` witness, the `V1State` witness, and the
`Inner.V1` equality.

**Source**: spqr/src/lib.rs (lines 198:0-210:1)
-/
private theorem bind_eq_ok {α β : Type} {m : Result α} {f : α → Result β} {r : β}
    (h : (do let x ← m; f x) = ok r) : ∃ v, m = ok v ∧ f v = ok r := by
  cases m with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => exact absurd h (by simp [Bind.bind, Aeneas.Std.bind])
  | div => exact absurd h (by simp [Bind.bind, Aeneas.Std.bind])

@[step]
theorem init_inner_spec
    (v : proto.pq_ratchet.Version) (d : proto.pq_ratchet.Direction)
    (auth_key : Slice U8)
    (h_ok : ∃ r, init_inner v d auth_key = ok r) :
    init_inner v d auth_key ⦃ (result : Option proto.pq_ratchet.pq_ratchet_state.Inner) =>
      match v with
      | .V0 => result = none
      | .V1 =>
        match d with
        | .A2B =>
          ∃ s vs,
            v1.chunked.states.States.init_a auth_key = ok s ∧
            v1.chunked.states.serialize.States.into_pb s = ok vs ∧
            result = some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs)
        | .B2A =>
          ∃ s vs,
            v1.chunked.states.States.init_b auth_key = ok s ∧
            v1.chunked.states.serialize.States.into_pb s = ok vs ∧
            result = some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) ⦄ := by
  obtain ⟨r, hr⟩ := h_ok
  simp only [show init_inner v d auth_key = ok r from hr, Aeneas.Std.WP.spec_ok]
  unfold init_inner at hr
  cases v with
  | V0 =>
    simp only [ok.injEq] at hr
    subst hr; rfl
  | V1 =>
    cases d with
    | A2B =>
      obtain ⟨s, hs, h2⟩ := bind_eq_ok hr
      obtain ⟨vs, hvs, h3⟩ := bind_eq_ok h2
      simp only [ok.injEq] at h3; subst h3
      exact ⟨s, vs, hs, hvs, rfl⟩
    | B2A =>
      obtain ⟨s, hs, h2⟩ := bind_eq_ok hr
      obtain ⟨vs, hvs, h3⟩ := bind_eq_ok h2
      simp only [ok.injEq] at h3; subst h3
      exact ⟨s, vs, hs, hvs, rfl⟩

/--
**Universality spec theorem for `spqr.init_inner`**:

Strengthens `init_inner_spec` by composing the sub-specs `init_a_spec` / `init_b_spec`
(from `Spqr/Specs/V1/Chunked/States/States/InitA.lean` and `InitB.lean`) and `into_pb_spec`
(from `Spqr/Specs/V1/Chunked/States/Serialize/States/IntoPb.lean`) to propagate the following
**universality properties** through the full `init_inner` pipeline:

### Universality Property 1 — Epoch Initialization
  In both V1 branches (A2B and B2A), the intermediate `States` value `s` has its unchunked
  core epoch field initialized to `1#u64`.

### Universality Property 2 — Key Length Invariants
  The embedded authenticator's `root_key` and `mac_key` fields are both exactly 32 bytes,
  as derived by HKDF-SHA256 during `Authenticator.new`.

### Universality Property 3 — Deterministic Key Derivation
  The authenticator is deterministically derived from the input `auth_key` via
  `Authenticator.new(auth_key.to_vec(), 1)`.  This feeds `auth_key` and epoch `1` into
  HKDF-SHA256 with a fixed protocol label, producing the 32-byte `root_key` and `mac_key`.

### Universality Property 4 — Variant Preservation Through Serialization
  The serialized `V1State` preserves the `States` variant tag:
  - A2B → `vs.inner_state = some (.KeysUnsampled pb_ku)`
  - B2A → `vs.inner_state = some (.NoHeaderReceived pb_nhr)`

### Universality Property 5 — Structural Completeness
  All `Option` fields in the produced protobuf sub-state value are populated (`some`):
  - A2B: `pb_ku.uc = some uc_inner`
  - B2A: `pb_nhr.uc = some uc_inner` and `pb_nhr.receiving_hdr = some pd`

### Preconditions
  In addition to the success precondition `h_ok`, this theorem requires
  `h_key : auth_key.length ≤ U32.max` to ensure that the HKDF input construction
  does not overflow.

**Source**: spqr/src/lib.rs (lines 198:0-210:1)
-/
@[step]
theorem init_inner_university_spec
    (v : proto.pq_ratchet.Version) (d : proto.pq_ratchet.Direction)
    (auth_key : Slice U8)
    (h_ok : ∃ r, init_inner v d auth_key = ok r)
    (h_key : auth_key.length ≤ U32.max) :
    init_inner v d auth_key ⦃ (result : Option proto.pq_ratchet.pq_ratchet_state.Inner) =>
      match v with
      | .V0 => result = none
      | .V1 =>
        match d with
        | .A2B =>
          ∃ s vs,
            v1.chunked.states.States.init_a auth_key = ok s ∧
            v1.chunked.states.serialize.States.into_pb s = ok vs ∧
            result = some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) ∧
            -- Universality Property 1–3: Epoch, key lengths, authenticator derivation
            (∃ ku, s = v1.chunked.states.States.KeysUnsampled ku ∧
              ku.uc.epoch = 1#u64 ∧
              ku.uc.auth.root_key.length = 32 ∧
              ku.uc.auth.mac_key.length = 32 ∧
              ∃ v, v.val = auth_key.val ∧
                authenticator.Authenticator.new v 1#u64 = ok ku.uc.auth) ∧
            -- Universality Property 4–5: Variant preservation & structural completeness
            (∃ pb_ku, vs.inner_state =
                some (proto.pq_ratchet.v1_state.InnerState.KeysUnsampled pb_ku) ∧
              ∃ uc_inner, pb_ku.uc = some uc_inner)
        | .B2A =>
          ∃ s vs,
            v1.chunked.states.States.init_b auth_key = ok s ∧
            v1.chunked.states.serialize.States.into_pb s = ok vs ∧
            result = some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) ∧
            -- Universality Property 1–3: Epoch, key lengths, authenticator derivation
            (∃ nhr, s = v1.chunked.states.States.NoHeaderReceived nhr ∧
              nhr.uc.epoch = 1#u64 ∧
              nhr.uc.auth.root_key.length = 32 ∧
              nhr.uc.auth.mac_key.length = 32 ∧
              ∃ v, v.val = auth_key.val ∧
                authenticator.Authenticator.new v 1#u64 = ok nhr.uc.auth) ∧
            -- Universality Property 4–5: Variant preservation & structural completeness
            (∃ pb_nhr, vs.inner_state =
                some (proto.pq_ratchet.v1_state.InnerState.NoHeaderReceived pb_nhr) ∧
              (∃ uc_inner, pb_nhr.uc = some uc_inner) ∧
              (∃ pd, pb_nhr.receiving_hdr = some pd)) ⦄ := by
  obtain ⟨r, hr⟩ := h_ok
  simp only [show init_inner v d auth_key = ok r from hr, Aeneas.Std.WP.spec_ok]
  unfold init_inner at hr
  cases v with
  | V0 =>
    simp only [ok.injEq] at hr
    subst hr; rfl
  | V1 =>
    cases d with
    | A2B =>
      obtain ⟨s, hs, h2⟩ := bind_eq_ok hr
      obtain ⟨vs, hvs, h3⟩ := bind_eq_ok h2
      simp only [ok.injEq] at h3; subst h3
      refine ⟨s, vs, hs, hvs, rfl, ?_, ?_⟩
      · -- Universality Properties 1–3: from init_a_spec
        have h_init_a := v1.chunked.states.States.init_a_spec auth_key h_key
        rw [hs] at h_init_a
        simp only [Aeneas.Std.WP.spec_ok] at h_init_a
        obtain ⟨ku, hku_eq, hku_epoch, hku_rk, hku_mk, v_auth, hv_val, hv_auth⟩ := h_init_a
        exact ⟨ku, hku_eq, hku_epoch, hku_rk, hku_mk, v_auth, hv_val, hv_auth⟩
      · -- Universality Properties 4–5: variant preservation & structural completeness
        -- Compose init_a_spec (variant = KeysUnsampled) with into_pb_spec to extract
        -- the variant tag and structural completeness of the serialized protobuf.
        have h_init_a := v1.chunked.states.States.init_a_spec auth_key h_key
        rw [hs] at h_init_a
        simp only [Aeneas.Std.WP.spec_ok] at h_init_a
        obtain ⟨ku, hku_eq, -⟩ := h_init_a
        subst hku_eq
        -- hvs : into_pb (.KeysUnsampled ku) = ok vs
        have h_pb := v1.chunked.states.serialize.States.into_pb_spec
          (.KeysUnsampled ku) ⟨vs, hvs⟩
        simp only [hvs, Aeneas.Std.WP.spec_ok] at h_pb
        obtain ⟨pb_ku, -, h_inner, h_uc⟩ := h_pb
        exact ⟨pb_ku, h_inner, h_uc⟩
    | B2A =>
      obtain ⟨s, hs, h2⟩ := bind_eq_ok hr
      obtain ⟨vs, hvs, h3⟩ := bind_eq_ok h2
      simp only [ok.injEq] at h3; subst h3
      refine ⟨s, vs, hs, hvs, rfl, ?_, ?_⟩
      · -- Universality Properties 1–3: from init_b_spec
        have h_init_b := v1.chunked.states.States.init_b_spec auth_key h_key
        rw [hs] at h_init_b
        simp only [Aeneas.Std.WP.spec_ok] at h_init_b
        obtain ⟨nhr, hnhr_eq, hnhr_epoch, hnhr_rk, hnhr_mk, v_auth, hv_val, hv_auth⟩ := h_init_b
        exact ⟨nhr, hnhr_eq, hnhr_epoch, hnhr_rk, hnhr_mk, v_auth, hv_val, hv_auth⟩
      · -- Universality Properties 4–5: variant preservation & structural completeness
        -- Compose init_b_spec (variant = NoHeaderReceived) with into_pb_spec to extract
        -- the variant tag and structural completeness of the serialized protobuf.
        have h_init_b := v1.chunked.states.States.init_b_spec auth_key h_key
        rw [hs] at h_init_b
        simp only [Aeneas.Std.WP.spec_ok] at h_init_b
        obtain ⟨nhr, hnhr_eq, -⟩ := h_init_b
        subst hnhr_eq
        -- hvs : into_pb (.NoHeaderReceived nhr) = ok vs
        have h_pb := v1.chunked.states.serialize.States.into_pb_spec
          (.NoHeaderReceived nhr) ⟨vs, hvs⟩
        simp only [hvs, Aeneas.Std.WP.spec_ok] at h_pb
        obtain ⟨pb_nhr, -, h_inner, h_uc, h_pd⟩ := h_pb
        exact ⟨pb_nhr, h_inner, h_uc, h_pd⟩

end spqr
