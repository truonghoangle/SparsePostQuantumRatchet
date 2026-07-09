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
   - `A2B` → delegates to `States.init_a(auth_key)` then `States.into_pb`.
   - `B2A` → delegates to `States.init_b(auth_key)` then `States.into_pb`.

In both V1 branches, the authenticator satisfies `initial_ratchet_step` — a single
explicit HKDF ratchet step from a zero-initialized state at epoch 1, producing
32-byte `root_key` and `mac_key`.

**Source**: spqr/src/lib.rs (lines 198:0-210:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

private theorem bind_eq_ok {α β : Type} {m : Result α} {f : α → Result β} {r : β}
    (h : (do let x ← m; f x) = ok r) : ∃ v, m = ok v ∧ f v = ok r := by
  cases m with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => exact absurd h (by simp [Bind.bind, Aeneas.Std.bind])
  | div => exact absurd h (by simp [Bind.bind, Aeneas.Std.bind])

/--
**Spec theorem for `spqr.init_inner`**:

• Matches on the version:
  - `V0`: immediately returns `ok none`.
  - `V1`: matches on the direction:
    - `A2B`: calls `init_a` then `into_pb`.
    - `B2A`: calls `init_b` then `into_pb`.

The result satisfies the same structural postconditions as before (variant
preservation, success witnesses), but the intermediate `States` witness now
carries `initial_ratchet_step auth_key.val 1#u64` on the authenticator.

**Source**: spqr/src/lib.rs (lines 198:0-210:1)
-/
@[step]
theorem init_inner_spec
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
          ∃ s ku vs,
            v1.chunked.states.States.init_a auth_key = ok s ∧
            s = v1.chunked.states.States.KeysUnsampled ku ∧
            v1.chunked.states.serialize.States.into_pb s = ok vs ∧
            result = some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) ∧
            -- Universality Property 1–3: Epoch + explicit HKDF derivation
            ku.uc.epoch = 1#u64 ∧
            initial_ratchet_step auth_key.val 1#u64 ku.uc.auth ∧
            -- Universality Property 4–5: Variant preservation & structural completeness
            ∃ pb_ku,
              vs.inner_state =
                  some (proto.pq_ratchet.v1_state.InnerState.KeysUnsampled pb_ku) ∧
              match pb_ku.uc with
              | some uc_inner =>
                uc_inner.epoch = ku.uc.epoch ∧
                match uc_inner.auth with
                | some a =>
                  a.root_key = ku.uc.auth.root_key ∧
                  a.mac_key = ku.uc.auth.mac_key
                | none => False
              | none => False
        | .B2A =>
          ∃ s nhr vs,
            v1.chunked.states.States.init_b auth_key = ok s ∧
            s = v1.chunked.states.States.NoHeaderReceived nhr ∧
            v1.chunked.states.serialize.States.into_pb s = ok vs ∧
            result = some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) ∧
            -- Universality Property 1–3: Epoch + explicit HKDF derivation
            nhr.uc.epoch = 1#u64 ∧
            initial_ratchet_step auth_key.val 1#u64 nhr.uc.auth ∧
            -- Universality Property 4–5: Variant preservation & structural completeness
            (∃ pb_nhr,
              vs.inner_state =
                  some (proto.pq_ratchet.v1_state.InnerState.NoHeaderReceived pb_nhr) ∧
              (match pb_nhr.uc with
              | some nhr_inner =>
                nhr_inner.epoch = nhr.uc.epoch ∧
                match nhr_inner.auth with
                | some a =>
                  a.root_key = nhr.uc.auth.root_key ∧
                  a.mac_key = nhr.uc.auth.mac_key
                | none => False
              | none => False) ∧
              match pb_nhr.receiving_hdr with
              | some pd =>
                pd.polys = 16#u32 ∧
                pd.is_complete = nhr.receiving_hdr.is_complete
              | none => False) ⦄ := by
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
      -- Universality Properties 1–3: from init_a_spec
      have h_init_a := v1.chunked.states.States.init_a_spec auth_key h_key
      rw [hs] at h_init_a
      simp only [Aeneas.Std.WP.spec_ok] at h_init_a
      obtain ⟨ku, hku_eq, h_epoch, h_ratchet⟩ := h_init_a
      subst hku_eq
      -- Universality Properties 4–5: from into_pb_spec
      have h_pb := v1.chunked.states.serialize.States.into_pb_spec
        (.KeysUnsampled ku) ⟨vs, hvs⟩
      simp only [hvs, Aeneas.Std.WP.spec_ok] at h_pb
      obtain ⟨pb_ku, -, h_inner, h_fields⟩ := h_pb
      exact ⟨_, ku, vs, hs, rfl, hvs, rfl, h_epoch, h_ratchet, pb_ku, h_inner, h_fields⟩
    | B2A =>
      obtain ⟨s, hs, h2⟩ := bind_eq_ok hr
      obtain ⟨vs, hvs, h3⟩ := bind_eq_ok h2
      simp only [ok.injEq] at h3; subst h3
      -- Universality Properties 1–3: from init_b_spec
      have h_init_b := v1.chunked.states.States.init_b_spec auth_key h_key
      rw [hs] at h_init_b
      simp only [Aeneas.Std.WP.spec_ok] at h_init_b
      obtain ⟨nhr, hnhr_eq, h_epoch, h_ratchet⟩ := h_init_b
      subst hnhr_eq
      -- Universality Properties 4–5: from into_pb_spec
      have h_pb := v1.chunked.states.serialize.States.into_pb_spec
        (.NoHeaderReceived nhr) ⟨vs, hvs⟩
      simp only [hvs, Aeneas.Std.WP.spec_ok] at h_pb
      obtain ⟨pb_nhr, -, h_inner, h_uc_fields, h_hdr_fields⟩ := h_pb
      exact ⟨_, nhr, vs, hs, rfl, hvs, rfl, h_epoch, h_ratchet, pb_nhr, h_inner,
      h_uc_fields, h_hdr_fields⟩

end spqr
