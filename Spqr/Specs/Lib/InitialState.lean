/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.InitInner
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

**Source**: spqr/src/lib.rs (lines 212:0-236:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.initial_state`**:

• Takes a `Params` struct containing `direction`, `version`, `min_version`, `auth_key`, and
  `chain_params`.
• Matches on `params.version`:
  - `V0`: calls `empty_state` to obtain an empty byte vector `es`, and returns
    `core.result.Result.Ok es`.
  - `V1`: performs the following sequence of operations:
    1. `alloc.slice.Slice.to_vec` clones the `auth_key` slice into a `Vec<u8>` value `v`.
    2. Converts `direction` to `i32` via `Into::into`, yielding `i`.
    3. Converts `min_version` to `i32` via `Into::into`, yielding `i1`.
    4. Serializes `chain_params` via `ChainParams.into_pb`, yielding `cp`.
    5. Calls `init_inner(V1, direction, auth_key)` to construct the initial inner state `o`.
    6. Builds a `PqRatchetState` protobuf with `version_negotiation`, `chain = none`, and
       `inner = o`, then encodes it to a byte vector `v1` via `encode_to_vec`.
    7. Returns `core.result.Result.Ok v1` wrapping the encoded bytes.

• The function succeeds (no panic) when the overall call is known to succeed, as captured
  by the precondition `h_ok : ∃ r, initial_state params = ok r`.

The result satisfies the following postconditions:

  When `params.version = V0`:
    There exists `es` such that `empty_state = ok es` and
    `result = core.result.Result.Ok es`.

  When `params.version = V1`:
    There exist intermediate values `v`, `i`, `i1`, `cp`, `o`, `v1` such that each
    sub-operation succeeds and the result is `core.result.Result.Ok v1`, where `v1` is
    the protobuf-encoded `PqRatchetState` containing the fully populated
    `version_negotiation`, `chain = none`, and the `inner` state from `init_inner`.

  This decomposition exposes the six computational stages of `initial_state` in the V1 case
  (key cloning, direction/version conversion, chain-params serialization, inner-state
  construction, protobuf encoding), allowing downstream proofs to compose with
  `init_inner_spec` and `init_inner_university_spec` to obtain detailed structural properties
  of the embedded inner state (epoch = 1, authenticator key lengths = 32, variant preservation
  under serialization, etc.).

The proof unfolds `initial_state` in the success hypothesis, destructures `params`, case-splits
on the version, and in each branch decomposes the `bind` calls to extract the intermediate
witnesses and the final `core.result.Result.Ok` equality.

**Source**: spqr/src/lib.rs (lines 212:0-236:1)
-/
private theorem bind_eq_ok {α β : Type} {m : Result α} {f : α → Result β} {r : β}
    (h : (do let x ← m; f x) = ok r) : ∃ v, m = ok v ∧ f v = ok r := by
  cases m with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => exact absurd h (by simp [Bind.bind, Aeneas.Std.bind])
  | div => exact absurd h (by simp [Bind.bind, Aeneas.Std.bind])

@[step]
theorem initial_state_spec
    (params : Params)
    (h_ok : ∃ r, initial_state params = ok r) :
    initial_state params ⦃ (result : core.result.Result (alloc.vec.Vec U8) Error) =>
      match params.version with
      | .V0 =>
        ∃ es, empty_state = ok es ∧
          result = core.result.Result.Ok es
      | .V1 =>
        ∃ v i i1 cp o v1,
          alloc.slice.Slice.to_vec core.clone.CloneU8 params.auth_key = ok v ∧
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
            } = ok v1 ∧
          result = core.result.Result.Ok v1 ⦄ := by
  obtain ⟨r, hr⟩ := h_ok
  simp only [show initial_state params = ok r from hr, Aeneas.Std.WP.spec_ok]
  unfold initial_state at hr
  rcases params with ⟨direction, version, min_version, auth_key, chain_params⟩
  cases version with
  | V0 =>
    obtain ⟨es, hes, h⟩ := bind_eq_ok hr
    simp only [ok.injEq] at h; subst h
    exact ⟨es, hes, rfl⟩
  | V1 =>
    obtain ⟨v, hv, h2⟩ := bind_eq_ok hr
    obtain ⟨i, hi, h3⟩ := bind_eq_ok h2
    obtain ⟨i1, hi1, h4⟩ := bind_eq_ok h3
    obtain ⟨cp, hcp, h5⟩ := bind_eq_ok h4
    obtain ⟨o, ho, h6⟩ := bind_eq_ok h5
    obtain ⟨v1, hv1, h7⟩ := bind_eq_ok h6
    simp only [ok.injEq] at h7; subst h7
    exact ⟨v, i, i1, cp, o, v1, hv, hi, hi1, hcp, ho, hv1, rfl⟩

end spqr
