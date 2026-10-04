/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.ChainFromVersionNegotiation
import Spqr.Specs.Chain.Chain.FromPb
/-!
# Spec theorem for `spqr::chain_from`

`chain_from` reconstructs a `Chain` from an optional serialised protobuf `Chain` message
and an optional `VersionNegotiation` message.  Its logic is a nested pattern match:

  1. If `pb = some pb1`, deserialise the chain via `Chain::from_pb(pb1)` and propagate
     any error with the `?` operator.
  2. If `pb = none` and `vn = some vn1`, fall back to constructing a fresh chain via
     `chain_from_version_negotiation(vn1)`.
  3. If both are `none`, return `Err(Error::ChainNotAvailable)`.

The function can fail in exactly two ways originating from this level:
  - `Err ChainNotAvailable` — both `pb` and `vn` are `none`.
  - Any error propagated from `Chain::from_pb` or `chain_from_version_negotiation`.

**Source**: spqr/src/lib.rs (lines 343:0-354:1)
-/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr

/-! ## Functional model

A short, pure, hierarchically-composed definition that a reviewer can read
to understand what `chain_from` does, mirroring the Rust control flow:

```rust
fn chain_from(pb: Option<Chain>, vn: Option<VersionNegotiation>)
    -> Result<Chain, Error>
{
    match pb {
        Some(pb1) => Chain::from_pb(pb1)?,   // propagate Err via ?
        None => match vn {
            Some(vn1) => chain_from_version_negotiation(vn1),
            None      => Err(ChainNotAvailable),
        }
    }
}
```
-/

/-- Pure model of `chain_from`: delegates to `Chain.from_pb` (with `?`),
    `chain_from_version_negotiation`, or returns `ChainNotAvailable`. -/
noncomputable def chain_from_model
    (pb : Option proto.pq_ratchet.Chain)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    : Result (core.result.Result chain.Chain Error) :=
  match pb with
  | some pb1 => do
      let r ← chain.Chain.from_pb pb1
      match r with
      | core.result.Result.Ok v   => ok (core.result.Result.Ok v)
      | core.result.Result.Err e  => ok (core.result.Result.Err e)
  | none =>
      match vn with
      | some vn1 => chain_from_version_negotiation vn1
      | none     => ok (core.result.Result.Err Error.ChainNotAvailable)

/-! ## Spec theorem

The one-line postcondition says the result equals `chain_from_model pb vn`,
linking the extracted low-level code to the readable model above. -/

/-- **Spec theorem**: `chain_from` satisfies `chain_from_model`. -/
@[step]
theorem chain_from_spec
    (pb : Option proto.pq_ratchet.Chain)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation) :
    chain_from pb vn ⦃ (result : core.result.Result chain.Chain Error) =>
      chain_from_model pb vn = ok result ⦄ := by
  unfold chain_from chain_from_model
  match pb, vn with
  | none, none =>
    simp [WP.spec_ok]
  | none, some vn1 =>
    simp only []
    have h := chain_from_version_negotiation_spec vn1
    unfold WP.spec WP.theta at h ⊢
    cases hm : chain_from_version_negotiation vn1 with
    | ok r => simp [WP.wp_return]
    | fail e => simp [hm] at h
    | div => simp [hm] at h
  | some pb1, _ =>
    simp only []
    cases hm : chain.Chain.from_pb pb1 with
    | ok r =>
      simp only [bind_tc_ok]
      cases r with
      | Ok v =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from, WP.spec_ok]
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from, WP.spec_ok]
    | fail e =>
      have hspec := chain.Chain.from_pb_spec pb1
      rw [hm] at hspec
      exact absurd hspec id
    | div =>
      have hspec := chain.Chain.from_pb_spec pb1
      rw [hm] at hspec
      exact absurd hspec id

end spqr
