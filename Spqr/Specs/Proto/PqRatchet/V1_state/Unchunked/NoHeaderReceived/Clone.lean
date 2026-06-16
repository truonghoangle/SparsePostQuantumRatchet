/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.Authenticator.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::v1_state::unchunked::{impl core::clone::Clone for NoHeaderReceived}::clone`

`NoHeaderReceived` is the protobuf-generated product (record) type

  `NoHeaderReceived ≃ { epoch : u64 ; auth : Option<Authenticator> }`

representing the serialised form of the "no header received" state in the unchunked ratchet
protocol.  This is the initial send-CT state before any ML-KEM header has been received from the
peer.  It records only the current epoch and an optional authenticator for MAC verification.
The two fields are:
  • `epoch : u64` — the epoch counter (`uint64` in proto3).
  • `auth : Option<Authenticator>` — the optional HMAC authenticator state used for message
    authentication (`Authenticator` in proto3; message fields are optional in prost).

The Rust source struct (src/v1/unchunked/send_ct.rs, lines 43–47):
  ```rust
  #[cfg_attr(test, derive(Clone))]
  pub struct NoHeaderReceived {
      pub epoch: Epoch,
      pub(super) auth: authenticator::Authenticator,
  }
  ```

The protobuf schema (src/proto/pq_ratchet.proto, lines 92–95, inside `V1State.Unchunked`):
  ```proto
  message NoHeaderReceived {
    uint64 epoch = 1;
    Authenticator auth = 2;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 388–393):
  ```lean
  structure proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived where
    epoch : Std.U64
    auth : Option proto.pq_ratchet.Authenticator
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 149:17-149:22
  impl Clone for NoHeaderReceived {
      fn clone(&self) -> Self {
          NoHeaderReceived {
              epoch: Clone::clone(&self.epoch),
              auth: Clone::clone(&self.auth),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `CloneU64.clone` for `epoch` (identity on `u64`).
  2. `Option::clone Authenticator.Insts.CoreCloneClone` for `auth` (identity clone on
     `Option<Authenticator>` — the `Authenticator` clone is the identity, as shown in
     `Authenticator/Clone.lean`).

Because `u64` is `Copy` — and its derived `Clone::clone` returns the argument unchanged — the
scalar field clone is the identity.  Because `Authenticator::clone` is the identity (both
`Vec<u8>` fields `root_key` and `mac_key` have identity clones, as shown in
`Authenticator/Clone.lean`), the `Option<Authenticator>` clone is the identity.  Therefore the
whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 149:17-149:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived

/-- `Option<Authenticator>` clone is the identity.

Because `Authenticator::clone` is the identity (see `Authenticator/Clone.lean`), and
`Option::clone` delegates to the element-level clone for `some` and is trivially the identity for
`none`, the `Option<Authenticator>` clone is the identity.

The Rust `Option<Authenticator>::clone` semantics:
  ```rust
  impl<T: Clone> Clone for Option<T> {
      fn clone(&self) -> Self {
          match self {
              Some(x) => Some(x.clone()),
              None => None,
          }
      }
  }
  ``` -/
@[step]
private lemma clone_option_authenticator_spec
    (v : Option proto.pq_ratchet.Authenticator) :
    core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.Authenticator.Insts.CoreCloneClone v
      ⦃ (r : Option proto.pq_ratchet.Authenticator) => r = v ⦄ := by
  suffices h : core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.Authenticator.Insts.CoreCloneClone v = ok v by
    rw [h]; simp [WP.spec_ok]
  cases v with
  | none => simp [core.option.Option.Insts.CoreCloneClone.clone]
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone]
    have h := spqr.proto.pq_ratchet.Authenticator.clone_spec x
    obtain ⟨r, hr, heq⟩ := WP.spec_imp_exists h
    simp [hr, heq]

/--
**Spec theorem for `proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived.Insts.CoreCloneClone.clone`**:

• Takes a `NoHeaderReceived` value `self` wrapping two fields:
    - `epoch : U64` — the epoch counter.
    - `auth : Option Authenticator` — the optional HMAC authenticator state.
• Delegates to field-wise cloning:
    - `core.clone.impls.CloneU64.clone` for `epoch` (identity on `U64`).
    - `core.option.Option.Insts.CoreCloneClone.clone Authenticator.Insts.CoreCloneClone` for `auth`
      (identity clone on `Option Authenticator` — see `clone_option_authenticator_spec`).
• Returns the resulting `NoHeaderReceived` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 730–742):
  ```lean
  def proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived) :
    Result proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived
    := do
    let i ← lift (core.clone.impls.CloneU64.clone self.epoch)
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.Authenticator.Insts.CoreCloneClone self.auth
    ok { epoch := i, auth := o }
  ```

• The function always succeeds (no panic / no error) for any `NoHeaderReceived` input, since
  `CloneU64.clone` is total and the `Option<Authenticator>` clone is total (see
  `Authenticator/Clone.lean`).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `NoHeaderReceived`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone`, simplifies the trivial `CloneU64.clone` / `lift`, and discharges the
`Option Authenticator` field clone via `step*` using the already-registered
`clone_option_authenticator_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 149:17-149:22)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  simp only [core.clone.impls.CloneU64.clone]
  simp only [lift]
  step*
  rw [o_post]

end spqr.proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived
