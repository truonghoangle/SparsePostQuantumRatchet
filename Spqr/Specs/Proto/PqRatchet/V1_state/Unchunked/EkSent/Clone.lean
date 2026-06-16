/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.Authenticator.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::v1_state::unchunked::{impl core::clone::Clone for EkSent}::clone`

`EkSent` is the protobuf-generated product (record) type

  `EkSent ≃ { epoch : u64 ; auth : Option<Authenticator> ; dk : Vec<u8> }`

representing the serialised form of the "EK sent" state in the unchunked ratchet protocol.  After
the encapsulation key (EK) has been sent, this state records the epoch at which the send occurred,
an optional authenticator for MAC verification, and the ML-KEM decapsulation key.  The three fields
are:
  • `epoch : u64` — the epoch counter at which the EK was sent (`uint64` in proto3).
  • `auth : Option<Authenticator>` — the optional HMAC authenticator state used for message
    authentication (`Authenticator` in proto3; message fields are optional in prost).
  • `dk : Vec<u8>` — the ML-KEM decapsulation key bytes (`bytes` in proto3).

The Rust source struct (src/v1/unchunked/send_ek.rs, lines 54–61):
  ```rust
  #[cfg_attr(test, derive(Clone))]
  #[hax_lib::attributes]
  pub struct EkSent {
      pub epoch: Epoch,
      auth: authenticator::Authenticator,
      #[hax_lib::refine(dk.len() == 2400)]
      dk: incremental_mlkem768::DecapsulationKey,
  }
  ```

The protobuf schema (src/proto/pq_ratchet.proto, lines 79–83, inside `V1State.Unchunked`):
  ```proto
  message EkSent {
    uint64 epoch = 1;
    Authenticator auth = 2;
    bytes dk = 3;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 425–431):
  ```lean
  structure proto.pq_ratchet.v1_state.unchunked.EkSent where
    epoch : Std.U64
    auth : Option proto.pq_ratchet.Authenticator
    dk : alloc.vec.Vec Std.U8
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 128:17-128:22
  impl Clone for EkSent {
      fn clone(&self) -> Self {
          EkSent {
              epoch: Clone::clone(&self.epoch),
              auth: Clone::clone(&self.auth),
              dk: Clone::clone(&self.dk),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `CloneU64.clone` for `epoch` (identity on `u64`).
  2. `Option::clone Authenticator.Insts.CoreCloneClone` for `auth` (identity clone on
     `Option<Authenticator>` — the `Authenticator` clone is the identity, as shown in
     `Authenticator/Clone.lean`).
  3. `CloneVec.clone CloneU8` for `dk` (identity clone on `Vec<u8>`).

Because `u64` is `Copy` — and its derived `Clone::clone` returns the argument unchanged — the
scalar field clone is the identity.  Because `Authenticator::clone` is the identity (both
`Vec<u8>` fields `root_key` and `mac_key` have identity clones, as shown in
`Authenticator/Clone.lean`), the `Option<Authenticator>` clone is the identity.  Because `u8` is
`Copy`, the element-wise `Vec<u8>` clone is the identity for the byte-vector field (`dk`).
Therefore the whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 128:17-128:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.v1_state.unchunked.EkSent

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

/-- `Vec<u8>` clone is the identity.

Because `u8` is `Copy`, its derived `Clone::clone` returns the argument unchanged.  The list-level
`Slice.clone` with the identity element-clone is therefore the identity, and
`alloc.vec.CloneVec.clone` wraps this in a `Vec`.

The Rust `Vec<u8>::clone` semantics:
  ```rust
  impl Clone for Vec<u8> {
      fn clone(&self) -> Self {
          // element-wise clone, each u8::clone is identity
          self.iter().map(|x| x.clone()).collect()
      }
  }
  ``` -/
@[step]
private lemma clone_vec_u8_spec (v : alloc.vec.Vec Std.U8) :
    alloc.vec.CloneVec.clone core.clone.CloneU8 v
      ⦃ (r : alloc.vec.Vec Std.U8) => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  apply WP.spec_mono
    (Slice.clone_spec (fun x _ => by simp))
  intro v' h
  exact h.symm

/--
**Spec theorem for `proto.pq_ratchet.v1_state.unchunked.EkSent.Insts.CoreCloneClone.clone`**:

• Takes an `EkSent` value `self` wrapping three fields:
    - `epoch : U64` — the epoch counter at which the EK was sent.
    - `auth : Option Authenticator` — the optional HMAC authenticator state.
    - `dk : Vec U8` — the ML-KEM decapsulation key bytes.
• Delegates to field-wise cloning:
    - `core.clone.impls.CloneU64.clone` for `epoch` (identity on `U64`).
    - `core.option.Option.Insts.CoreCloneClone.clone Authenticator.Insts.CoreCloneClone` for `auth`
      (identity clone on `Option Authenticator` — see `clone_option_authenticator_spec`).
    - `alloc.vec.CloneVec.clone CloneU8` for `dk`
      (identity clone on `Vec U8` — see `clone_vec_u8_spec`).
• Returns the resulting `EkSent` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 830–842):
  ```lean
  def proto.pq_ratchet.v1_state.unchunked.EkSent.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.v1_state.unchunked.EkSent) :
    Result proto.pq_ratchet.v1_state.unchunked.EkSent
    := do
    let i ← lift (core.clone.impls.CloneU64.clone self.epoch)
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.Authenticator.Insts.CoreCloneClone self.auth
    let v ← alloc.vec.CloneVec.clone core.clone.CloneU8 self.dk
    ok { epoch := i, auth := o, dk := v }
  ```

• The function always succeeds (no panic / no error) for any `EkSent` input, since
  `CloneU64.clone` is total, the `Option<Authenticator>` clone is total (see
  `Authenticator/Clone.lean`), and the `Vec<u8>` clone is total (element-wise `CloneU8.clone` is
  the identity on bounded integers).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `EkSent`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone`, simplifies the trivial `CloneU64.clone` / `lift`, and discharges the
`Option Authenticator` field clone and the `Vec U8` field clone via `step*` using the
already-registered `clone_option_authenticator_spec` and `clone_vec_u8_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 128:17-128:22)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.v1_state.unchunked.EkSent) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.EkSent) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  simp only [core.clone.impls.CloneU64.clone]
  simp only [lift]
  step*
  rw [o_post, v_post]

end spqr.proto.pq_ratchet.v1_state.unchunked.EkSent
