/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.Authenticator.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::v1_state::unchunked::{impl core::clone::Clone for EkSentCt1Received}::clone`

`EkSentCt1Received` is the protobuf-generated product (record) type

  `EkSentCt1Received ≃ { epoch : u64 ; auth : Option<Authenticator> ; dk : Vec<u8> ; ct1 : Vec<u8> }`

representing the serialised form of the "EK sent, CT1 received" state in the unchunked ratchet
protocol.  After the encapsulation key (EK) has been sent and the first ciphertext (CT1) has been
received, this state records the epoch at which the exchange occurred, an optional authenticator for
MAC verification, the ML-KEM decapsulation key, and the first ciphertext.  The four fields are:
  • `epoch : u64` — the epoch counter at which the EK was sent (`uint64` in proto3).
  • `auth : Option<Authenticator>` — the optional HMAC authenticator state used for message
    authentication (`Authenticator` in proto3; message fields are optional in prost).
  • `dk : Vec<u8>` — the ML-KEM decapsulation key bytes (`bytes` in proto3).
  • `ct1 : Vec<u8>` — the first ML-KEM ciphertext bytes (`bytes` in proto3).

The Rust source struct (src/v1/unchunked/send_ek.rs, lines 65–72):
  ```rust
  #[cfg_attr(test, derive(Clone))]
  #[hax_lib::attributes]
  pub struct EkSentCt1Received {
      pub epoch: Epoch,
      auth: authenticator::Authenticator,
      #[hax_lib::refine(dk.len() == 2400)]
      dk: incremental_mlkem768::DecapsulationKey,
      #[hax_lib::refine(ct1.len() == 960)]
      ct1: incremental_mlkem768::Ciphertext1,
  }
  ```

The protobuf schema (src/proto/pq_ratchet.proto, lines 84–89, inside `V1State.Unchunked`):
  ```proto
  message EkSentCt1Received {
    uint64 epoch = 1;
    Authenticator auth = 2;
    bytes dk = 3;
    bytes ct1 = 4;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 405–409):
  ```lean
  structure proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received where
    epoch : Std.U64
    auth : Option proto.pq_ratchet.Authenticator
    dk : alloc.vec.Vec Std.U8
    ct1 : alloc.vec.Vec Std.U8
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 137:17-137:22
  impl Clone for EkSentCt1Received {
      fn clone(&self) -> Self {
          EkSentCt1Received {
              epoch: Clone::clone(&self.epoch),
              auth: Clone::clone(&self.auth),
              dk: Clone::clone(&self.dk),
              ct1: Clone::clone(&self.ct1),
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
  4. `CloneVec.clone CloneU8` for `ct1` (identity clone on `Vec<u8>`).

Because `u64` is `Copy` — and its derived `Clone::clone` returns the argument unchanged — the
scalar field clone is the identity.  Because `Authenticator::clone` is the identity (both
`Vec<u8>` fields `root_key` and `mac_key` have identity clones, as shown in
`Authenticator/Clone.lean`), the `Option<Authenticator>` clone is the identity.  Because `u8` is
`Copy`, the element-wise `Vec<u8>` clone is the identity for both byte-vector fields (`dk`,
`ct1`).  Therefore the whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 137:17-137:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received

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
**Spec theorem for `proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received.Insts.CoreCloneClone.clone`**:

• Takes an `EkSentCt1Received` value `self` wrapping four fields:
    - `epoch : U64` — the epoch counter at which the EK was sent.
    - `auth : Option Authenticator` — the optional HMAC authenticator state.
    - `dk : Vec U8` — the ML-KEM decapsulation key bytes.
    - `ct1 : Vec U8` — the first ML-KEM ciphertext bytes.
• Delegates to field-wise cloning:
    - `core.clone.impls.CloneU64.clone` for `epoch` (identity on `U64`).
    - `core.option.Option.Insts.CoreCloneClone.clone Authenticator.Insts.CoreCloneClone` for `auth`
      (identity clone on `Option Authenticator` — see `clone_option_authenticator_spec`).
    - `alloc.vec.CloneVec.clone CloneU8` for `dk`
      (identity clone on `Vec U8` — see `clone_vec_u8_spec`).
    - `alloc.vec.CloneVec.clone CloneU8` for `ct1`
      (identity clone on `Vec U8` — see `clone_vec_u8_spec`).
• Returns the resulting `EkSentCt1Received` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 771–786):
  ```lean
  def proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received) :
    Result proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received
    := do
    let i ← lift (core.clone.impls.CloneU64.clone self.epoch)
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.Authenticator.Insts.CoreCloneClone self.auth
    let v ← alloc.vec.CloneVec.clone core.clone.CloneU8 self.dk
    let v1 ← alloc.vec.CloneVec.clone core.clone.CloneU8 self.ct1
    ok { epoch := i, auth := o, dk := v, ct1 := v1 }
  ```

• The function always succeeds (no panic / no error) for any `EkSentCt1Received` input, since
  `CloneU64.clone` is total, the `Option<Authenticator>` clone is total (see
  `Authenticator/Clone.lean`), and each `Vec<u8>` clone is total (element-wise `CloneU8.clone` is
  the identity on bounded integers).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `EkSentCt1Received`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone`, simplifies the trivial `CloneU64.clone` / `lift`, and discharges the
`Option Authenticator` field clone and the two `Vec U8` field clones via `step*` using the
already-registered `clone_option_authenticator_spec` and `clone_vec_u8_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 137:17-137:22)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  simp only [core.clone.impls.CloneU64.clone]
  simp only [lift]
  step*
  rw [o_post, v_post, v1_post]

end spqr.proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received
