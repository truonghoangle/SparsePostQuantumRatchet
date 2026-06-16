/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.Authenticator.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::v1_state::unchunked::{impl core::clone::Clone for Ct1SentEkReceived}::clone`

`Ct1SentEkReceived` is the protobuf-generated product (record) type

  `Ct1SentEkReceived ≃ { epoch : u64 ; auth : Option<Authenticator> ; es : Vec<u8> ; ek : Vec<u8> ; ct1 : Vec<u8> }`

representing the serialised form of the "CT1 sent, EK received" state in the unchunked ratchet
protocol.  After the first ciphertext (CT1) has been sent and the encapsulation key (EK) has been
received, this state records the epoch at which the send occurred, an optional authenticator for MAC
verification, the encapsulation state, the encapsulation key, and the first ciphertext.  The five
fields are:
  • `epoch : u64` — the epoch counter at which CT1 was sent (`uint64` in proto3).
  • `auth : Option<Authenticator>` — the optional HMAC authenticator state used for message
    authentication (`Authenticator` in proto3; message fields are optional in prost).
  • `es : Vec<u8>` — the ML-KEM encapsulation state bytes (`bytes` in proto3).
  • `ek : Vec<u8>` — the ML-KEM encapsulation key bytes (`bytes` in proto3).
  • `ct1 : Vec<u8>` — the first ML-KEM ciphertext bytes (`bytes` in proto3).

The Rust source struct (src/v1/unchunked/send_ct.rs, lines 73–82):
  ```rust
  #[cfg_attr(test, derive(Clone))]
  #[hax_lib::attributes]
  pub struct Ct1SentEkReceived {
      pub epoch: Epoch,
      auth: authenticator::Authenticator,
      #[hax_lib::refine(es.len() == 2080)]
      es: incremental_mlkem768::EncapsulationState,
      #[hax_lib::refine(ek.len() == 1152)]
      ek: incremental_mlkem768::EncapsulationKey,
      #[hax_lib::refine(ct1.len() == 960)]
      ct1: incremental_mlkem768::Ciphertext1,
  }
  ```

The protobuf schema (src/proto/pq_ratchet.proto, lines 114–120, inside `V1State.Unchunked`):
  ```proto
  message Ct1SentEkReceived {
    uint64 epoch = 1;
    Authenticator auth = 2;
    bytes es = 3;
    bytes ek = 4;
    bytes ct1 = 5;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 351–356):
  ```lean
  structure proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived where
    epoch : Std.U64
    auth : Option proto.pq_ratchet.Authenticator
    es : alloc.vec.Vec Std.U8
    ek : alloc.vec.Vec Std.U8
    ct1 : alloc.vec.Vec Std.U8
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 189:17-189:22
  impl Clone for Ct1SentEkReceived {
      fn clone(&self) -> Self {
          Ct1SentEkReceived {
              epoch: Clone::clone(&self.epoch),
              auth: Clone::clone(&self.auth),
              es: Clone::clone(&self.es),
              ek: Clone::clone(&self.ek),
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
  3. `CloneVec.clone CloneU8` for `es` (identity clone on `Vec<u8>`).
  4. `CloneVec.clone CloneU8` for `ek` (identity clone on `Vec<u8>`).
  5. `CloneVec.clone CloneU8` for `ct1` (identity clone on `Vec<u8>`).

Because `u64` is `Copy` — and its derived `Clone::clone` returns the argument unchanged — the
scalar field clone is the identity.  Because `Authenticator::clone` is the identity (both
`Vec<u8>` fields `root_key` and `mac_key` have identity clones, as shown in
`Authenticator/Clone.lean`), the `Option<Authenticator>` clone is the identity.  Because `u8` is
`Copy`, the element-wise `Vec<u8>` clone is the identity for all three byte-vector fields (`es`,
`ek`, `ct1`).  Therefore the whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 189:17-189:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived

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
**Spec theorem for `proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived.Insts.CoreCloneClone.clone`**:

• Takes a `Ct1SentEkReceived` value `self` wrapping five fields:
    - `epoch : U64` — the epoch counter at which CT1 was sent.
    - `auth : Option Authenticator` — the optional HMAC authenticator state.
    - `es : Vec U8` — the ML-KEM encapsulation state bytes.
    - `ek : Vec U8` — the ML-KEM encapsulation key bytes.
    - `ct1 : Vec U8` — the first ML-KEM ciphertext bytes.
• Delegates to field-wise cloning:
    - `core.clone.impls.CloneU64.clone` for `epoch` (identity on `U64`).
    - `core.option.Option.Insts.CoreCloneClone.clone Authenticator.Insts.CoreCloneClone` for `auth`
      (identity clone on `Option Authenticator` — see `clone_option_authenticator_spec`).
    - `alloc.vec.CloneVec.clone CloneU8` for `es`
      (identity clone on `Vec U8` — see `clone_vec_u8_spec`).
    - `alloc.vec.CloneVec.clone CloneU8` for `ek`
      (identity clone on `Vec U8` — see `clone_vec_u8_spec`).
    - `alloc.vec.CloneVec.clone CloneU8` for `ct1`
      (identity clone on `Vec U8` — see `clone_vec_u8_spec`).
• Returns the resulting `Ct1SentEkReceived` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 631–643):
  ```lean
  def proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived) :
    Result proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived
    := do
    let i ← lift (core.clone.impls.CloneU64.clone self.epoch)
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.Authenticator.Insts.CoreCloneClone self.auth
    let v ← alloc.vec.CloneVec.clone core.clone.CloneU8 self.es
    let v1 ← alloc.vec.CloneVec.clone core.clone.CloneU8 self.ek
    let v2 ← alloc.vec.CloneVec.clone core.clone.CloneU8 self.ct1
    ok { epoch := i, auth := o, es := v, ek := v1, ct1 := v2 }
  ```

• The function always succeeds (no panic / no error) for any `Ct1SentEkReceived` input, since
  `CloneU64.clone` is total, the `Option<Authenticator>` clone is total (see
  `Authenticator/Clone.lean`), and each `Vec<u8>` clone is total (element-wise `CloneU8.clone` is
  the identity on bounded integers).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `Ct1SentEkReceived`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone`, simplifies the trivial `CloneU64.clone` / `lift`, and discharges the
`Option Authenticator` field clone and the three `Vec U8` field clones via `step*` using the
already-registered `clone_option_authenticator_spec` and `clone_vec_u8_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 189:17-189:22)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  simp only [core.clone.impls.CloneU64.clone]
  simp only [lift]
  step*
  rw [o_post, v_post, v1_post, v2_post]

end spqr.proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived
