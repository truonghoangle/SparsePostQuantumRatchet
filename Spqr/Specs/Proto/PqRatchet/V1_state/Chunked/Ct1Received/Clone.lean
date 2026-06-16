/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.V1_state.Unchunked.EkSentCt1Received.Clone
import Spqr.Specs.Proto.PqRatchet.PolynomialEncoder.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::v1_state::chunked::{impl core::clone::Clone for Ct1Received}::clone`

`Ct1Received` is the protobuf-generated product (record) type

  `Ct1Received ≃ { uc : Option<EkSentCt1Received> ; sending_ek : Option<PolynomialEncoder> }`

representing the serialised form of the "CT1 received" state in the chunked ratchet protocol.
After the first ciphertext (CT1) has been received from the peer, this state records the unchunked
EK-sent-CT1-received sub-state and the polynomial encoder used to send the encapsulation key in
chunks.  The two fields are:
  • `uc : Option<EkSentCt1Received>` — the unchunked EK-sent-CT1-received sub-state
    (`Unchunked.EkSentCt1Received` in proto3; message fields are optional in prost).
  • `sending_ek : Option<PolynomialEncoder>` — the polynomial encoder producing encapsulation key
    chunks (`PolynomialEncoder` in proto3; message fields are optional in prost).

The Rust source struct (src/v1/chunked/send_ek.rs, lines 36–40):
  ```rust
  #[cfg_attr(test, derive(Clone))]
  pub struct Ct1Received {
      uc: unchunked::EkSentCt1Received,
      sending_ek: polynomial::PolyEncoder,
  }
  ```

The protobuf schema (src/proto/pq_ratchet.proto, lines 140–143, inside `V1State.Chunked`):
  ```proto
  message Ct1Received {
    Unchunked.EkSentCt1Received uc = 1;
    PolynomialEncoder sending_ek = 2;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 421–423):
  ```lean
  structure proto.pq_ratchet.v1_state.chunked.Ct1Received where
    uc : Option proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received
    sending_ek : Option proto.pq_ratchet.PolynomialEncoder
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 236:17-236:22
  impl Clone for Ct1Received {
      fn clone(&self) -> Self {
          Ct1Received {
              uc: Clone::clone(&self.uc),
              sending_ek: Clone::clone(&self.sending_ek),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `Option::clone EkSentCt1Received.Insts.CoreCloneClone` for `uc` (identity clone on
     `Option<EkSentCt1Received>` — the `EkSentCt1Received` clone is the identity, as shown in
     `V1_state/Unchunked/EkSentCt1Received/Clone.lean`).
  2. `Option::clone PolynomialEncoder.Insts.CoreCloneClone` for `sending_ek` (identity clone on
     `Option<PolynomialEncoder>` — the `PolynomialEncoder` clone is the identity, as shown in
     `PolynomialEncoder/Clone.lean`).

Because `EkSentCt1Received::clone` is the identity (all four fields — `epoch : u64`, `auth : Option
Authenticator`, `dk : Vec<u8>`, `ct1 : Vec<u8>` — have identity clones, as shown in
`V1_state/Unchunked/EkSentCt1Received/Clone.lean`), the `Option<EkSentCt1Received>` clone is the
identity.  Because `PolynomialEncoder::clone` is the identity (all three fields — `idx : u32`,
`pts : Vec<Vec<u8>>`, `polys : Vec<Vec<u8>>` — have identity clones, as shown in
`PolynomialEncoder/Clone.lean`), the `Option<PolynomialEncoder>` clone is the identity.  Therefore
the whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 236:17-236:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.v1_state.chunked.Ct1Received

/-- `Option<EkSentCt1Received>` clone is the identity.

Because `EkSentCt1Received::clone` is the identity (see
`V1_state/Unchunked/EkSentCt1Received/Clone.lean`), and `Option::clone` delegates to the
element-level clone for `some` and is trivially the identity for `none`, the
`Option<EkSentCt1Received>` clone is the identity.

The Rust `Option<EkSentCt1Received>::clone` semantics:
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
private lemma clone_option_ek_sent_ct1_received_spec
    (v : Option proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received) :
    core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received.Insts.CoreCloneClone v
      ⦃ (r : Option proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received) => r = v ⦄ := by
  suffices h : core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received.Insts.CoreCloneClone v = ok v by
    rw [h]; simp [WP.spec_ok]
  cases v with
  | none => simp [core.option.Option.Insts.CoreCloneClone.clone]
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone]
    have h := spqr.proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received.clone_spec x
    obtain ⟨r, hr, heq⟩ := WP.spec_imp_exists h
    simp [hr, heq]

/-- `Option<PolynomialEncoder>` clone is the identity.

Because `PolynomialEncoder::clone` is the identity (see `PolynomialEncoder/Clone.lean`), and
`Option::clone` delegates to the element-level clone for `some` and is trivially the identity for
`none`, the `Option<PolynomialEncoder>` clone is the identity.

The Rust `Option<PolynomialEncoder>::clone` semantics:
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
private lemma clone_option_polynomial_encoder_spec
    (v : Option proto.pq_ratchet.PolynomialEncoder) :
    core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.PolynomialEncoder.Insts.CoreCloneClone v
      ⦃ (r : Option proto.pq_ratchet.PolynomialEncoder) => r = v ⦄ := by
  suffices h : core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.PolynomialEncoder.Insts.CoreCloneClone v = ok v by
    rw [h]; simp [WP.spec_ok]
  cases v with
  | none => simp [core.option.Option.Insts.CoreCloneClone.clone]
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone]
    have h := spqr.proto.pq_ratchet.PolynomialEncoder.clone_spec x
    obtain ⟨r, hr, heq⟩ := WP.spec_imp_exists h
    simp [hr, heq]

/--
**Spec theorem for `proto.pq_ratchet.v1_state.chunked.Ct1Received.Insts.CoreCloneClone.clone`**:

• Takes a `Ct1Received` value `self` wrapping two fields:
    - `uc : Option EkSentCt1Received` — the unchunked EK-sent-CT1-received sub-state.
    - `sending_ek : Option PolynomialEncoder` — the polynomial encoder for encapsulation key
      chunks.
• Delegates to field-wise cloning:
    - `core.option.Option.Insts.CoreCloneClone.clone EkSentCt1Received.Insts.CoreCloneClone` for
      `uc`
      (identity clone on `Option EkSentCt1Received` — see `clone_option_ek_sent_ct1_received_spec`).
    - `core.option.Option.Insts.CoreCloneClone.clone PolynomialEncoder.Insts.CoreCloneClone` for
      `sending_ek`
      (identity clone on `Option PolynomialEncoder` — see `clone_option_polynomial_encoder_spec`).
• Returns the resulting `Ct1Received` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 817–828):
  ```lean
  def proto.pq_ratchet.v1_state.chunked.Ct1Received.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.v1_state.chunked.Ct1Received) :
    Result proto.pq_ratchet.v1_state.chunked.Ct1Received
    := do
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received.Insts.CoreCloneClone
        self.uc
    let o1 ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.PolynomialEncoder.Insts.CoreCloneClone self.sending_ek
    ok { uc := o, sending_ek := o1 }
  ```

• The function always succeeds (no panic / no error) for any `Ct1Received` input, since
  the `Option<EkSentCt1Received>` clone is total (see
  `V1_state/Unchunked/EkSentCt1Received/Clone.lean`) and the `Option<PolynomialEncoder>` clone is
  total (see `PolynomialEncoder/Clone.lean`).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `Ct1Received`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone` and discharges the two `Option` field clones via `step*` using the
already-registered `clone_option_ek_sent_ct1_received_spec` and
`clone_option_polynomial_encoder_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 236:17-236:22)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.v1_state.chunked.Ct1Received) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.v1_state.chunked.Ct1Received) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  step*
  rw [o_post, o1_post]

end spqr.proto.pq_ratchet.v1_state.chunked.Ct1Received
