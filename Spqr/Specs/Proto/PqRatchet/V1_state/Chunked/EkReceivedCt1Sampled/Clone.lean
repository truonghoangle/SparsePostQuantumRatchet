/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.V1_state.Unchunked.Ct1SentEkReceived.Clone
import Spqr.Specs.Proto.PqRatchet.PolynomialEncoder.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::v1_state::chunked::{impl core::clone::Clone for EkReceivedCt1Sampled}::clone`

`EkReceivedCt1Sampled` is the protobuf-generated product (record) type

  `EkReceivedCt1Sampled ≃ { uc : Option<Ct1SentEkReceived> ; sending_ct1 : Option<PolynomialEncoder> }`

representing the serialised form of the "EK received, CT1 sampled" state in the chunked ratchet
protocol.  After the encapsulation key (EK) has been received and the first ciphertext (CT1) has been
sampled, this state records the unchunked CT1-sent-EK-received sub-state and the polynomial encoder
used to send the first ciphertext in chunks.  The two fields are:
  • `uc : Option<Ct1SentEkReceived>` — the unchunked CT1-sent-EK-received sub-state
    (`Unchunked.Ct1SentEkReceived` in proto3; message fields are optional in prost).
  • `sending_ct1 : Option<PolynomialEncoder>` — the polynomial encoder accumulating first-ciphertext
    chunks (`PolynomialEncoder` in proto3; message fields are optional in prost).

The Rust source struct (src/v1/chunked/send_ct.rs, lines 42–46):
  ```rust
  #[cfg_attr(test, derive(Clone))]
  pub struct EkReceivedCt1Sampled {
      uc: unchunked::Ct1SentEkReceived,
      sending_ct1: polynomial::PolyEncoder,
  }
  ```

The protobuf schema (src/proto/pq_ratchet.proto, lines 163–166, inside `V1State.Chunked`):
  ```proto
  message EkReceivedCt1Sampled {
    Unchunked.Ct1SentEkReceived uc = 1;
    PolynomialEncoder sending_ct1 = 2;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 361–363):
  ```lean
  structure proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled where
    uc : Option proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived
    sending_ct1 : Option proto.pq_ratchet.PolynomialEncoder
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 274:17-274:22
  impl Clone for EkReceivedCt1Sampled {
      fn clone(&self) -> Self {
          EkReceivedCt1Sampled {
              uc: Clone::clone(&self.uc),
              sending_ct1: Clone::clone(&self.sending_ct1),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `Option::clone Ct1SentEkReceived.Insts.CoreCloneClone` for `uc` (identity clone on
     `Option<Ct1SentEkReceived>` — the `Ct1SentEkReceived` clone is the identity, as shown in
     `V1_state/Unchunked/Ct1SentEkReceived/Clone.lean`).
  2. `Option::clone PolynomialEncoder.Insts.CoreCloneClone` for `sending_ct1` (identity clone on
     `Option<PolynomialEncoder>` — the `PolynomialEncoder` clone is the identity, as shown in
     `PolynomialEncoder/Clone.lean`).

Because `Ct1SentEkReceived::clone` is the identity (all five fields — `epoch : u64`, `auth : Option
Authenticator`, `es : Vec<u8>`, `ek : Vec<u8>`, `ct1 : Vec<u8>` — have identity clones, as shown
in `V1_state/Unchunked/Ct1SentEkReceived/Clone.lean`), the `Option<Ct1SentEkReceived>` clone is the
identity.  Because `PolynomialEncoder::clone` is the identity (all three fields — `idx : u32`,
`pts : Vec<Vec<u8>>`, `polys : Vec<Vec<u8>>` — have identity clones, as shown in
`PolynomialEncoder/Clone.lean`), the `Option<PolynomialEncoder>` clone is the identity.  Therefore
the whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 274:17-274:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled

/-- `Option<Ct1SentEkReceived>` clone is the identity.

Because `Ct1SentEkReceived::clone` is the identity (see
`V1_state/Unchunked/Ct1SentEkReceived/Clone.lean`), and `Option::clone` delegates to the
element-level clone for `some` and is trivially the identity for `none`, the
`Option<Ct1SentEkReceived>` clone is the identity.

The Rust `Option<Ct1SentEkReceived>::clone` semantics:
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
private lemma clone_option_ct1sent_ek_received_spec
    (v : Option proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived) :
    core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived.Insts.CoreCloneClone v
      ⦃ (r : Option proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived) => r = v ⦄ := by
  suffices h : core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived.Insts.CoreCloneClone v = ok v by
    rw [h]; simp [WP.spec_ok]
  cases v with
  | none => simp [core.option.Option.Insts.CoreCloneClone.clone]
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone]
    have h := spqr.proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived.clone_spec x
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
**Spec theorem for `proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled.Insts.CoreCloneClone.clone`**:

• Takes an `EkReceivedCt1Sampled` value `self` wrapping two fields:
    - `uc : Option Ct1SentEkReceived` — the unchunked CT1-sent-EK-received sub-state.
    - `sending_ct1 : Option PolynomialEncoder` — the polynomial encoder for first-ciphertext
      chunks.
• Delegates to field-wise cloning:
    - `core.option.Option.Insts.CoreCloneClone.clone Ct1SentEkReceived.Insts.CoreCloneClone` for
      `uc`
      (identity clone on `Option Ct1SentEkReceived` — see `clone_option_ct1sent_ek_received_spec`).
    - `core.option.Option.Insts.CoreCloneClone.clone PolynomialEncoder.Insts.CoreCloneClone` for
      `sending_ct1`
      (identity clone on `Option PolynomialEncoder` — see `clone_option_polynomial_encoder_spec`).
• Returns the resulting `EkReceivedCt1Sampled` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 654–669):
  ```lean
  def proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled) :
    Result proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled
    := do
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived.Insts.CoreCloneClone
        self.uc
    let o1 ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.PolynomialEncoder.Insts.CoreCloneClone self.sending_ct1
    ok { uc := o, sending_ct1 := o1 }
  ```

• The function always succeeds (no panic / no error) for any `EkReceivedCt1Sampled` input, since
  the `Option<Ct1SentEkReceived>` clone is total (see
  `V1_state/Unchunked/Ct1SentEkReceived/Clone.lean`) and the `Option<PolynomialEncoder>` clone is
  total (see `PolynomialEncoder/Clone.lean`).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `EkReceivedCt1Sampled`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone` and discharges the two `Option` field clones via `step*` using the
already-registered `clone_option_ct1sent_ek_received_spec` and
`clone_option_polynomial_encoder_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 274:17-274:22)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  step*
  rw [o_post, o1_post]

end spqr.proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled
