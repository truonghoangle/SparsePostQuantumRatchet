/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.V1_state.Unchunked.Ct2Sent.Clone
import Spqr.Specs.Proto.PqRatchet.PolynomialEncoder.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::v1_state::chunked::{impl core::clone::Clone for Ct2Sampled}::clone`

`Ct2Sampled` is the protobuf-generated product (record) type

  `Ct2Sampled ≃ { uc : Option<Ct2Sent> ; sending_ct2 : Option<PolynomialEncoder> }`

representing the serialised form of the "CT2 sampled" state in the chunked ratchet protocol.  After
the second ciphertext (CT2) has been sampled, this state records the unchunked CT2-sent sub-state
and the polynomial encoder used for chunked transmission.  The two fields are:
  • `uc : Option<Ct2Sent>` — the optional unchunked CT2-sent state containing the epoch counter
    and authenticator (`Unchunked.Ct2Sent` in proto3; message fields are optional in prost).
  • `sending_ct2 : Option<PolynomialEncoder>` — the optional polynomial encoder state used for
    chunked CT2 transmission (`PolynomialEncoder` in proto3; message fields are optional in prost).

The Rust source struct (src/v1/chunked/send_ct.rs, lines 57–61):
  ```rust
  #[cfg_attr(test, derive(Clone))]
  pub struct Ct2Sampled {
      uc: unchunked::Ct2Sent,
      sending_ct2: polynomial::PolyEncoder,
  }
  ```

The protobuf schema (src/proto/pq_ratchet.proto, lines 171–174, inside `V1State.Chunked`):
  ```proto
  message Ct2Sampled {
    Unchunked.Ct2Sent uc = 1;
    PolynomialEncoder sending_ct2 = 2;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 327–329):
  ```lean
  structure proto.pq_ratchet.v1_state.chunked.Ct2Sampled where
    uc : Option proto.pq_ratchet.v1_state.unchunked.Ct2Sent
    sending_ct2 : Option proto.pq_ratchet.PolynomialEncoder
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 288:17-288:22
  impl Clone for Ct2Sampled {
      fn clone(&self) -> Self {
          Ct2Sampled {
              uc: Clone::clone(&self.uc),
              sending_ct2: Clone::clone(&self.sending_ct2),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `Option::clone Ct2Sent.Insts.CoreCloneClone` for `uc` (identity clone on
     `Option<Ct2Sent>` — the `Ct2Sent` clone is the identity, as shown in
     `Ct2Sent/Clone.lean`).
  2. `Option::clone PolynomialEncoder.Insts.CoreCloneClone` for `sending_ct2` (identity clone on
     `Option<PolynomialEncoder>` — the `PolynomialEncoder` clone is the identity, as shown in
     `PolynomialEncoder/Clone.lean`).

Because `Ct2Sent::clone` is the identity (both the `u64` epoch field and the
`Option<Authenticator>` auth field have identity clones, as shown in `Ct2Sent/Clone.lean`), the
`Option<Ct2Sent>` clone is the identity.  Because `PolynomialEncoder::clone` is the identity (the
`u32` index field and the two `Vec<Vec<u8>>` fields have identity clones, as shown in
`PolynomialEncoder/Clone.lean`), the `Option<PolynomialEncoder>` clone is the identity.  Therefore
the whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 288:17-288:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.v1_state.chunked.Ct2Sampled

/-- `Option<Ct2Sent>` clone is the identity.

Because `Ct2Sent::clone` is the identity (see `Ct2Sent/Clone.lean`), and
`Option::clone` delegates to the element-level clone for `some` and is trivially the identity for
`none`, the `Option<Ct2Sent>` clone is the identity.

The Rust `Option<Ct2Sent>::clone` semantics:
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
private lemma clone_option_ct2sent_spec
    (v : Option proto.pq_ratchet.v1_state.unchunked.Ct2Sent) :
    core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.Ct2Sent.Insts.CoreCloneClone v
      ⦃ (r : Option proto.pq_ratchet.v1_state.unchunked.Ct2Sent) => r = v ⦄ := by
  suffices h : core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.Ct2Sent.Insts.CoreCloneClone v = ok v by
    rw [h]; simp [WP.spec_ok]
  cases v with
  | none => simp [core.option.Option.Insts.CoreCloneClone.clone]
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone]
    have h := spqr.proto.pq_ratchet.v1_state.unchunked.Ct2Sent.clone_spec x
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
**Spec theorem for `proto.pq_ratchet.v1_state.chunked.Ct2Sampled.Insts.CoreCloneClone.clone`**:

• Takes a `Ct2Sampled` value `self` wrapping two fields:
    - `uc : Option Ct2Sent` — the optional unchunked CT2-sent state.
    - `sending_ct2 : Option PolynomialEncoder` — the optional polynomial encoder state.
• Delegates to field-wise cloning:
    - `core.option.Option.Insts.CoreCloneClone.clone Ct2Sent.Insts.CoreCloneClone` for `uc`
      (identity clone on `Option Ct2Sent` — see `clone_option_ct2sent_spec`).
    - `core.option.Option.Insts.CoreCloneClone.clone PolynomialEncoder.Insts.CoreCloneClone` for
      `sending_ct2` (identity clone on `Option PolynomialEncoder` — see
      `clone_option_polynomial_encoder_spec`).
• Returns the resulting `Ct2Sampled` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 573–584):
  ```lean
  def proto.pq_ratchet.v1_state.chunked.Ct2Sampled.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.v1_state.chunked.Ct2Sampled) :
    Result proto.pq_ratchet.v1_state.chunked.Ct2Sampled
    := do
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.v1_state.unchunked.Ct2Sent.Insts.CoreCloneClone
        self.uc
    let o1 ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.PolynomialEncoder.Insts.CoreCloneClone self.sending_ct2
    ok { uc := o, sending_ct2 := o1 }
  ```

• The function always succeeds (no panic / no error) for any `Ct2Sampled` input, since
  the `Option<Ct2Sent>` clone is total (see `Ct2Sent/Clone.lean`) and the
  `Option<PolynomialEncoder>` clone is total (see `PolynomialEncoder/Clone.lean`).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `Ct2Sampled`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone` and discharges the two `Option` field clones via `step*` using the
already-registered `clone_option_ct2sent_spec` and `clone_option_polynomial_encoder_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 288:17-288:22)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.v1_state.chunked.Ct2Sampled) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.v1_state.chunked.Ct2Sampled) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  step*
  rw [o_post, o1_post]

end spqr.proto.pq_ratchet.v1_state.chunked.Ct2Sampled
