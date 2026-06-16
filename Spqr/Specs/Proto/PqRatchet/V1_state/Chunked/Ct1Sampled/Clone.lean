/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.V1_state.Unchunked.Ct1Sent.Clone
import Spqr.Specs.Proto.PqRatchet.PolynomialEncoder.Clone
import Spqr.Specs.Proto.PqRatchet.PolynomialDecoder.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::v1_state::chunked::{impl core::clone::Clone for Ct1Sampled}::clone`

`Ct1Sampled` is the protobuf-generated product (record) type

  `Ct1Sampled ≃ { uc : Option<Ct1Sent> ; sending_ct1 : Option<PolynomialEncoder> ; receiving_ek : Option<PolynomialDecoder> }`

representing the serialised form of the "CT1 sampled" state in the chunked ratchet protocol.  After
the first ciphertext (CT1) has been sampled, this state records the unchunked CT1-sent sub-state, the
polynomial encoder used to send the first ciphertext in chunks, and the polynomial decoder used to
receive the encapsulation key in chunks.  The three fields are:
  • `uc : Option<Ct1Sent>` — the unchunked CT1-sent sub-state (`Unchunked.Ct1Sent` in proto3;
    message fields are optional in prost).
  • `sending_ct1 : Option<PolynomialEncoder>` — the polynomial encoder accumulating first-ciphertext
    chunks (`PolynomialEncoder` in proto3; message fields are optional in prost).
  • `receiving_ek : Option<PolynomialDecoder>` — the polynomial decoder accumulating encapsulation
    key chunks (`PolynomialDecoder` in proto3; message fields are optional in prost).

The Rust source struct (src/v1/chunked/send_ct.rs, lines 32–40):
  ```rust
  #[cfg_attr(test, derive(Clone))]
  #[hax_lib::attributes]
  pub struct Ct1Sampled {
      uc: unchunked::Ct1Sent,
      sending_ct1: polynomial::PolyEncoder,
      // `receiving_ek` only decodes messages of length `incremental_mlkem768::ENCAPSULATION_KEY_SIZE`
      #[hax_lib::refine(receiving_ek.get_pts_needed() == incremental_mlkem768::ENCAPSULATION_KEY_SIZE / 2)]
      receiving_ek: polynomial::PolyDecoder,
  }
  ```

The protobuf schema (src/proto/pq_ratchet.proto, lines 158–162, inside `V1State.Chunked`):
  ```proto
  message Ct1Sampled {
    Unchunked.Ct1Sent uc = 1;
    PolynomialEncoder sending_ct1 = 2;
    PolynomialDecoder receiving_ek = 3;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 365–371):
  ```lean
  structure proto.pq_ratchet.v1_state.chunked.Ct1Sampled where
    uc : Option proto.pq_ratchet.v1_state.unchunked.Ct1Sent
    sending_ct1 : Option proto.pq_ratchet.PolynomialEncoder
    receiving_ek : Option proto.pq_ratchet.PolynomialDecoder
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 265:17-265:22
  impl Clone for Ct1Sampled {
      fn clone(&self) -> Self {
          Ct1Sampled {
              uc: Clone::clone(&self.uc),
              sending_ct1: Clone::clone(&self.sending_ct1),
              receiving_ek: Clone::clone(&self.receiving_ek),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `Option::clone Ct1Sent.Insts.CoreCloneClone` for `uc` (identity clone on
     `Option<Ct1Sent>` — the `Ct1Sent` clone is the identity, as shown in
     `V1_state/Unchunked/Ct1Sent/Clone.lean`).
  2. `Option::clone PolynomialEncoder.Insts.CoreCloneClone` for `sending_ct1` (identity clone on
     `Option<PolynomialEncoder>` — the `PolynomialEncoder` clone is the identity, as shown in
     `PolynomialEncoder/Clone.lean`).
  3. `Option::clone PolynomialDecoder.Insts.CoreCloneClone` for `receiving_ek` (identity clone on
     `Option<PolynomialDecoder>` — the `PolynomialDecoder` clone is the identity, as shown in
     `PolynomialDecoder/Clone.lean`).

Because `Ct1Sent::clone` is the identity (all five fields — `epoch : u64`, `auth : Option
Authenticator`, `hdr : Vec<u8>`, `es : Vec<u8>`, `ct1 : Vec<u8>` — have identity clones, as shown
in `V1_state/Unchunked/Ct1Sent/Clone.lean`), the `Option<Ct1Sent>` clone is the identity.  Because
`PolynomialEncoder::clone` is the identity (all three fields — `idx : u32`, `pts : Vec<Vec<u8>>`,
`polys : Vec<Vec<u8>>` — have identity clones, as shown in `PolynomialEncoder/Clone.lean`), the
`Option<PolynomialEncoder>` clone is the identity.  Because `PolynomialDecoder::clone` is the
identity (all four fields — `pts_needed : u32`, `polys : u32`, `pts : Vec<Vec<u8>>`,
`is_complete : bool` — have identity clones, as shown in `PolynomialDecoder/Clone.lean`), the
`Option<PolynomialDecoder>` clone is the identity.  Therefore the whole struct-level clone is
observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 265:17-265:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.v1_state.chunked.Ct1Sampled

/-- `Option<Ct1Sent>` clone is the identity.

Because `Ct1Sent::clone` is the identity (see `V1_state/Unchunked/Ct1Sent/Clone.lean`), and
`Option::clone` delegates to the element-level clone for `some` and is trivially the identity for
`none`, the `Option<Ct1Sent>` clone is the identity.

The Rust `Option<Ct1Sent>::clone` semantics:
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
private lemma clone_option_ct1sent_spec
    (v : Option proto.pq_ratchet.v1_state.unchunked.Ct1Sent) :
    core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.Ct1Sent.Insts.CoreCloneClone v
      ⦃ (r : Option proto.pq_ratchet.v1_state.unchunked.Ct1Sent) => r = v ⦄ := by
  suffices h : core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.Ct1Sent.Insts.CoreCloneClone v = ok v by
    rw [h]; simp [WP.spec_ok]
  cases v with
  | none => simp [core.option.Option.Insts.CoreCloneClone.clone]
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone]
    have h := spqr.proto.pq_ratchet.v1_state.unchunked.Ct1Sent.clone_spec x
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

/-- `Option<PolynomialDecoder>` clone is the identity.

Because `PolynomialDecoder::clone` is the identity (see `PolynomialDecoder/Clone.lean`), and
`Option::clone` delegates to the element-level clone for `some` and is trivially the identity for
`none`, the `Option<PolynomialDecoder>` clone is the identity.

The Rust `Option<PolynomialDecoder>::clone` semantics:
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
private lemma clone_option_polynomial_decoder_spec
    (v : Option proto.pq_ratchet.PolynomialDecoder) :
    core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.PolynomialDecoder.Insts.CoreCloneClone v
      ⦃ (r : Option proto.pq_ratchet.PolynomialDecoder) => r = v ⦄ := by
  suffices h : core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.PolynomialDecoder.Insts.CoreCloneClone v = ok v by
    rw [h]; simp [WP.spec_ok]
  cases v with
  | none => simp [core.option.Option.Insts.CoreCloneClone.clone]
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone]
    have h := spqr.proto.pq_ratchet.PolynomialDecoder.clone_spec x
    obtain ⟨r, hr, heq⟩ := WP.spec_imp_exists h
    simp [hr, heq]

/--
**Spec theorem for `proto.pq_ratchet.v1_state.chunked.Ct1Sampled.Insts.CoreCloneClone.clone`**:

• Takes a `Ct1Sampled` value `self` wrapping three fields:
    - `uc : Option Ct1Sent` — the unchunked CT1-sent sub-state.
    - `sending_ct1 : Option PolynomialEncoder` — the polynomial encoder for first-ciphertext
      chunks.
    - `receiving_ek : Option PolynomialDecoder` — the polynomial decoder for encapsulation key
      chunks.
• Delegates to field-wise cloning:
    - `core.option.Option.Insts.CoreCloneClone.clone Ct1Sent.Insts.CoreCloneClone` for `uc`
      (identity clone on `Option Ct1Sent` — see `clone_option_ct1sent_spec`).
    - `core.option.Option.Insts.CoreCloneClone.clone PolynomialEncoder.Insts.CoreCloneClone` for
      `sending_ct1`
      (identity clone on `Option PolynomialEncoder` — see `clone_option_polynomial_encoder_spec`).
    - `core.option.Option.Insts.CoreCloneClone.clone PolynomialDecoder.Insts.CoreCloneClone` for
      `receiving_ek`
      (identity clone on `Option PolynomialDecoder` — see `clone_option_polynomial_decoder_spec`).
• Returns the resulting `Ct1Sampled` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 674–688):
  ```lean
  def proto.pq_ratchet.v1_state.chunked.Ct1Sampled.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.v1_state.chunked.Ct1Sampled) :
    Result proto.pq_ratchet.v1_state.chunked.Ct1Sampled
    := do
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.v1_state.unchunked.Ct1Sent.Insts.CoreCloneClone
        self.uc
    let o1 ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.PolynomialEncoder.Insts.CoreCloneClone self.sending_ct1
    let o2 ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.PolynomialDecoder.Insts.CoreCloneClone self.receiving_ek
    ok { uc := o, sending_ct1 := o1, receiving_ek := o2 }
  ```

• The function always succeeds (no panic / no error) for any `Ct1Sampled` input, since
  the `Option<Ct1Sent>` clone is total (see `V1_state/Unchunked/Ct1Sent/Clone.lean`), the
  `Option<PolynomialEncoder>` clone is total (see `PolynomialEncoder/Clone.lean`), and the
  `Option<PolynomialDecoder>` clone is total (see `PolynomialDecoder/Clone.lean`).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `Ct1Sampled`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone` and discharges the three `Option` field clones via `step*` using the
already-registered `clone_option_ct1sent_spec`, `clone_option_polynomial_encoder_spec`, and
`clone_option_polynomial_decoder_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 265:17-265:22)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.v1_state.chunked.Ct1Sampled) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.v1_state.chunked.Ct1Sampled) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  step*
  rw [o_post, o1_post, o2_post]

end spqr.proto.pq_ratchet.v1_state.chunked.Ct1Sampled
