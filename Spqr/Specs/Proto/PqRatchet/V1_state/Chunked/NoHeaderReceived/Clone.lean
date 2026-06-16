/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.V1_state.Unchunked.NoHeaderReceived.Clone
import Spqr.Specs.Proto.PqRatchet.PolynomialDecoder.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::v1_state::chunked::{impl core::clone::Clone for NoHeaderReceived}::clone`

`NoHeaderReceived` is the protobuf-generated product (record) type

  `NoHeaderReceived ≃ { uc : Option<Unchunked.NoHeaderReceived> ; receiving_hdr : Option<PolynomialDecoder> }`

representing the serialised form of the "no header received" state in the chunked ratchet protocol.
This is the initial send-CT state before any ML-KEM header has been received from the peer.  It
wraps the unchunked no-header-received sub-state and the polynomial decoder used to receive the
header in chunks.  The two fields are:
  • `uc : Option<Unchunked.NoHeaderReceived>` — the unchunked no-header-received sub-state
    (`Unchunked.NoHeaderReceived` in proto3; message fields are optional in prost).
  • `receiving_hdr : Option<PolynomialDecoder>` — the polynomial decoder accumulating header chunks
    (`PolynomialDecoder` in proto3; message fields are optional in prost).

The Rust source struct (src/v1/chunked/send_ct.rs, lines 14–21):
  ```rust
  #[cfg_attr(test, derive(Clone))]
  #[hax_lib::attributes]
  pub struct NoHeaderReceived {
      pub(super) uc: unchunked::NoHeaderReceived,
      // `receiving_hdr` only decodes messages of length
      //   `incremental_mlkem768::HEADER_SIZE + authenticator::Authenticator::MACSIZE`
      #[hax_lib::refine(receiving_hdr.get_pts_needed()
          == (incremental_mlkem768::HEADER_SIZE + authenticator::Authenticator::MACSIZE) / 2)]
      pub(super) receiving_hdr: polynomial::PolyDecoder,
  }
  ```

The protobuf schema (src/proto/pq_ratchet.proto, lines 150–153, inside `V1State.Chunked`):
  ```proto
  message NoHeaderReceived {
    Unchunked.NoHeaderReceived uc = 1;
    PolynomialDecoder receiving_hdr = 2;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 398–400):
  ```lean
  structure proto.pq_ratchet.v1_state.chunked.NoHeaderReceived where
    uc : Option proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived
    receiving_hdr : Option proto.pq_ratchet.PolynomialDecoder
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 251:17-251:22
  impl Clone for NoHeaderReceived {
      fn clone(&self) -> Self {
          NoHeaderReceived {
              uc: Clone::clone(&self.uc),
              receiving_hdr: Clone::clone(&self.receiving_hdr),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `Option::clone Unchunked.NoHeaderReceived.Insts.CoreCloneClone` for `uc` (identity clone on
     `Option<Unchunked.NoHeaderReceived>` — the `Unchunked.NoHeaderReceived` clone is the identity,
     as shown in `V1_state/Unchunked/NoHeaderReceived/Clone.lean`).
  2. `Option::clone PolynomialDecoder.Insts.CoreCloneClone` for `receiving_hdr` (identity clone on
     `Option<PolynomialDecoder>` — the `PolynomialDecoder` clone is the identity, as shown in
     `PolynomialDecoder/Clone.lean`).

Because `Unchunked.NoHeaderReceived::clone` is the identity (both fields — `epoch : u64`,
`auth : Option Authenticator` — have identity clones, as shown in
`V1_state/Unchunked/NoHeaderReceived/Clone.lean`), the `Option<Unchunked.NoHeaderReceived>` clone
is the identity.  Because `PolynomialDecoder::clone` is the identity (all four fields —
`pts_needed : u32`, `polys : u32`, `pts : Vec<Vec<u8>>`, `is_complete : bool` — have identity
clones, as shown in `PolynomialDecoder/Clone.lean`), the `Option<PolynomialDecoder>` clone is the
identity.  Therefore the whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 251:17-251:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.v1_state.chunked.NoHeaderReceived

/-- `Option<Unchunked.NoHeaderReceived>` clone is the identity.

Because `Unchunked.NoHeaderReceived::clone` is the identity (see
`V1_state/Unchunked/NoHeaderReceived/Clone.lean`), and `Option::clone` delegates to the
element-level clone for `some` and is trivially the identity for `none`, the
`Option<Unchunked.NoHeaderReceived>` clone is the identity.

The Rust `Option<Unchunked.NoHeaderReceived>::clone` semantics:
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
private lemma clone_option_unchunked_no_header_received_spec
    (v : Option proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived) :
    core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived.Insts.CoreCloneClone v
      ⦃ (r : Option proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived) => r = v ⦄ := by
  suffices h : core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived.Insts.CoreCloneClone v = ok v by
    rw [h]; simp [WP.spec_ok]
  cases v with
  | none => simp [core.option.Option.Insts.CoreCloneClone.clone]
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone]
    have h := spqr.proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived.clone_spec x
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
**Spec theorem for `proto.pq_ratchet.v1_state.chunked.NoHeaderReceived.Insts.CoreCloneClone.clone`**:

• Takes a `NoHeaderReceived` value `self` wrapping two fields:
    - `uc : Option Unchunked.NoHeaderReceived` — the unchunked no-header-received sub-state.
    - `receiving_hdr : Option PolynomialDecoder` — the polynomial decoder for header chunks.
• Delegates to field-wise cloning:
    - `core.option.Option.Insts.CoreCloneClone.clone
        Unchunked.NoHeaderReceived.Insts.CoreCloneClone` for `uc`
      (identity clone on `Option Unchunked.NoHeaderReceived` — see
      `clone_option_unchunked_no_header_received_spec`).
    - `core.option.Option.Insts.CoreCloneClone.clone PolynomialDecoder.Insts.CoreCloneClone` for
      `receiving_hdr`
      (identity clone on `Option PolynomialDecoder` — see `clone_option_polynomial_decoder_spec`).
• Returns the resulting `NoHeaderReceived` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 756–769):
  ```lean
  def proto.pq_ratchet.v1_state.chunked.NoHeaderReceived.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.v1_state.chunked.NoHeaderReceived) :
    Result proto.pq_ratchet.v1_state.chunked.NoHeaderReceived
    := do
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived.Insts.CoreCloneClone
        self.uc
    let o1 ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.PolynomialDecoder.Insts.CoreCloneClone
        self.receiving_hdr
    ok { uc := o, receiving_hdr := o1 }
  ```

• The function always succeeds (no panic / no error) for any `NoHeaderReceived` input, since
  the `Option<Unchunked.NoHeaderReceived>` clone is total (see
  `V1_state/Unchunked/NoHeaderReceived/Clone.lean`) and the `Option<PolynomialDecoder>` clone is
  total (see `PolynomialDecoder/Clone.lean`).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `NoHeaderReceived`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone` and discharges the two `Option` field clones via `step*` using the
already-registered `clone_option_unchunked_no_header_received_spec` and
`clone_option_polynomial_decoder_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 251:17-251:22)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.v1_state.chunked.NoHeaderReceived) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.v1_state.chunked.NoHeaderReceived) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  step*
  rw [o_post, o1_post]

end spqr.proto.pq_ratchet.v1_state.chunked.NoHeaderReceived
