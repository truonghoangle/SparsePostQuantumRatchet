/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.V1_state.Unchunked.HeaderReceived.Clone
import Spqr.Specs.Proto.PqRatchet.PolynomialDecoder.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::v1_state::chunked::{impl core::clone::Clone for HeaderReceived}::clone`

`HeaderReceived` is the protobuf-generated product (record) type

  `HeaderReceived ≃ { uc : Option<Unchunked.HeaderReceived> ; receiving_ek : Option<PolynomialDecoder> }`

representing the serialised form of the "header received" state in the chunked ratchet protocol.
After an ML-KEM header has been fully received (all chunks assembled) from the peer, this state
records the unchunked header-received sub-state and the polynomial decoder used to receive the
encapsulation key in chunks.  The two fields are:
  • `uc : Option<Unchunked.HeaderReceived>` — the unchunked header-received sub-state
    (`Unchunked.HeaderReceived` in proto3; message fields are optional in prost).
  • `receiving_ek : Option<PolynomialDecoder>` — the polynomial decoder accumulating encapsulation
    key chunks (`PolynomialDecoder` in proto3; message fields are optional in prost).

The Rust source struct (src/v1/chunked/send_ct.rs, lines 23–30):
  ```rust
  #[cfg_attr(test, derive(Clone))]
  #[hax_lib::attributes]
  pub struct HeaderReceived {
      uc: unchunked::HeaderReceived,
      // `receiving_ek` only decodes messages of length `incremental_mlkem768::ENCAPSULATION_KEY_SIZE`
      #[hax_lib::refine(receiving_ek.get_pts_needed() == incremental_mlkem768::ENCAPSULATION_KEY_SIZE / 2)]
      receiving_ek: polynomial::PolyDecoder,
  }
  ```

The protobuf schema (src/proto/pq_ratchet.proto, lines 154–157, inside `V1State.Chunked`):
  ```proto
  message HeaderReceived {
    Unchunked.HeaderReceived uc = 1;
    PolynomialDecoder receiving_ek = 2;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 384–386):
  ```lean
  structure proto.pq_ratchet.v1_state.chunked.HeaderReceived where
    uc : Option proto.pq_ratchet.v1_state.unchunked.HeaderReceived
    receiving_ek : Option proto.pq_ratchet.PolynomialDecoder
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 258:17-258:22
  impl Clone for HeaderReceived {
      fn clone(&self) -> Self {
          HeaderReceived {
              uc: Clone::clone(&self.uc),
              receiving_ek: Clone::clone(&self.receiving_ek),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `Option::clone Unchunked.HeaderReceived.Insts.CoreCloneClone` for `uc` (identity clone on
     `Option<Unchunked.HeaderReceived>` — the `Unchunked.HeaderReceived` clone is the identity, as
     shown in `V1_state/Unchunked/HeaderReceived/Clone.lean`).
  2. `Option::clone PolynomialDecoder.Insts.CoreCloneClone` for `receiving_ek` (identity clone on
     `Option<PolynomialDecoder>` — the `PolynomialDecoder` clone is the identity, as shown in
     `PolynomialDecoder/Clone.lean`).

Because `Unchunked.HeaderReceived::clone` is the identity (all three fields — `epoch : u64`,
`auth : Option Authenticator`, `hdr : Vec<u8>` — have identity clones, as shown in
`V1_state/Unchunked/HeaderReceived/Clone.lean`), the `Option<Unchunked.HeaderReceived>` clone is
the identity.  Because `PolynomialDecoder::clone` is the identity (all four fields — `pts_needed :
u32`, `polys : u32`, `pts : Vec<Vec<u8>>`, `is_complete : bool` — have identity clones, as shown
in `PolynomialDecoder/Clone.lean`), the `Option<PolynomialDecoder>` clone is the identity.
Therefore the whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 258:17-258:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.v1_state.chunked.HeaderReceived

/-- `Option<Unchunked.HeaderReceived>` clone is the identity.

Because `Unchunked.HeaderReceived::clone` is the identity (see
`V1_state/Unchunked/HeaderReceived/Clone.lean`), and `Option::clone` delegates to the element-level
clone for `some` and is trivially the identity for `none`, the `Option<Unchunked.HeaderReceived>`
clone is the identity.

The Rust `Option<Unchunked.HeaderReceived>::clone` semantics:
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
private lemma clone_option_unchunked_header_received_spec
    (v : Option proto.pq_ratchet.v1_state.unchunked.HeaderReceived) :
    core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.HeaderReceived.Insts.CoreCloneClone v
      ⦃ (r : Option proto.pq_ratchet.v1_state.unchunked.HeaderReceived) => r = v ⦄ := by
  suffices h : core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.v1_state.unchunked.HeaderReceived.Insts.CoreCloneClone v = ok v by
    rw [h]; simp [WP.spec_ok]
  cases v with
  | none => simp [core.option.Option.Insts.CoreCloneClone.clone]
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone]
    have h := spqr.proto.pq_ratchet.v1_state.unchunked.HeaderReceived.clone_spec x
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
**Spec theorem for `proto.pq_ratchet.v1_state.chunked.HeaderReceived.Insts.CoreCloneClone.clone`**:

• Takes a `HeaderReceived` value `self` wrapping two fields:
    - `uc : Option Unchunked.HeaderReceived` — the unchunked header-received sub-state.
    - `receiving_ek : Option PolynomialDecoder` — the polynomial decoder for encapsulation key
      chunks.
• Delegates to field-wise cloning:
    - `core.option.Option.Insts.CoreCloneClone.clone
        Unchunked.HeaderReceived.Insts.CoreCloneClone` for `uc`
      (identity clone on `Option Unchunked.HeaderReceived` — see
      `clone_option_unchunked_header_received_spec`).
    - `core.option.Option.Insts.CoreCloneClone.clone PolynomialDecoder.Insts.CoreCloneClone` for
      `receiving_ek`
      (identity clone on `Option PolynomialDecoder` — see `clone_option_polynomial_decoder_spec`).
• Returns the resulting `HeaderReceived` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 717–728):
  ```lean
  def proto.pq_ratchet.v1_state.chunked.HeaderReceived.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.v1_state.chunked.HeaderReceived) :
    Result proto.pq_ratchet.v1_state.chunked.HeaderReceived
    := do
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.v1_state.unchunked.HeaderReceived.Insts.CoreCloneClone
        self.uc
    let o1 ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.PolynomialDecoder.Insts.CoreCloneClone self.receiving_ek
    ok { uc := o, receiving_ek := o1 }
  ```

• The function always succeeds (no panic / no error) for any `HeaderReceived` input, since
  the `Option<Unchunked.HeaderReceived>` clone is total (see
  `V1_state/Unchunked/HeaderReceived/Clone.lean`) and the `Option<PolynomialDecoder>` clone is
  total (see `PolynomialDecoder/Clone.lean`).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `HeaderReceived`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone` and discharges the two `Option` field clones via `step*` using the
already-registered `clone_option_unchunked_header_received_spec` and
`clone_option_polynomial_decoder_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 258:17-258:22)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.v1_state.chunked.HeaderReceived) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.v1_state.chunked.HeaderReceived) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  step*
  rw [o_post, o1_post]

end spqr.proto.pq_ratchet.v1_state.chunked.HeaderReceived
