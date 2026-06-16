/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.Chain.Epoch.EpochDirection.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::chain::{impl core::clone::Clone for Epoch}::clone`

`Epoch` is the protobuf-generated product (record) type

  `Epoch ≃ { send : Option EpochDirection ; recv : Option EpochDirection }`

representing the serialised form of a single chain epoch, containing optional send and receive
direction descriptors.  The two fields are:
  • `send : Option EpochDirection` — the optional send-direction state for this epoch.
  • `recv : Option EpochDirection` — the optional receive-direction state for this epoch.

The protobuf schema (src/proto/pq_ratchet.proto, lines 196–204), nested inside `Chain`:
  ```proto
  message Chain {
    message Epoch {
      message EpochDirection {
        uint32 ctr = 1;
        bytes next = 2;
        bytes prev = 3;
      }
      EpochDirection send = 1;
      EpochDirection recv = 2;
    }
    ...
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 295–297):
  ```lean
  structure proto.pq_ratchet.chain.Epoch where
    send : Option proto.pq_ratchet.chain.epoch.EpochDirection
    recv : Option proto.pq_ratchet.chain.epoch.EpochDirection
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 341:13-341:18
  impl Clone for Epoch {
      fn clone(&self) -> Self {
          Epoch {
              send: Clone::clone(&self.send),
              recv: Clone::clone(&self.recv),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `Option::clone` with `EpochDirection::clone` for `send` (identity on
     `Option<EpochDirection>`).
  2. `Option::clone` with `EpochDirection::clone` for `recv` (identity on
     `Option<EpochDirection>`).

Because `EpochDirection::clone` is the identity — its three fields (`ctr : u32`,
`next : Vec<u8>`, `prev : Vec<u8>`) all have identity clones, as shown in
`EpochDirection/Clone.lean` — the `Option<EpochDirection>` clone is also the identity:
  - `None.clone()` returns `None` unchanged.
  - `Some(x).clone()` returns `Some(x.clone()) = Some(x)` since `x.clone() = x`.

Therefore the whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 341:13-341:18)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.chain.Epoch

/-- `Option<EpochDirection>` clone is the identity.

Because `EpochDirection::clone` is the identity (see `EpochDirection/Clone.lean`), and
`Option::clone` delegates to the element-level clone for `some` and is trivially the identity for
`none`, the `Option<EpochDirection>` clone is the identity.

The Rust `Option::clone` semantics:
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
private lemma clone_option_epoch_direction_spec
    (v : Option proto.pq_ratchet.chain.epoch.EpochDirection) :
    core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.chain.epoch.EpochDirection.Insts.CoreCloneClone v
      ⦃ (r : Option proto.pq_ratchet.chain.epoch.EpochDirection) => r = v ⦄ := by
  suffices h : core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.chain.epoch.EpochDirection.Insts.CoreCloneClone v = ok v by
    rw [h]; simp [WP.spec_ok]
  cases v with
  | none => simp [core.option.Option.Insts.CoreCloneClone.clone]
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone]
    have h := spqr.proto.pq_ratchet.chain.epoch.EpochDirection.clone_spec x
    obtain ⟨r, hr, heq⟩ := WP.spec_imp_exists h
    simp [hr, heq]

/--
**Spec theorem for `proto.pq_ratchet.chain.Epoch.Insts.CoreCloneClone.clone`**:

• Takes an `Epoch` value `self` wrapping two fields:
    - `send : Option EpochDirection` — the optional send-direction state for this epoch.
    - `recv : Option EpochDirection` — the optional receive-direction state for this epoch.
• Delegates to field-wise cloning:
    - `core.option.Option.Insts.CoreCloneClone.clone EpochDirection.Insts.CoreCloneClone` for
      `send` (identity clone on `Option EpochDirection` — see `clone_option_epoch_direction_spec`).
    - `core.option.Option.Insts.CoreCloneClone.clone EpochDirection.Insts.CoreCloneClone` for
      `recv` (identity clone on `Option EpochDirection` — see `clone_option_epoch_direction_spec`).
• Returns the resulting `Epoch` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 474–486):
  ```lean
  def proto.pq_ratchet.chain.Epoch.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.chain.Epoch) :
    Result proto.pq_ratchet.chain.Epoch := do
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.chain.epoch.EpochDirection.Insts.CoreCloneClone
        self.send
    let o1 ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.chain.epoch.EpochDirection.Insts.CoreCloneClone
        self.recv
    ok { send := o, recv := o1 }
  ```

• The function always succeeds (no panic / no error) for any `Epoch` input, since the
  `EpochDirection` clone is total and the `Option` clone dispatches to it for `some` values
  and is trivially total for `none`.
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `Epoch`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone` and discharges the two `Option EpochDirection` field clones via `step*`
using the already-registered `clone_option_epoch_direction_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 341:13-341:18)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.chain.Epoch) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.chain.Epoch) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  step*
  rw [o_post, o1_post]

end spqr.proto.pq_ratchet.chain.Epoch
