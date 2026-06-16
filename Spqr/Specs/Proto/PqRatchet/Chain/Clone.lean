/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Proto.PqRatchet.Chain.Epoch.Clone
import Spqr.Specs.Proto.PqRatchet.ChainParams.Clone
/-!
# Spec theorem for `spqr::proto::pq_ratchet::{impl core::clone::Clone for Chain}::clone`

`Chain` is the protobuf-generated product (record) type

  `Chain ≃ { direction : i32 ; current_epoch : u64 ; links : Vec<Epoch> ;
             next_root : Vec<u8> ; send_epoch : u64 ; params : Option<ChainParams> }`

representing the serialised form of a single ratchet chain.  The six fields are:
  • `direction : i32` — the chain direction, encoded as a protobuf `Direction` enum (mapped to
    `i32` by prost).
  • `current_epoch : u64` — the current epoch counter for this chain.
  • `links : Vec<Epoch>` — the list of epoch descriptors (`repeated Epoch` in proto3), each
    containing optional send and receive `EpochDirection` records.
  • `next_root : Vec<u8>` — the next root key material (`bytes` in proto3).
  • `send_epoch : u64` — the send epoch counter.
  • `params : Option<ChainParams>` — the optional chain parameters (max jump, max out-of-order
    keys).

The protobuf schema (src/proto/pq_ratchet.proto, lines 195–211):
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
    Direction direction = 1;
    uint64 current_epoch = 2;
    repeated Epoch links = 3;
    bytes next_root = 4;
    uint64 send_epoch = 5;
    ChainParams params = 6;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 302–308):
  ```lean
  structure proto.pq_ratchet.Chain where
    direction : Std.I32
    current_epoch : Std.U64
    links : alloc.vec.Vec proto.pq_ratchet.chain.Epoch
    next_root : alloc.vec.Vec Std.U8
    send_epoch : Std.U64
    params : Option proto.pq_ratchet.ChainParams
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 324:9-324:14
  impl Clone for Chain {
      fn clone(&self) -> Self {
          Chain {
              direction: Clone::clone(&self.direction),
              current_epoch: Clone::clone(&self.current_epoch),
              links: Clone::clone(&self.links),
              next_root: Clone::clone(&self.next_root),
              send_epoch: Clone::clone(&self.send_epoch),
              params: Clone::clone(&self.params),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `CloneI32.clone` for `direction` (identity on `i32`).
  2. `CloneU64.clone` for `current_epoch` (identity on `u64`).
  3. `CloneVec.clone Epoch.Insts.CoreCloneClone` for `links` (identity clone on
     `Vec<Epoch>` — each `Epoch` clone is the identity, as shown in `Epoch/Clone.lean`).
  4. `CloneVec.clone CloneU8` for `next_root` (identity clone on `Vec<u8>`).
  5. `CloneU64.clone` for `send_epoch` (identity on `u64`).
  6. `Option.clone ChainParams.Insts.CoreCloneClone` for `params` (identity clone on
     `Option<ChainParams>` — the `ChainParams` clone is the identity, as shown in
     `ChainParams/Clone.lean`).

Because `i32` and `u64` are `Copy` — and their derived `Clone::clone` returns the argument
unchanged — the scalar field clones are the identity.  Because `Epoch::clone` is the identity
(its fields are `Option<EpochDirection>` whose clone is the identity), the `Vec<Epoch>` clone is
the identity.  Because `u8` is `Copy`, the `Vec<u8>` clone is the identity.  Because
`ChainParams::clone` is the identity (both `u32` fields are `Copy`), the `Option<ChainParams>`
clone is the identity.  Therefore the whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 324:9-324:14)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.Chain

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

/-- `Epoch::clone` returns its argument unchanged (equality form).

This is the equality-level corollary of `Epoch.clone_spec` (see `Epoch/Clone.lean`), extracted via
`WP.spec_imp_exists` for use in `Slice.clone_spec` proofs at the `Vec<Epoch>` level.

The Rust `Epoch::clone` semantics:
  ```rust
  impl Clone for Epoch {
      fn clone(&self) -> Self {
          Epoch {
              send: Clone::clone(&self.send),
              recv: Clone::clone(&self.recv),
          }
      }
  }
  ``` -/
private lemma clone_epoch_id (x : proto.pq_ratchet.chain.Epoch) :
    proto.pq_ratchet.chain.Epoch.Insts.CoreCloneClone.clone x = ok x := by
  obtain ⟨r, hr, heq⟩ := WP.spec_imp_exists
    (spqr.proto.pq_ratchet.chain.Epoch.clone_spec x)
  subst heq; exact hr

/-- `Vec<Epoch>` clone is the identity.

The outer-level `Slice.clone` delegates to `Epoch::clone` (via the
`proto.pq_ratchet.chain.Epoch.Insts.CoreCloneClone` trait instance) for each element.  Since each
element-wise clone is the identity (`clone_epoch_id`), the outer clone is the identity as well.

The Rust `Vec<Epoch>::clone` semantics:
  ```rust
  impl Clone for Vec<Epoch> {
      fn clone(&self) -> Self {
          // element-wise clone, each Epoch::clone is identity
          self.iter().map(|x| x.clone()).collect()
      }
  }
  ``` -/
@[step]
private lemma clone_vec_epoch_spec (v : alloc.vec.Vec proto.pq_ratchet.chain.Epoch) :
    alloc.vec.CloneVec.clone proto.pq_ratchet.chain.Epoch.Insts.CoreCloneClone v
      ⦃ (r : alloc.vec.Vec proto.pq_ratchet.chain.Epoch) => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  apply WP.spec_mono
    (Slice.clone_spec (fun x _ => clone_epoch_id x))
  intro v' h
  exact h.symm

/-- `Option<ChainParams>` clone is the identity.

Because `ChainParams::clone` is the identity (see `ChainParams/Clone.lean`), and
`Option::clone` delegates to the element-level clone for `some` and is trivially the identity for
`none`, the `Option<ChainParams>` clone is the identity.

The Rust `Option<ChainParams>::clone` semantics:
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
private lemma clone_option_chain_params_spec
    (v : Option proto.pq_ratchet.ChainParams) :
    core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.ChainParams.Insts.CoreCloneClone v
      ⦃ (r : Option proto.pq_ratchet.ChainParams) => r = v ⦄ := by
  suffices h : core.option.Option.Insts.CoreCloneClone.clone
      proto.pq_ratchet.ChainParams.Insts.CoreCloneClone v = ok v by
    rw [h]; simp [WP.spec_ok]
  cases v with
  | none => simp [core.option.Option.Insts.CoreCloneClone.clone]
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone]
    have h := spqr.proto.pq_ratchet.ChainParams.clone_spec x
    obtain ⟨r, hr, heq⟩ := WP.spec_imp_exists h
    simp [hr, heq]

/--
**Spec theorem for `proto.pq_ratchet.Chain.Insts.CoreCloneClone.clone`**:

• Takes a `Chain` value `self` wrapping six fields:
    - `direction : I32` — the chain direction (protobuf `Direction` enum, mapped to `i32`).
    - `current_epoch : U64` — the current epoch counter.
    - `links : Vec Epoch` — the list of epoch descriptors.
    - `next_root : Vec U8` — the next root key material (`bytes` in proto3).
    - `send_epoch : U64` — the send epoch counter.
    - `params : Option ChainParams` — the optional chain parameters.
• Delegates to field-wise cloning:
    - `core.clone.impls.CloneI32.clone` for `direction` (identity on `I32`).
    - `core.clone.impls.CloneU64.clone` for `current_epoch` and `send_epoch` (identity on `U64`).
    - `alloc.vec.CloneVec.clone Epoch.Insts.CoreCloneClone` for `links`
      (identity clone on `Vec Epoch` — see `clone_vec_epoch_spec`).
    - `alloc.vec.CloneVec.clone CloneU8` for `next_root`
      (identity clone on `Vec U8` — see `clone_vec_u8_spec`).
    - `core.option.Option.Insts.CoreCloneClone.clone ChainParams.Insts.CoreCloneClone` for `params`
      (identity clone on `Option ChainParams` — see `clone_option_chain_params_spec`).
• Returns the resulting `Chain` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 499–519):
  ```lean
  def proto.pq_ratchet.Chain.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.Chain) : Result proto.pq_ratchet.Chain := do
    let i ← lift (core.clone.impls.CloneI32.clone self.direction)
    let i1 ← lift (core.clone.impls.CloneU64.clone self.current_epoch)
    let v ←
      alloc.vec.CloneVec.clone proto.pq_ratchet.chain.Epoch.Insts.CoreCloneClone
        self.links
    let v1 ← alloc.vec.CloneVec.clone core.clone.CloneU8 self.next_root
    let i2 ← lift (core.clone.impls.CloneU64.clone self.send_epoch)
    let o ←
      core.option.Option.Insts.CoreCloneClone.clone
        proto.pq_ratchet.ChainParams.Insts.CoreCloneClone self.params
    ok
      {
        direction := i,
        current_epoch := i1,
        links := v,
        next_root := v1,
        send_epoch := i2,
        params := o
      }
  ```

• The function always succeeds (no panic / no error) for any `Chain` input, since
  `CloneI32.clone` and `CloneU64.clone` are total, each `Epoch` clone is total (see
  `Epoch/Clone.lean`), the `Vec<u8>` clone is total (element-wise `CloneU8.clone` is the
  identity on bounded integers), and the `Option<ChainParams>` clone is total (see
  `ChainParams/Clone.lean`).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `Chain`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone`, simplifies the trivial `CloneI32.clone` / `CloneU64.clone` / `lift`,
and discharges the `Vec Epoch`, `Vec U8`, and `Option ChainParams` field clones via `step*`
using the already-registered `clone_vec_epoch_spec`, `clone_vec_u8_spec`, and
`clone_option_chain_params_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 324:9-324:14)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.Chain) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.Chain) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  simp only [core.clone.impls.CloneI32.clone]
  simp only [core.clone.impls.CloneU64.clone]
  simp only [lift]
  step*
  rw [v_post, v1_post, o_post]

end spqr.proto.pq_ratchet.Chain
