/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::proto::pq_ratchet::chain::epoch::{impl core::clone::Clone for EpochDirection}::clone`

`EpochDirection` is the protobuf-generated product (record) type

  `EpochDirection ≃ { ctr : u32 ; next : Vec<u8> ; prev : Vec<u8> }`

representing the serialised form of a single direction (send or receive) within a chain epoch.
The three fields are:
  • `ctr : u32` — the current key counter for this direction.
  • `next : Vec<u8>` — the next key material (serialised as `bytes` in proto3).
  • `prev : Vec<u8>` — the previous key material (serialised as `bytes` in proto3).

The protobuf schema (src/proto/pq_ratchet.proto, lines 196–201), nested inside `Chain.Epoch`:
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

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 350:17-350:22
  impl Clone for EpochDirection {
      fn clone(&self) -> Self {
          EpochDirection {
              ctr: Clone::clone(&self.ctr),
              next: Clone::clone(&self.next),
              prev: Clone::clone(&self.prev),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `CloneU32.clone` for `ctr` (identity on `u32`).
  2. `CloneVec.clone CloneU8` for `next` (identity clone on `Vec<u8>`).
  3. `CloneVec.clone CloneU8` for `prev` (identity clone on `Vec<u8>`).

Because `u32` is `Copy` — and its derived `Clone::clone` returns the argument unchanged — the
`ctr` clone is the identity.  Because `u8` is `Copy`, the element-wise `Clone::clone` inside
`Vec<u8>` is the identity, making each `Vec<u8>` clone the identity as well.  Therefore the whole
struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 350:17-350:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.chain.epoch.EpochDirection

/-- `Vec<u8>` clone is the identity.

Because `u8` is `Copy`, its derived `Clone::clone` returns the argument unchanged.  The list-level
`Slice.clone` with the identity element-clone is therefore the identity, and
`alloc.vec.CloneVec.clone` wraps this in a `Vec`. -/
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
**Spec theorem for `proto.pq_ratchet.chain.epoch.EpochDirection.Insts.CoreCloneClone.clone`**:

• Takes an `EpochDirection` value `self` wrapping three fields:
    - `ctr : U32` — the current key counter for this direction.
    - `next : Vec U8` — the next key material (`bytes` in proto3).
    - `prev : Vec U8` — the previous key material (`bytes` in proto3).
• Delegates to field-wise cloning:
    - `core.clone.impls.CloneU32.clone` for `ctr` (identity on `U32`).
    - `alloc.vec.CloneVec.clone CloneU8` for `next` (identity clone on `Vec U8` —
      see `clone_vec_u8_spec`).
    - `alloc.vec.CloneVec.clone CloneU8` for `prev` (identity clone on `Vec U8` —
      see `clone_vec_u8_spec`).
• Returns the resulting `EpochDirection` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 450–460):
  ```lean
  def proto.pq_ratchet.chain.epoch.EpochDirection.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.chain.epoch.EpochDirection) :
    Result proto.pq_ratchet.chain.epoch.EpochDirection := do
    let i ← lift (core.clone.impls.CloneU32.clone self.ctr)
    let v ← alloc.vec.CloneVec.clone core.clone.CloneU8 self.next
    let v1 ← alloc.vec.CloneVec.clone core.clone.CloneU8 self.prev
    ok { ctr := i, next := v, prev := v1 }
  ```

• The function always succeeds (no panic / no error) for any `EpochDirection` input, since
  `CloneU32.clone` is total and each `Vec<u8>` clone is total (element-wise `CloneU8.clone` is
  the identity on bounded integers).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `EpochDirection`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone`, simplifies the trivial `CloneU32.clone` / `lift`, and discharges the
two `Vec U8` field clones via `step*` using the already-registered `clone_vec_u8_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 350:17-350:22)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.chain.epoch.EpochDirection) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.chain.epoch.EpochDirection) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  simp only [core.clone.impls.CloneU32.clone]
  simp only [lift]
  step*
  rw [v_post, v1_post]

end spqr.proto.pq_ratchet.chain.epoch.EpochDirection
