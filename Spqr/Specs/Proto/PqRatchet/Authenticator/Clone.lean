/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::proto::pq_ratchet::{impl core::clone::Clone for Authenticator}::clone`

`Authenticator` is the protobuf-generated product (record) type

  `Authenticator ≃ { root_key : Vec<u8> ; mac_key : Vec<u8> }`

representing the serialised form of an HMAC authenticator state.  The two fields are:
  • `root_key : Vec<u8>` — the root key material from which per-epoch MAC keys are derived
    (`bytes` in proto3).
  • `mac_key : Vec<u8>` — the current MAC key used for authenticating messages
    (`bytes` in proto3).

The protobuf schema (src/proto/pq_ratchet.proto, lines 61–64):
  ```proto
  message Authenticator {
    bytes root_key = 1;
    bytes mac_key = 2;
  }
  ```

The Lean type definition (SrcTranslated/Types.lean, lines 313–315):
  ```lean
  structure proto.pq_ratchet.Authenticator where
    root_key : alloc.vec.Vec Std.U8
    mac_key : alloc.vec.Vec Std.U8
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  // Source: 'target/out/signal.proto.pq_ratchet.rs', lines 91:9-91:14
  impl Clone for Authenticator {
      fn clone(&self) -> Self {
          Authenticator {
              root_key: Clone::clone(&self.root_key),
              mac_key: Clone::clone(&self.mac_key),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `CloneVec.clone CloneU8` for `root_key` (identity clone on `Vec<u8>`).
  2. `CloneVec.clone CloneU8` for `mac_key` (identity clone on `Vec<u8>`).

Because `u8` is `Copy` — and its derived `Clone::clone` returns the argument unchanged — the
element-wise `Vec<u8>` clone is the identity for both fields.  Therefore the whole struct-level
clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 91:9-91:14)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.Authenticator

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
**Spec theorem for `proto.pq_ratchet.Authenticator.Insts.CoreCloneClone.clone`**:

• Takes an `Authenticator` value `self` wrapping two fields:
    - `root_key : Vec U8` — the root key material (`bytes` in proto3).
    - `mac_key : Vec U8` — the current MAC key (`bytes` in proto3).
• Delegates to field-wise cloning:
    - `alloc.vec.CloneVec.clone CloneU8` for `root_key`
      (identity clone on `Vec U8` — see `clone_vec_u8_spec`).
    - `alloc.vec.CloneVec.clone CloneU8` for `mac_key`
      (identity clone on `Vec U8` — see `clone_vec_u8_spec`).
• Returns the resulting `Authenticator` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 532–538):
  ```lean
  def proto.pq_ratchet.Authenticator.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.Authenticator) :
    Result proto.pq_ratchet.Authenticator := do
    let v ← alloc.vec.CloneVec.clone core.clone.CloneU8 self.root_key
    let v1 ← alloc.vec.CloneVec.clone core.clone.CloneU8 self.mac_key
    ok { root_key := v, mac_key := v1 }
  ```

• The function always succeeds (no panic / no error) for any `Authenticator` input, since
  each `Vec<u8>` clone is total (element-wise `CloneU8.clone` is the identity on bounded
  integers).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `Authenticator`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone` and discharges the two `Vec U8` field clones via `step*` using the
already-registered `clone_vec_u8_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 91:9-91:14)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.Authenticator) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.Authenticator) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  step*
  rw [v_post, v1_post]

end spqr.proto.pq_ratchet.Authenticator
