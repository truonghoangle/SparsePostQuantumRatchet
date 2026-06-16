/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::proto::pq_ratchet::{impl core::clone::Clone for ChainParams}::clone`

`ChainParams` is the protobuf-generated product (record) type

  `ChainParams ≃ { max_jump : u32 ; max_ooo_keys : u32 }`

representing the chain-level configuration parameters.  The two fields are:
  • `max_jump : u32` — the maximum allowed forward jump from the current counter (`ctr`);
    disallows requesting a key more than `max_jump` positions ahead.
    If zero, defaults to 25 000.
  • `max_ooo_keys : u32` — the number of old keys to retain for out-of-order message decryption;
    messages older than `ctr - max_ooo_keys` that arrive out-of-order will fail with
    `Error::KeyTrimmed`.

The protobuf schema (src/proto/pq_ratchet.proto, lines 223–231):
  ```proto
  message ChainParams {
    // Disallow requesting a key that is more than MAX_JUMP ahead of `ctr`.
    // If zero, defaults to 25,000.
    uint32 max_jump = 1;
    // Keep around keys back to at least `ctr - MAX_OOO_KEYS`, in case an
    // out-of-order message comes in.  Messages older than this that arrive
    // out-of-order will not be able to be decrypted and will return
    // Error::KeyTrimmed.
    uint32 max_ooo_keys = 2;
  }
  ```

The prost-generated Rust struct carries `#[derive(Clone, Copy)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone, Copy)]
  impl Clone for ChainParams {
      fn clone(&self) -> Self {
          ChainParams {
              max_jump: Clone::clone(&self.max_jump),
              max_ooo_keys: Clone::clone(&self.max_ooo_keys),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `CloneU32.clone` for `max_jump` (identity on `u32`).
  2. `CloneU32.clone` for `max_ooo_keys` (identity on `u32`).

Because `u32` is `Copy` — and its derived `Clone::clone` returns the argument unchanged — both
field-level clones are the identity.  The struct also derives `Copy`, so Aeneas optimises the
entire clone body to a plain return of the input value.  Therefore the whole struct-level clone
is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 361:9-361:14)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.ChainParams

/--
**Spec theorem for `proto.pq_ratchet.ChainParams.Insts.CoreCloneClone.clone`**:

• Takes a `ChainParams` value `self` wrapping two fields:
    - `max_jump : U32` — the maximum forward-jump distance for key requests.
    - `max_ooo_keys : U32` — the retention window size for out-of-order keys.
• Because both fields are `Copy` (`u32`), the derived `Clone::clone` is the identity on each
  field, and the struct itself derives `Copy`.  Aeneas accordingly simplifies the clone body to
  a direct return:
    ```lean
    def proto.pq_ratchet.ChainParams.Insts.CoreCloneClone.clone
      (self : proto.pq_ratchet.ChainParams) :
      Result proto.pq_ratchet.ChainParams := do
      ok self
    ```
• Returns the resulting `ChainParams` unchanged.

• The function always succeeds (no panic / no error) for any `ChainParams` input, since the
  body is simply `ok self`.
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `ChainParams`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone` to expose the trivial `ok self` body, and the resulting goal is
discharged by `simp`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 361:9-361:14)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.ChainParams) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.ChainParams) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  simp

end spqr.proto.pq_ratchet.ChainParams
