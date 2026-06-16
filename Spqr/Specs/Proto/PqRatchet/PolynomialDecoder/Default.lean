/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::proto::pq_ratchet::{impl core::default::Default for PolynomialDecoder}::default`

`PolynomialDecoder` is the protobuf-generated product (record) type

  `PolynomialDecoder ≃ { pts_needed : u32 ; polys : u32 ; pts : Vec<Vec<u8>> ; is_complete : bool }`

representing the serialised form of a polynomial decoder's state.  The four fields are:
  • `pts_needed : u32` — the number of evaluation points still needed before decoding can complete.
  • `polys : u32` — the number of polynomials accumulated so far.
  • `pts : Vec<Vec<u8>>` — the list of serialised evaluation points (`repeated bytes` in proto3).
  • `is_complete : bool` — whether enough points have been received for decoding.

The protobuf schema (src/proto/pq_ratchet.proto, lines 18–23):
  ```proto
  message PolynomialDecoder {
    uint32 pts_needed = 1;
    uint32 polys = 2;
    repeated bytes pts = 3;
    bool is_complete = 4;
  }
  ```

The prost-generated Rust struct carries a `#[derive(Default)]`, producing:
  ```rust
  impl Default for PolynomialDecoder {
      fn default() -> Self {
          PolynomialDecoder {
              pts_needed: 0u32,
              polys: 0u32,
              pts: Vec::new(),       // Vec<Vec<u8>>
              is_complete: false,
          }
      }
  }
  ```

The compiler-derived `Default::default` implementation constructs a `PolynomialDecoder` with every
field set to its proto3 default value:
  1. `pts_needed` is set to `0 : u32` (the default for `uint32` in proto3).
  2. `polys` is set to `0 : u32` (the default for `uint32` in proto3).
  3. `pts` is set to `Vec::new()` (an empty `Vec<Vec<u8>>`), the default for `repeated bytes`.
  4. `is_complete` is set to `false` (the default for `bool` in proto3).

Because `Vec::new()` is a pure constructor returning the empty vector, `0#u32` is a constant, and
`false` is a constant, the function is total and always succeeds:
  `default() = ok ⟨0, 0, [], false⟩`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 14:37-14:53)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.PolynomialDecoder

/--
**Spec theorem for `proto.pq_ratchet.PolynomialDecoder.Insts.CoreDefaultDefault.default`**:

• Takes no arguments.
• Mirrors the Rust `Default::default()` which returns:
    ```rust
    PolynomialDecoder { pts_needed: 0u32, polys: 0u32, pts: Vec::new(), is_complete: false }
    ```
• In the Aeneas extraction this becomes:
    ```lean
    ok { pts_needed := 0#u32,
         polys := 0#u32,
         pts := alloc.vec.Vec.new (alloc.vec.Vec Std.U8),
         is_complete := false }
    ```
  where `alloc.vec.Vec.new T = ⟨[]⟩`.
• Returns the resulting `PolynomialDecoder` wrapped in `ok`.

• The function always succeeds (no panic / no error), since it constructs a fixed constant value
  with no fallible operations.
• The result is the canonical "zero" / "empty" `PolynomialDecoder`:
    `default() = ok ⟨0, 0, [], false⟩`

The result satisfies the value-level specification:

  `result.pts_needed = 0#u32 ∧ result.polys = 0#u32
   ∧ result.pts.val = [] ∧ result.is_complete = false`

The proof unfolds `default` and simplifies `Vec.new` to the empty list, then discharges the
conjunction by `simp`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 14:37-14:53)
-/
@[step]
theorem default_spec :
    Insts.CoreDefaultDefault.default ⦃ (result : proto.pq_ratchet.PolynomialDecoder) =>
      result.pts_needed = 0#u32 ∧ result.polys = 0#u32
      ∧ result.pts.val = [] ∧ result.is_complete = false ⦄ := by
  unfold Insts.CoreDefaultDefault.default
  simp [alloc.vec.Vec.new]

end spqr.proto.pq_ratchet.PolynomialDecoder
