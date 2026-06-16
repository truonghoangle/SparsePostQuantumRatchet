/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::proto::pq_ratchet::{impl core::default::Default for PolynomialEncoder}::default`

`PolynomialEncoder` is the protobuf-generated product (record) type

  `PolynomialEncoder ≃ { idx : u32 ; pts : Vec<Vec<u8>> ; polys : Vec<Vec<u8>> }`

representing the serialised form of a polynomial encoder's state.  The three fields are:
  • `idx : u32` — the current index in the encoding sequence.
  • `pts : Vec<Vec<u8>>` — the list of serialised evaluation points (`repeated bytes` in proto3).
  • `polys : Vec<Vec<u8>>` — the list of serialised polynomials (`repeated bytes` in proto3).

The protobuf schema (src/proto/pq_ratchet.proto, lines 8–16):
  ```proto
  message PolynomialEncoder {
    uint32 idx = 1;
    repeated bytes pts = 2;
    repeated bytes polys = 3;
  }
  ```

The prost-generated Rust struct carries a `#[derive(Default)]`, producing:
  ```rust
  impl Default for PolynomialEncoder {
      fn default() -> Self {
          PolynomialEncoder {
              idx: 0u32,
              pts: Vec::new(),   // Vec<Vec<u8>>
              polys: Vec::new(), // Vec<Vec<u8>>
          }
      }
  }
  ```

The compiler-derived `Default::default` implementation constructs a `PolynomialEncoder` with every
field set to its proto3 default value:
  1. `idx` is set to `0 : u32` (the default for `uint32` in proto3).
  2. `pts` is set to `Vec::new()` (an empty `Vec<Vec<u8>>`), the default for `repeated bytes`.
  3. `polys` is set to `Vec::new()` (an empty `Vec<Vec<u8>>`), the default for `repeated bytes`.

Because `Vec::new()` is a pure constructor returning the empty vector, and `0#u32` is a constant,
the function is total and always succeeds:
  `default() = ok ⟨0, [], []⟩`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 2:37-2:53)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.PolynomialEncoder

/--
**Spec theorem for `proto.pq_ratchet.PolynomialEncoder.Insts.CoreDefaultDefault.default`**:

• Takes no arguments.
• Mirrors the Rust `Default::default()` which returns:
    ```rust
    PolynomialEncoder { idx: 0u32, pts: Vec::new(), polys: Vec::new() }
    ```
• In the Aeneas extraction this becomes:
    ```lean
    ok { idx := 0#u32,
         pts := alloc.vec.Vec.new (alloc.vec.Vec Std.U8),
         polys := alloc.vec.Vec.new (alloc.vec.Vec Std.U8) }
    ```
  where `alloc.vec.Vec.new T = ⟨[]⟩`.
• Returns the resulting `PolynomialEncoder` wrapped in `ok`.

• The function always succeeds (no panic / no error), since it constructs a fixed constant value
  with no fallible operations.
• The result is the canonical "zero" / "empty" `PolynomialEncoder`:
    `default() = ok ⟨0, [], []⟩`

The result satisfies the value-level specification:

  `result.idx = 0#u32 ∧ result.pts.val = [] ∧ result.polys.val = []`

The proof unfolds `default` and simplifies `Vec.new` to the empty list, then discharges the
conjunction by `simp`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 2:37-2:53)
-/
@[step]
theorem default_spec :
    Insts.CoreDefaultDefault.default ⦃ (result : proto.pq_ratchet.PolynomialEncoder) =>
      result.idx = 0#u32 ∧ result.pts.val = [] ∧ result.polys.val = [] ⦄ := by
  unfold Insts.CoreDefaultDefault.default
  simp [alloc.vec.Vec.new]

end spqr.proto.pq_ratchet.PolynomialEncoder
