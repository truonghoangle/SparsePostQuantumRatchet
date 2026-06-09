/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::authenticator::Authenticator::MACSIZE`

`MACSIZE` is the associated constant on `Authenticator` defining the byte length of a MAC
(Message Authentication Code) produced by the authenticator in the Sparse Post-Quantum Ratchet.
Each MAC is computed via HMAC-SHA-256 and is truncated (or asserted) to exactly `MACSIZE` bytes.
The constant is exposed in Rust as

  `pub const MACSIZE: usize = 32usize;`

inside the `impl Authenticator` block. It is used in `hax_lib` annotations to constrain the
length of MAC slices throughout the authenticator layer:
  • `#[hax_lib::requires(expected_mac.len() == Authenticator::MACSIZE)]` on `verify_ct` and
    `verify_hdr`,
  • `#[hax_lib::ensures(|res| res.len() == Authenticator::MACSIZE)]` on `mac_ct` and `mac_hdr`.

The constant is unconditional and pure — its evaluation never fails and never depends on any
input. Its value `32` matches the output length of SHA-256 (256 bits = 32 bytes).

**Source**: spqr/src/authenticator.rs (lines 34:4-34:39)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.authenticator.Authenticator

/-
natural language description:

• `MACSIZE` is a public associated constant of type `usize`
  on `Authenticator`.
• It is defined as the literal `32`, recording the byte length
  of every HMAC-SHA-256 tag produced or verified by the
  authenticator.
• The constant is unconditional and pure — its evaluation never
  fails and never depends on any input.

natural language specs:

• The underlying `usize` value of `MACSIZE` is `32`:
    `MACSIZE = 32#usize`
  and equivalently as a natural number:
    `MACSIZE.val = 32`.
• The value `32` coincides with the output length of SHA-256,
  which is the hash function used by HMAC in the authenticator.
-/

/-- **The `usize` value of `MACSIZE` is `32#usize`**. -/
@[simp]
theorem MACSIZE_eq :
    MACSIZE = 32#usize := by
  simp [MACSIZE]

/--
**The underlying natural-number value of `MACSIZE` is `32`**.
-/
@[simp]
theorem MACSIZE_val :
    MACSIZE.val = 32 := by
  simp

/--
**Spec and proof concerning `authenticator.Authenticator.MACSIZE`**:

`MACSIZE` is the constant `32 : usize`, recording the byte length of every HMAC-SHA-256 tag
produced or verified by the `Authenticator`. The value `32` matches the output length of SHA-256
(256 bits = 32 bytes), which is the hash function underlying the HMAC computation in
`mac_ct` and `mac_hdr`.

Concretely:

  `MACSIZE.val = 32`

The proof unfolds the definition and reduces the `usize` literal `32#usize` to its natural-number
value.

**Source**: spqr/src/authenticator.rs (lines 34:4-34:39)
-/
@[step]
theorem MACSIZE_spec :
    ok MACSIZE ⦃ (result : Std.Usize) =>
      result.val = 32 ⦄ := by
  simp

end spqr.authenticator.Authenticator
