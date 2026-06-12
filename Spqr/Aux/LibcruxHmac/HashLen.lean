/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Types

/-!
# Digest length of `libcrux_hmac::Algorithm`

`libcrux_hmac::Algorithm` enumerates the hash algorithms supported by
`libcrux_hmac::hmac`.  Each algorithm has a fixed digest (output) length in
bytes, mirrored by `libcrux_hmac::tag_size` in the Rust crate:

```rust
pub const fn tag_size(alg: Algorithm) -> usize {
    match alg {
        Algorithm::Sha1 => 20,
        Algorithm::Sha256 => 32,
        Algorithm::Sha384 => 48,
        Algorithm::Sha512 => 64,
    }
}
```

This file defines `Algorithm.hash_len : Algorithm → Nat` (the natural tag
length used when `hmac` is called with `tag_length = None`), together with:

natural language specs:
- `hash_len_Sha1 … hash_len_Sha512`: per-constructor values (`rfl`, `@[simp]`);
- `hash_len_pos`: every digest length is positive;
- `hash_len_le`: every digest length is at most 64 (the SHA-512 digest length).

**Source**: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-hmac-0.0.6/src/hmac.rs'
-/

open Aeneas Aeneas.Std Result

namespace spqr.libcrux_hmac

/-- Digest (output) length in bytes of each HMAC hash algorithm:
    `Sha1 ↦ 20`, `Sha256 ↦ 32`, `Sha384 ↦ 48`, `Sha512 ↦ 64`.

    This is the natural tag length used by `libcrux_hmac::hmac` when called
    with `tag_length = None` (cf. `libcrux_hmac::tag_size`).

    **Source**: 'libcrux-hmac-0.0.6/src/hmac.rs' (`tag_size`) -/
def Algorithm.hash_len : Algorithm → Nat
  | .Sha1 => 20
  | .Sha256 => 32
  | .Sha384 => 48
  | .Sha512 => 64

/-- **Spec lemma for `Algorithm.hash_len`**: the SHA-1 digest length is 20 bytes. -/
@[simp]
theorem Algorithm.hash_len_Sha1 : Algorithm.Sha1.hash_len = 20 := rfl

/-- **Spec lemma for `Algorithm.hash_len`**: the SHA-256 digest length is 32 bytes. -/
@[simp]
theorem Algorithm.hash_len_Sha256 : Algorithm.Sha256.hash_len = 32 := rfl

/-- **Spec lemma for `Algorithm.hash_len`**: the SHA-384 digest length is 48 bytes. -/
@[simp]
theorem Algorithm.hash_len_Sha384 : Algorithm.Sha384.hash_len = 48 := rfl

/-- **Spec lemma for `Algorithm.hash_len`**: the SHA-512 digest length is 64 bytes. -/
@[simp]
theorem Algorithm.hash_len_Sha512 : Algorithm.Sha512.hash_len = 64 := rfl

/-- **Spec lemma for `Algorithm.hash_len`**: every digest length is positive. -/
theorem Algorithm.hash_len_pos (alg : Algorithm) : 0 < alg.hash_len := by
  cases alg <;> simp

/-- **Spec lemma for `Algorithm.hash_len`**: every digest length is at most 64
    bytes (the SHA-512 digest length). -/
theorem Algorithm.hash_len_le (alg : Algorithm) : alg.hash_len ≤ 64 := by
  cases alg <;> simp

end spqr.libcrux_hmac
