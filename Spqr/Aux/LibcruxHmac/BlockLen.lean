/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Types
import Spqr.Aux.LibcruxHmac.HashLen

/-!
# Block length of `libcrux_hmac::Algorithm`

Each hash algorithm used by `libcrux_hmac::hmac` has a fixed internal block
size in bytes (the HMAC construction pads/hashes the key to this block
length):

| Algorithm | Block length (bytes) |
|-----------|---------------------|
| SHA-1     | 64                  |
| SHA-256   | 64                  |
| SHA-384   | 128                 |
| SHA-512   | 128                 |

(cf. FIPS 180-2 §1 / §6; SHA-1 and SHA-256 operate on 64-byte blocks,
SHA-384 and SHA-512 on 128-byte blocks.)

This file defines `Algorithm.block_len : Algorithm → Nat` together with:

natural language specs:
- `block_len_Sha1 … block_len_Sha512`: per-constructor values (`rfl`, `@[simp]`);
- `block_len_pos`: every block length is positive;
- `hash_len_le_block_len`: the digest length never exceeds the block length
  (needed by the HMAC key-normalization step).

**Source**: FIPS 180-2 §1/§6; 'libcrux-hmac-0.0.6/src/hacl/hmac.rs'
  (block sizes visible in the `let l: u32 = …` assignments of
  `compute_sha1` (64), `compute_sha2_256` (64), `compute_sha2_384` (128),
  `compute_sha2_512` (128)).
-/

open Aeneas Aeneas.Std Result

namespace spqr.libcrux_hmac

/-- Internal block length in bytes of each HMAC hash algorithm:
    `Sha1/Sha256 ↦ 64`, `Sha384/Sha512 ↦ 128`.

    This is the block size `B` of the underlying hash function used by the
    HMAC construction (RFC 2104 §2) to pad/hash the key.

    **Source**: FIPS 180-2 §1/§6;
    'libcrux-hmac-0.0.6/src/hacl/hmac.rs' (`let l: u32`) -/
def Algorithm.block_len : Algorithm → Nat
  | .Sha1   => 64
  | .Sha256 => 64
  | .Sha384 => 128
  | .Sha512 => 128

/-- **Spec lemma for `Algorithm.block_len`**: SHA-1 block size is 64 bytes. -/
@[simp]
theorem Algorithm.block_len_Sha1 : Algorithm.Sha1.block_len = 64 := rfl

/-- **Spec lemma for `Algorithm.block_len`**: SHA-256 block size is 64 bytes. -/
@[simp]
theorem Algorithm.block_len_Sha256 : Algorithm.Sha256.block_len = 64 := rfl

/-- **Spec lemma for `Algorithm.block_len`**: SHA-384 block size is 128 bytes. -/
@[simp]
theorem Algorithm.block_len_Sha384 : Algorithm.Sha384.block_len = 128 := rfl

/-- **Spec lemma for `Algorithm.block_len`**: SHA-512 block size is 128 bytes. -/
@[simp]
theorem Algorithm.block_len_Sha512 : Algorithm.Sha512.block_len = 128 := rfl

/-- **Spec lemma for `Algorithm.block_len`**: every block length is positive. -/
theorem Algorithm.block_len_pos (alg : Algorithm) : 0 < alg.block_len := by
  cases alg <;> simp

/-- **Spec lemma**: the digest length never exceeds the block length
    (`hLen ≤ B`), which is required by the HMAC key-normalization step
    (RFC 2104 §2: the hash-if-long branch needs `hLen ≤ B` so that zero-padding
    to `B` bytes is well-defined). -/
theorem Algorithm.hash_len_le_block_len (alg : Algorithm) :
    alg.hash_len ≤ alg.block_len := by
  cases alg <;> simp

end spqr.libcrux_hmac
