/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Aeneas

/-!
# SHA-2 constants (FIPS 180-2 §4.2.2, §4.2.3, §5.3.2–§5.3.4)

The SHA-2 family uses two constant tables and per-variant initial hash
values:

* **`K^{256}`** (FIPS 180-2 §4.2.2): sixty-four 32-bit words used by SHA-256
  (the first thirty-two bits of the fractional parts of the cube roots of
  the first sixty-four primes).
* **`K^{512}`** (FIPS 180-2 §4.2.3): eighty 64-bit words used by SHA-384 and
  SHA-512 (the first sixty-four bits of the fractional parts of the cube
  roots of the first eighty primes).
* **Initial hash values**: SHA-256 (§5.3.2), SHA-384 (§5.3.3) and SHA-512
  (§5.3.4) each have a distinct eight-word IV.  SHA-384's IV (§5.3.3) is
  exactly what distinguishes it from a plainly truncated SHA-512.

This file defines:

* `k256` — the 64-word `K^{256}` table as a `List U32` (S3);
* `k512` — the 80-word `K^{512}` table as a `List U64` (S3);
* `sha256H0` — the SHA-256 IV (8 × `U32`) (S3);
* `sha384H0` — the SHA-384 IV (8 × `U64`) (S3);
* `sha512H0` — the SHA-512 IV (8 × `U64`) (S3);

together with:

natural language specs:
- `k256_length` (SL11): `K^{256}` has exactly 64 words;
- `k512_length` (SL11): `K^{512}` has exactly 80 words;
- `sha256H0_length` / `sha384H0_length` / `sha512H0_length` (SL11): every IV
  has exactly 8 words;
- `sha384H0_ne_sha512H0`: the SHA-384 and SHA-512 IVs differ (so SHA-384 is
  not a plainly truncated SHA-512).

The numeric values are transcribed from FIPS 180-2; value-level correctness
of the pipeline is gated by the test vectors of Step 1.7.

**Source**: FIPS 180-2 §4.2.2 (`K^{256}`), §4.2.3 (`K^{512}`),
§5.3.2–§5.3.4 (SHA-256/384/512 IVs).
-/

open Aeneas Aeneas.Std

namespace spec.sha

/-! ## `K^{256}` round constants (FIPS 180-2 §4.2.2) -/

/-- The sixty-four SHA-256 round constants `K^{256}` (FIPS 180-2 §4.2.2):
    the first thirty-two bits of the fractional parts of the cube roots of
    the first sixty-four prime numbers. -/
def k256 : List U32 :=
  [0x428a2f98#u32, 0x71374491#u32, 0xb5c0fbcf#u32, 0xe9b5dba5#u32,
   0x3956c25b#u32, 0x59f111f1#u32, 0x923f82a4#u32, 0xab1c5ed5#u32,
   0xd807aa98#u32, 0x12835b01#u32, 0x243185be#u32, 0x550c7dc3#u32,
   0x72be5d74#u32, 0x80deb1fe#u32, 0x9bdc06a7#u32, 0xc19bf174#u32,
   0xe49b69c1#u32, 0xefbe4786#u32, 0x0fc19dc6#u32, 0x240ca1cc#u32,
   0x2de92c6f#u32, 0x4a7484aa#u32, 0x5cb0a9dc#u32, 0x76f988da#u32,
   0x983e5152#u32, 0xa831c66d#u32, 0xb00327c8#u32, 0xbf597fc7#u32,
   0xc6e00bf3#u32, 0xd5a79147#u32, 0x06ca6351#u32, 0x14292967#u32,
   0x27b70a85#u32, 0x2e1b2138#u32, 0x4d2c6dfc#u32, 0x53380d13#u32,
   0x650a7354#u32, 0x766a0abb#u32, 0x81c2c92e#u32, 0x92722c85#u32,
   0xa2bfe8a1#u32, 0xa81a664b#u32, 0xc24b8b70#u32, 0xc76c51a3#u32,
   0xd192e819#u32, 0xd6990624#u32, 0xf40e3585#u32, 0x106aa070#u32,
   0x19a4c116#u32, 0x1e376c08#u32, 0x2748774c#u32, 0x34b0bcb5#u32,
   0x391c0cb3#u32, 0x4ed8aa4a#u32, 0x5b9cca4f#u32, 0x682e6ff3#u32,
   0x748f82ee#u32, 0x78a5636f#u32, 0x84c87814#u32, 0x8cc70208#u32,
   0x90befffa#u32, 0xa4506ceb#u32, 0xbef9a3f7#u32, 0xc67178f2#u32]

/-! ## `K^{512}` round constants (FIPS 180-2 §4.2.3) -/

/-- The eighty SHA-384/SHA-512 round constants `K^{512}`
    (FIPS 180-2 §4.2.3): the first sixty-four bits of the fractional parts
    of the cube roots of the first eighty prime numbers. -/
def k512 : List U64 :=
  [0x428a2f98d728ae22#u64, 0x7137449123ef65cd#u64,
   0xb5c0fbcfec4d3b2f#u64, 0xe9b5dba58189dbbc#u64,
   0x3956c25bf348b538#u64, 0x59f111f1b605d019#u64,
   0x923f82a4af194f9b#u64, 0xab1c5ed5da6d8118#u64,
   0xd807aa98a3030242#u64, 0x12835b0145706fbe#u64,
   0x243185be4ee4b28c#u64, 0x550c7dc3d5ffb4e2#u64,
   0x72be5d74f27b896f#u64, 0x80deb1fe3b1696b1#u64,
   0x9bdc06a725c71235#u64, 0xc19bf174cf692694#u64,
   0xe49b69c19ef14ad2#u64, 0xefbe4786384f25e3#u64,
   0x0fc19dc68b8cd5b5#u64, 0x240ca1cc77ac9c65#u64,
   0x2de92c6f592b0275#u64, 0x4a7484aa6ea6e483#u64,
   0x5cb0a9dcbd41fbd4#u64, 0x76f988da831153b5#u64,
   0x983e5152ee66dfab#u64, 0xa831c66d2db43210#u64,
   0xb00327c898fb213f#u64, 0xbf597fc7beef0ee4#u64,
   0xc6e00bf33da88fc2#u64, 0xd5a79147930aa725#u64,
   0x06ca6351e003826f#u64, 0x142929670a0e6e70#u64,
   0x27b70a8546d22ffc#u64, 0x2e1b21385c26c926#u64,
   0x4d2c6dfc5ac42aed#u64, 0x53380d139d95b3df#u64,
   0x650a73548baf63de#u64, 0x766a0abb3c77b2a8#u64,
   0x81c2c92e47edaee6#u64, 0x92722c851482353b#u64,
   0xa2bfe8a14cf10364#u64, 0xa81a664bbc423001#u64,
   0xc24b8b70d0f89791#u64, 0xc76c51a30654be30#u64,
   0xd192e819d6ef5218#u64, 0xd69906245565a910#u64,
   0xf40e35855771202a#u64, 0x106aa07032bbd1b8#u64,
   0x19a4c116b8d2d0c8#u64, 0x1e376c085141ab53#u64,
   0x2748774cdf8eeb99#u64, 0x34b0bcb5e19b48a8#u64,
   0x391c0cb3c5c95a63#u64, 0x4ed8aa4ae3418acb#u64,
   0x5b9cca4f7763e373#u64, 0x682e6ff3d6b2b8a3#u64,
   0x748f82ee5defb2fc#u64, 0x78a5636f43172f60#u64,
   0x84c87814a1f0ab72#u64, 0x8cc702081a6439ec#u64,
   0x90befffa23631e28#u64, 0xa4506cebde82bde9#u64,
   0xbef9a3f7b2c67915#u64, 0xc67178f2e372532b#u64,
   0xca273eceea26619c#u64, 0xd186b8c721c0c207#u64,
   0xeada7dd6cde0eb1e#u64, 0xf57d4f7fee6ed178#u64,
   0x06f067aa72176fba#u64, 0x0a637dc5a2c898a6#u64,
   0x113f9804bef90dae#u64, 0x1b710b35131c471b#u64,
   0x28db77f523047d84#u64, 0x32caab7b40c72493#u64,
   0x3c9ebe0a15c9bebc#u64, 0x431d67c49c100d4c#u64,
   0x4cc5d4becb3e42b6#u64, 0x597f299cfc657e2a#u64,
   0x5fcb6fab3ad6faec#u64, 0x6c44198c4a475817#u64]

/-! ## SHA-256 initial hash value (FIPS 180-2 §5.3.2) -/

/-- The SHA-256 initial hash value `H⁽⁰⁾` (FIPS 180-2 §5.3.2): eight 32-bit
    words (the first thirty-two bits of the fractional parts of the square
    roots of the first eight primes). -/
def sha256H0 : List U32 :=
  [0x6a09e667#u32, 0xbb67ae85#u32, 0x3c6ef372#u32, 0xa54ff53a#u32,
   0x510e527f#u32, 0x9b05688c#u32, 0x1f83d9ab#u32, 0x5be0cd19#u32]

/-! ## SHA-384 initial hash value (FIPS 180-2 §5.3.3) -/

/-- The SHA-384 initial hash value `H⁽⁰⁾` (FIPS 180-2 §5.3.3): eight 64-bit
    words (the first sixty-four bits of the fractional parts of the square
    roots of the ninth through sixteenth primes).  This distinct IV is what
    separates SHA-384 from a plainly truncated SHA-512. -/
def sha384H0 : List U64 :=
  [0xcbbb9d5dc1059ed8#u64, 0x629a292a367cd507#u64,
   0x9159015a3070dd17#u64, 0x152fecd8f70e5939#u64,
   0x67332667ffc00b31#u64, 0x8eb44a8768581511#u64,
   0xdb0c2e0d64f98fa7#u64, 0x47b5481dbefa4fa4#u64]

/-! ## SHA-512 initial hash value (FIPS 180-2 §5.3.4) -/

/-- The SHA-512 initial hash value `H⁽⁰⁾` (FIPS 180-2 §5.3.4): eight 64-bit
    words (the first sixty-four bits of the fractional parts of the square
    roots of the first eight primes). -/
def sha512H0 : List U64 :=
  [0x6a09e667f3bcc908#u64, 0xbb67ae8584caa73b#u64,
   0x3c6ef372fe94f82b#u64, 0xa54ff53a5f1d36f1#u64,
   0x510e527fade682d1#u64, 0x9b05688c2b3e6c1f#u64,
   0x1f83d9abfb41bd6b#u64, 0x5be0cd19137e2179#u64]

/-! ## Length lemmas (SL11) -/

/-- **Spec lemma (`k256_length`, SL11)**: the `K^{256}` table has exactly 64
    words. -/
@[simp]
theorem k256_length : k256.length = 64 := by decide

/-- **Spec lemma (`k512_length`, SL11)**: the `K^{512}` table has exactly 80
    words. -/
@[simp]
theorem k512_length : k512.length = 80 := by decide

/-- **Spec lemma (`sha256H0_length`, SL11)**: the SHA-256 IV has exactly 8
    words. -/
@[simp]
theorem sha256H0_length : sha256H0.length = 8 := by decide

/-- **Spec lemma (`sha384H0_length`, SL11)**: the SHA-384 IV has exactly 8
    words. -/
@[simp]
theorem sha384H0_length : sha384H0.length = 8 := by decide

/-- **Spec lemma (`sha512H0_length`, SL11)**: the SHA-512 IV has exactly 8
    words. -/
@[simp]
theorem sha512H0_length : sha512H0.length = 8 := by decide

/-! ## SHA-384 vs SHA-512 IV separation -/

/-- **Spec lemma (`sha384H0_ne_sha512H0`)**: the SHA-384 and SHA-512 initial
    hash values differ.  This witnesses that SHA-384 is *not* a plainly
    truncated SHA-512 — the two algorithms start from distinct IVs
    (FIPS 180-2 §5.3.3 vs §5.3.4). -/
theorem sha384H0_ne_sha512H0 : sha384H0 ≠ sha512H0 := by decide

end spec.sha
