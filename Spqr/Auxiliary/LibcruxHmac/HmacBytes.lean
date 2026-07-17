/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Types
import Spqr.Auxiliary.LibcruxHmac.HashLen

/-!
# Abstract byte-level model of `libcrux_hmac::hmac`

`libcrux_hmac::hmac` computes an HMAC tag over a payload with a key, truncated
to a requested tag length:

```rust
pub fn hmac(alg: Algorithm, key: &[u8], data: &[u8], tag_length: Option<usize>) -> Vec<u8>
```

The underlying cryptographic computation is kept *uninterpreted*: we introduce
an `opaque` raw function `spec.hmac_bytes_raw` (inhabited by the constant
`[]` witness, so no new axiom is introduced) and a total wrapper
`spec.hmac_bytes` that pads/truncates the raw output to exactly `n` bytes via
`List.takeD`.  This makes the key length property **provable** (no axiom):

natural language specs:
- `hmac_bytes_length`: `(spec.hmac_bytes alg key data n).length = n`
  (from `List.takeD_length`);
- `hmac_tag_len_none` / `hmac_tag_len_some`: the effective tag length is the
  requested `tag_length` when present, and otherwise the digest length
  `Algorithm.hash_len` of the chosen hash algorithm (`Sha1 ↦ 20`,
  `Sha256 ↦ 32`, `Sha384 ↦ 48`, `Sha512 ↦ 64`, cf.
  `Spqr.Auxiliary.LibcruxHmac.HashLen` and the `libcrux_hmac::Algorithm` enum in
  `SrcTranslated/Types.lean`);
- `hmac_tag_len_le_max`: the effective tag length always fits in a `usize`,
  which lets us package the modelled tag as an `alloc.vec.Vec U8`
  (`spec.hmac_vec`);
- `hmac_vec_val` / `hmac_vec_length`: the underlying bytes and length of the
  packaged tag.

`spec.hmac_vec` is the value returned by the concrete model of
`libcrux_hmac.hmac` in `SrcTranslated/FunsExternal.lean`
(`ok (spec.hmac_vec alg key.val payload.val tag_len)`); the corresponding
spec theorems (`libcrux_hmac.hmac_spec`, `libcrux_hmac.hmac_none_spec`,
`libcrux_hmac.hmac_some_spec`) live next to that model.

**Source**: 'libcrux-hmac-0.0.6/src/hmac.rs' (`hmac`)
-/

open Aeneas Aeneas.Std Result
open spqr

namespace spec

/-- Uninterpreted (opaque) raw HMAC function: given an algorithm, a key, a
    payload, and a requested tag length, produces some list of bytes.  The
    explicit witness `fun _ _ _ _ => []` only establishes inhabitedness — the
    body is *not* definitionally available, and no properties are assumed
    about the function; all observable structure comes from the total wrapper
    `spec.hmac_bytes` below. -/
opaque hmac_bytes_raw :
    libcrux_hmac.Algorithm → List Std.U8 → List Std.U8 → Nat → List Std.U8 :=
  fun _ _ _ _ => []

/-- Abstract model of the HMAC tag of length `n`: the raw opaque output,
    padded/truncated to exactly `n` bytes (`List.takeD n _ 0#u8`), so that the
    length property `hmac_bytes_length` is provable rather than assumed. -/
def hmac_bytes (alg : libcrux_hmac.Algorithm) (key data : List Std.U8)
    (n : Nat) : List Std.U8 :=
  (hmac_bytes_raw alg key data n).takeD n 0#u8

/-- **Spec lemma for `spec.hmac_bytes`**: the modelled HMAC tag has exactly the
    requested length `n` (from `List.takeD_length`; no axiom involved). -/
@[simp]
theorem hmac_bytes_length (alg : libcrux_hmac.Algorithm)
    (key data : List Std.U8) (n : Nat) :
    (hmac_bytes alg key data n).length = n := by
  simp [hmac_bytes, List.takeD_length]

/-- Effective tag length of `libcrux_hmac::hmac`: the requested `tag_length`
    when given (`some l ↦ l.val`), and otherwise the digest length of the hash
    algorithm (`none ↦ alg.hash_len`, mirroring Rust's
    `tag_length.unwrap_or(tag_size(alg))`). -/
def hmac_tag_len (alg : libcrux_hmac.Algorithm) (tag_len : Option Std.Usize) :
    Nat :=
  match tag_len with
  | some l => l.val
  | none => alg.hash_len

/-- **Spec lemma for `spec.hmac_tag_len`**: with `tag_length = None` the
    effective tag length is the algorithm's digest length
    (`Sha1 ↦ 20`, `Sha256 ↦ 32`, `Sha384 ↦ 48`, `Sha512 ↦ 64`). -/
@[simp]
theorem hmac_tag_len_none (alg : libcrux_hmac.Algorithm) :
    hmac_tag_len alg none = alg.hash_len := rfl

/-- **Spec lemma for `spec.hmac_tag_len`**: with `tag_length = Some l` the
    effective tag length is the requested `l`. -/
@[simp]
theorem hmac_tag_len_some (alg : libcrux_hmac.Algorithm) (l : Std.Usize) :
    hmac_tag_len alg (some l) = l.val := rfl

/-- **Spec lemma for `spec.hmac_tag_len`**: the effective tag length always
    fits in a `usize` — a requested length is itself a `Usize`, and every
    digest length is at most 64 bytes (`Algorithm.hash_len_le`). -/
theorem hmac_tag_len_le_max (alg : libcrux_hmac.Algorithm)
    (tag_len : Option Std.Usize) :
    hmac_tag_len alg tag_len ≤ Std.Usize.max := by
  match tag_len with
  | some l =>
    simp only [hmac_tag_len_some]
    scalar_tac
  | none =>
    have h := libcrux_hmac.Algorithm.hash_len_le alg
    simp only [hmac_tag_len_none]
    scalar_tac

/-- Abstract model of the HMAC tag as a `Vec<u8>`: the bytes
    `spec.hmac_bytes` of the effective length `spec.hmac_tag_len alg tag_len`,
    packaged as an `alloc.vec.Vec Std.U8` (well-formed by
    `hmac_bytes_length` and `hmac_tag_len_le_max`). -/
def hmac_vec (alg : libcrux_hmac.Algorithm) (key data : List Std.U8)
    (tag_len : Option Std.Usize) : alloc.vec.Vec Std.U8 :=
  ⟨hmac_bytes alg key data (hmac_tag_len alg tag_len), by
    simpa [hmac_bytes_length] using hmac_tag_len_le_max alg tag_len⟩

/-- **Spec lemma for `spec.hmac_vec`**: its underlying byte list is exactly
    `spec.hmac_bytes` at the effective tag length. -/
@[simp]
theorem hmac_vec_val (alg : libcrux_hmac.Algorithm) (key data : List Std.U8)
    (tag_len : Option Std.Usize) :
    (hmac_vec alg key data tag_len).val =
      hmac_bytes alg key data (hmac_tag_len alg tag_len) := rfl

/-- **Spec lemma for `spec.hmac_vec`**: the modelled HMAC tag has exactly the
    effective tag length `spec.hmac_tag_len alg tag_len`. -/
@[simp]
theorem hmac_vec_length (alg : libcrux_hmac.Algorithm) (key data : List Std.U8)
    (tag_len : Option Std.Usize) :
    (hmac_vec alg key data tag_len).val.length = hmac_tag_len alg tag_len := by
  simp [hmac_vec_val, hmac_bytes_length]

end spec
