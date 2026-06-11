/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Code.FunsExternal

/-!
# Spec theorem for `spqr::kdf::hkdf_to_vec`

The function `hkdf_to_vec` produces a byte vector of HKDF-SHA-256 output. Given a salt, input
keying material (IKM), context info, and a desired output length `okm_len`, it:
  1. Allocates a zero-filled `Vec<u8>` of length `okm_len` via `vec![0u8; okm_len]`.
  2. Passes a mutable slice of that buffer to `hkdf_to_slice`, which fills it with the HKDF-SHA-256
     expansion.
  3. Returns the filled vector.

The upstream Rust contract asserts `res.len() >= okm_len`. In our opaque model of `hkdf_to_slice`
(which preserves the slice identity), the result is exactly the `okm_len`-length zero vector, so
`result.length = okm_len.val` — a stronger property that implies the Rust postcondition.

**Source**: spqr/src/kdf.rs (lines 6:0-10:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.kdf

/-- **Spec theorem for `kdf.hkdf_to_vec`**:

Given `salt`, `ikm`, `info` (all byte slices) and the desired output length `okm_len`, the call
always succeeds and returns a `Vec<u8>` whose underlying list is `List.replicate okm_len.val 0#u8`
and whose length equals `okm_len.val`.

This follows from composing:
  1. `alloc.vec.from_elem_spec`:
       `vec![0u8; okm_len]` produces a vector with
       `val = List.replicate okm_len.val 0#u8` and `length = okm_len.val`.
  2. `alloc.vec.Vec.deref_mut`:
       borrows the vector as a mutable slice (pure, never fails).
  3. `kdf.hkdf_to_slice_spec`:
       the HKDF call preserves the slice (`s.val = okm.val`).
  4. The write-back closure reconstructs the vector from the (unchanged) slice.

The Rust contract `res.len() >= okm_len` follows immediately from `result.length = okm_len.val`.

**Source**: spqr/src/kdf.rs (lines 6:0-10:1)
-/
@[step]
theorem hkdf_to_vec_spec
    (salt ikm info : Slice Std.U8) (okm_len : Std.Usize) :
    hkdf_to_vec salt ikm info okm_len ⦃ (result : alloc.vec.Vec Std.U8) =>
      result.val = List.replicate okm_len.val 0#u8 ∧
      result.length = okm_len.val ⦄ := by
  unfold hkdf_to_vec
  step*
  simp_all [alloc.vec.Vec.deref_mut, lift, kdf.hkdf_to_slice, alloc.vec.Vec.length]

end spqr.kdf
