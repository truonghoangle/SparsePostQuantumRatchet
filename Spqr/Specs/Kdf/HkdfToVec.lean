/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Auxiliary.Aeneas.Slice
import Spqr.Auxiliary.Aeneas.Vec
import Spqr.Specs.Kdf.HkdfToSlice

/-!
# Spec theorem for `spqr::kdf::hkdf_to_vec`

`hkdf_to_vec` allocates a zero-filled buffer of length `okm_len`, fills it in-place via
`hkdf_to_slice`, and returns it as a `Vec`.

Source: "spqr/src/kdf.rs"

**D51 audit note.** The `h : okm_len.val ≤ 255 * 32` precondition is propagated from
`hkdf_to_slice_spec`. In Rust, the bound is not enforced — `expand` panics via `expect`.
See `HkdfToSlice.lean` for the full D51 note and `docs/listDefects.md` §D51. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.kdf
open crypto

attribute [step_simps] alloc.vec.Vec.deref_mut lift in
/-- **Spec theorem for `spqr::kdf::hkdf_to_vec`**
• Requires that `okm_len.val ≤ 255 * 32`.
• The returned `Vec U8` is the `okm_len`-byte HKDF-SHA256 output, and has length `okm_len`. -/
@[step]
theorem hkdf_to_vec_spec (salt ikm info : Slice U8) (okm_len : Usize) (h : okm_len.val ≤ 255 * 32) :
    hkdf_to_vec salt ikm info okm_len ⦃ (v : alloc.vec.Vec U8) =>
      v.val = hkdf salt.val ikm.val info.val okm_len.val ∧ v.length = okm_len.val ⦄ := by
  unfold hkdf_to_vec
  step*
  simp_all [Slice.length]

end spqr.kdf
