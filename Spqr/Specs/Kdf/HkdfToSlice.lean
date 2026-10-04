/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Crypto.Hkdf

/-!
# Spec axiom for `spqr::kdf::hkdf_to_slice`

`hkdf_to_slice` fills its output buffer with HKDF-SHA256 output keying material.

Source: "spqr/src/kdf.rs"

## D51 audit note (LOW; config — erased HKDF length bound)

The Lean axiom `hkdf_to_slice_spec` requires `h : okm.length ≤ 255 * 32` (= 8160 bytes),
matching the RFC 5869 bound on the HKDF output length `L`. In Rust, this bound is **not
enforced**: `kdf.rs` L15–17 calls `hkdf.expand(info, okm).expect("all lengths should work")`,
which panics if `okm.len() > 8160`.

All current callers use `okm_len ∈ {32, 64, 96}`, well within bounds. The defect is latent:
a future caller requesting `okm_len > 8160` would panic. The Lean trusted base silently
assumes the bound holds; if violated, the axiom's postcondition would be unsound.

See also `HkdfToVec.lean` which propagates the same bound. See `docs/listDefects.md` §D51. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.kdf
open crypto

/-- **Spec axiom for `spqr::kdf::hkdf_to_slice`**
• The function implements RFC 5869 HKDF-SHA256.
• The bound `okm.length ≤ 255 * 32` is the RFC's bound on `L`; every call site is well within it.

**D51 note.** This `h` precondition is erased in Rust — the `expect` panics if violated.
The Lean spec trusts this bound but Rust does not enforce it. -/
@[step]
axiom hkdf_to_slice_spec (salt ikm info okm : Slice U8) (h : okm.length ≤ 255 * 32) :
    hkdf_to_slice salt ikm info okm ⦃ (out : Slice U8) =>
      out.val = hkdf salt.val ikm.val info.val okm.length ⦄

end spqr.kdf
