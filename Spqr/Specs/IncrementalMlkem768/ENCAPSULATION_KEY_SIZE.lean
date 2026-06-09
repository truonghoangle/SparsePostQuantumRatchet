/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::incremental_mlkem768::ENCAPSULATION_KEY_SIZE`

`ENCAPSULATION_KEY_SIZE` is the module-level constant defining the byte length of the
*encapsulation key* (`EncapsulationKey`) of the *incremental* ML-KEM-768 KEM (libcrux's
`incremental` API). In the incremental encapsulation flow, the public key / ciphertext stream is
split into two parts (`pk1`, `pk2`); the encapsulation key corresponds to the `pk2` part. Its size
is fixed by the parameter set and is exposed in Rust as

  `pub const ENCAPSULATION_KEY_SIZE: usize = incremental::pk2_len();`

where `incremental::pk2_len()` is a `const fn` that returns the byte length of the second
public-key chunk. For ML-KEM-768 this length is `1152`, which is also the value emitted by the
Aeneas extraction: the concrete model of `pk2_len` in `Spqr.Code.FunsExternal` is `ok 1152#usize`.

The function proceeds in one stage:
  1. `incremental.pk2_len` — the length accessor for the second public-key chunk of the
     incremental ML-KEM-768 KEM. The Aeneas extraction provides a concrete model `ok 1152#usize`
     for this `const fn`, so no additional axiom is required: the defining equation is already
     available as `pk2_len_spec` in `Spqr.Code.FunsExternal`.

**Source**: spqr/src/incremental_mlkem768.rs (lines 15:0-15:65)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- **`incremental.pk2_len` lifted as a `step` lemma**.

The Aeneas extraction already models `incremental::pk2_len` concretely as `ok 1152#usize` (see
`libcrux_ml_kem.mlkem768.incremental.pk2_len` in `Spqr.Code.FunsExternal`), and the equation
`pk2_len = ok 1152#usize` is provided there as `pk2_len_spec`. We repackage it here as a
Hoare-style `step` lemma so it is visible to the `step` / `step*` tactics that drive the
spec-style proofs in this development. -/
@[step]
private lemma pk2_len_spec :
    libcrux_ml_kem.mlkem768.incremental.pk2_len
      ⦃ (result : Std.Usize) => result = 1152#usize ⦄ := by
  rw [libcrux_ml_kem.mlkem768.incremental.pk2_len_spec]
  simp [WP.spec_ok]

/--
**Spec and proof concerning `incremental_mlkem768.ENCAPSULATION_KEY_SIZE`**:

`ENCAPSULATION_KEY_SIZE` is computed as `incremental.pk2_len`, yielding the constant
`1152 : usize`. It records the byte length of the encapsulation key (`EncapsulationKey`, i.e. the
`pk2` part) of the incremental ML-KEM-768 KEM. The Aeneas extraction models `incremental::pk2_len`
concretely as `ok 1152#usize` (the parameter value for ML-KEM-768), so the result is simply
`1152`.

Concretely:

  `ENCAPSULATION_KEY_SIZE ⦃ (result : Usize) => result.val = 1152 ⦄`

The proof unfolds the definition of `ENCAPSULATION_KEY_SIZE`, dispatches the
`incremental.pk2_len` call via the `pk2_len_spec` step lemma, and extracts the natural-number
value.

**Source**: spqr/src/incremental_mlkem768.rs (lines 15:0-15:65)
-/
@[step]
theorem ENCAPSULATION_KEY_SIZE_spec :
    ENCAPSULATION_KEY_SIZE ⦃ (result : Std.Usize) =>
      result.val = 1152 ⦄ := by
  unfold ENCAPSULATION_KEY_SIZE
  simp [WP.spec_ok]

end spqr.incremental_mlkem768
