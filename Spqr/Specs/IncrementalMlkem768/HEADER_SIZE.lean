/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::incremental_mlkem768::HEADER_SIZE`

`HEADER_SIZE` is the module-level constant defining the byte length of the *header* (`Header`) of
the *incremental* ML-KEM-768 KEM (libcrux's `incremental` API). In the incremental encapsulation
flow, the public key / ciphertext stream is split into two parts (`pk1`, `pk2`); the header
corresponds to the `pk1` part. Its size is fixed by the parameter set and is exposed in Rust as

  `pub const HEADER_SIZE: usize = incremental::pk1_len();`

where `incremental::pk1_len()` is a `const fn` that returns the byte length of the first public-key
chunk. For ML-KEM-768 this length is `64`, which is also the value emitted by the Aeneas
extraction: the concrete model of `pk1_len` in `Spqr.Code.FunsExternal` is `ok 64#usize`.

The function proceeds in one stage:
  1. `incremental.pk1_len` — the length accessor for the first public-key chunk of the incremental
     ML-KEM-768 KEM. The Aeneas extraction provides a concrete model `ok 64#usize` for this
     `const fn`, so no additional axiom is required: the defining equation is already available as
     `pk1_len_spec` in `Spqr.Code.FunsExternal`.

**Source**: spqr/src/incremental_mlkem768.rs (lines 13:0-13:54)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- **`incremental.pk1_len` lifted as a `step` lemma**.

The Aeneas extraction already models `incremental::pk1_len` concretely as `ok 64#usize` (see
`libcrux_ml_kem.mlkem768.incremental.pk1_len` in `Spqr.Code.FunsExternal`), and the equation
`pk1_len = ok 64#usize` is provided there as `pk1_len_spec`. We repackage it here as a
Hoare-style `step` lemma so it is visible to the `step` / `step*` tactics that drive the
spec-style proofs in this development. -/
@[step]
private lemma pk1_len_spec :
    libcrux_ml_kem.mlkem768.incremental.pk1_len
      ⦃ (result : Std.Usize) => result = 64#usize ⦄ := by
  rw [libcrux_ml_kem.mlkem768.incremental.pk1_len_spec]
  simp [WP.spec_ok]

/--
**Spec and proof concerning `incremental_mlkem768.HEADER_SIZE`**:

`HEADER_SIZE` is computed as `incremental.pk1_len`, yielding the constant `64 : usize`. It records
the byte length of the header (`Header`, i.e. the `pk1` part) of the incremental ML-KEM-768 KEM.
The Aeneas extraction models `incremental::pk1_len` concretely as `ok 64#usize` (the parameter
value for ML-KEM-768), so the result is simply `64`.

Concretely:

  `HEADER_SIZE ⦃ (result : Usize) => result.val = 64 ⦄`

The proof unfolds the definition of `HEADER_SIZE`, dispatches the `incremental.pk1_len` call via
the `pk1_len_spec` step lemma, and extracts the natural-number value.

**Source**: spqr/src/incremental_mlkem768.rs (lines 13:0-13:54)
-/
@[step]
theorem HEADER_SIZE_spec :
    HEADER_SIZE ⦃ (result : Std.Usize) =>
      result.val = 64 ⦄ := by
  unfold HEADER_SIZE
  simp [WP.spec_ok]

end spqr.incremental_mlkem768
