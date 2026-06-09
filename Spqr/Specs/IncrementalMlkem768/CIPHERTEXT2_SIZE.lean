/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::incremental_mlkem768::CIPHERTEXT2_SIZE`

`CIPHERTEXT2_SIZE` is the module-level constant defining the byte length of the second ciphertext
(`Ciphertext2`) produced by the *incremental* ML-KEM-768 KEM (libcrux's `incremental` API). In
ML-KEM-768, `Ciphertext2` is the (compressed) v-component of the KEM ciphertext; its size is fixed
by the parameter set and is exposed in Rust as

  `pub const CIPHERTEXT2_SIZE: usize = incremental::Ciphertext2::len();`

where `incremental::Ciphertext2<LEN>::len()` is a `const fn` that returns the const-generic
length `LEN`. For ML-KEM-768 this length is `128`, which is also the value that flows through
Aeneas's monomorphization: the extraction instantiates `Ciphertext2.len` at `128#usize`.

The function proceeds in one stage:
  1. `Ciphertext2.len LEN` — the const-generic length accessor for `Ciphertext2<LEN>`. Unlike its
     `Ciphertext1` counterpart, the Aeneas extraction provides a concrete model
     `fun LEN => ok LEN` for this `const fn`, so no additional axiom is required: the defining
     equation is already available as `Ciphertext2.len_spec` in `Spqr.Code.FunsExternal`.

**Source**: spqr/src/incremental_mlkem768.rs (lines 11:0-11:68)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- **`Ciphertext2.len` lifted as a `step` lemma**.

The Aeneas extraction already models `incremental::Ciphertext2<LEN>::len` concretely as
`fun LEN => ok LEN` (see `libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2.len` in
`Spqr.Code.FunsExternal`), and the equation `Ciphertext2.len LEN = ok LEN` is provided there as
`Ciphertext2.len_spec`. We repackage it here as a Hoare-style `step` lemma so it is visible to the
`step` / `step*` tactics that drive the spec-style proofs in this development. -/
@[step]
private lemma Ciphertext2_len_spec (LEN : Std.Usize) :
    libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2.len LEN
      ⦃ (result : Std.Usize) => result = LEN ⦄ := by
  rw [libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2.len_spec]
  simp [WP.spec_ok]

/--
**Spec and proof concerning `incremental_mlkem768.CIPHERTEXT2_SIZE`**:

`CIPHERTEXT2_SIZE` is computed as `Ciphertext2.len 128#usize`, yielding the constant `128 : usize`.
It records the byte length of the second ciphertext (`Ciphertext2`) of the incremental ML-KEM-768
KEM. The Aeneas extraction has already monomorphized the const-generic `LEN` to `128#usize` (the
parameter value for ML-KEM-768), and `Ciphertext2::len` is semantically the identity on `LEN`, so
the result is simply `128`.

Concretely:

  `CIPHERTEXT2_SIZE ⦃ (result : Usize) => result.val = 128 ⦄`

The proof unfolds the definition of `CIPHERTEXT2_SIZE`, dispatches the `Ciphertext2.len 128#usize`
call via the `Ciphertext2_len_spec` step lemma, and extracts the natural-number value.

**Source**: spqr/src/incremental_mlkem768.rs (lines 11:0-11:68)
-/
@[step]
theorem CIPHERTEXT2_SIZE_spec :
    CIPHERTEXT2_SIZE ⦃ (result : Std.Usize) =>
      result.val = 128 ⦄ := by
  unfold CIPHERTEXT2_SIZE
  simp [WP.spec_ok]

end spqr.incremental_mlkem768
