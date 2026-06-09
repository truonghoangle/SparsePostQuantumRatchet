/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::incremental_mlkem768::CIPHERTEXT1_SIZE`

`CIPHERTEXT1_SIZE` is the module-level constant defining the byte length of the first ciphertext
(`Ciphertext1`) produced by the *incremental* ML-KEM-768 KEM (libcrux's `incremental` API). In
ML-KEM-768, `Ciphertext1` is the truncated u-vector part of the KEM ciphertext; its size is fixed
by the parameter set and is exposed in Rust as

  `pub const CIPHERTEXT1_SIZE: usize = incremental::Ciphertext1::len();`

where `incremental::Ciphertext1<LEN>::len()` is a `const fn` that returns the const-generic
length `LEN`. For ML-KEM-768 this length is `960`, which is also the value that flows through
Aeneas's monomorphization: the extraction instantiates `Ciphertext1.len` at `960#usize`.

The function proceeds in one stage:
  1. `Ciphertext1.len LEN` — an opaque (external, axiomatized) accessor that returns the
     const-generic length `LEN` of `Ciphertext1<LEN>`. Semantically this is the identity
     `fun LEN => ok LEN`, but the Aeneas extraction leaves it as an axiom because it is a
     `const fn` defined in the upstream `libcrux_ml_kem` crate.

**Source**: spqr/src/incremental_mlkem768.rs (lines 8:0-8:68)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- `incremental::Ciphertext1<LEN>::len()` returns its const-generic length `LEN`.

In upstream `libcrux_ml_kem`, `Ciphertext1<LEN>::len` is defined as `const fn len() -> usize { LEN }`,
i.e. it is observationally the identity on the const generic. The Aeneas extraction emits it as an
external axiom (`libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1.len`), so we postulate the
defining equation here. -/
axiom Ciphertext1_len_id (LEN : Std.Usize) :
    libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1.len LEN = ok LEN

/-- **`Ciphertext1.len` lifted as a `step` lemma**.

This makes the identity `Ciphertext1.len LEN = ok LEN` visible to the `step` / `step*` tactics
that drive the spec-style proofs in this development. -/
@[step]
private lemma Ciphertext1_len_spec (LEN : Std.Usize) :
    libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1.len LEN
      ⦃ (result : Std.Usize) => result = LEN ⦄ := by
  rw [Ciphertext1_len_id]
  simp [WP.spec_ok]

/--
**Spec and proof concerning `incremental_mlkem768.CIPHERTEXT1_SIZE`**:

`CIPHERTEXT1_SIZE` is computed as `Ciphertext1.len 960#usize`, yielding the constant `960 : usize`.
It records the byte length of the first ciphertext (`Ciphertext1`) of the incremental ML-KEM-768
KEM. The Aeneas extraction has already monomorphized the const-generic `LEN` to `960#usize` (the
parameter value for ML-KEM-768), and `Ciphertext1::len` is semantically the identity on `LEN`, so
the result is simply `960`.

Concretely:

  `CIPHERTEXT1_SIZE ⦃ (result : Usize) => result.val = 960 ⦄`

The proof unfolds the definition of `CIPHERTEXT1_SIZE`, dispatches the opaque
`Ciphertext1.len 960#usize` call via the `Ciphertext1_len_spec` step lemma, and extracts the
natural-number value.

**Source**: spqr/src/incremental_mlkem768.rs (lines 8:0-8:68)
-/
@[step]
theorem CIPHERTEXT1_SIZE_spec :
    CIPHERTEXT1_SIZE ⦃ (result : Std.Usize) =>
      result.val = 960 ⦄ := by
  unfold CIPHERTEXT1_SIZE
  step
  grind

end spqr.incremental_mlkem768
