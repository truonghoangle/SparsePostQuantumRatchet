/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Code.FunsExternal

/-!
# Spec theorem for `spqr::incremental_mlkem768::ek_matches_header`

`ek_matches_header` is the module-level predicate of the *incremental* ML-KEM-768 KEM (libcrux's
`incremental` API) that checks whether a given *encapsulation key* (`EncapsulationKey`, i.e. the
`pk2` part of the public-key stream) is consistent with a given *header* (`Header`, i.e. the `pk1`
part). It is exposed in Rust as

  `pub fn ek_matches_header(ek: &EncapsulationKey, hdr: &Header) -> bool {
       incremental::validate_pk_bytes(hdr, ek).is_ok()
   }`

i.e. it derefs the two `Vec<u8>` inputs to byte slices, calls the upstream
`incremental::validate_pk_bytes` validator, and returns `true` iff the returned `Result` is `Ok`.

The function proceeds in three stages:
  1. `alloc.vec.Vec.deref` (twice) — view the two `Vec<u8>` inputs as `Slice U8`. This is a pure
     coercion that never fails, modelled as the identity on the byte payload by the Aeneas
     extraction.
  2. `incremental.validate_pk_bytes hdr ek` — the upstream cryptographic validator. The Aeneas
     extraction provides a concrete model `fun _ _ => ok (Result.Ok ())` for this opaque routine
     (see `libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes` in `Spqr.Code.FunsExternal`), and
     the equation `validate_pk_bytes pk1 pk2 = ok (Ok ())` is provided there as
     `validate_pk_bytes_spec`. Thus, in the extracted Lean model, validation *always succeeds*.
  3. `core.result.Result.is_ok` — the Boolean discriminator on `core::result::Result`, returning
     `true` on the `Ok` branch and `false` on the `Err` branch. The Aeneas extraction leaves this
     as an external axiom (`core.result.Result.is_ok` in `Spqr.Code.FunsExternal`) because it is a
     generic standard-library method; we therefore postulate the defining equation on the `Ok`
     branch here (this is the only branch reachable in this function).

**Source**: spqr/src/incremental_mlkem768.rs (lines 28:0-30:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- `core::result::Result::is_ok` on the `Ok` branch returns `true`.

In upstream `core::result`, `Result::is_ok` is defined as
`const fn is_ok(&self) -> bool { matches!(*self, Ok(_)) }`, i.e. it returns `true` on `Ok(_)` and
`false` on `Err(_)`. The Aeneas extraction emits it as an external axiom
(`core.result.Result.is_ok`), so we postulate the defining equation on the `Ok` branch — which is
the only branch reachable from `ek_matches_header` since `validate_pk_bytes` always returns
`Ok ()` in the extracted model. -/
axiom Result_is_ok_Ok {T E : Type} (v : T) :
    core.result.Result.is_ok (E := E) (core.result.Result.Ok v) = ok true

/-- **`core.result.Result.is_ok` on `Ok` lifted as a `step` lemma**.

This makes the identity `is_ok (Ok v) = ok true` visible to the `step` / `step*` tactics that
drive the spec-style proofs in this development. -/
@[step]
private lemma Result_is_ok_Ok_spec {T E : Type} (v : T) :
    core.result.Result.is_ok (E := E) (core.result.Result.Ok v)
      ⦃ (result : Bool) => result = true ⦄ := by
  rw [Result_is_ok_Ok]
  simp [WP.spec_ok]

/--
**Spec and proof concerning `incremental_mlkem768.ek_matches_header`**:

`ek_matches_header ek hdr` is computed as
`(incremental.validate_pk_bytes (deref hdr) (deref ek)).is_ok`, yielding the Boolean `true`. It
records whether the encapsulation key `ek` is consistent with the header `hdr` for the incremental
ML-KEM-768 KEM. The Aeneas extraction models `incremental::validate_pk_bytes` concretely as
`fun _ _ => ok (Ok ())` (the underlying cryptographic validator is opaque, so the model is
optimistic), and `Result::is_ok` on the `Ok` branch is `true`, so the result is simply `true`.

Concretely:

  `ek_matches_header ek hdr ⦃ (result : Bool) => result = true ⦄`

The proof unfolds the definition of `ek_matches_header`, dispatches the `validate_pk_bytes` call
via the `validate_pk_bytes_spec` rewrite (provided in `Spqr.Code.FunsExternal`), and dispatches
the `Result::is_ok` call via the `Result_is_ok_Ok_spec` step lemma.

**Source**: spqr/src/incremental_mlkem768.rs (lines 28:0-30:1)
-/
@[step]
theorem ek_matches_header_spec
    (ek : alloc.vec.Vec Std.U8) (hdr : alloc.vec.Vec Std.U8) :
    ek_matches_header ek hdr ⦃ (result : Bool) =>
      result = true ⦄ := by
  unfold ek_matches_header
  simp [WP.spec_ok, Result_is_ok_Ok]

end spqr.incremental_mlkem768
