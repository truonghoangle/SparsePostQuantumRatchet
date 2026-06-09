/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Specs.Aeneas.TryFromSliceToArray

/-!
# Spec theorem for `spqr::incremental_mlkem768::decaps`

`decaps` is the decapsulation routine of the *incremental* ML-KEM-768 KEM (libcrux's
`incremental` API). Given the *decapsulation key* (`dk`, i.e. the secret key), the first
ciphertext part (`ct1`) and the second ciphertext part (`ct2`), it recovers the shared
secret as a byte vector. It is exposed in Rust as

  `pub fn decaps(dk: &DecapsulationKey, ct1: &Ciphertext1, ct2: &Ciphertext2) -> Secret {
       let ct1 = incremental::Ciphertext1 {
           value: ct1.as_slice().try_into().expect("size should be correct"),
       };
       let ct2 = incremental::Ciphertext2 {
           value: ct2.as_slice().try_into().expect("size should be correct"),
       };
       incremental::decapsulate_compressed_key(
           dk.as_slice().try_into().expect("size should be correct"),
           &ct1,
           &ct2,
       )
       .to_vec()
   }`,

annotated with
  `#[hax_lib::requires(ct1.len() == 960 && ct2.len() == 128 && dk.len() == 2400)]`
  `#[hax_lib::ensures(|result| result.len() == 32)]`,

i.e. the output byte vector has the fixed length `32 = SHARED_SECRET_SIZE`, the byte length
of the shared secret in the ML-KEM-768 parameter set.

The function proceeds in five stages:
  1. `ct1.as_slice().try_into().expect(…)` — convert the 960-byte `ct1` vector to a
     fixed-size `Array U8 960#usize` via `TryFromArrayCopySlice.try_from` (a copy-based
     slice-to-array conversion) and unwrap the `Ok` result via `Result.expect`.
  2. `ct2.as_slice().try_into().expect(…)` — convert the 128-byte `ct2` vector to a
     fixed-size `Array U8 128#usize` via `TryFromArrayCopySlice.try_from` and unwrap.
  3. `dk.as_slice().try_into().expect(…)` — convert the 2400-byte `dk` vector to a
     fixed-size `Array U8 2400#usize` via `TryFromSharedArraySlice.try_from` (a shared
     borrow conversion) and unwrap.
  4. `incremental::decapsulate_compressed_key(a2, {value: a}, {value: a1})` — the opaque
     ML-KEM-768 decapsulation step, producing a fixed-size `Array U8 32#usize` (the shared
     secret). In the Aeneas extraction this is modelled as `fun _ _ _ => ok default`.
  5. `a3.to_slice()` → `Slice.to_vec` — convert the 32-byte shared secret array into a
     fresh `Vec U8` of length `32`.

Composing the five stages, the byte-length specification of the result is pinned down at
exactly `32`, matching the Rust `ensures` clause.

**Source**: spqr/src/incremental_mlkem768.rs (lines 156:0-169:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/--
**Spec and proof concerning `incremental_mlkem768.decaps`**:

`decaps dk ct1 ct2` runs the five-stage decapsulation pipeline of the incremental
ML-KEM-768 KEM — convert the three input byte vectors (`ct1`, `ct2`, `dk`) to fixed-size
arrays, invoke `decapsulate_compressed_key`, and clone the resulting 32-byte shared secret
array into a fresh `Vec U8` — and returns the result.

In the Aeneas-extracted model, the underlying cryptographic primitive
`incremental.decapsulate_compressed_key` is opaque (its `Array U8 32#usize` result is the
`default` inhabitant, i.e. the all-zero 32-byte array). The *byte contents* of the
resulting vector are therefore unconstrained by this spec; only the *byte length* is
pinned down, exactly matching the Rust `#[hax_lib::ensures]` annotation
`result.len() == 32`.

Concretely:

  `decaps dk ct1 ct2 ⦃ (result : Vec U8) => result.length = 32 ⦄`

The proof unfolds the definition of `decaps`, steps through the `Vec.as_slice`,
`TryFromArrayCopySlice.try_from`, and `Result.expect` calls for `ct1` and `ct2` via
`step*`, then manually unfolds `TryFromSharedArraySlice.try_from` for `dk` (splitting on
the length condition), and finally dispatches the remaining monadic steps —
`Result.expect`, `decapsulate_compressed_key`, `Array.to_slice`, and `Slice.to_vec` — via
`step*`.

**Source**: spqr/src/incremental_mlkem768.rs (lines 156:0-169:1)
-/
@[step]
theorem decaps_spec
    (dk ct1 ct2 : alloc.vec.Vec Std.U8)
    (hdk : dk.length = 2400) (hct1 : ct1.length = 960)
    (hct2 : ct2.length = 128) :
    incremental_mlkem768.decaps dk ct1 ct2
      ⦃ (result : alloc.vec.Vec Std.U8) => result.length = 32 ⦄ := by
  unfold incremental_mlkem768.decaps
  step*
  unfold core.array.TryFromSharedArraySlice.try_from
  simp [core.result.Result.expect]
  split
  · simp
    step*
    split
    · simp_all
      step*
      split
      · step*
      · step*
    · step*
  · simp
    step*

end spqr.incremental_mlkem768
