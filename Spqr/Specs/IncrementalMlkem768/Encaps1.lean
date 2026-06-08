/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Code.FunsExternal
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Specs.IncrementalMlkem768.Generate

/-!
# Spec theorem for `spqr::incremental_mlkem768::encaps1`

`encaps1` is the first half of the *incremental* ML-KEM-768 encapsulation pipeline
(libcrux's `incremental` API). Given the *header* part of a public key (`hdr`, i.e. the
`pk1` bytes) and a caller-provided RNG, it freshly samples 32 bytes of randomness, runs
`encapsulate1` against `hdr` to produce the first ciphertext piece together with the
opaque *encapsulation state* and *shared secret* buffers, and returns the triple
`(ct1, es, ss)` of byte vectors (with the updated RNG threaded back to the caller).
It is exposed in Rust as

  `pub fn encaps1<R: Rng + CryptoRng>(
       hdr: &Header,
       rng: &mut R,
   ) -> (Ciphertext1, EncapsulationState, Secret) {
       let mut randomness = [0u8; libcrux_ml_kem::SHARED_SECRET_SIZE];
       rng.fill_bytes(&mut randomness);
       let mut state = vec![0u8; incremental::encaps_state_len()];
       let mut ss    = vec![0u8; libcrux_ml_kem::SHARED_SECRET_SIZE];
       let ct1 = incremental::encapsulate1(hdr.as_slice(), randomness, &mut state, &mut ss);
       hax_lib::assume!(ct1.is_ok());
       hax_lib::assume!(state.len() == 2080 && ss.len() == 32);
       (ct1.expect("…").value.to_vec(), state, ss)
   }`,

annotated with
  `#[hax_lib::requires(hdr.len() == 64)]`
  `#[hax_lib::ensures(|(ct1, es, ss)|
       ct1.len() == 960 && es.len() == 2080 && ss.len() == 32)]`,

i.e. the three output byte vectors have the fixed lengths dictated by the ML-KEM-768
parameter set: `CIPHERTEXT1_SIZE = 960`, `encaps_state_len() = 2080` and
`SHARED_SECRET_SIZE = 32`.

The function proceeds in five stages:
  1. `Array.repeat 32#usize 0#u8` — allocate a fresh 32-byte randomness buffer
     `randomness : Array U8 SHARED_SECRET_SIZE` (with `SHARED_SECRET_SIZE = 32`),
     initialised to all zeros.
  2. `RngCore::fill_bytes` (via `Array.to_slice_mut` and its back-function) — overwrite
     the randomness buffer with fresh bytes drawn from the caller's RNG. The back-function
     of `Array.to_slice_mut` re-packages the (possibly mutated) slice into an
     `Array U8 32`, so the post-RNG buffer `randomness1` has *type* `Array U8 32#usize`
     regardless of what the (abstract) RNG instance produced.
  3. `alloc.vec.from_elem` — allocate the two `Vec<u8>` work buffers: `state` of length
     `encaps_state_len() = 2080` and `ss` of length `SHARED_SECRET_SIZE = 32`, both
     initialised to all zeros.
  4. `incremental.encapsulate1` — run the opaque ML-KEM-768 encapsulation step against
     `hdr.as_slice()`, the 32-byte randomness, and the two mutable byte slices obtained
     from `state` and `ss` via `Vec.deref_mut`. In the Aeneas extraction this routine is
     modelled as `fun _ _ state ss => ok (Ok ⟨default⟩, state, ss)`: it returns an all-zero
     `Ciphertext1 960#usize` wrapped in `Ok`, and threads the input slices through
     unchanged. `Result.expect` therefore succeeds with the `default` ciphertext, whose
     `.value` field is the 960-byte all-zero array.
  5. `Array.to_slice` → `alloc.slice.Slice.to_vec` (with `core.clone.CloneU8`) — convert
     the 960-byte ciphertext value into a fresh `Vec U8` of length `960`; the two
     `deref_mut` back-functions then rebuild the original `Vec U8` for `state` and `ss`,
     preserving their byte lengths `2080` and `32`.

Composing the five stages, the byte-length specifications of the three components of the
resulting triple are pinned down at exactly `960`, `2080` and `32`, matching the Rust
`ensures` clause.

**Source**: spqr/src/incremental_mlkem768.rs (lines 48:0-66:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/--
**Spec and proof concerning `incremental_mlkem768.encaps1`**:

`encaps1 randrngRngInst rand_coreCryptoRngInst hdr rng` runs the five-stage first-half
encapsulation pipeline of the incremental ML-KEM-768 KEM — sample 32 bytes of randomness,
allocate the `state` and `ss` work buffers, invoke `encapsulate1`, and clone the resulting
960-byte ciphertext value into a fresh `Vec U8` — and returns the triple
`(ct1, es, ss) : Vec U8 × Vec U8 × Vec U8` together with the updated RNG state.

In the Aeneas-extracted model, the underlying cryptographic primitive
`incremental.encapsulate1` is opaque (its `Ciphertext1 960#usize` result is the `default`
inhabitant, i.e. the all-zero 960-byte array, and the two mutable byte slices are
threaded through unchanged), the work-buffer allocations `alloc.vec.from_elem` produce
all-zero vectors of the requested length, and `Result.expect` on `Ok ⟨default⟩` returns
`⟨default⟩`. The *byte contents* of the resulting vectors are therefore unconstrained by
this spec; only the *byte lengths* are pinned down, exactly matching the Rust
`#[hax_lib::ensures]` annotation `ct1.len() == 960 && es.len() == 2080 && ss.len() == 32`.

Concretely:

  `encaps1 ⦃ (result : (Vec U8 × Vec U8 × Vec U8) × R) =>
       result.1.1.length = 960
     ∧ result.1.2.1.length = 2080
     ∧ result.1.2.2.length = 32 ⦄`

The proof unfolds the definition of `encaps1` and discharges the five stages of the
pipeline with the `step*` tactic: the randomness allocation (`Array.repeat`), the
`Array.to_slice_mut`/back-function pair, the abstract `fill_bytes` step (whose only
length-relevant content is the type-level fact that the back-function rebuilds an
`Array U8 32#usize`, plus the axiom `fill_bytes_ok` that the call never panics), the
`encaps_state_len`/`SHARED_SECRET_SIZE` calls (dispatched via their `_spec` rewrites in
`Spqr.Code.FunsExternal`), the two `Vec.from_elem` work-buffer allocations (whose lengths
are exactly the requested `2080` and `32`), the `Vec.as_slice` view of `hdr` and the two
`Vec.deref_mut` views of `state` and `ss`, the opaque `encapsulate1` call (dispatched via
`encapsulate1_spec`), the `Result.expect` extraction of the inner `Ciphertext1`, and the
final `Array.to_slice` → `Slice.to_vec` cloning step (which preserves the 960-byte length)
together with the two `deref_mut` back-functions (each of which preserves the byte length
of the corresponding work buffer).

**Source**: spqr/src/incremental_mlkem768.rs (lines 48:0-66:1)
-/
@[step]
theorem encaps1_spec
    {R : Type} (randrngRngInst : rand.rng.Rng R)
    (rand_coreCryptoRngInst : rand_core.CryptoRng R)
    (hdr : alloc.vec.Vec Std.U8) (rng : R)
    (hfb : fill_bytes_ok randrngRngInst.rand_coreRngCoreInst) :
    incremental_mlkem768.encaps1 randrngRngInst rand_coreCryptoRngInst hdr rng
      ⦃ (result : ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8) ×
                   (alloc.vec.Vec Std.U8)) × R) =>
            result.1.1.length     = 960
           ∧ result.1.2.1.length   = 2080
           ∧ result.1.2.2.length   = 32 ⦄ := by
  unfold incremental_mlkem768.encaps1
  step*
  simp only [alloc.vec.Vec.deref_mut, lift, bind_tc_ok]
  step*

end spqr.incremental_mlkem768
