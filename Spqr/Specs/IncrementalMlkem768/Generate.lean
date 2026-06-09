/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `spqr::incremental_mlkem768::generate`

`generate` is the key-generation routine of the *incremental* ML-KEM-768 KEM (libcrux's
`incremental` API). It draws fresh randomness from a caller-provided RNG and produces a
`Keys` record bundling the three byte streams of a freshly minted key pair:
the *header* (`hdr`, i.e. the `pk1` part of the public key), the *encapsulation key*
(`ek`, i.e. the `pk2` part of the public key) and the *decapsulation key* (`dk`, i.e.
the secret key `sk`). It is exposed in Rust as

  `pub fn generate<R: Rng + CryptoRng>(rng: &mut R) -> Keys {
       let mut randomness = [0u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
       rng.fill_bytes(&mut randomness);
       let k = incremental::KeyPairCompressedBytes::from_seed(randomness);
       Keys {
           hdr: k.pk1().to_vec(),
           ek:  k.pk2().to_vec(),
           dk:  k.sk().to_vec(),
       }
   }`

annotated with
  `#[hax_lib::ensures(|result|
       result.hdr.len() == HEADER_SIZE
    && result.ek.len()  == ENCAPSULATION_KEY_SIZE
    && result.dk.len()  == 2400)]`,

i.e. the three output byte vectors have the fixed lengths dictated by the ML-KEM-768
parameter set: `HEADER_SIZE = pk1_len() = 64`, `ENCAPSULATION_KEY_SIZE = pk2_len() = 1152`,
and `|sk| = 2400`.

The function proceeds in four stages:
  1. `Array.repeat 64#usize 0#u8` — allocate a fresh seed buffer
     `randomness : Array U8 KEY_GENERATION_SEED_SIZE` (with `KEY_GENERATION_SEED_SIZE = 64`),
     initialised to all zeros.
  2. `RngCore::fill_bytes` (via `Array.to_slice_mut` and its back-function) — overwrite the
     seed buffer with fresh random bytes drawn from the caller's RNG. The back-function of
     `Array.to_slice_mut` re-packages the (possibly mutated) slice into an `Array U8 64`,
     so the post-RNG buffer `randomness1` has *type* `Array U8 64#usize` regardless of what
     the (abstract) RNG instance produced.
  3. `incremental.KeyPairCompressedBytes.from_seed` — derive an ML-KEM-768 incremental
     compressed key pair `k : KeyPairCompressedBytes` from the 64-byte seed. The Aeneas
     extraction models this opaque cryptographic routine as `fun _ => ok default`, since
     `KeyPairCompressedBytes` is axiomatised (see `Spqr.Code.TypesExternal`).
  4. `pk1 k`, `pk2 k`, `sk k` — extract the three fixed-size byte arrays of the compressed
     key pair, namely `Array U8 64`, `Array U8 1152` and `Array U8 2400`. The Aeneas
     extraction models each as `fun _ => ok default`. Each is then converted to a slice via
     `Array.to_slice` and cloned into a fresh `Vec U8` via `alloc.slice.Slice.to_vec` with
     the `core.clone.CloneU8` instance — operations that preserve the byte length.

Composing the four stages, the byte-length specifications of the three `Vec U8` fields of
the resulting `Keys` record are pinned down at exactly `64`, `1152` and `2400`,
matching the Rust `ensures` clause.

**Source**: spqr/src/incremental_mlkem768.rs (lines 34:0-43:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- **Functional contract for `rand_core::RngCore::fill_bytes`**.

In upstream `rand_core`, `RngCore::fill_bytes(&mut self, dest: &mut [u8])` overwrites
`dest` with fresh random bytes drawn from `self`. The trait method is *opaque* in the
Aeneas extraction — it is part of the `rand_core.RngCore` trait declaration in
`Spqr.Code.Types` (`fill_bytes : Self → Slice U8 → Result (Self × Slice U8)`) and has no
concrete model elsewhere. Functionally, the only contract `fill_bytes` is supposed to
satisfy is that it never panics (it merely writes into `dest`). We capture this here as
a *definition* of the proposition that every concrete call returns `ok (rng', s')` for
some updated RNG state `rng'` and (mutated) slice `s'`.

This matches the semantics of every honest Rust implementation of `RngCore::fill_bytes`
(in particular, the `OsRng` and `ChaCha20Rng` implementations used by callers of
`generate`), and is the minimal assumption needed to derive a (non-vacuous) spec for
`generate` in the abstract model. Downstream specs take an instance of this proposition
as a hypothesis rather than relying on an axiom. -/
def fill_bytes_ok
    {R : Type} (rngInst : rand_core.RngCore R) : Prop :=
  ∀ (rng : R) (s : Slice Std.U8),
    ∃ rng' s', rngInst.fill_bytes rng s = ok (rng', s')

/-- **Step-style spec lemma for `rand_core::RngCore::fill_bytes`**.

Lifts the `fill_bytes_ok` hypothesis into the `step` / `step*` machinery: under the
assumption that every call to `fill_bytes` succeeds, we expose no information about the
output beyond its mere existence (`True`). This is sufficient for length-only specs like
`generate_spec`, because the length of the resulting `Array U8 64` is dictated by its
type (rebuilt by `Array.to_slice_mut`'s back-function), not by the actual bytes that the
RNG wrote. -/
@[step]
private lemma fill_bytes_spec
    {R : Type} (rngInst : rand_core.RngCore R)
    (hfb : fill_bytes_ok rngInst) (rng : R) (s : Slice Std.U8) :
    rngInst.fill_bytes rng s ⦃ (_ : R × Slice Std.U8) => True ⦄ := by
  obtain ⟨rng', s', h⟩ := hfb rng s
  rw [h]
  simp [WP.spec_ok]

/--
**Spec and proof concerning `incremental_mlkem768.generate`**:

`generate randrngRngInst rand_coreCryptoRngInst rng` runs the four-stage key-generation
pipeline of the incremental ML-KEM-768 KEM — sample 64 bytes of randomness, derive a
compressed key pair, and clone its three fixed-size byte arrays into freshly allocated
byte vectors — and returns the resulting `Keys` record together with the updated RNG
state.

In the Aeneas-extracted model, the underlying cryptographic primitive
`KeyPairCompressedBytes::from_seed` is opaque (its result is the `default` inhabitant
of the axiomatised `KeyPairCompressedBytes` type) and the projections `pk1`, `pk2`, `sk`
return the `default` (all-zero) inhabitants of `Array U8 64`, `Array U8 1152` and
`Array U8 2400` respectively. The *byte contents* of the resulting vectors are therefore
unconstrained by this spec; only the *byte lengths* are pinned down, exactly matching
the Rust `#[hax_lib::ensures]` annotation
`result.hdr.len() == HEADER_SIZE && result.ek.len() == ENCAPSULATION_KEY_SIZE
   && result.dk.len() == 2400`,
with `HEADER_SIZE = 64` and `ENCAPSULATION_KEY_SIZE = 1152` (see `HEADER_SIZE.lean` and
`ENCAPSULATION_KEY_SIZE.lean`).

Concretely:

  `generate ⦃ (result : Keys × R) =>
       result.1.hdr.length = 64
     ∧ result.1.ek.length  = 1152
     ∧ result.1.dk.length  = 2400 ⦄`

The proof unfolds the definition of `generate` and discharges the four stages of the
pipeline with the `step*` tactic: the seed allocation (`Array.repeat`), the
`Array.to_slice_mut`/back-function pair, the abstract `fill_bytes` step (whose only
length-relevant content is the type-level fact that the back-function rebuilds an
`Array U8 64#usize`, plus the axiom `fill_bytes_ok` that the call never panics), the
`from_seed`/`pk1`/`pk2`/`sk` calls (dispatched via their `_spec` rewrites in
`Spqr.Code.FunsExternal`), and the three `Array.to_slice` → `Slice.to_vec` cloning
steps (each of which preserves the byte length).

**Source**: spqr/src/incremental_mlkem768.rs (lines 34:0-43:1)
-/
@[step]
theorem generate_spec
    {R : Type} (randrngRngInst : rand.rng.Rng R)
    (rand_coreCryptoRngInst : rand_core.CryptoRng R) (rng : R)
    (hfb : fill_bytes_ok randrngRngInst.rand_coreRngCoreInst) :
    incremental_mlkem768.generate randrngRngInst rand_coreCryptoRngInst rng
      ⦃ (result : incremental_mlkem768.Keys × R) =>
          result.1.hdr.length = 64
        ∧ result.1.ek.length  = 1152
        ∧ result.1.dk.length  = 2400 ⦄ := by
  unfold incremental_mlkem768.generate
  step*

end spqr.incremental_mlkem768
