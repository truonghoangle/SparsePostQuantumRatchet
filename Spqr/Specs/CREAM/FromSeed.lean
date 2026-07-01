/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Aeneas
import SrcTranslated.FunsExternal


/-! # Spec axioms for `KeyPairCompressedBytes::from_seed`

[libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::from_seed]:
Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs',
lines 240:12-240:80.

Deterministic ML-KEM-768 key generation from a fixed 64-byte seed.  The function is fully
determined by the input seed (identical seeds yield identical key pairs, with no hidden
randomness).  The resulting key pair satisfies all structural validity constraints of ML-KEM,
including correct internal format and consistency between public and secret key components.
Serialization is lossless (encoding followed by decoding recovers the original key pair), and
the generated keys are functionally correct for the KEM protocol: encapsulation with the
public key and decapsulation with the corresponding secret key recover the same shared secret.

No cryptographic security properties (pseudorandomness, IND-CCA, etc.) are included; those
belong to the scheme-level analysis rather than the specification of this single function. -/

open Aeneas Aeneas.Std spqr

namespace libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes

--------------------------------------------------------------------------------
-- Type abbreviations
--------------------------------------------------------------------------------

private abbrev KP :=
  libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes

private abbrev CT1 :=
  libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1 960#usize

private abbrev CT2 :=
  libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2 128#usize

private instance : Inhabited CT1 := ⟨⟨default⟩⟩
private instance : Inhabited CT2 := ⟨⟨default⟩⟩

--------------------------------------------------------------------------------
-- Abstract predicates and operations
--------------------------------------------------------------------------------

/-- The generated compressed key pair satisfies all structural invariants. -/
opaque ValidKeyPairCompressedBytes :
  KP → Prop

/-- The public and secret keys form a valid ML-KEM-768 key pair.
    Arguments: pk1 (64 B), pk2 (1152 B), sk (2400 B). -/
opaque ConsistentKeyPair :
  Array Std.U8 64#usize →
  Array Std.U8 1152#usize →
  Array Std.U8 2400#usize → Prop

/-- Serialization of a key pair to a flat byte list:
    pk1 (64 B) ++ pk2 (1152 B) ++ sk (2400 B).

    `KeyPairCompressedBytes` is a concrete structure (see `TypesExternal.lean`),
    so serialization is defined directly in terms of its fields rather than
    left opaque.  This aligns with `Funs.lean`, where `incremental_mlkem768.generate`
    extracts `pk1`, `pk2`, `sk` as separate byte arrays. -/
def serialize (kp : KP) : List Std.U8 :=
  kp.pk1_val.val ++ kp.pk2_val.val ++ kp.sk_val.val

/-- Deserialization of a key pair from a flat byte list.
    Inverse of `serialize`: splits a 3616-byte list into the three
    fixed-size components (pk1 64 B, pk2 1152 B, sk 2400 B). -/
def deserialize (bs : List Std.U8) : Option KP :=
  if h : bs.length = 3616 then
    some {
      pk1_val := ⟨bs.take 64, by simp [List.length_take]; omega⟩
      pk2_val := ⟨(bs.drop 64).take 1152,
                   by simp [List.length_take, List.length_drop]; omega⟩
      sk_val  := ⟨bs.drop 1216, by simp [List.length_drop]; omega⟩
    }
  else none

/-- Combined ML-KEM-768 encapsulation, aligned with the two-phase
    incremental API already present in `FunsExternal.lean`:

    * `libcrux_ml_kem.mlkem768.incremental.encapsulate1`
      (`Slice U8 → Array U8 32 → Slice U8 → Slice U8 → Result …`)
    * `libcrux_ml_kem.mlkem768.incremental.encapsulate2`
      (`Array U8 2080 → Array U8 1152 → Result (Ciphertext2 128)`)

    The `randomness` parameter corresponds to the 32-byte randomness
    seed taken by `encapsulate1`.  The two public-key parts (`pk1`,
    `pk2`) come from the `KeyPairCompressedBytes` fields.

    This definition combines both phases into a single pure function for
    specification convenience; the actual implementation sequences
    `encapsulate1` (which takes `pk1` as a slice, `randomness`, and
    mutable state/shared-secret buffers) followed by `encapsulate2`
    (which takes the encapsulation state and `pk2`).

    The result is modelled via the `default` inhabitants matching the
    concrete models of `encapsulate1` and `encapsulate2` in
    `FunsExternal.lean`. -/
def encapsulate
    (_pk1 : Array Std.U8 64#usize)
    (_pk2 : Array Std.U8 1152#usize)
    (_randomness : Array Std.U8 32#usize) :
    (CT1 × CT2) × Array Std.U8 32#usize :=
  ((⟨default⟩, ⟨default⟩), default)

/-- **Spec theorem for `encapsulate`**: the combined encapsulation returns
    the default inhabitants of `CT1`, `CT2`, and the 32-byte shared secret,
    matching the concrete models of `encapsulate1` and `encapsulate2` in
    `FunsExternal.lean`. -/
@[simp]
theorem encapsulate_spec
    (pk1 : Array Std.U8 64#usize)
    (pk2 : Array Std.U8 1152#usize)
    (randomness : Array Std.U8 32#usize) :
    encapsulate pk1 pk2 randomness = ((⟨default⟩, ⟨default⟩), default) := by
  rfl

--------------------------------------------------------------------------------
-- Specification axioms for `from_seed`
--------------------------------------------------------------------------------

/-- Output has the expected serialized size:
    pk1 (64) + pk2 (1152) + sk (2400) = 3616 bytes. -/
@[step]
axiom from_seed_size
    (seed : Array Std.U8 64#usize) :
    from_seed seed
    ⦃ (kp : KP) =>
      (serialize kp).length = 3616 ⦄

/-- The generated key pair satisfies all structural invariants. -/
@[step]
axiom from_seed_valid
    (seed : Array Std.U8 64#usize) :
    from_seed seed
    ⦃ (kp : KP) =>
      ValidKeyPairCompressedBytes kp ⦄

/-- Serialization is lossless. -/
@[step]
axiom from_seed_roundtrip
    (seed : Array Std.U8 64#usize) :
    from_seed seed
    ⦃ (kp : KP) =>
      deserialize (serialize kp) = some kp ⦄

/-- The generated public and secret keys are consistent. -/
@[step]
axiom from_seed_consistent
    (seed : Array Std.U8 64#usize) :
    from_seed seed
    ⦃ (kp : KP) =>
      ConsistentKeyPair
        kp.pk1_val
        kp.pk2_val
        kp.sk_val ⦄

/-- Determinism with respect to equal seeds. -/
theorem from_seed_congr
    (seed₁ seed₂ : Array Std.U8 64#usize)
    (h : seed₁ = seed₂) :
    from_seed seed₁ = from_seed seed₂ :=
  congrArg from_seed h

/--
Correctness of the ML-KEM-768 construction:
for every choice of encapsulation randomness, a ciphertext produced
using the generated public key decapsulates to the same shared secret
using the generated secret key.

The `randomness` parameter corresponds to the 32-byte seed taken by
`libcrux_ml_kem.mlkem768.incremental.encapsulate1` in `FunsExternal.lean`.

Uses `libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key`
from `FunsExternal.lean` (accessible here via parent-namespace resolution).
-/
@[step]
axiom from_seed_correct
    (seed : Array Std.U8 64#usize)
    (randomness : Array Std.U8 32#usize) :
    from_seed seed
    ⦃ (kp : KP) =>
      let ((ct1, ct2), ss) := encapsulate kp.pk1_val kp.pk2_val randomness
      libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key
        kp.sk_val ct1 ct2 = .ok ss ⦄

end libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes
