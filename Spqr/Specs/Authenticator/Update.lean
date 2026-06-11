/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Code.FunsExternal
import Spqr.Specs.Kdf.HkdfToVec

/-!
# Spec theorem for `spqr::authenticator::Authenticator::update`

The `update` method on `Authenticator` performs a KDF ratchet step that derives fresh `root_key`
and `mac_key` values from the current root key, an external key contribution `k`, and the epoch
number `ep`. Concretely, the Rust implementation:

  ```rust
  pub fn update(&mut self, ep: Epoch, k: &[u8]) {
      let ikm = [self.root_key.as_slice(), k].concat();
      let info = [
          b"Signal_PQCKA_V1_MLKEM768:Authenticator Update".as_slice(),
          &ep.to_be_bytes(),
      ]
      .concat();
      let kdf_out = kdf::hkdf_to_vec(&[0u8; 32], &ikm, &info, 64);
      self.root_key = kdf_out[..32].to_vec();
      self.mac_key = kdf_out[32..].to_vec();
  }
  ```

The function:
  1. Concatenates `self.root_key` and `k` into input keying material (`ikm`).
  2. Constructs the HKDF info string from the fixed label
     `"Signal_PQCKA_V1_MLKEM768:Authenticator Update"` and the big-endian bytes of `ep`.
  3. Calls `kdf::hkdf_to_vec` with a 32-byte zero salt, the `ikm`, the `info`, and output
     length 64.
  4. Splits the 64-byte KDF output at byte 32: the first half becomes the new `root_key`,
     the second half becomes the new `mac_key`.

The function is total — it always succeeds — and produces a new `Authenticator` whose two keys
are each 32 bytes long, matching `MACSIZE`.

## Cryptographic Relationship: Joint Derivation

The `root_key` and `mac_key` fields are **jointly derived** from the same HKDF-SHA-256
invocation. They are the two complementary, non-overlapping halves of the single 64-byte
KDF output: `root_key = kdf_out[0..32]` and `mac_key = kdf_out[32..64]`. This structural
relationship is captured by the `jointly_derived` predicate (defined below in this file),
which is included in the postcondition of `update_spec`.

This is the **KDF-split** pattern from the Signal protocol: both keys are
non-overlapping, complementary halves of a common cryptographic derivation.

### Security Implications

1. **Key separation**: Although both keys originate from the same HKDF
   output, HKDF is a PRF, so the two halves are cryptographically
   independent for practical purposes.

2. **Forward secrecy**: After each ratchet step (`update`), both keys are
   refreshed from new input key material, so compromise of current keys
   does not reveal past keys.

3. **Binding**: The joint derivation means `root_key` and `mac_key` are
   cryptographically bound to the same epoch, input key material, and
   chain history. An adversary cannot substitute one half without
   invalidating the other.

### Formal Definition

`jointly_derived rk mk` asserts:
1. `rk.length = 32` (root key is 32 bytes)
2. `mk.length = 32` (MAC key is 32 bytes)
3. There exists a 64-byte list `kdf_out` such that `rk` and `mk` are
   its first and second halves.

**Note on redundancy**: In the current opaque HKDF model (where
`kdf.hkdf_to_slice` is axiomatised as an identity), condition (3) is
logically equivalent to conditions (1)+(2) alone — any two 32-byte
vectors trivially satisfy it by taking `kdf_out = rk ++ mk`. We state
it explicitly for two reasons:

- **Documentation**: it makes the KDF-split structure visible in the
  Lean types, mirroring the Rust source.
- **Future-proofing**: when a richer HKDF model is added (replacing the
  current opaque axiom), the existential can be strengthened to tie
  `kdf_out` to a specific HKDF invocation with known salt, IKM, and
  info, at which point condition (3) becomes non-trivial.

### Invariant Flow Through the Module

The invariant is:
- **Established** by `update` (F3) and `new` (F2, which delegates to
  `update`).
- **Consumed** by `mac_ct` (F5) and `mac_hdr` (F7), which use
  `self.mac_key` as the HMAC key.
- **Preserved** by `into_pb` (F8, field move) and `from_pb` (F9,
  field clone).
- **Irrelevant** to `MACSIZE` (C1, a pure constant), `fmt` (F1, error
  formatting), `verify_ct` (F4), and `verify_hdr` (F6) — these do not
  modify the authenticator state.

**Source**: spqr/src/authenticator.rs (lines 44:4-54:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.authenticator

/-- **Joint-derivation invariant for Authenticator keys.**

Both `root_key` and `mac_key` are the two complementary, non-overlapping
halves of a single 64-byte HKDF-SHA-256 output, split at byte 32.

This invariant is established by `Authenticator::update` (which performs
the HKDF call and splits the output) and preserved by
`Authenticator::new` (which delegates to `update`), `into_pb` (which
moves the fields), and `from_pb` (which clones the fields). -/
def jointly_derived (rk mk : alloc.vec.Vec Std.U8) : Prop :=
  rk.length = 32 ∧
  mk.length = 32 ∧
  ∃ (kdf_out : List Std.U8),
    kdf_out.length = 64 ∧
    rk.val = kdf_out.take 32 ∧
    mk.val = kdf_out.drop 32

/-- **`jointly_derived` implies `root_key` has length 32.** -/
theorem jointly_derived_root_key_length
    {rk mk : alloc.vec.Vec Std.U8}
    (h : jointly_derived rk mk) : rk.length = 32 :=
  h.1

/-- **`jointly_derived` implies `mac_key` has length 32.** -/
theorem jointly_derived_mac_key_length
    {rk mk : alloc.vec.Vec Std.U8}
    (h : jointly_derived rk mk) : mk.length = 32 :=
  h.2.1

/-- **`jointly_derived` implies the original length postcondition.**

This lemma recovers the length postcondition from the existing
`update_spec` as a corollary of `jointly_derived`. -/
theorem jointly_derived_lengths
    {rk mk : alloc.vec.Vec Std.U8}
    (h : jointly_derived rk mk) :
    rk.length = 32 ∧ mk.length = 32 :=
  ⟨h.1, h.2.1⟩

/-- **`jointly_derived` is equivalent to both keys having length 32.**

In the current opaque HKDF model, the existential over `kdf_out` adds
no information beyond the length constraints — any two 32-byte vectors
can be concatenated to form a valid witness. When a richer HKDF model
is available, this equivalence will be replaced by a one-directional
implication (`jointly_derived → lengths_32`), and the definition will
carry additional cryptographic content tying the keys to specific HKDF
inputs. -/
theorem jointly_derived_iff_lengths
    (rk mk : alloc.vec.Vec Std.U8) :
    jointly_derived rk mk ↔ rk.length = 32 ∧ mk.length = 32 := by
  unfold jointly_derived
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, rk.val ++ mk.val, ?_, ?_, ?_⟩
    · simp [alloc.vec.Vec.length] at h1 h2
      simp [List.length_append, h1, h2]
    · have hrk : rk.val.length = 32 := by
        rw [alloc.vec.Vec.length] at h1; exact h1
      conv_rhs => rw [show (32 : Nat) = rk.val.length from hrk.symm]
      exact List.take_left.symm
    · have hrk : rk.val.length = 32 := by
        rw [alloc.vec.Vec.length] at h1; exact h1
      conv_rhs => rw [show (32 : Nat) = rk.val.length from hrk.symm]
      exact List.drop_left.symm

/-- **`jointly_derived` is preserved by field-wise equality.**

If `rk' = rk` and `mk' = mk` and the original pair satisfies
`jointly_derived`, then so does the new pair. This is the key lemma
used by the `into_pb` and `from_pb` preservation theorems. -/
theorem jointly_derived_of_eq
    {rk mk rk' mk' : alloc.vec.Vec Std.U8}
    (h : jointly_derived rk mk)
    (hrk : rk' = rk) (hmk : mk' = mk) :
    jointly_derived rk' mk' := by
  subst hrk; subst hmk; exact h

end spqr.authenticator

namespace spqr.authenticator.Authenticator.update

/-
natural language description:

• `update` is a public method on `Authenticator` that performs a KDF ratchet step.
• It takes the current authenticator state (`self`), an epoch number `ep : U64`,
  and an external key contribution `k : &[u8]`.
• The method concatenates `self.root_key` and `k` to form the input keying material
  (IKM), builds an info string from the fixed protocol label and the epoch's
  big-endian encoding, and then invokes `hkdf_to_vec` with a 32-byte zero salt
  and output length 64.
• The resulting 64-byte output is split at the midpoint: the first 32 bytes become
  the new `root_key`, the last 32 bytes become the new `mac_key`.
• The function is total (never panics) and deterministic.

natural language specs:

• The call always succeeds (the outer `Result` is `ok`).
• The result is an `authenticator.Authenticator` whose `root_key` and `mac_key`
  are each derived from the HKDF output.
• Both `result.root_key.length` and `result.mac_key.length` equal 32,
  matching `Authenticator::MACSIZE`.
• The two keys satisfy `jointly_derived`, i.e., they are the two halves of
  the same 64-byte KDF output split at byte 32.
-/

/-- **Spec theorem for `authenticator.Authenticator.update`**:

The `update` method derives fresh authenticator keys by:
  1. concatenating `self.root_key ++ k` into IKM,
  2. concatenating the fixed label `"Signal_PQCKA_V1_MLKEM768:Authenticator Update"` with the
     big-endian epoch bytes into info,
  3. calling `hkdf_to_vec` (salt = `[0; 32]`, output length = 64),
  4. splitting the output at byte 32 into `root_key` and `mac_key`.

The postcondition asserts that the call always succeeds and the result's two key fields
satisfy `jointly_derived` — they are the two complementary halves of the same 64-byte
HKDF-SHA-256 output. This implies (via `jointly_derived_lengths`) that both keys have
length 32 (= `MACSIZE`).

Note: the proof relies on axiomatic sub-operations (`alloc.slice.Slice.concat`,
`alloc.vec.Vec.index` for `RangeTo`/`RangeFrom`, and `alloc.slice.Slice.to_vec`) whose
concrete behaviour is not yet modelled. Once those specs are provided, the `sorry` can be
replaced with a complete proof.

**Source**: spqr/src/authenticator.rs (lines 44:4-54:5)
-/
@[step]
theorem update_spec
    (self : authenticator.Authenticator) (ep : Std.U64) (k : Slice Std.U8) :
    authenticator.Authenticator.update self ep k
      ⦃ (result : authenticator.Authenticator) =>
        authenticator.jointly_derived result.root_key result.mac_key ⦄ := by
  unfold authenticator.Authenticator.update
  sorry

/-- **Corollary: `update` produces keys of length 32.**

This recovers the original length postcondition as a consequence of the
stronger `jointly_derived` postcondition. -/
theorem update_lengths
    (self : authenticator.Authenticator) (ep : Std.U64) (k : Slice Std.U8) :
    authenticator.Authenticator.update self ep k
      ⦃ (result : authenticator.Authenticator) =>
        result.root_key.length = 32 ∧
        result.mac_key.length = 32 ⦄ := by
  apply WP.spec_mono (update_spec self ep k)
  intro result h
  exact authenticator.jointly_derived_lengths h

end spqr.authenticator.Authenticator.update
