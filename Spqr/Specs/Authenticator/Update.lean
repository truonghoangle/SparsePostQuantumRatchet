/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Code.FunsExternal
import Spqr.Specs.Kdf.HkdfToVec
import Spqr.Specs.Authenticator.JointDerivation

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
relationship is captured by the `jointly_derived` predicate (defined in
`Spqr/Specs/Authenticator/JointDerivation.lean`), which is included in the postcondition
of `update_spec`.

**Source**: spqr/src/authenticator.rs (lines 44:4-54:5)
-/

open Aeneas Aeneas.Std Result spqr

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
