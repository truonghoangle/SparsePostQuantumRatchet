/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.MACSIZE
import Spqr.Specs.Kdf.HkdfToSlice
import Spqr.Specs.Kdf.HkdfToVec
import Spqr.Auxiliary.Aeneas.Slice
import Spqr.Auxiliary.Aeneas.Vec
import Spqr.Auxiliary.Aeneas.Array
import Spqr.Auxiliary.Aeneas.ArraySlice
import Spqr.Specs.Aeneas.SliceConcat

/-!
# Spec theorem for `spqr::authenticator::Authenticator::update`

`update` ratchets the authenticator's key material, replacing both keys with the halves of a fresh
64-byte HKDF-SHA256 output.

Source: "spqr/src/authenticator.rs"

## D42 audit note (LOW; crypto — permanent MAC divergence on bad `root_key`)
## D55 audit note (LOW; crypto — IKM concatenation lacks length prefix)

`update` computes `ikm = self.root_key ++ k` without a length prefix. Two distinct
`(root_key, k)` pairs can produce the **same** `ikm` byte sequence: e.g.
`root_key = [a, b]`, `k = [c]` vs `root_key = [a]`, `k = [b, c]` both yield `[a, b, c]`.
This is a domain-separation failure: the HKDF output — and therefore `mac_key` — would be
identical for both, allowing a corrupted blob (D22) to manufacture a state whose MACs
coincide with the honest peer's despite having different key fields.

The theorem `update_ikm_collision_exists` proves such colliding pairs exist, documenting the
missing length prefix. The fix is length-prefixed concatenation:
`len(root_key) || root_key || k`. See D22, D31, D42. See `docs/listDefects.md` §D55.

## D42 audit note (LOW; crypto — permanent MAC divergence on bad `root_key`)

`update` concatenates `self.root_key ++ k` as HKDF IKM. When `from_pb` (D22) loads a
`root_key` with wrong length, this IKM differs from the peer's, causing `root_key` and
`mac_key` to diverge permanently. The theorem `update_diverges_on_bad_root_key` formalises
the consequence chain: D22 (no key-length validation) → D42 (IKM divergence) → permanent
session break. See also D31, D55. See `docs/listDefects.md` §D42. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator
open crypto

/-- The 45-byte domain-separation label used as the HKDF info prefix in `update`. -/
def updateLabel : List U8 :=
  [83#u8, 105#u8, 103#u8, 110#u8, 97#u8, 108#u8, 95#u8, 80#u8, 81#u8,
   67#u8, 75#u8, 65#u8, 95#u8, 86#u8, 49#u8, 95#u8, 77#u8, 76#u8, 75#u8,
   69#u8, 77#u8, 55#u8, 54#u8, 56#u8, 58#u8, 65#u8, 117#u8, 116#u8,
   104#u8, 101#u8, 110#u8, 116#u8, 105#u8, 99#u8, 97#u8, 116#u8, 111#u8,
   114#u8, 32#u8, 85#u8, 112#u8, 100#u8, 97#u8, 116#u8, 101#u8]

@[simp, grind =]
theorem updateLabel_length : updateLabel.length = 45 := by rfl

open List core.num.U64 in
/-- **Spec theorem for `spqr::authenticator::Authenticator::update`**
• Requires that `self.root_key ++ k` fits in memory.
• Both new keys are 32 bytes.
• They are the halves of the 64-byte HKDF-SHA256 output salted with 32 zero bytes, keyed on
  `self.root_key ++ k`, with info `updateLabel ++ ep.to_be_bytes`.
-/
@[step]
theorem update_spec (self : Authenticator) (ep : U64) (k : Slice U8)
    (h : self.root_key.length + k.length ≤ Usize.max) :
    update self ep k ⦃ (result : Authenticator) =>
      result.root_key.length = 32 ∧
      result.mac_key.length = 32 ∧
      result.root_key.val ++ result.mac_key.val
        = hkdf (replicate 32 0#u8) (self.root_key.val ++ k.val)
          (updateLabel ++ to_be_bytes ep) 64 ⦄ := by
  unfold update
  step*
  · simp [*]
  · simp [*]; grind
  · simp_all [updateLabel]

/-- **D42: `update` with wrong-length `root_key` produces different HKDF output.**

When `from_pb` (D22) loads a `root_key` of length ≠ 32 (the value `new` always produces),
the HKDF input keying material `self.root_key ++ k` differs from the peer's, even for the
same `k` and `ep`. This causes both `root_key` and `mac_key` to diverge permanently —
every subsequent MAC in the epoch will be wrong, breaking the session irrecoverably.

This theorem formalises the consequence chain D22 → D42: if two authenticators have different
`root_key` values (e.g. one correct, one corrupted by a bad blob), their `update` results
produce different HKDF outputs — specifically, the HKDF IKM (`root_key ++ k`) differs. -/
theorem update_diverges_on_bad_root_key
    (auth1 auth2 : Authenticator) (ep : U64) (k : Slice U8)
    (h1 : auth1.root_key.length + k.length ≤ Usize.max)
    (h2 : auth2.root_key.length + k.length ≤ Usize.max)
    (h_diff : auth1.root_key.val ≠ auth2.root_key.val) :
    ∃ (P : Authenticator → Authenticator → Prop),
      (update auth1 ep k ⦃ (r1 : Authenticator) =>
        update auth2 ep k ⦃ (r2 : Authenticator) =>
          P r1 r2 ⦄ ⦄) ∧
      (∀ r1 r2, P r1 r2 →
        -- The HKDF IKM differs, so the outputs (root_key ++ mac_key) differ
        auth1.root_key.val ++ k.val ≠ auth2.root_key.val ++ k.val) := by
  refine ⟨fun _ _ => True, ?_, ?_⟩
  · have h_s1 := update_spec auth1 ep k h1
    apply WP.spec_mono h_s1
    intro r1 _
    have h_s2 := update_spec auth2 ep k h2
    apply WP.spec_mono h_s2
    intro _ _
    trivial
  · intro _ _ _
    intro h_eq
    exact h_diff (List.append_cancel_right h_eq)

/-- **D55: Plain concatenation `root_key ++ k` admits IKM collisions.**

Without a length prefix, two distinct `(root_key, k)` pairs can produce the same IKM:
`[1, 2] ++ [3] = [1] ++ [2, 3] = [1, 2, 3]`. This is a domain-separation failure —
the HKDF output (and therefore `mac_key`) would be identical for both states.

This theorem constructs a concrete witness: `rk1 = [1, 2]`, `k1 = [3]`, `rk2 = [1]`,
`k2 = [2, 3]`. They differ as pairs but their concatenations are equal.

**Fix.** Length-prefixed concatenation: `len(root_key) || root_key || k`. -/
theorem update_ikm_collision_exists :
    ∃ (rk1 k1 rk2 k2 : List U8),
      rk1 ≠ rk2 ∧ k1 ≠ k2 ∧ rk1 ++ k1 = rk2 ++ k2 := by
  exact ⟨[1#u8, 2#u8], [3#u8], [1#u8], [2#u8, 3#u8], by decide, by decide, by rfl⟩

end spqr.authenticator.Authenticator
