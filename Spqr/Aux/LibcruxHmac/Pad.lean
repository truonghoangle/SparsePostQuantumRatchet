/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Aeneas

/-!
# Merkle–Damgård padding for SHA-1 / SHA-2

FIPS 180-2 §5.1 specifies the padding applied to a message `m` before
hashing.  The padded message is:

```
padded = m ∥ 0x80 ∥ 0^k ∥ ⟨8·|m|⟩_L
```

where `k` is the minimal non-negative integer such that `|padded| ≡ 0 (mod B)`,
and `⟨8·|m|⟩_L` is the message bit-length encoded as `L` big-endian bytes.
The block size `B` and length-field width `L` are hash-dependent:

| Hash     | B   | L  |
|----------|-----|----|
| SHA-1    | 64  | 8  |
| SHA-256  | 64  | 8  |
| SHA-384  | 128 | 16 |
| SHA-512  | 128 | 16 |

This file defines:

* `byte n` — create a `U8` from a natural number (modulo 256);
* `lenBytes L n` — big-endian encoding of `n` in `L` bytes (S5);
* `padAmount B L n` — number of zero-padding bytes (helper);
* `pad B L m` — the full FIPS 180-2 §5.1 padding (S4);

together with:

natural language specs:
- `byte_inj`: `byte` is injective on `[0, 256)`;
- `lenBytes_length` (SL3): `(lenBytes L n).length = L`;
- `lenBytes_inj` (SL4): `lenBytes L` is injective for values `< 2^(8*L)`;
- `pad_length`: `(pad B L m).length = m.length + 1 + padAmount B L m.length + L`;
- `pad_length_mod` (SL5): `(pad B L m).length % B = 0` (for `0 < B`);
- `pad_prefix` (SL6): `(pad B L m).take m.length = m`;
- `pad_length_le` (SL7): `(pad B L m).length ≤ m.length + L + B` (for `0 < B`);
- `pad_inj` (ST5): `pad B L` is injective (Merkle–Damgård suffix-freeness),
  under the message-length bound `8 * m.length < 2^(8*L)`.

**Source**: FIPS 180-2 §5.1 (padding the message).
-/

open Aeneas Aeneas.Std

namespace spec.sha

/-! ## Byte construction helper -/

/-- Create a `U8` from a natural number `n` (taken modulo 256).
    Used to construct the `0x80` marker byte, zero-padding bytes, and
    length-field bytes in the SHA padding. -/
@[reducible]
def byte (n : Nat) : U8 := ⟨BitVec.ofNat 8 n⟩

/-- **Spec lemma (`byte_inj`)**: `byte` is injective on values in `[0, 256)`.
    Two bytes constructed from in-range naturals are equal only when the
    naturals are equal. -/
theorem byte_inj {n m : Nat} (hn : n < 256) (hm : m < 256)
    (h : byte n = byte m) : n = m := by
  simp only [byte, UScalar.mk.injEq] at h
  have := congr_arg BitVec.toNat h
  simp [BitVec.toNat_ofNat] at this
  omega

/-! ## Big-endian length encoding (S5, FIPS 180-2 §5.1) -/

/-- Big-endian encoding of the natural number `n` in exactly `L` bytes.

    FIPS 180-2 §5.1: the message bit-length is encoded as `L` big-endian
    bytes (`L = 8` for SHA-1/SHA-256, `L = 16` for SHA-384/SHA-512).

    The encoding is total: values exceeding `2^(8·L)` are silently reduced
    modulo `2^(8·L)`.  The injectivity lemma `lenBytes_inj` restricts to the
    in-range case `n < 2^(8·L)`. -/
def lenBytes : Nat → Nat → List U8
  | 0,     _ => []
  | L + 1, n => lenBytes L (n / 256) ++ [byte (n % 256)]

/-- **Spec lemma (`lenBytes_length`, SL3)**: the big-endian encoding always
    has exactly `L` bytes. -/
@[simp]
theorem lenBytes_length : ∀ (L n : Nat), (lenBytes L n).length = L
  | 0,     _ => rfl
  | L + 1, n => by simp [lenBytes, lenBytes_length L]

/-- Auxiliary bound: if `n < 2^(8·(L+1))` then `n / 256 < 2^(8·L)`.
    This is used in the inductive step of `lenBytes_inj` to establish the
    bound for the recursive call. -/
private theorem div_256_lt_of_lt_pow {L n : Nat}
    (h : n < 2 ^ (8 * (L + 1))) : n / 256 < 2 ^ (8 * L) := by
  have h1 : 2 ^ (8 * (L + 1)) = 2 ^ (8 * L) * 256 := by
    have : 8 * (L + 1) = 8 * L + 8 := by omega
    rw [this, Nat.pow_add]
  omega

/-- **Spec lemma (`lenBytes_inj`, SL4)**: `lenBytes L` is injective on
    values below `2^(8·L)` (the representable range for `L` bytes).

    This is the key lemma underlying Merkle–Damgård suffix-freeness
    (`pad_inj`): the length suffix uniquely determines the original message
    length. -/
theorem lenBytes_inj : ∀ {L : Nat} {n m : Nat},
    n < 2 ^ (8 * L) → m < 2 ^ (8 * L) →
    lenBytes L n = lenBytes L m → n = m
  | 0, _, _, hn, _, _ => by omega
  | L + 1, n, m, hn, hm, h => by
    simp only [lenBytes] at h
    have hlen : (lenBytes L (n / 256)).length = (lenBytes L (m / 256)).length := by
      simp
    have h_pfx := List.append_inj_left h hlen
    have h_sfx := List.append_inj_right h hlen
    have h_mod : n % 256 = m % 256 := by
      simp only [List.cons.injEq, and_true] at h_sfx
      exact byte_inj (Nat.mod_lt n (by omega)) (Nat.mod_lt m (by omega)) h_sfx
    have h_div : n / 256 = m / 256 :=
      lenBytes_inj (div_256_lt_of_lt_pow hn) (div_256_lt_of_lt_pow hm) h_pfx
    have := Nat.div_add_mod n 256
    have := Nat.div_add_mod m 256
    omega

/-! ## Padding (S4, FIPS 180-2 §5.1) -/

/-- Number of zero-padding bytes in the Merkle–Damgård pad.
    Chosen so that `n + 1 + padAmount B L n + L ≡ 0 (mod B)`. -/
def padAmount (B L n : Nat) : Nat :=
  (B - (n + 1 + L) % B) % B

/-- Merkle–Damgård padding for SHA-1/SHA-2 (FIPS 180-2 §5.1).

    Given block size `B`, length-field width `L`, and message `m`,
    produces `m ∥ 0x80 ∥ 0^k ∥ ⟨8·|m|⟩_L` where `k = padAmount B L |m|`.

    The result has length divisible by `B` (see `pad_length_mod`). -/
def pad (B L : Nat) (m : List U8) : List U8 :=
  m ++ [byte 0x80] ++ List.replicate (padAmount B L m.length) (byte 0) ++
    lenBytes L (8 * m.length)

/-- **Spec lemma (`pad_length`)**: explicit length of the padded message. -/
@[simp]
theorem pad_length (B L : Nat) (m : List U8) :
    (pad B L m).length = m.length + 1 + padAmount B L m.length + L := by
  simp [pad]
  grind

/-- `padAmount B L n < B` when `B > 0`. -/
theorem padAmount_lt (B L n : Nat) (hB : 0 < B) : padAmount B L n < B :=
  Nat.mod_lt _ hB

/-! ### SL5: padded length is divisible by B -/

/-- Auxiliary: `(n + (B - n % B) % B) % B = 0` for `0 < B`.
    This is the core modular-arithmetic fact behind `pad_length_mod`. -/
private theorem mod_add_complement_eq_zero (n B : Nat) (hB : 0 < B) :
    (n + (B - n % B) % B) % B = 0 := by
  have hmod_lt : n % B < B := Nat.mod_lt n hB
  by_cases h : n % B = 0
  · simp [h]
  · rw [Nat.mod_eq_of_lt (show B - n % B < B by omega)]
    have hkey : n + (B - n % B) = n / B * B + B := by
      have := Nat.div_add_mod n B
      grind
    rw [hkey, show n / B * B + B = B * (n / B + 1) from by ring]
    exact Nat.mul_mod_right B _

/-- **Spec lemma (`pad_length_mod`, SL5)**: the padded message length is
    divisible by the block size `B`.

    Hypothesis: `0 < B` (satisfied by all SHA variants: `B ∈ {64, 128}`). -/
theorem pad_length_mod (B L : Nat) (hB : 0 < B) (m : List U8) :
    (pad B L m).length % B = 0 := by
  rw [pad_length]
  unfold padAmount
  have hrearrange : m.length + 1 + (B - (m.length + 1 + L) % B) % B + L =
                    (m.length + 1 + L) + (B - (m.length + 1 + L) % B) % B := by omega
  rw [hrearrange]
  exact mod_add_complement_eq_zero (m.length + 1 + L) B hB

/-! ### SL6: the message is a prefix of the padded output -/

/-- **Spec lemma (`pad_prefix`, SL6)**: the original message `m` is recovered
    as the first `m.length` bytes of `pad B L m`. -/
theorem pad_prefix (B L : Nat) (m : List U8) :
    (pad B L m).take m.length = m := by
  simp [pad, List.append_assoc]

/-! ### SL7: upper bound on padded length -/

/-- **Spec lemma (`pad_length_le`, SL7)**: the padded message is at most
    `m.length + L + B` bytes long.

    Hypothesis: `0 < B` (so that `padAmount < B`). -/
theorem pad_length_le (B L : Nat) (m : List U8) (hB : 0 < B) :
    (pad B L m).length ≤ m.length + L + B := by
  rw [pad_length]
  have := padAmount_lt B L m.length
  omega

/-! ### ST5: Merkle–Damgård padding is injective -/

/-- The "before" portion of the pad: `m ∥ 0x80 ∥ 0^k` (everything except
    the length field).  Private helper for the proof of `pad_inj`. -/
private def padBefore (B L : Nat) (m : List U8) : List U8 :=
  m ++ [byte 0x80] ++ List.replicate (padAmount B L m.length) (byte 0)

/-- The pad decomposes as `padBefore ++ lenBytes`. -/
private theorem pad_eq_before_append (B L : Nat) (m : List U8) :
    pad B L m = padBefore B L m ++ lenBytes L (8 * m.length) := by
  simp only [pad, padBefore, List.append_assoc]

/-- Taking the first `m.length` bytes of `padBefore` recovers `m`. -/
private theorem take_padBefore (B L : Nat) (m : List U8) :
    (padBefore B L m).take m.length = m := by
  simp [padBefore, List.append_assoc]

/-- **Spec theorem (`pad_inj`, ST5)**: Merkle–Damgård padding is injective
    (suffix-freeness).

    If two messages `m₁` and `m₂` satisfy the FIPS 180-2 message-length bound
    (`8 · |m| < 2^(8·L)`) and pad to the same output, then `m₁ = m₂`.

    The proof uses:
    1. decompose both sides as `padBefore ++ lenBytes`;
    2. `List.append_inj_left/right` with equal prefix lengths to split;
    3. `lenBytes_inj` (SL4) on the suffix to recover `|m₁| = |m₂|`;
    4. `take_padBefore` to recover `m₁ = m₂` from the shared prefix. -/
theorem pad_inj {B L : Nat} {m₁ m₂ : List U8}
    (h1 : 8 * m₁.length < 2 ^ (8 * L))
    (h2 : 8 * m₂.length < 2 ^ (8 * L))
    (h : pad B L m₁ = pad B L m₂) : m₁ = m₂ := by
  -- Step 1: decompose as padBefore ++ lenBytes
  rw [pad_eq_before_append, pad_eq_before_append] at h
  -- Step 2: the "before" parts have equal length
  have hlen_eq : (padBefore B L m₁).length = (padBefore B L m₂).length := by
    have h_total := congr_arg List.length h
    simp only [List.length_append, lenBytes_length] at h_total
    omega
  -- Step 3: split the append equality
  have hbefore := List.append_inj_left h hlen_eq
  have hsuffix := List.append_inj_right h hlen_eq
  -- Step 4: from the suffix, recover m₁.length = m₂.length
  have hlen : m₁.length = m₂.length := by
    have := lenBytes_inj h1 h2 hsuffix
    omega
  -- Step 5: from the prefix, recover m₁ = m₂
  have eq₁ := take_padBefore B L m₁
  have eq₂ := take_padBefore B L m₂
  rw [hbefore, hlen] at eq₁
  exact eq₁.symm.trans eq₂

end spec.sha
