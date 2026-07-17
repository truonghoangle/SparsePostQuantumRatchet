/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Aeneas

/-!
# SHA-1 constants (FIPS 180-2 §4.2.1, §5.3.1)

SHA-1 uses a sequence of constant 32-bit words `K_t` (FIPS 180-2 §4.2.1) and
a fixed initial hash value `H⁽⁰⁾` (FIPS 180-2 §5.3.1).

## Round constants `K_t` (FIPS 180-2 §4.2.1)

The eighty round constants take one of four values, depending on the round
index `t`:

```
K_t = 0x5a827999   (0  ≤ t ≤ 19)
K_t = 0x6ed9eba1   (20 ≤ t ≤ 39)
K_t = 0x8f1bbcdc   (40 ≤ t ≤ 59)
K_t = 0xca62c1d6   (60 ≤ t ≤ 79)
```

## Initial hash value `H⁽⁰⁾` (FIPS 180-2 §5.3.1)

```
H₀⁽⁰⁾ = 0x67452301
H₁⁽⁰⁾ = 0xefcdab89
H₂⁽⁰⁾ = 0x98badcfe
H₃⁽⁰⁾ = 0x10325476
H₄⁽⁰⁾ = 0xc3d2e1f0
```

This file defines:

* `sha1K t` — the round constant `K_t` selected by the round index `t` (S3);
* `sha1KList` — the eighty round constants as an explicit `List U32`;
* `sha1H0` — the five-word initial hash value (S3);

together with:

natural language specs:
- `sha1H0_length` (SL11): the SHA-1 IV has exactly 5 words;
- `sha1KList_length` (SL11): there are exactly 80 round constants;
- `sha1K_eq_getElem`: `sha1K t` agrees with the list at in-range indices;
- per-range value lemmas `sha1K_range0 … sha1K_range3` for the four bands.

The numeric values are transcribed from FIPS 180-2; the value-level
correctness of the whole pipeline is gated by the test vectors of Step 1.7.

**Source**: FIPS 180-2 §4.2.1 (SHA-1 constants), §5.3.1 (SHA-1 IV).
-/

open Aeneas Aeneas.Std

namespace spec.sha

/-! ## SHA-1 round constants (FIPS 180-2 §4.2.1) -/

/-- SHA-1 round constant `K_t`, selected by the round index `t`
    (FIPS 180-2 §4.2.1).  The four bands are
    `[0,20)`, `[20,40)`, `[40,60)`, `[60,80)`. -/
def sha1K (t : Nat) : U32 :=
  if t < 20 then 0x5a827999#u32
  else if t < 40 then 0x6ed9eba1#u32
  else if t < 60 then 0x8f1bbcdc#u32
  else 0xca62c1d6#u32

/-- The eighty SHA-1 round constants as an explicit list (FIPS 180-2 §4.2.1).
    Used as the `K`-table of the SHA-1 `HashParams` instance. -/
def sha1KList : List U32 :=
  List.replicate 20 0x5a827999#u32 ++
  List.replicate 20 0x6ed9eba1#u32 ++
  List.replicate 20 0x8f1bbcdc#u32 ++
  List.replicate 20 0xca62c1d6#u32

/-! ## SHA-1 initial hash value (FIPS 180-2 §5.3.1) -/

/-- The SHA-1 initial hash value `H⁽⁰⁾` (FIPS 180-2 §5.3.1): five 32-bit
    words. -/
def sha1H0 : List U32 :=
  [0x67452301#u32, 0xefcdab89#u32, 0x98badcfe#u32, 0x10325476#u32,
   0xc3d2e1f0#u32]

/-! ## Length lemmas (SL11) -/

/-- **Spec lemma (`sha1H0_length`, SL11)**: the SHA-1 IV has exactly 5
    words. -/
@[simp]
theorem sha1H0_length : sha1H0.length = 5 := by decide

/-- **Spec lemma (`sha1KList_length`, SL11)**: there are exactly 80 SHA-1
    round constants. -/
@[simp]
theorem sha1KList_length : sha1KList.length = 80 := by
  simp [sha1KList]

/-! ## Round-constant value lemmas -/

/-- **Spec lemma (`sha1K_range0`)**: `K_t = 0x5a827999` for `0 ≤ t < 20`. -/
theorem sha1K_range0 {t : Nat} (h : t < 20) : sha1K t = 0x5a827999#u32 := by
  simp [sha1K, h]

/-- **Spec lemma (`sha1K_range1`)**: `K_t = 0x6ed9eba1` for `20 ≤ t < 40`. -/
theorem sha1K_range1 {t : Nat} (h0 : 20 ≤ t) (h1 : t < 40) :
    sha1K t = 0x6ed9eba1#u32 := by
  simp only [sha1K]
  rw [if_neg (by omega), if_pos (by omega)]

/-- **Spec lemma (`sha1K_range2`)**: `K_t = 0x8f1bbcdc` for `40 ≤ t < 60`. -/
theorem sha1K_range2 {t : Nat} (h0 : 40 ≤ t) (h1 : t < 60) :
    sha1K t = 0x8f1bbcdc#u32 := by
  simp only [sha1K]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

/-- **Spec lemma (`sha1K_range3`)**: `K_t = 0xca62c1d6` for `60 ≤ t < 80`. -/
theorem sha1K_range3 {t : Nat} (h0 : 60 ≤ t) :
    sha1K t = 0xca62c1d6#u32 := by
  simp only [sha1K]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **Spec lemma (`sha1KList_eq_map`)**: the explicit round-constant table
    coincides with mapping the selector `sha1K` over `[0, 80)`. -/
theorem sha1KList_eq_map : sha1KList = (List.range 80).map sha1K := by
  decide

/-- **Spec lemma (`sha1K_eq_getElem`)**: the round-constant selector `sha1K`
    agrees with the explicit list `sha1KList` at every in-range index. -/
theorem sha1K_eq_getElem {t : Nat} (h : t < 80) :
    sha1KList[t]! = sha1K t := by
  rw [sha1KList_eq_map, List.getElem!_eq_getElem?_getD, List.getElem?_map]
  simp [h]


end spec.sha
