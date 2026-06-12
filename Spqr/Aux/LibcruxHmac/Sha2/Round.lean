/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Aux.LibcruxHmac.Word
import Spqr.Aux.LibcruxHmac.Sha1.Round
import Spqr.Aux.LibcruxHmac.Sha2.Constants

/-!
# SHA-2 round functions, schedule and compression (FIPS 180-2 §4.1.2–§4.1.3, §6.2–§6.4)

This file implements the SHA-2 logical (sigma) functions, the message
schedule and the single-block compression for both the SHA-256 (32-bit) and
SHA-512/SHA-384 (64-bit) families (FIPS 180-2 §4.1.2/§4.1.3 and §6.2/§6.4).

The `Ch` and `Maj` functions are *shared* with SHA-1 and are imported from
`Sha1/Round.lean`.

## Sigma functions (FIPS 180-2 §4.1.2 / §4.1.3)

SHA-256 (32-bit, `{256}`):

```
Σ₀(x) = ROTR² x  ⊕ ROTR¹³ x ⊕ ROTR²² x
Σ₁(x) = ROTR⁶ x  ⊕ ROTR¹¹ x ⊕ ROTR²⁵ x
σ₀(x) = ROTR⁷ x  ⊕ ROTR¹⁸ x ⊕ SHR³  x
σ₁(x) = ROTR¹⁷ x ⊕ ROTR¹⁹ x ⊕ SHR¹⁰ x
```

SHA-512/SHA-384 (64-bit, `{512}`):

```
Σ₀(x) = ROTR²⁸ x ⊕ ROTR³⁴ x ⊕ ROTR³⁹ x
Σ₁(x) = ROTR¹⁴ x ⊕ ROTR¹⁸ x ⊕ ROTR⁴¹ x
σ₀(x) = ROTR¹  x ⊕ ROTR⁸  x ⊕ SHR⁷  x
σ₁(x) = ROTR¹⁹ x ⊕ ROTR⁶¹ x ⊕ SHR⁶  x
```

## Message schedule (FIPS 180-2 §6.2.2 / §6.4.2)

```
W_t = M_t                                        (0  ≤ t ≤ 15)
W_t = σ₁(W_{t-2}) +ʷ W_{t-7} +ʷ σ₀(W_{t-15}) +ʷ W_{t-16}   (16 ≤ t)
```

with 64 rounds for SHA-256 and 80 rounds for SHA-512/SHA-384.

## Compression (FIPS 180-2 §6.2.2 / §6.4.2)

For each round `t`, working variables `(a, b, c, d, e, f, g, h)`:

```
T₁ = h +ʷ Σ₁(e) +ʷ Ch(e, f, g) +ʷ K_t +ʷ W_t
T₂ = Σ₀(a) +ʷ Maj(a, b, c)
(a, b, c, d, e, f, g, h) ← (T₁+ʷT₂, a, b, c, d+ʷT₁, e, f, g)
```

This file defines:

* `bsig0_256`, `bsig1_256`, `ssig0_256`, `ssig1_256` — the 32-bit Σ/σ
  functions (S9);
* `bsig0_512`, `bsig1_512`, `ssig0_512`, `ssig1_512` — the 64-bit Σ/σ
  functions (S9);
* `sha256Next`, `sha512Next` — schedule recurrences;
* `sha256Schedule`, `sha512Schedule` — the message schedules (S10);
* `sha256RoundStep`, `sha512RoundStep` — one compression round (S11);
* `sha256CompressW`/`sha256Compress`, `sha512CompressW`/`sha512Compress` —
  single-block compression (S11);

together with:

natural language specs:
- `sha256RoundStep_length` / `sha512RoundStep_length` (SL12): one round
  preserves the 8-word state;
- `sha256Schedule_length` / `sha512Schedule_length` (SL12): schedules have
  64 / 80 words;
- `sha256Compress_length` / `sha512Compress_length` (SL12): compression
  preserves the 8-word state.

**Source**: FIPS 180-2 §4.1.2/§4.1.3 (SHA-2 functions), §6.2.2/§6.4.2
(SHA-256/SHA-512 hash computation).
-/

open Aeneas Aeneas.Std

namespace spec.sha

/-! ## Logical-right-shift abbreviation -/

/-- SHA `SHR(n, x)` — logical right shift by `n` bits (FIPS 180-2 §3.2,
    equation (3.2)).  Defined directly on the underlying `BitVec` (a pure,
    total logical right shift), mirroring the `rotl`/`rotr` abbreviations in
    `Word.lean`. -/
def shr {ty : UScalarTy} (n : U32) (x : UScalar ty) : UScalar ty :=
  ⟨x.bv >>> n.val⟩


/-! ## SHA-256 (32-bit) sigma functions (FIPS 180-2 §4.1.2) -/

/-- `Σ₀^{256}(x) = ROTR² x ⊕ ROTR¹³ x ⊕ ROTR²² x` (FIPS 180-2 §4.1.2). -/
def bsig0_256 (x : U32) : U32 :=
  (rotr 2#u32 x ^^^ rotr 13#u32 x) ^^^ rotr 22#u32 x

/-- `Σ₁^{256}(x) = ROTR⁶ x ⊕ ROTR¹¹ x ⊕ ROTR²⁵ x` (FIPS 180-2 §4.1.2). -/
def bsig1_256 (x : U32) : U32 :=
  (rotr 6#u32 x ^^^ rotr 11#u32 x) ^^^ rotr 25#u32 x

/-- `σ₀^{256}(x) = ROTR⁷ x ⊕ ROTR¹⁸ x ⊕ SHR³ x` (FIPS 180-2 §4.1.2). -/
def ssig0_256 (x : U32) : U32 :=
  (rotr 7#u32 x ^^^ rotr 18#u32 x) ^^^ shr 3#u32 x

/-- `σ₁^{256}(x) = ROTR¹⁷ x ⊕ ROTR¹⁹ x ⊕ SHR¹⁰ x` (FIPS 180-2 §4.1.2). -/
def ssig1_256 (x : U32) : U32 :=
  (rotr 17#u32 x ^^^ rotr 19#u32 x) ^^^ shr 10#u32 x

/-! ## SHA-512 (64-bit) sigma functions (FIPS 180-2 §4.1.3) -/

/-- `Σ₀^{512}(x) = ROTR²⁸ x ⊕ ROTR³⁴ x ⊕ ROTR³⁹ x` (FIPS 180-2 §4.1.3). -/
def bsig0_512 (x : U64) : U64 :=
  (rotr 28#u32 x ^^^ rotr 34#u32 x) ^^^ rotr 39#u32 x

/-- `Σ₁^{512}(x) = ROTR¹⁴ x ⊕ ROTR¹⁸ x ⊕ ROTR⁴¹ x` (FIPS 180-2 §4.1.3). -/
def bsig1_512 (x : U64) : U64 :=
  (rotr 14#u32 x ^^^ rotr 18#u32 x) ^^^ rotr 41#u32 x

/-- `σ₀^{512}(x) = ROTR¹ x ⊕ ROTR⁸ x ⊕ SHR⁷ x` (FIPS 180-2 §4.1.3). -/
def ssig0_512 (x : U64) : U64 :=
  (rotr 1#u32 x ^^^ rotr 8#u32 x) ^^^ shr 7#u32 x

/-- `σ₁^{512}(x) = ROTR¹⁹ x ⊕ ROTR⁶¹ x ⊕ SHR⁶ x` (FIPS 180-2 §4.1.3). -/
def ssig1_512 (x : U64) : U64 :=
  (rotr 19#u32 x ^^^ rotr 61#u32 x) ^^^ shr 6#u32 x

/-! ## SHA-256 message schedule (FIPS 180-2 §6.2.2) -/

/-- The SHA-256 schedule recurrence
    `W_t = σ₁(W_{t-2}) +ʷ W_{t-7} +ʷ σ₀(W_{t-15}) +ʷ W_{t-16}`
    (FIPS 180-2 §6.2.2). -/
def sha256Next (ws : List U32) : U32 :=
  let n := ws.length
  wadd (wadd (wadd (ssig1_256 ws[n-2]!) ws[n-7]!) (ssig0_256 ws[n-15]!))
    ws[n-16]!

/-- The 64-word SHA-256 message schedule from a 16-word block
    (FIPS 180-2 §6.2.2). -/
def sha256Schedule (block : List U32) : List U32 :=
  extendTo sha256Next 64 block

/-- **Spec lemma (`sha256Schedule_length`, SL12)**: from a 16-word block the
    schedule has exactly 64 words. -/
theorem sha256Schedule_length (block : List U32) (h : block.length = 16) :
    (sha256Schedule block).length = 64 := by
  unfold sha256Schedule
  exact extendTo_length sha256Next 64 block (by omega)

/-! ## SHA-512 message schedule (FIPS 180-2 §6.4.2) -/

/-- The SHA-512 schedule recurrence
    `W_t = σ₁(W_{t-2}) +ʷ W_{t-7} +ʷ σ₀(W_{t-15}) +ʷ W_{t-16}`
    (FIPS 180-2 §6.4.2). -/
def sha512Next (ws : List U64) : U64 :=
  let n := ws.length
  wadd (wadd (wadd (ssig1_512 ws[n-2]!) ws[n-7]!) (ssig0_512 ws[n-15]!))
    ws[n-16]!

/-- The 80-word SHA-512 message schedule from a 16-word block
    (FIPS 180-2 §6.4.2). -/
def sha512Schedule (block : List U64) : List U64 :=
  extendTo sha512Next 80 block

/-- **Spec lemma (`sha512Schedule_length`, SL12)**: from a 16-word block the
    schedule has exactly 80 words. -/
theorem sha512Schedule_length (block : List U64) (h : block.length = 16) :
    (sha512Schedule block).length = 80 := by
  unfold sha512Schedule
  exact extendTo_length sha512Next 80 block (by omega)

/-! ## SHA-256 compression (FIPS 180-2 §6.2.2) -/

/-- One round of the SHA-256 compression loop with working variables
    `st = [a, b, c, d, e, f, g, h]`, schedule word `wt`, and round constant
    `kt` (FIPS 180-2 §6.2.2):

    ```
    T₁ = h +ʷ Σ₁(e) +ʷ Ch(e, f, g) +ʷ kt +ʷ wt
    T₂ = Σ₀(a) +ʷ Maj(a, b, c)
    (a, …, h) ← (T₁+ʷT₂, a, b, c, d+ʷT₁, e, f, g)
    ``` -/
def sha256RoundStep (kt wt : U32) (st : List U32) : List U32 :=
  let a := st[0]!
  let b := st[1]!
  let c := st[2]!
  let d := st[3]!
  let e := st[4]!
  let f := st[5]!
  let g := st[6]!
  let h := st[7]!
  let t1 :=
    wadd (wadd (wadd (wadd h (bsig1_256 e)) (ch e f g)) kt) wt
  let t2 := wadd (bsig0_256 a) (maj a b c)
  [wadd t1 t2, a, b, c, wadd d t1, e, f, g]

/-- **Spec lemma (`sha256RoundStep_length`, SL12)**: a round always yields an
    8-word state. -/
@[simp]
theorem sha256RoundStep_length (kt wt : U32) (st : List U32) :
    (sha256RoundStep kt wt st).length = 8 := by
  simp [sha256RoundStep]

/-- The range `[0, 64)` is non-empty (used for the SHA-256 compression
    fold). -/
theorem sha256_range_ne : (List.range 64) ≠ [] := by
  intro h
  have := congrArg List.length h
  simp only [List.length_range, List.length_nil] at this
  omega

/-- SHA-256 single-block compression from a *precomputed* schedule `w`: run
    the 64 rounds, then add (wordwise, mod 2³²) the result back into the
    input state `st` (FIPS 180-2 §6.2.2). -/
def sha256CompressW (st w : List U32) : List U32 :=
  List.zipWith wadd st
    ((List.range 64).foldl (fun acc t => sha256RoundStep (k256[t]!) w[t]! acc) st)

/-- **Spec lemma (`sha256CompressW_length`, SL12)**: compression preserves
    the 8-word state. -/
theorem sha256CompressW_length (st w : List U32) (h : st.length = 8) :
    (sha256CompressW st w).length = 8 := by
  unfold sha256CompressW
  rw [List.length_zipWith,
      foldl_const_length _ 8
        (fun s x => sha256RoundStep_length (k256[x]!) (w[x]!) s)
        (List.range 64) sha256_range_ne st, h]
  exact Nat.min_self 8

/-- SHA-256 single-block compression: parse the schedule from `block`, then
    run `sha256CompressW` (FIPS 180-2 §6.2.2). -/
def sha256Compress (st block : List U32) : List U32 :=
  sha256CompressW st (sha256Schedule block)

/-- **Spec lemma (`sha256Compress_length`, SL12)**: compression preserves the
    8-word state. -/
theorem sha256Compress_length (st block : List U32) (h : st.length = 8) :
    (sha256Compress st block).length = 8 := by
  unfold sha256Compress
  exact sha256CompressW_length st (sha256Schedule block) h

/-! ## SHA-512 compression (FIPS 180-2 §6.4.2) -/

/-- One round of the SHA-512 compression loop with working variables
    `st = [a, b, c, d, e, f, g, h]`, schedule word `wt`, and round constant
    `kt` (FIPS 180-2 §6.4.2).  Identical structure to SHA-256 but with the
    64-bit sigma functions. -/
def sha512RoundStep (kt wt : U64) (st : List U64) : List U64 :=
  let a := st[0]!
  let b := st[1]!
  let c := st[2]!
  let d := st[3]!
  let e := st[4]!
  let f := st[5]!
  let g := st[6]!
  let h := st[7]!
  let t1 :=
    wadd (wadd (wadd (wadd h (bsig1_512 e)) (ch e f g)) kt) wt
  let t2 := wadd (bsig0_512 a) (maj a b c)
  [wadd t1 t2, a, b, c, wadd d t1, e, f, g]

/-- **Spec lemma (`sha512RoundStep_length`, SL12)**: a round always yields an
    8-word state. -/
@[simp]
theorem sha512RoundStep_length (kt wt : U64) (st : List U64) :
    (sha512RoundStep kt wt st).length = 8 := by
  simp [sha512RoundStep]

/-- The range `[0, 80)` is non-empty (used for the SHA-512 compression
    fold). -/
theorem sha512_range_ne : (List.range 80) ≠ [] := sha1_range_ne

/-- SHA-512 single-block compression from a *precomputed* schedule `w`: run
    the 80 rounds, then add (wordwise, mod 2⁶⁴) the result back into the
    input state `st` (FIPS 180-2 §6.4.2). -/
def sha512CompressW (st w : List U64) : List U64 :=
  List.zipWith wadd st
    ((List.range 80).foldl (fun acc t => sha512RoundStep (k512[t]!) w[t]! acc) st)

/-- **Spec lemma (`sha512CompressW_length`, SL12)**: compression preserves
    the 8-word state. -/
theorem sha512CompressW_length (st w : List U64) (h : st.length = 8) :
    (sha512CompressW st w).length = 8 := by
  unfold sha512CompressW
  rw [List.length_zipWith,
      foldl_const_length _ 8
        (fun s x => sha512RoundStep_length (k512[x]!) (w[x]!) s)
        (List.range 80) sha512_range_ne st, h]
  exact Nat.min_self 8

/-- SHA-512 single-block compression: parse the schedule from `block`, then
    run `sha512CompressW` (FIPS 180-2 §6.4.2). -/
def sha512Compress (st block : List U64) : List U64 :=
  sha512CompressW st (sha512Schedule block)

/-- **Spec lemma (`sha512Compress_length`, SL12)**: compression preserves the
    8-word state. -/
theorem sha512Compress_length (st block : List U64) (h : st.length = 8) :
    (sha512Compress st block).length = 8 := by
  unfold sha512Compress
  exact sha512CompressW_length st (sha512Schedule block) h

end spec.sha
