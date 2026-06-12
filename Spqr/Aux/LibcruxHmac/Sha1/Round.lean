/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Aux.LibcruxHmac.Word
import Spqr.Aux.LibcruxHmac.Sha1.Constants

/-!
# SHA-1 round functions, schedule and compression (FIPS 180-2 §4.1.1, §6.1)

This file implements the SHA-1 logical (round) functions, the message
schedule, and the single-block compression function (FIPS 180-2 §4.1.1 and
§6.1.2).

## Logical functions (FIPS 180-2 §4.1.1)

SHA-1 uses one of three logical functions `f_t(x, y, z)` per round band:

```
Ch(x, y, z)     = (x ∧ y) ⊕ (¬x ∧ z)        (0  ≤ t ≤ 19)
Parity(x, y, z) = x ⊕ y ⊕ z                 (20 ≤ t ≤ 39, 60 ≤ t ≤ 79)
Maj(x, y, z)    = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z) (40 ≤ t ≤ 59)
```

`Ch` and `Maj` are *shared* with SHA-2 (FIPS 180-2 §4.1.2/§4.1.3); they are
defined here generically over an arbitrary `UScalar ty` and re-used by
`Sha2/Round.lean`.

## Message schedule (FIPS 180-2 §6.1.2)

```
W_t = M_t                                                      (0  ≤ t ≤ 15)
W_t = ROTL¹(W_{t-3} ⊕ W_{t-8} ⊕ W_{t-14} ⊕ W_{t-16})          (16 ≤ t ≤ 79)
```

## Compression (FIPS 180-2 §6.1.2)

For each `t = 0 … 79` with working variables `(a, b, c, d, e)`:

```
T = ROTL⁵(a) +ʷ f_t(b, c, d) +ʷ e +ʷ K_t +ʷ W_t
(a, b, c, d, e) ← (T, a, ROTL³⁰(b), c, d)
```

The new hash state is the wordwise modular sum of the input state and the
final working variables.

This file defines:

* `ch`, `maj`, `parity` — the SHA logical functions (S8), generic over
  `UScalar ty` (shared with SHA-2);
* `extendTo` — generic schedule-extension helper;
* `sha1F` — the round-band selector `f_t`;
* `sha1Next` — the SHA-1 schedule recurrence step;
* `sha1Schedule` — the 80-word message schedule (S10);
* `sha1RoundStep` — one round of the compression loop (S11);
* `sha1CompressW` / `sha1Compress` — the single-block compression (S11);

together with:

natural language specs:
- `extendTo_length`: `extendTo f n ws` has length `n` when `ws.length ≤ n`;
- `foldl_const_length`: a left fold whose step has constant output length `n`
  has result length `n` over a non-empty list;
- `sha1RoundStep_length` (SL12): one round preserves the 5-word state;
- `sha1Schedule_length` (SL12): the schedule has exactly 80 words;
- `sha1Compress_length` (SL12): compression preserves the 5-word state;
- per-band value lemmas `sha1F_range0 … sha1F_range3`.

**Source**: FIPS 180-2 §4.1.1 (SHA-1 functions), §6.1.2 (SHA-1 hash
computation).
-/

open Aeneas Aeneas.Std

namespace spec.sha

/-! ## Logical functions (FIPS 180-2 §4.1.1 / §4.1.2 — shared with SHA-2) -/

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)` (FIPS 180-2 §4.1.1, §4.1.2).
    Generic over `UScalar ty`; shared by SHA-1 and SHA-2. -/
def ch {ty : UScalarTy} (x y z : UScalar ty) : UScalar ty :=
  (x &&& y) ^^^ ((~~~ x) &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` (FIPS 180-2 §4.1.1,
    §4.1.2).  Generic over `UScalar ty`; shared by SHA-1 and SHA-2. -/
def maj {ty : UScalarTy} (x y z : UScalar ty) : UScalar ty :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Parity(x, y, z) = x ⊕ y ⊕ z` (FIPS 180-2 §4.1.1).  Used by SHA-1 in the
    second and fourth round bands. -/
def parity {ty : UScalarTy} (x y z : UScalar ty) : UScalar ty :=
  x ^^^ y ^^^ z

/-! ## Generic schedule-extension helper -/

/-- Extend a word list `ws` to length `n` by repeatedly appending `f ws`
    (the next schedule word, computed from the current prefix).

    This is the common skeleton of the SHA-1 / SHA-256 / SHA-512 message
    schedules: each new word `W_t` is a function of the already-computed
    words `W_0 … W_{t-1}`. -/
def extendTo {α : Type*} (f : List α → α) (n : Nat) (ws : List α) : List α :=
  if ws.length < n then extendTo f n (ws ++ [f ws]) else ws
termination_by n - ws.length
decreasing_by
  rename_i h
  rw [List.length_append, List.length_singleton]
  omega

/-- **Spec lemma (`extendTo_length`)**: when the seed already has length at
    most `n`, the extended list has length exactly `n`. -/
theorem extendTo_length {α : Type*} (f : List α → α) (n : Nat) (ws : List α)
    (h : ws.length ≤ n) : (extendTo f n ws).length = n := by
  rw [extendTo]
  split
  · rename_i hlt
    exact extendTo_length f n (ws ++ [f ws]) (by
      rw [List.length_append, List.length_singleton]; omega)
  · rename_i hge
    omega
termination_by n - ws.length
decreasing_by
  rw [List.length_append, List.length_singleton]
  omega

/-- **Spec lemma (`foldl_const_length`)**: a left fold whose step function
    always returns a list of length `n` produces a result of length `n`,
    provided the list folded over is non-empty (so the final step fixes the
    length). -/
theorem foldl_const_length {α γ : Type*} (g : List γ → α → List γ) (n : Nat)
    (hg : ∀ s x, (g s x).length = n) :
    ∀ (l : List α), l ≠ [] → ∀ (st : List γ), (l.foldl g st).length = n := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton xs x _ =>
    intro _ st
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact hg _ x

/-- The range `[0, 80)` is non-empty (used for the SHA-1 compression fold). -/
theorem sha1_range_ne : (List.range 80) ≠ [] := by
  intro h
  have := congrArg List.length h
  simp only [List.length_range, List.length_nil] at this
  omega


/-! ## SHA-1 round-band selector `f_t` (FIPS 180-2 §4.1.1) -/

/-- The SHA-1 round function `f_t(x, y, z)`, selected by the round index `t`
    (FIPS 180-2 §4.1.1). -/
def sha1F (t : Nat) (x y z : U32) : U32 :=
  if t < 20 then ch x y z
  else if t < 40 then parity x y z
  else if t < 60 then maj x y z
  else parity x y z

/-- **Spec lemma (`sha1F_range0`)**: `f_t = Ch` for `0 ≤ t < 20`. -/
theorem sha1F_range0 {t : Nat} (h : t < 20) (x y z : U32) :
    sha1F t x y z = ch x y z := by simp [sha1F, h]

/-- **Spec lemma (`sha1F_range1`)**: `f_t = Parity` for `20 ≤ t < 40`. -/
theorem sha1F_range1 {t : Nat} (h0 : 20 ≤ t) (h1 : t < 40) (x y z : U32) :
    sha1F t x y z = parity x y z := by
  simp only [sha1F]
  rw [if_neg (by omega), if_pos (by omega)]

/-- **Spec lemma (`sha1F_range2`)**: `f_t = Maj` for `40 ≤ t < 60`. -/
theorem sha1F_range2 {t : Nat} (h0 : 40 ≤ t) (h1 : t < 60) (x y z : U32) :
    sha1F t x y z = maj x y z := by
  simp only [sha1F]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

/-- **Spec lemma (`sha1F_range3`)**: `f_t = Parity` for `60 ≤ t < 80`. -/
theorem sha1F_range3 {t : Nat} (h0 : 60 ≤ t) (x y z : U32) :
    sha1F t x y z = parity x y z := by
  simp only [sha1F]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ## SHA-1 message schedule (FIPS 180-2 §6.1.2) -/

/-- The SHA-1 schedule recurrence: given the prefix `W_0 … W_{t-1}`, compute
    `W_t = ROTL¹(W_{t-3} ⊕ W_{t-8} ⊕ W_{t-14} ⊕ W_{t-16})`
    (FIPS 180-2 §6.1.2). -/
def sha1Next (ws : List U32) : U32 :=
  let n := ws.length
  rotl 1#u32 (((ws[n-3]! ^^^ ws[n-8]!) ^^^ ws[n-14]!) ^^^ ws[n-16]!)

/-- The 80-word SHA-1 message schedule, extending a 16-word block via the
    `sha1Next` recurrence (FIPS 180-2 §6.1.2). -/
def sha1Schedule (block : List U32) : List U32 :=
  extendTo sha1Next 80 block

/-- **Spec lemma (`sha1Schedule_length`, SL12)**: from a 16-word block the
    schedule has exactly 80 words. -/
theorem sha1Schedule_length (block : List U32) (h : block.length = 16) :
    (sha1Schedule block).length = 80 := by
  unfold sha1Schedule
  exact extendTo_length sha1Next 80 block (by omega)

/-! ## SHA-1 compression (FIPS 180-2 §6.1.2) -/

/-- One round of the SHA-1 compression loop with working variables
    `st = [a, b, c, d, e]`, round index `t`, and schedule word `wt`
    (FIPS 180-2 §6.1.2):

    ```
    T = ROTL⁵(a) +ʷ f_t(b, c, d) +ʷ e +ʷ K_t +ʷ wt
    (a, b, c, d, e) ← (T, a, ROTL³⁰(b), c, d)
    ``` -/
def sha1RoundStep (t : Nat) (wt : U32) (st : List U32) : List U32 :=
  let a := st[0]!
  let b := st[1]!
  let c := st[2]!
  let d := st[3]!
  let e := st[4]!
  let temp :=
    wadd (wadd (wadd (wadd (rotl 5#u32 a) (sha1F t b c d)) e) (sha1K t)) wt
  [temp, a, rotl 30#u32 b, c, d]

/-- **Spec lemma (`sha1RoundStep_length`, SL12)**: a round always yields a
    5-word state. -/
@[simp]
theorem sha1RoundStep_length (t : Nat) (wt : U32) (st : List U32) :
    (sha1RoundStep t wt st).length = 5 := by
  simp [sha1RoundStep]

/-- SHA-1 single-block compression from a *precomputed* schedule `w`:
    run the 80 rounds, then add (wordwise, mod 2³²) the result back into the
    input state `st` (FIPS 180-2 §6.1.2). -/
def sha1CompressW (st w : List U32) : List U32 :=
  List.zipWith wadd st
    ((List.range 80).foldl (fun acc t => sha1RoundStep t w[t]! acc) st)

/-- **Spec lemma (`sha1CompressW_length`, SL12)**: compression preserves the
    5-word state. -/
theorem sha1CompressW_length (st w : List U32) (h : st.length = 5) :
    (sha1CompressW st w).length = 5 := by
  unfold sha1CompressW
  rw [List.length_zipWith,
      foldl_const_length _ 5 (fun s x => sha1RoundStep_length x (w[x]!) s)
        (List.range 80) sha1_range_ne st, h]
  exact Nat.min_self 5

/-- SHA-1 single-block compression: parse the schedule from `block`, then run
    `sha1CompressW` (FIPS 180-2 §6.1.2). -/
def sha1Compress (st block : List U32) : List U32 :=
  sha1CompressW st (sha1Schedule block)

/-- **Spec lemma (`sha1Compress_length`, SL12)**: compression preserves the
    5-word state. -/
theorem sha1Compress_length (st block : List U32) (h : st.length = 5) :
    (sha1Compress st block).length = 5 := by
  unfold sha1Compress
  exact sha1CompressW_length st (sha1Schedule block) h

end spec.sha
