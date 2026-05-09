/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Bits

/-! # GF(2)[X] Polynomial Library

Consolidated definitions, lemmas, and theorems about the function
`natToGF2Poly : Nat → GF2Poly` (which interprets a natural number's
binary representation as the coefficient vector of a polynomial over
GF(2)) and about the irreducible polynomial
`POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1` used to model `GF(2¹⁶)` as
`GF2Poly / (POLY_GF2)`.

Conventions:
- XOR (`^^^`) on `Nat` corresponds to polynomial addition (`+`) over GF(2).
- Shift-left (`<<< n`) corresponds to multiplication by `X ^ n`.
- `Nat.testBit n` corresponds to checking whether the n-th coefficient
  is non-zero.
-/

open Aeneas Aeneas.Std Result
open Polynomial

abbrev GF2Poly := (ZMod 2)[X]
abbrev GF216 := GaloisField 2 16


namespace spqr.encoding.gf


/-! ## Constants -/

/-! ## Core definitions -/

/-- Convert a natural number to a GF(2) polynomial by interpreting
its binary representation as polynomial coefficients.

For example, `natToGF2Poly 0b1011 = X³ + X + 1` since bits 0, 1,
and 3 are set. -/
noncomputable def natToGF2Poly (n : ℕ) : (ZMod 2)[X] :=
  (n.bitIndices.map (X ^ ·)).sum

/-- The irreducible polynomial used for GF(2¹⁶) reduction:
    POLY = X¹⁶ + X¹² + X³ + X + 1   (0x1100b in hex).

    GF(2¹⁶) ≅ GF(2)[X] / (POLY). -/
noncomputable def POLY_GF2 : GF2Poly :=
  X ^ 16 + X ^ 12 + X ^ 3 + X + 1

/-! ## Helper lemma relating `bitIndices` to `testBit` -/

/-- Membership in `n.bitIndices` is equivalent to `n.testBit m = true`. -/
private lemma mem_bitIndices_iff_testBit {n m : ℕ} :
    m ∈ n.bitIndices ↔ n.testBit m = true := by
  induction n using Nat.binaryRec generalizing m with
  | zero => simp
  | bit b n ih =>
    cases m with
    | zero =>
      cases b
      · -- 0 ∉ (bitIndices n).map (· + 1) since ·+1 ≥ 1
        rw [Nat.bitIndices_bit_false, Nat.testBit_bit_zero]
        simp only [Bool.false_eq_true, iff_false]
        intro h; rw [List.mem_map] at h; obtain ⟨_, _, h⟩ := h; omega
      · rw [Nat.bitIndices_bit_true, Nat.testBit_bit_zero]
        simp
    | succ m =>
      cases b
      · rw [Nat.bitIndices_bit_false, Nat.testBit_bit_succ]
        simp only [List.mem_map]
        exact ⟨fun ⟨a, ha, h⟩ => (Nat.succ_injective h) ▸ ih.mp ha,
               fun h => ⟨m, ih.mpr h, rfl⟩⟩
      · rw [Nat.bitIndices_bit_true, Nat.testBit_bit_succ]
        simp only [List.mem_cons, List.mem_map]
        constructor
        · rintro (heq | ⟨a, ha, heq⟩)
          · omega
          · exact (Nat.succ_injective heq) ▸ ih.mp ha
        · intro h; exact Or.inr ⟨m, ih.mpr h, rfl⟩

/-- Helper: for a `Nodup` list, mapping `if a = · then 1 else 0` and summing
gives 1 when `a` is in the list. -/
private lemma list_sum_ite_eq_one_of_mem {l : List ℕ} {a : ℕ}
    (hmem : a ∈ l) (hnd : l.Nodup) :
    (l.map (fun x => if a = x then (1 : ZMod 2) else 0)).sum = 1 := by
  induction l with
  | nil => simp at hmem
  | cons b t iht =>
    simp only [List.map_cons, List.sum_cons]
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · simp only [↓reduceIte]
      suffices h : (t.map (fun x => if a = x then (1 : ZMod 2) else 0)).sum = 0 by
        rw [h]; ring
      exact List.sum_eq_zero (fun x hx => by
        simp only [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simp [show a ≠ y from fun h => hnd.1 (h ▸ hy)])
    · have hab : a ≠ b := fun h => hnd.1 (h ▸ hmem')
      simp only [hab, ↓reduceIte, zero_add]
      exact iht hmem' hnd.2

/-! ## Coefficient characterization and basic lemmas of `natToGF2Poly` -/

/-- The coefficient of `natToGF2Poly n` at position `m` is `1` when bit `m`
of `n` is set, and `0` otherwise. -/
lemma natToGF2Poly_coeff (n : Nat) (m : Nat) :
    (natToGF2Poly n).coeff m = if n.testBit m then (1 : ZMod 2) else 0 := by
  unfold natToGF2Poly
  -- Distribute coeff over the list sum using lcoeff as an AddMonoidHom
  have hdist : (n.bitIndices.map (X ^ ·)).sum.coeff m =
      ((n.bitIndices.map (X ^ ·)).map (fun p => p.coeff m)).sum :=
    map_list_sum (Polynomial.lcoeff (ZMod 2) m) _
  rw [hdist, List.map_map]
  simp only [Function.comp_def, coeff_X_pow]
  -- Goal: (n.bitIndices.map (fun i => if m = i then 1 else 0)).sum = ...
  by_cases hm : n.testBit m = true
  · simp only [hm, ↓reduceIte]
    exact list_sum_ite_eq_one_of_mem
      (mem_bitIndices_iff_testBit.mpr hm) Nat.bitIndices_nodup
  · push_neg at hm
    simp only [hm, ↓reduceIte, Bool.false_eq_true]
    exact List.sum_eq_zero (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have hmi : m ≠ i := fun h => by
        subst h; exact absurd (mem_bitIndices_iff_testBit.mp hi) (by simp [hm])
      simp [hmi])

/-- `natToGF2Poly 0 = 0`. -/
lemma natToGF2Poly_zero : natToGF2Poly 0 = 0 := by
  ext m; simp [natToGF2Poly_coeff]

/-- XOR of natural numbers corresponds to addition of GF(2) polynomials. -/
lemma natToGF2Poly_xor (a b : Nat) :
    natToGF2Poly (a ^^^ b) = natToGF2Poly a + natToGF2Poly b := by
  ext m
  simp only [natToGF2Poly_coeff, coeff_add, Nat.testBit_xor]
  cases a.testBit m <;> cases b.testBit m <;> decide

/-- Left-shift on naturals corresponds to multiplication by `X ^ k` over GF(2). -/
lemma natToGF2Poly_shiftLeft (a k : Nat) :
    natToGF2Poly (a <<< k) = natToGF2Poly a * X ^ k := by
  ext m
  simp only [natToGF2Poly_coeff, coeff_mul_X_pow', Nat.testBit_shiftLeft,
    Bool.and_eq_true, decide_eq_true_eq]
  by_cases hkm : k ≤ m <;> simp [hkm]

/-- The natural-number encoding of the irreducible polynomial
    POLY = 0x1100b corresponds to `POLY_GF2` in GF(2)[X]:

    `natToGF2Poly 0x1100b = X¹⁶ + X¹² + X³ + X + 1 = POLY_GF2`. -/
lemma natToGF2Poly_POLY :
    natToGF2Poly 0x1100b = POLY_GF2 := by
  ext m
  simp only [natToGF2Poly_coeff]
  unfold POLY_GF2
  simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  rcases Nat.lt_or_ge m 17 with hlt | hge
  · interval_cases m <;> decide
  · have htb : Nat.testBit (0x1100b : Nat) m = false := by
      apply Nat.testBit_eq_false_of_lt
      exact lt_of_lt_of_le (by norm_num : (0x1100b : Nat) < 2 ^ 17)
        (Nat.pow_le_pow_right (by norm_num) hge)
    simp only [htb, ↓reduceIte, show m ≠ 16 from by omega, show m ≠ 12 from by omega,
               show m ≠ 3 from by omega, show (1 : ℕ) ≠ m from by omega, show m ≠ 0 from by omega,
               add_zero]
    simp

/-- **Natural-number polynomial decomposition at an arbitrary bit boundary.**

For any natural number `v` and bit position `n`:

  `natToGF2Poly v = natToGF2Poly (v % 2^n) + natToGF2Poly (v >>> n) * X^n`

This decomposes a GF(2) polynomial into its lower `n` coefficients
and its upper coefficients shifted down. -/
theorem natToGF2Poly_split (v n : Nat) :
    natToGF2Poly v =
      natToGF2Poly (v % 2 ^ n) + natToGF2Poly (v >>> n) * X ^ n := by
  ext m
  simp only [natToGF2Poly_coeff, coeff_add, coeff_mul_X_pow',
             Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hm : n ≤ m
  · simp only [hm, ↓reduceIte, show ¬ m < n from by omega]
    grind
  · push_neg at hm
    simp only [show ¬ n ≤ m from by omega, ↓reduceIte, hm, ↓reduceIte, add_zero]
    congr 1

/-- **Injectivity of `natToGF2Poly` on naturals.**

If two natural numbers map to the same GF(2) polynomial, they are equal.
This is because the coefficient of `natToGF2Poly n` at position `m` is
`1` iff bit `m` of `n` is set, so equal polynomials force equal bit
patterns. -/
lemma natToGF2Poly_inj (a b : Nat)
    (h : natToGF2Poly a = natToGF2Poly b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro m
  have hcoeff : (natToGF2Poly a).coeff m = (natToGF2Poly b).coeff m :=
    congrArg (fun p => p.coeff m) h
  simp only [natToGF2Poly_coeff] at hcoeff
  by_cases ha : a.testBit m
  · by_cases hb : b.testBit m
    · exact ha.trans hb.symm
    · simp [ha, hb] at hcoeff
  · by_cases hb : b.testBit m
    · simp [ha, hb] at hcoeff
    · exact (Bool.eq_false_iff.mpr ha).trans (Bool.eq_false_iff.mpr hb).symm

/-! ## Properties of `POLY_GF2` -/

/-- **`POLY_GF2` is monic** (leading coefficient is 1). -/
theorem POLY_GF2_monic : POLY_GF2.Monic := by
  unfold POLY_GF2 Polynomial.Monic Polynomial.leadingCoeff
  have hnd : (X ^ 16 + X ^ 12 + X ^ 3 + X + (1 : GF2Poly)).natDegree = 16 := by
    compute_degree!
  rw [hnd]
  simp [coeff_add, coeff_X_pow, coeff_X, coeff_one]

/-- **`POLY_GF2` has degree 16.** -/
theorem POLY_GF2_natDegree : POLY_GF2.natDegree = 16 := by
  unfold POLY_GF2; compute_degree!

/-- **`POLY_GF2 ≠ 1`** (its degree is 16, not 0). -/
theorem POLY_GF2_ne_one : POLY_GF2 ≠ 1 := by
  intro h; have := congr_arg Polynomial.natDegree h
  simp [POLY_GF2_natDegree] at this

/-! ### Computable GF(2) polynomial arithmetic for irreducibility verification -/

/-- One step of GF(2) polynomial long-division: if the leading term of `a`
    can be cancelled by a shift of `b`, XOR to cancel it. -/
private def gf2ModAux (b : Nat) : Nat → Nat → Nat
  | a, 0       => a
  | a, fuel + 1 =>
    if b ≤ 1 then (if b = 1 then 0 else a)
    else if a.log2 < b.log2 then a
    else gf2ModAux b (a ^^^ (b <<< (a.log2 - b.log2))) fuel

/-- GF(2) polynomial remainder: `gf2Mod a b` computes `a mod b` where
    `a` and `b` are natural-number encodings of GF(2) polynomials. -/
private def gf2Mod (a b : Nat) : Nat := gf2ModAux b a (a + 1)

/-- Check that no monic GF(2) polynomial of degree `d` divides `n`. -/
private def gf2NoDivisorOfDeg (n d : Nat) : Bool :=
  (List.range (2 ^ d)).all fun lower => gf2Mod n (2 ^ d + lower) != 0

/-! ## Characteristic-2 facts in `GF2Poly` -/

/-- **In `GF2Poly`, every element is its own negation.**

This is a consequence of characteristic 2: `a + a = 0` implies `-a = a`. -/
lemma zmod2_poly_neg_eq (a : GF2Poly) : -a = a := by
  have h : a + a = 0 := by
    ext n; simp only [coeff_add, coeff_zero]
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc (a.coeff n) + (a.coeff n) = 2 * (a.coeff n) := by ring
      _ = 0 * (a.coeff n) := by rw [h2]
      _ = 0 := by ring
  exact neg_eq_of_add_eq_zero_left h

/-- **In `GF2Poly`, subtraction equals addition.**

Direct consequence of `zmod2_poly_neg_eq`: `a - b = a + (-b) = a + b`. -/
lemma zmod2_poly_sub_eq_add (a b : GF2Poly) : a - b = a + b := by
  rw [sub_eq_add_neg, zmod2_poly_neg_eq]

/-! #### Linking lemmas -/

/-- Each step of `gf2ModAux` preserves the congruence class modulo
    `natToGF2Poly b`: the difference `natToGF2Poly a - natToGF2Poly result`
    is divisible by `natToGF2Poly b`. -/
private lemma gf2ModAux_preserves_dvd (b a fuel : Nat) (hb : b ≥ 2) :
    natToGF2Poly b ∣ natToGF2Poly a - natToGF2Poly (gf2ModAux b a fuel) := by
  induction fuel generalizing a with
  | zero => simp [gf2ModAux, sub_self]
  | succ n ih =>
    simp only [gf2ModAux, show ¬(b ≤ 1) from by omega, ↓reduceIte]
    split
    · -- a.log2 < b.log2 → result = a
      simp [sub_self]
    · -- recursive case
      rename_i hlog
      push_neg at hlog
      set shift := a.log2 - b.log2
      set a' := a ^^^ (b <<< shift)
      -- One step: natToGF2Poly a - natToGF2Poly a' = natToGF2Poly b * X ^ shift
      have hstep : natToGF2Poly a - natToGF2Poly a' =
          natToGF2Poly b * X ^ shift := by
        have h1 : natToGF2Poly a' = natToGF2Poly a + natToGF2Poly b * X ^ shift := by
          change natToGF2Poly (a ^^^ (b <<< shift)) = _
          rw [natToGF2Poly_xor, natToGF2Poly_shiftLeft]
        have haa : ∀ (p : GF2Poly), p + p = 0 := fun p =>
          (zmod2_poly_sub_eq_add p p).symm.trans (sub_self p)
        calc natToGF2Poly a - natToGF2Poly a'
            = natToGF2Poly a + natToGF2Poly a' := zmod2_poly_sub_eq_add ..
          _ = natToGF2Poly a + (natToGF2Poly a + natToGF2Poly b * X ^ shift) := by rw [h1]
          _ = (natToGF2Poly a + natToGF2Poly a) + natToGF2Poly b * X ^ shift := by ring
          _ = 0 + natToGF2Poly b * X ^ shift := by rw [haa]
          _ = natToGF2Poly b * X ^ shift := by ring
      -- Telescope: a - result = (a - a') + (a' - result)
      have ih' := ih a'
      have htelescope : natToGF2Poly a - natToGF2Poly (gf2ModAux b a' n) =
          (natToGF2Poly a - natToGF2Poly a') +
          (natToGF2Poly a' - natToGF2Poly (gf2ModAux b a' n)) := by ring
      rw [htelescope, hstep]
      exact dvd_add (dvd_mul_right _ _) ih'



/-- The degree of the result of `gf2ModAux` (with sufficient fuel) is
    strictly less than the degree of the divisor. -/
private lemma gf2ModAux_log2_lt (b a fuel : Nat) (hb : b ≥ 2)
    (hfuel : a.log2 + 1 ≤ b.log2 + fuel) :
    gf2ModAux b a fuel = 0 ∨ (gf2ModAux b a fuel).log2 < b.log2 := by
  induction fuel generalizing a with
  | zero =>
    simp [gf2ModAux]
    omega
  | succ n ih =>
    simp only [gf2ModAux, show ¬(b ≤ 1) from by omega, ↓reduceIte]
    split
    · -- a.log2 < b.log2 → result is a
      rename_i hlt
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · left
        rfl
      · right
        exact hlt
    · -- recursive step
      rename_i hlog
      push_neg at hlog
      set shift := a.log2 - b.log2
      set a' := a ^^^ (b <<< shift)
      -- After XOR, the highest bit of a is cleared, so a'.log2 < a.log2
      have ha_pos : a ≥ 2 := by
        have hb_log2 : 1 ≤ b.log2 := (Nat.le_log2 (by omega)).mpr (by omega)
        have h1 : 1 ≤ a.log2 := le_trans hb_log2 hlog
        have ha_ne : a ≠ 0 := by
          intro heq
          subst heq
          simp [Nat.log2_zero] at h1
        exact (Nat.le_log2 ha_ne).mp h1
      have hlog2_lt : a'.log2 < a.log2 := by
        by_cases ha'_zero : a' = 0
        · simp [ha'_zero, Nat.log2_zero]
          have : 1 ≤ a.log2 := (Nat.le_log2 (by omega)).mpr (by omega)
          omega
        · rw [Nat.log2_lt ha'_zero]
          -- Goal: a' < 2 ^ a.log2  (XOR clears the top bit)
          apply Nat.lt_of_testBit a.log2
          · -- (a').testBit a.log2 = false (XOR of two set bits)
            change (a ^^^ (b <<< shift)).testBit a.log2 = false
            rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
            have h1 : a.testBit a.log2 = true := Nat.testBit_log2 (by omega)
            have h2 : decide (shift ≤ a.log2) = true := decide_eq_true_eq.mpr (by omega)
            have h3 : a.log2 - shift = b.log2 := by omega
            have h4 : b.testBit b.log2 = true := Nat.testBit_log2 (by omega)
            simp [h1, h2, h3, h4]
          · rw [← Nat.one_shiftLeft, Nat.testBit_shiftLeft]
            simp
          · intro j hj
            change (a ^^^ (b <<< shift)).testBit j = (2 ^ a.log2).testBit j
            rw [Nat.testBit_xor, Nat.testBit_shiftLeft,
                ← Nat.one_shiftLeft, Nat.testBit_shiftLeft]
            have haj : a.testBit j = false :=
              Nat.testBit_eq_false_of_lt ((Nat.log2_lt (show a ≠ 0 by omega)).mp (by omega))
            have hbsj : b.testBit (j - shift) = false :=
              Nat.testBit_eq_false_of_lt ((Nat.log2_lt (show b ≠ 0 by omega)).mp (by omega))
            have h1j : (1 : Nat).testBit (j - a.log2) = false :=
              Nat.testBit_eq_false_of_lt (Nat.one_lt_pow (by omega) (by norm_num))
            simp [haj, show shift ≤ j from by omega, hbsj,
                  show a.log2 ≤ j from by omega, h1j]
      apply ih
      omega

/-- For `b ≥ 2`, `natToGF2Poly b` has `natDegree = b.log2`. -/
private lemma natToGF2Poly_natDegree_eq_log2 (b : Nat) (hb : b ≥ 2) :
    (natToGF2Poly b).natDegree = b.log2 := by
  have hb_ne : b ≠ 0 := by omega
  apply le_antisymm
  · apply Polynomial.natDegree_le_of_degree_le
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro m hm
    rw [natToGF2Poly_coeff]
    have hm' : b.log2 < m := by exact_mod_cast hm
    simp [Nat.testBit_eq_false_of_lt ((Nat.log2_lt hb_ne).mp hm')]
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [natToGF2Poly_coeff]
    simp [Nat.testBit_log2 hb_ne]

/-- A natural number `b ≥ 2` encodes a monic GF(2) polynomial. -/
private lemma natToGF2Poly_monic_of_ge_two (b : Nat) (hb : b ≥ 2) :
    (natToGF2Poly b).Monic := by
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rw [natToGF2Poly_natDegree_eq_log2 b hb, natToGF2Poly_coeff]
  simp [Nat.testBit_log2 (show b ≠ 0 by omega)]

/-- If `gf2Mod a b ≠ 0` and `b ≥ 2`, then `natToGF2Poly b` does not
    divide `natToGF2Poly a`. -/
private lemma gf2Mod_ne_zero_of_not_dvd (a b : Nat) (hb : b ≥ 2)
    (hmod : gf2Mod a b ≠ 0) : ¬ (natToGF2Poly b ∣ natToGF2Poly a) := by
  intro ⟨q, hq⟩
  set r := gf2Mod a b with hr_def
  have hdvd_diff := gf2ModAux_preserves_dvd b a (a + 1) hb
  have hdvd_r : natToGF2Poly b ∣ natToGF2Poly r := by
    have : natToGF2Poly b ∣ natToGF2Poly a := ⟨q, hq⟩
    have : natToGF2Poly b ∣ natToGF2Poly a - natToGF2Poly r := hdvd_diff
    exact (dvd_add_right this).mp ⟨q, by rw [hq]; ring⟩
  obtain ⟨s, hs⟩ := hdvd_r
  have hr_ne : natToGF2Poly r ≠ 0 := by
    intro h
    have := natToGF2Poly_inj r 0 (by rw [h, natToGF2Poly_zero])
    exact hmod this
  have hs_ne : s ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hs
    exact hr_ne hs
  have hmonic_b : (natToGF2Poly b).Monic := natToGF2Poly_monic_of_ge_two b hb
  have hdeg : (natToGF2Poly b * s).natDegree = (natToGF2Poly b).natDegree + s.natDegree :=
    hmonic_b.natDegree_mul' hs_ne
  have hdeg_b : (natToGF2Poly b).natDegree = b.log2 :=
    natToGF2Poly_natDegree_eq_log2 b hb
  have hlower : b.log2 ≤ (natToGF2Poly r).natDegree := by
    rw [hs, hdeg, hdeg_b]
    omega
  have hupper : (natToGF2Poly r).natDegree ≤ r.log2 := by
    apply Polynomial.natDegree_le_of_degree_le
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro m hm
    rw [natToGF2Poly_coeff]
    have hm' : r.log2 < m := by exact_mod_cast hm
    simp [Nat.testBit_eq_false_of_lt ((Nat.log2_lt hmod).mp hm')]
  have hlog2_lt : r.log2 < b.log2 := by
    have hfuel : a.log2 + 1 ≤ b.log2 + (a + 1) := by
      have hb_log2 : 1 ≤ b.log2 := (Nat.le_log2 (by omega)).mpr (by omega)
      suffices a.log2 ≤ a by omega
      rcases Nat.eq_zero_or_pos a with rfl | ha_pos
      · simp
      · suffices a < 2 ^ (a + 1) by
          have := (Nat.log2_lt (by omega)).mpr this
          omega
        suffices ∀ n : Nat, n < 2 ^ (n + 1) from this a
        intro n
        induction n with
        | zero => norm_num
        | succ k ih =>
          calc k + 1 ≤ 2 ^ (k + 1) := ih
            _ < 2 ^ (k + 1) + 2 ^ (k + 1) :=
              lt_add_of_pos_right _ (pos_of_gt ih)
            _ = 2 ^ (k + 2) := by ring
    have hbound := gf2ModAux_log2_lt b a (a + 1) hb hfuel
    change r = 0 ∨ r.log2 < b.log2 at hbound
    rcases hbound with h | h
    · exact absurd h hmod
    · exact h
  omega

/-- `natToGF2Poly 1 = 1` as a GF(2) polynomial. -/
lemma natToGF2Poly_one : natToGF2Poly 1 = 1 := by
  ext m; simp only [natToGF2Poly_coeff, coeff_one]
  cases m with
  | zero => decide
  | succ n =>
    have htb : Nat.testBit 1 (n + 1) = false :=
      Nat.testBit_eq_false_of_lt (Nat.one_lt_pow (by omega) (by norm_num))
    simp [htb]

/-- `natToGF2Poly (2^k) = X^k` as a GF(2) polynomial. -/
private lemma natToGF2Poly_pow2 (k : Nat) : natToGF2Poly (2 ^ k) = X ^ k := by
  rw [show (2 : Nat) ^ k = 1 <<< k from (Nat.one_shiftLeft k).symm,
      natToGF2Poly_shiftLeft, natToGF2Poly_one, one_mul]

/-- Every polynomial over GF(2) is in the range of `natToGF2Poly`. -/
private lemma natToGF2Poly_surj (q : GF2Poly) : ∃ n, natToGF2Poly n = q := by
  induction q using Polynomial.induction_on' with
  | add p r ih_p ih_r =>
    obtain ⟨np, rfl⟩ := ih_p
    obtain ⟨nr, rfl⟩ := ih_r
    exact ⟨np ^^^ nr, natToGF2Poly_xor np nr⟩
  | monomial n a =>
    fin_cases a
    · exact ⟨0, by simp [natToGF2Poly_zero]⟩
    · refine ⟨2 ^ n, ?_⟩
      rw [natToGF2Poly_pow2]
      simp [X_pow_eq_monomial]

/-- If `q` is monic with `1 ≤ q.natDegree`, then `q = natToGF2Poly b`
    for some `b ≥ 2`. -/
private lemma monic_eq_natToGF2Poly (q : GF2Poly)
    (hd : 1 ≤ q.natDegree) : ∃ b, b ≥ 2 ∧ natToGF2Poly b = q := by
  obtain ⟨n, hn⟩ := natToGF2Poly_surj q
  refine ⟨n, ?_, hn⟩
  by_contra h
  push_neg at h
  interval_cases n
  · simp only [natToGF2Poly_zero] at hn
    rw [← hn] at hd
    simp at hd
  · rw [← hn] at hd; simp [natToGF2Poly_one] at hd

/-- Computational check that no monic polynomial of degree `d` (1 ≤ d ≤ 8)
    divides `0x1100b`, proved for each degree by `native_decide`. -/
private lemma gf2NoDivisorOfDeg_POLY (d : Nat) (hd : 1 ≤ d) (hd8 : d ≤ 8) :
    gf2NoDivisorOfDeg 0x1100b d = true := by
  interval_cases d <;> decide

/-- For all `lower < 2^d`, `gf2Mod 0x1100b (2^d + lower) ≠ 0`,
    extracted from `gf2NoDivisorOfDeg_POLY`. -/
private lemma gf2_no_divisor_all (d : Nat) (hd : 1 ≤ d) (hd8 : d ≤ 8)
    (lower : Nat) (hlower : lower < 2 ^ d) :
    gf2Mod 0x1100b (2 ^ d + lower) ≠ 0 := by
  have hstep := gf2NoDivisorOfDeg_POLY d hd hd8
  simp only [gf2NoDivisorOfDeg, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hstep
  exact hstep lower hlower

/-- **`POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1` is irreducible over `GF(2) = ZMod 2`.**

The proof proceeds by computational verification: we implement a GF(2)
polynomial remainder function via XOR bit-manipulation on natural numbers,
check that no monic polynomial of degree 1 through 8 divides `0x1100b`
(the bit-encoding of `POLY_GF2`), and link this computation back to the
algebraic statement using `natToGF2Poly` and
`Monic.irreducible_iff_lt_natDegree_lt`. -/
theorem POLY_GF2_irreducible : Irreducible POLY_GF2 := by
  have hmonic := POLY_GF2_monic
  rw [hmonic.irreducible_iff_lt_natDegree_lt POLY_GF2_ne_one, POLY_GF2_natDegree]
  -- Goal: ∀ q, q.Monic → q.natDegree ∈ Finset.Ioc 0 8 → ¬ q ∣ POLY_GF2
  intro q hq_monic hq_deg hq_dvd
  simp only [Nat.reduceDiv, Finset.mem_Ioc] at hq_deg
  -- We know: 0 < q.natDegree ≤ 8, q is monic, q ∣ POLY_GF2
  -- Get the natural number encoding b ≥ 2 with natToGF2Poly b = q
  obtain ⟨b, hb_ge, hb_eq⟩ := monic_eq_natToGF2Poly q (by omega)
  -- q divides POLY_GF2 = natToGF2Poly 0x1100b
  rw [← hb_eq, ← natToGF2Poly_POLY] at hq_dvd
  -- b.log2 = q.natDegree, so 1 ≤ b.log2 ≤ 8
  have hlog_eq : b.log2 = q.natDegree := by
    rw [← natToGF2Poly_natDegree_eq_log2 b hb_ge, hb_eq]
  have hlog_pos : 1 ≤ b.log2 := by omega
  have hlog_le : b.log2 ≤ 8 := by omega
  -- Decompose b = 2^(b.log2) + (b - 2^(b.log2))
  set d := b.log2
  set lower := b - 2 ^ d
  have h2d_le_b : 2 ^ d ≤ b := Nat.log2_self_le (show b ≠ 0 by omega)
  have hb_decomp : b = 2 ^ d + lower := by omega
  have hb_lt_2d1 : b < 2 ^ (d + 1) :=
    (Nat.log2_lt (show b ≠ 0 by omega)).mp (by omega : b.log2 < b.log2 + 1)
  have h2d1_eq : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
  have hlower_lt : lower < 2 ^ d := by omega
  -- The computational check says gf2Mod 0x1100b b ≠ 0
  have hmod_ne : gf2Mod 0x1100b b ≠ 0 := by
    rw [hb_decomp]
    exact gf2_no_divisor_all d hlog_pos hlog_le lower hlower_lt
  -- Therefore natToGF2Poly b does not divide natToGF2Poly 0x1100b
  exact gf2Mod_ne_zero_of_not_dvd 0x1100b b hb_ge hmod_ne hq_dvd

/-! ## Modular-reduction utilities for `POLY_GF2` -/

/-- **`p %ₘ POLY_GF2 - p` is divisible by `POLY_GF2`.**

A direct consequence of the division identity
`p %ₘ POLY_GF2 + (p /ₘ POLY_GF2) * POLY_GF2 = p`. -/
lemma POLY_GF2_dvd_modByMonic_sub (p : GF2Poly) :
    POLY_GF2 ∣ (p %ₘ POLY_GF2 - p) := by
  have hadd := Polynomial.modByMonic_add_div p POLY_GF2_monic
  refine ⟨-(p /ₘ POLY_GF2), ?_⟩
  linear_combination hadd

/-- **Idempotence of `%ₘ POLY_GF2`**: applying the reduction twice is
the same as applying it once. -/
lemma modByMonic_modByMonic_self (p : GF2Poly) :
    (p %ₘ POLY_GF2) %ₘ POLY_GF2 = p %ₘ POLY_GF2 :=
  Polynomial.modByMonic_eq_of_dvd_sub POLY_GF2_monic
    (POLY_GF2_dvd_modByMonic_sub p)

/-- **Bridge lemma**: any monic polynomial `P` and ring-homomorphism `φ`
that vanishes at `P` makes the residue `p %ₘ P` φ-equal to `p` itself.

This is the standard "transport along the quotient map" identity:
if `φ : GF2Poly →+* R` factors through `GF2Poly ⧸ (P)` (i.e.
`φ P = 0`), then `φ p = φ (p %ₘ P)`.  Multiplying through by the
quotient identity `p = P * (p /ₘ P) + (p %ₘ P)`, the `P · q` term is
killed by `φ P = 0`.
-/
lemma ringHom_modByMonic
    {R : Type*} [CommRing R]
    (φ : GF2Poly →+* R)
    (P : GF2Poly) (hMonic : P.Monic) (hφ : φ P = 0)
    (p : GF2Poly) :
    φ (p %ₘ P) = φ p := by
  -- `modByMonic_add_div p hMonic : p %ₘ P + P * (p /ₘ P) = p`
  have heq : p %ₘ P + P * (p /ₘ P) = p :=
    Polynomial.modByMonic_add_div p hMonic
  have h1 : φ p = φ (p %ₘ P + P * (p /ₘ P)) := by rw [heq]
  have h2 :
      φ (p %ₘ P + P * (p /ₘ P)) = φ (p %ₘ P) + φ P * φ (p /ₘ P) := by
    simp [map_add, map_mul]
  rw [h1, h2, hφ]; ring

/-- **Multiplicativity of `%ₘ POLY_GF2` (compatibility with the quotient ring

multiplication).**

For any two natural numbers `p` and `q`, reducing the product of their
`natToGF2Poly` encodings modulo `POLY_GF2` is the same as first reducing
each factor modulo `POLY_GF2`, multiplying the residues, and reducing the
result again.  This is the algebraic statement that the quotient map
`GF2Poly → GF2Poly ⧸ (POLY_GF2)` is a ring homomorphism.

 **Existence of a ring homomorphism from `GF2Poly` to `GF216`
that vanishes on `POLY_GF2`.**

Concretely, since `POLY_GF2` is irreducible of degree `16` over `ZMod 2`,
the quotient `AdjoinRoot POLY_GF2 = GF2Poly ⧸ (POLY_GF2)` is a field
with `2 ^ 16` elements, hence (non-canonically) isomorphic — as a
`ZMod 2`-algebra — to `GF216 = GaloisField 2 16` via
`GaloisField.algEquivGaloisFieldOfFintype`.  Composing the canonical
quotient map `AdjoinRoot.mk POLY_GF2` with this isomorphism gives a
ring homomorphism `GF2Poly →+* GF216` which sends `POLY_GF2` to
`0` (because `AdjoinRoot.mk_self` says `AdjoinRoot.mk POLY_GF2 POLY_GF2 = 0`).
-/
lemma exists_ringHom_modByMonic :
    ∃ φ : GF2Poly →+* GF216,
      φ POLY_GF2 = 0 := by
  -- The quotient map `GF2Poly → GF2Poly ⧸ (P)` is a ring homomorphism that vanishes at `P`.
  classical
  have hmonic : POLY_GF2.Monic := POLY_GF2_monic
  have hne : POLY_GF2 ≠ 0 := hmonic.ne_zero
  -- POLY_GF2 = X^16 + X^12 + X^3 + X + 1 is irreducible over `ZMod 2`.
  have hirr : Irreducible POLY_GF2 := POLY_GF2_irreducible
  haveI : Fact (Irreducible POLY_GF2) := ⟨hirr⟩
  -- The power basis of `AdjoinRoot POLY_GF2` over `ZMod 2`.
  let pb := AdjoinRoot.powerBasis hne
  -- Hence `AdjoinRoot POLY_GF2` is a finite-dimensional `ZMod 2`-vector space.
  haveI : Module.Finite (ZMod 2) (AdjoinRoot POLY_GF2) := pb.finite
  haveI : Fintype (AdjoinRoot POLY_GF2) := Module.fintypeOfFintype pb.basis
  -- It has dimension `natDegree POLY_GF2 = 16`.
  have hdim : Module.finrank (ZMod 2) (AdjoinRoot POLY_GF2) = 16 := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim, POLY_GF2_natDegree]
  -- Hence its cardinality is `2 ^ 16`.
  have hcard : Fintype.card (AdjoinRoot POLY_GF2) = 2 ^ 16 := by
    rw [Module.card_fintype pb.basis, ZMod.card, Fintype.card_fin,
        AdjoinRoot.powerBasis_dim, POLY_GF2_natDegree]
  -- Identify `AdjoinRoot POLY_GF2` with `GF216`.
  let e : AdjoinRoot POLY_GF2 ≃ₐ[ZMod 2] GF216 :=
    GaloisField.algEquivGaloisFieldOfFintype 2 16 hcard
  -- The composite ring homomorphism.
  have hmk : (AdjoinRoot.mk POLY_GF2) POLY_GF2 = 0 := AdjoinRoot.mk_self
  refine ⟨(e : AdjoinRoot POLY_GF2 →+* GF216).comp (AdjoinRoot.mk POLY_GF2), ?_⟩
  rw [RingHom.comp_apply, hmk, map_zero]

/-- A chosen ring homomorphism `GF2Poly →+* GF216` that vanishes on
`POLY_GF2`.  We pick one provided by `exists_ringHom_modByMonic`. -/
noncomputable def φ : GF2Poly →+* GF216 :=
  Classical.choose exists_ringHom_modByMonic

/-- The chosen ring homomorphism `φ` sends `POLY_GF2` to `0`. -/
lemma hφ : φ POLY_GF2 = 0 :=
  Classical.choose_spec exists_ringHom_modByMonic

/-- Interpret a natural number as an element of `GF216 = GF(2¹⁶)`,
using the canonical chain
`Nat → GF2Poly → GF216`
where the first arrow is `natToGF2Poly` (binary expansion as a
GF(2)-polynomial) and the second arrow is the chosen ring homomorphism
`φ` (which factors through `GF2Poly / (POLY_GF2)`). -/
noncomputable def _root_.Nat.toGF216 (n : Nat) : GF216 :=
  φ (natToGF2Poly n)

/-- Convert a `GF16` element to its mathematical counterpart in `GF(2¹⁶)`.

A `GF16` stores a `Std.U16` value whose 16-bit representation encodes
a polynomial in GF(2)[X] modulo the irreducible polynomial
`POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1`.  We interpret the U16 value
as a natural number and map it through `Nat.toGF216` (defined in
`Spqr.Math.Gf`), which applies the canonical ring homomorphism
`φ : GF2Poly →+* GF216` to the GF(2)-polynomial encoding of the
natural number.

For example, `GF16toGF216 ⟨3⟩` (where `3 = 0b11`) maps to the
GF(2¹⁶) element corresponding to `X + 1`. -/
noncomputable def GF16toGF216 (g : GF16) : GF216 :=
  g.value.val.toGF216

end spqr.encoding.gf
