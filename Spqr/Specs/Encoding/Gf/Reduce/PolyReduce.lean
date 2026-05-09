/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.Reduce.ReduceBytes
/-! # Spec theorem for `spqr::encoding::gf::reduce::poly_reduce`

In GF(2¹⁶) — the Galois field with 65 536 elements — after
carry-less polynomial multiplication (`poly_mul`) produces a
32-bit unreduced product (degree ≤ 30), reduction modulo the
irreducible polynomial POLY is needed to obtain the canonical
16-bit representative.

The reduction proceeds in two byte-by-byte passes using the
precomputed table `REDUCE_BYTES`:
  1. Extract the high byte `i1 = v >> 24` and XOR
     `REDUCE_BYTES[i1] << 8` into `v`, clearing bits 24–31.
  2. Extract the next byte `i2 = (v >> 16) & 0xFF` and XOR
     `REDUCE_BYTES[i2]` into `v`, clearing bits 16–23.
  3. Return the low 16 bits of `v` as the reduced result.

Each `REDUCE_BYTES[k]` entry stores the precomputed 16-bit XOR
mask that results from reducing all set bits in byte `k` against
POLY.  This is equivalent to computing `(k · x¹⁶) mod POLY`
for the second pass, and `(k · x²⁴) mod POLY` (after appropriate
shifting) for the first pass.

**Source** "spqr/src/encoding/gf.rs" (lines 489:4-498:5)
-/

open Aeneas Aeneas.Std Result Polynomial spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.reduce

/-- Spec-level two-pass table-based polynomial reduction.

Given a 32-bit value `v`, reduces modulo POLY = 0x1100b via two
byte-level table lookups (processing from the high byte down)
and returns the low 16 bits as the canonical GF(2¹⁶) representative.

  1. Look up `reduceByteTable[v >>> 24]` and XOR it (shifted left by 8)
     into `v`, folding bits 24–31 into bits 8–23.
  2. Look up `reduceByteTable[(v' >>> 16) &&& 0xFF]` and XOR it into `v'`,
     folding bits 16–23 into bits 0–15.
  3. Return the low 16 bits.

This is the correct specification for `poly_reduce`, matching the
high-to-low byte processing order of the Rust implementation.
The result is the canonical fully-reduced representative (< 2¹⁶). -/
def polyReduceSpec (v : Nat) : Nat :=
  let t1 := reduceByteTable (v >>> 24)
  let v1 := v ^^^ (t1 <<< 8)
  let t2 := reduceByteTable ((v1 >>> 16) &&& 255)
  (v1 ^^^ t2) % 2 ^ 16

private lemma nat_and_255_lt_256 (n : Nat) : n &&& 255 < 256 := by
  apply Nat.lt_of_testBit 8
  · rw [Nat.testBit_and]
    have : Nat.testBit 255 8 = false :=
      Nat.testBit_eq_false_of_lt (by norm_num : 255 < 2 ^ 8)
    simp [this]
  · decide
  · intro j hj
    have h1 : Nat.testBit (n &&& 255) j = false := by
      rw [Nat.testBit_and]
      have : Nat.testBit 255 j = false :=
        Nat.testBit_eq_false_of_lt (calc (255 : Nat) < 2 ^ 8 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega))
      simp [this]
    have h2 : Nat.testBit 256 j = false := by
      apply Nat.testBit_eq_false_of_lt
      calc (256 : Nat) = 2 ^ 8 := by norm_num
        _ < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [h1, h2]

private lemma index_usize_ok_eq {α : Type _} [Inhabited α] {n : Std.Usize}
    (a : Array α n) (j : Std.Usize) (w : α)
    (h : a.index_usize j = ok w) :
    w = a.val[j.val]! := by
  simp only [Array.index_usize, Array.getElem?_Usize_eq] at h
  split at h <;> simp_all [List.getElem!_eq_getElem?_getD]

theorem xor_table_shift_dvd (k n : Nat)
    (htable : natToGF2Poly (reduceByteTable k) =
      (natToGF2Poly k * X ^ 16) %ₘ POLY_GF2) :
    POLY_GF2 ∣ (natToGF2Poly k * X ^ (n + 16) +
      natToGF2Poly (reduceByteTable k) * X ^ n) := by
  have hchar2 : natToGF2Poly k * X ^ (n + 16) +
      natToGF2Poly (reduceByteTable k) * X ^ n =
    (natToGF2Poly k * X ^ 16 - natToGF2Poly (reduceByteTable k)) * X ^ n := by
    rw [zmod2_poly_sub_eq_add]; ring
  rw [hchar2]
  apply dvd_mul_of_dvd_left
  rw [htable]
  set p := natToGF2Poly k * X ^ 16
  have h := Polynomial.modByMonic_add_div p POLY_GF2_monic
  refine ⟨p /ₘ POLY_GF2, ?_⟩
  grind

theorem polyReduceSpec_correct (v : Nat) (hv : v < 2 ^ 32)
    (htable : ∀ k, k < 256 → natToGF2Poly (reduceByteTable k) =
      (natToGF2Poly k * X ^ 16) %ₘ POLY_GF2) :
    natToGF2Poly (polyReduceSpec v) = (natToGF2Poly v) %ₘ POLY_GF2 := by
  have hk1_lt : v >>> 24 < 256 := by
    rw [Nat.shiftRight_eq_div_pow]
    have h2 : (0 : Nat) < 2 ^ 24 := by positivity
    rw [Nat.div_lt_iff_lt_mul h2]
    have h32 : (256 : Nat) * 2 ^ 24 = 2 ^ 32 := by norm_num
    omega
  have ht1_lt : reduceByteTable (v >>> 24) < 2 ^ 16 := by
    unfold reduceByteTable; exact Nat.mod_lt _ (by positivity)
  unfold polyReduceSpec
  set k1 := v >>> 24 with hk1_def
  set t1 := reduceByteTable k1 with ht1_def
  set v1 := v ^^^ (t1 <<< 8) with hv1_def
  set k2 := (v1 >>> 16) &&& 255 with hk2_def
  set t2 := reduceByteTable k2 with ht2_def
  have hk2_lt : k2 < 256 := nat_and_255_lt_256 _
  have ht2_lt : t2 < 2 ^ 16 := by
    rw [ht2_def]; unfold reduceByteTable; exact Nat.mod_lt _ (by positivity)
  have hhigh : (v1 ^^^ t2) >>> 16 = k2 ^^^ (k1 <<< 8) := by
    apply Nat.eq_of_testBit_eq
    intro i
    have ht2_high : ∀ j, 16 ≤ j → t2.testBit j = false := fun j hj =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le ht2_lt (Nat.pow_le_pow_right (by norm_num) hj))
    have ht1_high : ∀ j, 16 ≤ j → t1.testBit j = false := fun j hj =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le ht1_lt (Nat.pow_le_pow_right (by norm_num) hj))
    have hv_high : ∀ j, 32 ≤ j → v.testBit j = false := fun j hj =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hj))
    have hk1_high : ∀ j, 8 ≤ j → k1.testBit j = false := fun j hj =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hk1_lt
          (calc (256 : Nat) = 2 ^ 8 := by norm_num
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj))
    rw [hv1_def, hk2_def]
    simp only [Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_shiftLeft,
               Nat.testBit_and]
    rw [show 16 + i = i + 16 from by ring, ht2_high (i + 16) (by omega)]
    have h255_lt : ∀ j, j < 8 → (255 : Nat).testBit j = true := by
      intro j hj; interval_cases j <;> decide
    have h255_ge : ∀ j, 8 ≤ j → (255 : Nat).testBit j = false := fun j hj =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le (by norm_num : (255 : Nat) < 2 ^ 8)
          (Nat.pow_le_pow_right (by norm_num) hj))
    rcases lt_or_ge i 8 with hi8 | hi8
    · simp only [h255_lt i hi8, Bool.and_true]
      have h8le : (8 : Nat) ≤ i + 16 := by omega
      have hk1shift_i_false : (decide (8 ≤ i)) = false := by
        simp only [decide_eq_false_iff_not, not_le]; omega
      have h8le_i16 : decide ((8 : Nat) ≤ i + 16) = true := by
        simp only [decide_eq_true_eq]; omega
      simp only [hk1shift_i_false, Bool.false_and, Bool.xor_false,
                 h8le_i16, Bool.true_and]
      rw [hv1_def, Nat.testBit_xor, Nat.testBit_shiftLeft, h8le_i16,
          Bool.true_and]
    · rcases lt_or_ge i 16 with hi16 | hi16
      · have h255i : (255 : Nat).testBit i = false := h255_ge i hi8
        have h_ile : decide ((8 : Nat) ≤ i + 16) = true := by
          simp only [decide_eq_true_eq]; omega
        have h_ile_i : decide ((8 : Nat) ≤ i) = true := by
          simp only [decide_eq_true_eq]; omega
        simp only [h255i, Bool.and_false, Bool.false_xor, h_ile, Bool.true_and,
                   h_ile_i]
        rw [hk1_def, Nat.testBit_shiftRight]
        have ht1_eq_false : t1.testBit (i + 16 - 8) = false := ht1_high _ (by omega)
        rw [ht1_eq_false, Bool.xor_false]
        grind
      · have hv_eq : v.testBit (i + 16) = false := hv_high _ (by omega)
        have ht1_eq : t1.testBit (i + 16 - 8) = false := ht1_high _ (by omega)
        have hk1_eq : k1.testBit (i - 8) = false := hk1_high _ (by omega)
        have h255i : (255 : Nat).testBit i = false := h255_ge i (by omega)
        have h_ile : decide ((8 : Nat) ≤ i + 16) = true := by
          simp only [decide_eq_true_eq]; omega
        have h_ile_i : decide ((8 : Nat) ≤ i) = true := by
          simp only [decide_eq_true_eq]; omega
        simp only [hv_eq, ht1_eq, hk1_eq, h255i, h_ile, h_ile_i,
                   Bool.and_false, Bool.xor_false]
  have hhigh_poly : natToGF2Poly ((v1 ^^^ t2) >>> 16) =
      natToGF2Poly k2 + natToGF2Poly k1 * X ^ 8 := by
    rw [hhigh, natToGF2Poly_xor, natToGF2Poly_shiftLeft]
  have hd1 : POLY_GF2 ∣ (natToGF2Poly k1 * X ^ (8 + 16) +
      natToGF2Poly t1 * X ^ 8) := xor_table_shift_dvd k1 8 (htable k1 hk1_lt)
  have hd2 : POLY_GF2 ∣ (natToGF2Poly k2 * X ^ (0 + 16) +
      natToGF2Poly t2 * X ^ 0) := xor_table_shift_dvd k2 0 (htable k2 hk2_lt)
  have hxor_eq : natToGF2Poly (v1 ^^^ t2) =
      natToGF2Poly v + natToGF2Poly t1 * X ^ 8 + natToGF2Poly t2 := by
    rw [natToGF2Poly_xor, hv1_def, natToGF2Poly_xor, natToGF2Poly_shiftLeft]
  have hsplit : natToGF2Poly (v1 ^^^ t2) =
      natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) +
        natToGF2Poly ((v1 ^^^ t2) >>> 16) * X ^ 16 :=
    natToGF2Poly_split (v1 ^^^ t2) 16
  have hkey : natToGF2Poly v - natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) =
      (natToGF2Poly k1 * X ^ (8 + 16) + natToGF2Poly t1 * X ^ 8) +
      (natToGF2Poly k2 * X ^ (0 + 16) + natToGF2Poly t2 * X ^ 0) := by
    have h1 : natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) =
        natToGF2Poly v + natToGF2Poly t1 * X ^ 8 + natToGF2Poly t2 -
          natToGF2Poly ((v1 ^^^ t2) >>> 16) * X ^ 16 := by
      have hh := hsplit
      rw [hxor_eq] at hh
      linear_combination -hh
    rw [h1, hhigh_poly]
    rw [show natToGF2Poly v - (natToGF2Poly v + natToGF2Poly t1 * X ^ 8 +
            natToGF2Poly t2 - (natToGF2Poly k2 + natToGF2Poly k1 * X ^ 8) * X ^ 16) =
          (natToGF2Poly k2 + natToGF2Poly k1 * X ^ 8) * X ^ 16 +
            -(natToGF2Poly t1 * X ^ 8 + natToGF2Poly t2) from by ring,
        zmod2_poly_neg_eq]
    ring
  have hdvd : POLY_GF2 ∣ (natToGF2Poly v - natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16)) := by
    rw [hkey]; exact dvd_add hd1 hd2
  have hmod_eq : natToGF2Poly v %ₘ POLY_GF2 =
      natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) %ₘ POLY_GF2 :=
    Polynomial.modByMonic_eq_of_dvd_sub POLY_GF2_monic hdvd
  have ha_lt : (v1 ^^^ t2) % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by norm_num)
  have ha_deg : (natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16)).degree < POLY_GF2.degree := by
    rw [Polynomial.degree_eq_natDegree POLY_GF2_monic.ne_zero, POLY_GF2_natDegree]
    rcases eq_or_ne (natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16)) 0 with heq | hne
    · rw [heq, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      have hm' : 16 ≤ m := by exact_mod_cast hm
      rw [natToGF2Poly_coeff]
      have hbnd : (v1 ^^^ t2) % 2 ^ 16 < 2 ^ m := lt_of_lt_of_le ha_lt
        (Nat.pow_le_pow_right (by norm_num) hm')
      rw [Nat.testBit_eq_false_of_lt hbnd]
      simp
  have ha_self : natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) %ₘ POLY_GF2 =
      natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) :=
    (Polynomial.modByMonic_eq_self_iff POLY_GF2_monic).mpr ha_deg
  rw [hmod_eq, ha_self]

/-- **Spec theorem for `spqr::encoding::gf::reduce::poly_reduce`**:

Table-based polynomial reduction of a 32-bit carry-less product
modulo the irreducible polynomial POLY = 0x1100b, yielding a
16-bit GF(2¹⁶) element.

The function uses the precomputed `REDUCE_BYTES` table to
process the input byte-by-byte from high to low:
  1. Clear bits 24–31 using `REDUCE_BYTES[v >> 24] << 8`.
  2. Clear bits 16–23 using `REDUCE_BYTES[(v >> 16) & 0xFF]`.
  3. Return the remaining 16 bits.

The result satisfies the algebraic specification:
  `natToGF2Poly result.val = (natToGF2Poly v.val) %ₘ POLY_GF2`

This connects the bitwise table-lookup implementation to
polynomial reduction in GF(2)[X], confirming that `poly_reduce`
computes the canonical degree-< 16 representative of `v` modulo
POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1.

**Source**: spqr/src/encoding/gf.rs (lines 489:4-498:5)
-/
@[step]
theorem poly_reduce_spec (v : Std.U32) :
    poly_reduce v ⦃ result =>
      natToGF2Poly result.val = (natToGF2Poly v.val) %ₘ POLY_GF2 ⦄ := by
  unfold poly_reduce spqr.encoding.gf.reduce.REDUCE_BYTES
  step*
  · simp only [Array.length_eq]
    scalar_tac
  · simp only [Array.length_eq]
    rw [i21_post1, UScalar.val_and]
    exact nat_and_255_lt_256 _
  · have hv_lt : v.val < 2 ^ 32 := v.hBounds
    have hi_val : i.val = v.val >>> 24 := i_post1
    have hi1_val : i1.val = v.val >>> 24 := by
      rw [i1_post, U32.cast_Usize_val_eq]; exact hi_val
    have hi1_lt : i1.val < 256 := by
      rw [hi1_val, Nat.shiftRight_eq_div_pow]
      have hp : (0 : Nat) < 2 ^ 24 := by positivity
      rw [Nat.div_lt_iff_lt_mul hp]
      have h32 : (256 : Nat) * 2 ^ 24 = 2 ^ 32 := by norm_num
      omega
    have hi2_eq : i2.val = reduceByteTable i1.val := by
      obtain ⟨w, hw_idx, hw_poly⟩ := a_post i1 hi1_lt
      have hw_eq : w = i2 := by
        have hw_idx' := index_usize_ok_eq a i1 w hw_idx
        simp_all
      have hi2_poly :
          natToGF2Poly i2.val = natToGF2Poly i1.val * X ^ 16 %ₘ POLY_GF2 := by
        rw [← hw_eq]; exact hw_poly
      exact natToGF2Poly_inj _ _
        (hi2_poly.trans (reduceByteTable_eq_poly_full i1.val hi1_lt).symm)
    have hi3_val : i3.val = i2.val := by
      rw [i3_post, U16.cast_U32_val_eq]
    have hi2_lt : i2.val < 2 ^ 16 := i2.hBounds
    have hi4_val : i4.val = i2.val <<< 8 := by
      rw [i4_post1, hi3_val]
      have hbnd : i2.val <<< 8 < U32.size := by
        rw [Nat.shiftLeft_eq]
        have hmul : i2.val * 2 ^ 8 < 2 ^ 16 * 2 ^ 8 :=
          Nat.mul_lt_mul_of_pos_right hi2_lt (by norm_num)
        have heq : (2 : Nat) ^ 16 * 2 ^ 8 = 2 ^ 24 := by norm_num
        have hlt : (2 : Nat) ^ 24 < U32.size := by
          scalar_tac
        omega
      exact Nat.mod_eq_of_lt hbnd
    have hv1_val : v1.val = v.val ^^^ (i2.val <<< 8) := by
      rw [v1_post1, UScalar.val_xor, hi4_val]
    have hi5_val : i5.val = v1.val >>> 16 := i5_post1
    have hsh_val : shifted_v.val = i5.val := by
      rw [shifted_v_post, U32.cast_Usize_val_eq]
    have hi21_val : i21.val = (v1.val >>> 16) &&& 255 := by
      rw [i21_post1, UScalar.val_and, hsh_val, hi5_val]; rfl
    have hi21_lt : i21.val < 256 := by
      rw [hi21_val]; exact nat_and_255_lt_256 _
    have hi6_eq : i6.val = reduceByteTable i21.val := by
      obtain ⟨w, hw_idx, hw_poly⟩ := a_post i21 hi21_lt
      have hw_eq : w = i6 := by
        have hw_idx' := index_usize_ok_eq a i21 w hw_idx
        rw [i6_post, hw_idx']
      have hi6_poly :
          natToGF2Poly i6.val = natToGF2Poly i21.val * X ^ 16 %ₘ POLY_GF2 := by
        rw [← hw_eq]; exact hw_poly
      exact natToGF2Poly_inj _ _
        (hi6_poly.trans (reduceByteTable_eq_poly_full i21.val hi21_lt).symm)
    have hi7_val : i7.val = i6.val := by
      rw [i7_post, U16.cast_U32_val_eq]
    have hv2_val : v2.val = v1.val ^^^ i6.val := by
      rw [v2_post1, UScalar.val_xor, hi7_val]
    have hbridge : (UScalar.cast UScalarTy.U16 v2).val = polyReduceSpec v.val := by
      rw [UScalar.cast_val_eq]
      change v2.val % 2 ^ 16 = polyReduceSpec v.val
      rw [hv2_val, hi6_eq, hi21_val, hv1_val, hi2_eq, hi1_val]
      simp only [polyReduceSpec]
    rw [hbridge]
    exact polyReduceSpec_correct v.val hv_lt reduceByteTable_eq_poly_full

end spqr.encoding.gf.reduce
